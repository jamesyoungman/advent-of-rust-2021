use std::collections::VecDeque;
use std::io;
use std::io::prelude::*;

type Bitstream = VecDeque<bool>;
#[derive(Debug, Eq, PartialEq)]

enum Packet {
    Literal {
        version: u8,
        value: u64,
    },
    Operator {
        version: u8,
        subpackets: Vec<Box<Packet>>,
    },
}

fn binstring(bits: &VecDeque<bool>) -> String {
    bits.iter().map(|b| if *b { '1' } else { '0' }).collect()
}

fn get_hex(hexdigit: char) -> Result<u8, String> {
    match hexdigit.to_digit(16) {
        Some(n) => {
            let result: Result<u8, _> = n.try_into();
            result.map_err(|e| e.to_string())
        }
        None => Err(format!(
            "not a hex digit: '{}' (unicode {})",
            hexdigit,
            hexdigit.escape_unicode(),
        )),
    }
}

fn to_bits(hex: u8) -> Bitstream {
    let mut result: VecDeque<bool> = VecDeque::with_capacity(4);
    for bitpos in (0..4).rev() {
        let bitvalue = (hex >> bitpos) & 1;
        result.push_back(bitvalue != 0);
    }
    result
}

#[test]
fn test_to_bits() {
    assert_eq!(to_bits(0x0), vec![false, false, false, false]);
    assert_eq!(to_bits(0x5), vec![false, true, false, true]);
    assert_eq!(to_bits(0xF), vec![true, true, true, true]);
}

fn extract_bits(s: &str) -> Result<Bitstream, String> {
    let mut result: VecDeque<bool> = VecDeque::with_capacity(s.len() * 4);
    for ch in s.chars() {
        match get_hex(ch) {
            Err(e) => {
                return Err(e);
            }
            Ok(digitval) => {
                result.extend(to_bits(digitval));
            }
        }
    }
    Ok(result)
}

fn extract_number(nbits: u8, mut bits: Bitstream) -> Result<(u64, Bitstream), String> {
    //println!("extract_number: extracting {} bits from {}", nbits, binstring(&bits));
    let mut result: u64 = 0;
    let bits_on_hand = bits.len();
    if bits_on_hand >= nbits as usize {
        let tail = bits.split_off(nbits.into());
        let saved_bits = bits.clone();
        for bitpos in 0..nbits {
            result <<= 1;
            result |= match bits.pop_front() {
                Some(true) => 1,
                Some(false) => 0,
                None => {
                    // This should not happen because we checked
                    // bits.len() >= nbits already.
                    return Err(format!(
			"logic error in bit splitting at bit position {}: had {} bits on hand, needed {}: saved_bits={}, tail={}",
			bitpos,
			bits_on_hand,
			nbits,
			binstring(&saved_bits),
			binstring(&tail),
		    ));
                }
            };
        }
        //println!("extract_number: result is {}, tail is {}",
        //         result, binstring(&tail));
        Ok((result, tail))
    } else {
        Err(format!(
            "not enough bits remain, needed at least {}, we have only {}: {}",
            nbits,
            bits.len(),
            binstring(&bits),
        ))
    }
}

fn extract1bit(bits: Bitstream) -> Result<(u8, Bitstream), String> {
    extract_u8(1, bits)
}

fn extract3bits(bits: Bitstream) -> Result<(u8, Bitstream), String> {
    extract_u8(3, bits)
}

fn extract5bits(bits: Bitstream) -> Result<(u8, Bitstream), String> {
    extract_u8(5, bits)
}

fn extract_u8(bitcount: u8, bits: Bitstream) -> Result<(u8, Bitstream), String> {
    let (n, unconsumed) = extract_u16(bitcount, bits)?;
    match n.try_into() {
        Ok(x) => Ok((x, unconsumed)),
        Err(e) => Err(e.to_string()),
    }
}

fn extract_u16(bitcount: u8, bits: Bitstream) -> Result<(u16, Bitstream), String> {
    assert!(bitcount <= 16);
    match extract_number(bitcount, bits) {
        Ok((n, bits)) => match n.try_into() {
            Ok(val) => Ok((val, bits)),
            Err(e) => Err(e.to_string()),
        },
        Err(e) => Err(e),
    }
}

#[test]
fn test_extract3bits() {
    match extract3bits(Bitstream::from(vec![
        true, false, true, true, false, false, false, false,
    ])) {
        Ok((version, tail)) => {
            assert_eq!(version, 5);
            assert_eq!(tail.len(), 5);
        }
        Err(e) => {
            panic!("extract_version failed: {}", e);
        }
    }
}

#[test]
fn test_extract_bits() {
    assert_eq!(
        extract_bits("F0"),
        Ok(Bitstream::from(vec![
            true, true, true, true, false, false, false, false
        ]))
    );
    assert_eq!(
        extract_bits("52"),
        Ok(Bitstream::from(vec![
            false, true, false, true, false, false, true, false
        ]))
    );
    assert!(extract_bits("2Z").is_err());
}

fn extract_literal(mut bits: Bitstream) -> Result<(u64, Bitstream), String> {
    let mut value: u64 = 0;
    let mut bits_extracted: usize = 0;
    loop {
        if bits.len() < 5 {
            return Err(format!(
                "we need at least 5 bits to extract a literal from {} but we have only {}",
                binstring(&bits),
                bits.len()
            ));
        }
        let (more, nibble, tail): (bool, u64, Bitstream) = {
            let (raw, tail) = extract5bits(bits)?;
            (raw & 0b10000 != 0, (raw & 0b01111).into(), tail)
        };
        bits_extracted += 4;
        assert!(bits_extracted < 60);
        value <<= 4;
        value |= nibble;
        bits = tail;
        if !more {
            break;
        }
    }
    Ok((value, bits))
}

fn sub_packets(operator_version: u8, input: Vec<Packet>) -> Packet {
    let mut pv: Vec<Box<Packet>> = Vec::with_capacity(input.len());
    for packet in input {
        pv.push(Box::new(packet));
    }
    Packet::Operator {
        version: operator_version,
        subpackets: pv,
    }
}

fn extract_packets(
    mut bits: Bitstream,
    max_packets: usize,
) -> Result<(Vec<Packet>, Bitstream), String> {
    let mut result: Vec<Packet> = Vec::new();
    while bits.len() > 3 && result.len() < max_packets {
        println!(
            "extract_packets: we have {} bits, have {} packets and will accept up to {}",
            bits.len(),
            result.len(),
            max_packets,
        );
        println!("extract_packets: remaining bits: {}", binstring(&bits),);

        if !contains_nonzero_bits(&bits) {
            println!(
                "extract_packets: early early termination hack with tail '{}'",
                binstring(&bits)
            );
            break;
        }

        let (packet_version, tail) = extract3bits(bits)?;
        println!("packet version is {}", packet_version);
        let (packet_type_id, tail) = extract3bits(tail)?;
        println!("packet type id is {}", packet_type_id);
        println!("{} bits remaining: {}", tail.len(), binstring(&tail));

        match packet_type_id {
            //0 if packet_version == 0 => {
            //	// This is a kind of hack introduced to be able to parse
            //	// the example "38006F45291200".
            //	return Ok((result, tail));
            //}
            4 => {
                println!("extracting a literal...");
                let (value, tail) = extract_literal(tail)?;
                result.push(Packet::Literal {
                    version: packet_version,
                    value,
                });
                bits = tail;
            }
            _ => {
                let (length_type_id, tail) = extract1bit(tail)?;
                match length_type_id {
                    0 => {
                        let (bitlen, mut to_take) = extract_u16(15, tail)?;
                        println!(
			    "extract_packets: extracting subpackets in first {} bits of {} (which has {} bits)",
			    bitlen,
			    binstring(&to_take),
			    to_take.len()
			);
                        bits = to_take.split_off(bitlen.into());
                        let (got, unconsumed) = extract_packets(to_take, usize::MAX)?;
                        println!("extract_packets: got subpackets {:#?}", got);
                        result.push(sub_packets(packet_version, got));
                    }
                    1 => {
                        let (expected_sub_packet_count, tail) = extract_u16(11, tail)?;
                        println!(
                            "extract_packets: extracting {} subpackets from {}",
                            expected_sub_packet_count,
                            binstring(&tail),
                        );
                        let (got, unconsumed) =
                            extract_packets(tail, expected_sub_packet_count.into())?;
                        println!("extract_packets: got subpackets {:#?}", got);
                        result.push(sub_packets(packet_version, got));
                        bits = unconsumed;
                    }
                    _ => unreachable!(),
                }
            }
        }
    }
    Ok((result, bits))
}

fn contains_nonzero_bits(bits: &Bitstream) -> bool {
    bits.iter().any(|b| *b)
}

#[test]
fn test_extract_packets() {
    let bits: Bitstream = extract_bits("D2FE28").expect("valid test data");
    match extract_packets(bits, usize::MAX) {
        Ok((packets, unconsumed)) => {
            assert_eq!(
                packets,
                vec![Packet::Literal {
                    version: 6,
                    value: 2021
                }]
            );
            assert!(!contains_nonzero_bits(&unconsumed));
        }
        Err(e) => {
            panic!("unexpected error: {}", e.to_string());
        }
    }

    let bits: Bitstream = extract_bits("38006F45291200").expect("valid test data");
    match extract_packets(bits, usize::MAX) {
        Ok((packets, unconsumed)) => {
            dbg!(&packets);
            assert_eq!(
                packets,
                vec![Packet::Operator {
                    version: 1,
                    subpackets: vec![
                        Box::new(Packet::Literal {
                            version: 6,
                            value: 10
                        }),
                        Box::new(Packet::Literal {
                            version: 2,
                            value: 20
                        }),
                    ]
                }]
            );
            assert!(!contains_nonzero_bits(&unconsumed));
        }
        Err(e) => {
            panic!("unexpected error: {}", e.to_string());
        }
    }
}

fn packet_total_version(p: &Packet) -> u32 {
    match p {
        Packet::Literal { version, value: _ } => (*version).into(),
        Packet::Operator {
            version,
            subpackets,
        } => {
            let me: u32 = (*version).into();
            let them: u32 = subpackets.iter().map(|p| packet_total_version(p)).sum();
            me + them
        }
    }
}

fn get_total_version(packets: &[Packet]) -> u32 {
    packets.iter().map(|p| packet_total_version(p)).sum()
}

fn gtv(s: &str) -> (u32, Vec<Packet>) {
    let bits: Bitstream = match extract_bits(s) {
        Ok(bits) => bits,
        Err(e) => {
            panic!("gtv: extract_bits failed: {}", e);
        }
    };
    println!("gtv: hex was {}, bits are {}", s, binstring(&bits));
    match extract_packets(bits, usize::MAX) {
        Ok((packets, unconsumed)) => {
            let total = get_total_version(&packets);
            (total, packets)
        }
        Err(e) => {
            panic!("gtv: extract_packets failed: {}", e);
        }
    }
}

#[test]
fn test_gtv() {
    let (total, structure) = gtv("8A004A801A8002F478");
    println!("{:#?}", structure);
    assert_eq!(total, 16);
    assert_eq!(
        structure,
        vec![Packet::Operator {
            version: 4,
            subpackets: vec![Box::new(Packet::Operator {
                version: 1,
                subpackets: vec![Box::new(Packet::Operator {
                    version: 5,
                    subpackets: vec![Box::new(Packet::Literal {
                        version: 6,
                        value: 15,
                    })]
                }),]
            }),]
        }]
    );

    let (total, structure) = gtv("620080001611562C8802118E34");
    println!("{:#?}", structure);
    assert_eq!(total, 12);
    assert_eq!(
        structure,
        vec![Packet::Operator {
            version: 3,
            subpackets: vec![
                Box::new(Packet::Operator {
                    version: 0,
                    subpackets: vec![
                        Box::new(Packet::Literal {
                            version: 0,
                            value: 10,
                        }),
                        Box::new(Packet::Literal {
                            version: 5,
                            value: 11,
                        })
                    ]
                }),
                Box::new(Packet::Operator {
                    version: 1,
                    subpackets: vec![
                        Box::new(Packet::Literal {
                            version: 0,
                            value: 12,
                        }),
                        Box::new(Packet::Literal {
                            version: 3,
                            value: 13,
                        })
                    ]
                })
            ]
        }]
    );

    let (total, structure) = gtv("C0015000016115A2E0802F182340");
    println!("{:#?}", &structure);
    assert_eq!(total, 23);
    assert_eq!(
        &structure,
        &vec![Packet::Operator {
            version: 6,
            subpackets: vec![
                Box::new(Packet::Operator {
                    version: 0,
                    subpackets: vec![
                        Box::new(Packet::Literal {
                            version: 0,
                            value: 10,
                        }),
                        Box::new(Packet::Literal {
                            version: 6,
                            value: 11,
                        })
                    ]
                }),
                Box::new(Packet::Operator {
                    version: 4,
                    subpackets: vec![
                        Box::new(Packet::Literal {
                            version: 7,
                            value: 12,
                        }),
                        Box::new(Packet::Literal {
                            version: 0,
                            value: 13,
                        })
                    ]
                })
            ]
        }]
    );

    let (total, structure) = gtv("A0016C880162017C3686B18A3D4780");
    println!("{:#?}", &structure);
    assert_eq!(total, 31);
    assert_eq!(
        structure,
        vec![Packet::Operator {
            // outermost
            version: 5,
            subpackets: vec![Box::new(Packet::Operator {
                version: 1,
                subpackets: vec![Box::new(Packet::Operator {
                    version: 3,
                    subpackets: vec![
                        Box::new(Packet::Literal {
                            version: 7,
                            value: 6,
                        }),
                        Box::new(Packet::Literal {
                            version: 6,
                            value: 6,
                        }),
                        Box::new(Packet::Literal {
                            version: 5,
                            value: 12,
                        }),
                        Box::new(Packet::Literal {
                            version: 2,
                            value: 15,
                        }),
                        Box::new(Packet::Literal {
                            version: 2,
                            value: 15,
                        }),
                    ]
                })]
            })]
        }]
    );
}

fn part1(s: &str) {
    let (total, structure) = gtv(s);
    println!("Day 15 part 1: total = {}", total);
}

fn part2() {
    println!("Day 15 part 2: ?");
}

fn main() {
    let mut input = String::new();
    match io::stdin().read_to_string(&mut input) {
        Ok(_) => (),
        Err(e) => {
            panic!("failed to read input: {}", e);
        }
    }
    let no_newline: &str = input.strip_suffix("\n").unwrap_or(input.as_str());
    part1(no_newline);
    part2();
}
