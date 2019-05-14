//
//  EVM.swift
//  IRGen
//
//  Created by Franklin Schrans on 5/3/18.
//

import BigInt

/// Constants related to EVM.
enum EVM {
  /// The size of an EVM storage location, in bytes.
  static var wordSize: BigInt {
    return 32
  }
}
