# The Flint Programming Language [![Build Status](https://travis-ci.org/flintlang/flint.svg?branch=master)](https://travis-ci.org/flintlang/flint)

<img src="docs/flint_small.png" height="70">


Flint is a new type-safe, contract-oriented programming language specifically designed for writing robust smart contracts on Ethereum.

Flint is still in **alpha development**, and is not ready to be used in production yet. 

Medium articles:
[Write Safer Smart Contracts](https://medium.com/@susan.eisenbach/write-safer-smart-contracts-b0c8049f72c5) and
[Flint: A New Language for Safe Smart Contracts on Ethereum](https://medium.com/@fschrans/flint-a-new-language-for-safe-smart-contracts-on-ethereum-a5672137a5c7)

Programming 2018! paper: [Writing Safe Smart Contracts in Flint](https://dl.acm.org/citation.cfm?doid=3191697.3213790)


Current working paper: [Flint for Safer Smart Contracts](https://arxiv.org/abs/1904.06534)

Flint has been developed as part of projects and summer work at [Imperial College Department of Computing](https://www.doc.ic.ac.uk) under the supervision of Professors Susan Eisenbach and Sophia Drossopoulou. Its original developer was Franklin Schrans for his MEng thesis and then continued. The following people have contributed to Flint: Matteo Bilardi,
Aurel Bily,
Mohammad Chowdhury,
Catalin Craciun,
Calin Farcas,
Ioannis Gabrielides,
Daniel Hails,
Alexander Harkness,
Constantin Mueller,
Yicheng Leo,
Matthew Ross Rachar,
Franklin Schrans,
Niklas Vangerow, and
Manshu Wang.

The documentation (reports and presentations) can be accessed [here](https://github.com/flintlang/flint/tree/master/docs/pdfs%20(student%20theses)) and the codebase is [here](https://github.com/flintlang/flint). We are very pleased to have support from the [Ethereum Foundation ](https://blog.ethereum.org/2018/10/15/ethereum-foundation-grants-update-wave-4/) for this work.

## Language Overview

The **Flint Programming Language Guide** ([website](https://docs.flintlang.org), [local](docs/language_guide.md)) gives a high-level overview of the language, and helps you getting started with smart contract development in Flint.

Flint is still under active development and proposes a variety of novel _contract-oriented_ features.

### Caller Protections

[**Caller protections**](https://docs.flintlang.org/caller-protections) require programmers to think about who should be able to call the contract’s sensitive functions. Protections are checked statically for internal calls (unlike Solidity modifiers), and at runtime for calls originating from external contracts.

Example:

```swift
// State declaration
contract Bank {
  var manager: Address
}

// Functions are declared in protection blocks,
// which specify which users are allowed to call them.
Bank :: (manager) { // manager is a state property.

  // Only `manager` of the Bank can call `clear`.
  func clear(address: Address) {
    // body
  }
}

// Anyone can initialize the contract.
Bank :: (any) {
  public init(manager: Address) {
    self.manager = manager
  }
}
```

### Type States
[**Type States**](docs/language_guide.md#type-states) integrate a design pattern of stateful contracts into the language itself, which both require programmers to think about what state a function can be called in but also to prevent vulnerabilities (e.g. Parity Multi-Sig wallet) from mistakes with respect to administrating state. States are checked statically for internal calls (unlike Solidity modifiers), and at runtime for calls originating from external contracts.

Example:
```swift
// Enumeration of states.
contract Auction (Preparing, InProgress) {}

Auction @(Preparing, InProgress) :: caller <- (any) {
  public init() {
    // ...
    become Preparing
  }
}

Auction @(Preparing) :: (beneficiary) {
  public func setBeneficiary(beneficiary: Address) mutates (beneficiary) {
    self.beneficiary = beneficiary
  }

  func openAuction() -> Bool {
    // ...
    become InProgress
  }
}
```

### Immutability by default

**Restricting writes to state** in functions helps programmers more easily reason about the smart contract. A function which writes to the contract’s state needs to be annotated with the `mutates (...)` keyword, giving the list of variables that are mutated.

Example:

```swift
Bank :: (any) {
  func incrementCount() mutates (count) {
    // count is a state property
    count += 1
  }

  func getCount() -> Int {
    return count
  }

  func decrementCount() {
    // error: Use of mutating statement in a nonmutating function
    // count -= 1
  }
}
```

### Asset types

[**Assets**](docs/language_guide.md#assets), such as Ether, are often at the center of smart contracts. Flint puts assets at the forefront through the special _Asset_ trait.

Flint's Asset type ensure a contract's state always truthfully represents its Ether value, preventing attacks such as TheDAO.

A restricted set of atomic operations can be performed on Assets. It is impossible to create, duplicate, or lose Assets (such as Ether) in unprivileged code. This prevents attacks relating to double-spending and re-entrancy.

Example use:

```swift
Bank :: account <- (balances.keys) {
  @payable
   func deposit(implicit value: inout Wei) mutates (balances) {
    // Omitting this line causes a compiler warning: the value received should be recorded.
    balances[address].transfer(&value)
  }

  func withdraw() mutates(account, balances) {
    // balances[account] is automatically set to 0 before transferring.
    send(account, &balances[account])
  }
}
```

The Asset feature is still in development. The [FIP-0001: Introduce the Asset trait](proposals/0001-asset-trait.md) proposal includes more details.

### Safer semantics

In the spirit of reducing vulnerabilities relating to unexpected language semantics, such as wrap-arounds due to integer overflows, Flint aims to provide safer operations. For instance, arithmetic operations on `Int` are safe by default: an overflow/underflow causes the Ethereum transaction to be reverted.

## Installation

For detailed installation instructions, see the [language guide](https://github.com/flintlang/flint/blob/master/docs/language_guide.md#installation), however, to install Flint on Ubuntu 18.04 LTS, you can simply run:

```bash
bash <(curl -s https://raw.githubusercontent.com/flintlang/flint/master/utils/install_ubuntu_18_04.sh)
```

which will install Flint into "~/.flint". An older version of the Flint compiler and its dependencies can be installed straight from Docker Hub:

```bash
docker pull franklinsch/flint
docker run -i -t franklinsch/flint
```

Example smart contracts are available in `flint/examples/valid/`.


## Contributing

Contributions to Flint are highly welcomed! [Contribution Guide](CONTRIBUTING.md)
The Issues page tracks the tasks which have yet to be completed.

Flint Improvement Proposals (FIPs) track the design and implementation of larger new features for Flint or the Flint compiler. An example is [FIP-0001: Introduce the Asset trait](proposals/0001-asset-trait.md).

## Cloning Repo
_For more information, see [Building from source](docs/language_guide.md#building-from-source) in the language guide_

Assuming you have all the prerequisites, you should be able to build flint by running

```bash
git clone --recurse-submodules https://www.github.com/flintlang/flint.git $HOME/.flint
cd $HOME/.flint
make release
echo "export PATH=$HOME/.flint/.build/release/:$PATH" >> ~/.bashrc
source ~/.bashrc
```


### Ubuntu 18.04 LTS
This assumes a standard Ubuntu build with `apt`, `wget`, `curl`, `gnupg`, `ca-certificates` and `git` installed. If you don't have one of them installed, you should be notified during the process. If you have any kind of error, try installing them. Note Ubuntu 16.04 has different installation procedures when using apt and installing Mono, thus the process would need to be done manually. You may find the [18.04 install script](https://raw.githubusercontent.com/flintlang/flint/master/utils/install_ubuntu_18_04.sh) a good place to start on what you need to install it.

```bash
bash <(curl -s https://raw.githubusercontent.com/flintlang/flint/master/utils/install_ubuntu_18_04.sh)
```



## Future plans

Future plans for Flint are numerous, and include:

1. **Gas estimation**: provide estimates about the gas execution cost of a function. Gas upper bounds are emitted as part of the contract's interface, making it possible to obtain the estimation of a call to an external Flint function.
2. **Formalization**: specify well-defined semantics for the language.
3. **The Flint Package Manager**: create a package manager which runs as a Flint smart contract on Ethereum. It will store contract APIs as well as safety and gas cost information of dependencies.
4. **Tooling**: build novel tools around smart contract development, such as new ways of simulating and visualizing different transaction orderings.

## License

The Flint project is available under the MIT license. See the LICENSE file for more information.
