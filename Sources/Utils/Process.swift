//
//  Process.swift
//  Utils
//
//  Created by matteo on 03/09/2019.
//

import Foundation

public struct ProcessResult {
  public let standardOutputResult: String?
  public let standardErrorResult: String?
  public let terminationStatus: Int32
}

extension Process {
  @discardableResult
  public static func execute(executableURL: URL, arguments: [String], currentDirectoryURL: URL?) -> ProcessResult {
    let process = Process()
    let standardOutputPipe = Pipe()
    let standardErrorPipe = Pipe()
    process.executableURL = executableURL
    process.arguments = arguments
    currentDirectoryURL.map { process.currentDirectoryURL = $0 }
    #if os(macOS)
    process.standardInput = FileHandle.nullDevice
    #else
    process.standardInput = FileHandle(forReadingAtPath: "/dev/null")!
    #endif
    process.standardOutput = standardOutputPipe
    process.standardError = standardErrorPipe
    try! process.run()
    let standardOutputData = standardOutputPipe.fileHandleForReading.readDataToEndOfFile()
    let standardErrorData = standardErrorPipe.fileHandleForReading.readDataToEndOfFile()
    let standardOutputText = String(data: standardOutputData, encoding: String.Encoding.utf8)
    let standardErrorText = String(data: standardErrorData, encoding: String.Encoding.utf8)
    process.waitUntilExit()

    if process.terminationStatus != 0 {
      print("The following external process call terminated with an error: ")
      print("Executable: \(executableURL.path)")
      print("Arguments: \(arguments)")
      currentDirectoryURL.map { print("Working directory: \($0)") }
      standardOutputText.map { print("stdout: \($0)") }
      standardErrorText.map { print("stderr: \($0)") }
    }

    return ProcessResult(standardOutputResult: standardOutputText,
                         standardErrorResult: standardErrorText,
                         terminationStatus: process.terminationStatus)
  }
}
