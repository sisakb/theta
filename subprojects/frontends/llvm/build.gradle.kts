/*
 *  Copyright 2023 Budapest University of Technology and Economics
 *
 *  Licensed under the Apache License, Version 2.0 (the "License");
 *  you may not use this file except in compliance with the License.
 *  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 *  Unless required by applicable law or agreed to in writing, software
 *  distributed under the License is distributed on an "AS IS" BASIS,
 *  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 *  See the License for the specific language governing permissions and
 *  limitations under the License.
 */

import org.gradle.internal.os.OperatingSystem.current
import java.io.ByteArrayOutputStream
import java.io.IOException

plugins {
    id("cpp-library")
}

val llvmConfigBinary = try {
    val output = runCommandForOutput("llvm-config", "--version")
    val version = output[0].split('.')
    val major = version[0]
    val minor = version[1]
    val patch = version[2]
    if (major == "14")
        "llvm-config"
    else
        throw IOException()
} catch (e: IOException) {
    try {
        val output = runCommandForOutput("llvm-config-14", "--version")
        val version = output[0].split('.')
        val major = version[0]
        val minor = version[1]
        val patch = version[2]
        if (major == "14")
            "llvm-config-14"
        else
            throw IOException()
    } catch (e: IOException) {
        println("LLVM-14 not installed, not building native library.")
        null
    }
}

val taskEnabled = current().isLinux && llvmConfigBinary != null

fun runCommandForOutput(vararg args: String): Array<String> {
    val process = ProcessBuilder(*args).start()
    val outputStream = ByteArrayOutputStream()
    process.inputStream.copyTo(outputStream)
    process.waitFor()
    val ret = outputStream.toString()
        .trim()
        .split(" ")
        .filter { it.length > 1 }
        .map { it.trim() }
        .toTypedArray()
    return ret
}

fun llvmConfigFlags(vararg args: String): Array<String> {
    if (!taskEnabled) return arrayOf()
    return try {
        runCommandForOutput(llvmConfigBinary!!, *args)
    } catch (e: IOException) {
        e.printStackTrace()
        arrayOf()
    }//.also { println("LLVM flags (${args.toList()}): ${it.toList()}") }
}

fun jniConfigFlags(): Array<String> {
    if (!taskEnabled) return arrayOf()
    val jdkHomeArr = runCommandForOutput("bash", "-c",
        "dirname \$(cd \$(dirname \$(readlink -f \$(which javac) || which javac)); pwd -P)")
    check(jdkHomeArr.size == 1)
    val jdkHome = File(jdkHomeArr[0])
    check(jdkHome.exists())
    val mainInclude = jdkHome.resolve("include")
    val linuxInclude = mainInclude.resolve("linux")
    return arrayOf(
        "-I${mainInclude.absolutePath}",
        "-I${linuxInclude.absolutePath}",
    )//.also { println("JNI flags: ${it.toList()}") }
}

library {
    targetMachines.add(machines.linux.x86_64)
    tasks.withType(CppCompile::class) {
        compilerArgs.addAll(listOf(
            "-Wall",
            "-fpic",
            *jniConfigFlags(),
            *llvmConfigFlags("--cxxflags")))
        onlyIf {
            println("CppCompile is enabled: $taskEnabled")
            this@Build_gradle.taskEnabled
        }
    }

    tasks.withType(LinkSharedLibrary::class) {
        linkerArgs.addAll(listOf(
            "-rdynamic",
            *llvmConfigFlags("--cxxflags", "--ldflags", "--libs", "core", "bitreader"),
            "-ldl"))
        onlyIf {
            println("LinkSharedLibrary is enabled: $taskEnabled")
            this@Build_gradle.taskEnabled
        }
    }
}