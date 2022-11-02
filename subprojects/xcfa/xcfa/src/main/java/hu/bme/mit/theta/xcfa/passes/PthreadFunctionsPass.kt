/*
 *  Copyright 2022 Budapest University of Technology and Economics
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

package hu.bme.mit.theta.xcfa.passes

import hu.bme.mit.theta.core.decl.VarDecl
import hu.bme.mit.theta.core.type.Type
import hu.bme.mit.theta.core.type.anytype.RefExpr
import hu.bme.mit.theta.frontend.transformation.grammar.expression.Reference
import hu.bme.mit.theta.xcfa.model.*

/**
 * Transforms the following pthread procedure calls into model elements:
 *      - pthread_create()
 *      - pthread_join()
 * Requires the ProcedureBuilder be `deterministic`.
 */
class PthreadFunctionsPass : ProcedurePass {
    override fun run(builder: XcfaProcedureBuilder): XcfaProcedureBuilder {
        checkNotNull(builder.metaData["deterministic"])
        for (edge in ArrayList(builder.getEdges())) {
            val edges = edge.splitIf(this::predicate)
            if(edges.size > 1 || (edges.size == 1 && predicate((edges[0].label as SequenceLabel).labels[0]))) {
                builder.removeEdge(edge)
                val labels: MutableList<XcfaLabel> = ArrayList()
                edges.forEach {
                    if (predicate((it.label as SequenceLabel).labels[0])) {
                        val invokeLabel = it.label.labels[0] as InvokeLabel
                        val fence = when(invokeLabel.name) {
                            "pthread_join" -> {
                                val handle = invokeLabel.params[1]
                                check(handle is RefExpr && (handle as RefExpr<out Type>).decl is VarDecl)

                                JoinLabel(handle, metadata = invokeLabel.metadata)
                            }
                            "pthread_create" -> {
                                val handle = invokeLabel.params[1] as Reference<*,*>
                                check(handle.op is RefExpr && (handle.op as RefExpr<out Type>).decl is VarDecl)

                                val funcptr = invokeLabel.params[3]
                                check(funcptr is RefExpr && (funcptr as RefExpr<out Type>).decl is VarDecl)

                                val param = invokeLabel.params[4]

                                StartLabel((funcptr as RefExpr<out Type>).decl.name, listOf(param), (handle.op as RefExpr<out Type>).decl as VarDecl<*>,  metadata = invokeLabel.metadata)
                            }
                            else -> error("Unknown pthread function ${invokeLabel.name}")
                        }
                        labels.add(fence)
                    } else {
                        labels.addAll(it.label.labels)
                    }
                }
                builder.addEdge(edge.withLabel(SequenceLabel(labels)))
            }
        }
        return builder
    }

    private fun predicate(it: XcfaLabel): Boolean {
        return it is InvokeLabel && it.name.startsWith("pthread_")
    }
}