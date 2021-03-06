/*
 * Copyright (c) 2017. Fengguo Wei and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Detailed contributors are listed in the CONTRIBUTOR.md
 */

package org.argus.jawa.alir.reachability

import java.util.concurrent.TimeoutException

import org.argus.jawa.alir.callGraph.CallGraph
import org.argus.jawa.alir.interprocedural.CallHandler
import org.argus.jawa.alir.pta.PTAScopeManager
import org.argus.jawa.core._
import org.argus.jawa.compiler.parser.CallStatement
import org.argus.jawa.core.util.MyTimeout
import org.argus.jawa.core.util._

import scala.language.postfixOps
import scala.concurrent.duration._

/**
 * @author <a href="mailto:fgwei521@gmail.com">Fengguo Wei</a>
 */ 
object SignatureBasedCallGraph {
  final val TITLE = "SignatureBasedCallGraph"
  
  def apply(
      global: Global, 
      entryPoints: ISet[Signature],
      timer: Option[MyTimeout] = Some(new MyTimeout(1 minutes))): CallGraph = build(global, entryPoints, timer)
      
  def build(
      global: Global, 
      entryPoints: ISet[Signature],
      timer: Option[MyTimeout]): CallGraph = {
    global.reporter.println(s"Building SignatureBasedCallGraph with ${entryPoints.size} entry points...")
    val cg = new CallGraph
    val processed: MSet[String] = msetEmpty
    entryPoints.foreach{ ep =>
      if(timer.isDefined) timer.get.refresh()
      try {
        val epmopt = global.getMethodOrResolve(ep)
        epmopt match {
          case Some(epm) =>
            if (!PTAScopeManager.shouldBypass(epm.getDeclaringClass) && epm.isConcrete) {
              sbcg(global, epm, cg, processed, timer)
            }
          case None =>
        }
      } catch {
        case te: TimeoutException =>
          global.reporter.error(TITLE, ep + ": " + te.getMessage)
      }
    }
    global.reporter.println(s"SignatureBasedCallGraph done with call size ${cg.getCallMap.size}.")
    cg
  }
  
  private def sbcg(global: Global, ep: JawaMethod, cg: CallGraph, processed: MSet[String], timer: Option[MyTimeout]) = {
    val worklist: MList[JawaMethod] = mlistEmpty // Make sure that all the method in the worklist are concrete.
    worklist += ep
    while(worklist.nonEmpty) {
      if(timer.isDefined) timer.get.isTimeoutThrow()
      val m = worklist.remove(0)
      processed += m.getSignature.signature
      try {
        m.getBody.resolvedBody.locations foreach { l =>
          l.statement match {
            case cs: CallStatement =>
              CallHandler.resolveSignatureBasedCall(global, cs.signature, cs.kind) foreach { callee =>
                cg.addCall(m.getSignature, callee.getSignature)
                if (!processed.contains(callee.getSignature.signature) && !PTAScopeManager.shouldBypass(callee.getDeclaringClass) && callee.isConcrete) {
                  worklist += callee
                }
              }
            case _ =>
          }
        }
      } catch {
        case e: Throwable => global.reporter.warning(TITLE, e.getMessage)
      }
    }
  }
}
