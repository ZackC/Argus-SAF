/*
 * Copyright (c) 2017. Fengguo Wei and others.
 * All rights reserved. This program and the accompanying materials
 * are made available under the terms of the Eclipse Public License v1.0
 * which accompanies this distribution, and is available at
 * http://www.eclipse.org/legal/epl-v10.html
 *
 * Detailed contributors are listed in the CONTRIBUTOR.md
 */

package com.zack.coker

import scala.concurrent.duration.DurationInt
import scala.language.postfixOps
import org.argus.amandroid.alir.componentSummary.ApkYard
import org.argus.amandroid.alir.pta.reachingFactsAnalysis.{AndroidRFAConfig, AndroidReachingFactsAnalysis}
import org.argus.amandroid.core.AndroidGlobalConfig
import org.argus.amandroid.core.appInfo.AppInfoCollector
import org.argus.amandroid.core.decompile.{DecompileLayout, DecompileStrategy, DecompilerSettings}
import org.argus.jawa.core.{ClassLoadManager, FileReporter, MsgLevel}
import org.argus.jawa.core.util.{FileUtil, MyTimeout}
import org.argus.jawa.alir.Context
import org.argus.jawa.alir.pta.reachingFactsAnalysis.SimHeap

import scala.collection.mutable
import scala.collection.mutable.ListBuffer

object CheckGetActivityViolation {
  def main(args: Array[String]): Unit = {
    val fileUri = FileUtil.toUri("/mnt/hgfs/UbuntuSharedFolder/Application-debug.apk")
    val outputPath = FileUtil.toUri("/home/zack/sshdPartition/ArgusOutput/")
    val outputUri = FileUtil.toUri(outputPath)
    val reporter = new FileReporter(outputUri, MsgLevel.INFO)
    val layout = DecompileLayout(outputUri)
    val strategy = DecompileStrategy(layout)
    val yard = new ApkYard(reporter)
    val settings = DecompilerSettings(debugMode = false, forceDelete = false, strategy, reporter)
    val apk = yard.loadApk(fileUri, settings, collectInfo = false)
    AppInfoCollector.collectInfo(apk)
    for (comp <- apk.model.getComponents.toList) {
      apk.model.getEnvMap.get(comp) match {
        case Some((esig, _)) =>
          val ep = apk.getMethod(esig).get
          implicit val factory = new SimHeap
          val initialfacts = AndroidRFAConfig.getInitialFactsForMainEnvironment(ep)
          val idfg2 = AndroidReachingFactsAnalysis(apk, ep, initialfacts, new ClassLoadManager, new Context(apk.nameUri), timeout = Some(new MyTimeout(AndroidGlobalConfig.settings.timeout minutes)))
          val callMapIter2 = idfg2.icfg.getCallGraph.getCallMap.iterator
          //collect methods that call getActivity
          //TODO: at some point consider switching the (String, String) tuple to the method signature
          //which contains both points of information - only problem is the "Any" class wildcard
          val currentPathsMap = new mutable.HashMap[(String, String), List[List[(String, String)]]]()
          //"Any" means match any class
          currentPathsMap += (("getActivity","Any") -> List(List(("getActivity", "Any"))))
          //initialize to true for first run
          var newMethodAdded = true
          while (newMethodAdded) {
            val callMapIter = idfg2.icfg.getCallGraph.getCallMap.iterator
            while (callMapIter.hasNext) {
              newMethodAdded = false
              val callMapItem = callMapIter.next
              val parentMethod = callMapItem._1.methodName.toString
              val parentClass = callMapItem._1.classTyp.toString()
              val parentMethodClassTuple = (parentMethod, parentClass)
              val childrenIter = callMapItem._2.iterator
              while (childrenIter.hasNext) {
                val child = childrenIter.next
                val childMethod:String = child.methodName.toString
                val childClass:String = child.classTyp.toString
                var childPaths:ListBuffer[List[(String,String)]] = ListBuffer[List[(String, String)]]()
                val wildcardTuple = (childMethod, "Any")
                val childMethodClassTuple = (childMethod, childClass)
                if(currentPathsMap.contains(wildcardTuple)){
                  val currentlyReachingPathListIter = currentPathsMap(wildcardTuple).iterator
                  while(currentlyReachingPathListIter.hasNext) {
                    val currentlyReachingPath = currentlyReachingPathListIter.next
                    var updatedPath = new ListBuffer[(String, String)]()
                    for (pathItem: (String, String) <- currentlyReachingPath) {
                      if (pathItem._2.contentEquals("Any")) {
                        val newPathItem = (pathItem._1, childClass)
                        updatedPath += newPathItem
                      } else {
                        updatedPath += pathItem
                      }
                    }
                    val pathWithCurrentMethod:List[(String,String)] = (parentMethod, parentClass) :: updatedPath.toList
                    childPaths = childPaths += pathWithCurrentMethod
                  }
                } else if (currentPathsMap.contains(childMethodClassTuple)){
                  val currentlyReachingPathList = currentPathsMap(childMethodClassTuple)
                  for(currentPath <- currentlyReachingPathList){
                    val pathWithCurrentMethod:List[(String, String)] = (parentMethod, parentClass) :: currentPath
                    childPaths = childPaths += pathWithCurrentMethod
                  }
                }
                if (childPaths.size > 0) {
                  currentPathsMap += (parentMethodClassTuple -> childPaths.toList)
                }
              }
            }
          }
          //not 100% confident in this list at the moment of creation; I should
          //double check it is complete later
          val initializedActivityFunctions = mutable.HashMap[String, Boolean]()
          initializedActivityFunctions += ("onAttach" -> true)
          initializedActivityFunctions += ("onCreate" -> true)
          initializedActivityFunctions += ("onCreateView" -> true)
          initializedActivityFunctions += ("onActivityCreated" -> true)
          initializedActivityFunctions += ("onStart" -> true)
          initializedActivityFunctions += ("onResume" -> true)
          initializedActivityFunctions += ("onPause" -> true)
          initializedActivityFunctions += ("onStop" -> true)
          initializedActivityFunctions += ("onDestroyView" -> true)
          initializedActivityFunctions += ("onDestroy" -> true)

          //TODO: extract the different possible envMain options and then check each with the
          //algorithm below
          for( key <- currentPathsMap.keySet){
            if(key._1.contentEquals("envMain")){
              val envPaths = currentPathsMap(key)
              val envPathsIter = envPaths.iterator
              while(envPathsIter.hasNext){
                val pathToCheck = envPathsIter.next()
                var activityIsInitialized = false
                val pathIter = pathToCheck.iterator
                while(pathIter.hasNext && !activityIsInitialized){
                  val pathItem = pathIter.next()
                  val currentMethod = pathItem._1
                  if(initializedActivityFunctions.contains(currentMethod)) {
                    activityIsInitialized = true
                  } else {
                    if (currentMethod.contentEquals("getActivity")) {
                      println("!!!!!! getActivity called when it may not be initialized !!!!!!")
                      println("suspect path: " + pathToCheck)
                    }
                  }
                }
              }
            }
          }

        case None =>
          apk.reporter.error("Test control flow", "Component " + comp.toString + " doesn't have an environment. Might be a package or name mismatch in the environment.")
      }
    }
  }
}
