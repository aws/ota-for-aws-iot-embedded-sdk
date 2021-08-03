/*
 Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 SPDX-License-Identifier: Apache-2.0
*/

/****************************************************************/

function isFunction(element) {
  return element.classList && element.classList.contains("function");
}

function isFunctionCall(element) {
  return element.classList && element.classList.contains("function-call");
}

function isFunctionBody(element) {
  return element.classList && element.classList.contains("function-body");
}

function isFunctionReturn(element) {
  return element.classList && element.classList.contains("function-return");
}

function isHidden(element) {
  return element.classList && element.classList.contains("hidden");
}

/****************************************************************/

function hideFunctionBody(element) {
  if (isFunctionBody(element)) {
    element.classList.add("hidden");
  }
}

function showFunctionBody(element) {
  if (isFunctionBody(element)) {
    element.classList.remove("hidden");
  }
}

function toggleFunctionBody(element) {
  if (isFunctionBody(element)) {
    element.classList.toggle("hidden");
  }
}

/****************************************************************/

function hideFunction(element) {
  if (isFunction(element)) {
    for (elt of element.children) {
      hideFunctionBody(elt);
    }
  }
}

function showFunction(element) {
  if (isFunction(element)) {
    for (elt of element.children) {
      showFunctionBody(elt);
    }
  }
}

function toggleFunction(element) {
  if (isFunction(element)) {
    for (elt of element.children) {
      toggleFunctionBody(elt);
    }
  }
}

function eventToggleFunction(event) {
  if (event.shiftKey && !event.altKey) {
    toggleFunction(this);
    event.stopPropagation();
  }
}

for (elt of document.getElementsByClassName("function")) {
  elt.addEventListener("click", eventToggleFunction);
}

for (elt of document.getElementsByClassName("step")) {
  elt.addEventListener("click", eventHideSiblings);
}

/****************************************************************/

function hideSiblings(element) {
  for (elt of element.parentElement.children) {
    if (elt != element) {
      hideFunction(elt);
    }
  }
}

function eventHideSiblings(element) {
  if (event.shiftKey && event.altKey) {
    hideSiblings(this);
  }
}

for (elt of document.getElementsByClassName("function")) {
  elt.addEventListener("click", eventHideSiblings);
}

/****************************************************************/
