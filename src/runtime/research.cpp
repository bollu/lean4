#include "runtime/research.h"

#include <assert.h>

#include <cstdint>
#include <cstdlib>  // For std::getenv
#include <iostream>

#include "runtime/exception.h"
#include "util/io.h"

extern "C" {
uint8_t research_isReuseAcrossConstructorsEnabled(lean_object *) {
  const char *_var =
      std::getenv("RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED");
  if (!_var) {
    return true;
  } else {
    std::string var(_var);
    if (var != "true" && var != "TRUE" && var != "1" && var != "false" &&
        var != "FALSE" && var != "0") {
      throw lean::throwable(
          "expected 'true/false' for "
          "RESEARCH_IS_REUSE_ACROSS_CONSTRUCTORS_ENABLED, found '" +
          var + "'");
    }
    return var == "true" || var == "TRUE" || var == "1";
  }
}

} // end extern "C"
