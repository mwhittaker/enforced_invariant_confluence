module String = struct
  type t = string
  let compare = compare
end

module StringSet = Set.Make(String)
module StringMap = Map.Make(String)
