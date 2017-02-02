#use "topfind";;
#require "graphics";;

let re_from = -2.5;;
let re_to = 0.5;;
let im_from = -1.5;;
let im_to = 1.5;;
let iterates = 100;;

Graphics.open_graph "";;

let width = Graphics.size_y ();;
let height = Graphics.size_y ();;

Graphics.draw_image (Graphics.make_image (Array.init height (fun y ->
  Array.init width (fun x ->
    let re_c = re_from +. (re_to -. re_from) *. float_of_int x /. float_of_int width in
    let im_c = im_from +. (im_to -. im_from) *. float_of_int y /. float_of_int height in
    Array.make iterates 0
    |> Array.fold_left (fun (re_z, im_z) _ ->
        (re_z *. re_z -. im_z *. im_z +. re_c, 2. *. re_z *. im_z +. im_c)) (0., 0.)
    |> (fun (re_z_n, im_z_n) ->
        if re_z_n *. re_z_n +. im_z_n *. im_z_n < 4. then Graphics.black
        else Graphics.white))))) 0 0;;

Graphics.close_graph ();;
