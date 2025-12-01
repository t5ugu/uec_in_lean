

import ProofWidgets.Component.InteractiveSvg
import ProofWidgets.Component.HtmlDisplay

open Lean ProofWidgets Svg Jsx

abbrev Vec2f := Float × Float
abbrev Ball := Nat × Nat × Vec2f
def Ball.lineSetId (b: Ball) : Nat := b.1
def Ball.lineSectionId (b: Ball) : Nat := b.2.1
def Ball.pos (b: Ball) : Vec2f := b.2.2
abbrev State := Array Ball

def lines : Array (Array Vec2f) := #[
  #[(-0.8, -0.5), (0.8, 0.5), (-0.5, 0.8)],
  #[(-0.4, 0.6), (-0.4, -0.6), (0.4, -0.6)]
]

def lineSvg (frame : Frame) : Array (Svg.Element frame) := lines.flatMap fun line => line
  |>.zip (line.drop 1)
  |>.map fun (p1, p2) =>
    Svg.line p1 p2 |>.setStroke (0.5, 0.5, 0.5) (.px 2)

def Float.clamp (x : Float) (low high : Float) : Float :=
  if x < low then low
  else if x > high then high
  else x

/-- return: dist, x, y -/
def nearestPointOnLine (line: (Vec2f × Vec2f)) (p : Vec2f) : Float × Vec2f :=
  let ((a, b), (c, d)) := line
  let db := d - b
  let ca := c - a
  let denom := db * db + ca * ca
  if denom == 0 then
    (0, a, b)
  else
    let t := (ca * (p.1 - a) + db * (p.2 - b)) / denom
    (t, a + ca * (t.clamp 0 1), b + db * (t.clamp 0 1))

def isvg : InteractiveSvg State where
  init := #[(0, 0, 0.0, 0.0), (1, 0, -0.4, 0.2)]
  frame :=
    { xmin := -1
      ymin := -1
      xSize := 2
      width := 400
      height := 400 }
  update _ _ _ _ mE _ get state :=
    match get Nat, mE with
    | some id, some p => match state[id]? with
      | some ⟨idOn, secOn, _⟩ =>
        let line := lines[idOn]!
        let ⟨d, x, y⟩ := nearestPointOnLine (line[secOn]!, line[(secOn + 1)]!) p.toAbsolute
        if d < 0.05 && secOn > 0 then
          state.set! id (idOn, secOn-1, x, y)
        else if d > 0.95 && secOn < (line.size - 2) then
          state.set! id (idOn, secOn+1, x, y)
        else
          state.set! id (idOn, secOn, x, y)
      | _ => state
    | _, _ => state
  render _ mS mE state := {
    elements :=
        let mouse := match mS, mE with
        | some s, some e => #[
            Svg.circle e (.px 5) |>.setFill (1.,1.,1.),
            Svg.line s e |>.setStroke (1.,1.,1.) (.px 2)
          ]
        | _, _ => #[]

        let circle := state.mapIdx fun idx (p : Ball) =>
          Svg.circle p.pos (.abs 0.2) |>.setFill (0.7,0.7,0.7) |>.setId s!"circle{idx}" |>.setData idx

        lineSvg _ ++ mouse ++ circle
  }

open Server RequestM in
@[server_rpc_method]
def updateSvg (params : UpdateParams State) : RequestM (RequestTask (UpdateResult State)) := isvg.serverRpcMethod params

@[widget_module]
def SvgWidget : Component (UpdateResult State) where
  javascript := include_str ".." / ".." / ".lake" / "packages" / "proofwidgets" / ".lake" / "build" / "js" / "interactiveSvg.js"

def init : UpdateResult State := {
  html := <div>Init!!!</div>,
  state := { state := isvg.init
             time := 0
             selected := none
             mousePos := none
             idToData := isvg.render 0 none none isvg.init |>.idToDataList}
}



#html <SvgWidget html={init.html} state={init.state}/>
