module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityBaseChangePasting
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedTorIndependentBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.TorIndependenceComp

/-!
# The base change map between right adjoints of pushforward on algebraic spaces

For a cartesian square of quasi-compact quasi-separated algebraic spaces with `X` and `Y'` Tor
independent over `Y`, the mate `Rg'_* ∘ a' ⟶ a ∘ Rg_*` of Stacks 0E5B is invertible (0E5C), which
defines the base change map `L(g')^* ∘ a ⟶ a' ∘ Lg^*` (0E5D); it is compatible with traces and
units (0E5L, 0E5M) and with stacking squares (0E5E, 0E5F).

The invertibility of 0E5C is the Tor independent base change theorem of Stacks 08IR,
`AlgebraicGeometry.Space.isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent`.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDerivedRightAdjointBaseChangeMap`: the map of 0E5D.

## Main results

* `AlgebraicGeometry.Space.isIso_quasicoherentDerivedRightAdjointBaseChange` (0E5C),
  `quasicoherentDerivedRightAdjointBaseChangeMap_trace` (0E5L),
  `quasicoherentDerivedRightAdjointBaseChangeMap_unit` (0E5M),
  `quasicoherentDerivedRightAdjointBaseChangeMap_vertical` (0E5E),
  `quasicoherentDerivedRightAdjointBaseChangeMap_horizontal` (0E5F).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 5000] SheafOfModules.instAbelian

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (hZ : B.Contains (⊤_ Scheme.{u}))

section Square

variable {X Y X' Y' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y' ⟶ Y} {f' : X' ⟶ Y'}
  {g' : X' ⟶ X} (sq : IsPullback g' f' f g)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
  (hY'qc : IsQuasiCompactSpace B S hS Y'.1) (hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ Y'.1)
  (hTor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom)

/-- The adjunction `Rf_* ⊣ a` of the square. -/
abbrev squareAdjF := quasicoherentDerivedRightAdjointAdjunction hZ f hXqc hXqs hYqs
  (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
  (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)

/-- The adjunction `Rf'_* ⊣ a'` of the square. -/
abbrev squareAdjF' := quasicoherentDerivedRightAdjointAdjunction hZ f'
  (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
  (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs
  (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y'.2 hY'qs
    (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc) f'.hom)
  (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
    (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) f'.hom)

/-- The adjunction `Lg^* ⊣ Rg_*` of the square. -/
abbrev squareAdjG := quasicoherentDerivedModuleAdjunction B S hS g
  (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hY'qc g.hom)
  (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs g.hom)

/-- The adjunction `L(g')^* ⊣ Rg'_*` of the square. -/
abbrev squareAdjG' := quasicoherentDerivedModuleAdjunction B S hS g'
  (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ X.2 hXqs
    (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc) g'.hom)
  (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
    (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) g'.hom)

/-- The base change map `Lg^* ∘ Rf_* ⟶ Rf'_* ∘ L(g')^*` on `D_QCoh` of the square. -/
abbrev squareBaseChange := quasicoherentDerivedBaseChange f g f' g' sq.w
  (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
  (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)
  (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y'.2 hY'qs
    (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc) f'.hom)
  (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
    (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) f'.hom)

include hTor in
/-- The base change map on `D_QCoh` of a Tor independent cartesian square is invertible
(Stacks 08IR). -/
theorem isIso_squareBaseChange :
    IsIso (squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs) :=
  isIso_quasicoherentDerivedBaseChange f g f' g' sq.w _ _ _ _
    (fun K => isIso_smallEtaleDerivedBaseChangeMap_of_torIndependent B S hS f g f' g' sq
      (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
      (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)
      hTor K.obj K.property)

include hTor in
/-- **Stacks 0E5C.**  For a cartesian square of quasi-compact quasi-separated algebraic spaces
with `X` and `Y'` Tor independent over `Y`, the base change transformation
`Rg'_* ∘ a' ⟶ a ∘ Rg_*` of Stacks 0E5B is an isomorphism. -/
@[stacks 0E5C]
theorem isIso_quasicoherentDerivedRightAdjointBaseChange :
    IsIso (quasicoherentDerivedRightAdjointBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs) := by
  have := isIso_squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs hTor
  unfold quasicoherentDerivedRightAdjointBaseChange
  infer_instance

include hTor in
/-- **The base change map `L(g')^* ∘ a ⟶ a' ∘ Lg^*`** (Stacks 0E5D) of a cartesian square of
quasi-compact quasi-separated algebraic spaces with `X` and `Y'` Tor independent over `Y`:
the unit of `Lg^* ⊣ Rg_*`, the inverse of the isomorphism of Stacks 0E5C, and the counit of
`L(g')^* ⊣ Rg'_*`. -/
@[stacks 0E5D]
def quasicoherentDerivedRightAdjointBaseChangeMap :
    quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs ⋙ quasicoherentDerivedModulePullback g' ⟶
      quasicoherentDerivedModulePullback g ⋙
        quasicoherentDerivedRightAdjoint hZ f'
          (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
          (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs :=
  letI : IsIso (RightAdjointBaseChange.rightAdjointMate
      (squareAdjF hZ hXqc hXqs hYqs) (squareAdjF' hZ sq hXqc hXqs hYqs hY'qc hY'qs)
      (squareAdjG hZ hYqs hY'qc hY'qs) (squareAdjG' hZ sq hXqc hXqs hYqs hY'qc hY'qs)
      (squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs)) :=
    isIso_quasicoherentDerivedRightAdjointBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs hTor
  RightAdjointBaseChange.map
      (squareAdjF hZ hXqc hXqs hYqs) (squareAdjF' hZ sq hXqc hXqs hYqs hY'qc hY'qs)
      (squareAdjG hZ hYqs hY'qc hY'qs) (squareAdjG' hZ sq hXqc hXqs hYqs hY'qc hY'qs)
      (squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs)

/-- The mate of the base change map of a Tor independent square is invertible (Stacks 0E5C),
stated for the explicit adjunctions of the square. -/
private theorem isIso_rightAdjointMate_squareBaseChange
    (hTor : TorIndependent X.2 Y'.2 Y.2 f.hom g.hom) :
    IsIso (RightAdjointBaseChange.rightAdjointMate
      (squareAdjF hZ hXqc hXqs hYqs) (squareAdjF' hZ sq hXqc hXqs hYqs hY'qc hY'qs)
      (squareAdjG hZ hYqs hY'qc hY'qs) (squareAdjG' hZ sq hXqc hXqs hYqs hY'qc hY'qs)
      (squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs)) :=
  isIso_quasicoherentDerivedRightAdjointBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs hTor

include hTor in
/-- **Stacks 0E5L.**  The trace maps and the base change maps agree: `Lg^*` of the trace
`Rf_* a K ⟶ K` is the base change map `β` at `a K`, followed by `Rf'_*` of the map `α` of
Stacks 0E5D and the trace `Rf'_* a' (Lg^* K) ⟶ Lg^* K`. -/
@[stacks 0E5L]
theorem quasicoherentDerivedRightAdjointBaseChangeMap_trace (K) :
    (squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs).app
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K) ≫
        (quasicoherentDerivedPushforward B S hS f'
          (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y'.2 hY'qs
            (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc) f'.hom)
          (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
            (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) f'.hom)).map
          ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sq hXqc hXqs hYqs hY'qc hY'qs
            hTor).app K) ≫
        (squareAdjF' hZ sq hXqc hXqs hYqs hY'qc hY'qs).counit.app
          ((quasicoherentDerivedModulePullback g).obj K) =
      (quasicoherentDerivedModulePullback g).map
        ((squareAdjF hZ hXqc hXqs hYqs).counit.app K) :=
  let := isIso_rightAdjointMate_squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs hTor
  RightAdjointBaseChange.map_counit _ _ _ _ _ K

include hTor in
/-- **Stacks 0E5M.**  The units and the base change maps agree: `L(g')^*` of the unit
`K ⟶ a (Rf_* K)`, followed by the map `α` of Stacks 0E5D at `Rf_* K` and by `a'` of the base
change map `β`, is the unit `L(g')^* K ⟶ a' (Rf'_* L(g')^* K)`. -/
@[stacks 0E5M]
theorem quasicoherentDerivedRightAdjointBaseChangeMap_unit (K) :
    (quasicoherentDerivedModulePullback g').map ((squareAdjF hZ hXqc hXqs hYqs).unit.app K) ≫
        (quasicoherentDerivedRightAdjointBaseChangeMap hZ sq hXqc hXqs hYqs hY'qc hY'qs
          hTor).app ((quasicoherentDerivedPushforward B S hS f
            (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
            (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs
              f.hom)).obj K) ≫
        (quasicoherentDerivedRightAdjoint hZ f'
          (isQuasiCompactSpace_of_isPullback hZ sq hXqc hYqs hY'qc)
          (isAbsolutelyQuasiSeparated_of_isPullback hZ sq hXqs hY'qs) hY'qs).map
          ((squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs).app K) =
      (squareAdjF' hZ sq hXqc hXqs hYqs hY'qc hY'qs).unit.app
        ((quasicoherentDerivedModulePullback g').obj K) :=
  let := isIso_rightAdjointMate_squareBaseChange hZ sq hXqc hXqs hYqs hY'qc hY'qs hTor
  RightAdjointBaseChange.unit_map _ _ _ _ _ K

end Square

section Vertical

variable {X X' Y Y' Z Z' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y ⟶ Z} {f' : X' ⟶ Y'}
  {g' : Y' ⟶ Z'} {k : X' ⟶ X} {l : Y' ⟶ Y} {m : Z' ⟶ Z}
  (sqt : IsPullback k f' f l) (sqb : IsPullback l g' g m)
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqc : IsQuasiCompactSpace B S hS Y.1) (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
  (hZqs : IsAbsolutelyQuasiSeparated B S hS hZ Z.1)
  (hY'qc : IsQuasiCompactSpace B S hS Y'.1) (hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ Y'.1)
  (hZ'qc : IsQuasiCompactSpace B S hS Z'.1) (hZ'qs : IsAbsolutelyQuasiSeparated B S hS hZ Z'.1)
  (hTt : TorIndependent X.2 Y'.2 Y.2 f.hom l.hom)
  (hTb : TorIndependent Y.2 Z'.2 Z.2 g.hom m.hom)

include sqb hTt hTb in
/-- The outer rectangle of the two squares of Stacks 0E5E is Tor independent. -/
theorem torIndependent_rectangle_vertical :
    TorIndependent X.2 Z'.2 Z.2 (f ≫ g).hom m.hom :=
  torIndependent_comp_of_isPullback B S hS f g m l g'
    (AlgebraicSpaces.isPullback_hom B S hS sqb) hTb hTt

/-- **Stacks 0E5E.**  For two vertically stacked cartesian squares of quasi-compact
quasi-separated algebraic spaces, with `f` and `l` as well as `g` and `m` Tor independent, the
base change map of Stacks 0E5D for the outer rectangle is the composite of those of the two
squares, read through the identifications `a ∘ b = c` and `a' ∘ b' = c'` of the right adjoints
of `R(g ∘ f)_* = Rg_* ∘ Rf_*` and `R(g' ∘ f')_* = Rg'_* ∘ Rf'_*`. -/
@[stacks 0E5E]
theorem quasicoherentDerivedRightAdjointBaseChangeMap_vertical (K) :
    (quasicoherentDerivedRightAdjointBaseChangeMap hZ (sqt.paste_vert sqb) hXqc hXqs hZqs
        hZ'qc hZ'qs (torIndependent_rectangle_vertical sqb hTt hTb)).app K =
      (quasicoherentDerivedModulePullback k).map
          ((RightAdjointBaseChange.rightAdjointCompIso (squareAdjF hZ hXqc hXqs hYqs)
            (squareAdjF hZ hYqc hYqs hZqs) (squareAdjF hZ hXqc hXqs hZqs)
            (quasicoherentDerivedPushforwardCompIso f g
              (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y.2 hYqs hXqc f.hom)
              (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs f.hom)
              (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Z.2 hZqs hYqc g.hom)
              (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y.2 hYqs g.hom)
              (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Z.2 hZqs hXqc (f ≫ g).hom)
              (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X.2 hXqs
                (f ≫ g).hom))).inv.app K) ≫
        (quasicoherentDerivedRightAdjointBaseChangeMap hZ sqt hXqc hXqs hYqs hY'qc hY'qs
          hTt).app ((quasicoherentDerivedRightAdjoint hZ g hYqc hYqs hZqs).obj K) ≫
        (quasicoherentDerivedRightAdjoint hZ f'
            (isQuasiCompactSpace_of_isPullback hZ sqt hXqc hYqs hY'qc)
            (isAbsolutelyQuasiSeparated_of_isPullback hZ sqt hXqs hY'qs) hY'qs).map
          ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sqb hYqc hYqs hZqs hZ'qc hZ'qs
            hTb).app K) ≫
        (RightAdjointBaseChange.rightAdjointCompIso (squareAdjF' hZ sqt hXqc hXqs hYqs hY'qc hY'qs)
          (squareAdjF' hZ sqb hYqc hYqs hZqs hZ'qc hZ'qs)
          (squareAdjF' hZ (sqt.paste_vert sqb) hXqc hXqs hZqs hZ'qc hZ'qs)
          (quasicoherentDerivedPushforwardCompIso f' g'
            (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Y'.2 hY'qs
              (isQuasiCompactSpace_of_isPullback hZ sqt hXqc hYqs hY'qc) f'.hom)
            (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
              (isAbsolutelyQuasiSeparated_of_isPullback hZ sqt hXqs hY'qs) f'.hom)
            (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Z'.2 hZ'qs hY'qc g'.hom)
            (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ Y'.2 hY'qs g'.hom)
            (isQuasiCompact_of_isQuasiCompactSpace B S hS hZ Z'.2 hZ'qs
              (isQuasiCompactSpace_of_isPullback hZ sqt hXqc hYqs hY'qc) (f' ≫ g').hom)
            (isQuasiSeparated_of_isAbsolutelyQuasiSeparated_source B S hS hZ X'.2
              (isAbsolutelyQuasiSeparated_of_isPullback hZ sqt hXqs hY'qs)
              (f' ≫ g').hom))).hom.app ((quasicoherentDerivedModulePullback m).obj K) := by
  have := isIso_squareBaseChange hZ sqt hXqc hXqs hYqs hY'qc hY'qs hTt
  have := isIso_squareBaseChange hZ sqb hYqc hYqs hZqs hZ'qc hZ'qs hTb
  have := isIso_squareBaseChange hZ (sqt.paste_vert sqb) hXqc hXqs hZqs hZ'qc hZ'qs
    (torIndependent_rectangle_vertical sqb hTt hTb)
  exact RightAdjointBaseChange.map_app_vertical _ _ _ _ _ _
    (squareAdjG' hZ sqt hXqc hXqs hYqs hY'qc hY'qs) (squareAdjG hZ hYqs hY'qc hY'qs)
    (squareAdjG hZ hZqs hZ'qc hZ'qs) _ _ _ _ _
    (quasicoherentDerivedBaseChange_vertical f g f' g' k l m sqt.w sqb.w _ _ _ _ _ _ _ _ _ _ _ _)
    K

end Vertical

section Horizontal

variable {X X' X'' Y Y' Y'' : AlgebraicSpaces B S hS} {f : X ⟶ Y} {f' : X' ⟶ Y'}
  {f'' : X'' ⟶ Y''} {g : X' ⟶ X} {g' : X'' ⟶ X'} {h : Y' ⟶ Y} {h' : Y'' ⟶ Y'}
  (sqr : IsPullback g f' f h) (sql : IsPullback g' f'' f' h')
  (hXqc : IsQuasiCompactSpace B S hS X.1) (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
  (hYqs : IsAbsolutelyQuasiSeparated B S hS hZ Y.1)
  (hX'qc : IsQuasiCompactSpace B S hS X'.1) (hX'qs : IsAbsolutelyQuasiSeparated B S hS hZ X'.1)
  (hY'qc : IsQuasiCompactSpace B S hS Y'.1) (hY'qs : IsAbsolutelyQuasiSeparated B S hS hZ Y'.1)
  (hY''qc : IsQuasiCompactSpace B S hS Y''.1)
  (hY''qs : IsAbsolutelyQuasiSeparated B S hS hZ Y''.1)
  (hTr : TorIndependent X.2 Y'.2 Y.2 f.hom h.hom)
  (hTl : TorIndependent X'.2 Y''.2 Y'.2 f'.hom h'.hom)

include sqr hTr hTl in
/-- The outer rectangle of the two squares of Stacks 0E5F is Tor independent. -/
theorem torIndependent_rectangle_horizontal :
    TorIndependent X.2 Y''.2 Y.2 f.hom (h' ≫ h).hom :=
  torIndependent_comp_right_of_isPullback B S hS f h h' g f'
    (AlgebraicSpaces.isPullback_hom B S hS sqr) hTr hTl

/-- **Stacks 0E5F.**  For two horizontally composed cartesian squares of quasi-compact
quasi-separated algebraic spaces, with `f` and `h` as well as `f'` and `h'` Tor independent, the
base change map of Stacks 0E5D for the outer rectangle is the composite of those of the two
squares, read through `L(g ∘ g')^* = L(g')^* ∘ Lg^*` and `L(h ∘ h')^* = L(h')^* ∘ Lh^*`. -/
@[stacks 0E5F]
theorem quasicoherentDerivedRightAdjointBaseChangeMap_horizontal (K) :
    (quasicoherentDerivedRightAdjointBaseChangeMap hZ (sql.paste_horiz sqr) hXqc hXqs hYqs
        hY''qc hY''qs (torIndependent_rectangle_horizontal sqr hTr hTl)).app K =
      (quasicoherentDerivedModulePullbackCompIso g' g).inv.app
          ((quasicoherentDerivedRightAdjoint hZ f hXqc hXqs hYqs).obj K) ≫
        (quasicoherentDerivedModulePullback g').map
          ((quasicoherentDerivedRightAdjointBaseChangeMap hZ sqr hXqc hXqs hYqs hY'qc hY'qs
            hTr).app K) ≫
        (quasicoherentDerivedRightAdjointBaseChangeMap hZ sql hX'qc hX'qs hY'qs hY''qc
          hY''qs hTl).app ((quasicoherentDerivedModulePullback h).obj K) ≫
        (quasicoherentDerivedRightAdjoint hZ f''
          (isQuasiCompactSpace_of_isPullback hZ (sql.paste_horiz sqr) hXqc hYqs hY''qc)
          (isAbsolutelyQuasiSeparated_of_isPullback hZ (sql.paste_horiz sqr) hXqs hY''qs)
          hY''qs).map ((quasicoherentDerivedModulePullbackCompIso h' h).hom.app K) := by
  have := isIso_squareBaseChange hZ sqr hXqc hXqs hYqs hY'qc hY'qs hTr
  have := isIso_squareBaseChange hZ sql hX'qc hX'qs hY'qs hY''qc hY''qs hTl
  have := isIso_squareBaseChange hZ (sql.paste_horiz sqr) hXqc hXqs hYqs hY''qc hY''qs
    (torIndependent_rectangle_horizontal sqr hTr hTl)
  exact RightAdjointBaseChange.map_app_horizontal _ _ _ _ _ _ _ _ _ _ _ _
    (quasicoherentDerivedModulePullbackCompIso h' h)
    (quasicoherentDerivedModulePullbackCompIso g' g)
    (quasicoherentDerivedBaseChange_horizontal f f' f'' g g' h h' sqr.w sql.w _ _ _ _ _ _) K

end Horizontal

end AlgebraicGeometry.Space

end
