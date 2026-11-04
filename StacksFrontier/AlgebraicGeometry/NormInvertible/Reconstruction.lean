module

public import StacksFrontier.AlgebraicGeometry.NormInvertible.Coboundary
public import StacksFrontier.AlgebraicGeometry.NormInvertible.LocalIso

/-!
# A module is reconstructed from the transition cocycle of a family of local generators

Let `L` be a sheaf of `𝒪_X`-modules on a ringed space and let `g i` be a generator of `L` on
`U i`, for a family of opens `U` covering `X`. The transition units
`t_{ij} = g i / g j` form a `Stacks.SheafOfModules.UnitTransitionCocycle`, and the module glued
from that cocycle is `L` itself: `L ≅ (generatorCocycle L g).glue`.

This is the converse direction of the cocycle model of
`StacksFrontier/AlgebraicGeometry/NormInvertible/Cocycle.lean`. That file builds a module out
of a cocycle, which is all the norm construction of
[Stacks, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY) needs; nothing there sends a
module back to a cocycle, so a construction carried out on local charts could not be transported
back to the module it came from. `glueIso` below is what makes the model two-sided, and
`isoOfTransitionEq` is the form a chart construction consumes: **two modules with local
generators having the same transition units on the same cover are isomorphic.**

## Main definitions

* `Stacks.SheafOfModules.generatorFrame` and `Stacks.SheafOfModules.generatorCoord`:
  multiplication by a local generator, as a linear equivalence `𝒪_X(V) ≃ L(V)`, and its inverse
  — the coordinate of a section in that frame.
* `Stacks.SheafOfModules.generatorCocycle`: the transition cocycle of a family of local
  generators.
* `Stacks.SheafOfModules.chartCoords`: the coordinates of a section of `L` over `W` in the chart
  frames, a compatible family for `generatorCocycle`.
* `Stacks.SheafOfModules.reconstructionApp`: those coordinates, as a linear map into the
  compatible families.

## Main results

* `Stacks.SheafOfModules.glueIso`: **`L ≅ (generatorCocycle L g).glue`.**
* `Stacks.SheafOfModules.isoOfTransitionEq`: two modules whose chart generators have the
  same transition units on the same cover are isomorphic.
* `Stacks.SheafOfModules.isoOfIsCoboundaryTwist`: the same conclusion when the two transition
  cocycles differ by a coboundary, through
  `Stacks.SheafOfModules.UnitTransitionCocycle.glueIsoOfCoboundaryTwist`.
* `Stacks.SheafOfModules.reconstructionApp_bijective`: the coordinate map is bijective on
  sections over every open.
* `Stacks.SheafOfModules.generatorCoord_restrict`: the coordinate of a section commutes with
  restriction, and `Stacks.SheafOfModules.chartCoords_restrictLe` is the chart form of that.

## Implementation notes

**Orientation.** `(generatorCocycle L g).transition i j` is `g i / g j`, the ratio *from* the
`j`-th frame *to* the `i`-th, and not the other way round. That is forced, not chosen: the
compatibility condition cut out by `UnitTransitionCocycle.sectionsSubmodule` reads
`t_{ij} · s_i| = s_j|`, and the coordinates of a section satisfy
`(g i / g j) · (coordinate in frame i) = (coordinate in frame j)`. The same orientation is used
by `Stacks.Divisors.normTransitionCocycle`, whose own implementation notes record the
caution.

**Two spellings of the ring of sections, and why every proof here is in term mode.** The
cocycle development states the transition units in `(X.presheaf.obj (op V))ˣ`, over
`CommRingCat`, while the generator calculus of `NormInvertible/Generators.lean` states them in
`((structureSheaf X.sheaf).obj.obj (op V))ˣ`, over `RingCat` — `structureSheaf` forgets
commutativity, so the two `Monoid` instances are definitionally equal but syntactically
different terms. Elaboration crosses that freely; `rw` does not, because it builds its motive at
`implicit` transparency. Every field of `generatorCocycle` and the membership proof
`chartCoords_mem` are therefore written as `Eq.trans`/`congrArg` chains rather than with `rw`,
which is also the idiom of the surrounding files. Commutativity is used exactly twice — once per
`mul_comm` — and in both places the goal supplies the `CommRingCat` spelling, which is the only
spelling in which commutativity is available at all.

`sectionsSubmoduleModule` is a `local instance` re-ascribing the module structure on the
compatible families to the `RingCat` spelling. The instance is *present* on
`UnitTransitionCocycle.gluedPresheafOfModules.obj`, which is built as
`ModuleCat.of (X.presheaf.obj V) _` and crosses to the expected
`ModuleCat ((structureSheaf X.sheaf).obj.obj V)`; it is simply not *synthesizable*, so a
`→ₗ[(structureSheaf X.sheaf).obj.obj (op W)]` in a declaration's type cannot be elaborated
without it. It is `inferInstanceAs` of the instance already there, so it introduces no diamond.

**Where the sheaf condition enters.** Injectivity of the coordinate map is separatedness of `L`
and surjectivity is gluing for `L`, both taken from
`StacksFrontier/AlgebraicGeometry/NormInvertible/LocalIso.lean`. The alternative — building the
morphism and appealing to `bijective_app_of_le_cover` — would still use the same two facts and
would additionally need the comparison of the chart trivializations, so it is not cheaper.

## References

* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : RingedSpace.{u, u}}
  (L : _root_.SheafOfModules.{u} (structureSheaf X.sheaf))

/-! ### The coordinate of a section in a local frame -/

/-- Multiplication by a local generator is bijective on the open the generator lives on. -/
theorem bijective_smul_generator {V : Opens X.carrier} (s : GeneratorSections X L V) :
    Function.Bijective (fun r : (structureSheaf X.sheaf).obj.obj (op V) => r • s.val) := by
  have h := s.property V le_rfl
  rwa [generator_restrict_self L V s] at h

/-- Multiplication by a local generator, as a linear equivalence from the functions on the open
to the sections of the module. -/
noncomputable def generatorFrame {V : Opens X.carrier} (s : GeneratorSections X L V) :
    (structureSheaf X.sheaf).obj.obj (op V) ≃ₗ[(structureSheaf X.sheaf).obj.obj (op V)]
      L.val.obj (op V) :=
  LinearEquiv.ofBijective
    (LinearMap.toSpanSingleton _ _ s.val) (bijective_smul_generator L s)

/-- The local frame sends a function `r` to `r • s`. -/
@[simp]
theorem generatorFrame_apply {V : Opens X.carrier} (s : GeneratorSections X L V)
    (r : (structureSheaf X.sheaf).obj.obj (op V)) : generatorFrame L s r = r • s.val :=
  rfl

/-- The coordinate of a section of `L` in a local frame. -/
noncomputable def generatorCoord {V : Opens X.carrier} (s : GeneratorSections X L V) :
    L.val.obj (op V) ≃ₗ[(structureSheaf X.sheaf).obj.obj (op V)]
      (structureSheaf X.sheaf).obj.obj (op V) :=
  (generatorFrame L s).symm

/-- A section is its coordinate in a local frame times the generator. -/
@[simp]
theorem generatorCoord_smul_self {V : Opens X.carrier} (s : GeneratorSections X L V)
    (x : L.val.obj (op V)) : generatorCoord L s x • s.val = x :=
  (generatorFrame L s).apply_symm_apply x

/-- The coordinate is characterized by the equation defining it. -/
theorem generatorCoord_unique {V : Opens X.carrier} (s : GeneratorSections X L V)
    (x : L.val.obj (op V)) (a : (structureSheaf X.sheaf).obj.obj (op V))
    (ha : a • s.val = x) : generatorCoord L s x = a := by
  rw [← ha]
  exact (generatorFrame L s).symm_apply_apply a

/-- The coordinate of a section commutes with restriction. -/
theorem generatorCoord_restrict {V W : Opens X.carrier} (h : W ≤ V)
    (s : GeneratorSections X L V) (x : L.val.obj (op V)) :
    generatorCoord L (generatorRestrict L h s) (L.val.map (homOfLE h).op x) =
      (structureSheaf X.sheaf).obj.map (homOfLE h).op (generatorCoord L s x) := by
  refine generatorCoord_unique L _ _ _ ?_
  rw [generatorRestrict_val, PresheafOfModules.restrictₛₗ_apply]
  exact (PresheafOfModules.map_smul L.val (homOfLE h).op (generatorCoord L s x) s.val).symm.trans
    (congrArg (fun z => L.val.map (homOfLE h).op z) (generatorCoord_smul_self L s x))

/-! ### The transition cocycle of a family of local generators -/

section Cocycle

variable {ι : Type u} {U : ι → Opens X.carrier}

attribute [local instance] UnitTransitionCocycle.sectionsProductModule

/-- The module structure on the compatible families of local coordinates, at the `RingCat`
spelling of the ring of sections. This is `inferInstanceAs` of the structure
`UnitTransitionCocycle.gluedPresheafOfModules` already carries; it is declared only because
instance search does not cross between the two spellings. -/
noncomputable local instance sectionsSubmoduleModule
    (D : UnitTransitionCocycle X U) (W : Opens X.carrier) :
    Module ((structureSheaf X.sheaf).obj.obj (op W)) (D.sectionsSubmodule W) :=
  inferInstanceAs (Module (X.presheaf.obj (op W)) _)

/-- **The transition cocycle of a family of local generators.** The transition from the `i`-th
chart to the `j`-th is the ratio of the `i`-th generator to the `j`-th. -/
noncomputable def generatorCocycle (g : ∀ i, GeneratorSections X L (U i)) :
    UnitTransitionCocycle X U where
  transition i j V hi hj :=
    generatorRatioUnit L V (generatorRestrict L hj (g j)) (generatorRestrict L hi (g i))
  restrict {i j _V W} hi hj h :=
    (generatorRatioUnit_restrict L h (generatorRestrict L hj (g j))
          (generatorRestrict L hi (g i))).symm.trans
      (congrArg₂ (generatorRatioUnit L W)
        (generatorRestrict_trans L hj h (g j)) (generatorRestrict_trans L hi h (g i)))
  symm _i _j V _hi _hj := generatorRatioUnit_symm L V _ _
  cocycle i j k V hi hj hk :=
    (mul_comm _ _).trans (generatorRatioUnit_comp L V (generatorRestrict L hk (g k))
      (generatorRestrict L hj (g j)) (generatorRestrict L hi (g i)))

/-- The transition unit of `generatorCocycle L g` from the `i`-th chart to the `j`-th on `V`
is the ratio of the restriction of `g i` to that of `g j`. -/
@[simp]
theorem generatorCocycle_transition (g : ∀ i, GeneratorSections X L (U i)) (i j : ι)
    (V : Opens X.carrier) (hi : V ≤ U i) (hj : V ≤ U j) :
    (generatorCocycle L g).transition i j V hi hj =
      generatorRatioUnit L V (generatorRestrict L hj (g j)) (generatorRestrict L hi (g i)) :=
  rfl

/-! ### The coordinates of a section in the chart frames -/

/-- The coordinates of a section of `L` over `W` in the chart frames. -/
noncomputable def chartCoords (g : ∀ i, GeneratorSections X L (U i)) (W : Opens X.carrier)
    (x : L.val.obj (op W)) (i : ι) :
    (structureSheaf X.sheaf).obj.obj (op (W ⊓ U i)) :=
  generatorCoord L (generatorRestrict L (inf_le_right : W ⊓ U i ≤ U i) (g i))
    (L.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op x)

/-- The chart coordinates of a section, restricted to any open inside the chart. The
containments `Z ≤ W` and `Z ≤ U i` are taken as arguments rather than composed from `hZ`, so
that a consumer can supply the proof terms its own goal carries. -/
theorem chartCoords_restrictLe (g : ∀ i, GeneratorSections X L (U i)) {W : Opens X.carrier}
    (i : ι) {Z : Opens X.carrier} (hZ : Z ≤ W ⊓ U i) (hZW : Z ≤ W) (hZi : Z ≤ U i)
    (x : L.val.obj (op W)) :
    (structureSheaf X.sheaf).obj.map (homOfLE hZ).op (chartCoords L g W x i) =
      generatorCoord L (generatorRestrict L hZi (g i)) (L.val.map (homOfLE hZW).op x) :=
  (generatorCoord_restrict L hZ (generatorRestrict L (inf_le_right : W ⊓ U i ≤ U i) (g i))
        (L.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op x)).symm.trans
    (congrArg₂ (fun (s : GeneratorSections X L Z) (y : L.val.obj (op Z)) => generatorCoord L s y)
      (generatorRestrict_trans L (inf_le_right : W ⊓ U i ≤ U i) hZ (g i))
      (map_map_apply L (inf_le_left : W ⊓ U i ≤ W) hZ x))

/-- **The chart coordinates of a section are a compatible family for the generator cocycle.** -/
theorem chartCoords_mem (g : ∀ i, GeneratorSections X L (U i)) (W : Opens X.carrier)
    (x : L.val.obj (op W)) :
    chartCoords L g W x ∈ (generatorCocycle L g).sectionsSubmodule W := by
  intro i j
  have hZW : W ⊓ U i ⊓ (W ⊓ U j) ≤ W := inf_le_left.trans inf_le_left
  have ha := chartCoords_restrictLe L g i (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i)
    hZW (inf_le_left.trans inf_le_right) x
  have hb := chartCoords_restrictLe L g j (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j)
    hZW (inf_le_right.trans inf_le_right) x
  have hA := generatorRatio_spec L (W ⊓ U i ⊓ (W ⊓ U j))
    (generatorRestrict L (inf_le_right.trans inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ U j) (g j))
    (generatorRestrict L (inf_le_left.trans inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ U i) (g i))
  have key : generatorCoord L
      (generatorRestrict L (inf_le_right.trans inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ U j) (g j))
      (L.val.map (homOfLE hZW).op x) =
    (structureSheaf X.sheaf).obj.map
        (homOfLE (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op (chartCoords L g W x i) *
      generatorRatio L (W ⊓ U i ⊓ (W ⊓ U j))
        (generatorRestrict L (inf_le_right.trans inf_le_right) (g j))
        (generatorRestrict L (inf_le_left.trans inf_le_right) (g i)) := by
    refine generatorCoord_unique L _ _ _ ?_
    rw [mul_smul, ← hA, ha]
    exact generatorCoord_smul_self L _ _
  exact (mul_comm _ _).trans (key.symm.trans hb.symm)

/-- The chart coordinates of a sum are the sum of the chart coordinates. -/
theorem chartCoords_add (g : ∀ i, GeneratorSections X L (U i)) (W : Opens X.carrier)
    (x y : L.val.obj (op W)) (i : ι) :
    chartCoords L g W (x + y) i = chartCoords L g W x i + chartCoords L g W y i :=
  (congrArg
      (fun z => generatorCoord L
        (generatorRestrict L (inf_le_right : W ⊓ U i ≤ U i) (g i)) z)
      (map_add (L.val.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op).hom x y)).trans
    (map_add (generatorCoord L (generatorRestrict L (inf_le_right : W ⊓ U i ≤ U i) (g i))) _ _)

/-- The chart coordinates of `r • x` are those of `x` multiplied by the restriction of `r`. -/
theorem chartCoords_smul (g : ∀ i, GeneratorSections X L (U i)) (W : Opens X.carrier)
    (r : (structureSheaf X.sheaf).obj.obj (op W)) (x : L.val.obj (op W)) (i : ι) :
    chartCoords L g W (r • x) i =
      (structureSheaf X.sheaf).obj.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r *
        chartCoords L g W x i :=
  (congrArg
      (fun z => generatorCoord L
        (generatorRestrict L (inf_le_right : W ⊓ U i ≤ U i) (g i)) z)
      (PresheafOfModules.map_smul L.val
        (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op r x)).trans
    (map_smul (generatorCoord L (generatorRestrict L (inf_le_right : W ⊓ U i ≤ U i) (g i))) _ _)

/-- The chart coordinates of a section of `L` over `W`, as a linear map into the compatible
families of the generator cocycle. -/
noncomputable def reconstructionApp (g : ∀ i, GeneratorSections X L (U i))
    (W : Opens X.carrier) :
    L.val.obj (op W) →ₗ[(structureSheaf X.sheaf).obj.obj (op W)]
      (generatorCocycle L g).sectionsSubmodule W where
  toFun x := ⟨chartCoords L g W x, chartCoords_mem L g W x⟩
  map_add' x y := Subtype.ext (funext fun i => chartCoords_add L g W x y i)
  map_smul' r x := Subtype.ext (funext fun i => chartCoords_smul L g W r x i)

/-- The `i`-th component of `reconstructionApp L g W x` is the `i`-th chart coordinate of
`x`. -/
@[simp]
theorem reconstructionApp_val (g : ∀ i, GeneratorSections X L (U i)) (W : Opens X.carrier)
    (x : L.val.obj (op W)) (i : ι) :
    (reconstructionApp L g W x).val i = chartCoords L g W x i :=
  rfl

/-! ### Bijectivity of the coordinate map -/

/-- The intersections of an open with the members of a covering family cover it. -/
theorem le_iSup_inf_of_coversTop {ι : Type u} {U : ι → Opens X.carrier}
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) (W : Opens X.carrier) : W ≤ ⨆ i, W ⊓ U i := by
  rw [← inf_iSup_eq]
  exact le_inf le_rfl (le_top.trans hU)

/-- On a covering family, a section of `L` is determined by its chart coordinates. -/
theorem reconstructionApp_injective (g : ∀ i, GeneratorSections X L (U i))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) (W : Opens X.carrier) :
    Function.Injective (reconstructionApp L g W) := by
  intro x y hxy
  refine section_eq_of_locally_eq L (fun i => W ⊓ U i) W (fun _ => inf_le_left)
    (le_iSup_inf_of_coversTop hU W) x y fun i => ?_
  exact (generatorCoord L (generatorRestrict L (inf_le_right : W ⊓ U i ≤ U i) (g i))).injective
    (congrArg (fun s : (generatorCocycle L g).sectionsSubmodule W => s.val i) hxy)

/-- On a covering family, every compatible family for the generator cocycle is the family of
chart coordinates of a section of `L`. -/
theorem reconstructionApp_surjective (g : ∀ i, GeneratorSections X L (U i))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) (W : Opens X.carrier) :
    Function.Surjective (reconstructionApp L g W) := by
  intro s
  have hcompat : ∀ i j,
      L.val.map (homOfLE (inf_le_left : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U i)).op
          (generatorFrame L (generatorRestrict L (inf_le_right : W ⊓ U i ≤ U i) (g i))
            (s.val i)) =
        L.val.map (homOfLE (inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U j)).op
          (generatorFrame L (generatorRestrict L (inf_le_right : W ⊓ U j ≤ U j) (g j))
            (s.val j)) := by
    intro i j
    have hA := generatorRatio_spec L (W ⊓ U i ⊓ (W ⊓ U j))
      (generatorRestrict L (inf_le_right.trans inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ U j) (g j))
      (generatorRestrict L (inf_le_left.trans inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ U i) (g i))
    have hres : ∀ (k : ι) (hk : W ⊓ U i ⊓ (W ⊓ U j) ≤ W ⊓ U k),
        L.val.map (homOfLE hk).op
            (generatorFrame L (generatorRestrict L (inf_le_right : W ⊓ U k ≤ U k) (g k))
              (s.val k)) =
          (structureSheaf X.sheaf).obj.map (homOfLE hk).op (s.val k) •
            (generatorRestrict L (hk.trans inf_le_right) (g k)).val := by
      intro k hk
      have hg := congrArg (fun t : GeneratorSections X L (W ⊓ U i ⊓ (W ⊓ U j)) => t.val)
        (generatorRestrict_trans L (inf_le_right : W ⊓ U k ≤ U k) hk (g k))
      rw [generatorRestrict_val, PresheafOfModules.restrictₛₗ_apply] at hg
      exact (PresheafOfModules.map_smul L.val (homOfLE hk).op (s.val k) _).trans
        (congrArg _ hg)
    refine (hres i inf_le_left).trans (Eq.trans ?_ (hres j inf_le_right).symm)
    rw [hA]
    exact (smul_smul _ _ _).trans
      (congrArg (fun r : (structureSheaf X.sheaf).obj.obj (op (W ⊓ U i ⊓ (W ⊓ U j))) =>
        r • (generatorRestrict L
          (inf_le_right.trans inf_le_right : W ⊓ U i ⊓ (W ⊓ U j) ≤ U j) (g j)).val)
        ((mul_comm _ _).trans (s.property i j)))
  obtain ⟨x, hx, -⟩ := existsUnique_glue L (fun i => W ⊓ U i) W (fun _ => inf_le_left)
    (le_iSup_inf_of_coversTop hU W)
    (fun i => generatorFrame L (generatorRestrict L (inf_le_right : W ⊓ U i ≤ U i) (g i))
      (s.val i)) hcompat
  refine ⟨x, Subtype.ext (funext fun i => ?_)⟩
  exact (congrArg (generatorCoord L
    (generatorRestrict L (inf_le_right : W ⊓ U i ≤ U i) (g i))) (hx i)).trans
    (generatorCoord_unique L _ _ _ rfl)

/-- On a covering family, the chart-coordinate map `reconstructionApp L g W` is bijective. -/
theorem reconstructionApp_bijective (g : ∀ i, GeneratorSections X L (U i))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) (W : Opens X.carrier) :
    Function.Bijective (reconstructionApp L g W) :=
  ⟨reconstructionApp_injective L g hU W, reconstructionApp_surjective L g hU W⟩

/-! ### The reconstruction isomorphism -/

/-- The chart coordinates, as a linear equivalence onto the compatible families. -/
noncomputable def reconstructionEquiv (g : ∀ i, GeneratorSections X L (U i))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) (W : Opens X.carrier) :
    L.val.obj (op W) ≃ₗ[(structureSheaf X.sheaf).obj.obj (op W)]
      (generatorCocycle L g).sectionsSubmodule W :=
  LinearEquiv.ofBijective (reconstructionApp L g W) (reconstructionApp_bijective L g hU W)

/-- The `i`-th component of `reconstructionEquiv L g hU W x` is the `i`-th chart coordinate of
`x`. -/
@[simp]
theorem reconstructionEquiv_val (g : ∀ i, GeneratorSections X L (U i))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) (W : Opens X.carrier) (x : L.val.obj (op W))
    (i : ι) : (reconstructionEquiv L g hU W x).val i = chartCoords L g W x i :=
  rfl

/-- The chart-coordinate equivalence commutes with restriction along `W ≤ V`. -/
theorem reconstructionEquiv_restrict (g : ∀ i, GeneratorSections X L (U i))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) {V W : Opens X.carrier} (h : W ≤ V)
    (x : L.val.obj (op V)) :
    reconstructionEquiv L g hU W (L.val.map (homOfLE h).op x) =
      (generatorCocycle L g).sectionsMap h (reconstructionEquiv L g hU V x) := by
  refine Subtype.ext (funext fun i => ?_)
  refine Eq.trans ?_ (UnitTransitionCocycle.sectionsMap_val (generatorCocycle L g) h
    (reconstructionEquiv L g hU V x) i).symm
  refine Eq.trans ?_ (chartCoords_restrictLe L g i (inf_le_inf_right (U i) h)
    ((inf_le_left : W ⊓ U i ≤ W).trans h) (inf_le_right : W ⊓ U i ≤ U i) x).symm
  exact congrArg (fun y => generatorCoord L
      (generatorRestrict L (inf_le_right : W ⊓ U i ≤ U i) (g i)) y)
    (map_map_apply L h (inf_le_left : W ⊓ U i ≤ W) x)

/-- **A module is the module glued from the transition cocycle of any family of local
generators on a covering family.** -/
noncomputable def glueIso (g : ∀ i, GeneratorSections X L (U i))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i) : L ≅ (generatorCocycle L g).glue := by
  apply (_root_.SheafOfModules.fullyFaithfulForget (structureSheaf X.sheaf)).preimageIso
  refine PresheafOfModules.isoMk
    (fun V => (reconstructionEquiv L g hU V.unop).toModuleIso) (fun {V W} f => ?_)
  apply ModuleCat.hom_ext
  ext x
  exact reconstructionEquiv_restrict L g hU f.unop.le x

/-! ### Comparing two modules through their transition units -/

/-- Equal transition units are a coboundary twist by the unit chart units. -/
theorem isCoboundaryTwist_one_of_transition_eq {D D' : UnitTransitionCocycle X U}
    (h : ∀ (i j : ι) (V : Opens X.carrier) (hi : V ≤ U i) (hj : V ≤ U j),
      D'.transition i j V hi hj = D.transition i j V hi hj) :
    UnitTransitionCocycle.IsCoboundaryTwist D D' (fun _ => 1) := by
  intro i j V hi hj
  rw [h i j V hi hj, map_one, map_one, inv_one, one_mul, one_mul]

/-- **Two modules whose local generators differ by a coboundary twist of their transition units
are isomorphic.** -/
noncomputable def isoOfIsCoboundaryTwist
    {M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)}
    (g : ∀ i, GeneratorSections X L (U i)) (k : ∀ i, GeneratorSections X M (U i))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i)
    {c : ∀ i, (X.presheaf.obj (op (U i)))ˣ}
    (hc : UnitTransitionCocycle.IsCoboundaryTwist
      (generatorCocycle L g) (generatorCocycle M k) c) : L ≅ M :=
  glueIso L g hU ≪≫ UnitTransitionCocycle.glueIsoOfCoboundaryTwist hc ≪≫ (glueIso M k hU).symm

/-- **Two modules whose local generators have the same transition units on the same covering
family are isomorphic.** This is the form in which a construction carried out chart by chart is
transported back to the modules it came from. -/
noncomputable def isoOfTransitionEq
    {M : _root_.SheafOfModules.{u} (structureSheaf X.sheaf)}
    (g : ∀ i, GeneratorSections X L (U i)) (k : ∀ i, GeneratorSections X M (U i))
    (hU : (⊤ : Opens X.carrier) ≤ ⨆ i, U i)
    (heq : ∀ (i j : ι) (V : Opens X.carrier) (hi : V ≤ U i) (hj : V ≤ U j),
      generatorRatioUnit L V (generatorRestrict L hj (g j)) (generatorRestrict L hi (g i)) =
        generatorRatioUnit M V (generatorRestrict M hj (k j)) (generatorRestrict M hi (k i))) :
    L ≅ M :=
  isoOfIsCoboundaryTwist L g k hU (c := fun _ => 1)
    (isCoboundaryTwist_one_of_transition_eq (D := generatorCocycle L g)
      (D' := generatorCocycle M k) (fun i j V hi hj => (heq i j V hi hj).symm))

end Cocycle

end Stacks.SheafOfModules
