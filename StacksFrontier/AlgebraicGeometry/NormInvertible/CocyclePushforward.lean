module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksFrontier.AlgebraicGeometry.NormInvertible.Cocycle

/-!
# Maps of glued modules from chartwise maps of functions

Let `f : Y' ⟶ Y` be a morphism of schemes, let `U : ι → Y.Opens` be a family of opens of the
target, and let `D` be a unit transition cocycle on `Y` for `U` and `D'` one on `Y'` for the
preimages `f ⁻¹ᵁ U i`. Say that `f` *intertwines* the two cocycles when pulling back a
transition unit of `D` gives the corresponding transition unit of `D'`. Then applying `f` to
each local coordinate carries a compatible family for `D` over `W` to a compatible family for
`D'` over `f ⁻¹ᵁ W`, and the resulting maps assemble into a morphism of sheaves of modules

`D.glue ⟶ f_* D'.glue`

on `Y`. This is the piece of the gluing calculus that lets one write down a map between two
glued modules, as opposed to an isomorphism between two gluings of cohomologous cocycles on one
space (`Stacks.SheafOfModules.UnitTransitionCocycle.glueIsoOfCoboundaryTwist`).

The example it is written for is [Stacks, Tag 0EHE]: there `Y` and `Y'` are the punctured
spectra of `A/t^{n+1}A` and of `A/tⁿA`, the charts are `D(x̄)` and `D(ȳ)`, the cocycles are the
two-chart cocycles of the transition elements, and the intertwining hypothesis is the
compatibility of the transition elements with reduction modulo `tⁿ`.

## Main definitions

* `Stacks.SheafOfModules.UnitTransitionCocycle.Intertwines`: the hypothesis that `f` carries the
  transition units of `D` to those of `D'`.
* `Stacks.SheafOfModules.UnitTransitionCocycle.pullbackSectionsHom`: applying `f` to each local
  coordinate, as a map of modules over the ring map on functions.
* `Stacks.SheafOfModules.UnitTransitionCocycle.glueHomOfIntertwines`: the morphism
  `D.glue ⟶ f_* D'.glue`.

## Main results

* `Stacks.SheafOfModules.UnitTransitionCocycle.pullbackSections_sectionsMap`: the chartwise
  pullback commutes with restriction.
* `Stacks.SheafOfModules.UnitTransitionCocycle.chartLinearEquiv_glueHomOfIntertwines`: in the
  chart trivializations the morphism is the map on functions.

## Implementation notes

The target is the direct image `AlgebraicGeometry.Scheme.Modules.pushforward f`, whose value on
an open `W` of `Y` is the value of the source module on `f ⁻¹ᵁ W` with `Γ(Y, W)` acting through
`f.app W`. No transport is needed to see the chartwise pullback as landing there: `f ⁻¹ᵁ` commutes
with `⊓` by `rfl`, so a family indexed by the opens `f ⁻¹ᵁ (W ⊓ U i)` *is* a family indexed by the
opens `f ⁻¹ᵁ W ⊓ f ⁻¹ᵁ U i` which `D'.sectionsSubmodule (f ⁻¹ᵁ W)` is cut out of.

The charts upstairs are the preimages `f ⁻¹ᵁ U i` on the nose, rather than a second family
assumed equal to them: an equality of opens would have to be transported through every ring of
sections. A caller holding a cocycle on a different but equal family rewrites that family first.

## References

* [Stacks Project, Tag 0EHE](https://stacks.math.columbia.edu/tag/0EHE)
* [Stacks Project, Tag 0BCY](https://stacks.math.columbia.edu/tag/0BCY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules.UnitTransitionCocycle

section

variable {Y Y' : Scheme.{u}}

/-- Pulling back functions along `f` commutes with restricting them to a smaller open. This is
`AlgebraicGeometry.Scheme.Hom.naturality` read on elements. -/
theorem app_presheafMap_apply (f : Y' ⟶ Y) {V V' : Y.Opens} (h : V' ≤ V) (z : Γ(Y, V)) :
    (Y'.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app V).hom z) =
      (f.app V').hom ((Y.presheaf.map (homOfLE h).op).hom z) := by
  have hnat := f.naturality (U := V') (U' := V) (homOfLE h).op
  rw [show ((Opens.map f.base).map ((homOfLE h).op).unop).op =
    (homOfLE (f.preimage_mono h)).op from Subsingleton.elim _ _] at hnat
  exact (congrArg (fun φ => φ z) (congrArg CommRingCat.Hom.hom hnat)).symm

variable {f : Y' ⟶ Y} {ι : Type u} {U : ι → Y.Opens}

/-- `Intertwines f D D'` says that pulling a transition unit of `D` back along `f` gives the
corresponding transition unit of `D'`: over an open `V` of `Y` inside both the `i`-th and the
`j`-th chart, `f^♯(tᵢⱼ) = t'ᵢⱼ` on `f ⁻¹ᵁ V`. -/
def Intertwines (f : Y' ⟶ Y) (D : UnitTransitionCocycle Y.toRingedSpace U)
    (D' : UnitTransitionCocycle Y'.toRingedSpace fun i => f ⁻¹ᵁ U i) : Prop :=
  ∀ (i j : ι) (V : Y.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
    Units.map (f.app V).hom (D.transition i j V hi hj) =
      D'.transition i j (f ⁻¹ᵁ V) (f.preimage_mono hi) (f.preimage_mono hj)

variable {D : UnitTransitionCocycle Y.toRingedSpace U}
  {D' : UnitTransitionCocycle Y'.toRingedSpace fun i => f ⁻¹ᵁ U i}

/-- Applying `f` to each local coordinate carries a family compatible for `D` over `W` to a
family compatible for `D'` over `f ⁻¹ᵁ W`. -/
theorem pullbackSections_mem (h : Intertwines f D D') (W : Y.Opens)
    (s : D.sectionsSubmodule W) :
    (fun i => (f.app (W ⊓ U i)).hom (s.val i)) ∈ D'.sectionsSubmodule (f ⁻¹ᵁ W) := by
  intro i j
  set Z : Y.Opens := W ⊓ U i ⊓ (W ⊓ U j)
  have hZi : Z ≤ U i := inf_le_left.trans inf_le_right
  have hZj : Z ≤ U j := inf_le_right.trans inf_le_right
  have htr : (D'.transition i j (f ⁻¹ᵁ Z) (f.preimage_mono hZi) (f.preimage_mono hZj)).val =
      (f.app Z).hom (D.transition i j Z hZi hZj).val :=
    (congrArg Units.val (h i j Z hZi hZj)).symm
  show (D'.transition i j (f ⁻¹ᵁ Z) (f.preimage_mono hZi) (f.preimage_mono hZj)).val *
      (Y'.presheaf.map (homOfLE (f.preimage_mono (inf_le_left : Z ≤ W ⊓ U i))).op).hom
        ((f.app (W ⊓ U i)).hom (s.val i)) =
    (Y'.presheaf.map (homOfLE (f.preimage_mono (inf_le_right : Z ≤ W ⊓ U j))).op).hom
      ((f.app (W ⊓ U j)).hom (s.val j))
  rw [htr, app_presheafMap_apply f (inf_le_left : Z ≤ W ⊓ U i) (s.val i),
    app_presheafMap_apply f (inf_le_right : Z ≤ W ⊓ U j) (s.val j), ← map_mul]
  exact congrArg (f.app Z).hom (s.property i j)

/-- Applying `f` to each local coordinate, as a map from the compatible families for `D` over
`W` to those for `D'` over `f ⁻¹ᵁ W`. -/
def pullbackSections (h : Intertwines f D D') (W : Y.Opens) (s : D.sectionsSubmodule W) :
    D'.sectionsSubmodule (f ⁻¹ᵁ W) :=
  ⟨_, pullbackSections_mem h W s⟩

/-- The `i`-th coordinate of `pullbackSections h W s` is `f.app (W ⊓ U i)` applied to the `i`-th
coordinate of `s`. -/
@[simp]
theorem pullbackSections_val (h : Intertwines f D D') (W : Y.Opens)
    (s : D.sectionsSubmodule W) (i : ι) :
    (pullbackSections h W s).val i = (f.app (W ⊓ U i)).hom (s.val i) := rfl

/-- The chartwise pullback commutes with restriction of compatible families. -/
theorem pullbackSections_sectionsMap (h : Intertwines f D D') {W W' : Y.Opens} (k : W' ≤ W)
    (s : D.sectionsSubmodule W) :
    D'.sectionsMap (f.preimage_mono k) (pullbackSections h W s) =
      pullbackSections h W' (D.sectionsMap k s) := by
  refine Subtype.ext (funext fun i => ?_)
  rw [sectionsMap_val, pullbackSections_val, pullbackSections_val, sectionsMap_val]
  exact app_presheafMap_apply f (inf_le_inf_right (U i) k) (s.val i)

/-- Applying `f` to each local coordinate, as a map of modules over the map `f.app W` on
functions. -/
noncomputable def pullbackSectionsHom (h : Intertwines f D D') (W : Y.Opens) :
    ModuleCat.of Γ(Y, W) (D.sectionsSubmodule W) ⟶
      (ModuleCat.restrictScalars (f.app W).hom).obj
        (ModuleCat.of Γ(Y', f ⁻¹ᵁ W) (D'.sectionsSubmodule (f ⁻¹ᵁ W))) := by
  let M' := ModuleCat.of Γ(Y', f ⁻¹ᵁ W) (D'.sectionsSubmodule (f ⁻¹ᵁ W))
  letI : Module Γ(Y, W) M' := Module.compHom M' (f.app W).hom
  exact ModuleCat.ofHom (show D.sectionsSubmodule W →ₗ[Γ(Y, W)] M' from
    { toFun := pullbackSections h W
      map_add' s t := Subtype.ext (funext fun i => by
        rw [pullbackSections_val]
        change (f.app (W ⊓ U i)).hom (s.val i + t.val i) =
          (f.app (W ⊓ U i)).hom (s.val i) + (f.app (W ⊓ U i)).hom (t.val i)
        exact map_add _ _ _)
      map_smul' r s := Subtype.ext (funext fun i => by
        rw [pullbackSections_val]
        change (f.app (W ⊓ U i)).hom
            ((Y.presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op).hom r * s.val i) =
          (Y'.presheaf.map (homOfLE (f.preimage_mono (inf_le_left : W ⊓ U i ≤ W))).op).hom
              ((f.app W).hom r) *
            (f.app (W ⊓ U i)).hom (s.val i)
        rw [map_mul, app_presheafMap_apply f (inf_le_left : W ⊓ U i ≤ W) r]) })

/-- **A map of glued modules from chartwise maps of functions.** Applying `f` to each local
coordinate of a compatible family is a morphism from the module glued on the target to the direct
image of the module glued on the source, whenever `f` intertwines the two cocycles. -/
noncomputable def glueHomOfIntertwines (h : Intertwines f D D') :
    D.glue ⟶ (Scheme.Modules.pushforward f).obj D'.glue :=
  ⟨{ app W := pullbackSectionsHom h W.unop
     naturality g := ModuleCat.hom_ext <| LinearMap.ext fun s =>
      (pullbackSections_sectionsMap h g.unop.le s).symm }⟩

/-- On sections over `W`, `glueHomOfIntertwines h` is `pullbackSections h W`. -/
@[simp]
theorem glueHomOfIntertwines_app (h : Intertwines f D D') (W : Y.Opens)
    (s : D.sectionsSubmodule W) :
    (glueHomOfIntertwines h).val.app (op W) s = pullbackSections h W s := rfl

/-- In the chart trivializations given by `chartLinearEquiv`, the morphism of glued modules
`glueHomOfIntertwines h` is the map `f.app V` on functions. -/
theorem chartLinearEquiv_glueHomOfIntertwines (h : Intertwines f D D') (i : ι) {V : Y.Opens}
    (hV : V ≤ U i) (s : D.sectionsSubmodule V) :
    D'.chartLinearEquiv i (f.preimage_mono hV)
        ((glueHomOfIntertwines h).val.app (op V) s) =
      (f.app V).hom (D.chartLinearEquiv i hV s) := by
  show (Y'.presheaf.map (homOfLE (le_inf le_rfl (f.preimage_mono hV))).op).hom
      ((pullbackSections h V s).val i) =
    (f.app V).hom ((Y.presheaf.map (homOfLE (le_inf le_rfl hV)).op).hom (s.val i))
  exact app_presheafMap_apply f (le_inf le_rfl hV) (s.val i)

end

end Stacks.SheafOfModules.UnitTransitionCocycle

end
