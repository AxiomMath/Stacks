module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackUnitValue
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackGlobalSection

/-!
# The pullback of a global section on the unit section

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi and `t : O_D ⟶ N` a global
section of an `O_D`-module. The pulled-back section `f^*t : O_C ≅ f^*O_D ⟶ f^*N` (Stacks 03LU)
is computed on the unit section through the unit `c : f⁻¹N ⟶ f^*N` of extension of scalars
along `f♯ : f⁻¹O_D ⟶ O_C` (Stacks 03CZ): `f^*t` sends `1` to `c(f⁻¹t(1))`. In the form of
morphisms of `f⁻¹O_D`-modules out of the unit module: `1 ↦ f⁻¹t(1) ↦ c(f⁻¹t(1))` is `f♯` (as a
map of modules) followed by `f^*t`.

This is how a map out of `f^*𝒞` agreeing with another on the image of `c` (as in the body of the
proof of [Stacks Project, Tag 0D3X]) is evaluated on pulled-back global sections.

## Main results

* `RingedToposModules.inverseImageModulesUnitIso_hom_comp_map_comp_fSharpAdjunction_unit`:
  the formula for a morphism of ringed topoi, in the namespace `Stacks.Sheaves`.
* `CategoryTheory.Adjunction.hom_comp_comp_unit_app_eq_of_homEquiv_inv`: the abstract chase.
* `Space.inverseImageModulesUnitIso_hom_comp_map_comp_extendScalarsFSharpAdjunction_unit`:
  the formula for `AlgebraicGeometry.Space.modulePullbackGlobalSection`, in the namespace
  `AlgebraicGeometry`.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

/-- **A unit component computed from one transpose**: if the transpose of `e⁻¹ : E ⟶ L P` is
`i⁻¹ ≫ u`, then `i ≫ q ≫ η_Q = u ≫ R(e ≫ L q)` for every `q : P ⟶ Q`. -/
theorem CategoryTheory.Adjunction.hom_comp_comp_unit_app_eq_of_homEquiv_inv {C D : Type*}
    [Category C] [Category D] {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {U P : C} {E : D}
    (i : U ≅ P) {Q : C} (q : P ⟶ Q) (u : U ⟶ R.obj E) (e : E ≅ L.obj P)
    (h : adj.homEquiv _ _ e.inv = i.inv ≫ u) :
    i.hom ≫ q ≫ adj.unit.app Q = u ≫ R.map (e.hom ≫ L.map q) := by
  have h3 : adj.unit.app P = i.inv ≫ u ≫ R.map e.hom := by
    rw [← Category.assoc, ← h, ← Adjunction.homEquiv_naturality_right, Iso.inv_hom_id,
      Adjunction.homEquiv_id]
  rw [← Adjunction.unit_naturality, h3]
  simp

namespace Stacks.Sheaves.RingedToposModules

open Stacks.SheafOfModules.ChangeOfRings Stacks.Sheaves.FinitePresentation

universe v u w v' u' w'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : RingedToposHom X Y)

/-- **The pullback of a global section, on the unit section** (Stacks 03CZ, 03LU): for a global
section `t : O_D ⟶ N`, the composite `f⁻¹O_D = f⁻¹1 ⟶ f⁻¹N ⟶ f^*N` of `f⁻¹t` with the unit `c`
of extension of scalars along `f♯` is `f♯` (as a map of `f⁻¹O_D`-modules) followed by the
pulled-back section `O_C ≅ f^*O_D ⟶ f^*N`. -/
theorem inverseImageModulesUnitIso_hom_comp_map_comp_fSharpAdjunction_unit
    {N : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (t : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶ N) :
    (inverseImageModulesUnitIso f).hom ≫
        (inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map t ≫
        (fSharpAdjunction f).unit.app
          ((inverseImageModules f.toToposHom (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj N) =
      unitToRestrictScalarsUnit f.fSharpInverseImage ≫
        (SheafOfModules.restrictScalars f.fSharpInverseImage).map
          ((pullbackModulesObjUnitIso f).hom ≫ f.pullbackModules.map t) :=
  CategoryTheory.Adjunction.hom_comp_comp_unit_app_eq_of_homEquiv_inv (fSharpAdjunction f)
    (inverseImageModulesUnitIso f) _ _ (pullbackModulesObjUnitIso f)
    (fSharpAdjunction_homEquiv_pullbackModulesObjUnitIso_inv f)

end Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules Stacks.SheafOfModules.ChangeOfRings
  Stacks.Sheaves.FinitePresentation

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **The pullback of a global section of an `𝒪_Y`-module, on the unit section**: for
`f : X ⟶ Y` and `t : 𝒪_Y ⟶ N`, the composite `f⁻¹𝒪_Y = f⁻¹1 ⟶ f⁻¹N ⟶ f^*N` of `f⁻¹t` with the
unit `c` of extension of scalars along `f♯` is `f♯` followed by `f^*t`
(`AlgebraicGeometry.Space.modulePullbackGlobalSection`). -/
theorem inverseImageModulesUnitIso_hom_comp_map_comp_extendScalarsFSharpAdjunction_unit
    (f : X ⟶ Y) {N : Modules.{u, u} B S hS Y.1 Y.2}
    (t : SheafOfModules.unit (structureRingSheaf B S hS Y) ⟶ N) :
    (inverseImageModulesUnitIso (smallEtaleRingedToposModulesHom B S hS f)).hom ≫
        (inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).map t ≫
        (extendScalarsFSharpAdjunction B S hS f).unit.app
          ((inverseImageModules (smallEtaleRingedToposModulesHom B S hS f).toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedTopos B S hS Y).O)).obj N) =
      unitToRestrictScalarsUnit (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage ≫
        (SheafOfModules.restrictScalars
          (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map
          (modulePullbackGlobalSection B S hS f t) :=
  inverseImageModulesUnitIso_hom_comp_map_comp_fSharpAdjunction_unit
    (smallEtaleRingedToposModulesHom B S hS f) t

end AlgebraicGeometry.Space
