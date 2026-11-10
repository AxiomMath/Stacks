module

public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpaceDualizing.PushforwardTwists
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.CategoryTheory.Adjunction.AdjunctionUnit
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison

/-!
# Derived direct image on morphisms out of the structure sheaf of projective space

Let `S` be a scheme, let `n = m + 1 ≥ 1` and let `f : ℙⁿ_S ⟶ S` be the structure morphism. Then
`Rf_*` is bijective on the morphisms `𝒪_{ℙⁿ_S}[a] ⟶ K` of `D(𝒪_{ℙⁿ_S})`, for every object `K` and
every degree `a`:

  `Hom(𝒪_{ℙⁿ_S}[a], K) ≅ Hom(Rf_*(𝒪_{ℙⁿ_S}[a]), Rf_* K)`,  `s ↦ Rf_* s`.

This is the one non-formal step of the proof of [Stacks, Tag 0A9W]: there it is the assertion
that the arrow `c` "transforms into an isomorphism under `Hom(𝒪_X, (-)[p])` by construction",
which unwinds to the statement that `Rf_*` is fully faithful on maps out of the shifts of `𝒪_X`.

## The argument

Let `L = Lf^*` be the derived pullback, left adjoint to `Rf_*` by [Stacks, Tag 079W]. Since
`𝒪_S` is flat, `L(𝒪_S[a]) ≅ 𝒪_{ℙⁿ_S}[a]`, and by the computation of the higher direct images
`Rf_*(𝒪_{ℙⁿ_S}[a]) ≅ 𝒪_S[a]`. So `Rf_* L (𝒪_S[a]) ≅ 𝒪_S[a]`, by *some* isomorphism. Any two
endomorphisms of `𝒪_S[a]` commute — they are global functions on `S` — and an adjunction whose
composite is isomorphic to the identity at an object with commuting endomorphisms has invertible
unit there (`Stacks.Adjunction.isIso_unit_app_of_iso_of_comm`). An invertible unit at `𝒪_S[a]`
is exactly bijectivity of `Rf_*` on maps out of `L(𝒪_S[a]) ≅ 𝒪_{ℙⁿ_S}[a]`.

No computation of the unit is needed, and no identification of its effect on cohomology: the
commutativity of the endomorphism ring of `𝒪_S` does that work.

## Main results

* `Stacks.Duality.ProjectiveSpaceDualizing.unit_endomorphisms_comm`: any two endomorphisms of the
  structure sheaf of a scheme commute.
* `Stacks.Duality.ProjectiveSpaceDualizing.derivedPullbackUnitIso`: `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` at the
  locally small model, for every morphism of schemes.
* `Stacks.Duality.ProjectiveSpaceDualizing.derivedPullbackSingleUnitIso`:
  `Lf^*(𝒪_Y[a]) ≅ 𝒪_X[a]` in every degree.
* `Stacks.Duality.ProjectiveSpaceDualizing.bijective_derivedPushforward_map_unit`: **`Rf_*` is
  bijective on the morphisms out of `𝒪_{ℙⁿ_S}[a]`.**

## Implementation notes

The derived categories are the locally small models
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, at which
`Stacks.Duality.derivedAdjunction` is stated. The identification `Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]` is
available at the standard model, as
`Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso`, and is carried to the locally
small model by `StacksDraft.DerivedModel.derivedPullbackModelIso` and the comparison equivalence
`Stacks.Injectives.grothendieckModelEquiv`, which is the identity on objects and matches the two
localization functors on the nose. The shifts come from the compatibility of `Lf^*` with the
shift which the adjunction induces from that of `Rf_*`
(`CategoryTheory.Adjunction.leftAdjointCommShift`).

## References

* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0A9W](https://stacks.math.columbia.edu/tag/0A9W)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality.ProjectiveSpaceDualizing

/-! ### Endomorphisms of the structure sheaf -/

/-- **Any two endomorphisms of the structure sheaf of a scheme commute.** An endomorphism of `𝒪_X`
as a module over itself is multiplication by its value at `1` on every open, and multiplication
in `𝒪_X(U)` is commutative. -/
theorem unit_endomorphisms_comm (X : Scheme.{u})
    (g h : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf) :
    g ≫ h = h ≫ g := by
  ext U
  let R := X.ringCatSheaf.obj.obj U
  change (h.val.app U).hom ((g.val.app U).hom (1 : R)) =
    (g.val.app U).hom ((h.val.app U).hom (1 : R))
  have key : ∀ (k : SheafOfModules.unit X.ringCatSheaf ⟶ SheafOfModules.unit X.ringCatSheaf)
      (y : R), (k.val.app U).hom y = y • (k.val.app U).hom (1 : R) := fun k y =>
    (congrArg (k.val.app U).hom (mul_one y).symm).trans ((k.val.app U).hom.map_smul y (1 : R))
  rw [key h ((g.val.app U).hom (1 : R)), key g ((h.val.app U).hom (1 : R))]
  exact (mul_comm : ∀ a b : (X.presheaf.obj U : Type u), a * b = b * a) _ _

/-- Any two endomorphisms of the structure sheaf placed in a single degree of the derived category
commute: the single functor is full. -/
theorem single_unit_endomorphisms_comm (X : Scheme.{u}) (a : ℤ)
    (g h : (DerivedCategory.singleFunctor X.Modules a).obj (SheafOfModules.unit X.ringCatSheaf) ⟶
      (DerivedCategory.singleFunctor X.Modules a).obj (SheafOfModules.unit X.ringCatSheaf)) :
    g ≫ h = h ≫ g := by
  obtain ⟨g', rfl⟩ := (DerivedCategory.singleFunctor X.Modules a).map_surjective g
  obtain ⟨h', rfl⟩ := (DerivedCategory.singleFunctor X.Modules a).map_surjective h
  exact ((Functor.map_comp _ g' h').symm.trans
    (congrArg (DerivedCategory.singleFunctor X.Modules a).map
      (unit_endomorphisms_comm X g' h'))).trans
      (Functor.map_comp _ h' g')

/-! ### The derived pullback of the structure sheaf -/

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`Lf^*(𝒪_Y[0]) ≅ 𝒪_X[0]`** at the locally small model, for an arbitrary morphism of schemes:
the identification of the standard model,
`Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso`, carried across the comparison of
the two models of the derived categories. -/
def derivedPullbackUnitIso :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor Y.Modules 0).obj (SheafOfModules.unit Y.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj (SheafOfModules.unit X.ringCatSheaf) :=
  ((StacksDraft.DerivedModel.derivedPullbackModelIso f.toLRSHom.toShHom).app
      ((@DerivedCategory.singleFunctor Y.Modules _ _ (HasDerivedCategory.standard _) 0).obj
        (SheafOfModules.unit Y.ringCatSheaf))).symm ≪≫
    (Stacks.Injectives.grothendieckModelEquiv _).functor.mapIso
      (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso f.toLRSHom.toShHom)

/-- The compatibility of `Lf^*` with the shift induced through `Lf^* ⊣ Rf_*` from that of
`Rf_*`. -/
@[instance_reducible]
def commShiftDerivedPullback : (derivedPullback f).CommShift ℤ :=
  (derivedAdjunction f).leftAdjointCommShift ℤ

/-- **`Lf^*(𝒪_Y[a]) ≅ 𝒪_X[a]`** at the locally small model, in every degree `a`: the degree-zero
identification `Stacks.Duality.ProjectiveSpaceDualizing.derivedPullbackUnitIso` moved by the
shift. -/
def derivedPullbackSingleUnitIso (a : ℤ) :
    (derivedPullback f).obj
        ((DerivedCategory.singleFunctor Y.Modules a).obj (SheafOfModules.unit Y.ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor X.Modules a).obj (SheafOfModules.unit X.ringCatSheaf) :=
  letI := commShiftDerivedPullback f
  (derivedPullback f).mapIso
      (((DerivedCategory.singleFunctors Y.Modules).shiftIso (-a) a 0 (by omega)).app
        (SheafOfModules.unit Y.ringCatSheaf)).symm ≪≫
    ((derivedPullback f).commShiftIso (-a)).app _ ≪≫
    (shiftFunctor (DerivedCategory X.Modules) (-a)).mapIso (derivedPullbackUnitIso f) ≪≫
    ((DerivedCategory.singleFunctors X.Modules).shiftIso (-a) a 0 (by omega)).app
      (SheafOfModules.unit X.ringCatSheaf)

/-! ### `Rf_*` on morphisms out of the structure sheaf of projective space -/

/-- Precomposition with an isomorphism is bijective. -/
theorem bijective_comp_iso {C : Type*} [Category C] {A B K : C} (e : A ≅ B) :
    Function.Bijective (fun s : B ⟶ K => e.hom ≫ s) :=
  ⟨fun s t h => by simpa using congrArg (e.inv ≫ ·) h,
    fun t => ⟨e.inv ≫ t, by simp⟩⟩

variable (m : ℕ) (S : Scheme.{u})

/-- **`Rf_*` is bijective on the morphisms out of `𝒪_{ℙⁿ_S}[a]`**, for `f : ℙⁿ_S ⟶ S` the
structure morphism, `n ≥ 1`, every degree `a` and every object `K` of `D(𝒪_{ℙⁿ_S})`.

The unit of `Lf^* ⊣ Rf_*` at `𝒪_S[a]` is invertible: `Rf_* Lf^*(𝒪_S[a]) ≅ Rf_*(𝒪_{ℙⁿ_S}[a]) ≅
𝒪_S[a]` and endomorphisms of `𝒪_S[a]` commute (`Stacks.Adjunction.isIso_unit_app_of_iso_of_comm`).
So `Rf_*` is bijective on the morphisms out of `Lf^*(𝒪_S[a]) ≅ 𝒪_{ℙⁿ_S}[a]`. -/
theorem bijective_derivedPushforward_map_unit (a : ℤ)
    (K : DerivedCategory (projectiveSpaceOver (m + 1) S).Modules) :
    Function.Bijective (fun s : (DerivedCategory.singleFunctor
        (projectiveSpaceOver (m + 1) S).Modules a).obj
        (SheafOfModules.unit (projectiveSpaceOver (m + 1) S).ringCatSheaf) ⟶ K =>
      (derivedPushforward (projectiveSpaceOver (m + 1) S ↘ S)).map s) := by
  set g := projectiveSpaceOver (m + 1) S ↘ S
  set φ := derivedPullbackSingleUnitIso g a
  have hU : IsIso ((derivedAdjunction g).unit.app
      ((DerivedCategory.singleFunctor S.Modules a).obj (SheafOfModules.unit S.ringCatSheaf))) :=
    Stacks.Adjunction.isIso_unit_app_of_iso_of_comm (derivedAdjunction g)
      ((derivedPushforward g).mapIso φ ≪≫ derivedPushforwardUnitIso m S a)
      (single_unit_endomorphisms_comm S a)
  have hR := Stacks.Adjunction.bijective_map_of_isIso_unit_app (derivedAdjunction g)
    (X := (DerivedCategory.singleFunctor S.Modules a).obj (SheafOfModules.unit S.ringCatSheaf)) K
  convert ((bijective_comp_iso (asIso ((derivedPushforward g).map φ.hom)).symm).comp hR).comp
    (bijective_comp_iso φ) using 1
  funext s
  simp

end Stacks.Duality.ProjectiveSpaceDualizing

end
