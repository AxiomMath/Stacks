module

public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.CompactPerfect
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.SupportedCompactGeneration

/-!
# Restriction to the members of a cover by two opens

Let `Y` be a scheme covered by two opens `A` and `B` with intersection `C`. This file collects the
facts about restriction `D(𝒪_Y) ⥤ D(𝒪_A)` used by the induction step of approximation by perfect
complexes ([Stacks, Tag 08ER]), at the locally small model of the derived categories.

## Main results

* `Stacks.Duality.OpenImmersion.derivedRestrictCompIso`: restriction along a composite of open
  immersions is restriction along the two in turn.
* `Stacks.Duality.OpenImmersion.stalkHomologyDerivedRestrictIso`: the stalks of the cohomology
  sheaves of a restriction are the stalks of the cohomology sheaves of the object.
* `Stacks.Duality.OpenImmersion.isZero_homology_of_isZero_homology_derivedRestrict_two`: the
  vanishing of a cohomology sheaf is detected on the members of the cover.
* `Stacks.Duality.OpenImmersion.isPerfect_of_forall_exists_isPerfect_derivedRestrict`: perfectness
  is local.
* `Stacks.Duality.OpenImmersion.isPerfect_of_isPerfect_derivedRestrict_two`: perfectness is
  detected on the members of the cover.
* `Stacks.Duality.OpenImmersion.exists_extension_of_isZero_derivedRestrict`: an object `p` of
  `D(𝒪_A)` vanishing on `C`, with a morphism `p ⟶ E|_A`, extends to an object of `D(𝒪_Y)`
  vanishing on `B`, with a morphism to `E` extending the given one. This is the extension of
  an approximation from an open of [Stacks, Tag 08EP] in the form the induction step uses.

## Implementation notes

The extension is `Rj_{A,*} p`. Its restriction to `B` vanishes by base change to `C`
([Stacks, Tag 08FE]). The morphism `Rj_{A,*}p ⟶ Rj_{A,*}(E|_A)` lifts along the unit
`E ⟶ Rj_{A,*}(E|_A)` because the cone `N` of the unit vanishes on `A`, so that `N` is
`Rj_{B,*}(N|_B)` and receives no nonzero morphism from an object vanishing on `B`.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Duality.QcqsGeneration Stacks.Duality.SupportedGeneration ZeroObject
open CategoryTheory.ObjectProperty (isIso_map_unit_of_isIso_counit)

universe w u

namespace Stacks.Duality.OpenImmersion

/-! ### Composites and stalks -/

/-- **Restriction along a composite of open immersions is restriction along the two in turn.** -/
def derivedRestrictCompIso {W U Y : Scheme.{u}} (f : W ⟶ U) (g : U ⟶ Y) [IsOpenImmersion f]
    [IsOpenImmersion g] : derivedRestrict (f ≫ g) ≅ derivedRestrict g ⋙ derivedRestrict f :=
  Functor.mapDerivedCategoryCongr (Scheme.Modules.restrictFunctorComp f g) ≪≫
    (Stacks.DerivedQCoh.mapDerivedCategoryComp (Scheme.Modules.restrictFunctor g)
      (Scheme.Modules.restrictFunctor f))

/-- Restriction along equal open immersions. -/
def derivedRestrictCongr {U Y : Scheme.{u}} {f g : U ⟶ Y} [IsOpenImmersion f]
    [IsOpenImmersion g] (h : f = g) : derivedRestrict f ≅ derivedRestrict g :=
  Functor.mapDerivedCategoryCongr (Scheme.Modules.restrictFunctorCongr h)

/-- **The stalks of the cohomology sheaves of a restriction.** For an open immersion `j : U ⟶ Y`
and `x ∈ U`, the stalk at `x` of `Hⁱ(K|_U)` is the stalk at `j x` of `Hⁱ(K)`. -/
def stalkHomologyDerivedRestrictIso {U Y : Scheme.{u}} (j : U ⟶ Y) [IsOpenImmersion j]
    [HasDerivedCategory.{w} U.Modules] [HasDerivedCategory.{w} Y.Modules]
    (K : DerivedCategory Y.Modules) (i : ℤ) (x : U) :
    TopCat.Presheaf.stalk (X := U)
        (((DerivedCategory.homologyFunctor U.Modules i).obj
          ((derivedRestrict j).obj K)).val.presheaf) x ≅
      TopCat.Presheaf.stalk (X := Y)
        (((DerivedCategory.homologyFunctor Y.Modules i).obj K).val.presheaf) (j x) :=
  (Scheme.Modules.toPresheaf U ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).mapIso
      (((Scheme.Modules.restrictFunctor j).mapDerivedCategoryHomologyIso i).app K) ≪≫
    (Scheme.Modules.restrictStalkNatIso j x).app _

/-- A cohomology sheaf of `D(𝒪_U)` vanishes exactly when all of its stalks do. -/
theorem isZero_homology_iff_forall_isZero_stalk {U : Scheme.{u}}
    [HasDerivedCategory.{w} U.Modules] (K : DerivedCategory U.Modules) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor U.Modules i).obj K) ↔
      ∀ x : U, IsZero (TopCat.Presheaf.stalk (X := U)
        (((DerivedCategory.homologyFunctor U.Modules i).obj K).val.presheaf) x) := by
  refine ⟨fun h x => (Scheme.Modules.toPresheaf U ⋙
    TopCat.Presheaf.stalkFunctor Ab.{u} x).map_isZero h, fun h => ?_⟩
  let M := (DerivedCategory.homologyFunctor U.Modules i).obj K
  have : IsIso (0 : (0 : U.Modules) ⟶ M) := by
    refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_stalk _ fun x => ?_
    exact isIso_of_source_target_iso_zero _
      (((Scheme.Modules.toPresheaf U ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x).map_isZero
        (isZero_zero _)).isoZero) (h x).isoZero
  exact (isZero_zero _).of_iso (asIso (0 : (0 : U.Modules) ⟶ M)).symm

/-! ### A cover by two opens -/

section TwoCover

variable {Y A B C : Scheme.{u}} (jA : A ⟶ Y) (jB : B ⟶ Y) (iA : C ⟶ A) (iB : C ⟶ B)
  [IsOpenImmersion jA] [IsOpenImmersion jB] [IsOpenImmersion iA] [IsOpenImmersion iB]

/-- **The vanishing of a cohomology sheaf is detected on a cover by two opens.** -/
theorem isZero_homology_of_isZero_homology_derivedRestrict_two
    (hcov : ∀ y : Y, (∃ x, jA x = y) ∨ (∃ x, jB x = y)) (K : DerivedCategory Y.Modules) (i : ℤ)
    (hA : IsZero ((DerivedCategory.homologyFunctor A.Modules i).obj ((derivedRestrict jA).obj K)))
    (hB : IsZero ((DerivedCategory.homologyFunctor B.Modules i).obj
      ((derivedRestrict jB).obj K))) :
    IsZero ((DerivedCategory.homologyFunctor Y.Modules i).obj K) := by
  refine (isZero_homology_iff_forall_isZero_stalk K i).2 fun y => ?_
  rcases hcov y with ⟨x, rfl⟩ | ⟨x, rfl⟩ <;>
    exact ((isZero_homology_iff_forall_isZero_stalk _ i).1 (by assumption) x).of_iso
      (stalkHomologyDerivedRestrictIso _ K i x).symm

/-- **An object of `D(𝒪_Y)` vanishing on `B` comes from `A`**: the unit `N ⟶ Rj_{A,*}(N|_A)` is
invertible. It is so on `A` because `Rj_{A,*}` is fully faithful, and on `B` both sides vanish, the
target by base change to the overlap. -/
theorem isIso_derivedRestrictPushforwardAdjunction_unit_of_isZero_restrict
    (hsq : IsPullback iA iB jA jB) (hcov : ∀ y : Y, (∃ x, jA x = y) ∨ (∃ x, jB x = y))
    (N : DerivedCategory Y.Modules) (hN : IsZero ((derivedRestrict jB).obj N)) :
    IsIso ((derivedRestrictPushforwardAdjunction jA).unit.app N) := by
  refine isIso_of_isIso_derivedRestrict_two jA jB _ ?_ ?_ hcov
  · exact isIso_map_unit_of_isIso_counit (derivedRestrictPushforwardAdjunction jA) N
      inferInstance
  · refine isIso_of_source_target_iso_zero _ hN.isoZero ?_
    exact baseChangeIso jA iA jB iB hsq _ ≪≫
      ((Stacks.Duality.derivedPushforward iB).map_isZero
        (isZero_derivedRestrict_comp_of_isZero iA iB jA jB hsq.w hN)).isoZero

/-- A strictly perfect model along an open immersion of an open subscheme of the source gives a
strictly perfect model along the inclusion of its image. -/
private theorem exists_hasStrictModel_image {E : CochainComplex Y.Modules ℤ} (a : A)
    (h : ∃ O : A.Opens, a ∈ O ∧
      CompactPerfect.HasStrictModel O.ι (CompactPerfect.restrictComplex jA E)) :
    ∃ O : Y.Opens, jA a ∈ O ∧ CompactPerfect.HasStrictModel O.ι E := by
  obtain ⟨O, haO, hO⟩ := h
  refine ⟨jA ''ᵁ O, ⟨a, haO, rfl⟩, ?_⟩
  refine ((hO.to_comp O.ι jA).comp (jA.isoImage O).inv).congr ?_
  rw [Iso.inv_comp_eq, Scheme.Hom.isoImage_hom_ι]

/-- **Perfectness is local.** An object of `D(𝒪_Y)` is perfect when every point of `Y` lies in
the image of an open immersion along which its restriction is perfect. -/
theorem isPerfect_of_forall_exists_isPerfect_derivedRestrict (K : DerivedCategory Y.Modules)
    (h : ∀ y : Y, ∃ (W : Scheme.{u}) (j : W ⟶ Y) (_ : IsOpenImmersion j) (w : W), j w = y ∧
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace)
        ((derivedRestrict j).obj K)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) K := by
  let E := (DerivedCategory.Q (C := Y.Modules)).objPreimage K
  let eE : (DerivedCategory.Q (C := Y.Modules)).obj E ≅ K :=
    (DerivedCategory.Q (C := Y.Modules)).objObjPreimageIso K
  refine CompactPerfect.isPerfect_of_hasStrictModel K E eE fun y => ?_
  obtain ⟨W, j, _, w, rfl, hW⟩ := h y
  exact exists_hasStrictModel_image j w (CompactPerfect.hasStrictModel_of_isPerfect _
    (CompactPerfect.restrictComplex j E)
    ((CompactPerfect.derivedRestrictQIso j E).symm ≪≫ (derivedRestrict j).mapIso eE) hW w)

/-- **Perfectness is detected on a cover by two opens.** -/
theorem isPerfect_of_isPerfect_derivedRestrict_two
    (hcov : ∀ y : Y, (∃ x, jA x = y) ∨ (∃ x, jB x = y)) (K : DerivedCategory Y.Modules)
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := A.toRingedSpace)
      ((derivedRestrict jA).obj K))
    (hB : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := B.toRingedSpace)
      ((derivedRestrict jB).obj K)) :
    Stacks.Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) K := by
  refine isPerfect_of_forall_exists_isPerfect_derivedRestrict K fun y => ?_
  rcases hcov y with ⟨a, ha⟩ | ⟨b, hb⟩
  · exact ⟨A, jA, inferInstance, a, ha, hA⟩
  · exact ⟨B, jB, inferInstance, b, hb, hB⟩

/-- **Extension of an object vanishing on the overlap, with a morphism.** Let `Y = A ∪ B` with
`A ∩ B = C`, let `p` be an object of `D(𝒪_A)` vanishing on `C` and `α : p ⟶ E|_A` a morphism to
the restriction of an object `E` of `D(𝒪_Y)`. Then there are an object `g` of `D(𝒪_Y)` vanishing
on `B`, an isomorphism `g|_A ≅ p` and a morphism `γ : g ⟶ E` restricting to `α` on `A`. -/
theorem exists_extension_of_isZero_derivedRestrict (hsq : IsPullback iA iB jA jB)
    (hcov : ∀ y : Y, (∃ x, jA x = y) ∨ (∃ x, jB x = y))
    (p : DerivedCategory A.Modules) (hp : IsZero ((derivedRestrict iA).obj p))
    (E : DerivedCategory Y.Modules) (α : p ⟶ (derivedRestrict jA).obj E) :
    ∃ (g : DerivedCategory Y.Modules) (eg : (derivedRestrict jA).obj g ≅ p) (γ : g ⟶ E),
      IsZero ((derivedRestrict jB).obj g) ∧ (derivedRestrict jA).map γ = eg.hom ≫ α := by
  let adjA := derivedRestrictPushforwardAdjunction jA
  let adjB := derivedRestrictPushforwardAdjunction jB
  have : (Stacks.Duality.derivedPushforward jA).Additive := adjA.right_adjoint_additive
  have : (Stacks.Duality.derivedPushforward jB).Additive := adjB.right_adjoint_additive
  let g := (Stacks.Duality.derivedPushforward jA).obj p
  have hgB : IsZero ((derivedRestrict jB).obj g) :=
    IsZero.of_iso ((Stacks.Duality.derivedPushforward iB).map_isZero hp)
      (baseChangeIso jA iA jB iB hsq p)
  let η := adjA.unit.app E
  obtain ⟨N, π, δ, hT⟩ := distinguished_cocone_triangle η
  have hNA : IsZero ((derivedRestrict jA).obj N) :=
    Triangle.isZero₃_of_isIso₁ _ ((derivedRestrict jA).map_distinguished _ hT)
      (isIso_map_unit_of_isIso_counit adjA E inferInstance)
  have hNB : IsIso (adjB.unit.app N) :=
    isIso_derivedRestrictPushforwardAdjunction_unit_of_isZero_restrict jB jA iB iA hsq.flip
      (fun y => (hcov y).symm) N hNA
  let x := (Stacks.Duality.derivedPushforward jA).map α
  have hz : x ≫ π = 0 := eq_zero_of_isZero_obj_of_isIso_unit adjB hgB hNB _
  obtain ⟨γ, hγ⟩ := Triangle.coyoneda_exact₂ _ hT x hz
  refine ⟨g, asIso (adjA.counit.app p), γ, hgB, ?_⟩
  have h₁ : (derivedRestrict jA).map η ≫ adjA.counit.app ((derivedRestrict jA).obj E) = 𝟙 _ :=
    adjA.left_triangle_components E
  have h₂ : (derivedRestrict jA).map x ≫ adjA.counit.app ((derivedRestrict jA).obj E) =
      adjA.counit.app p ≫ α := adjA.counit.naturality α
  have h₃ : (derivedRestrict jA).map γ ≫ (derivedRestrict jA).map η =
      (derivedRestrict jA).map x := by
    rw [← Functor.map_comp]
    exact congrArg (derivedRestrict jA).map hγ.symm
  rw [asIso_hom, ← h₂, ← h₃, Category.assoc, h₁]
  exact (Category.comp_id _).symm

end TwoCover

end Stacks.Duality.OpenImmersion

end
