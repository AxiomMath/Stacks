module

public import StacksFrontier.AlgebraicGeometry.Perfect.BeilinsonTwistExceptional
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectiveSpace.TwistGeneration
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.TwistOrthogonalVanishing
public import StacksFrontier.Homology.DerivedCategory.ModelComparisonTransport

/-!
# The twists `𝒪, 𝒪(-1), …, 𝒪(-n)` detect the zero object of `D_QCoh(𝒪_{ℙⁿ_k})`

Let `k` be a field and `X = ℙⁿ_k`. An object `K` of `D(𝒪_X)` with quasi-coherent cohomology
sheaves, receiving no nonzero morphism from a shift of `𝒪(-a)[0]` for `0 ≤ a ≤ n`, is zero. This
is the generation statement of [Stacks, Tag 0A9V] on `D_QCoh(𝒪_X)` that the proof of
[Stacks, Tag 0FYB] uses through [Stacks, Tag 0BQU].

The argument is the one of
`Stacks.AlgebraicGeometry.ExampleGenerator.isWeakTriangulatedGenerator_twistSumQCoh`, run on the
model `ℙⁿ_k = ℙⁿ_ℤ ×_ℤ Spec k` of projective space that the conditions of [Stacks, Tag 0FYB] are
stated on:

* the Koszul step `Stacks.Duality.ProjectiveSpace.subsingleton_twistOver_shift_hom` propagates the
  vanishing from `𝒪, …, 𝒪(-n)` to every `𝒪(-m)`, `m ≥ 0`;
* `Stacks.AmpleNonvanishing.isZero_of_hom_single_eq_zero` concludes, `𝒪(1)` being ample and every
  quasi-coherent module of finite type being a quotient of a finite sum of twists `𝒪(-m)`
  ([Stacks, Tag 01YS] (1)).

Both run at the locally small model of `D(𝒪_X)`; the statement is wanted at the standard model,
which is where the conditions of [Stacks, Tag 0FYB] live. The passage is through the comparison
`Stacks.Injectives.grothendieckModelEquiv`, which is the identity on objects and matches the two
localization functors on the nose: everything is first read on cochain complexes.

## Main results

* `Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.isZero_homology_of_hom_twist_eq_zero`
  is the statement at the locally small model, read on a cochain complex.
* `Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization.isZero_of_hom_twistSingle_eq_zero`
  is the statement at the standard model.

## References

* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
* [Stacks Project, Tag 0FYB](https://stacks.math.columbia.edu/tag/0FYB)
* [Stacks Project, Tag 01YS](https://stacks.math.columbia.edu/tag/01YS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow (twistOver)

namespace Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization

universe u

variable (k : Type u) [Field k] (n : ℕ)

/-! ### At the locally small model -/

section LocallySmall

/-- The underlying space of `ℙⁿ_k` is compact. -/
instance compactSpace_projSpace :
    CompactSpace (projectiveSpaceOverRing n (CommRingCat.of k)) :=
  QuasiCompact.compactSpace_of_compactSpace
    (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))

/-- The underlying space of `ℙⁿ_k` is quasi-separated. -/
instance quasiSeparatedSpace_projSpace :
    QuasiSeparatedSpace (projectiveSpaceOverRing n (CommRingCat.of k)) :=
  quasiSeparatedSpace_of_quasiSeparated
    (projectiveSpaceOver n (Spec (CommRingCat.of k)) ↘ Spec (CommRingCat.of k))

/-- The shift of the single-object complex in `D(A)` is the class of the shifted complex. -/
private def shiftSingleIso {A : Type*} [Category A] [Abelian A] [HasDerivedCategory A] (X : A)
    (q : ℤ) : (shiftFunctor _ q).obj ((DerivedCategory.singleFunctor A 0).obj X) ≅
      DerivedCategory.Q.obj (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj X)⟦q⟧) :=
  (shiftFunctor _ q).mapIso ((DerivedCategory.singleFunctorIsoCompQ _ 0).app _) ≪≫
    ((DerivedCategory.Q.commShiftIso q).app _).symm

/-- **The twists `𝒪, …, 𝒪(-n)` detect quasi-coherent complexes**, at the locally small model of
`D(𝒪_X)` and read on a cochain complex `K`: if `K` has quasi-coherent cohomology and every
morphism from the class of a shift of `𝒪(-a)[0]`, `0 ≤ a ≤ n`, to the class of `K` vanishes,
then `K` is acyclic. -/
theorem isZero_homology_of_hom_twist_eq_zero
    (K : CochainComplex (projectiveSpaceOverRing n (CommRingCat.of k)).Modules ℤ)
    (hqc : ∀ i : ℤ, (K.homology i).IsQuasicoherent)
    (h : ∀ a : ℕ, a ≤ n → ∀ q : ℤ,
      ∀ f : DerivedCategory.Q.obj
          (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (twistOver n (Spec (CommRingCat.of k)) (-(a : ℤ))))⟦q⟧) ⟶ DerivedCategory.Q.obj K,
        f = 0)
    (i : ℤ) : IsZero (K.homology i) := by
  set S := Spec (CommRingCat.of k)
  set Y := DerivedCategory.Q.obj K
  have eH : ∀ j : ℤ, (DerivedCategory.homologyFunctor _ j).obj Y ≅ K.homology j := fun j =>
    (DerivedCategory.homologyFunctorFactors _ j).app K
  have h₁ : ∀ a : ℕ, a ≤ n → ∀ q : ℤ, Subsingleton ((shiftFunctor _ q).obj
      ((DerivedCategory.singleFunctor (projectiveSpaceOver n S).Modules 0).obj
        (twistOver n S (-(a : ℤ)))) ⟶ Y) := fun a ha q => by
    let e := shiftSingleIso (twistOver n S (-(a : ℤ))) q
    refine ⟨fun f g => ?_⟩
    rw [← cancel_epi e.inv, h a ha q (e.inv ≫ f), h a ha q (e.inv ≫ g)]
  have h₂ := Stacks.Duality.ProjectiveSpace.subsingleton_twistOver_shift_hom n S Y h₁
  have hY : DerivedCategoryB.derivedCategoryB (A := (projectiveSpaceOver n S).Modules)
      (SheafOfModules.isQuasicoherent (projectiveSpaceOver n S).ringCatSheaf) Y := fun j =>
    (SheafOfModules.isQuasicoherent (projectiveSpaceOver n S).ringCatSheaf).prop_of_iso
      (eH j).symm (hqc j)
  have hzero : IsZero (⟨Y, hY⟩ : Stacks.Duality.quasiCoherentDerivedCategory
      (projectiveSpaceOver n S)) := by
    refine Stacks.AmpleNonvanishing.isZero_of_hom_single_eq_zero (projectiveSpaceOver n S)
      (twistOver n S 1) (Stacks.ProjectiveSpace.isAmple_projectiveSpaceTwistingSheaf n S)
      (fun M => ∃ m : ℕ, M = twistOver n S (-(m : ℤ))) ?_ ⟨Y, hY⟩ ?_
    · intro F hqcF hft
      obtain ⟨r, d, b, hb, p, hp, hd⟩ :=
        Stacks.ProjectiveSpace.exists_epi_biproduct_tensorPowModule n S 0 F hqcF hft
      refine ⟨r, fun j => twistOver n S (d j), fun j => ⟨(-d j).toNat, ?_⟩, ?_⟩
      · have := hd j
        exact congrArg (twistOver n S) (by omega)
      · let e : (∐ fun j : Fin r => twistOver n S (d j)) ≅ b.pt :=
          (Sigma.mapIso fun j =>
              (ProjTwistTensorPow.tensorPowModuleProjectiveTwistIso n S (d j)).symm) ≪≫
            (colimit.isColimit _).coconePointUniqueUpToIso hb.isColimit
        exact ⟨e.hom ≫ p, epi_comp' (IsIso.epi_of_iso e.hom) hp⟩
    · rintro M ⟨m, rfl⟩ p f
      let e := ((DerivedCategory.singleFunctors (projectiveSpaceOver n S).Modules).shiftIso
        (-p) p 0 (by omega)).app (twistOver n S (-(m : ℤ)))
      simpa using e.inv ≫= (h₂ m (-p)).elim (e.hom ≫ f) 0
  exact ((DerivedCategory.homologyFunctor _ i).map_isZero
    ((DerivedCategoryB.derivedCategoryB (A := (projectiveSpaceOver n S).Modules)
      (SheafOfModules.isQuasicoherent (projectiveSpaceOver n S).ringCatSheaf)).ι.map_isZero
        hzero)).of_iso (eH i).symm

end LocallySmall

/-! ### At the standard model -/

section Standard

/-- The standard model of `D(𝒪_X)`. -/
abbrev stdModel : HasDerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules :=
  HasDerivedCategory.standard _

attribute [local instance 100000] HasDerivedCategory.standard

/-- **The twists `𝒪, …, 𝒪(-n)` detect the zero object of `D_QCoh(𝒪_{ℙⁿ_k})`**, at the standard
model: an object with quasi-coherent cohomology sheaves receiving no nonzero morphism from any
shift of `𝒪(-a)[0]`, `0 ≤ a ≤ n`, is zero. -/
theorem isZero_of_hom_twistSingle_eq_zero
    (Y : DerivedCategory (projectiveSpaceOverRing n (CommRingCat.of k)).Modules)
    (hY : ∀ i : ℤ, ((DerivedCategory.homologyFunctor _ i).obj Y).IsQuasicoherent)
    (h : ∀ a : ℕ, a ≤ n → ∀ j : ℤ, Subsingleton (twistSingle k n (-(a : ℤ)) ⟶ Y⟦j⟧)) :
    IsZero Y := by
  set K := DerivedCategory.Q.objPreimage Y
  let eY : DerivedCategory.Q.obj K ≅ Y := DerivedCategory.Q.objObjPreimageIso Y
  have eH : ∀ j : ℤ, (DerivedCategory.homologyFunctor _ j).obj Y ≅ K.homology j := fun j =>
    (DerivedCategory.homologyFunctor _ j).mapIso eY.symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ j).app K
  refine Stacks.Cohomology.PushforwardRestriction.isZero_derived_of_homology_isZero _
    fun i => ?_
  refine IsZero.of_iso ?_ (eH i)
  refine isZero_homology_of_hom_twist_eq_zero k n K
    (fun j => (SheafOfModules.isQuasicoherent
      (projectiveSpaceOverRing n (CommRingCat.of k)).ringCatSheaf).prop_of_iso (eH j) (hY j)) ?_ i
  intro a ha q f
  let E := Stacks.Injectives.grothendieckModelEquiv
    (projectiveSpaceOverRing n (CommRingCat.of k)).Modules
  obtain ⟨g, rfl⟩ := E.fullyFaithfulFunctor.map_surjective
    (X := DerivedCategory.Q.obj (((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
      (twistOver n (Spec (CommRingCat.of k)) (-(a : ℤ))))⟦q⟧))
    (Y := DerivedCategory.Q.obj K) f
  suffices hg : g = 0 by rw [hg, E.functor.map_zero]; rfl
  let e := (shiftSingleIso (twistOver n (Spec (CommRingCat.of k)) (-(a : ℤ))) q).symm
  have : e.inv ≫ g ≫ eY.hom = 0 :=
    ((Stacks.Duality.ProjectiveSpace.forall_subsingleton_shift_hom_iff _ Y).2 (h a ha) q).elim _ _
  simpa using e.hom ≫= this =≫ eY.inv

end Standard

end Stacks.AlgebraicGeometry.BeilinsonCoherentCharacterization

end
