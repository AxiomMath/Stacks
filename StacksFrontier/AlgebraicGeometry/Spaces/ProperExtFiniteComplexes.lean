module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperExtFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.ModelDerivedHomCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.HomFromStructureSheafLinear
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedHomBoundedBelow
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomAdjunction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ApproximationQcqs
public import StacksFrontier.AlgebraicGeometry.Spaces.PseudoCoherent.CoherentCohomologyConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowTwistWitness
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactPointSpace
public import StacksFrontier.Homology.DerivedCategory.PerfectApproximation
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AlternatingQuasicoherentComparison
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmpleTwist.GeneratedInDegreeOne

/-!
# Ext groups between coherent complexes on a proper algebraic space are finite

**Stacks 0D0T.**  Let `A` be a Noetherian ring and `X` an algebraic space over `A` proper over
`A`.  For `K ∈ D⁻_Coh(𝒪_X)` and `L ∈ D⁺_Coh(𝒪_X)` the group `Ext^n_X(K, L) = Hom_{D(𝒪_X)}(K, L[n])`
is a finite `A`-module for every `n`.

## The argument

`X` is Noetherian, so `K` is pseudo-coherent (Stacks 08IK) and, `X` being quasi-compact and
quasi-separated, approximation by perfect complexes holds (Stacks 08HP): there is a perfect `P`
with a map `P ⟶ K` whose cone has no cohomology in degrees `≥ m`, for `m` as small as wanted.  For
`m` below the bottom of `L[n]`, precomposition embeds `Hom(K, L[n])` into `Hom(P, L[n])`.

On the equi-universe model `Y` of the small étale ringed site, the derived internal Hom exists at
the module universe, and `Hom(P, L[n]) = Hom(𝒪_Y, RSheafHom(P, L)[n])` (Stacks 08JA,
`AlgebraicGeometry.RingedSite.homLinearEquivHomStructureSheafDerivedSheafHom`).  Read back on `X`,
`RSheafHom(P, L)` lies in `D⁺_Coh(𝒪_X)`: it is bounded below because `P` is bounded above and `L`
below, and its cohomology is coherent because `P` is locally strictly perfect
(`AlgebraicGeometry.Space.isCoherentOnSite_homology_of_modelDerivedSheafHom`, the coherent clause
of Stacks 0D0S).  So `Hom(P, L[n])` is the hypercohomology `Hom(𝒪_X, N[n])` of an object of
`D⁺_Coh(𝒪_X)`, which is finite by Stacks 08AS
(`AlgebraicGeometry.Space.moduleFinite_hom_unit_of_derivedCategoryBPlus`).  Every identification
is `A`-linear, and a submodule of a finite module over a Noetherian ring is finite.

## Main results

* `AlgebraicGeometry.Space.moduleFinite_hom_shift_of_isProper`: Stacks 0D0T.

## References

* [Stacks Project, Tag 0D0T](https://stacks.math.columbia.edu/tag/0D0T)
* [Stacks Project, Tag 0D0S](https://stacks.math.columbia.edu/tag/0D0S)
* [Stacks Project, Tag 08HP](https://stacks.math.columbia.edu/tag/08HP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace DerivedCategory

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- **Precomposition with an approximation is injective on maps into a bounded below target.**
If `α : P ⟶ K` induces isomorphisms on `H^i` for `i > m` and an epimorphism on `H^m`, then
`g ↦ α ≫ g` is injective on morphisms from `K` to an object concentrated in degrees `≥ m`. -/
theorem precomp_injective_of_approximatesFrom {P K M : DerivedCategory C} (α : P ⟶ K) (m : ℤ)
    (hα : ApproximatesFrom α m) (hM : M.IsGE m) :
    Function.Injective (fun g : K ⟶ M => α ≫ g) := by
  obtain ⟨Cn, β, γ, hT⟩ := distinguished_cocone_triangle α
  have hC : Cn.IsLE (m - 1) := by
    rw [isLE_iff]
    intro i hi
    exact (approximatesFrom_iff_isZero_homology_obj₃ (Triangle.mk α β γ) hT m).1 hα i (by omega)
  have h0 : ∀ g : K ⟶ M, α ≫ g = 0 → g = 0 := by
    intro g hg
    obtain ⟨h, rfl⟩ := Triangle.yoneda_exact₂ _ hT g hg
    have := hM
    have : TStructure.t.IsLE (Triangle.mk α β γ).obj₃ (m - 1) := hC
    rw [TStructure.t.zero h (m - 1) m (by omega), comp_zero]
  intro g₁ g₂ h
  exact sub_eq_zero.1 (h0 _ (by simpa only [Preadditive.comp_sub] using sub_eq_zero.2 h))

end DerivedCategory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **The empty open subspace has quasi-compact inclusion**: every pullback of it is an algebraic
space without points. -/
theorem isQuasiCompact_ι_openSubspace_of_eq_empty (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) (U : TopologicalSpace.Opens (points B S hS F))
    (hU : (U : Set (points B S hS F)) = ∅) :
    IsQuasiCompact B S hS ((openSubspacesOrderIso B S hS F hF).symm U).1.ι := by
  intro Z hZ _ g
  set G := (openSubspacesOrderIso B S hS F hF).symm U
  have hG : IsAlgebraicSpace B S hS G.1.toFunctor := G.2.1
  have hP := isAlgebraicSpace_pullback B S hS g G.1.ι hZ hG hF
  refine isQuasiCompactSpace_of_compactSpace_points B S hS hP ?_
  have hempty : IsEmpty (points B S hS G.1.toFunctor) := by
    have h := openSubspacesOrderIso_apply B S hS F hF G
    rw [show openSubspacesOrderIso B S hS F hF G = U from OrderIso.apply_symm_apply _ _] at h
    change (U : Set (points B S hS F)) = _ at h
    rw [hU] at h
    exact ⟨fun x => by
      have hx : pointsMap B S hS G.1.toFunctor G.1.ι x ∈ (∅ : Set (points B S hS F)) :=
        h ▸ ⟨x, rfl⟩
      exact hx⟩
  have : IsEmpty (points B S hS (pullback g G.1.ι)) :=
    ⟨fun y => hempty.false (pointsMap B S hS _ (pullback.snd g G.1.ι) y)⟩
  infer_instance

section Main

attribute [local instance 10000] HasDerivedCategory.standard smallEtaleRingedSite_hasSheafify
  smallEtaleRingedSite_wEqualsLocallyBijective smallEtaleRingedSite_hasSheafify_over
  smallEtaleRingedSite_wEqualsLocallyBijective_over

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] modulesLinear

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A)))
    (X : (BigFppfOver B (Spec (.of A)) hA)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B (Spec (.of A)) hA X)

/-- **`Hom(P, L[n])` through the model.**  If `N` represents `RSheafHom(P, L)` on the
equi-universe model, then finiteness of `Hom(𝒪_X, N[n])` gives finiteness of `Hom(P, L[n])`. -/
private theorem moduleFinite_hom_shift_of_modelDerivedSheafHom [IsNoetherianRing A]
    (P L N : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX))
    (eN : (modelDerived B (Spec (.of A)) hA X hX).obj N ≅
      ((RingedSite.derivedSheafHomBifunctor
        (smallEtaleModelRingedSite B (Spec (.of A)) hA X hX)).obj
          (op ((modelDerived B (Spec (.of A)) hA X hX).obj P))).obj
            ((modelDerived B (Spec (.of A)) hA X hX).obj L))
    (n : ℤ)
    (hN : Module.Finite A
      ((DerivedCategory.singleFunctor (Modules.{u, u} B (Spec (.of A)) hA X hX) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O)) ⟶ N⟦n⟧)) :
    Module.Finite A (P ⟶ L⟦n⟧) := by
  let Ym := smallEtaleModelRingedSite B (Spec (.of A)) hA X hX
  let e := modulesEquivModelModules B (Spec (.of A)) hA X hX
  let eD := modelDerived B (Spec (.of A)) hA X hX
  let ψ := (modelGlobalSectionRingHom B (Spec (.of A)) hA X hX).comp (baseRingHom A B hA X hX)
  let : Linear A (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Ym.O)) :=
    Stacks.SheafOfModules.linearOver _ ψ
  have : e.functor.Linear A :=
    modulesEquivModelModules_functor_linear B (Spec (.of A)) hA X hX (baseRingHom A B hA X hX)
  have : eD.IsEquivalence := Stacks.Injectives.mapDerivedCategory_isEquivalence e.functor
  let OX := (DerivedCategory.singleFunctor (Modules.{u, u} B (Spec (.of A)) hA X hX) 0).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B (Spec (.of A)) hA X hX).O))
  have h₇ : Module.Finite A (eD.obj OX ⟶ eD.obj (N⟦n⟧)) :=
    Module.Finite.of_surjective (eD.mapLinearMap A) eD.map_surjective
  let iO : RingedSite.derivedStructureSheaf Ym ≅ eD.obj OX :=
    eqToIso (RingedSite.derivedStructureSheaf_eq_singleFunctor_obj Ym) ≪≫
      (DerivedCategory.singleFunctor _ 0).mapIso
        (modulesEquivModelModulesUnitIso B (Spec (.of A)) hA X hX).symm ≪≫
      ((e.functor.mapDerivedCategorySingleFunctor 0).app _).symm
  let iR : ((RingedSite.derivedSheafHomBifunctor Ym).obj (op (eD.obj P))).obj
      ((eD.obj L)⟦n⟧) ≅ eD.obj (N⟦n⟧) :=
    ((((RingedSite.derivedSheafHomBifunctor Ym).obj (op (eD.obj P))).commShiftIso n).app
        (eD.obj L)) ≪≫ (CategoryTheory.shiftFunctor _ n).mapIso eN.symm ≪≫
      ((eD.commShiftIso n).app N).symm
  let Ψ : (eD.obj P ⟶ eD.obj (L⟦n⟧)) ≃ₗ[A] (eD.obj OX ⟶ eD.obj (N⟦n⟧)) :=
    (Linear.homCongr A (Iso.refl _) ((eD.commShiftIso n).app L)).trans
      ((RingedSite.homLinearEquivHomStructureSheafDerivedSheafHom Ym ψ (eD.obj P)
        ((eD.obj L)⟦n⟧)).trans (Linear.homCongr A iO iR))
  have : Module.Finite A (eD.obj P ⟶ eD.obj (L⟦n⟧)) := Module.Finite.equiv Ψ.symm
  exact Module.Finite.of_injective (eD.mapLinearMap A) fun _ _ h => eD.map_injective h

/-- **Maps from a bounded above perfect complex are finite.**  For `P` perfect and bounded above
and `L ∈ D⁺_Coh(𝒪_X)`, the `A`-module `Hom(P, L[n])` is finite. -/
private theorem moduleFinite_hom_shift_of_isPerfect [IsNoetherianRing A]
    (f : X ⟶ yoneda.obj (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f)
    (P L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX))
    (hP : (smallEtaleRingedSite B (Spec (.of A)) hA X hX).IsPerfect P) (c : ℤ) (hPc : P.IsLE c)
    (hL : DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L)
    (n : ℤ) : Module.Finite A (P ⟶ L⟦n⟧) := by
  obtain ⟨l, hl⟩ := hL.1
  let Ym := smallEtaleModelRingedSite B (Spec (.of A)) hA X hX
  let e := modulesEquivModelModules B (Spec (.of A)) hA X hX
  let eD := modelDerived B (Spec (.of A)) hA X hX
  have : eD.IsEquivalence := Stacks.Injectives.mapDerivedCategory_isEquivalence e.functor
  have hH : ∀ (i : ℤ) (M : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX)),
      (DerivedCategory.homologyFunctor _ i).obj (eD.obj M) ≅
        e.functor.obj ((DerivedCategory.homologyFunctor _ i).obj M) := fun i M =>
    (StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso e.functor i).app M
  have hPc' : (eD.obj P).IsLE c := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    exact (e.functor.map_isZero (((DerivedCategory.isLE_iff P _).1 hPc) i hi)).of_iso (hH i P)
  have hl' : (eD.obj L).IsGE l := by
    rw [DerivedCategory.isGE_iff]
    intro i hi
    exact (e.functor.map_isZero (hl i hi)).of_iso (hH i L)
  let Z := ((RingedSite.derivedSheafHomBifunctor Ym).obj (op (eD.obj P))).obj (eD.obj L)
  have hZ : Z.IsGE (l - c) := RingedSite.isGE_derivedSheafHom Ym (eD.obj P) (eD.obj L) c l hPc' hl'
  let N := eD.objPreimage Z
  let eN : eD.obj N ≅ Z := eD.objObjPreimageIso Z
  have hN : DerivedCategoryB.derivedCategoryBPlus
      (isCoherent.{u, u} B (Spec (.of A)) hA X hX) N := by
    refine ⟨⟨l - c, fun i hi => ?_⟩, fun i => ?_⟩
    · have hz : IsZero (e.functor.obj ((DerivedCategory.homologyFunctor _ i).obj N)) :=
        (((DerivedCategory.isGE_iff Z _).1 hZ) i hi).of_iso
          ((hH i N).symm ≪≫ (DerivedCategory.homologyFunctor _ i).mapIso eN)
      exact (e.inverse.map_isZero hz).of_iso (e.unitIso.app _)
    · exact (isCoherent_iff_isCoherentOnSite B (Spec (.of A)) hA X hX _).2
        (isCoherentOnSite_homology_of_modelDerivedSheafHom B (Spec (.of A)) hA X hX P hP L
          (fun j => (hL.2 j).toIsCoherentOnSite) N eN i)
  exact moduleFinite_hom_shift_of_modelDerivedSheafHom A B hA X hX P L N eN n
    (moduleFinite_hom_unit_of_derivedCategoryBPlus f hf N hN n)

/-- **Stacks 0D0T.**  Let `A` be a Noetherian ring and `X` an algebraic space over `A` proper over
`A`.  Let `K ∈ D⁻_Coh(𝒪_X)` and `L ∈ D⁺_Coh(𝒪_X)`.  Then `Ext^n_X(K, L) = Hom_{D(𝒪_X)}(K, L[n])`
is a finite `A`-module for every `n ∈ ℤ`. -/
@[stacks 0D0T]
theorem moduleFinite_hom_shift_of_isProper [IsNoetherianRing A]
    (f : X ⟶ yoneda.obj (baseObject A B hA)) (hf : IsProper B (Spec (.of A)) hA f)
    (K L : DerivedCategory (Modules.{u, u} B (Spec (.of A)) hA X hX))
    (hK : DerivedCategoryB.derivedCategoryBMinus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) K)
    (hL : DerivedCategoryB.derivedCategoryBPlus (isCoherent.{u, u} B (Spec (.of A)) hA X hX) L)
    (n : ℤ) : Module.Finite A (K ⟶ L⟦n⟧) := by
  have : IsLocallyNoetherian
      ((BigFppfOver.toScheme B (Spec (.of A)) hA).obj (baseObject A B hA)) :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of A)))
  have hXN : IsNoetherian B (Spec (.of A)) hA B.contains_terminal X :=
    isNoetherian_of_isProper_toAffine B (Spec (.of A)) hA (baseObject A B hA)
      (inferInstanceAs (IsAffine (Spec (.of A)))) (X := ⟨X, hX⟩) (ObjectProperty.homMk f) hf
  obtain ⟨b, hb⟩ := hK.1
  obtain ⟨l, hl⟩ := hL.1
  obtain ⟨Kc, hKc, ⟨eK⟩⟩ := isPseudoCoherent_of_isCoherent_homology_of_isNoetherian B
    (Spec (.of A)) hA ⟨X, hX⟩ B.contains_terminal hXN K hK.2 ⟨b, hb⟩
  obtain ⟨r, hr⟩ := approximationByPerfectComplexes_of_qcqs B (Spec (.of A)) hA
    B.contains_terminal X hX hXN.1 hXN.2.1 Set.univ isClosed_univ
    (isQuasiCompact_ι_openSubspace_of_eq_empty B (Spec (.of A)) hA X hX _ Set.compl_univ)
  let m := l - n
  let E : QuasicoherentDerivedCategory.{u, u} B (Spec (.of A)) hA X hX :=
    ⟨K, fun i => (hK.2 i).toIsQuasicoherentOnSite⟩
  obtain ⟨P, hPperf, -, α, hiso, hepi⟩ := hr E m ⟨Kc, hKc (m - r), ⟨eK⟩⟩
    (fun _ _ => Set.subset_univ _)
  have : L.IsGE l := (DerivedCategory.isGE_iff L l).2 hl
  have : (L⟦n⟧).IsGE m := DerivedCategory.TStructure.t.isGE_shift L l n m (by omega)
  have hPle : P.IsLE (max m b) := by
    rw [DerivedCategory.isLE_iff]
    intro i hi
    have := hiso i (by omega)
    exact (hb i (by omega)).of_iso
      (asIso ((DerivedCategory.homologyFunctor (Modules.{u, u} B (Spec (.of A)) hA X hX) i).map α))
  have := moduleFinite_hom_shift_of_isPerfect A B hA X hX f hf P L hPperf _ hPle hL n
  exact Module.Finite.of_injective (Linear.leftComp A (L⟦n⟧) α)
    (DerivedCategory.precomp_injective_of_approximatesFrom α m ⟨hiso, hepi⟩ inferInstance)

end Main

end AlgebraicGeometry.Space

end
