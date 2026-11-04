module

public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.Algebra.Module.InjectiveNearPrime

/-!
# Minimal chain models of bounded complexes of finite projective modules

Let `A` be a ring, `p` a prime of `A` and `P` a bounded complex of finite projective
`A`-modules. [Stacks, Tag 0BCD] produces, over a principal localization `A_f` with `f ∉ p`, a
bounded complex of finite free `A_f`-modules whose term in degree `i` has rank
`dim_{κ(p)} Hⁱ(P ⊗_A κ(p))` and which represents `P ⊗_A A_f` in the derived category.

This file reads that statement back at the level of complexes: the minimal complex is
*homotopy equivalent* to the termwise extension of scalars `P ⊗_A A_f`, and the fibre
dimensions are those of the homology of the termwise base change `P ⊗_A κ(p)`. Both
translations come from the fact that bounded above complexes of projective modules compute
derived extension of scalars and are K-projective, so that an isomorphism of the derived
category between two of them is induced by a homotopy equivalence.

## Main results

* `StacksDraft.Perfect.exists_away_homotopyEquiv_free_model`: the chain-level form of
  [Stacks, Tag 0BCD] for a bounded complex of finite projective modules.

## References

* [Stacks Project, Tag 0BCD](https://stacks.math.columbia.edu/tag/0BCD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex.DerivedExtensionScalars

universe u

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

variable {A : Type u} [CommRing A]

/-- The termwise extension of scalars of a complex of `A`-modules along `φ : A →+* B`. -/
abbrev baseChangeComplex {B : Type u} [CommRing B] (φ : A →+* B)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) : CochainComplex (ModuleCat.{u} B) ℤ :=
  ((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj P

/-- A derived isomorphism between two bounded above complexes of projective modules is induced
by a homotopy equivalence. -/
private theorem nonempty_homotopyEquiv_of_derivedIso {R : Type u} [CommRing R]
    (M N : CochainComplex (ModuleCat.{u} R) ℤ) (b c : ℤ) [M.IsStrictlyLE b] [N.IsStrictlyLE c]
    [∀ i, Projective (M.X i)] [∀ i, Projective (N.X i)]
    (e : DerivedCategory.Q.obj M ≅ DerivedCategory.Q.obj N) :
    Nonempty (HomotopyEquiv M N) := by
  have : M.IsKProjective := CochainComplex.isKProjective_of_projective M b
  have : N.IsKProjective := CochainComplex.isKProjective_of_projective N c
  let E : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj M) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj N) :=
    (DerivedCategory.quotientCompQhIso _).app M ≪≫ e ≪≫
      ((DerivedCategory.quotientCompQhIso _).app N).symm
  obtain ⟨f, hf⟩ := (CochainComplex.IsKProjective.Qh_map_bijective M
    ((HomotopyCategory.quotient _ _).obj N)).surjective E.hom
  obtain ⟨g, hg⟩ := (CochainComplex.IsKProjective.Qh_map_bijective N
    ((HomotopyCategory.quotient _ _).obj M)).surjective E.inv
  have hfg : f ≫ g = 𝟙 _ := (CochainComplex.IsKProjective.Qh_map_bijective M
    ((HomotopyCategory.quotient _ _).obj M)).injective (by
      rw [Functor.map_comp, hf, hg, E.hom_inv_id]
      simp)
  have hgf : g ≫ f = 𝟙 _ := (CochainComplex.IsKProjective.Qh_map_bijective N
    ((HomotopyCategory.quotient _ _).obj N)).injective (by
      rw [Functor.map_comp, hg, hf, E.inv_hom_id]
      simp)
  exact ⟨HomotopyCategory.homotopyEquivOfIso
    { hom := f, inv := g, hom_inv_id := hfg, inv_hom_id := hgf }⟩

/-- A bounded above complex of projective modules computes derived extension of scalars. -/
private def totalDerivedIsoOfProjective {B : Type u} [CommRing B] {φ : A →+* B}
    (D : TotalDerivedExtensionScalars.{u, u, u} φ) (P : CochainComplex (ModuleCat.{u} A) ℤ)
    (b : ℤ) [P.IsStrictlyLE b] [∀ i, Projective (P.X i)] :
    D.functor.obj (DerivedCategory.Q.obj P) ≅ DerivedCategory.Q.obj (baseChangeComplex φ P) :=
  @asIso _ _ _ _ (D.comparison.app P) (D.comparison_isIso_of_projective P b)

/-- **The chain-level form of [Stacks, Tag 0BCD].** Let `P` be a bounded complex of finite
projective `A`-modules and `p` a prime of `A`. There are `f ∉ p` and a complex `Q` of
`A_f`-modules whose term in degree `i` is free of rank `dim_{κ(p)} Hⁱ(P ⊗_A κ(p))`, together with
a homotopy equivalence between `Q` and the termwise extension of scalars `P ⊗_A A_f`. -/
theorem exists_away_homotopyEquiv_free_model (p : Ideal A) [p.IsPrime]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfin : ∀ i, Module.Finite A (P.X i)) (hproj : ∀ i, Module.Projective A (P.X i)) :
    ∃ f : A, f ∉ p ∧ ∃ Q : CochainComplex (ModuleCat.{u} (Localization.Away f)) ℤ,
      (∃ a' b' : ℤ, Q.IsStrictlyGE a' ∧ Q.IsStrictlyLE b') ∧
      (∀ i, Nonempty (Q.X i ≅ ModuleCat.of (Localization.Away f)
        (ULift.{u} (Fin (Module.finrank p.ResidueField
          ((baseChangeComplex (algebraMap A p.ResidueField) P).homology i)) →
            Localization.Away f)))) ∧
      Nonempty (HomotopyEquiv Q (baseChangeComplex (algebraMap A (Localization.Away f)) P)) := by
  classical
  have hprojc : ∀ i, Projective (P.X i) := fun i =>
    have := hproj i
    ModuleCat.projective_of_categoryTheory_projective (P.X i)
  have hK : IsPerfect (DerivedCategory.Q.obj P) :=
    ⟨P, a, b, inferInstance, inferInstance, hfin, hproj, ⟨Iso.refl _⟩⟩
  obtain ⟨-, -, f, hf, Q, a', b', hQa, hQb, hQX, ⟨eQ⟩⟩ :=
    exists_away_bounded_free_complex_representing.{u, u} p (DerivedCategory.Q.obj P) hK
  refine ⟨f, hf, Q, ⟨a', b', hQa, hQb⟩, fun i => ?_, ?_⟩
  · obtain ⟨e⟩ := hQX i
    let Dk := totalDerivedExtensionScalars.{u, u, u} (algebraMap A p.ResidueField)
    have hr := ((DerivedCategory.homologyFunctor (ModuleCat.{u} p.ResidueField) i).mapIso
      (totalDerivedIsoOfProjective Dk P b) ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} p.ResidueField) i).app
          (baseChangeComplex (algebraMap A p.ResidueField) P)).toLinearEquiv.finrank_eq
    have hr' : Module.finrank p.ResidueField
        ((baseChangeComplex (algebraMap A p.ResidueField) P).homology i) =
        Module.finrank p.ResidueField ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} p.ResidueField) i).obj (Dk.functor.obj (DerivedCategory.Q.obj P))) :=
      hr.symm
    rw [hr']
    exact ⟨e⟩
  · have : Q.IsStrictlyLE b' := hQb
    have hQproj : ∀ i, Projective (Q.X i) := fun i =>
      Projective.of_iso (hQX i).some.symm inferInstance
    let Df := totalDerivedExtensionScalars.{u, u, u} (algebraMap A (Localization.Away f))
    have : (baseChangeComplex (algebraMap A (Localization.Away f)) P).IsStrictlyLE b := by
      dsimp only [baseChangeComplex]
      infer_instance
    have hPproj : ∀ i, Projective ((baseChangeComplex (algebraMap A
        (Localization.Away f)) P).X i) := fun i =>
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u} _).map_projective (P.X i) inferInstance
    exact nonempty_homotopyEquiv_of_derivedIso Q _ b' b
      (eQ ≪≫ totalDerivedIsoOfProjective Df P b)

/-! ### Comparing two minimal models -/

/-- **A chain map which is a monomorphism on homology in a degree where the source has zero
incoming and outgoing differentials is a monomorphism in that degree.** In that degree the
source term *is* its homology. -/
theorem mono_f_of_mono_homologyMap {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (ψ : K ⟶ L) {j i k : ℤ} (hj : j + 1 = i) (hk : i + 1 = k)
    (hin : K.d j i = 0) (hout : K.d i k = 0) [Mono (HomologicalComplex.homologyMap ψ i)] :
    Mono (ψ.f i) := by
  have := K.isIso_iCycles i k (by simp [← hk]) hout
  have := K.isIso_homologyπ j i (by simp [← hj]) hin
  refine ⟨fun x y hxy => ?_⟩
  have h1 : (x ≫ inv (K.iCycles i) ≫ HomologicalComplex.cyclesMap ψ i) ≫ L.iCycles i =
      (y ≫ inv (K.iCycles i) ≫ HomologicalComplex.cyclesMap ψ i) ≫ L.iCycles i := by
    simp only [Category.assoc, HomologicalComplex.cyclesMap_i, IsIso.inv_hom_id_assoc, hxy]
  have h2 := (cancel_mono (L.iCycles i)).1 h1
  have h3 : (x ≫ inv (K.iCycles i) ≫ K.homologyπ i) ≫ HomologicalComplex.homologyMap ψ i =
      (y ≫ inv (K.iCycles i) ≫ K.homologyπ i) ≫ HomologicalComplex.homologyMap ψ i := by
    simp only [Category.assoc, HomologicalComplex.homologyπ_naturality]
    simp only [← Category.assoc] at h2 ⊢
    rw [h2]
  have h4 := (cancel_mono (HomologicalComplex.homologyMap ψ i)).1 h3
  exact (cancel_mono (inv (K.iCycles i) ≫ K.homologyπ i)).1 (by
    simpa only [Category.assoc] using h4)

/-- Two `R`-algebra structures on the same ring which agree as ring homomorphisms give the same
injectivity statement for the base change of a linear map. -/
private theorem injective_baseChange_congr {R S M N : Type u} [CommRing R] [CommRing S]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] (a₁ a₂ : Algebra R S)
    (h : a₁ = a₂) (b : M →ₗ[R] N) :
    (letI := a₁; Function.Injective (b.baseChange S)) →
      (letI := a₂; Function.Injective (b.baseChange S)) := by
  subst h
  exact id

/-- **Comparison of two complexes with minimal first differentials.** Let `φ : P ⟶ P'` be a chain
map of complexes of `R`-modules with `P¹` finite and `P'¹` finite projective, and let `χ : R → K`
be a ring map to a field such that the differentials `P⁰ → P¹ → P²` vanish after base change to
`K` and the map `H¹(P ⊗ K) → H¹(P' ⊗ K)` is injective. Then there is `g` with `χ g ≠ 0` such that
for every ring map `ψ : R → B` inverting `g`, the differential `P⁰ ⊗ B → P¹ ⊗ B` vanishes as soon
as `(φ⁰ ⊗ B) ≫ d'` does. -/
theorem exists_ne_zero_d_eq_zero_of_comp_eq_zero {R : Type u} [CommRing R] {K : Type u} [Field K]
    (χ : R →+* K) {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (φ : P ⟶ P')
    [Module.Finite R (P.X 1)] [Module.Finite R (P'.X 1)] [Module.Projective R (P'.X 1)]
    (hmin0 : (baseChangeComplex χ P).d 0 1 = 0) (hmin1 : (baseChangeComplex χ P).d 1 2 = 0)
    (hH1 : Mono (HomologicalComplex.homologyMap
      (((ModuleCat.extendScalars.{u, u, u} χ).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ) 1)) :
    ∃ g : R, χ g ≠ 0 ∧ ∀ (B : Type u) [CommRing B] (ψ : R →+* B), IsUnit (ψ g) →
      (((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex (ComplexShape.up ℤ)).map
          φ).f 0 ≫ (baseChangeComplex ψ P').d 0 1 = 0 →
        (baseChangeComplex ψ P).d 0 1 = 0 := by
  have hmono := mono_f_of_mono_homologyMap
    (((ModuleCat.extendScalars.{u, u, u} χ).mapHomologicalComplex
      (ComplexShape.up ℤ)).map φ) (j := 0) (i := 1) (k := 2) rfl rfl hmin0 hmin1
  have key : ∀ (B : Type u) [CommRing B] (ψ : R →+* B),
      Mono ((ModuleCat.extendScalars.{u, u, u} ψ).map (φ.f 1)) ↔
        letI := ψ.toAlgebra; Function.Injective ((φ.f 1).hom.baseChange B) :=
    fun B _ ψ => ⟨fun h => injective_baseChange_congr _ _
      (Algebra.algebra_ext _ _ fun _ => rfl) _ ((ModuleCat.mono_iff_injective _).1 h),
      fun h => (ModuleCat.mono_iff_injective _).2 (injective_baseChange_congr _ _
        (Algebra.algebra_ext _ _ fun _ => rfl) _ h)⟩
  obtain ⟨g, hg, hB⟩ := exists_ne_zero_injective_baseChange_of_injective_field χ (φ.f 1).hom
    ((key K χ).1 hmono)
  refine ⟨g, hg, fun B _ ψ hψ hcomp => ?_⟩
  let : Algebra R B := ψ.toAlgebra
  have := (key B ψ).2 (hB B hψ)
  refine (cancel_mono ((ModuleCat.extendScalars.{u, u, u} ψ).map (φ.f 1))).1 ?_
  rw [Limits.zero_comp]
  exact ((((ModuleCat.extendScalars.{u, u, u} ψ).mapHomologicalComplex
    (ComplexShape.up ℤ)).map φ).comm 0 1).symm.trans hcomp

/-! ### Persistence under further localization, and minimality -/

/-- Termwise extension of scalars composes, at a complex. -/
def baseChangeComplexCompIso {B C : Type u} [CommRing B] [CommRing C] (φ : A →+* B)
    (ψ : B →+* C) (P : CochainComplex (ModuleCat.{u} A) ℤ) :
    baseChangeComplex ψ (baseChangeComplex φ P) ≅ baseChangeComplex (ψ.comp φ) P :=
  (Functor.mapHomologicalComplexCompIso (ModuleCat.extendScalarsComp φ ψ).symm
    (ComplexShape.up ℤ)).app P

/-- **The chain-level form of [Stacks, Tag 0BCD], valid over every algebra inverting one
element.** For a bounded complex `P` of finite projective `A`-modules and a prime `p`, there is
`f ∉ p` such that over every `A`-algebra `R` in which `f` is a unit, `P ⊗_A R` is homotopy
equivalent to a complex whose term in degree `i` is free of rank `dim_{κ(p)} Hⁱ(P ⊗_A κ(p))`. -/
theorem exists_homotopyEquiv_free_model_of_isUnit (p : Ideal A) [p.IsPrime]
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (a b : ℤ) [P.IsStrictlyGE a] [P.IsStrictlyLE b]
    (hfin : ∀ i, Module.Finite A (P.X i)) (hproj : ∀ i, Module.Projective A (P.X i)) :
    ∃ f : A, f ∉ p ∧ ∀ (R : Type u) [CommRing R] (φ : A →+* R), IsUnit (φ f) →
      ∃ Q : CochainComplex (ModuleCat.{u} R) ℤ,
        (∃ a' b' : ℤ, Q.IsStrictlyGE a' ∧ Q.IsStrictlyLE b') ∧
        (∀ i, Nonempty (Q.X i ≅ ModuleCat.of R
          (ULift.{u} (Fin (Module.finrank p.ResidueField
            ((baseChangeComplex (algebraMap A p.ResidueField) P).homology i)) → R)))) ∧
        Nonempty (HomotopyEquiv Q (baseChangeComplex φ P)) := by
  obtain ⟨f, hf, Q, ⟨a', b', hQa, hQb⟩, hQX, ⟨e⟩⟩ :=
    exists_away_homotopyEquiv_free_model p P a b hfin hproj
  refine ⟨f, hf, fun R _ φ hφ => ?_⟩
  let ι : Localization.Away f →+* R := IsLocalization.Away.lift f hφ
  have hι : ι.comp (algebraMap A (Localization.Away f)) = φ := IsLocalization.Away.lift_comp f hφ
  let F := ModuleCat.extendScalars.{u, u, u} ι
  refine ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q, ⟨a', b', ?_, ?_⟩, fun i => ?_, ?_⟩
  · dsimp only [F]
    infer_instance
  · dsimp only [F]
    infer_instance
  · obtain ⟨eX⟩ := hQX i
    obtain ⟨eF⟩ := extendScalars_standard_free_iso.{u, u} ι (Module.finrank p.ResidueField
      ((baseChangeComplex (algebraMap A p.ResidueField) P).homology i))
    exact ⟨F.mapIso eX ≪≫ eF⟩
  · refine ⟨(F.mapHomotopyEquiv e).trans (HomotopyEquiv.ofIso ?_)⟩
    refine baseChangeComplexCompIso (algebraMap A (Localization.Away f)) ι P ≪≫ ?_
    rw [hι]

/-- **A complex of finite-dimensional vector spaces whose homology in a degree is as large as
the term vanishes on the differential out of that degree.** -/
theorem d_eq_zero_of_finrank_homology_eq {K : Type u} [Field K]
    (V : CochainComplex (ModuleCat.{u} K) ℤ) (i j : ℤ) (_hij : i + 1 = j)
    [FiniteDimensional K (V.X i)]
    (h : Module.finrank K (V.homology i) = Module.finrank K (V.X i)) : V.d i j = 0 := by
  have hinj : Function.Injective (V.iCycles i).hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  have : FiniteDimensional K (V.cycles i) := Module.Finite.of_injective (V.iCycles i).hom hinj
  have h1 : Module.finrank K (V.homology i) ≤ Module.finrank K (V.cycles i) :=
    LinearMap.finrank_le_finrank_of_surjective
      ((ModuleCat.epi_iff_surjective (V.homologyπ i)).1 inferInstance)
  have h2 : Module.finrank K (V.cycles i) ≤ Module.finrank K (V.X i) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  have h3 : Module.finrank K (V.cycles i) = Module.finrank K (V.X i) := by omega
  have : Epi (V.iCycles i) := (ModuleCat.epi_iff_surjective _).2
    ((LinearMap.injective_iff_surjective_of_finrank_eq_finrank h3).1 hinj)
  refine (cancel_epi (V.iCycles i)).1 ?_
  rw [HomologicalComplex.iCycles_d, Limits.comp_zero]

end StacksDraft.Perfect

end
