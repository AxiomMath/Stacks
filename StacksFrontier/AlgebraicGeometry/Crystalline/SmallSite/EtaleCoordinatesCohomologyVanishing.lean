module

public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeRestrictOpen
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.EtaleCoordinatesForms
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeAbelianDegreewise
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseQuasicoherentCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleRestrictionCohomologyULift
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ModuleUniverseComparison
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenSectionsMoore07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.OpenCechFunctorialRing07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SmoothPresentationCohomology07LH

/-!
# Crystalline cohomology of an affine scheme with a lift with `d` étale coordinates vanishes above
`d`

Let `(p, (S, I, γ), X)` be a global crystalline situation with `X` and `S` affine and `p`
nilpotent on `X`, `A = Γ(S, 𝒪_S)`, `C = Γ(X, 𝒪_X)`, and let `A → B → C` be a smooth `A`-algebra
with a surjection onto `C` carrying *étale coordinates* `t₁, …, t_d ∈ B` (the map
`A[T₁, …, T_d] → B`, `Tᵢ ↦ tᵢ`, is étale).  For every crystal `ℱ` in quasi-coherent
`𝒪_{X/S}`-modules,

`H^j(Cris(X/S), ℱ) = 0` for `j > d`.

By [Stacks, Lemma 60.21.4, Tag 07LH] (`...SmallSite.smoothPresentationPair_computesCohomology`) the
cohomology of `ℱ` is that of the completed de Rham complex `M' ⊗^∧_{D'} Ω^*_{D'}`, `D'` the
completed divided power envelope of `ker(B → C)`; and `Ω_{D'/A,δ}` is spanned by the `dtᵢ`
([Stacks, Tag 07HW], `Crystalline.subsingleton_envelopeForms_of_etale`), so its exterior powers,
and hence the terms of the complex, vanish above `d`.

## Main results

* `...SmallSite.isZero_cohomology_of_etaleCoordinates` — the vanishing, for an arbitrary smooth
  presentation with `d` étale coordinates.
* `...SmallSite.isZero_cohomology_overSituation_of_smoothLift` — the same for `Cris(U/S)`, `U`
  affine over `X`, given a smooth lift of `U`
  (`Crystalline.GlobalCrystallineSituation.CechEnvelope.SmoothLift`) with `d` étale coordinates.

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Tag 07HW](https://stacks.math.columbia.edu/tag/07HW)
* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite DividedPowers
open scoped TensorProduct

universe u

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-- The `p`-adic completion of a subsingleton module is a subsingleton. -/
theorem subsingleton_adicCompletion_of_subsingleton {R M : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] (I : Ideal R) [Subsingleton M] : Subsingleton (AdicCompletion I M) :=
  ⟨fun _ _ ↦ AdicCompletion.ext fun _ ↦ Subsingleton.elim _ _⟩

/-- A tensor product with a subsingleton right factor is a subsingleton. -/
theorem subsingleton_tensorProduct_of_subsingleton_right {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] [Subsingleton N] :
    Subsingleton (M ⊗[R] N) :=
  subsingleton_of_forall_eq 0 fun x ↦ by
    induction x using TensorProduct.induction_on with
    | zero => rfl
    | tmul m n => rw [Subsingleton.elim n 0, TensorProduct.tmul_zero]
    | add x y hx hy => rw [hx, hy, add_zero]

attribute [local instance] tensorPowerEnvelopeAlgebraInstance presentationEnvelopeAlgebraInst

section Presentation

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.X] [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.X, ⊤))) (Fc : QuasiCoherentCrystal S)

/-- **Crystalline cohomology vanishes above the number of étale coordinates of a smooth
presentation.**  Let `A → B → C = Γ(X, 𝒪_X)` with `A → B` smooth, `B → C` surjective, and
`t₁, …, t_d ∈ B` étale coordinates.  Then `H^j(Cris(X/S), ℱ) = 0` for every crystal `ℱ` in
quasi-coherent modules and every `j > d`. -/
theorem isZero_cohomology_of_etaleCoordinates {P' : Type u} [CommRing P']
    [Algebra (affineSituation S hp).A P'] [Algebra.Smooth ((affineSituation S hp).A : Type u) P']
    (f' : P' →ₐ[(affineSituation S hp).A] (affineSituation S hp).C) (hf' : Function.Surjective f')
    {d : ℕ} (t : Fin d → P')
    (ht : (MvPolynomial.aeval (R := ((affineSituation S hp).A : Type u)) t).toRingHom.Etale)
    (j : ℕ) (hj : d < j) :
    IsZero ((cohomologyFunctor S j).obj (abelianSheaf Fc.obj)) := by
  obtain ⟨a, ha, haug⟩ := exists_smoothPresentationMap (affineSituation S hp) f' hf'
  obtain ⟨e⟩ := smoothPresentationPair_computesCohomology hp Fc f' hf' a ha haug j
  refine IsZero.of_iso ?_ e.symm
  refine Functor.map_isZero _ ?_
  refine ShortComplex.isZero_homology_of_isZero_X₂ _ ?_
  have hforms : Subsingleton (dividedPowerDifferentialForms (A := ((affineSituation S hp).A :
      Type u)) (presentationEnvelope (affineSituation S hp) f').object.dividedPowers j) :=
    subsingleton_envelopeForms_of_etale (affineSituation S hp).A
      (algebraMap ((affineSituation S hp).A : Type u) P') _ _
      (presentationEnvelope (affineSituation S hp) f') t ht hj
  let R := presentationFormsData (affineSituation S hp) f'
  let M := smoothPresentationPair hp Fc f' hf' a ha
  have : Subsingleton (R.Om j) :=
    subsingleton_adicCompletion_of_subsingleton (M := dividedPowerDifferentialForms
      (A := ((affineSituation S hp).A : Type u))
      (presentationEnvelope (affineSituation S hp) f').object.dividedPowers j)
      (pAdicIdeal (A := (presentationEnvelope (affineSituation S hp) f').object)
        (affineSituation S hp).p)
  have : Subsingleton (M.carrier ⊗[R.ring] R.Om j) :=
    subsingleton_tensorProduct_of_subsingleton_right
  have : Subsingleton (CompletedTensor (affineSituation S hp).p R.ring (R.Om j) M.carrier) :=
    subsingleton_adicCompletion_of_subsingleton _
  exact AddCommGrpCat.isZero_of_subsingleton
    (AddCommGrpCat.of (CompletedTensor (affineSituation S hp).p R.ring (R.Om j) M.carrier))

universe w₁ w₂ w₃

/-- **The module form, on the big site**: for a quasi-coherent sheaf of `𝒪_{X/S}`-modules `N` on
`CRIS(X/S)` (for instance `N ⊗_A M`, `...tensorConstantModule`), the cohomology modules of
`RΓ(CRIS(X/S), N) ∈ D⁺(Mod_A)` vanish in degrees `> d`, in the presence of a smooth presentation
of `Γ(X, 𝒪_X)` with `d` étale coordinates.  The restriction of `N` to `Cris(X/S)` is a crystal in
quasi-coherent modules and has the same cohomology. -/
theorem isZero_homology_derivedBigModuleGlobalSections_of_etaleCoordinates
    [HasDerivedCategory.{w₁} (ModuleSheaf S)] [HasDerivedCategory.{w₂} (BigModuleSheaf S)]
    [HasDerivedCategory.{w₃} (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤))]
    {P' : Type u} [CommRing P']
    [Algebra (affineSituation S hp).A P'] [Algebra.Smooth ((affineSituation S hp).A : Type u) P']
    (f' : P' →ₐ[(affineSituation S hp).A] (affineSituation S hp).C) (hf' : Function.Surjective f')
    {d : ℕ} (t : Fin d → P')
    (ht : (MvPolynomial.aeval (R := ((affineSituation S hp).A : Type u)) t).toRingHom.Etale)
    (N : SheafOfModules.{u} (crystallineStructureSheaf S)) (hN : N.IsQuasicoherentOnSite)
    (i : ℤ) (hi : (d : ℤ) < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Γ(S.S.scheme, ⊤)) i).obj
      (DerivedCategory.Plus.ι.obj
        ((derivedBigModuleGlobalSections S).obj ((bigModuleULift S).obj N)))) := by
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, i = (k : ℤ) := ⟨i.toNat, by omega⟩
  let Fc : QuasiCoherentCrystal S :=
    ⟨restrictSheafOfModules N, isQuasiCoherentCrystal_restrictSheafOfModules hN⟩
  have hforget : IsZero ((forgetBaseAction S).obj
      (moduleULiftCohomology S (restrictSheafOfModules N) k)) :=
    (isZero_cohomology_of_etaleCoordinates hp Fc f' hf' t ht k (by omega)).of_iso
      (moduleULiftCohomologyIsoAbelian S (restrictSheafOfModules N) k)
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ (k : ℤ)).mapIso
    (derivedRestrictModuleGlobalSectionsULiftIso S N))
  refine IsZero.of_iso ?_
    (homologyModuleULiftDerivedGlobalSectionsIso S (restrictSheafOfModules N) k)
  exact ModuleCat.isZero_iff_subsingleton.2 (AddCommGrpCat.isZero_iff_subsingleton.1 hforget)

end Presentation

section SmoothLift

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) {U : Scheme.{u}} [IsAffine U] {j : U ⟶ S.X}
  (L : CechEnvelope.SmoothLift S j) {d : ℕ} (t : Fin d → L.ring)
  (ht : (MvPolynomial.aeval (R := (baseSectionsRing S : Type u)) t).toRingHom.Etale)

include hp ht in
/-- **Crystalline cohomology of an affine `U` over `X` with a smooth lift carrying `d` étale
coordinates vanishes above `d`**: for a smooth lift `B` of `U` over `A = Γ(S, 𝒪_S)`
(`Crystalline.GlobalCrystallineSituation.CechEnvelope.SmoothLift`) and `t₁, …, t_d ∈ B` with
`A[T₁, …, T_d] → B` étale, `H^i(Cris(U/S), ℱ) = 0` for every crystal `ℱ` in quasi-coherent modules
on `Cris(U/S)` and every `i > d`. -/
theorem isZero_cohomology_overSituation_of_smoothLift
    (Fc : QuasiCoherentCrystal (overSituation S j)) (i : ℕ) (hi : d < i) :
    IsZero ((cohomologyFunctor (overSituation S j) i).obj (abelianSheaf Fc.obj)) := by
  have : IsAffine (overSituation S j).X := ‹IsAffine U›
  have : IsAffine (overSituation S j).S.scheme := ‹IsAffine S.S.scheme›
  let hp' := CechEnvelope.isNilpotent_prime_over S j hp
  let : Algebra (affineSituation (overSituation S j) hp').A L.ring := L.algebra
  have : Algebra.Smooth ((affineSituation (overSituation S j) hp').A : Type u) L.ring :=
    L.smooth
  let f' : L.ring →ₐ[(affineSituation (overSituation S j) hp').A]
      (affineSituation (overSituation S j) hp').C :=
    { toRingHom := L.toSections
      commutes' := L.toSections_algebraMap }
  exact isZero_cohomology_of_etaleCoordinates hp' Fc f' L.surjective_toSections t ht i hi

end SmoothLift

section Restrict

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme]
  (hp : IsNilpotent (S.p : Γ(S.S.scheme, ⊤))) (V : S.X.Opens) (hV : IsAffineOpen V)
  (hVW : V ≤ sourceToBase S ⁻¹ᵁ ⊤)
  (L : CechEnvelope.SmoothLift S V.ι) {d : ℕ} (t : Fin d → L.ring)
  (ht : (MvPolynomial.aeval (R := (baseSectionsRing S : Type u)) t).toRingHom.Etale)

/-- The restriction `Γ(S, 𝒪_S) → Γ(S|_⊤, 𝒪)` to the open subscheme `⊤`, a ring isomorphism. -/
def topRestrictRingEquiv :
    Γ(S.S.scheme, ⊤) ≃+* Γ((restrict S ⊤ V hVW).S.scheme, ⊤) :=
  (Scheme.Γ.mapIso (Scheme.topIso S.S.scheme).op).commRingCatIsoToRingEquiv

omit [IsAffine S.S.scheme] in
/-- `topRestrictRingEquiv` is the map on global sections of the inclusion of `⊤`. -/
theorem topRestrictRingEquiv_apply (a : Γ(S.S.scheme, ⊤)) :
    topRestrictRingEquiv V hVW a = (restrictSι S ⊤ V hVW).hom.appTop a := rfl

omit [IsAffine S.S.scheme] in
/-- The structure maps on global sections of `U ⟶ S` and of `U ⟶ S|_⊤` agree through
`topRestrictRingEquiv`. -/
theorem sourceToBase_overSituation_appTop (a : Γ(S.S.scheme, ⊤)) :
    (sourceToBase (overSituation S V.ι)).appTop a =
      (sourceToBase (restrict S ⊤ V hVW)).appTop (topRestrictRingEquiv V hVW a) := by
  have h := congrArg Scheme.Hom.appTop (sourceToBase_restrict_comp_ι S ⊤ V hVW)
  have h' : sourceToBase (overSituation S V.ι) = V.ι ≫ sourceToBase S := Category.assoc _ _ _
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop] at h
  rw [h', Scheme.Hom.comp_appTop, topRestrictRingEquiv_apply]
  exact (ConcreteCategory.congr_hom h a).symm

include hp hV ht in
/-- **The vanishing in the restricted-site form of `...SmallSite.LocallyVanishingAbove`**: for an
affine open `V` of `X` with a smooth lift carrying `d` étale coordinates and a crystal `ℱ` in
quasi-coherent modules on `Cris(X/S)`, `H^j(Cris(V/S|_⊤), ℱ|) = 0` for `j > d`.  The lift is
read over `Γ(S|_⊤) ≅ Γ(S)` and `isZero_cohomology_of_etaleCoordinates` is applied to the
restricted situation, whose crystal is the restriction of `ℱ`. -/
theorem subsingleton_cohomology_restrict_of_smoothLift (Fc : QuasiCoherentCrystal S) (j : ℕ)
    (hj : d < j) :
    Subsingleton (cohomology (restrict S ⊤ V hVW)
      ((smallExtendAbelianRestriction S ⊤ V hVW).obj (abelianSheaf Fc.obj)) j) := by
  have : IsAffine (restrict S ⊤ V hVW).X := hV
  have : IsAffine (restrict S ⊤ V hVW).S.scheme := isAffineOpen_top S.S.scheme
  let hp' := isNilpotent_prime_openSituation07Q9 S hV hVW
  let ε := topRestrictRingEquiv V hVW
  let A' := ((affineSituation (restrict S ⊤ V hVW) hp').A : Type u)
  let ε' : A' ≃+* (baseSectionsRing S : Type u) := ε.symm
  let : Algebra A' L.ring := ((algebraMap (baseSectionsRing S) L.ring).comp
    ε'.toRingHom).toAlgebra
  have hsm : (algebraMap A' L.ring).Smooth := by
    refine RingHom.Smooth.comp ?_ (RingHom.smooth_algebraMap.2 L.smooth)
    exact ((RingHom.etale_iff_formallyUnramified_and_smooth _).1
      (RingHom.Etale.of_bijective ε'.bijective)).2
  have : Algebra.Smooth A' L.ring := RingHom.smooth_algebraMap.1 hsm
  let f' : L.ring →ₐ[A'] (affineSituation (restrict S ⊤ V hVW) hp').C :=
    { toRingHom := L.toSections
      commutes' := fun a ↦ (L.toSections_algebraMap (ε' a)).trans
        ((sourceToBase_overSituation_appTop V hVW (ε' a)).trans
          (congrArg (sourceToBase (restrict S ⊤ V hVW)).appTop.hom (ε.apply_symm_apply a))) }
  have ht' : (MvPolynomial.aeval (R := A') t).toRingHom.Etale := by
    have heq : (MvPolynomial.aeval (R := A') t).toRingHom =
        (MvPolynomial.aeval (R := (baseSectionsRing S : Type u)) t).toRingHom.comp
          (MvPolynomial.mapEquiv (Fin d) ε').toRingHom := by
      refine MvPolynomial.ringHom_ext (fun a ↦ ?_) (fun i ↦ ?_)
      · rw [RingHom.comp_apply]
        simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.mapEquiv_apply,
          MvPolynomial.map_C, AlgHom.toRingHom_eq_coe, MvPolynomial.aeval_C]
        rfl
      · rw [RingHom.comp_apply]
        simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, MvPolynomial.mapEquiv_apply,
          MvPolynomial.map_X, AlgHom.toRingHom_eq_coe, MvPolynomial.aeval_X]
    rw [heq]
    exact RingHom.Etale.respectsIso.2 _ _ ht
  exact AddCommGrpCat.isZero_iff_subsingleton.1 (isZero_cohomology_of_etaleCoordinates hp'
    (restrictCrystal07Q9 S ⊤ V hVW Fc.obj Fc.property) f' L.surjective_toSections t ht' j hj)

omit hVW in
include hp hV ht in
/-- **The hypothesis of `...SmallSite.CohomologicalDimensionFiniteCover` on one affine open**, for
an affine open `V` of `X` carrying a smooth lift with `d` étale coordinates (for instance a
nonempty finite intersection of coordinate charts,
`...CechEnvelope.exists_smoothLift_etaleCoordinates_inter`): there is an open `W` of `S` through
which `V` maps such that the cohomology of the restricted site vanishes above `d`. -/
theorem exists_restrict_subsingleton_cohomology_of_smoothLift (Fc : QuasiCoherentCrystal S) :
    ∃ (W : S.S.scheme.Opens) (hVW : V ≤ sourceToBase S ⁻¹ᵁ W), ∀ j : ℕ, d < j →
      Subsingleton (cohomology (restrict S W V hVW)
        ((smallExtendAbelianRestriction S W V hVW).obj (abelianSheaf Fc.obj)) j) :=
  ⟨⊤, by simp, fun j hj ↦ subsingleton_cohomology_restrict_of_smoothLift hp V hV _ L t ht Fc j hj⟩

end Restrict

end Crystalline.GlobalCrystallineSituation.SmallSite
