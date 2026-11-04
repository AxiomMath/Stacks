module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociatedFieldExtension

/-!
# Weakly associated points along an open immersion

Weak association of a point to an `𝒪_X`-module is a condition on the stalk, so it is
transported by any isomorphism identifying stalks semilinearly over an isomorphism of local
rings. Three consequences are collected here and used throughout the étale-localization
results of Stacks 38.5:

* weak association is invariant under an isomorphism of `𝒪_X`-modules;
* for an open immersion `j : X ⟶ Y` a point is weakly associated to the restriction, or
  equivalently to the pullback, of an `𝒪_Y`-module exactly when its image is weakly associated
  to the module itself;
* on an affine scheme, weak association of a point is weak association of the corresponding
  prime to the module of global sections.

## Main results

* `AlgebraicGeometry.isWeaklyAssociatedPrime_iff_of_semilinearEquiv`: weak association of a
  prime transfers along an additive bijection which is semilinear over a ring isomorphism.
* `AlgebraicGeometry.isWeaklyAssociatedPoint_iff_of_iso`: invariance under an isomorphism of
  sheaves of modules.
* `AlgebraicGeometry.isWeaklyAssociatedPoint_restrict_iff` and
  `AlgebraicGeometry.isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion`: the two forms of
  the statement for an open immersion.
* `Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion`: the
pullback of a
  quasi-coherent module along an open immersion is quasi-coherent.
* `AlgebraicGeometry.isWeaklyAssociatedPoint_Spec_iff`: the affine comparison, with the module
  of global sections written through `AlgebraicGeometry.moduleSpecΓFunctor`.

## Implementation notes

The scalar compatibility of the stalk isomorphism attached to a restriction is checked on
germs: `Mathlib.AlgebraicGeometry.Scheme.Modules.germ_restrictStalkNatIso_hom_app` says the
isomorphism sends the germ of a section over `U` to the germ of the same section over
`j ''ᵁ U`, and `Mathlib.AlgebraicGeometry.Scheme.Modules.smul_restrictAppIso_hom_apply`
identifies the two scalar actions. Both sides of the required equation are rewritten through
`PresheafOfModules.germ_smul` rather than unfolded, so no transparency adjustment is needed.

## References

* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
* [Stacks Project, Tag 056M](https://stacks.math.columbia.edu/tag/056M)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- A weakly associated prime maps to a weakly associated prime along an additive bijection of
modules which is semilinear over a ring isomorphism. -/
private theorem IsWeaklyAssociatedPrime.map_of_semilinearEquiv {R S M N : Type*} [CommRing R]
    [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (e : R ≃+* S)
    (f : M ≃+ N) (hf : ∀ r m, f (r • m) = e r • f m) {p : Ideal R}
    (hp : IsWeaklyAssociatedPrime R M p) :
    IsWeaklyAssociatedPrime S N (p.map e.toRingHom) := by
  obtain ⟨m, hm⟩ := hp
  refine ⟨f m, ?_⟩
  have hann : (S ∙ f m).annihilator.comap e.toRingHom = (R ∙ m).annihilator := by
    ext r
    simp only [Ideal.mem_comap, Submodule.mem_annihilator_span_singleton]
    show e r • f m = 0 ↔ r • m = 0
    rw [← hf]
    simpa only [map_zero] using (f.injective.eq_iff (a := r • m) (b := 0))
  rw [← hann] at hm
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_comap_eq e.toRingHom p hm
  rwa [← hqp, Ideal.map_comap_of_surjective e.toRingHom e.surjective q]

/-- Weak association of a prime transfers along an additive bijection of modules which is
semilinear over a ring isomorphism. -/
theorem isWeaklyAssociatedPrime_iff_of_semilinearEquiv {R S M N : Type*} [CommRing R]
    [CommRing S] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N] (e : R ≃+* S)
    (f : M ≃+ N) (hf : ∀ r m, f (r • m) = e r • f m) (p : Ideal R) :
    IsWeaklyAssociatedPrime R M p ↔ IsWeaklyAssociatedPrime S N (p.map e.toRingHom) := by
  refine ⟨IsWeaklyAssociatedPrime.map_of_semilinearEquiv e f hf, fun hp => ?_⟩
  have hf' : ∀ s n, f.symm (s • n) = e.symm s • f.symm n := fun s n =>
    f.injective (by simp only [f.apply_symm_apply, hf, e.apply_symm_apply])
  have h := IsWeaklyAssociatedPrime.map_of_semilinearEquiv e.symm f.symm hf' hp
  rwa [RingEquiv.toRingHom_eq_coe, RingEquiv.toRingHom_eq_coe, Ideal.map_of_equiv] at h

/-- Weak association of a point is invariant under an isomorphism of `𝒪_X`-modules. -/
theorem isWeaklyAssociatedPoint_iff_of_iso {X : Scheme.{u}} {F G : X.Modules} (e : F ≅ G)
    (x : X) :
    Stacks.Divisors.IsWeaklyAssociatedPoint F x ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint G x := by
  have forward {F G : X.Modules} (e : F ≅ G) (hx : Stacks.Divisors.IsWeaklyAssociatedPoint F x) :
      Stacks.Divisors.IsWeaklyAssociatedPoint G x := by
    let f : (F : OXModule X.toRingedSpace) ⟶ (G : OXModule X.toRingedSpace) := e.hom
    let g : (G : OXModule X.toRingedSpace) ⟶ (F : OXModule X.toRingedSpace) := e.inv
    have hfg : f ≫ g = 𝟙 _ := e.hom_inv_id
    have hfmono : Mono f := ⟨fun a b h => by
      simpa only [Category.assoc, hfg, Category.comp_id] using congrArg (· ≫ g) h⟩
    change IsWeaklyAssociatedPrime _ (OXModule.stalk F x) _ at hx
    show IsWeaklyAssociatedPrime _ (OXModule.stalk G x) _
    exact Module.weaklyAssociatedPrimes_subset_of_injective
      (f := OXModule.stalkLinearMap F G f x)
      (@OXModule.stalkMapAdd_injective_of_mono _ F G f hfmono x) hx
  exact ⟨forward e, forward e.symm⟩

/-- The inverse of the stalk map of an open immersion sends a germ over `U` to the germ over
`j ''ᵁ U` of the corresponding section. -/
private theorem commRingCatIsoToRingEquiv_asIso_stalkMap_symm_germ {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] {x : X} (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
    (asIso (j.stalkMap x)).symm.commRingCatIsoToRingEquiv (X.presheaf.germ U x hx a) =
      Y.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa) ((j.appIso U).inv a) := by
  apply (asIso (j.stalkMap x)).symm.commRingCatIsoToRingEquiv.symm.injective
  simp only [RingEquiv.symm_apply_apply]
  show X.presheaf.germ U x hx a =
    j.stalkMap x (Y.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa) ((j.appIso U).inv a))
  rw [j.germ_stalkMap_apply, Scheme.Hom.appIso_inv_app_apply]
  exact (X.presheaf.germ_res_apply _ _ _ _).symm

/-- Weak association of a point of an open subscheme to the restriction of a module is weak
association of its image to the module. -/
theorem isWeaklyAssociatedPoint_restrict_iff {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (G : Y.Modules) (x : X) :
    Stacks.Divisors.IsWeaklyAssociatedPoint (Scheme.Modules.restrict G j) x ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint G (j.base x) := by
  let e : (X.presheaf.stalk x) ≃+* (Y.presheaf.stalk (j.base x)) :=
    (asIso (j.stalkMap x)).symm.commRingCatIsoToRingEquiv
  let f : OXModule.stalk (Scheme.Modules.restrict G j) x ≃+ OXModule.stalk G (j.base x) :=
    ((Scheme.Modules.restrictStalkNatIso j x).app G).addCommGroupIsoToAddEquiv
  have he (U : X.Opens) (hx : x ∈ U) (a : Γ(X, U)) :
      e (X.presheaf.germ U x hx a) =
        Y.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa) ((j.appIso U).inv a) :=
    commRingCatIsoToRingEquiv_asIso_stalkMap_symm_germ j U hx a
  have hf : ∀ r m, f (r • m) = e r • f m := by
    intro r m
    obtain ⟨U₁, hx₁, a, ha⟩ := TopCat.Presheaf.exists_germ_eq X.presheaf r
    obtain ⟨U₂, hx₂, t, ht⟩ :=
      TopCat.Presheaf.exists_germ_eq (Scheme.Modules.restrict G j).presheaf m
    let U := U₁ ⊓ U₂
    let a' := X.presheaf.map (homOfLE (inf_le_left : U ≤ U₁)).op a
    let t' := (Scheme.Modules.restrict G j).presheaf.map
      (homOfLE (inf_le_right : U ≤ U₂)).op t
    have hx : x ∈ U := ⟨hx₁, hx₂⟩
    have ha' : X.presheaf.germ U x hx a' = r := by rwa [TopCat.Presheaf.germ_res_apply]
    have ht' : (Scheme.Modules.restrict G j).presheaf.germ U x hx t' = m := by
      rwa [TopCat.Presheaf.germ_res_apply]
    have hfm (s : Γ(Scheme.Modules.restrict G j, U)) :
        f ((Scheme.Modules.restrict G j).presheaf.germ U x hx s) =
          G.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa) s :=
      ConcreteCategory.congr_hom
        (Scheme.Modules.germ_restrictStalkNatIso_hom_app j x G hx) s
    rw [← ha', ← ht']
    refine (congrArg f
      (PresheafOfModules.germ_smul (Scheme.Modules.restrict G j).val x U hx a' t').symm).trans ?_
    refine (hfm (a' • t')).trans ?_
    rw [he, hfm]
    have hs := Scheme.Modules.smul_restrictAppIso_hom_apply j G U a' t'
    change a' • t' = (G.smul ((j.appIso U).inv a')).hom t' at hs
    rw [hs]
    let z : Γ(G, j ''ᵁ U) := t'
    show G.presheaf.germ (j ''ᵁ U) (j.base x) (by simpa)
      ((G.smul ((j.appIso U).inv a')).hom z) = _
    rw [G.smul_apply ((j.appIso U).inv a') z]
    show TopCat.Presheaf.germ G.val.presheaf (j ''ᵁ U) (j.base x) (by simpa)
      (((j.appIso U).inv a') • z) = _
    exact PresheafOfModules.germ_smul G.val (j.base x) (j ''ᵁ U) (by simpa)
      ((j.appIso U).inv a') z
  show IsWeaklyAssociatedPrime _ (OXModule.stalk (Scheme.Modules.restrict G j) x) _ ↔
    IsWeaklyAssociatedPrime _ (OXModule.stalk G (j.base x)) _
  rw [← IsLocalRing.map_ringEquiv_maximalIdeal e]
  exact isWeaklyAssociatedPrime_iff_of_semilinearEquiv e f hf _

/-- Weak association of a point of an open subscheme to the pullback of a module is weak
association of its image to the module. -/
theorem isWeaklyAssociatedPoint_pullback_iff_of_isOpenImmersion {X Y : Scheme.{u}} (j : X ⟶ Y)
    [IsOpenImmersion j] (G : Y.Modules) (x : X) :
    Stacks.Divisors.IsWeaklyAssociatedPoint ((Scheme.Modules.pullback j).obj G) x ↔
      Stacks.Divisors.IsWeaklyAssociatedPoint G (j.base x) :=
  (isWeaklyAssociatedPoint_iff_of_iso
      ((Scheme.Modules.restrictFunctorIsoPullback j).app G) x).symm.trans
    (isWeaklyAssociatedPoint_restrict_iff j G x)

/-- On an affine scheme, weak association of a point to a quasi-coherent module is weak
association of the corresponding prime to the module of global sections. -/
theorem isWeaklyAssociatedPoint_Spec_iff (R : Type u) [CommRing R]
    (G : (Spec (.of R)).Modules) [G.IsQuasicoherent] (x : Spec (.of R)) :
    Stacks.Divisors.IsWeaklyAssociatedPoint G x ↔
      IsWeaklyAssociatedPrime R ((moduleSpecΓFunctor (R := .of R)).obj G) x.asIdeal := by
  let hU := isAffineOpen_top (Spec (.of R))
  let q : Ideal Γ(Spec (.of R), ⊤) := (hU.primeIdealOf ⟨x, trivial⟩).asIdeal
  let e : Γ(Spec (.of R), ⊤) ≃+* R := (Scheme.ΓSpecIso (.of R)).commRingCatIsoToRingEquiv
  let f : Γ(G, ⊤) ≃+ ↑((moduleSpecΓFunctor (R := .of R)).obj G) := AddEquiv.refl _
  have hf : ∀ r m, f (r • m) = e r • f m := by
    intro r m
    have he : (Scheme.ΓSpecIso (.of R)).inv.hom (e r) = r := e.symm_apply_apply r
    show r • m = (Scheme.ΓSpecIso (.of R)).inv.hom (e r) • m
    rw [he]
  have hqeq : q = PrimeSpectrum.comap e.toRingHom x := by
    dsimp [q]
    apply congrArg PrimeSpectrum.asIdeal
    show hU.isoSpec.hom ⟨x, trivial⟩ = PrimeSpectrum.comap e.toRingHom x
    rw [IsAffineOpen.isoSpec_hom, Scheme.Opens.toSpecΓ_top, ← SpecMap_ΓSpecIso_hom]
    rfl
  have hmap : q.map e.toRingHom = x.asIdeal := by
    rw [hqeq]
    exact Ideal.map_comap_of_surjective e.toRingHom e.surjective x.asIdeal
  rw [← hmap, ← isWeaklyAssociatedPrime_iff_of_semilinearEquiv e f hf q]
  exact (isWeaklyAssociatedPrime_iff_isWeaklyAssociatedPoint G ⊤ hU x trivial).symm

end AlgebraicGeometry

end
