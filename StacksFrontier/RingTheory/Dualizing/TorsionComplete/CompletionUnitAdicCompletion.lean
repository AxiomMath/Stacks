module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.RingTheory.AdicCompletion.Functoriality
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteFlatTensor
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.Equivalence

/-!
# The derived completion of a module whose derived completion is its adic completion

Let `I` be a finitely generated ideal of a commutative ring `A` and let `N` be an `A`-module.
Several statements of the library (Stacks 0EEU among them) identify the derived `I`-adic
completion `N^∧` of `N`, regarded as a complex in degree `0`, with the classical `I`-adic
completion `AdicCompletion I N` — but only up to an *unspecified* isomorphism of objects of
`D(A)`. This file shows that any such abstract identification is automatically the canonical
one: the canonical map `N ⟶ AdicCompletion I N` is then a derived completion, in the sense that
derived completion inverts it, and `AdicCompletion I N` is derived complete.

The argument uses only the universal properties on both sides. Morphisms out of the derived
completion of `N` into a derived complete object are determined by their composite with the unit
of the reflection, and morphisms out of the classical completion into an `I`-adically complete
module are determined by their composite with `AdicCompletion.of`. Comparing the two through the
given isomorphism produces a two-sided inverse of the comparison map, the degree-zero single
functor being fully faithful.

## Main results

* `Dualizing.bijective_comp_derivedCompletionUnit` — precomposition with the unit of derived
  completion is bijective on morphisms into a derived complete object.
* `Dualizing.isIso_derivedCompletion_map_adicCompletionOf` — if the derived completion of `N` is
  isomorphic, in any way, to `AdicCompletion I N` placed in degree `0`, then derived completion
  inverts the canonical map `N ⟶ AdicCompletion I N`, and `AdicCompletion I N` is derived
  complete.

## References

* [Stacks Project, Tag 0EEU](https://stacks.math.columbia.edu/tag/0EEU)
* [Stacks Project, Tag 0G3E](https://stacks.math.columbia.edu/tag/0G3E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AdicCompletionFlatTensor

attribute [local instance] HasDerivedCategory.standard
  Dualizing.hasProductsOfShape_nat_derivedCategory

universe u

namespace Dualizing

variable {A : Type u} [CommRing A] (I : Ideal A) (hI : I.FG)

/-- **Morphisms out of a derived completion.** Precomposition with the unit `X ⟶ X^∧` of derived
`I`-adic completion is a bijection from morphisms `X^∧ ⟶ Z` to morphisms `X ⟶ Z`, for every
derived `I`-complete object `Z`. -/
theorem bijective_comp_derivedCompletionUnit (X Z : DerivedCategory (ModuleCat.{u} A))
    (hZ : IsDerivedComplete I Z) :
    Function.Bijective (fun g : ((derivedCompletionReflection A I hI).1 ⋙
        (derivedCompleteProperty A I).ι).obj X ⟶ Z =>
      (derivedCompletionReflection A I hI).2.unit.app X ≫ g) := by
  let P := derivedCompleteProperty.{u, u} A I
  let Z' : P.FullSubcategory := ⟨Z, hZ⟩
  let adj := (derivedCompletionReflection A I hI).2
  refine ⟨fun g₁ g₂ hg => ?_, fun f => ?_⟩
  · have h₁ := (adj.homEquiv X Z').injective (a₁ := P.fullyFaithfulι.preimage (Y := Z') g₁)
      (a₂ := P.fullyFaithfulι.preimage (Y := Z') g₂) (by
        rwa [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, P.fullyFaithfulι.map_preimage,
          P.fullyFaithfulι.map_preimage])
    have h₂ := congrArg P.ι.map h₁
    rwa [P.fullyFaithfulι.map_preimage, P.fullyFaithfulι.map_preimage] at h₂
  · refine ⟨P.ι.map ((adj.homEquiv X Z').symm f), ?_⟩
    have h := (adj.homEquiv X Z').apply_symm_apply f
    rwa [Adjunction.homEquiv_unit] at h

include hI in
/-- Two linear maps out of an adic completion into an `I`-adically separated module agree as soon
as they agree on the image of `AdicCompletion.of`, the ideal being finitely generated. -/
theorem AdicCompletion.linearMap_ext_of {N P : Type u} [AddCommGroup N] [Module A N]
    [AddCommGroup P] [Module A P] [IsHausdorff I P]
    {f g : AdicCompletion I N →ₗ[A] P}
    (h : f ∘ₗ AdicCompletion.of I N = g ∘ₗ AdicCompletion.of I N) : f = g := by
  refine LinearMap.ext fun x => sub_eq_zero.mp ?_
  refine IsHausdorff.haus (I := I) inferInstance (f x - g x) fun n => ?_
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (x.val n)
  have hx : x - AdicCompletion.of I N y ∈ (I ^ n • ⊤ : Submodule A (AdicCompletion I N)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval (I := I) (M := N) hI, LinearMap.mem_ker,
      map_sub, AdicCompletion.eval_of, AdicCompletion.eval_apply, Submodule.mkQ_apply, hy,
      sub_self]
  have hfg : f (AdicCompletion.of I N y) = g (AdicCompletion.of I N y) :=
    congrArg (fun φ : N →ₗ[A] P => φ y) h
  rw [SModEq.zero, show f x - g x = (f (x - AdicCompletion.of I N y)) -
    (g (x - AdicCompletion.of I N y)) by simp [hfg]]
  exact Submodule.sub_mem _ (Submodule.smul_top_le_comap_smul_top (I ^ n) f hx)
    (Submodule.smul_top_le_comap_smul_top (I ^ n) g hx)

/-- The unit of derived completion at a derived complete object is a split monomorphism: some
`ψ : Z^∧ ⟶ Z` retracts it, and that retraction is an inverse. -/
theorem isIso_derivedCompletionUnit_of_isDerivedComplete (Z : DerivedCategory (ModuleCat.{u} A))
    (hZ : IsDerivedComplete I Z) :
    IsIso ((derivedCompletionReflection A I hI).2.unit.app Z) := by
  let η := (derivedCompletionReflection.{u, u} A I hI).2.unit
  obtain ⟨ψ, hψ⟩ := (bijective_comp_derivedCompletionUnit I hI Z Z hZ).2 (𝟙 Z)
  refine ⟨ψ, hψ, ?_⟩
  refine (bijective_comp_derivedCompletionUnit I hI Z _
    ((derivedCompletionReflection A I hI).1.obj Z).property).1 ?_
  dsimp only at hψ ⊢
  rw [reassoc_of% hψ, Category.comp_id]

include hI in
/-- An endomorphism of `AdicCompletion I N`, placed in degree `0`, which fixes the canonical map
`N ⟶ AdicCompletion I N` is the identity. -/
theorem singleFunctor_adicCompletion_endo_eq_id (N : Type u) [AddCommGroup N] [Module A N]
    {t : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I N)) ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I N))}
    (ht : (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.ofHom (AdicCompletion.of I N)) ≫ t =
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.ofHom (AdicCompletion.of I N))) :
    t = 𝟙 _ := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let tbar : AdicCompletion I N →ₗ[A] AdicCompletion I N := (S.preimage t).hom
  have htbar : tbar ∘ₗ AdicCompletion.of I N = AdicCompletion.of I N := by
    have h1 : S.map (ModuleCat.ofHom (AdicCompletion.of I N) ≫ S.preimage t) =
        S.map (ModuleCat.ofHom (AdicCompletion.of I N)) := by
      rwa [S.map_comp, S.map_preimage]
    exact congrArg ModuleCat.Hom.hom (S.map_injective h1)
  have htid : tbar = LinearMap.id :=
    AdicCompletion.linearMap_ext_of I hI (htbar.trans (LinearMap.id_comp _).symm)
  rw [← S.map_preimage t, ← ModuleCat.ofHom_hom (S.preimage t)]
  change S.map (ModuleCat.ofHom tbar) = _
  rw [htid, ModuleCat.ofHom_id, S.map_id]

/-- Let `c : X ⟶ Y` be a morphism into a derived complete object which factors through the unit
of derived completion as `η_X ≫ ψ` with `ψ` an isomorphism. Then derived completion inverts `c`. -/
theorem isIso_derivedCompletion_map_of_isIso_lift {X Y : DerivedCategory (ModuleCat.{u} A)}
    (hY : IsDerivedComplete I Y) (c : X ⟶ Y)
    {ψ : ((derivedCompletionReflection A I hI).1 ⋙ (derivedCompleteProperty A I).ι).obj X ⟶ Y}
    (hψ : (derivedCompletionReflection A I hI).2.unit.app X ≫ ψ = c) [IsIso ψ] :
    IsIso ((derivedCompletionReflection A I hI).1.map c) := by
  let P := derivedCompleteProperty.{u, u} A I
  let D := (derivedCompletionReflection A I hI).1
  let η := (derivedCompletionReflection.{u, u} A I hI).2.unit
  have hηY := isIso_derivedCompletionUnit_of_isDerivedComplete I hI Y hY
  have hnat : η.app X ≫ P.ι.map (D.map c) = c ≫ η.app Y := (η.naturality c).symm
  have hfac : ψ = P.ι.map (D.map c) ≫ inv (η.app Y) := by
    refine (bijective_comp_derivedCompletionUnit I hI X Y hY).1 ?_
    dsimp only
    rw [hψ, reassoc_of% hnat, IsIso.hom_inv_id, Category.comp_id]
  have : IsIso (P.ι.map (D.map c)) := by
    rw [show P.ι.map (D.map c) = ψ ≫ η.app Y by
      rw [hfac, Category.assoc, IsIso.inv_hom_id, Category.comp_id]]
    infer_instance
  let := P.fullyFaithfulι
  exact isIso_of_reflects_iso _ P.ι

/-- **An abstract identification of the derived completion of a module with its adic completion
is the canonical one.** Let `N` be an `A`-module whose derived `I`-adic completion is isomorphic,
by any isomorphism whatever, to `AdicCompletion I N` placed in degree `0`. Then derived
completion inverts the canonical map `N ⟶ AdicCompletion I N`.

Write `η` for the unit of derived completion and `c` for the canonical map. Since
`AdicCompletion I N` is derived complete, `c` factors as `η ≫ ψ`; the given isomorphism `e`
composed with `η` is a map of modules `h : N ⟶ AdicCompletion I N`, which extends over `c` to an
endomorphism `h̄` of the complete module `AdicCompletion I N`, and uniqueness of factorizations
through `η` gives `ψ ≫ h̄ = e`. So `ψ` has the right inverse `h̄ ≫ e⁻¹`; the composite the other
way round restricts along `c` to `c` itself, hence is the identity by uniqueness of extensions
along `c`. -/
theorem isIso_derivedCompletion_map_adicCompletionOf (N : Type u) [AddCommGroup N] [Module A N]
    (e' : (derivedCompleteProperty A I).ι.obj ((derivedCompletion A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A N))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I N))) :
    IsIso ((derivedCompletion A I hI).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.ofHom (AdicCompletion.of I N)))) := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  let P := derivedCompleteProperty.{u, u} A I
  let D := (derivedCompletionReflection A I hI).1
  let X := S.obj (ModuleCat.of A N)
  let Y := S.obj (ModuleCat.of A (AdicCompletion I N))
  let e : (D ⋙ P.ι).obj X ≅ Y := e'
  change IsIso (D.map (S.map (ModuleCat.ofHom (AdicCompletion.of I N))))
  let η := (derivedCompletionReflection.{u, u} A I hI).2.unit
  let c : X ⟶ Y := S.map (ModuleCat.ofHom (AdicCompletion.of I N))
  have : IsAdicComplete I (AdicCompletion I N) := AdicCompletion.isAdicComplete (I := I) (M := N) hI
  have hY : IsDerivedComplete I Y :=
    (isDerivedCompleteModule_of_isAdicComplete_and_adicCompletion_surjective A I
      (AdicCompletion I N)).1 this
  have B := bijective_comp_derivedCompletionUnit I hI X Y hY
  obtain ⟨ψ, hψ⟩ := B.2 c
  dsimp only at hψ
  -- the module map underlying `η ≫ e`, and its extension over `c`
  let h : N →ₗ[A] AdicCompletion I N := (S.preimage (η.app X ≫ e.hom)).hom
  have hh : S.map (ModuleCat.ofHom h) = η.app X ≫ e.hom := by
    change S.map (ModuleCat.ofHom (S.preimage (η.app X ≫ e.hom)).hom) = _
    rw [ModuleCat.ofHom_hom, S.map_preimage]
  let hbar : AdicCompletion I N →ₗ[A] AdicCompletion I N :=
    (AdicCompletion.ofLinearEquiv I (AdicCompletion I N)).symm.toLinearMap ∘ₗ
      (AdicCompletion.map I h).restrictScalars A
  have hbar_of : hbar ∘ₗ AdicCompletion.of I N = h := by
    refine LinearMap.ext fun x => ?_
    simp [hbar, AdicCompletion.map_of]
  let s : Y ⟶ Y := S.map (ModuleCat.ofHom hbar)
  have hs : ψ ≫ s = e.hom := by
    refine B.1 ?_
    dsimp only
    rw [reassoc_of% hψ, ← hh]
    change S.map _ ≫ S.map _ = _
    rw [← S.map_comp, ← ModuleCat.ofHom_comp, hbar_of]
  -- the composite the other way round is the identity
  let t : Y ⟶ Y := s ≫ e.inv ≫ ψ
  have ht : ψ ≫ t = ψ := by
    change ψ ≫ s ≫ e.inv ≫ ψ = ψ
    rw [← Category.assoc, hs, e.hom_inv_id_assoc]
  have hct : c ≫ t = c := by
    rw [← hψ, Category.assoc, ht]
  have ht1 : t = 𝟙 Y := singleFunctor_adicCompletion_endo_eq_id I hI N hct
  have hψiso : IsIso ψ :=
    ⟨s ≫ e.inv, by rw [← Category.assoc, hs, e.hom_inv_id], by rwa [Category.assoc]⟩
  exact isIso_derivedCompletion_map_of_isIso_lift I hI hY c hψ

/-- **Stacks 0EEU for a localization, as an abstract isomorphism for this reflection.** Over a
Noetherian ring, the derived `I`-adic completion of a localization `M_f` of a finite module at one
element is isomorphic to its adic completion, placed in degree `0`. The library's form of
Stacks 0EEU is stated for a reflector which is a derived limit of the ideal-power tensor tower;
the reflector of Stacks 0EET is one, and it agrees with `Dualizing.derivedCompletion` by
uniqueness of left adjoints. -/
theorem nonempty_derivedCompletion_iso_adicCompletion_of_isLocalizedModule [IsNoetherianRing A]
    (M Mf : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup Mf] [Module A Mf] (f : A) (φ : M →ₗ[A] Mf)
    [IsLocalizedModule (Submonoid.powers f) φ] :
    Nonempty ((derivedCompleteProperty A I).ι.obj ((derivedCompletion A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A Mf))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I Mf))) := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  obtain ⟨L, ⟨adjL⟩, hL, -, -⟩ := AdicCompletionTor.derivedCompletion_homology_shortExact A I T
  obtain ⟨e⟩ := (derivedCompletion_iso_adicCompletion_of_finite_tensor_flat_and_localization
      A I T L ⟨adjL⟩ hL).2 M Mf f φ
  exact ⟨(derivedCompleteProperty A I).ι.mapIso
    ((adjL.leftAdjointUniq (derivedCompletionReflection A I hI).2).app _).symm ≪≫ e⟩

/-- **The derived completion of a localization of a finite module is its adic completion,
canonically.** Over a Noetherian ring, derived `I`-adic completion inverts the canonical map
`M_f ⟶ (M_f)^∧` from a localization of a finite module at one element to its adic completion. -/
theorem isIso_derivedCompletion_map_adicCompletionOf_of_isLocalizedModule [IsNoetherianRing A]
    (M Mf : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup Mf] [Module A Mf] (f : A) (φ : M →ₗ[A] Mf)
    [IsLocalizedModule (Submonoid.powers f) φ] :
    IsIso ((derivedCompletion A I hI).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map
        (ModuleCat.ofHom (AdicCompletion.of I Mf)))) :=
  isIso_derivedCompletion_map_adicCompletionOf I hI Mf
    (nonempty_derivedCompletion_iso_adicCompletion_of_isLocalizedModule I hI M Mf f φ).some

/-- **Stacks 0EEU for a tensor product with a flat module, as an abstract isomorphism for this
reflection.** Over a Noetherian ring, the derived `I`-adic completion of `M ⊗_A F`, for `M` finite
and `F` flat, is isomorphic to its adic completion placed in degree `0`. -/
theorem nonempty_derivedCompletion_iso_adicCompletion_of_tensor_flat [IsNoetherianRing A]
    (M F : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup F] [Module A F] [Module.Flat A F] :
    Nonempty ((derivedCompleteProperty A I).ι.obj ((derivedCompletion A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (TensorProduct A M F)))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I (TensorProduct A M F)))) := by
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A
  obtain ⟨L, ⟨adjL⟩, hL, -, -⟩ := AdicCompletionTor.derivedCompletion_homology_shortExact A I T
  obtain ⟨e⟩ := (derivedCompletion_iso_adicCompletion_of_finite_tensor_flat_and_localization
      A I T L ⟨adjL⟩ hL).1 M F
  exact ⟨(derivedCompleteProperty A I).ι.mapIso
    ((adjL.leftAdjointUniq (derivedCompletionReflection A I hI).2).app _).symm ≪≫ e⟩

/-- An abstract identification of the derived completion with the adic completion transports
along a linear equivalence of modules. -/
theorem nonempty_derivedCompletion_iso_adicCompletion_of_linearEquiv
    {N N' : Type u} [AddCommGroup N] [Module A N] [AddCommGroup N'] [Module A N']
    (l : N ≃ₗ[A] N')
    (h : Nonempty ((derivedCompleteProperty A I).ι.obj ((derivedCompletion A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A N'))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I N')))) :
    Nonempty ((derivedCompleteProperty A I).ι.obj ((derivedCompletion A I hI).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A N))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
        (ModuleCat.of A (AdicCompletion I N))) := by
  obtain ⟨e⟩ := h
  let S := DerivedCategory.singleFunctor (ModuleCat.{u} A) 0
  exact ⟨(derivedCompletion A I hI ⋙ (derivedCompleteProperty A I).ι).mapIso
      (S.mapIso l.toModuleIso) ≪≫ e ≪≫
    S.mapIso ((AdicCompletion.congr I l).restrictScalars A).toModuleIso.symm⟩

end Dualizing

end
