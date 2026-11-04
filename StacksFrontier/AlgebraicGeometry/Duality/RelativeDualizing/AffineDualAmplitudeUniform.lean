module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.CoherentDerivedDualityCoherence
public import StacksFrontier.Homology.HomComplex.Evaluation.Iterated

/-!
# The amplitude of duality against a dualizing complex on an affine scheme, uniformly

Let `R` be a Noetherian ring and `ω` a dualizing complex for `R`. For an object `A` of
`D_Coh(𝒪_{Spec R})` the two bounds

`A ∈ D^{≥q}  ⟹  R𝓗om_{𝒪_{Spec R}}(A, ω̃) ∈ D^{≤b-q}`,
`A ∈ D^{≤q}  ⟹  R𝓗om_{𝒪_{Spec R}}(A, ω̃) ∈ D^{≥a-q}`

hold with `[a, b]` an injective amplitude interval for `ω`, hence **with `a` and `b` depending
only on `ω`** and not on `A` or on `q`. This file states them in that shape: the interval is
chosen once, before the object.

`Stacks.Duality.exists_isLE_restrictSpec_derivedSheafHom` and
`Stacks.Duality.exists_isGE_restrictSpec_derivedSheafHom` prove the same two bounds for the
restriction to an affine open of a globally given object of `D(𝒪_X)`, and return the bound as an
unquantified `∃ m`. That form is what the two exchanges of [Stacks, Tag 0A89] consume: there the
bound is maximized over a finite affine cover and nothing depends on its value. A dévissage that
applies the bound repeatedly, at objects produced in the course of the argument and at varying
`q`, needs one interval good for all of them, which is what is recorded here.

## Main results

* `Stacks.Duality.exists_hasInjectiveAmplitude_forall_isLE_derivedSheafHomTilde`: the bound
  above, uniformly.
* `Stacks.Duality.exists_hasInjectiveAmplitude_forall_isGE_derivedSheafHomTilde`: the bound
  below, uniformly.

## The proof

An object of `D_Coh(𝒪_{Spec R})` is the derived sheafification of an object of `D_Coh(R)`
(`Stacks.Duality.exists_iso_tilde_of_isCoherent_homology`), and the bound on it is read off the
bound on that object: above by
`AlgebraicGeometry.AffineExt.isLE_affineDerivedSheafHom_of_isGE_of_hasInjectiveAmplitude`, the
`Ext`-presheaf bound of [Stacks, Tag 0A88] which is proved on the sheaf side directly because
the sheafification of an injective module need not be injective ([Stacks, Tag 0CRZ]); below by
the module-side bound `StacksDraft.DerivedHom.derivedHom_isGE_of_isLE_of_injectiveAmplitude`
carried across the comparison of [Stacks, Tag 0A88],
`AlgebraicGeometry.isIso_affineDerivedTildeHomComparison_of_finite_homology`. Those are the two
routes of `Stacks.Duality.exists_isLE_restrictSpec_derivedSheafHom` and
`Stacks.Duality.exists_isGE_restrictSpec_derivedSheafHom`, with the transport to an affine open
of an ambient scheme removed and the amplitude interval pulled in front of the object.

## References

* [Stacks Project, Tag 0A6I](https://stacks.math.columbia.edu/tag/0A6I)
* [Stacks Project, Tag 0A7B](https://stacks.math.columbia.edu/tag/0A7B)
* [Stacks Project, Tag 0A88](https://stacks.math.columbia.edu/tag/0A88)
* [Stacks Project, Tag 0A89](https://stacks.math.columbia.edu/tag/0A89)
* [Stacks Project, Tag 0CRZ](https://stacks.math.columbia.edu/tag/0CRZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

-- Standard model only: `Stacks.SheafOfModules.derivedSheafHom`,
--   `StacksDraft.DerivedHom.derivedHomAdjunction`.
attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.Duality

variable (R : CommRingCat.{u}) [IsNoetherianRing R]

/-- **Duality against a dualizing complex on an affine scheme carries `D^{≥q}_Coh` into
`D^{≤b-q}`, with `b` independent of the object and of `q`.** For `R` Noetherian and `ω` a
dualizing complex for `R`, pick an injective amplitude interval `[a, b]` for `ω`; then for every
`A` in `D(𝒪_{Spec R})` with coherent cohomology sheaves and no cohomology below `q`, the object
`R𝓗om_{𝒪_{Spec R}}(A, ω̃)` has no cohomology above `b - q`. -/
theorem exists_hasInjectiveAmplitude_forall_isLE_derivedSheafHomTilde
    {ω : DerivedCategory (ModuleCat.{u} R)} (hω : Dualizing.IsDualizingComplex ω) :
    ∃ b : ℤ, ∀ (A : DerivedCategory (Spec R).Modules) (q : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj A).IsCoherent) →
      A.IsGE q →
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj (op A)).obj
        ((tilde.functor R).mapDerivedCategory.obj ω)).IsLE (b - q) := by
  obtain ⟨a, b, hab⟩ := hω.finiteInjectiveDimension
  refine ⟨b, fun A q hAcoh hAq => ?_⟩
  obtain ⟨M, hM, ⟨eA⟩⟩ := exists_iso_tilde_of_isCoherent_homology R A hAcoh
  have hMq : M.IsGE q := (DerivedCategory.isGE_iff _ q).2 fun i hi =>
    (StandardModel.isZero_homology_mapDerivedCategory_obj_iff _ M i).1 <|
      IsZero.of_iso ((DerivedCategory.isGE_iff _ q).1 hAq i hi)
        ((DerivedCategory.homologyFunctor (Spec R).Modules i).mapIso eA)
  have :=
    AlgebraicGeometry.AffineExt.isLE_affineDerivedSheafHom_of_isGE_of_hasInjectiveAmplitude
      R M ω q a b hMq hab
  exact DerivedCategory.TStructure.t.isLE_of_iso
    (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).mapIso (Iso.op eA.symm)).app
      ((tilde.functor R).mapDerivedCategory.obj ω)) (b - q)

/-- **Duality against a dualizing complex on an affine scheme carries `D^{≤q}_Coh` into
`D^{≥a-q}`, with `a` independent of the object and of `q`.** For `R` Noetherian and `ω` a
dualizing complex for `R`, pick an injective amplitude interval `[a, b]` for `ω`; then for every
`A` in `D(𝒪_{Spec R})` with coherent cohomology sheaves and no cohomology above `q`, the object
`R𝓗om_{𝒪_{Spec R}}(A, ω̃)` has no cohomology below `a - q`. -/
theorem exists_hasInjectiveAmplitude_forall_isGE_derivedSheafHomTilde
    {ω : DerivedCategory (ModuleCat.{u} R)} (hω : Dualizing.IsDualizingComplex ω) :
    ∃ a : ℤ, ∀ (A : DerivedCategory (Spec R).Modules) (q : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (Spec R).Modules i).obj A).IsCoherent) →
      A.IsLE q →
      (((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).obj (op A)).obj
        ((tilde.functor R).mapDerivedCategory.obj ω)).IsGE (a - q) := by
  obtain ⟨a, b, hab⟩ := hω.finiteInjectiveDimension
  refine ⟨a, fun A q hAcoh hAq => ?_⟩
  obtain ⟨M, hM, ⟨eA⟩⟩ := exists_iso_tilde_of_isCoherent_homology R A hAcoh
  have hMq : M.IsLE q := (DerivedCategory.isLE_iff _ q).2 fun i hi =>
    (StandardModel.isZero_homology_mapDerivedCategory_obj_iff _ M i).1 <|
      IsZero.of_iso (DerivedCategory.isZero_of_isLE _ q i hi)
        ((DerivedCategory.homologyFunctor (Spec R).Modules i).mapIso eA)
  have hRHom : ((StacksDraft.DerivedHom.derivedHomAdjunction
      (R := (R : Type u))).hom.obj (op M, ω)).IsGE (a - q) :=
    StacksDraft.DerivedHom.derivedHom_isGE_of_isLE_of_injectiveAmplitude _ M ω q a b hMq hab
  have hiso : IsIso (affineDerivedTildeHomComparison R M ω) :=
    isIso_affineDerivedTildeHomComparison_of_finite_homology R M ω hM
      hω.finiteInjectiveDimension
  have := CategoryTheory.Functor.isGE_obj_mapDerivedCategory (tilde.functor R) _ (a - q) hRHom
  exact DerivedCategory.TStructure.t.isGE_of_iso
    (asIso (affineDerivedTildeHomComparison R M ω) ≪≫
      ((Stacks.SheafOfModules.derivedSheafHom (Spec R).sheaf).mapIso (Iso.op eA.symm)).app
        ((tilde.functor R).mapDerivedCategory.obj ω)) (a - q)

end Stacks.Duality

end
