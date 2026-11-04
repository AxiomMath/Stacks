module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.InjectiveHull.Basic
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionHom
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.NormalizedDualizingComplex
public import StacksFrontier.RingTheory.Dualizing.NormalizedUniqueness
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.Complete
public import StacksFrontier.RingTheory.Dualizing.TorsionComplete.DerivedHomCompletionTorsion

/-!
# The local duality theorem

Let `(A, 𝔪, κ)` be a Noetherian local ring, let `ω` be a normalized dualizing complex, let `E`
be an injective hull of `κ`, and let `Z = V(𝔪) ⊆ Spec(A)`. Writing `(-)^∧` for derived
`𝔪`-adic completion, local duality is the isomorphism

`RHom_A(K, ω)^∧ ≅ RHom_A(RΓ_Z(K), E[0])`

in `D(A)`, valid for every object `K` of `D(A)`.

For any commutative ring and any finitely generated ideal, completing derived Hom turns both
arguments into local cohomology: `RHom_A(K, L)^∧ ≅ RHom_A(RΓ_Z(K), RΓ_Z(L))`.

## Main results

* `Dualizing.LocalDuality.nonempty_localCohomology_iso_localCohomology`: `RΓ_Z(ω) ≅ RΓ_Z(ω')`
  for any two normalized dualizing complexes `ω` and `ω'`.
* `Dualizing.LocalDuality.injectiveHullUnitsMulEquivUnitsAdicCompletion`: the automorphism group
  of an injective hull of the residue field is the group of units of the `𝔪`-adic completion of
  `A`.
* `Dualizing.LocalDuality.nonempty_derivedCompletion_derivedHom_iso_derivedHom_localCohomology`:
  the completed derived Hom is derived Hom between local cohomologies.
* `Dualizing.LocalDuality.nonempty_derivedCompletion_derivedHom_iso_derivedHom_injectiveHull`:
  the local duality theorem.
* `Dualizing.LocalDuality.nonempty_localDualityNatIso`: the local duality theorem as an
  isomorphism of functors of `K`.

## References

* [Stacks Project, Tag 0A84](https://stacks.math.columbia.edu/tag/0A84)
* [Stacks Project, Tag 0A83](https://stacks.math.columbia.edu/tag/0A83)
* [Stacks Project, Tag 0A82](https://stacks.math.columbia.edu/tag/0A82)
* [Stacks Project, Tag 0A6E](https://stacks.math.columbia.edu/tag/0A6E)
* [Stacks Project, Tag 0A6X](https://stacks.math.columbia.edu/tag/0A6X)
* [Stacks Project, Tag 0A6Y](https://stacks.math.columbia.edu/tag/0A6Y)
* [Stacks Project, Tag 08Y4](https://stacks.math.columbia.edu/tag/08Y4)
* [Stacks Project, Tag 08Z6](https://stacks.math.columbia.edu/tag/08Z6)
* [Stacks Project, Tag 0A7F](https://stacks.math.columbia.edu/tag/0A7F)
* [Stacks Project, Tag 0A7M](https://stacks.math.columbia.edu/tag/0A7M)
* [Stacks Project, Tag 0FNT](https://stacks.math.columbia.edu/tag/0FNT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Dualizing.LocalDuality

open StacksDraft.DerivedHom

attribute [local instance] Dualizing.hasProductsOfShape_nat_derivedCategory

/-- Let `(A, 𝔪, κ)` be a Noetherian local ring and let `Z = V(𝔪)`. If `ω` and `ω'` are normalized
dualizing complexes for `A`, then `RΓ_Z(ω) ≅ RΓ_Z(ω')` in `D(A)`. -/
@[stacks 0A83 "the realization is independent of the normalized dualizing complex"]
public theorem nonempty_localCohomology_iso_localCohomology
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (ω ω' : DerivedCategory (ModuleCat.{max v u} A))
    (hω : IsNormalizedDualizingComplex.{u, v} ω)
    (hω' : IsNormalizedDualizingComplex.{u, v} ω') :
    Nonempty
      ((derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A)
              (IsNoetherian.noetherian _)).ι.obj
            ((localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
              (IsNoetherian.noetherian _)).obj ω) ≅
          (derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A)
              (IsNoetherian.noetherian _)).ι.obj
            ((localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
              (IsNoetherian.noetherian _)).obj ω')) := by
  obtain ⟨concentrated⟩ := nonempty_localCohomology_iso_single_homology_zero.{u, v} A ω hω
  obtain ⟨concentrated'⟩ := nonempty_localCohomology_iso_single_homology_zero.{u, v} A ω' hω'
  obtain ⟨i, hi, hhull⟩ := exists_isInjectiveHull_homology_zero_localCohomology.{u, v} A ω hω
  obtain ⟨j, hj, hhull'⟩ := exists_isInjectiveHull_homology_zero_localCohomology.{u, v} A ω' hω'
  let := hi
  let := hj
  obtain ⟨hullIso, -⟩ := Module.exists_iso_of_isInjectiveHull i j hhull hhull'
  exact ⟨concentrated ≪≫
    (DerivedCategory.singleFunctor (ModuleCat.{max v u} A) 0).mapIso hullIso ≪≫
    concentrated'.symm⟩

/-- Let `(A, 𝔪, κ)` be a Noetherian local ring and let `i : κ ⟶ E` present `E` as an injective
hull of the residue field. The units of `End_A(E)` are the units of the `𝔪`-adic completion
`A^∧` of `A`. -/
@[stacks 0A83 "the automorphism group of an injective hull of the residue field is the units of \
the completion"]
public def injectiveHullUnitsMulEquivUnitsAdicCompletion
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (E : Type u) [AddCommGroup E] [Module A E]
    (i : ModuleCat.of A (A ⧸ IsLocalRing.maximalIdeal A) ⟶ ModuleCat.of A E)
    [Mono i] (hi : Module.IsInjectiveHull i) :
    (Module.End A E)ˣ ≃* (AdicCompletion (IsLocalRing.maximalIdeal A) A)ˣ :=
  Units.mapEquiv (Dualizing.endAlgEquivAdicCompletion A E i hi).toRingEquiv.toMulEquiv

add_to_stacks 0A83 "the opening sentence, that `RΓ_Z(ω)` is an injective hull of the residue \
field: the hull half, read from Stacks 0A82"
  exists_isInjectiveHull_homology_zero_localCohomology

add_to_stacks 0A83 "the opening sentence, that `RΓ_Z(ω)` is an injective hull of the residue \
field placed in degree zero: the concentration half, read from Stacks 0A82"
  nonempty_localCohomology_iso_single_homology_zero

add_to_stacks 0A83 "an injective hull of the residue field is unique up to isomorphism; proved \
for an arbitrary object of an arbitrary abelian category, which is Stacks 08Y4"
  Module.exists_iso_of_isInjectiveHull

/-- For a finite family `f` generating an ideal `I` of a commutative ring `A`, with `Z = V(I)`,
there is an isomorphism `RHom_A(K, L)^∧ ≅ RHom_A(RΓ_Z(K), RΓ_Z(L))` in `D(A)`. -/
public theorem nonempty_derivedCompletion_derivedHom_iso_derivedHom_localCohomology
    (A : Type u) [CommRing A] {r : ℕ} (f : Fin r → A) (I : Ideal A) (hI : I.FG)
    (hf : Ideal.span (Set.range f) = I) (K L : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty
      ((DerivedCompletion.derivedCompletionFunctor A f).obj
          ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, L)) ≅
        (derivedHomAdjunction (R := A)).hom.obj
          (Opposite.op ((derivedPowerTorsionProperty A I hI).ι.obj
              ((localCohomologyFunctor A I hI).obj K)),
            (derivedPowerTorsionProperty A I hI).ι.obj
              ((localCohomologyFunctor A I hI).obj L))) := by
  obtain ⟨-, -, -, ⟨completionInside⟩, completionAbsorbed, -⟩ :=
    DerivedHomCechCompletion.derivedHom_cechCompletion A f
  exact ⟨completionInside.app (Opposite.op K, L) ≪≫
    (completionAbsorbed.app (Opposite.op K, L)).symm ≪≫
    derivedHomCompletionTorsionIso A I hI f hf K L⟩

/-- The local duality theorem. Let `(A, 𝔪, κ)` be a Noetherian local ring, let `ω` be a
normalized dualizing complex, let `i : κ ⟶ E` be an injective hull of the residue field, and let
`Z = V(𝔪)`. Then derived `𝔪`-adic completion of `RHom_A(K, ω)` is `RHom_A(RΓ_Z(K), E[0])`, for
every `K` in `D(A)`. -/
@[stacks 0A84]
public theorem nonempty_derivedCompletion_derivedHom_iso_derivedHom_injectiveHull
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω)
    {E : ModuleCat.{u} A}
    (i : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (K : DerivedCategory (ModuleCat.{u} A)) :
    Nonempty
      ((DerivedCompletion.derivedCompletionFunctor A f).obj
          ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, ω)) ≅
        (derivedHomAdjunction (R := A)).hom.obj
          (Opposite.op ((derivedPowerTorsionProperty A (IsLocalRing.maximalIdeal A)
              (IsNoetherian.noetherian _)).ι.obj
            ((localCohomologyFunctor A (IsLocalRing.maximalIdeal A)
              (IsNoetherian.noetherian _)).obj K)),
            (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)) := by
  obtain ⟨concentrated⟩ := nonempty_localCohomology_iso_single_homology_zero.{u, u} A ω hω
  obtain ⟨j, hj, hjhull⟩ :=
    exists_isInjectiveHull_homology_zero_localCohomology.{u, u} A ω hω
  let := hj
  obtain ⟨hullIso, -⟩ := Module.exists_iso_of_isInjectiveHull j i hjhull hi
  obtain ⟨duality⟩ :=
    nonempty_derivedCompletion_derivedHom_iso_derivedHom_localCohomology A f
      (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _) hf K ω
  exact ⟨duality ≪≫ (derivedHomAdjunction (R := A)).hom.mapIso ((Iso.refl _).prod
    (concentrated ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso hullIso))⟩

/-- The local duality theorem, natural in `K`. Let `(A, 𝔪, κ)` be a Noetherian local ring, let
`ω` be a normalized dualizing complex, let `i : κ ⟶ E` be an injective hull of the residue
field, and let `Z = V(𝔪)`. Then derived `𝔪`-adic completion of `RHom_A(-, ω)` is
`RHom_A(RΓ_Z(-), E[0])`, as an isomorphism of contravariant functors on `D(A)`. -/
@[stacks 0A84 "natural in K"]
public theorem nonempty_localDualityNatIso
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {r : ℕ} (f : Fin r → A) (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω)
    {E : ModuleCat.{u} A}
    (i : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono i] (hi : Module.IsInjectiveHull i) :
    Nonempty (Dualizing.derivedHomInto A ω ⋙ DerivedCompletion.derivedCompletionFunctor A f ≅
      (Stacks.LocalCohomology.CechFormula.localCohomologyEndofunctor A
          (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _)).op ⋙
        Dualizing.derivedHomInto A
          ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)) := by
  obtain ⟨concentrated⟩ := nonempty_localCohomology_iso_single_homology_zero.{u, u} A ω hω
  obtain ⟨j, hj, hjhull⟩ :=
    exists_isInjectiveHull_homology_zero_localCohomology.{u, u} A ω hω
  let := hj
  obtain ⟨hullIso, -⟩ := Module.exists_iso_of_isInjectiveHull j i hjhull hi
  exact ⟨Dualizing.derivedCompletionDerivedHomTorsionNatIso A (IsLocalRing.maximalIdeal A)
      (IsNoetherian.noetherian _) f hf ω ≪≫
    Functor.isoWhiskerLeft _ (Dualizing.derivedHomIntoMapIso A
      (concentrated ≪≫
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso hullIso))⟩

end Dualizing.LocalDuality

end
