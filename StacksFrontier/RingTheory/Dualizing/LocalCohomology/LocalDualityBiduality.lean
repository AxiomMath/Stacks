module

public import StacksFrontier.RingTheory.Dualizing.BidualitySameUniverse
public import StacksFrontier.RingTheory.Dualizing.LocalCohomology.LocalDuality
public import StacksFrontier.RingTheory.Dualizing.DerivedHomFiniteCohomology
public import StacksFrontier.RingTheory.Dualizing.RelativeUniquenessInternalHomCompare
public import StacksFrontier.RingTheory.LocalCohomology.CechFormula.DerivedHom

/-!
# Local duality without completion

Let `I = (f₁, …, f_r)` be a finitely generated ideal of a Noetherian ring `A`, let `Z = V(I)` and
let `ω` be a dualizing complex. For `K` with finite cohomology modules and bounded below there is
an isomorphism

`RΓ_Z(K) ≅ RHom_A(RHom_A(K, ω), RΓ_Z(ω))`

in `D(A)`, natural in `K`.

This is local duality with no completion anywhere, and it is two statements composed. Biduality
(Stacks 0A7C) identifies `K` with `RHom_A(RHom_A(K, ω), ω)` naturally, and
`Stacks.LocalCohomology.CechFormula.localCohomologyDerivedHomMor` moves `RΓ_Z` from outside the
derived Hom to its second argument, which it may because `RHom_A(K, ω)` is pseudo-coherent
(Stacks 0A7C again) and `ω` is bounded. Both inputs are natural in `K`, so the composite is.

Compare Stacks 0A84,
`Dualizing.LocalDuality.nonempty_derivedCompletion_derivedHom_iso_derivedHom_injectiveHull`:
there derived completion appears on the left and `RΓ_Z` only inside the derived Hom, and the
price of the completion is that passing to cohomology modules needs Stacks 0A06. Here there is
no completion to undo.

## Main definitions

* `Dualizing.LocalDuality.localCohomologyBidualityMor` — the canonical morphism
  `RΓ_Z(K) ⟶ RHom_A(RHom_A(K, ω), RΓ_Z(ω))`.

## Main results

* `Dualizing.isPseudoCoherent_derivedHom_of_isDualizingComplex` — `RHom_A(K, ω)` is
  pseudo-coherent for `K` bounded below with finite cohomology, in the same-universe adjunction.
* `Dualizing.LocalDuality.localCohomologyBidualityMor_naturality` — the morphism is natural
  in `K`.
* `Dualizing.LocalDuality.isIso_localCohomologyBidualityMor` — **it is invertible**.
* `Dualizing.LocalDuality.nonempty_localCohomology_iso_derivedHom_derivedHom` — the resulting
  isomorphism.
* `Dualizing.LocalDuality.nonempty_localCohomology_iso_derivedHom_injectiveHull` — over a
  Noetherian local ring with a normalized dualizing complex, the same isomorphism with `RΓ_Z(ω)`
  replaced by the injective hull of the residue field in degree zero.

## References

* [Stacks Project, Tag 0A7C](https://stacks.math.columbia.edu/tag/0A7C)
* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StacksDraft.DerivedHom
open Stacks.LocalCohomology.CechFormula

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Dualizing

variable {A : Type u} [CommRing A] [IsNoetherianRing A]

/-- **Derived Hom into a dualizing complex is pseudo-coherent**, for the same-universe
tensor--Hom adjunction. Boundedness above is
`StacksDraft.DerivedHom.derivedHom_isLE_of_isGE_of_injectiveAmplitude`, finiteness of the
cohomology modules is `Dualizing.derivedHom_finiteCohomology` read through the comparison
`Dualizing.modelHomIsoDerivedHomAdjunctionOverRing` of the two spellings of internal derived
Hom, and pseudo-coherence over a Noetherian ring is the conjunction of the two by
`StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology`. -/
theorem isPseudoCoherent_derivedHom_of_isDualizingComplex
    (ω K : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω) (n : ℤ)
    (hKge : K.IsGE n)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, ω)) := by
  obtain ⟨a, b, hamp⟩ := hω.finiteInjectiveDimension
  have hLE : ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, ω)).IsLE (b - n) :=
    derivedHom_isLE_of_isGE_of_injectiveAmplitude (derivedHomAdjunction (R := A)) K ω n a b
      hKge hamp
  have hfin := derivedHom_finiteCohomology.{u, u} K ω hK hω.finiteCohomology
    ⟨a, b, hamp⟩
  refine ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_boundedAbove_finite_homology
    ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, ω)) 0 PUnit).2.1).mpr
      ⟨⟨b - n, fun i hi => DerivedCategory.isZero_of_isLE _ (b - n) i hi⟩, fun i => ?_⟩
  have := hfin i
  exact Module.Finite.equiv
    (((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).mapIso
      (modelHomIsoDerivedHomAdjunctionOverRing A K ω)).toLinearEquiv).symm

namespace LocalDuality

section General

variable {r : ℕ} (I : Ideal A) (hI : I.FG) (f : Fin r → A)
  (hf : Ideal.span (Set.range f) = I)

/-- **Local duality without completion.** The canonical morphism
`RΓ_Z(K) ⟶ RHom_A(RHom_A(K, ω), RΓ_Z(ω))`: biduality on the source, then `RΓ_Z` moved inside the
derived Hom by `Stacks.LocalCohomology.CechFormula.localCohomologyDerivedHomMor`. -/
def localCohomologyBidualityMor (ω K : DerivedCategory (ModuleCat.{u} A)) :
    (localCohomologyEndofunctor A I hI).obj K ⟶
      (derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, ω)),
          (localCohomologyEndofunctor A I hI).obj ω) :=
  (localCohomologyEndofunctor A I hI).map
      (bidualityMor (derivedHomAdjunction (R := A)).toDerivedHomAdjunction ω K) ≫
    localCohomologyDerivedHomMor I hI f hf ω
      ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, ω))

omit [IsNoetherianRing A] in
/-- `Dualizing.LocalDuality.localCohomologyBidualityMor` is natural in `K`: biduality is natural
by `Dualizing.bidualityMor_naturality` and the second factor is natural by
`Stacks.LocalCohomology.CechFormula.localCohomologyDerivedHomMor_naturality`. -/
theorem localCohomologyBidualityMor_naturality (ω : DerivedCategory (ModuleCat.{u} A))
    {K K' : DerivedCategory (ModuleCat.{u} A)} (g : K ⟶ K') :
    (localCohomologyEndofunctor A I hI).map g ≫
        localCohomologyBidualityMor I hI f hf ω K' =
      localCohomologyBidualityMor I hI f hf ω K ≫
        (derivedHomAdjunction (R := A)).hom.map
          (((derivedHomAdjunction (R := A)).hom.map
            ((g.op, 𝟙 ω) : (Opposite.op K', ω) ⟶ (Opposite.op K, ω))).op,
            𝟙 ((localCohomologyEndofunctor A I hI).obj ω)) := by
  dsimp only [localCohomologyBidualityMor]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp,
    bidualityMor_naturality (derivedHomAdjunction (R := A)).toDerivedHomAdjunction ω g,
    CategoryTheory.Functor.map_comp, Category.assoc,
    localCohomologyDerivedHomMor_naturality I hI f hf ω
      ((derivedHomAdjunction (R := A)).hom.map
        ((g.op, 𝟙 ω) : (Opposite.op K', ω) ⟶ (Opposite.op K, ω))),
    Category.assoc]

/-- **Local duality without completion is an isomorphism.** For `ω` a dualizing complex and `K`
bounded below with finite cohomology modules, `RΓ_Z(K) ⟶ RHom_A(RHom_A(K, ω), RΓ_Z(ω))` is
invertible: biduality (Stacks 0A7C) makes the first factor invertible, and the second is
invertible because `RHom_A(K, ω)` is pseudo-coherent and `ω` is bounded below. -/
theorem isIso_localCohomologyBidualityMor (ω K : DerivedCategory (ModuleCat.{u} A))
    (hω : IsDualizingComplex ω) (n : ℤ) (hKge : K.IsGE n)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    IsIso (localCohomologyBidualityMor I hI f hf ω K) := by
  obtain ⟨a, b, J, hJge, hJle, hJinj, ⟨eJ⟩⟩ := hω.finiteInjectiveDimension
  have : J.IsStrictlyGE a := hJge
  have hωGE : ω.IsGE a := DerivedCategory.TStructure.t.isGE_of_iso eJ.symm a
  have hbid := isIso_bidualityMor_of_isDualizingComplex ω K hω hK
  have hb : IsIso ((localCohomologyEndofunctor A I hI).map
      (bidualityMor (derivedHomAdjunction (R := A)).toDerivedHomAdjunction ω K)) := by
    have := hbid
    infer_instance
  have hing := isIso_localCohomologyDerivedHomMor I hI f hf ω
    ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, ω))
    (isPseudoCoherent_derivedHom_of_isDualizingComplex ω K hω n hKge hK) ⟨a, hωGE⟩
  rw [localCohomologyBidualityMor]
  infer_instance

include hf in
/-- **`RΓ_Z(K) ≅ RHom_A(RHom_A(K, ω), RΓ_Z(ω))`** for `ω` a dualizing complex and `K` bounded
below with finite cohomology modules: local duality in the derived category, with no completion.
The isomorphism is `Dualizing.LocalDuality.localCohomologyBidualityMor`, natural in `K` by
`Dualizing.LocalDuality.localCohomologyBidualityMor_naturality`. -/
theorem nonempty_localCohomology_iso_derivedHom_derivedHom
    (ω K : DerivedCategory (ModuleCat.{u} A)) (hω : IsDualizingComplex ω) (n : ℤ)
    (hKge : K.IsGE n)
    (hK : ∀ i : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) :
    Nonempty ((localCohomologyEndofunctor A I hI).obj K ≅
      (derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, ω)),
          (localCohomologyEndofunctor A I hI).obj ω)) :=
  have := isIso_localCohomologyBidualityMor I hI f hf ω K hω n hKge hK
  ⟨asIso (localCohomologyBidualityMor I hI f hf ω K)⟩
end General

/-! ### The local case: `RΓ_Z(ω)` is the injective hull of the residue field -/

section Local

variable [IsLocalRing A] {r : ℕ}

/-- **Local duality without completion, over a Noetherian local ring.** For `ω` a normalized
dualizing complex, `E` an injective hull of the residue field and `K` bounded below with finite
cohomology modules,

`RΓ_Z(K) ≅ RHom_A(RHom_A(K, ω), E[0])`,   `Z = V(𝔪)`.

This is `Dualizing.LocalDuality.nonempty_localCohomology_iso_derivedHom_derivedHom` with the
identification of `RΓ_Z(ω)` with `E[0]` -- Stacks 0A82, in the form
`Dualizing.LocalDuality.nonempty_localCohomology_iso_single_homology_zero` together with the
uniqueness of injective hulls -- whiskered into the second argument. The identification does not
involve `K`, so naturality in `K` survives it. -/
theorem nonempty_localCohomology_iso_derivedHom_injectiveHull
    (f : Fin r → A) (hf : Ideal.span (Set.range f) = IsLocalRing.maximalIdeal A)
    (ω : DerivedCategory (ModuleCat.{u} A))
    (hω : IsNormalizedDualizingComplex.{u, u} ω)
    {E : ModuleCat.{u} A}
    (i : (ModuleCat.uliftFunctor.{u} A).obj
      (ModuleCat.of A (IsLocalRing.ResidueField A)) ⟶ E)
    [Mono i] (hi : Module.IsInjectiveHull i)
    (K : DerivedCategory (ModuleCat.{u} A)) (m : ℤ) (hKge : K.IsGE m)
    (hK : ∀ j : ℤ, Module.Finite A
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) j).obj K)) :
    Nonempty ((localCohomologyEndofunctor A (IsLocalRing.maximalIdeal A)
          (IsNoetherian.noetherian _)).obj K ≅
      (derivedHomAdjunction (R := A)).hom.obj
        (Opposite.op ((derivedHomAdjunction (R := A)).hom.obj (Opposite.op K, ω)),
          (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj E)) := by
  obtain ⟨e⟩ := nonempty_localCohomology_iso_derivedHom_derivedHom
    (IsLocalRing.maximalIdeal A) (IsNoetherian.noetherian _) f hf ω K hω.1 m hKge hK
  obtain ⟨concentrated⟩ := nonempty_localCohomology_iso_single_homology_zero.{u, u} A ω hω
  obtain ⟨j, hj, hjhull⟩ :=
    exists_isInjectiveHull_homology_zero_localCohomology.{u, u} A ω hω
  let := hj
  obtain ⟨hullIso, -⟩ := Module.exists_iso_of_isInjectiveHull j i hjhull hi
  exact ⟨e ≪≫ (derivedHomAdjunction (R := A)).hom.mapIso
    ((Iso.refl _).prod (concentrated ≪≫
      (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso hullIso))⟩

end Local

end LocalDuality

end Dualizing

end
