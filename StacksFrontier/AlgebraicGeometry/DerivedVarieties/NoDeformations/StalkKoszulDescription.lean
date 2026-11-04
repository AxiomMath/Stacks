module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.ClosedFibreTransport
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.LiftedKoszulExistence
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.StalkKoszulDeformationSituation
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalkPerfect
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.StalkSpellingFunctorBridge
public import StacksFrontier.RingTheory.Koszul.DerivedQuotientModel
public import StacksFrontier.RingTheory.Koszul.Regular

/-!
# Case II of Stacks 0G0R, in a local ring

Let `p : W ⟶ S` be flat and locally of finite type over a locally Noetherian base, let `z` be a
point of `W`, and let `K` be a perfect object of `D(𝒪_W)`. Suppose the closed fibre of the stalk
map of `p` at `z` is presented, by a ring isomorphism `E`, as a ring `B` in which a regular
sequence `f̄₁, …, f̄_r` is given, and suppose the derived restriction of `K_z` to that closed fibre
is the cyclic module `B ⧸ (f̄₁, …, f̄_r)` placed in degree zero. Then `K_z` itself is a cyclic
module `𝒪_{W,z} ⧸ I` placed in degree zero, with `I` reducing to `(f̄₁, …, f̄_r)` on the closed
fibre and with `𝒪_{W,z} ⧸ I` flat over the local ring of the base.

That is what Case II of [Stacks, Tag 0G0R] extracts from [Stacks, Tag 0G0N], in the form the rest
of its argument consumes: the ideal `I` is the one cutting out the subscheme `Z`, and the flatness
is the flatness of `Z` over `S`.

## Main results

* `AlgebraicGeometry.isPerfect_derivedStalk_of_isPerfect`: the derived stalk of a perfect object
  is perfect.
* `AlgebraicGeometry.mem_map_maximalIdeal_of_surjective`: a surjective homomorphism of local
  rings carries the maximal ideal onto the maximal ideal.
* `AlgebraicGeometry.exists_ideal_derivedStalk_iso_single_of_closedFibre_koszul`: **the
  statement above.**

## Implementation notes

The three hypotheses of `AlgebraicGeometry.FlatLocalKoszulDeformationSituation` that are not
automatic for a stalk map are produced here from the data over `B`:

* the regular sequence is `E⁻¹ ∘ f̄`, regular by
  `RingTheory.Sequence.isRegular_of_ringEquiv`;
* its membership in the image of the maximal ideal follows from
  `mem_map_maximalIdeal_of_surjective`, the closed-fibre map being a surjection of local rings;
* the Koszul identification on the closed fibre is
  `StacksDraft.DerivedRingIso.nonempty_iso_single_of_ringEquiv` followed by
  `StacksDraft.DerivedRingIso.quotientRestrictScalarsIso` and
  `Koszul.nonempty_Q_obj_seqCochainComplex_iso_single`, the last requiring Koszul-regularity of
  the transported sequence, which is [Stacks, Tag 062F].

Perfectness of the derived stalk is
`AlgebraicGeometry.RingedSpace.isPerfect_moduleStalkOver_of_isPerfect` at the local-ring spelling
of the stalk functor; the three exactness instances have to be
re-seated at the `StrictlyPerfect.OXMod` spelling of the source category, which instance search
does not reach on its own.

The conclusion's Koszul complex is turned back into a cyclic module by
`Koszul.nonempty_Q_obj_seqCochainComplex_iso_single` at the lifted sequence, which is regular in
`𝒪_{W,z}` by [Stacks, Tag 0G0N] and therefore Koszul-regular.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 0G0N](https://stacks.math.columbia.edu/tag/0G0N)
* [Stacks Project, Tag 062F](https://stacks.math.columbia.edu/tag/062F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-- **The derived stalk of a perfect object is perfect.** -/
theorem isPerfect_derivedStalk_of_isPerfect {X : Scheme.{u}} (x : X)
    (K : DerivedCategory X.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K) :
    StacksDraft.Perfect.IsPerfect ((derivedStalkFunctor x).obj K) := by
  have hA : (show StrictlyPerfect.OXMod X.toRingedSpace ⥤
      ModuleCat.{u} (X.presheaf.stalk x) from
      Stacks.ModuleSkyscraper.modulesStalkFunctor X x).Additive :=
    inferInstanceAs (Stacks.ModuleSkyscraper.modulesStalkFunctor X x).Additive
  have hL : PreservesFiniteLimits (show StrictlyPerfect.OXMod X.toRingedSpace ⥤
      ModuleCat.{u} (X.presheaf.stalk x) from
      Stacks.ModuleSkyscraper.modulesStalkFunctor X x) :=
    inferInstanceAs (PreservesFiniteLimits (Stacks.ModuleSkyscraper.modulesStalkFunctor X x))
  have hC : PreservesFiniteColimits (show StrictlyPerfect.OXMod X.toRingedSpace ⥤
      ModuleCat.{u} (X.presheaf.stalk x) from
      Stacks.ModuleSkyscraper.modulesStalkFunctor X x) :=
    inferInstanceAs (PreservesFiniteColimits (Stacks.ModuleSkyscraper.modulesStalkFunctor X x))
  exact AlgebraicGeometry.RingedSpace.isPerfect_moduleStalkOver_of_isPerfect x
    (ringCatStalkRingEquiv x).symm (Stacks.ModuleSkyscraper.modulesStalkFunctor X x)
    (modulesRingCatStalkFunctorIso x).symm K hK

/-- **A surjection of local rings carries the maximal ideal onto the maximal ideal.** -/
theorem mem_map_maximalIdeal_of_surjective {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] (φ : A →+* B) (hsurj : Function.Surjective φ) (b : B)
    (hb : b ∈ IsLocalRing.maximalIdeal B) :
    b ∈ Ideal.map φ (IsLocalRing.maximalIdeal A) := by
  obtain ⟨a, rfl⟩ := hsurj b
  refine Ideal.mem_map_of_mem _ ?_
  by_contra hna
  exact IsLocalRing.notMem_maximalIdeal.mpr ((IsLocalRing.notMem_maximalIdeal.mp hna).map φ) hb

/-- The image of the ideal generated by `u` under `φ` is generated by `v` if `φ ∘ u = v`. -/
private theorem map_span_range_eq_of_apply_eq {A B ι : Type*} [CommRing A] [CommRing B]
    (φ : A →+* B) (u : ι → A) (v : ι → B) (h : ∀ i, φ (u i) = v i) :
    Ideal.map φ (Ideal.span (Set.range u)) = Ideal.span (Set.range v) := by
  rw [Ideal.map_span, ← Set.range_comp]
  exact congrArg (Ideal.span ∘ Set.range) (funext h)

/-- The Koszul complex on a regular sequence resolves the cyclic module it cuts out. -/
private theorem nonempty_Q_obj_seqCochainComplex_iso_single_of_regular {R : Type u} [CommRing R]
    {r : ℕ} (f : Fin r → R) (hf : RingTheory.Sequence.IsRegular R (List.ofFn f)) :
    Nonempty (DerivedCategory.Q.obj (Koszul.seqCochainComplex f) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R (R ⧸ Ideal.span (Set.range f)))) :=
  Koszul.nonempty_Q_obj_seqCochainComplex_iso_single f
    ((Koszul.isKoszulRegularOn_and_isKoszulRegular_of_regular (M := R)).2.2 hf)

/-- **The closed-fibre Koszul identification, transported along a ring isomorphism.** If the
derived restriction of `K_z` to a ring `B ≅ 𝒪_{W,z} ⧸ 𝔪` is `B ⧸ (f̄)` in degree zero, its derived
restriction to the closed fibre is the Koszul complex of the transported regular sequence. -/
theorem nonempty_derivedExtensionScalars_iso_koszul_of_ringEquiv {W S : Scheme.{u}} (p : W ⟶ S)
    (z : W) {B : Type u} [CommRing B] (E : (W.presheaf.stalk z ⧸ stalkMapFibreIdeal p z) ≃+* B)
    {r : ℕ} (fbar : Fin r → B) (fbar' : Fin r → W.presheaf.stalk z ⧸ stalkMapFibreIdeal p z)
    (hEfbar : ∀ i, E (fbar' i) = fbar i)
    (hreg' : RingTheory.Sequence.IsRegular
      (W.presheaf.stalk z ⧸ stalkMapFibreIdeal p z) (List.ofFn fbar'))
    (K : DerivedCategory W.Modules)
    (hfib : Nonempty ((totalDerivedExtensionScalars.{u, u, u}
        ((E : _ →+* B).comp (Ideal.Quotient.mk (stalkMapFibreIdeal p z)))).functor.obj
        ((derivedStalkFunctor z).obj K) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        (ModuleCat.of B (B ⧸ Ideal.span (Set.range fbar))))) :
    Nonempty ((derivedExtensionScalarsGeneral
      (Ideal.Quotient.mk (stalkMapFibreIdeal p z))).functor.obj
      ((derivedStalkFunctor z).obj K) ≅ DerivedCategory.Q.obj
        ((Koszul.seqComplex fbar').extend ComplexShape.embeddingDownNat)) := by
  have hspan' := map_span_range_eq_of_apply_eq (E : _ →+* B) fbar' fbar hEfbar
  have emod : (ModuleCat.restrictScalars.{u, u, u} (E : _ →+* B)).obj
      (ModuleCat.of B (B ⧸ Ideal.span (Set.range fbar))) ≅
      ModuleCat.of (W.presheaf.stalk z ⧸ stalkMapFibreIdeal p z)
        ((W.presheaf.stalk z ⧸ stalkMapFibreIdeal p z) ⧸ Ideal.span (Set.range fbar')) :=
    Iso.symm (StacksDraft.DerivedRingIso.quotientRestrictScalarsIso E
        (Ideal.span (Set.range fbar')) ≪≫
      (ModuleCat.restrictScalars.{u, u, u}
          (E : (W.presheaf.stalk z ⧸ stalkMapFibreIdeal p z) →+* B)).mapIso
        (eqToIso (congrArg (fun J => ModuleCat.of B (B ⧸ J)) hspan')))
  obtain ⟨e⟩ := StacksDraft.DerivedRingIso.nonempty_iso_single_of_ringEquiv E
    (Ideal.Quotient.mk (stalkMapFibreIdeal p z)) ((derivedStalkFunctor z).obj K)
    (ModuleCat.of B (B ⧸ Ideal.span (Set.range fbar))) hfib
  obtain ⟨eK⟩ := nonempty_Q_obj_seqCochainComplex_iso_single_of_regular fbar' hreg'
  exact ⟨e ≪≫ (DerivedCategory.singleFunctor
    (ModuleCat.{u} (W.presheaf.stalk z ⧸ stalkMapFibreIdeal p z)) 0).mapIso emod ≪≫ eK.symm⟩

section CaseII

variable {W S : Scheme.{u}} (p : W ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType p] [Flat p]
  (z : W)

/-- **Case II of [Stacks, Tag 0G0R] in the local ring at `z`.** In a flat deformation situation
whose closed fibre is presented as a ring `B` carrying a regular sequence `f̄`, a perfect `K`
whose derived restriction to the closed fibre is `B ⧸ (f̄)` in degree zero is itself a cyclic
module `𝒪_{W,z} ⧸ I` in degree zero, with `I` reducing to `(f̄)` and `𝒪_{W,z} ⧸ I` flat over the
base. -/
theorem exists_ideal_derivedStalk_iso_single_of_closedFibre_koszul
    {B : Type u} [CommRing B] (E : (W.presheaf.stalk z ⧸ stalkMapFibreIdeal p z) ≃+* B)
    {r : ℕ} (fbar : Fin r → B)
    (hreg : RingTheory.Sequence.IsRegular B (List.ofFn fbar))
    (hmem : ∀ i, fbar i ∈ Ideal.map ((E : _ →+* B).comp
      (Ideal.Quotient.mk (stalkMapFibreIdeal p z)))
      (IsLocalRing.maximalIdeal (W.presheaf.stalk z)))
    (K : DerivedCategory W.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) K)
    (hfib : Nonempty ((totalDerivedExtensionScalars.{u, u, u}
        ((E : _ →+* B).comp (Ideal.Quotient.mk (stalkMapFibreIdeal p z)))).functor.obj
        ((derivedStalkFunctor z).obj K) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj
        (ModuleCat.of B (B ⧸ Ideal.span (Set.range fbar))))) :
    ∃ I : Ideal (W.presheaf.stalk z),
      Nonempty ((derivedStalkFunctor z).obj K ≅
        (DerivedCategory.singleFunctor (ModuleCat.{u} (W.presheaf.stalk z)) 0).obj
          (ModuleCat.of (W.presheaf.stalk z) (W.presheaf.stalk z ⧸ I))) ∧
      Ideal.map ((E : _ →+* B).comp (Ideal.Quotient.mk (stalkMapFibreIdeal p z))) I =
        Ideal.span (Set.range fbar) ∧
      RingHom.Flat ((Ideal.Quotient.mk I).comp (p.stalkMap z).hom) := by
  classical
  let fbar' : Fin r → (W.presheaf.stalk z ⧸ stalkMapFibreIdeal p z) := fun i => E.symm (fbar i)
  have hEfbar : ∀ i, E (fbar' i) = fbar i := fun i => E.apply_symm_apply (fbar i)
  have hmapfbar : (List.ofFn fbar').map E = List.ofFn fbar := by
    rw [List.map_ofFn]
    exact congrArg List.ofFn (funext hEfbar)
  have hreg' : RingTheory.Sequence.IsRegular
      (W.presheaf.stalk z ⧸ stalkMapFibreIdeal p z) (List.ofFn fbar') :=
    RingTheory.Sequence.isRegular_of_ringEquiv E (List.ofFn fbar') (by rwa [hmapfbar])
  have hmem' : ∀ i, fbar' i ∈ (IsLocalRing.maximalIdeal (W.presheaf.stalk z)).map
      (Ideal.Quotient.mk (stalkMapFibreIdeal p z)) := by
    intro i
    have h : fbar i ∈ Ideal.map
        (E : (W.presheaf.stalk z ⧸ stalkMapFibreIdeal p z) →+* B)
        ((IsLocalRing.maximalIdeal (W.presheaf.stalk z)).map
          (Ideal.Quotient.mk (stalkMapFibreIdeal p z))) := by
      rw [Ideal.map_map]
      exact hmem i
    obtain ⟨a, ha, hae⟩ := (Ideal.mem_map_iff_of_surjective
      (E : (W.presheaf.stalk z ⧸ stalkMapFibreIdeal p z) →+* B) E.surjective).mp h
    exact (E.injective (by rwa [hEfbar i]) : a = fbar' i) ▸ ha
  obtain ⟨f, hfbar2, hfreg, hfflat, ⟨eKos⟩⟩ :=
    exists_koszulDescription_and_flat_quotient_of_fibrewise_koszul
      (flatLocalKoszulDeformationSituationOfStalkMap p z r fbar' hmem' hreg'
        ((derivedStalkFunctor z).obj K) (isPerfect_derivedStalk_of_isPerfect z K hK)
        (nonempty_derivedExtensionScalars_iso_koszul_of_ringEquiv p z E fbar fbar' hEfbar
          hreg' K hfib))
  let g : Fin r → W.presheaf.stalk z := f
  have hgreg : RingTheory.Sequence.IsRegular (W.presheaf.stalk z) (List.ofFn g) := hfreg
  refine ⟨Ideal.span (Set.range g), ?_, ?_, hfflat⟩
  · obtain ⟨eQ⟩ := nonempty_Q_obj_seqCochainComplex_iso_single_of_regular g hgreg
    exact ⟨eKos ≪≫ eQ⟩
  · refine map_span_range_eq_of_apply_eq _ g _ fun i => ?_
    exact (congrArg E
      (hfbar2 i : Ideal.Quotient.mk (stalkMapFibreIdeal p z) (f i) = fbar' i)).trans (hEfbar i)

end CaseII

end AlgebraicGeometry

end
