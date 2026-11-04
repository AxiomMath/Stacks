module

public import Mathlib.Algebra.Category.ModuleCat.Descent
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Finiteness.Descent
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
public import StacksFrontier.Homology.Perfect.Basic
public import StacksFrontier.Homology.Perfect.BaseChange
public import StacksFrontier.Homology.Perfect.FibreCriterion
public import StacksFrontier.Homology.Perfect.MinimalRepresentative
public import StacksFrontier.Homology.PseudoCoherent.Local
public import StacksFrontier.Homology.PseudoCoherent.Locality
public import StacksFrontier.Homology.PseudoCoherent.Relative.Defs
public import StacksFrontier.Homology.PseudoCoherent.Triangle
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars

@[expose] public section

/-!
# Perfectness of a complex is a local condition

Let `R` be a commutative ring and let `K` be an object of the derived category `D(R)`. This module
proves that perfectness of `K` is local: it descends along a finite cover of `Spec R` by standard
opens, it descends along a faithfully flat ring map, and for a pseudo-coherent `K` perfectness
together with a prescribed Tor window is detected by the cohomology of the derived fibres
`K ⊗_R^L κ(p)`.

## Main results

* `StacksDraft.Perfect.isPerfect_of_localizationSpan` ([stacks 066Y]): perfectness descends along
  a finite cover of `Spec R` by standard opens.
* `StacksDraft.Perfect.isPerfect_of_faithfullyFlat_baseChange` ([stacks 068T]): perfectness
  descends along a faithfully flat map of commutative rings.
* `StacksDraft.Perfect.isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes`
  ([stacks 068V]): a pseudo-coherent object is perfect of Tor amplitude in `[a, b]` exactly when
  the cohomology of every derived fibre vanishes outside `[a, b]`, and it is enough to test the
  fibres at maximal ideals.
* `StacksDraft.Perfect.isPerfect_iff_isPerfect_at_primes_of_isBoundedBelow_and_stalkwise_criteria`
  ([stacks 068W]): for a pseudo-coherent object, perfectness at all prime stalks, at all maximal
  stalks, and the vanishing of the derived fibre cohomology in all sufficiently low degrees at
  every prime or every maximal ideal are equivalent, and for a bounded below object they are
  equivalent to perfectness itself.
* `StacksDraft.Perfect.fibreCohomologyVanishes_iff_isZero_homology`: the fibre-cohomology
  predicate of `Perfect.FibreCriterion` and the vanishing of `Hⁱ(K ⊗_R^L κ(p))` for the canonical
  derived base change of [stacks 064H] agree on a pseudo-coherent object.

## Implementation notes

The route is the characterization [stacks 0658] of perfectness as pseudo-coherence together with
finite Tor dimension. Pseudo-coherence descends by [stacks 066D], which is available as
`StacksDraft.PseudoCoherence.isPseudoCoherentFrom_and_isPseudoCoherent_of_localizationAux`. For the
Tor-dimension half, finite Tor dimension is recorded by `Perfect.HasFlatRepresentative`, and
rather than descending a flat representative directly the proof descends the single piece of data
that `HasFlatRepresentative` is used for: pseudo-coherence supplies a bounded above complex `F` of
finite free modules representing `K`, and the flat representatives of the localizations force both
the cohomology of `K` to vanish outside the common window `[a, b]` (by [stacks 00EO] (1)) and the
cokernel of `F^{a-1} → F^a` to be flat (by flatness being local on a standard cover,
`Module.flat_of_isLocalized_span`). The canonical truncation `F≥a` is then a flat representative
of `K` supported in `[a, b]`.

The same two ingredients prove the faithfully flat descent: pseudo-coherence descends, which is
the content of [stacks 068R], and flatness of the bottom cokernel descends by
`Module.Flat.of_flat_tensorProduct`.

For the fibrewise criterion the derived fibre is the one of `Perfect.FibreCriterion`: it is
computed on a bounded above finite free representative, which is K-flat. The forward direction
compares such a representative with the finite projective representative in `[a, b]` supplied by
[stacks 0658]; both are K-projective, hence homotopy equivalent, and extension of scalars to the
residue field preserves homotopy equivalences. The backward direction runs [stacks 068U] in degree
`a - 1` at every maximal ideal, which makes the localization perfect with a representative in
degrees `≥ a` on a standard open cover, and then descends along that cover.

Tor amplitude in `[a, b]` is recorded by `Perfect.HasFlatRepresentative`, which by [stacks 0654] is
exactly Tor amplitude in `[a, b]` and is the form in which [stacks 0658] states finite Tor
dimension. The statement of [stacks 068V] additionally spells out the termwise consequence: every
bounded above flat representative of `K`, which is what computes `K ⊗_R^L M`, has vanishing
cohomology outside `[a, b]` after tensoring with an arbitrary module.

The stalkwise criterion is stated over the canonical derived base change of [stacks 064H],
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`, rather than over a
caller-supplied datum. That the base change of a perfect object is perfect is [stacks 066W] from
`Perfect.BaseChange`, which is itself already stated over the same canonical datum, so it applies
with no comparison in between. The two other implications that are not bookkeeping are: at a fixed
prime, the stalk is perfect exactly when the fibre cohomology dies in all low degrees, proved over
the unique maximal ideal of `R_p` where [stacks 0BYP] produces a single element on whose principal
open the stalk is perfect, and that open is all of `Spec R_p`; and for a bounded below object,
[stacks 0BYP] at every maximal ideal produces a cover of `Spec R` along which [stacks 066Y]
descends perfectness. On a pseudo-coherent object, the fibre predicate of `Perfect.FibreCriterion`
and the vanishing of the cohomology of the canonical derived fibre agree, by
`fibreCohomologyVanishes_iff_isZero_homology`.

The finite family of elements in the source is represented by a family indexed by a finite type,
and the derived tensor product with `R_{f_i}` by derived extension of scalars along
`R → R_{f_i}`, which is exact because a localization is flat. Ring and module carrier universes
are kept independent.

## References

* [Stacks Project, Tag 066Y](https://stacks.math.columbia.edu/tag/066Y)
* [Stacks Project, Tag 068T](https://stacks.math.columbia.edu/tag/068T)
* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
* [Stacks Project, Tag 068W](https://stacks.math.columbia.edu/tag/068W)
-/

open CategoryTheory CategoryTheory.Limits
open scoped ChangeOfRings

universe u v w

attribute [local instance] HasDerivedCategory.standard

namespace StacksDraft.Perfect

/-! ### Elementary manipulations of flat representatives -/

/-- A flat representative is transported along an isomorphism of the derived category. -/
private lemma hasFlatRepresentative_of_iso {R : Type u} [CommRing R]
    {X Y : DerivedCategory (ModuleCat.{max u v} R)} (e : X ≅ Y) {a b : ℤ}
    (h : HasFlatRepresentative X a b) : HasFlatRepresentative Y a b := by
  obtain ⟨E, hflat, hge, hle, ⟨eE⟩⟩ := h
  exact ⟨E, hflat, hge, hle, ⟨e.symm ≪≫ eE⟩⟩

/-- A flat representative supported in `[a, b]` is also one supported in any larger window. -/
private lemma hasFlatRepresentative_mono {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{max u v} R)} {a a' b b' : ℤ}
    (ha : a' ≤ a) (hb : b ≤ b') (h : HasFlatRepresentative K a b) :
    HasFlatRepresentative K a' b' := by
  obtain ⟨E, hflat, hge, hle, e⟩ := h
  let : E.IsStrictlyGE a := hge
  let : E.IsStrictlyLE b := hle
  exact ⟨E, hflat, E.isStrictlyGE_of_ge a' a ha, E.isStrictlyLE_of_le b b' hb, e⟩

/-- **The canonical truncation is a flat representative.** Let `F` be a bounded above complex of
flat `R`-modules representing `K`, vanishing strictly above `b`, and assume that the cohomology of
`K` vanishes below `a` and that the cokernel of `F^{a-1} → F^a` is flat. Then the canonical
truncation `F≥a` is a complex of flat modules concentrated in `[a, b]` representing `K`, so `K`
has a flat representative supported in `[a, b]`. -/
private lemma hasFlatRepresentative_truncGE {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ)
    (F : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (α : DerivedCategory.Q.obj F ⟶ K) (hα : IsIso α)
    (hFLE : F.IsStrictlyLE b) (hFflat : ∀ i : ℤ, Module.Flat R (F.X i))
    (hlow : ∀ j : ℤ, j < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) j).obj K))
    (hcok : Module.Flat R (cokernel (F.d (a - 1) a) : ModuleCat.{max u v} R)) :
    HasFlatRepresentative K a b := by
  have := hα
  have hFGE : F.IsGE a := by
    rw [CochainComplex.isGE_iff]
    intro j hj
    rw [HomologicalComplex.exactAt_iff_isZero_homology]
    exact (hlow j hj).of_iso
      (((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) j).app F).symm ≪≫
        (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) j).mapIso (asIso α))
  have : QuasiIso (F.πTruncGE a) := inferInstance
  refine ⟨F.truncGE a, ?_, inferInstance, truncGE_isStrictlyLE F a b hFLE,
    ⟨(asIso α).symm ≪≫ asIso (DerivedCategory.Q.map (F.πTruncGE a))⟩⟩
  intro j
  by_cases hj : j < a
  · have hz : IsZero ((F.truncGE a).X j) :=
      CochainComplex.isZero_of_isStrictlyGE (F.truncGE a) a j hj
    let : Subsingleton ((F.truncGE a).X j) := ModuleCat.isZero_iff_subsingleton.mp hz
    let : Module.Projective R ((F.truncGE a).X j) := inferInstance
    infer_instance
  · by_cases haj : j = a
    · subst haj
      let e : (F.truncGE j).X j ≅ (cokernel (F.d (j - 1) j) : ModuleCat.{max u v} R) :=
        F.truncGEXIsoOpcycles j ≪≫
          IsColimit.coconePointUniqueUpToIso (F.opcyclesIsCokernel (j - 1) j (by simp))
            (colimit.isColimit _)
      let : Module.Flat R ((cokernel (F.d (j - 1) j) : ModuleCat.{max u v} R)) := hcok
      exact Module.Flat.of_linearEquiv e.toLinearEquiv
    · have haj' : a < j := lt_of_le_of_ne (not_lt.mp hj) (Ne.symm haj)
      let e : (F.truncGE a).X j ≅ F.X j := CochainComplex.truncGEXIso F a j haj'
      let : Module.Flat R (F.X j) := hFflat j
      exact Module.Flat.of_linearEquiv e.toLinearEquiv

/-! ### Flatness of the bottom cokernel after localization -/

/-- **The base change of the bottom cokernel is flat.** Let `F` be a complex of flat `R`-modules
vanishing strictly above `b`, let `R → S` be flat, and suppose the termwise base change of `F` to
`S` has a flat representative supported in `[a, c]`. Then the base change of the cokernel of
`F^{a-1} → F^a` is a flat `S`-module.

Extension of scalars along a flat map preserves cokernels and flatness of the terms, so [stacks
0653] applies to the base change of `F` over `S`. -/
private lemma flat_extendScalars_cokernel {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.Flat) (F : CochainComplex (ModuleCat.{w} R) ℤ) (a b c : ℤ)
    (hFLE : F.IsStrictlyLE b) (hFflat : ∀ i : ℤ, Module.Flat R (F.X i))
    (hamp : HasFlatRepresentative
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)) a c) :
    Module.Flat S ((ModuleCat.extendScalars.{u, v, w} f).obj (cokernel (F.d (a - 1) a))) := by
  let G := ModuleCat.extendScalars.{u, v, w} f
  have : Limits.PreservesFiniteLimits G :=
    StacksDraft.PseudoCoherence.preservesFiniteLimits_extendScalars_of_flat f hf
  have : Limits.PreservesFiniteColimits G :=
    StacksDraft.PseudoCoherence.preservesFiniteColimits_extendScalars f
  have : Limits.PreservesColimit (Limits.parallelPair (F.d (a - 1) a) 0) G :=
    StacksDraft.PseudoCoherence.preservesCokernel_extendScalars f (F.d (a - 1) a)
  set F' := (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj F with hF'
  have hF'bounded : TorAmplitude.BoundedAbove F' :=
    ⟨b, fun n hn => G.map_isZero (CochainComplex.isZero_of_isStrictlyLE F b n hn)⟩
  have hF'flat : TorAmplitude.IsComplexOfFlats F' := by
    intro n
    algebraize [f]
    have : Module.Flat R (F.X n) := hFflat n
    have : Module.Flat S (TensorProduct R S ((F.X n : Type w))) :=
      Module.Flat.baseChange R S _
    exact this
  have hcok : Module.Flat S (cokernel (F'.d (a - 1) a) : ModuleCat.{max v w} S) :=
    cokernel_flat_of_hasFlatRepresentative F' a c hF'bounded hF'flat hamp
  exact Module.Flat.of_linearEquiv
    (M := (cokernel (F'.d (a - 1) a) : ModuleCat.{max v w} S))
    (PreservesCokernel.iso G (F.d (a - 1) a)).toLinearEquiv

/-! ### Descent of perfectness along a standard open cover -/

/-- **Descent of a flat representative along a standard open cover.** Let the elements `f i`
generate the unit ideal, let `K` be pseudo-coherent with cohomology vanishing outside `[a, b]`,
and suppose each derived localization `K ⊗_R R_{f i}` has a flat representative supported in
`[a, c i]` for some upper bound `c i` depending on `i`. Then `K` itself has a flat representative
supported in `[a, b]`.

Pseudo-coherence supplies a bounded above complex `F` of finite free modules representing `K` and
vanishing strictly above `b`; flatness of the cokernel of `F^{a-1} → F^a` is local on the cover,
and the canonical truncation `F≥a` is then the required representative. -/
private lemma hasFlatRepresentative_of_localizationSpan {R : Type u} [CommRing R]
    {ι : Type*} [Finite ι] (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ)
    (hpseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (hvan : ∀ j : ℤ, (j < a ∨ b < j) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) j).obj K))
    (hloc : ∀ i, ∃ c : ℤ, HasFlatRepresentative
      ((PseudoCoherence.localizationAwayFunctorAux.{u, v} (f i)).obj K) a c) :
    HasFlatRepresentative K a b := by
  classical
  obtain ⟨F, α, hFfree, hFLE, hα⟩ :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
      K b).2.2 hpseudo fun j hj => hvan j (Or.inr hj)
  have hFflat : ∀ i : ℤ, Module.Flat R (F.X i) := by
    intro i
    have : Module.Free R (F.X i) := (hFfree i).2
    infer_instance
  have hcokflat : Module.Flat R
      ((cokernel (F.d (a - 1) a) : ModuleCat.{max u v} R) : Type (max u v)) := by
    refine Module.flat_of_isLocalized_span R _ (Set.range f) hf
      (fun r => TensorProduct R (Localization.Away r.1)
        ((cokernel (F.d (a - 1) a) : ModuleCat.{max u v} R) : Type (max u v)))
      (fun r => TensorProduct.mk R (Localization.Away r.1) _ 1) ?_
    rintro ⟨-, i, rfl⟩
    obtain ⟨c, hc⟩ := hloc i
    have hflat : Module.Flat R (Localization.Away (f i)) :=
      IsLocalization.flat (Localization.Away (f i)) (Submonoid.powers (f i))
    let G := ModuleCat.extendScalars.{u, u, max v u} (algebraMap R (Localization.Away (f i)))
    have : G.Additive := extendScalars_additive.{u, u, max v u} _
    have : PreservesFiniteLimits G :=
      StacksDraft.PseudoCoherence.preservesFiniteLimits_extendScalars_of_flat _
        (RingHom.flat_algebraMap_iff.mpr hflat)
    have : PreservesFiniteColimits G :=
      StacksDraft.PseudoCoherence.preservesFiniteColimits_extendScalars _
    have hloc' := flat_extendScalars_cokernel (algebraMap R (Localization.Away (f i)))
      (RingHom.flat_algebraMap_iff.mpr hflat) F a b c hFLE hFflat
      (hasFlatRepresentative_of_iso (G.mapDerivedCategoryFactors.app F)
        (hasFlatRepresentative_of_iso
          ((PseudoCoherence.localizationAwayFunctorAux.{u, v} (f i)).mapIso (asIso α).symm) hc))
    have : Module.Flat (Localization.Away (f i))
        (TensorProduct R (Localization.Away (f i))
          ((cokernel (F.d (a - 1) a) : ModuleCat.{max u v} R) : Type (max u v))) :=
      Module.Flat.of_linearEquiv
        (PseudoCoherence.extendScalarsTensorIso (S := Localization.Away (f i)) _).toLinearEquiv.symm
    exact Module.Flat.trans R (Localization.Away (f i)) _
  exact hasFlatRepresentative_truncGE K a b F α hα hFLE hFflat
    (fun j hj => hvan j (Or.inl hj)) hcokflat

/-- Let `R` be a commutative ring, let the elements `f i` generate the unit ideal, and let `K` be
an object of the derived category of `R`-modules. If the derived localization `K ⊗_R R_{f i}` is
perfect for every `i`, then `K` is perfect. -/
@[stacks 066Y]
theorem isPerfect_of_localizationSpan {R : Type u} [CommRing R] {ι : Type*} [Finite ι]
    (f : ι → R) (hf : Ideal.span (Set.range f) = ⊤)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : ∀ i, IsPerfect ((PseudoCoherence.localizationAwayFunctorAux.{u, v} (f i)).obj K)) :
    IsPerfect K := by
  classical
  have hlocal : ∀ i, StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((PseudoCoherence.localizationAwayFunctorAux.{u, v} (f i)).obj K) ∧
      ∃ a b : ℤ, HasFlatRepresentative
        ((PseudoCoherence.localizationAwayFunctorAux.{u, v} (f i)).obj K) a b := fun i =>
    (isPerfect_iff_pseudoCoherent_and_finiteTorDimension _).1.mp (hK i)
  have hpseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent K :=
    (PseudoCoherence.isPseudoCoherentFrom_and_isPseudoCoherent_of_localizationAux f hf K 0).2
      fun i => (hlocal i).1
  choose a b hab using fun i => (hlocal i).2
  obtain ⟨a', ha'⟩ := Finite.bddBelow_range a
  obtain ⟨b', hb'⟩ := Finite.bddAbove_range b
  have hamp : ∀ i, HasFlatRepresentative
      ((PseudoCoherence.localizationAwayFunctorAux.{u, v} (f i)).obj K) a' b' := fun i =>
    hasFlatRepresentative_mono (ha' ⟨i, rfl⟩) (hb' ⟨i, rfl⟩) (hab i)
  have hvan : ∀ j : ℤ, (j < a' ∨ b' < j) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) j).obj K) := by
    intro j hj
    rw [ModuleCat.isZero_iff_subsingleton]
    apply Module.subsingleton_of_localizationSpan_range f hf
    intro i
    exact ModuleCat.isZero_iff_subsingleton.mp
      ((homology_isZero_of_hasFlatRepresentative _ a' b' j (hamp i) hj).of_iso
        (PseudoCoherence.localizationAwayHomologyIso (f i) K j).symm)
  exact (isPerfect_iff_pseudoCoherent_and_finiteTorDimension K).1.mpr
    ⟨hpseudo, a', b',
      hasFlatRepresentative_of_localizationSpan f hf K a' b' hpseudo hvan
        fun i => ⟨b', hamp i⟩⟩

/-! ### Faithfully flat descent of pseudo-coherence

The declarations in this section descend `m`-pseudo-coherence and pseudo-coherence along a
faithfully flat ring map; this is the content of [stacks 068R].
-/

section FaithfullyFlat

/-- Extension of scalars along a ring map preserves zero morphisms, with no relation imposed
between the universe of the target ring and the universe of the source modules. Mathlib's
instance goes through the adjunction, which needs the module universe to contain the universe of
the target ring. -/
instance (priority := high) extendScalars_preservesZeroMorphisms
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S) :
    (ModuleCat.extendScalars.{u, v, w} f).PreservesZeroMorphisms :=
  ⟨fun X Y => by
    ext m
    change (1 : S) ⊗ₜ[R,f] ((0 : X →ₗ[R] Y) m) = 0
    simp⟩

private theorem isPseudoCoherentFrom_mono
    {R : Type u} [Ring R]
    {K : DerivedCategory (ModuleCat.{w} R)} {m n : ℤ}
    (hmn : m ≤ n) (hK : PseudoCoherence.IsPseudoCoherentFrom K m) :
    PseudoCoherence.IsPseudoCoherentFrom K n := by
  obtain ⟨E, hE, α, hα, hαm⟩ := hK
  refine ⟨E, hE, α, fun i hi => hα i (lt_of_le_of_lt hmn hi), ?_⟩
  rcases hmn.eq_or_lt with rfl | h
  · exact hαm
  · have := hα n h
    infer_instance

private theorem finite_homology_of_isPseudoCoherentFrom_of_vanishing
    {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{w} R)) (m n : ℤ)
    (hmn : m ≤ n) (hK : PseudoCoherence.IsPseudoCoherentFrom K m)
    (hvanish : ∀ i : ℤ, n < i →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj K)) :
    Module.Finite R ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) n).obj K) :=
  _root_.PseudoCoherence.finite_homology_of_isPseudoCoherentFrom K n
    (isPseudoCoherentFrom_mono hmn hK) hvanish

private theorem isPseudoCoherentFrom_boundedAboveHomology
    {R : Type u} [CommRing R]
    {K : DerivedCategory (ModuleCat.{w} R)} {m : ℤ}
    (hK : PseudoCoherence.IsPseudoCoherentFrom K m) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj K) := by
  obtain ⟨E, hE, α, hα, _⟩ := hK
  obtain ⟨b, hb⟩ := hE.upperBound
  refine ⟨max m b, fun i hi => ?_⟩
  have hm : m < i := lt_of_le_of_lt (le_max_left m b) hi
  have hb' : b < i := lt_of_le_of_lt (le_max_right m b) hi
  have : E.IsStrictlyLE b := hb
  have hzero : Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).obj
        (DerivedCategory.Q.obj E)) :=
    DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj E) b i hb'
  have : IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) i).map α) := hα i hm
  exact hzero.of_iso (asIso ((DerivedCategory.homologyFunctor
    (ModuleCat.{w} R) i).map α)).symm

private theorem isPseudoCoherentFrom_of_baseChange_vanishing
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (m : ℤ)
    (hvanish : ∀ i : ℤ, m ≤ i →
      Limits.IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)))) :
    PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m :=
  StacksDraft.PseudoCoherence.isPseudoCoherentFrom_of_homology_isZero _ m fun i hi =>
    StacksDraft.PseudoCoherence.isZero_derivedHomology_of_isZero_baseChange f hf K i (hvanish i hi)

private theorem finite_topHomology_of_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (m n : ℤ)
    (hmn : m ≤ n)
    (hK : PseudoCoherence.IsPseudoCoherentFrom
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K)) m)
    (hvanish : ∀ i : ℤ, n < i →
      Limits.IsZero
        ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)))) :
    Module.Finite R
      ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) n).obj
        (DerivedCategory.Q.obj K)) := by
  apply StacksDraft.PseudoCoherence.finite_of_finite_extendScalars f hf
  have hfin : Module.Finite S
      ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) n).obj
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K))) :=
    finite_homology_of_isPseudoCoherentFrom_of_vanishing _ m n hmn hK hvanish
  exact Module.Finite.equiv
    (StacksDraft.PseudoCoherence.derivedHomology_extendScalarsIso f hf.flat K n).toLinearEquiv

private theorem pseudoCoherent_of_pseudoCoherentFrom_descent
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (K : CochainComplex (ModuleCat.{w} R) ℤ)
    (h : ∀ m : ℤ,
      PseudoCoherence.IsPseudoCoherentFrom
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) m →
        PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m)
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj K) :=
  (StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).mpr fun m =>
    h m ((StacksDraft.PseudoCoherence.pseudoCoherent_iff_all _).mp hK m)

private theorem isPseudoCoherentFrom_of_boundedFiniteFree
    {R : Type u} [Ring R] (E : CochainComplex (ModuleCat.{w} R) ℤ)
    (hE : PseudoCoherence.IsBoundedFiniteFree E) (m : ℤ) :
    PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj E) m :=
  ⟨E, hE, 𝟙 _, fun _ _ => inferInstance, inferInstance⟩

private theorem boundedFiniteFree_single
    {R : Type u} [Ring R] (P : ModuleCat.{w} R)
    [Module.Finite R P] [Module.Free R P] (n : ℤ) :
    PseudoCoherence.IsBoundedFiniteFree
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) n).obj P) := by
  refine ⟨⟨n, inferInstance⟩, ⟨n, inferInstance⟩, fun i => ?_⟩
  by_cases hi : i = n
  · subst i
    let e := (HomologicalComplex.singleObjXSelf (.up ℤ) n P).symm.toLinearEquiv
    exact ⟨Module.Finite.equiv e, Module.Free.of_equiv e⟩
  · have := ModuleCat.isZero_iff_subsingleton.mp
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n P i hi)
    exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton _ _⟩

private theorem boundedFiniteFree_extendScalars
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] (f : R →+* S)
    (E : CochainComplex (ModuleCat.{w} R) ℤ) (hE : PseudoCoherence.IsBoundedFiniteFree E) :
    PseudoCoherence.IsBoundedFiniteFree
      (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj E) := by
  let _ := f.toAlgebra
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩, hfin⟩ := hE
  have := ha
  have := hb
  refine ⟨⟨a, inferInstance⟩, ⟨b, inferInstance⟩, fun i => ?_⟩
  have := (hfin i).1
  have := (hfin i).2
  show Module.Finite S (TensorProduct R S (E.X i)) ∧
    Module.Free S (TensorProduct R S (E.X i))
  exact ⟨inferInstance, inferInstance⟩

private theorem exists_finiteFree_epi
    {R : Type u} [Ring R] [Small.{w} R]
    (M : ModuleCat.{w} R) [Module.Finite R M] :
    ∃ (P : ModuleCat.{w} R), Module.Finite R P ∧ Module.Free R P ∧
      ∃ π : P ⟶ M, Epi π := by
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' R M
  have : Small.{w} (Fin n → R) := Module.Finite.small R (Fin n → R)
  let e := Shrink.linearEquiv R (Fin n → R)
  refine ⟨ModuleCat.of R (Shrink.{w} (Fin n → R)), Module.Finite.equiv e.symm,
    Module.Free.of_equiv e.symm, ModuleCat.ofHom (π.comp e.toLinearMap), ?_⟩
  exact (ModuleCat.epi_iff_surjective _).mpr (hπ.comp e.surjective)

private theorem exists_cone_descent_step
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Small.{w} R]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (m n : ℤ) (hmn : m ≤ n)
    (hK : PseudoCoherence.IsPseudoCoherentFrom
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj K)) m)
    (hvanish : ∀ i : ℤ, n < i →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj K)))) :
    ∃ L : CochainComplex (ModuleCat.{w} R) ℤ,
      PseudoCoherence.IsPseudoCoherentFrom
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj L)) m ∧
      (∀ i : ℤ, n ≤ i →
        Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
          (DerivedCategory.Q.obj
            (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj L)))) ∧
      (PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj L) m →
        PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m) := by
  have := finite_topHomology_of_baseChange f hf K m n hmn hK hvanish
  let e : ((DerivedCategory.homologyFunctor (ModuleCat.{w} R) n).obj
      (DerivedCategory.Q.obj K)) ≅ K.homology n :=
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{w} R) n).app K
  have : Module.Finite R (K.homology n) := Module.Finite.equiv e.toLinearEquiv
  obtain ⟨P, hPfin, hPfree, π, hπ⟩ := exists_finiteFree_epi (K.homology n)
  have := hPfin
  have := hPfree
  have := hπ
  have : Module.Projective R P := inferInstance
  have : Projective P := ModuleCat.projective_of_categoryTheory_projective P
  obtain ⟨α, hα⟩ := StacksDraft.PseudoCoherence.exists_single_map_epi_homology K n P π
  have := hα
  let E := (HomologicalComplex.single (ModuleCat.{w} R) (.up ℤ) n).obj P
  have hE : PseudoCoherence.IsBoundedFiniteFree E := boundedFiniteFree_single P n
  let L := CochainComplex.mappingCone α
  let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle α)
  have hT := DerivedCategory.mappingCone_triangle_distinguished α
  let F := ModuleCat.extendScalars.{u, v, w} f
  let : Limits.PreservesFiniteLimits F :=
    StacksDraft.PseudoCoherence.preservesFiniteLimits_extendScalars_of_flat f hf.flat
  let : Limits.PreservesFiniteColimits F :=
    StacksDraft.PseudoCoherence.preservesFiniteColimits_extendScalars f
  let D := F.mapDerivedCategory
  have hDE : PseudoCoherence.IsPseudoCoherentFrom (D.obj (DerivedCategory.Q.obj E)) (m + 1) :=
    _root_.PseudoCoherence.isPseudoCoherentFrom_of_iso
      (isPseudoCoherentFrom_of_boundedFiniteFree _ (boundedFiniteFree_extendScalars f E hE) _)
      (F.mapDerivedCategoryFactors.app E).symm
  have hDK : PseudoCoherence.IsPseudoCoherentFrom (D.obj (DerivedCategory.Q.obj K)) m :=
    _root_.PseudoCoherence.isPseudoCoherentFrom_of_iso hK (F.mapDerivedCategoryFactors.app K).symm
  have hDL : PseudoCoherence.IsPseudoCoherentFrom (D.obj (DerivedCategory.Q.obj L)) m :=
    _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_one m (D.mapTriangle.obj T)
      (D.map_distinguished T hT) hDE hDK
  refine ⟨L, _root_.PseudoCoherence.isPseudoCoherentFrom_of_iso hDL
    (F.mapDerivedCategoryFactors.app L), ?_, ?_⟩
  · intro i hi
    apply StacksDraft.PseudoCoherence.isZero_derivedHomology_baseChange f hf.flat
    exact StacksDraft.PseudoCoherence.isZero_homology_mappingCone_of_single K n P α
      (fun j hj => StacksDraft.PseudoCoherence.isZero_derivedHomology_of_isZero_baseChange
        f hf K j (hvanish j hj)) i hi
  · intro hL
    exact _root_.PseudoCoherence.isPseudoCoherent_of_distinguished_two m T hT
      (isPseudoCoherentFrom_of_boundedFiniteFree E hE m) hL

private theorem isPseudoCoherentFrom_of_baseChange_of_bound
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Small.{w} R]
    (f : R →+* S) (hf : f.FaithfullyFlat) (m : ℤ) (d : ℕ)
    (K : CochainComplex (ModuleCat.{w} R) ℤ)
    (hK : PseudoCoherence.IsPseudoCoherentFrom
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj K)) m)
    (hvanish : ∀ i : ℤ, m + (d : ℤ) ≤ i →
      Limits.IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max v w} S) i).obj
        (DerivedCategory.Q.obj
          (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj K)))) :
    PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m := by
  induction d generalizing K with
  | zero =>
    exact isPseudoCoherentFrom_of_baseChange_vanishing f hf K m
      (fun i hi => hvanish i (by simpa using hi))
  | succ d ih =>
    obtain ⟨L, hL, hvanishL, hKL⟩ := exists_cone_descent_step f hf K m (m + d)
      (by omega) hK (fun i hi => hvanish i (by omega))
    exact hKL (ih L hL hvanishL)

private theorem isPseudoCoherentFrom_of_faithfullyFlat_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Small.{w} R]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{w} R) ℤ) (m : ℤ)
    (hK : PseudoCoherence.IsPseudoCoherentFrom
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex (.up ℤ)).obj K)) m) :
    PseudoCoherence.IsPseudoCoherentFrom (DerivedCategory.Q.obj K) m := by
  obtain ⟨b, hb⟩ := isPseudoCoherentFrom_boundedAboveHomology hK
  apply isPseudoCoherentFrom_of_baseChange_of_bound f hf m (b - m + 1).toNat K hK
  intro i hi
  apply hb i
  omega

/-! ### Descent of perfectness along a faithfully flat ring map -/

/-- **The bottom cokernel is flat after faithfully flat descent.** Let `F` be a complex of flat
`R`-modules vanishing strictly above `b`, and suppose that `F ⊗_R S` has a flat representative
supported in `[a, b]`. Then the cokernel of `F^{a-1} → F^a` is a flat `R`-module.

The base change of that cokernel is flat over `S` by `flat_extendScalars_cokernel`, and faithful
flatness descends flatness. -/
private lemma flat_cokernel_of_faithfullyFlat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (F : CochainComplex (ModuleCat.{w} R) ℤ) (a b : ℤ) (hFLE : F.IsStrictlyLE b)
    (hFflat : ∀ i : ℤ, Module.Flat R (F.X i))
    (hamp : HasFlatRepresentative
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)) a b) :
    Module.Flat R (cokernel (F.d (a - 1) a) : ModuleCat.{w} R) := by
  algebraize [f]
  have : Module.Flat S
      (TensorProduct R S ((cokernel (F.d (a - 1) a) : ModuleCat.{w} R) : Type w)) :=
    flat_extendScalars_cokernel f hf.flat F a b b hFLE hFflat hamp
  exact Module.Flat.of_flat_tensorProduct R
    ((cokernel (F.d (a - 1) a) : ModuleCat.{w} R) : Type w) S

/-- Let `R → S` be a faithfully flat map of commutative rings and let `K` be a complex of
`R`-modules. If `K ⊗_R S` is perfect, then `K` is perfect. -/
@[stacks 068T]
theorem isPerfect_of_faithfullyFlat_baseChange
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.FaithfullyFlat)
    (K : CochainComplex (ModuleCat.{max u v w} R) ℤ)
    (hK : IsPerfect
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, max u v w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))) :
    IsPerfect (DerivedCategory.Q.obj K) := by
  have hsmall : Small.{max u v w} R := small_max.{max v w} R
  obtain ⟨hPseudoS, a, b, hFlatS⟩ :=
    (isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{v, max u w} _).1.mp hK
  have hpseudo : StacksDraft.PseudoCoherence.IsPseudoCoherent (DerivedCategory.Q.obj K) :=
    pseudoCoherent_of_pseudoCoherentFrom_descent f K
      (isPseudoCoherentFrom_of_faithfullyFlat_baseChange f hf K) hPseudoS
  have hvan : ∀ j : ℤ, (j < a ∨ b < j) →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v w} R) j).obj
        (DerivedCategory.Q.obj K)) := fun j hj =>
    StacksDraft.PseudoCoherence.isZero_derivedHomology_of_isZero_baseChange f hf K j
      (homology_isZero_of_hasFlatRepresentative _ a b j hFlatS hj)
  obtain ⟨F, α, hFfree, hFLE, hα⟩ :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective.{u,
      max v w} (DerivedCategory.Q.obj K) b).2.2 hpseudo fun j hj => hvan j (Or.inr hj)
  have hFflat : ∀ i : ℤ, Module.Flat R (F.X i) := by
    intro i
    have : Module.Free R (F.X i) := (hFfree i).2
    infer_instance
  have hampF : HasFlatRepresentative.{v, max u w}
      (DerivedCategory.Q.obj
        (((ModuleCat.extendScalars.{u, v, max u v w} f).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj F)) a b := by
    let G := ModuleCat.extendScalars.{u, v, max u v w} f
    have : Limits.PreservesFiniteLimits G :=
      StacksDraft.PseudoCoherence.preservesFiniteLimits_extendScalars_of_flat f hf.flat
    have : Limits.PreservesFiniteColimits G :=
      StacksDraft.PseudoCoherence.preservesFiniteColimits_extendScalars f
    exact hasFlatRepresentative_of_iso
      ((G.mapDerivedCategoryFactors.app K).symm ≪≫
        G.mapDerivedCategory.mapIso (asIso α).symm ≪≫ G.mapDerivedCategoryFactors.app F) hFlatS
  exact (isPerfect_iff_pseudoCoherent_and_finiteTorDimension.{u, max v w}
      (DerivedCategory.Q.obj K)).1.mpr
    ⟨hpseudo, a, b, hasFlatRepresentative_truncGE.{u, max v w} _ a b F α hα hFLE hFflat
      (fun j hj => hvan j (Or.inl hj))
      (flat_cokernel_of_faithfullyFlat f hf F a b hFLE hFflat hampF)⟩

end FaithfullyFlat


/-! ### The fibrewise criterion for perfectness in a Tor window -/

section Fibre

/-- If every maximal ideal misses an element of `s`, then finitely many elements of `s` generate
the unit ideal. -/
private lemma exists_finite_span_eq_top {R : Type u} [CommRing R] (s : Set R)
    (h : ∀ m : Ideal R, m.IsMaximal → ∃ g ∈ s, g ∉ m) :
    ∃ t : Finset R, (t : Set R) ⊆ s ∧ Ideal.span (Set.range ((↑) : {x // x ∈ t} → R)) = ⊤ := by
  have hspan : Ideal.span s = ⊤ := by
    by_contra hne
    obtain ⟨m, hmMax, hm⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨g, hg, hgm⟩ := h m hmMax
    exact hgm (hm (Ideal.subset_span hg))
  obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite s).mp hspan
  refine ⟨t, hts, ?_⟩
  rw [← ht]
  exact congrArg Ideal.span (by ext x; simp)

/-- Two K-projective representatives of the same object of `D(R)` are homotopy equivalent. -/
private lemma nonempty_homotopyEquiv_of_derived_iso {R : Type u} [CommRing R]
    (M N : CochainComplex (ModuleCat.{max u v} R) ℤ) [M.IsKProjective] [N.IsKProjective]
    (e : DerivedCategory.Q.obj M ≅ DerivedCategory.Q.obj N) : Nonempty (HomotopyEquiv M N) := by
  let E : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj M) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj N) :=
    (DerivedCategory.quotientCompQhIso _).app M ≪≫ e ≪≫
      ((DerivedCategory.quotientCompQhIso _).app N).symm
  obtain ⟨g, hg⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective M
      ((HomotopyCategory.quotient _ _).obj N)).surjective E.hom
  obtain ⟨g', hg'⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective N
      ((HomotopyCategory.quotient _ _).obj M)).surjective E.inv
  have hgg' : g ≫ g' = 𝟙 _ :=
    (CochainComplex.IsKProjective.Qh_map_bijective M
      ((HomotopyCategory.quotient _ _).obj M)).injective (by
        rw [Functor.map_comp, hg, hg', E.hom_inv_id]
        simp)
  have hg'g : g' ≫ g = 𝟙 _ :=
    (CochainComplex.IsKProjective.Qh_map_bijective N
      ((HomotopyCategory.quotient _ _).obj N)).injective (by
        rw [Functor.map_comp, hg', hg, E.inv_hom_id]
        simp)
  exact ⟨HomotopyCategory.homotopyEquivOfIso
    { hom := g, inv := g', hom_inv_id := hgg', inv_hom_id := hg'g }⟩

/-- **The fibrewise vanishing of a perfect complex of Tor amplitude in `[a, b]`.** If the
pseudo-coherent object `K` has a flat representative supported in `[a, b]` then for every prime
`p` the cohomology of the derived fibre `K ⊗_R^L κ(p)` vanishes outside `[a, b]`.

Pseudo-coherence supplies a bounded above finite free representative `F` and [stacks 0658] a
finite projective representative `E` concentrated in `[a, b]`. Both are K-projective, hence
homotopy equivalent, and extension of scalars to `κ(p)` preserves homotopy equivalences; the fibre
of `E` visibly vanishes outside `[a, b]`. -/
private lemma fibreCohomologyVanishes_of_hasFlatRepresentative {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (a b i : ℤ)
    (hamp : HasFlatRepresentative K a b) (hi : i < a ∨ b < i) :
    FibreCohomologyVanishes.{u, v} p K i := by
  obtain ⟨F, α, hFfree, hFLE, hα⟩ :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
      K b).2.2 hK fun j hj =>
      homology_isZero_of_hasFlatRepresentative K a b j hamp (Or.inr hj)
  obtain ⟨E, hEfp, hEGE, hELE, ⟨eE⟩⟩ :=
    (isPerfect_iff_pseudoCoherent_and_finiteTorDimension K).2 a b hK hamp
  have := hα
  refine ⟨F, ⟨⟨b, hFLE⟩, hFfree⟩, ⟨asIso α⟩, ?_⟩
  have : F.IsStrictlyLE b := hFLE
  have : E.IsStrictlyLE b := hELE
  have (j : ℤ) : Projective (F.X j) := by
    have : Module.Free R (F.X j) := (hFfree j).2
    have : Module.Projective R (F.X j) := inferInstance
    exact ModuleCat.projective_of_categoryTheory_projective (F.X j)
  have (j : ℤ) : Projective (E.X j) := by
    have : Module.Projective R (E.X j) := (hEfp j).2
    exact ModuleCat.projective_of_categoryTheory_projective (E.X j)
  have : F.IsKProjective := CochainComplex.isKProjective_of_projective F b
  have : E.IsKProjective := CochainComplex.isKProjective_of_projective E b
  obtain ⟨he⟩ := nonempty_homotopyEquiv_of_derived_iso F E (asIso α ≪≫ eE)
  let G := ModuleCat.extendScalars.{u, u, max v u} (algebraMap R p.ResidueField)
  have : G.Additive := extendScalars_additive.{u, u, max v u} _
  have hzE : IsZero ((residueFieldComplex.{u, v} p E).homology i) := by
    refine ShortComplex.isZero_homology_of_isZero_X₂ _ (G.map_isZero ?_)
    rcases hi with hi | hi
    · exact CochainComplex.isZero_of_isStrictlyGE E a i hi
    · exact CochainComplex.isZero_of_isStrictlyLE E b i hi
  exact hzE.of_iso ((G.mapHomotopyEquiv he).toHomologyIso i)

/-- From vanishing of one cohomology module of the fibre at a prime `p`, the corresponding
cohomology module of `K` dies after localizing at some element outside `p`. This is [stacks 068U]
read through the vanishing of the cohomology of both summands of the resulting decomposition. -/
private lemma exists_away_homology_isZero_of_fibre {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (hi : FibreCohomologyVanishes.{u, v} p K i) :
    ∃ g : R, g ∉ p ∧ IsZero ((DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} (Localization.Away g)) i).obj
        ((PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K)) := by
  obtain ⟨g, hg, hrest⟩ := exists_localization_iso_biprod_truncGE_truncLE p K hK i hi
  dsimp only at hrest
  obtain ⟨-, -, e, -⟩ := hrest
  refine ⟨g, hg, ?_⟩
  set Kf := (PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K with hKf
  set upper := (DerivedCategory.TStructure.t.truncGE (i + 1)).obj Kf with hupper
  set lower := (DerivedCategory.TStructure.t.truncLE (i - 1)).obj Kf with hlower
  set H := DerivedCategory.homologyFunctor
    (ModuleCat.{max u v} (Localization.Away g)) i with hHdef
  have hzUpper : IsZero (H.obj upper) := DerivedCategory.isZero_of_isGE upper (i + 1) i (by omega)
  have hzLower : IsZero (H.obj lower) := DerivedCategory.isZero_of_isLE lower (i - 1) i (by omega)
  have hzSum : IsZero (H.obj (upper ⊞ lower)) := by
    let c := H.biprodComparison upper lower
    let c' := H.biprodComparison' upper lower
    have : IsSplitMono c := IsSplitMono.mk' ⟨c', by
      dsimp [c, c', Functor.biprodComparison, Functor.biprodComparison']
      rw [biprod.lift_desc, ← H.map_comp, ← H.map_comp, ← H.map_add]
      simp⟩
    rw [IsZero.iff_id_eq_zero, ← cancel_mono c]
    refine biprod.hom_ext _ _ (hzUpper.eq_of_tgt _ _) (hzLower.eq_of_tgt _ _)
  exact hzSum.of_iso (H.mapIso e)

/-- **Cohomology vanishes where all the fibres at maximal ideals vanish.** A cohomology module of
a pseudo-coherent object whose fibre cohomology dies in degree `i` at every maximal ideal is
itself zero: it dies after localizing at an element outside each maximal ideal, so its support is
empty. -/
private lemma homology_isZero_of_maximal_fibres {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ)
    (h : ∀ m : MaximalSpectrum R, FibreCohomologyVanishes.{u, v} m.asIdeal K i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K) := by
  set H := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K with hH
  rw [ModuleCat.isZero_iff_subsingleton]
  refine Module.subsingleton_of_localization_maximal
    (fun q : Ideal R => LocalizedModule q.primeCompl ((H : Type (max u v))))
    (fun q : Ideal R => LocalizedModule.mkLinearMap q.primeCompl ((H : Type (max u v)))) ?_
  intro q hq
  obtain ⟨g, hg, hz⟩ := exists_away_homology_isZero_of_fibre q K hK i (h ⟨q, hq⟩)
  have hAway : Subsingleton (LocalizedModule.Away g ((H : Type (max u v)))) :=
    ModuleCat.isZero_iff_subsingleton.mp
      (hz.of_iso (PseudoCoherence.localizationAwayHomologyIso g K i).symm)
  have : q.IsPrime := hq.isPrime
  refine (Module.notMem_support_iff (p := (⟨q, this⟩ : PrimeSpectrum R))).mp ?_
  intro hqSupport
  exact hg ((PrimeSpectrum.mem_zeroLocus _ {g}).mp
    (LocalizedModule.subsingleton_iff_support_subset.mp hAway hqSupport) rfl)

/-- **Local perfectness in a Tor window from the fibre at a prime.** If the cohomology of `K`
vanishes below `a` and the degree-`a - 1` fibre cohomology at `p` vanishes, then there is an
element outside `p` over which `K` acquires a flat representative supported in degrees `≥ a`.

[stacks 068U] applied in degree `a - 1` makes the upper truncation `τ_{≥ a}` of the localization
perfect; the localization is itself in degrees `≥ a`, so the truncation map is an isomorphism. -/
private lemma exists_away_hasFlatRepresentative {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (a : ℤ)
    (hlow : ∀ j : ℤ, j < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) j).obj K))
    (hfib : FibreCohomologyVanishes.{u, v} p K (a - 1)) :
    ∃ g : R, g ∉ p ∧ ∃ c : ℤ, HasFlatRepresentative
      ((PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K) a c := by
  obtain ⟨g, hg, hrest⟩ :=
    exists_localization_iso_biprod_truncGE_truncLE p K hK (a - 1) hfib
  dsimp only at hrest
  obtain ⟨-, ⟨P, c, hPGE, hPLE, hPfin, hPproj, ⟨eU⟩, -⟩, -⟩ := hrest
  refine ⟨g, hg, c, ?_⟩
  have hKfGE : ((PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K).IsGE (a - 1 + 1) := by
    rw [DerivedCategory.isGE_iff]
    intro j hj
    exact PseudoCoherence.localizationAway_homology_isZero g K j (hlow j (by omega))
  set π := (DerivedCategory.TStructure.t.truncGEπ (a - 1 + 1)).app
    ((PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K) with hπ
  have hiso : IsIso π :=
    (DerivedCategory.TStructure.t.isGE_iff_isIso_truncGEπ_app (a - 1 + 1) _).mp hKfGE
  have hPGE' : P.IsStrictlyGE a := by rwa [sub_add_cancel] at hPGE
  refine ⟨P, fun j => ?_, hPGE', hPLE, ⟨asIso π ≪≫ eU⟩⟩
  have : Module.Projective (Localization.Away g) (P.X j) := hPproj j
  infer_instance

/-- Let `R` be a commutative ring, let `a, b : ℤ` and let `K` be a pseudo-coherent object of the
derived category of `R`-modules. Then `K` is perfect of Tor amplitude in `[a, b]` if and only if
the cohomology of the derived fibre `K ⊗_R^L κ(p)` vanishes outside `[a, b]` for every prime ideal
`p`, and it is enough to test this at the maximal ideals.

Tor amplitude in `[a, b]` is expressed, as in [stacks 0658], by the existence of a flat
representative supported in `[a, b]`; by [stacks 0654] this is exactly Tor amplitude in `[a, b]`,
and the third clause spells that out: every bounded above flat representative of `K` — which is
what computes `K ⊗_R^L M` — has vanishing cohomology outside `[a, b]` after tensoring with an
arbitrary module. -/
@[stacks 068V]
theorem isPerfect_and_torAmplitude_iff_fibreCohomologyVanishes {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (a b : ℤ) :
    let perfectWithTorAmplitude :=
      IsPerfect K ∧ HasFlatRepresentative K a b ∧
        ∀ E : CochainComplex (ModuleCat.{max u v} R) ℤ, TorAmplitude.BoundedAbove E →
          TorAmplitude.IsComplexOfFlats E → Nonempty (K ≅ DerivedCategory.Q.obj E) →
            TorAmplitude.HasTorAmplitudeIn E a b
    let primeVanishes := ∀ q : PrimeSpectrum R, ∀ i : ℤ, i < a ∨ b < i →
      FibreCohomologyVanishes.{u, v} q.asIdeal K i
    let maximalVanishes := ∀ m : MaximalSpectrum R, ∀ i : ℤ, i < a ∨ b < i →
      FibreCohomologyVanishes.{u, v} m.asIdeal K i
    (perfectWithTorAmplitude ↔ primeVanishes) ∧ (primeVanishes ↔ maximalVanishes) := by
  classical
  intro perfectWithTorAmplitude primeVanishes maximalVanishes
  have hsmall : Small.{max u v} R := small_max R
  have hforward : HasFlatRepresentative K a b → primeVanishes := by
    intro hamp q i hi
    exact fibreCohomologyVanishes_of_hasFlatRepresentative q.asIdeal K hK a b i hamp hi
  have hbackward : maximalVanishes → perfectWithTorAmplitude := by
    intro h
    have hvan : ∀ j : ℤ, (j < a ∨ b < j) →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) j).obj K) := fun j hj =>
      homology_isZero_of_maximal_fibres K hK j fun m => h m j hj
    set s : Set R := {g : R | ∃ c : ℤ, HasFlatRepresentative
      ((PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K) a c} with hs
    obtain ⟨t, hts, htspan⟩ := exists_finite_span_eq_top s fun m hm => by
      obtain ⟨g, hg, hloc⟩ := exists_away_hasFlatRepresentative m K hK a
        (fun j hj => hvan j (Or.inl hj)) (h ⟨m, hm⟩ (a - 1) (Or.inl (by omega)))
      exact ⟨g, hloc, hg⟩
    have hamp : HasFlatRepresentative K a b :=
      hasFlatRepresentative_of_localizationSpan (ι := {x // x ∈ t}) (↑) htspan K a b hK hvan
        fun i => hts i.2
    refine ⟨(isPerfect_iff_pseudoCoherent_and_finiteTorDimension K).1.mpr ⟨hK, a, b, hamp⟩,
      hamp, ?_⟩
    rintro E hEbounded hEflat ⟨eE⟩
    obtain ⟨A, hAflat, hAGE, hALE, ⟨eA⟩⟩ := hamp
    exact TorAmplitude.termwise_torAmplitude_of_flat_representative E A a b hEbounded hEflat
      hAflat hAGE hALE (eE.symm ≪≫ eA)
  refine ⟨⟨fun hp => hforward hp.2.1, fun hp => hbackward fun m i hi => hp m.toPrimeSpectrum i hi⟩,
    ⟨fun hp m i hi => hp m.toPrimeSpectrum i hi, fun hm => hforward (hbackward hm).2.1⟩⟩

end Fibre


/-! ### Perfectness from the stalks and the fibres -/

section Stalks

/-- Perfectness is invariant under isomorphism in the derived category. -/
private lemma isPerfect_of_iso' {R : Type u} [CommRing R]
    {K L : DerivedCategory (ModuleCat.{max u v} R)} (hK : IsPerfect K) (e : K ≅ L) :
    IsPerfect L := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨i⟩⟩ := hK
  exact ⟨P, a, b, ha, hb, hf, hp, ⟨e.symm ≪≫ i⟩⟩

/-- A perfect object has vanishing cohomology in all sufficiently low degrees. -/
private lemma homology_isZero_below_of_isPerfect {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (hK : IsPerfect K) :
    ∃ a : ℤ, ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj K) := by
  obtain ⟨P, a, b, ha, hb, hf, hp, ⟨e⟩⟩ := hK
  refine ⟨a, fun i hi => ?_⟩
  have hPi : IsZero (P.X i) := P.isZero_of_isStrictlyGE a i hi
  exact (((DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) i).app P).isZero_iff.mpr
    (ShortComplex.isZero_homology_of_isZero_X₂ (P.sc i) hPi)).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).mapIso e)

open CochainComplex.DerivedExtensionScalars in
/-- Derived extension of scalars along `R → R_f` is derived localization away from `f`: both are
total left derived functors of the same termwise construction. -/
private noncomputable def totalDerivedAwayIso {R : Type u} [CommRing R] (g : R) :
    (totalDerivedExtensionScalars.{u, u, v} (algebraMap R (Localization.Away g))).functor ≅
      PseudoCoherence.localizationAwayFunctorAux.{u, v} g := by
  let F := ModuleCat.extendScalars.{u, u, max v u} (algebraMap R (Localization.Away g))
  have : F.Additive := extendScalars_additive.{u, u, max v u} _
  have : PreservesFiniteLimits F :=
    extendScalars_preservesFiniteLimits_of_flat'.{u, v} _
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (Localization.Away g) (Submonoid.powers g)))
  have : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u}
      (algebraMap R (Localization.Away g))).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  let D := totalDerivedExtensionScalars.{u, u, v} (algebraMap R (Localization.Away g))
  change D.functor ≅ F.mapDerivedCategory
  have hmap : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactors
  exact @Functor.leftDerivedUnique _ _ _ _ _ _
    F.mapDerivedCategory D.functor _ _ D.comparison F.mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (ModuleCat.{max v u} R) (ComplexShape.up ℤ))
    inferInstance D.isLeftDerived hmap

open CochainComplex.DerivedExtensionScalars in
/-- Perfectness of the derived base change to `R_f` is perfectness of the derived localization
away from `f`. -/
private lemma isPerfect_localizationAway_of_total {R : Type u} [CommRing R] (g : R)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (h : IsPerfect ((totalDerivedExtensionScalars.{u, u, v}
      (algebraMap R (Localization.Away g))).functor.obj K)) :
    IsPerfect ((PseudoCoherence.localizationAwayFunctorAux.{u, v} g).obj K) :=
  isPerfect_of_iso' h ((totalDerivedAwayIso.{u, v} g).app K)

open CochainComplex.DerivedExtensionScalars in
/-- Along a flat ring map, derived extension of scalars commutes with the cohomology functors. -/
private noncomputable def totalDerivedCompHomologyIso_of_flat {R A : Type u} [CommRing R]
    [CommRing A] (f : R →+* A) (hf : f.Flat) (n : ℤ) :
    (totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n ≅
      DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n ⋙ ModuleCat.extendScalars f := by
  let F := ModuleCat.extendScalars.{u, u, max u v} f
  have : F.Additive := extendScalars_additive.{u, u, max v u} f
  have : PreservesFiniteLimits F := extendScalars_preservesFiniteLimits_of_flat'.{u, v} f hf
  have : PreservesColimitsOfSize.{0, 0} F :=
    (ModuleCat.extendRestrictScalarsAdj.{v, u, u} f).leftAdjoint_preservesColimits
  have : PreservesFiniteColimits F := PreservesColimitsOfSize.preservesFiniteColimits F
  let D := totalDerivedExtensionScalars.{u, u, v} f
  have hmap : F.mapDerivedCategory.IsLeftDerivedFunctor F.mapDerivedCategoryFactors.hom
      (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts _ _ F.mapDerivedCategoryFactors
  let eD : D.functor ≅ F.mapDerivedCategory := @Functor.leftDerivedUnique _ _ _ _ _ _
    F.mapDerivedCategory D.functor _ _ D.comparison F.mapDerivedCategoryFactors.hom
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ))
    inferInstance D.isLeftDerived hmap
  exact Functor.isoWhiskerRight eD
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n) ≪≫
    PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso F n

open CochainComplex.DerivedExtensionScalars in
/-- Derived extension of scalars preserves pseudo-coherence: a bounded above finite free
representative stays one. -/
private lemma pseudoCoherent_totalDerived {R A : Type u} [CommRing R] [CommRing A] (f : R →+* A)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    StacksDraft.PseudoCoherence.IsPseudoCoherent
      ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj K) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hP.upperBound
  let _ : Algebra R A := f.toAlgebra
  let F := ModuleCat.extendScalars.{u, u, max u v} f
  let PA := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  let D := totalDerivedExtensionScalars.{u, u, v} f
  have (i : ℤ) : Module.Free R (P.X i) := (hP.finiteFree i).2
  have (i : ℤ) : Module.Projective R (P.X i) := inferInstance
  have : ∀ i, Projective (P.X i) := fun i => ModuleCat.projective_of_categoryTheory_projective _
  have hPle : P.IsStrictlyLE b := hb
  have hc : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P b
  refine ⟨PA, ?_, ⟨(@asIso _ _ _ _ (D.comparison.app P) hc).symm ≪≫ D.functor.mapIso e⟩⟩
  refine ⟨⟨b, by dsimp only [PA]; infer_instance⟩, fun i => ⟨?_, ?_⟩⟩
  · show Module.Finite A (TensorProduct R A (P.X i))
    have : Module.Finite R (P.X i) := (hP.finiteFree i).1
    infer_instance
  · show Module.Free A (TensorProduct R A (P.X i))
    infer_instance

open CochainComplex.DerivedExtensionScalars in
/-- Base change along a composite agrees with the two successive base changes, on a
pseudo-coherent object. -/
private lemma totalDerived_comp_obj_of_pseudoCoherent {R A B : Type u} [CommRing R] [CommRing A]
    [CommRing B] (f : R →+* A) (g : A →+* B)
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    Nonempty ((totalDerivedExtensionScalars.{u, u, v} g).functor.obj
        ((totalDerivedExtensionScalars.{u, u, v} f).functor.obj K) ≅
      (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor.obj K) := by
  obtain ⟨P, ⟨b, hb⟩, hP, ⟨e⟩⟩ :=
    (StacksDraft.PseudoCoherence.pseudoCoherent_iff_pseudoCoherentFrom_all_iff_finiteProjective
      K 0).2.1.mp hK
  let F := ModuleCat.extendScalars.{u, u, max u v} f
  let PA : CochainComplex (ModuleCat.{max u v} A) ℤ :=
    (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P
  have hPle : P.IsStrictlyLE b := hb
  have (i : ℤ) : Module.Projective R (P.X i) := (hP i).2
  have : ∀ i, Projective (P.X i) := fun i => ModuleCat.projective_of_categoryTheory_projective _
  have hPAle : PA.IsStrictlyLE b := by dsimp only [PA]; infer_instance
  let _ : Algebra R A := f.toAlgebra
  have : ∀ i, Projective (PA.X i) := fun i => by
    have hproj : Module.Projective A ((PA.X i : Type (max u v))) := by
      show Module.Projective A (TensorProduct R A (P.X i))
      infer_instance
    exact ModuleCat.projective_of_categoryTheory_projective (PA.X i)
  let Df := totalDerivedExtensionScalars.{u, u, v} f
  let Dg := totalDerivedExtensionScalars.{u, u, v} g
  let Dgf := totalDerivedExtensionScalars.{u, u, v} (g.comp f)
  have hf : IsIso (Df.comparison.app P) := Df.comparison_isIso_of_projective P b
  have hg : IsIso (Dg.comparison.app PA) := Dg.comparison_isIso_of_projective PA b
  have hgf : IsIso (Dgf.comparison.app P) := Dgf.comparison_isIso_of_projective P b
  exact ⟨Dg.functor.mapIso
      (Df.functor.mapIso e.symm ≪≫ @asIso _ _ _ _ (Df.comparison.app P) hf) ≪≫
    @asIso _ _ _ _ (Dg.comparison.app PA) hg ≪≫
    (Functor.isoWhiskerRight
      (NatIso.mapHomologicalComplex (ModuleCat.extendScalarsComp f g) (ComplexShape.up ℤ))
      DerivedCategory.Q).symm.app P ≪≫
    (@asIso _ _ _ _ (Dgf.comparison.app P) hgf).symm ≪≫ (Dgf.functor.mapIso e.symm).symm⟩

open CochainComplex.DerivedExtensionScalars in
/-- **The two readings of fibre-cohomology vanishing agree.** For a pseudo-coherent object `K` of
`D(R)` and a prime `p`, the predicate `Perfect.FibreCohomologyVanishes p K i` of
`Perfect.FibreCriterion` — which asserts the vanishing of `Hⁱ` of the termwise base change to
`κ(p)` of some bounded above finite free representative — holds exactly when `Hⁱ(K ⊗_R^L κ(p))`
vanishes for the canonical derived base change of [stacks 064H].

A bounded above complex of finite free modules is a complex of projectives, so the comparison of
the derived base-change datum is invertible on it and it computes `K ⊗_R^L κ(p)`; conversely any
two such representatives are K-projective, hence homotopy equivalent, and an additive functor
preserves homotopy equivalences, so the predicate does not depend on the chosen representative. -/
theorem fibreCohomologyVanishes_iff_isZero_homology {R : Type u} [CommRing R]
    (p : Ideal R) [p.IsPrime] (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (i : ℤ) :
    FibreCohomologyVanishes.{u, v} p K i ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} p.ResidueField) i).obj
        ((totalDerivedExtensionScalars.{u, u, v}
          (algebraMap R p.ResidueField)).functor.obj K)) := by
  obtain ⟨P, hP, ⟨e⟩⟩ := hK
  obtain ⟨b, hb⟩ := hP.upperBound
  let D := totalDerivedExtensionScalars.{u, u, v} (algebraMap R p.ResidueField)
  have hPle : P.IsStrictlyLE b := hb
  have (j : ℤ) : Module.Free R (P.X j) := (hP.finiteFree j).2
  have (j : ℤ) : Module.Projective R (P.X j) := inferInstance
  have : ∀ j, Projective (P.X j) := fun j => ModuleCat.projective_of_categoryTheory_projective _
  have hc : IsIso (D.comparison.app P) := D.comparison_isIso_of_projective P b
  have key : IsZero ((residueFieldComplex.{u, v} p P).homology i) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} p.ResidueField) i).obj
        (D.functor.obj K)) := by
    refine Iso.isZero_iff ?_
    exact ((DerivedCategory.homologyFunctorFactors
        (ModuleCat.{max u v} p.ResidueField) i).app (residueFieldComplex.{u, v} p P)).symm ≪≫
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} p.ResidueField) i).mapIso
        ((@asIso _ _ _ _ (D.comparison.app P) hc).symm ≪≫ D.functor.mapIso e)
  refine ⟨fun h => key.mp ?_, fun h => ⟨P, hP, ⟨e⟩, key.mpr h⟩⟩
  obtain ⟨Q, hQ, ⟨eQ⟩, hzQ⟩ := h
  obtain ⟨c, hc'⟩ := hQ.upperBound
  have hQle : Q.IsStrictlyLE c := hc'
  have (j : ℤ) : Module.Free R (Q.X j) := (hQ.finiteFree j).2
  have (j : ℤ) : Module.Projective R (Q.X j) := inferInstance
  have : ∀ j, Projective (Q.X j) := fun j => ModuleCat.projective_of_categoryTheory_projective _
  have : Q.IsKProjective := CochainComplex.isKProjective_of_projective Q c
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P b
  obtain ⟨he⟩ := nonempty_homotopyEquiv_of_derived_iso Q P (eQ ≪≫ e.symm)
  let G := ModuleCat.extendScalars.{u, u, max v u} (algebraMap R p.ResidueField)
  have : G.Additive := extendScalars_additive.{u, u, max v u} _
  exact hzQ.of_iso ((G.mapHomotopyEquiv he).toHomologyIso i).symm

open CochainComplex.DerivedExtensionScalars in
/-- If the stalk of `K` at `p` is perfect then the cohomology of the fibre at `p` vanishes in all
sufficiently low degrees: the fibre is the derived base change of the stalk along the residue
map, and a perfect object is bounded below. -/
private theorem fibre_vanishes_below_of_perfect_at_prime {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (q : PrimeSpectrum R)
    (h : IsPerfect ((totalDerivedExtensionScalars.{u, u, v}
      (algebraMap R (Localization.AtPrime q.asIdeal))).functor.obj K)) :
    ∃ a : ℤ, ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v} q.asIdeal.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, v}
            (algebraMap R q.asIdeal.ResidueField)).functor.obj K)) := by
  have hbase := isPerfect_derivedExtensionScalars.{u, u, v}
    (IsLocalRing.residue (Localization.AtPrime q.asIdeal)) _ h
  obtain ⟨a, ha⟩ := homology_isZero_below_of_isPerfect _ hbase
  obtain ⟨e⟩ := totalDerived_comp_obj_of_pseudoCoherent
    (algebraMap R (Localization.AtPrime q.asIdeal))
    (IsLocalRing.residue (Localization.AtPrime q.asIdeal)) K hK
  refine ⟨a, fun i hi => (ha i hi).of_iso ?_⟩
  exact (DerivedCategory.homologyFunctor
    (ModuleCat.{max u v} q.asIdeal.ResidueField) i).mapIso e.symm

open CochainComplex.DerivedExtensionScalars in
/-- Conversely, vanishing of the fibre cohomology at `p` in all sufficiently low degrees makes the
stalk at `p` perfect. Over the local ring `R_p` the single fibre condition and [stacks 0BYP] make
the stalk perfect on a principal neighbourhood of the maximal ideal, which is all of
`Spec R_p`. -/
private theorem perfect_at_prime_of_fibre_vanishes_below {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (q : PrimeSpectrum R)
    (h : ∃ a : ℤ, ∀ i : ℤ, i < a →
      IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v} q.asIdeal.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, v}
            (algebraMap R q.asIdeal.ResidueField)).functor.obj K))) :
    IsPerfect ((totalDerivedExtensionScalars.{u, u, v}
      (algebraMap R (Localization.AtPrime q.asIdeal))).functor.obj K) := by
  classical
  set Rp := Localization.AtPrime q.asIdeal with hRp
  set Kp := (totalDerivedExtensionScalars.{u, u, v} (algebraMap R Rp)).functor.obj K with hKp
  have hKpc : StacksDraft.PseudoCoherence.IsPseudoCoherent Kp :=
    pseudoCoherent_totalDerived (algebraMap R Rp) K hK
  obtain ⟨a, ha⟩ := h
  have hlocal : ∀ m : MaximalSpectrum Rp, ∀ i : ℤ, i < a →
      FibreCohomologyVanishes.{u, v} m.asIdeal Kp i := by
    intro m i hi
    have hmprime : m.asIdeal.IsPrime := m.isMaximal.isPrime
    have hpq : q.asIdeal = m.asIdeal.comap (algebraMap R Rp) := by
      rw [IsLocalRing.eq_maximalIdeal m.isMaximal]
      simpa [Rp] using (Localization.AtPrime.under_maximalIdeal (I := q.asIdeal)).symm
    let l : q.asIdeal.ResidueField →+* m.asIdeal.ResidueField :=
      Ideal.ResidueField.map q.asIdeal m.asIdeal (algebraMap R Rp) hpq
    let g : Rp →+* m.asIdeal.ResidueField := algebraMap Rp m.asIdeal.ResidueField
    have hcomp : l.comp (algebraMap R q.asIdeal.ResidueField) = g.comp (algebraMap R Rp) := by
      ext x
      simp [l, g, Ideal.ResidueField.map_algebraMap]
    have hl : l.Flat := by
      rw [RingHom.Flat]
      let _ := l.toAlgebra
      infer_instance
    obtain ⟨e1⟩ := totalDerived_comp_obj_of_pseudoCoherent (algebraMap R Rp) g K hK
    obtain ⟨e2⟩ := totalDerived_comp_obj_of_pseudoCoherent
      (algebraMap R q.asIdeal.ResidueField) l K hK
    rw [hcomp] at e2
    set Kk := (totalDerivedExtensionScalars.{u, u, v}
      (algebraMap R q.asIdeal.ResidueField)).functor.obj K with hKk
    let F := ModuleCat.extendScalars.{u, u, max u v} l
    have hzF : IsZero (F.obj ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v} q.asIdeal.ResidueField) i).obj Kk)) := F.map_isZero (ha i hi)
    have hz : IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{max u v} m.asIdeal.ResidueField) i).obj
          ((totalDerivedExtensionScalars.{u, u, v} l).functor.obj Kk)) :=
      ((totalDerivedCompHomologyIso_of_flat l hl i).app Kk).isZero_iff.mpr hzF
    refine (fibreCohomologyVanishes_iff_isZero_homology m.asIdeal Kp hKpc i).mpr ?_
    exact hz.of_iso ((DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} m.asIdeal.ResidueField) i).mapIso (e1 ≪≫ e2.symm))
  have hge : Kp.IsGE a := (DerivedCategory.isGE_iff Kp a).2 fun i hi =>
    homology_isZero_of_maximal_fibres Kp hKpc i fun m => hlocal m i hi
  obtain ⟨g, hg, hperf, -⟩ :=
    exists_away_bounded_free_complex_representing_of_fibre_vanishing_below
      (IsLocalRing.maximalIdeal Rp) Kp hKpc ⟨a, hge⟩ a
      (fun i hi => (fibreCohomologyVanishes_iff_isZero_homology
        (IsLocalRing.maximalIdeal Rp) Kp hKpc i).mp
          (hlocal ⟨IsLocalRing.maximalIdeal Rp, IsLocalRing.maximalIdeal.isMaximal Rp⟩ i hi))
  refine isPerfect_of_localizationSpan (fun _ : Fin 1 => g) ?_ Kp fun _ => ?_
  · rw [show Set.range (fun _ : Fin 1 => g) = {g} by ext x; simp]
    exact Ideal.span_singleton_eq_top.mpr (IsLocalRing.notMem_maximalIdeal.mp hg)
  · exact isPerfect_localizationAway_of_total g Kp hperf

open CochainComplex.DerivedExtensionScalars in
/-- Perfectness at every maximal stalk implies perfectness at every prime stalk: a prime is
contained in a maximal ideal, and the stalk at the prime is a derived base change of the stalk at
that maximal ideal. -/
private theorem perfect_at_prime_of_perfect_at_maximals {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K)
    (h : ∀ m : MaximalSpectrum R, IsPerfect ((totalDerivedExtensionScalars.{u, u, v}
      (algebraMap R (Localization.AtPrime m.asIdeal))).functor.obj K))
    (q : PrimeSpectrum R) :
    IsPerfect ((totalDerivedExtensionScalars.{u, u, v}
      (algebraMap R (Localization.AtPrime q.asIdeal))).functor.obj K) := by
  obtain ⟨m, hmMax, hqm⟩ := Ideal.exists_le_maximal q.asIdeal q.isPrime.ne_top
  have hle : ∀ x ∈ m.primeCompl, x ∈ q.asIdeal.primeCompl := fun x hx hxq => hx (hqm hxq)
  let g : Localization.AtPrime m →+* Localization.AtPrime q.asIdeal :=
    IsLocalization.map (M := m.primeCompl) (T := q.asIdeal.primeCompl)
      (Localization.AtPrime q.asIdeal) (RingHom.id R) hle
  have hg : g.comp (algebraMap R (Localization.AtPrime m)) =
      algebraMap R (Localization.AtPrime q.asIdeal) := by
    simpa [g] using IsLocalization.map_comp (Q := Localization.AtPrime q.asIdeal)
      (g := RingHom.id R) hle
  have hbase := isPerfect_derivedExtensionScalars.{u, u, v} g _ (h ⟨m, hmMax⟩)
  obtain ⟨e⟩ := totalDerived_comp_obj_of_pseudoCoherent
    (algebraMap R (Localization.AtPrime m)) g K hK
  rw [hg] at e
  exact isPerfect_of_iso' hbase e

open CochainComplex.DerivedExtensionScalars in
/-- A bounded below pseudo-coherent object which is perfect at every prime stalk is perfect:
[stacks 0BYP] makes it perfect on a principal neighbourhood of every prime, and [stacks 066Y]
descends perfectness from the resulting cover of `Spec R`. -/
private theorem isPerfect_of_isGE_and_perfect_at_primes {R : Type u} [CommRing R]
    (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) (hbounded : ∃ a : ℤ, K.IsGE a)
    (h : ∀ q : PrimeSpectrum R, IsPerfect ((totalDerivedExtensionScalars.{u, u, v}
      (algebraMap R (Localization.AtPrime q.asIdeal))).functor.obj K)) :
    IsPerfect K := by
  classical
  set s : Set R := {g : R | IsPerfect ((totalDerivedExtensionScalars.{u, u, v}
    (algebraMap R (Localization.Away g))).functor.obj K)} with hs
  obtain ⟨t, hts, hfspan⟩ := exists_finite_span_eq_top s fun m hm => by
    have hmprime : m.IsPrime := hm.isPrime
    obtain ⟨a, ha⟩ := fibre_vanishes_below_of_perfect_at_prime K hK ⟨m, hmprime⟩
      (h ⟨m, hmprime⟩)
    obtain ⟨g, hg, hperf, -⟩ :=
      exists_away_bounded_free_complex_representing_of_fibre_vanishing_below
        m K hK hbounded a ha
    exact ⟨g, hperf, hg⟩
  refine isPerfect_of_localizationSpan ((↑) : {x // x ∈ t} → R) hfspan K fun i => ?_
  exact isPerfect_localizationAway_of_total (i : R) K (hts i.property)

/-- Let `R` be a commutative ring and let `K` be a pseudo-coherent object of the derived category
of `R`-modules. Then `K` perfect implies that every stalk `K ⊗_R^L R_p` is perfect; perfectness at
all prime stalks, perfectness at all maximal stalks, and the vanishing of the cohomology of the
derived fibre `K ⊗_R^L κ(p)` in all sufficiently low degrees at every prime or at every maximal
ideal are equivalent; and if `K` is bounded below these are also equivalent to perfectness of `K`
itself.

The derived base change is the canonical one of [stacks 064H],
`CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`. -/
@[stacks 068W]
theorem isPerfect_iff_isPerfect_at_primes_of_isBoundedBelow_and_stalkwise_criteria
    {R : Type u} [CommRing R] (K : DerivedCategory (ModuleCat.{max u v} R))
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K) :
    let perfect := IsPerfect K
    let perfectAtPrimes := ∀ q : PrimeSpectrum R,
      IsPerfect ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
        (algebraMap R (Localization.AtPrime q.asIdeal))).functor.obj K)
    let perfectAtMaximals := ∀ m : MaximalSpectrum R,
      IsPerfect ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
        (algebraMap R (Localization.AtPrime m.asIdeal))).functor.obj K)
    let fibreVanishesBelowAtPrimes := ∀ q : PrimeSpectrum R,
      ∃ a : ℤ, ∀ i : ℤ, i < a →
        IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{max u v} q.asIdeal.ResidueField) i).obj
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
              (algebraMap R q.asIdeal.ResidueField)).functor.obj K))
    let fibreVanishesBelowAtMaximals := ∀ m : MaximalSpectrum R,
      ∃ a : ℤ, ∀ i : ℤ, i < a →
        IsZero ((DerivedCategory.homologyFunctor
          (ModuleCat.{max u v} m.asIdeal.ResidueField) i).obj
            ((CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
              (algebraMap R m.asIdeal.ResidueField)).functor.obj K))
    (perfect → perfectAtPrimes) ∧
      (perfectAtPrimes ↔ perfectAtMaximals) ∧
      (perfectAtPrimes ↔ fibreVanishesBelowAtPrimes) ∧
      (perfectAtMaximals ↔ fibreVanishesBelowAtMaximals) ∧
      ((∃ a : ℤ, K.IsGE a) → (perfect ↔ perfectAtPrimes)) := by
  intro perfect perfectAtPrimes perfectAtMaximals fibreVanishesBelowAtPrimes
    fibreVanishesBelowAtMaximals
  have hperfectPrime : perfect → perfectAtPrimes := fun hp q =>
    isPerfect_derivedExtensionScalars.{u, u, v}
      (algebraMap R (Localization.AtPrime q.asIdeal)) K hp
  have hprimeMax : perfectAtPrimes → perfectAtMaximals := fun hp m => hp m.toPrimeSpectrum
  refine ⟨hperfectPrime, ⟨hprimeMax, perfect_at_prime_of_perfect_at_maximals K hK⟩,
    ⟨fun hp q => fibre_vanishes_below_of_perfect_at_prime K hK q (hp q),
      fun hp q => perfect_at_prime_of_fibre_vanishes_below K hK q (hp q)⟩,
    ⟨fun hp m => fibre_vanishes_below_of_perfect_at_prime K hK m.toPrimeSpectrum (hp m),
      fun hp m => perfect_at_prime_of_fibre_vanishes_below K hK m.toPrimeSpectrum (hp m)⟩,
    fun hbounded => ⟨hperfectPrime,
      isPerfect_of_isGE_and_perfect_at_primes K hK hbounded⟩⟩

end Stalks

end StacksDraft.Perfect

end
