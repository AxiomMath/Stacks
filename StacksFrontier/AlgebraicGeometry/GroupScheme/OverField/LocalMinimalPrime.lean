module

public import Mathlib.AlgebraicGeometry.Group.Smooth
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.RingHom.Flat
public import Mathlib.Topology.Sober
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GroupScheme.OverField.IdentityComponent
public import StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleComponents
public import StacksFrontier.RingTheory.Spectrum.Prime.Surjective

/-!
# Minimal primes of local rings on a group scheme

Every local ring of a group scheme over a field has a unique minimal prime ideal.  The point is
translated to a rational point after base change to its residue field, where the uniqueness of
the irreducible component through the identity applies; flat descent along the projection of
the base change then transports the conclusion back.

## Main results

* `AlgebraicGeometry.existsUnique_minimalPrime_stalk` states that the stalk at every point of a
  group scheme over a field has a unique minimal prime.
* `AlgebraicGeometry.existsUnique_minimalPrime_stalk_of_irreducibleComponent` and
  `AlgebraicGeometry.existsUnique_minimalPrime_localization_of_irreducibleComponent` turn a
  unique irreducible component through a point into a unique minimal prime of the local ring
  there, and `AlgebraicGeometry.existsUnique_minimalPrime_of_faithfullyFlat`,
  `AlgebraicGeometry.existsUnique_minimalPrime_of_flat_localHom` and
  `AlgebraicGeometry.existsUnique_minimalPrime_of_ringEquiv` transport that uniqueness along
  flat and bijective ring maps.
* `AlgebraicGeometry.existsUnique_irreducibleComponent_of_openEmbedding` transports a unique
  irreducible component through a point along an open embedding.

## Implementation notes

A group scheme over `k` is represented as a group object in the category of schemes over
`Spec k`.  The assertion of uniqueness is stated as an existence-and-uniqueness proposition for
membership in `minimalPrimes`.

The minimal primes of a local ring correspond to the irreducible components through the
corresponding point of a spectrum, which is
`PrimeSpectrum.irreducibleComponentsThroughEquiv`; a flat local homomorphism of local rings is
faithfully flat, so the induced map of spectra is surjective and carries minimal primes to
minimal primes.

## References

* [Stacks Project, Tag 047M](https://stacks.math.columbia.edu/tag/047M)
-/

@[expose] public section

open CategoryTheory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace AlgebraicGeometry

universe u

/-- An open embedding transports a unique irreducible component through a point. -/
theorem existsUnique_irreducibleComponent_of_openEmbedding
    {X : Type*} {Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {f : Y → X} (hf : Topology.IsOpenEmbedding f) (y : Y)
    (h : ∃! Z : irreducibleComponents X, f y ∈ (Z : Set X)) :
    ∃! W : irreducibleComponents Y, y ∈ (W : Set Y) := by
  obtain ⟨Z, hZ, hZu⟩ := h
  have hne : ((Z : Set X) ∩ Set.range f).Nonempty := ⟨f y, hZ, y, rfl⟩
  let W : irreducibleComponents Y :=
    ⟨f ⁻¹' Z, preimage_mem_irreducibleComponents Z.property hf hne⟩
  refine ⟨W, hZ, fun W' hW' => ?_⟩
  obtain ⟨C, hC, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (f '' (W' : Set Y)) (W'.property.1.image f hf.continuous.continuousOn)
  have hCZ : C = (Z : Set X) := congrArg Subtype.val (hZu ⟨C, hC⟩ (hsub ⟨y, hW', rfl⟩))
  apply Subtype.ext
  have hsub' : (W' : Set Y) ⊆ (W : Set Y) := by
    intro z hz
    show f z ∈ (Z : Set X)
    rw [← hCZ]
    exact hsub ⟨z, hz, rfl⟩
  exact hsub'.antisymm (W'.property.2 W.property.1 hsub')

/-- A unique irreducible component through a point of a spectrum gives a unique minimal prime
in the localization at that point. -/
@[ega "I 7.2.8.1" "special case"]
theorem existsUnique_minimalPrime_localization_of_irreducibleComponent
    {R : Type*} [CommRing R] (p : PrimeSpectrum R)
    (h : ∃! Z : irreducibleComponents (PrimeSpectrum R),
      p ∈ (Z : Set (PrimeSpectrum R))) :
    ∃! q : Ideal (Localization.AtPrime p.asIdeal), q ∈ minimalPrimes _ := by
  let _ : p.asIdeal.IsPrime := p.isPrime
  let e := PrimeSpectrum.irreducibleComponentsThroughEquiv R p.asIdeal
    (Localization.AtPrime p.asIdeal)
  obtain ⟨Z, hZ, hZu⟩ := h
  let z : PrimeSpectrum.irreducibleComponentsThrough R p.asIdeal := ⟨Z, Z.property, hZ⟩
  refine ⟨(e z).1, (e z).2, fun q hq => ?_⟩
  let z' := e.symm ⟨q, hq⟩
  have hcomp : (⟨z'.1, z'.2.1⟩ : irreducibleComponents (PrimeSpectrum R)) = Z :=
    hZu ⟨z'.1, z'.2.1⟩ z'.2.2
  have heq : z' = z := Subtype.ext <| congrArg
    (fun T : irreducibleComponents (PrimeSpectrum R) => (T : Set (PrimeSpectrum R))) hcomp
  exact congrArg Subtype.val ((e.apply_symm_apply ⟨q, hq⟩).symm.trans (congrArg e heq))

/-- A faithfully flat algebra has a unique minimal prime only if its base does. -/
theorem existsUnique_minimalPrime_of_faithfullyFlat
    {R S : Type*} [CommRing R] [Nontrivial R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S]
    (hS : ∃! q : Ideal S, q ∈ minimalPrimes S) :
    ∃! p : Ideal R, p ∈ minimalPrimes R := by
  have hsurj : Set.SurjOn (fun q => Ideal.comap (algebraMap R S) q)
      (minimalPrimes S) (minimalPrimes R) := by
    intro p hp
    obtain ⟨P, hP⟩ := (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S))
      (⟨p, hp.1.1⟩ : PrimeSpectrum R)
    obtain ⟨q, hq, hqP⟩ :=
      Ideal.exists_minimalPrimes_le (I := (⊥ : Ideal S)) (J := P.asIdeal) bot_le
    refine ⟨q, hq, ?_⟩
    have hPp : Ideal.comap (algebraMap R S) P.asIdeal = p :=
      congrArg PrimeSpectrum.asIdeal hP
    have hle : Ideal.comap (algebraMap R S) q ≤ p := by
      rw [← hPp]
      exact Ideal.comap_mono hqP
    have hprime : (Ideal.comap (algebraMap R S) q).IsPrime := hq.1.1.comap _
    exact le_antisymm hle (hp.2 ⟨hprime, bot_le⟩ hle)
  obtain ⟨q, hq, hqu⟩ := hS
  obtain ⟨p, hp⟩ := Ideal.nonempty_minimalPrimes (I := (⊥ : Ideal R)) bot_ne_top
  obtain ⟨q₀, hq₀, hq₀p⟩ := hsurj hp
  refine ⟨p, hp, fun p' hp' => ?_⟩
  obtain ⟨q', hq', hq'p⟩ := hsurj hp'
  rw [← hq₀p, ← hq'p, hqu q₀ hq₀, hqu q' hq']

/-- A flat local homomorphism of local rings has a unique minimal prime in its source if it has
one in its target. -/
theorem existsUnique_minimalPrime_of_flat_localHom
    {R S : Type*} [CommRing R] [IsLocalRing R]
    [CommRing S] [IsLocalRing S] (f : R →+* S) [IsLocalHom f]
    (hf : f.Flat) (hS : ∃! q : Ideal S, q ∈ minimalPrimes S) :
    ∃! p : Ideal R, p ∈ minimalPrimes R := by
  let _ : Algebra R S := f.toAlgebra
  have : Module.Flat R S := hf
  have : IsLocalHom (algebraMap R S) := inferInstanceAs (IsLocalHom f)
  have : Module.FaithfullyFlat R S := Module.FaithfullyFlat.of_flat_of_isLocalHom
  exact existsUnique_minimalPrime_of_faithfullyFlat hS

/-- Isomorphic local rings have unique minimal primes together. -/
theorem existsUnique_minimalPrime_of_ringEquiv
    {R S : Type*} [CommRing R] [IsLocalRing R] [CommRing S] [IsLocalRing S]
    (e : R ≃+* S) (hS : ∃! q : Ideal S, q ∈ minimalPrimes S) :
    ∃! p : Ideal R, p ∈ minimalPrimes R := by
  let _ : IsLocalHom e.toRingHom := IsLocalHom.of_surjective _ e.surjective
  exact existsUnique_minimalPrime_of_flat_localHom e.toRingHom
    (RingHom.Flat.of_bijective e.bijective) hS

/-- A unique irreducible component through a point of a scheme gives a unique minimal prime in
the local ring at that point. -/
theorem existsUnique_minimalPrime_stalk_of_irreducibleComponent
    {X : Scheme.{u}} (x : X)
    (h : ∃! Z : irreducibleComponents X, x ∈ (Z : Set X)) :
    ∃! p : Ideal (X.presheaf.stalk x), p ∈ minimalPrimes _ := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  let p := hU.primeIdealOf ⟨x, hxU⟩
  have hcomp : ∃! Z : irreducibleComponents (PrimeSpectrum Γ(X, U)),
      p ∈ (Z : Set (PrimeSpectrum Γ(X, U))) := by
    have : IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
    apply existsUnique_irreducibleComponent_of_openEmbedding hU.fromSpec.isOpenEmbedding p
    simpa [p, hU.fromSpec_primeIdealOf] using h
  have hLoc := existsUnique_minimalPrime_localization_of_irreducibleComponent p hcomp
  let : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    (X.presheaf.germ U x hxU).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  let e : Localization.AtPrime p.asIdeal ≃+* X.presheaf.stalk x :=
    (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (X.presheaf.stalk x)).toRingEquiv
  exact existsUnique_minimalPrime_of_ringEquiv e.symm hLoc

/-- **Stacks Project, Tag 047M.** Every local ring of a group scheme over a field has a
unique minimal prime ideal. -/
@[stacks 047M "local_unique_minimal_prime"]
theorem existsUnique_minimalPrime_stalk (k : Type u) [Field k]
    (G : Grp (Over (Spec (CommRingCat.of k)))) (g : G.X.left) :
    ∃! p : Ideal (G.X.left.presheaf.stalk g),
      p ∈ minimalPrimes (G.X.left.presheaf.stalk g) := by
  classical
  let f := G.X.hom
  let K := G.X.left.residueField g
  let b : Spec K ⟶ Spec (.of k) := G.X.left.fromSpecResidueField g ≫ f
  let Y : Scheme := Limits.pullback f b
  let t : Spec K ⟶ Y :=
    Limits.pullback.lift (G.X.left.fromSpecResidueField g) (𝟙 _) (by simp [b])
  let y : Y := t (IsLocalRing.closedPoint K)
  have hy : (Limits.pullback.fst f b) y = g := by
    show (t ≫ Limits.pullback.fst f b) (IsLocalRing.closedPoint K) = g
    rw [Limits.pullback.lift_fst]
    exact Scheme.fromSpecResidueField_apply g _
  let : GrpObj (Over.mk f) := G.grp
  let H : Over (Spec (.of K)) := Over.mk (Limits.pullback.snd f b)
  let : GrpObj H := Over.grpObjMkPullbackSnd
  let x' : MonoidalCategoryStruct.tensorUnit (Over (Spec (.of K))) ⟶ H :=
    Over.homMk t (by dsimp [t, H]; rw [Limits.pullback.lift_snd]; rfl)
  let α := (GrpObj.mulRight x').symm ≪≫ (GrpObj.mulRight (η[H]))
  have hα : x' ≫ α.hom = η[H] := by
    dsimp only [Iso.trans_hom, Iso.symm_hom, α]
    rw [← Category.assoc, ← Iso.eq_comp_inv]
    simp [comp_lift_assoc]
  have hα' : α.hom.left y = (η[H]).left (IsLocalRing.closedPoint K) := by
    let s : Spec K := IsLocalRing.closedPoint K
    have h := congrArg
      (fun z : MonoidalCategoryStruct.tensorUnit (Over (Spec (.of K))) ⟶ H =>
        z.left s) hα
    change (t ≫ α.hom.left) s = _ at h
    rw [Scheme.Hom.comp_apply] at h
    simpa [y, s] using h
  let : GrpObj (Over.mk H.hom) := by dsimp [H]; infer_instance
  have hcomp : ∃! Z : irreducibleComponents Y, y ∈ (Z : Set Y) := by
    have : IsIso α.hom.left := by
      show IsIso ((Over.forget _).map α.hom)
      infer_instance
    have : IsOpenImmersion α.hom.left := inferInstance
    apply existsUnique_irreducibleComponent_of_openEmbedding α.hom.left.isOpenEmbedding y
    simpa [hα'] using
      existsUnique_irreducibleComponent_containing_identity
        (H.hom : H.left ⟶ Spec (.of K))
  have hX := existsUnique_minimalPrime_of_flat_localHom
    ((Limits.pullback.fst f b).stalkMap y).hom
    (by have : Flat (Limits.pullback.fst f b) := inferInstance; exact Flat.stalkMap _ _)
    (existsUnique_minimalPrime_stalk_of_irreducibleComponent y hcomp)
  rw [hy] at hX
  exact hX

end AlgebraicGeometry

end
