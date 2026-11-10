module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Colimits
public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AbsoluteWeakNormalizationInitial.Basic
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.AbsolutelyWeaklyNormalPerfect
public import StacksFrontier.AlgebraicGeometry.Frobenius
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeakNormalization.AbsoluteWeakNormalCriterion
public import StacksFrontier.AlgebraicGeometry.Size.OpenCover
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.AffineSiteEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.SheafCriterion
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.StructureSheafFailure
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.FrobeniusColimit
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.PhSheafOfSections
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.RingColimitFiltered
public import StacksFrontier.AlgebraicGeometry.Topologies.WeakNormalization.StructureSheafSheafification
public import StacksFrontier.CategoryTheory.Sites.Stackification.UniversalProperty
public import StacksFrontier.Topology.Sheaves.Limits.FilteredColimitSections
public import StacksFrontier.Topology.Sheaves.Limits.SpectralCovers
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Frobenius-colimit h sheaf

For a ring `A` and a natural number `p` the set `colim_F A` is the colimit of
`A →^F A →^F ⋯` along `F : a ↦ a ^ p`; for an `𝔽_p`-algebra this is the perfection.  On the big
h site `(Sch/S)_h` of Stacks 0EU1 the rule `X ↦ colim_F Γ(X, 𝒪_X)` is a presheaf of sets.  Stacks
0EVK asserts that, for `S` over `𝔽_p`, there is a unique sheaf whose sections over every
quasi-compact quasi-separated object are given by that rule.  This file proves both halves.

## Main definitions

* `AlgebraicGeometry.BigHOver.sectionsRingPresheaf`: the presheaf `X ↦ Γ(X, 𝒪_X)` of rings; its
  underlying presheaf of sets is `AlgebraicGeometry.BigHOver.globalFunctions`.
* `AlgebraicGeometry.BigHOver.frobeniusSectionsSequence`: the tower `Γ →^F Γ →^F ⋯`.
* `AlgebraicGeometry.BigHOver.frobeniusColimitSections`: the presheaf `colim_F Γ(-, 𝒪)`.
* `AlgebraicGeometry.BigHOver.awnSections`: the presheaf `X ↦ Γ(Xᵃʷⁿ, 𝒪)` of global functions
  on absolute weak normalizations.
* `AlgebraicGeometry.BigHOver.awnComparison`: the comparison
  `colim_F Γ(X, 𝒪_X) ⟶ Γ(Xᵃʷⁿ, 𝒪)`, sending the stage `n` class of `a` to the `pⁿ`-th root of
  the pullback of `a`.

## Main results

* `AlgebraicGeometry.BigHOver.isSheaf_awnSections`: `X ↦ Γ(Xᵃʷⁿ, 𝒪)` is a sheaf for the h
  topology.
* `AlgebraicGeometry.BigHOver.bijective_awnComparison_app`: over a scheme in characteristic `p`
  the comparison is bijective on quasi-compact quasi-separated objects.
* `AlgebraicGeometry.BigHOver.existsUnique_iso_of_bijective_isAffine`: two h sheaves receiving
  a map from a common presheaf which is bijective on objects with affine underlying scheme are
  isomorphic by a unique isomorphism compatible with the two maps.
* `AlgebraicGeometry.BigHOver.existsUnique_iso_frobeniusColimitSections`: **Stacks 0EVK**,
  existence and uniqueness.

## Implementation notes

The identification `ℱ(X) = colim_F Γ(X, 𝒪_X)` of the source is read as a morphism of presheaves
`colim_F Γ(-, 𝒪) ⟶ ℱ` which is bijective on quasi-compact quasi-separated objects; naturality in
`X` is the source's implicit requirement that the identification be compatible with restriction.

**Existence.**  The source takes the Zariski sheafification of `X ↦ colim_F Γ(X, 𝒪_X)` and checks
the four conditions of the h sheaf criterion Stacks 0EVI.  The sufficiency direction of that
criterion is not available in this development, so the proof here goes through the absolute
weak normalization instead, as Stacks 0EVW does.  The sheaf is `X ↦ Γ(Xᵃʷⁿ, 𝒪)`.  It is an h
sheaf by the Zariski and proper-surjective descent statements proved for Stacks 0EVT, assembled
by the sheaf criterion Stacks 0EU5.  Over `𝔽_p` Frobenius is bijective on `Γ(Xᵃʷⁿ, 𝒪)`, because
`Xᵃʷⁿ` is absolutely weakly normal and absolutely weakly normal `𝔽_p`-algebras are perfect
(Stacks 0EVV).  This makes the comparison map well defined.

It is injective on quasi-compact objects: a function whose pullback to `Xᵃʷⁿ` vanishes is
nilpotent, because `Xᵃʷⁿ ⟶ X` is surjective.  It is surjective on quasi-compact quasi-separated
objects: over an affine open, `Xᵃʷⁿ` is the spectrum of the absolute weak normalization of the
ring, which is the Frobenius colimit (Stacks 0EVW), so every function there has a `pⁿ`-th power
pulled back from `X`.  The local preimages over a finite affine covering agree on the
quasi-compact overlaps up to nilpotents, so a further power glues them.

**Uniqueness.**  It is the statement that such a morphism exhibits its target as a
sheafification of `colim_F Γ(-, 𝒪)`, which is
`CategoryTheory.Presheaf.existsUnique_hom_of_isLocallyBijective`.  Only objects with affine
underlying scheme are needed for this.  The localisation to affine objects is cover density of
the big affine h site, Stacks 0EU4.  An arrow of `CategoryTheory.Sieve.coverByImage` need not
have affine source; it only factors through an affine object, and that is all either local
statement needs.

## References

* [Stacks Project, Tag 0EVK](https://stacks.math.columbia.edu/tag/0EVK)
* [Stacks Project, Tag 0EVT](https://stacks.math.columbia.edu/tag/0EVT)
* [Stacks Project, Tag 0EVW](https://stacks.math.columbia.edu/tag/0EVW)
* [Stacks Project, Tag 0EVV](https://stacks.math.columbia.edu/tag/0EVV)
* [Stacks Project, Tag 0EU5](https://stacks.math.columbia.edu/tag/0EU5)
* [Stacks Project, Tag 0EU1](https://stacks.math.columbia.edu/tag/0EU1)
* [Stacks Project, Tag 0EU4](https://stacks.math.columbia.edu/tag/0EU4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.Presheaf

/-- The Frobenius `a ↦ a ^ p` of the presheaf of sets underlying a presheaf of commutative
rings.  It is a morphism of presheaves of sets for every `p`, and a morphism of presheaves of
rings exactly when the values have characteristic dividing `p`. -/
public def frobeniusForget {C : Type*} [Category* C] (G : Cᵒᵖ ⥤ CommRingCat.{u}) (p : ℕ) :
    (G ⋙ CategoryTheory.forget CommRingCat.{u}) ⟶ (G ⋙ CategoryTheory.forget CommRingCat.{u}) where
  app X := TypeCat.ofHom (fun (a : ToType (G.obj X)) => a ^ p)
  naturality _ _ _ := by
    ext a
    simp

/-- The Frobenius of a presheaf of commutative rings raises a section to its `p`-th power. -/
public theorem frobeniusForget_app {C : Type*} [Category* C] (G : Cᵒᵖ ⥤ CommRingCat.{u}) (p : ℕ)
    (X : Cᵒᵖ) (a : ToType (G.obj X)) : (frobeniusForget G p).app X a = a ^ p :=
  rfl

end CategoryTheory.Presheaf

namespace AlgebraicGeometry

/-! ### Frobenius in characteristic `p` -/

section Frobenius

variable {R : Type*} [CommRing R] (p : ℕ) [Fact p.Prime]

/-- Iterating the `p`-th power endomorphism `k` times raises to the `p ^ k`-th power. -/
private theorem primePowerEndomorphism_iterate (hp : (p : R) = 0) (k : ℕ) (x : R) :
    (Stacks.Frobenius.primePowerEndomorphism R p hp)^[k] x = x ^ p ^ k := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Stacks.Frobenius.primePowerEndomorphism_apply,
      ← pow_mul, ← pow_succ]

/-- In a ring in which the prime `p` vanishes, raising to a `p ^ k`-th power is additive. -/
private theorem sub_pow_prime_pow (hp : (p : R) = 0) (k : ℕ) (x y : R) :
    (x - y) ^ p ^ k = x ^ p ^ k - y ^ p ^ k := by
  have h := map_sub (Stacks.Frobenius.primePowerEndomorphism R p hp ^ k) x y
  rwa [RingHom.coe_pow, primePowerEndomorphism_iterate, primePowerEndomorphism_iterate,
    primePowerEndomorphism_iterate] at h

/-- **In a ring in which the prime `p` vanishes, raising to a `p ^ k`-th power is additive.**

The hypothesis is the vanishing of the image of `p` rather than `CharP`, which it does not imply:
a ring in which `1 = 0` has every natural number vanishing and is not of characteristic `p`. So
this is not an instance of `sub_pow_char_pow`, and it is the form in which the vanishing arrives
from a presheaf of rings whose values are only known to kill `p`. -/
public alias sub_pow_prime_pow_of_natCast_eq_zero := sub_pow_prime_pow

/-- In a reduced ring in which the prime `p` vanishes, the `p`-th power map is injective. -/
@[ega "0 21.1.4"]
private theorem pow_injective_of_isReduced [_root_.IsReduced R] (hp : (p : R) = 0) :
    Function.Injective (fun x : R => x ^ p) := by
  intro x y hxy
  have hxy' : x ^ p = y ^ p := hxy
  have h : (x - y) ^ p ^ 1 = 0 := by
    rw [sub_pow_prime_pow p hp, pow_one, hxy', sub_self]
  exact sub_eq_zero.mp (IsReduced.eq_zero _ ⟨_, h⟩)

/-- A nilpotent element has a vanishing `p ^ k`-th power for some `k`. -/
private theorem exists_pow_prime_pow_eq_zero {x : R} (hx : IsNilpotent x) :
    ∃ k : ℕ, x ^ p ^ k = 0 := by
  obtain ⟨m, hm⟩ := hx
  exact ⟨m, pow_eq_zero_of_le (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le hm⟩

/-- If `(x - y) ^ p ^ k` vanishes in a ring in which the prime `p` vanishes, then `x` and `y`
have the same `p ^ K`-th power for every `K ≥ k`. -/
private theorem pow_prime_pow_eq_of_sub_pow_eq_zero (hp : (p : R) = 0) {x y : R} {k K : ℕ}
    (hk : (x - y) ^ p ^ k = 0) (hK : k ≤ K) : x ^ p ^ K = y ^ p ^ K := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hK
  rw [← sub_eq_zero, ← sub_pow_prime_pow p hp, pow_add, pow_mul, hk,
    zero_pow (pow_ne_zero _ (Fact.out : p.Prime).ne_zero)]

end Frobenius

/-! ### Global functions on absolute weak normalizations in characteristic `p` -/

section AbsoluteWeakNormalization

/-- The absolute weak normalization of a scheme is absolutely weakly normal. -/
private theorem isAbsolutelyWeaklyNormal_absoluteWeakNormalization (X : Scheme.{u}) :
    IsAbsolutelyWeaklyNormal X.absoluteWeakNormalization := by
  let awn : UniversalHomeomorphismOver X := initial (UniversalHomeomorphismOver X)
  refine (isIso_initialTo_iff_isAbsolutelyWeaklyNormal X awn).mp ?_
  rw [show initial.to awn = 𝟙 awn from Subsingleton.elim _ _]
  change IsIso (𝟙 awn.obj.left)
  infer_instance

/-- The `ZMod p`-algebra structure on a ring in which the prime `p` vanishes. -/
@[instance_reducible]
private noncomputable def zmodAlgebraOfCastEqZero (p : ℕ) [Fact p.Prime] (R : Type*)
    [CommRing R] (hp : (p : R) = 0) : Algebra (ZMod p) R := by
  classical
  by_cases hR : Nontrivial R
  · haveI : CharP R p := (CharP.charP_iff_prime_eq_zero Fact.out).2 hp
    exact RingHom.toAlgebra (ZMod.castHom (dvd_refl p) R)
  · haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp hR
    exact RingHom.toAlgebra
      { toFun := fun _ => 0
        map_one' := Subsingleton.elim _ _
        map_mul' := fun _ _ => Subsingleton.elim _ _
        map_zero' := rfl
        map_add' := fun _ _ => Subsingleton.elim _ _ }

variable (p : ℕ) [hp : Fact p.Prime]

/-- On an absolutely weakly normal scheme in which the prime `p` vanishes, taking `p`-th powers
of global functions is bijective.

It is injective because the scheme is reduced, and surjective because the ring of functions on
every affine open is absolutely weakly normal, hence perfect (Stacks 0EVV), so `p`-th roots exist
locally and glue by injectivity on the overlaps. -/
private theorem pow_bijective_of_isAbsolutelyWeaklyNormal {Y : Scheme.{u}}
    (hY : IsAbsolutelyWeaklyNormal Y) (hpY : (p : Γ(Y, ⊤)) = 0) :
    Function.Bijective (fun s : Γ(Y, ⊤) => s ^ p) := by
  have _ : IsReduced Y := absolutelyWeaklyNormal_isReduced hY
  have hpU (U : Y.Opens) : (p : Γ(Y, U)) = 0 :=
    Stacks.Frobenius.cast_eq_zero_of_isInCharacteristic hpY U
  have hinj (U : Y.Opens) : Function.Injective (fun s : Γ(Y, U) => s ^ p) :=
    pow_injective_of_isReduced p (hpU U)
  have hsurj (U : Y.affineOpens) : Function.Surjective (fun s : Γ(Y, U.1) => s ^ p) := by
    let := zmodAlgebraOfCastEqZero p Γ(Y, U.1) (hpU U.1)
    have hiff : IsAbsolutelyWeaklyNormal Y ↔
        ∀ V : Y.affineOpens, IsAbsolutelyWeaklyNormalRing Γ(Y, V.val) :=
      (isAbsolutelyWeaklyNormal_tfae Y).out 1 2
    have hawn : IsAbsolutelyWeaklyNormalRing Γ(Y, U.1) := hiff.mp hY U
    exact ((isAbsolutelyWeaklyNormalRing_iff_perfectRing p hp.out _).mp hawn).bijective_frobenius.2
  refine ⟨hinj ⊤, fun s => ?_⟩
  let U : Y.affineOpens → Y.Opens := fun V => V.1
  have hcov : (⊤ : Y.Opens) ≤ iSup U := by rw [iSup_affineOpens_eq_top Y]
  choose r hr using fun V : Y.affineOpens =>
    hsurj V (Y.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op s)
  have hr' (V : Y.affineOpens) : r V ^ p = Y.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op s :=
    hr V
  obtain ⟨t, ht, -⟩ := Y.sheaf.existsUnique_gluing' U ⊤ (fun V => homOfLE le_top) hcov r (by
    intro V W
    apply hinj
    change (Y.presheaf.map _ (r V)) ^ p = (Y.presheaf.map _ (r W)) ^ p
    rw [← map_pow, ← map_pow, hr', hr', ← ConcreteCategory.comp_apply,
      ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← Functor.map_comp]
    rfl)
  let t' : Γ(Y, ⊤) := t
  have ht' (V : Y.affineOpens) : Y.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op t' = r V := ht V
  refine ⟨t', Y.sheaf.eq_of_locally_eq' U ⊤ (fun V => homOfLE le_top) hcov _ _ fun V => ?_⟩
  change Y.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op (t' ^ p) =
    Y.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op s
  rw [map_pow, ht', hr']

/-- On the absolute weak normalization of a scheme in which the prime `p` vanishes, taking
`p`-th powers of global functions is bijective. -/
private theorem pow_bijective_absoluteWeakNormalization (X : Scheme.{u})
    (hX : (p : Γ(X, ⊤)) = 0) :
    Function.Bijective (fun s : Γ(X.absoluteWeakNormalization, ⊤) => s ^ p) :=
  pow_bijective_of_isAbsolutelyWeaklyNormal p
    (isAbsolutelyWeaklyNormal_absoluteWeakNormalization X)
    (by simpa using congrArg X.absoluteWeakNormalizationHom.appTop.hom hX)

/-- A section over a quasi-compact open whose pullback to the absolute weak normalization
vanishes is nilpotent: the absolute weak normalization maps onto the scheme, so the basic open
of the section is empty. -/
private theorem isNilpotent_of_absoluteWeakNormalizationHom_app_eq_zero {X : Scheme.{u}}
    {W : X.Opens} (hW : IsCompact (W : Set X)) (a : Γ(X, W))
    (ha : X.absoluteWeakNormalizationHom.app W a = 0) : IsNilpotent a := by
  refine (Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hW a).mpr ?_
  have hpre : X.absoluteWeakNormalizationHom ⁻¹ᵁ X.basicOpen a = ⊥ := by
    rw [Scheme.preimage_basicOpen, ha, Scheme.basicOpen_zero]
  have hsurj := (surjective_absoluteWeakNormalizationHom X).surj
  refine eq_bot_iff.mpr fun x hx => ?_
  obtain ⟨y, rfl⟩ := hsurj x
  have hy : y ∈ X.absoluteWeakNormalizationHom ⁻¹ᵁ X.basicOpen a := hx
  rw [hpre] at hy
  exact hy

end AbsoluteWeakNormalization

/-! ### Frobenius roots in the absolute weak normalization of an affine scheme -/

section AffineRoots

variable (p : ℕ) [hp : Fact p.Prime]

/-- Every element of the absolute weak normalization of an algebra over `𝔽_p` has a `pⁿ`-th
power coming from the algebra.  This is read off from Stacks 0EVW, which identifies the
absolute weak normalization with the colimit of the Frobenius tower. -/
private theorem exists_pow_eq_algebraMap_absoluteWeakNormalization (A : Type u) [CommRing A]
    [Algebra (ZMod p) A] (r : Algebra.AbsoluteWeakNormalization A) :
    ∃ (n : ℕ) (a : A), r ^ p ^ n = algebraMap A (Algebra.AbsoluteWeakNormalization A) a := by
  obtain ⟨e, he, -⟩ :=
    Algebra.existsUnique_frobeniusColimit_iso_absoluteWeakNormalization p hp.out A
  obtain ⟨n, a, ha⟩ := Algebra.frobeniusColimit_exists_rep p A (e.inv r)
  refine ⟨n, a, ?_⟩
  let D := Algebra.frobeniusDiagram p A
  let ιn : A →+* ↑(colimit D) := (colimit.ι D n).hom
  let ι0 : A →+* ↑(colimit D) := (colimit.ι D 0).hom
  let eR : ↑(colimit D) →+* Algebra.AbsoluteWeakNormalization A := e.hom.hom
  have hr : r = eR (ιn a) := by
    change r = e.hom (colimit.ι D n a)
    rw [ha]
    exact (Iso.inv_hom_id_apply e r).symm
  have h0 : eR (ι0 a) = algebraMap A (Algebra.AbsoluteWeakNormalization A) a :=
    congrArg (fun φ : CommRingCat.of A ⟶ CommRingCat.of (Algebra.AbsoluteWeakNormalization A) =>
      φ.hom a) he
  have hpow : ιn a ^ p ^ n = ι0 a :=
    ((map_pow ιn a (p ^ n)).symm.trans (Algebra.frobeniusColimit_ι_zero_pow p A n a).symm)
  rw [hr, ← map_pow, hpow, h0]

/-- Let `Y ⟶ Z` be a universal homeomorphism from an absolutely weakly normal scheme to an affine
scheme in which the prime `p` vanishes.  Then every global function on `Y` has a `pⁿ`-th power
pulled back from `Z`.

The morphism is the absolute weak normalization of `Z` (Stacks 0EUS), which over an affine scheme
is the spectrum of the absolute weak normalization of the ring of functions (Stacks 0EUR); this
reduces the claim to `exists_pow_eq_algebraMap_absoluteWeakNormalization`. -/
private theorem exists_pow_eq_appTop_of_universalHomeomorphism {Y Z : Scheme.{u}} [IsAffine Z]
    (q : Y ⟶ Z) (hq : UniversalHomeomorphism q) (hY : IsAbsolutelyWeaklyNormal Y)
    (hZ : (p : Γ(Z, ⊤)) = 0) (g : Γ(Y, ⊤)) :
    ∃ (n : ℕ) (a : Γ(Z, ⊤)), g ^ p ^ n = q.appTop a := by
  let := zmodAlgebraOfCastEqZero p Γ(Z, ⊤) hZ
  let A := Γ(Z, ⊤)
  let R := Algebra.AbsoluteWeakNormalization A
  let φ : CommRingCat.of A ⟶ CommRingCat.of R := CommRingCat.ofHom (algebraMap A R)
  let q' : Spec (.of R) ⟶ Z := Spec.map φ ≫ Z.isoSpec.inv
  have hiso : UniversalHomeomorphism Z.isoSpec.inv :=
    (universalHomeomorphism_iff_integral_universallyInjective_surjective _).mpr
      ⟨inferInstance, inferInstance, inferInstance⟩
  have hq' : UniversalHomeomorphism q' :=
    universalHomeomorphism_comp _ _ (absoluteWeakNormalization_universalHomeomorphism A) hiso
  let Y₁ : UniversalHomeomorphismOver Z := ⟨Over.mk q, hq⟩
  let Y₂ : UniversalHomeomorphismOver Z := ⟨Over.mk q', hq'⟩
  have hRawn : IsAbsolutelyWeaklyNormalRing R :=
    Algebra.isAbsolutelyWeaklyNormalRing_of_isTerminal A
      (Algebra.absoluteWeakNormalizationCandidate A)
      (Algebra.absoluteWeakNormalizationCandidate_isTerminal A)
  have hY₂ : IsAbsolutelyWeaklyNormal Y₂.obj.left := by
    intro x
    refine ⟨⟨⊤, isAffineOpen_top (Spec (.of R))⟩, Set.mem_univ _, ?_⟩
    change IsAbsolutelyWeaklyNormalRing Γ(Spec (.of R), ⊤)
    exact absolutelyWeaklyNormalRing_of_ringEquiv
      ((Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv) hRawn
  let i₁ : Z.absoluteWeakNormalization ⟶ Y := (initial.to Y₁).hom.left
  let i₂ : Z.absoluteWeakNormalization ⟶ Spec (.of R) := (initial.to Y₂).hom.left
  have hi₁ : IsIso i₁ := (isIso_initialTo_iff_isAbsolutelyWeaklyNormal Z Y₁).mpr hY
  have hi₂ : IsIso i₂ := (isIso_initialTo_iff_isAbsolutelyWeaklyNormal Z Y₂).mpr hY₂
  have hw₁ : i₁ ≫ q = Z.absoluteWeakNormalizationHom := (initial.to Y₁).hom.w
  have hw₂ : i₂ ≫ q' = Z.absoluteWeakNormalizationHom := (initial.to Y₂).hom.w
  -- the comparison `j : Y ⟶ Spec R` over `Z`
  let j : Y ⟶ Spec (.of R) := inv i₁ ≫ i₂
  have hj : j ≫ q' = q := by
    rw [Category.assoc, hw₂, ← hw₁, IsIso.inv_hom_id_assoc]
  have hjiso : IsIso j := inferInstance
  -- transport `g` to `R`
  let r : R := (Scheme.ΓSpecIso (.of R)).hom ((inv j).appTop g)
  obtain ⟨n, a, hra⟩ := exists_pow_eq_algebraMap_absoluteWeakNormalization p A r
  refine ⟨n, a, ?_⟩
  have hinvSpec : Z.isoSpec.inv.appTop = (Scheme.ΓSpecIso Γ(Z, ⊤)).inv := by
    rw [← cancel_epi (Scheme.ΓSpecIso Γ(Z, ⊤)).hom, Iso.hom_inv_id, ← Scheme.toSpecΓ_appTop,
      ← Scheme.Hom.comp_appTop, Scheme.isoSpec_inv_toSpecΓ]
    rfl
  have hqa : q.appTop a = j.appTop ((Scheme.ΓSpecIso (.of R)).inv (algebraMap A R a)) := by
    rw [← hj, Scheme.Hom.comp_appTop]
    change j.appTop ((Spec.map φ).appTop (Z.isoSpec.inv.appTop a)) = _
    rw [hinvSpec]
    congr 1
    exact (ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality φ) a).symm
  rw [hqa, ← hra, map_pow, map_pow]
  change g ^ p ^ n = (j.appTop ((Scheme.ΓSpecIso (.of R)).inv
    ((Scheme.ΓSpecIso (.of R)).hom ((inv j).appTop g)))) ^ p ^ n
  rw [Iso.hom_inv_id_apply, ← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    IsIso.hom_inv_id]
  rfl

end AffineRoots

/-! ### Frobenius roots in the absolute weak normalization of a qcqs scheme -/

section QcqsRoots

variable (p : ℕ) [hp : Fact p.Prime]

/-- Pulling back along a morphism of schemes commutes with restriction. -/
private theorem app_map_apply {X Y : Scheme.{u}} (f : X ⟶ Y) {U V : Y.Opens} (h : U ≤ V)
    (x : Γ(Y, V)) :
    f.app U (Y.presheaf.map (homOfLE h).op x) =
      X.presheaf.map ((TopologicalSpace.Opens.map f.base).map (homOfLE h)).op (f.app V x) :=
  ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) x

/-- Over an affine open `U` of a scheme in which the prime `p` vanishes, every function on the
inverse image of `U` in the absolute weak normalization has a `pⁿ`-th power pulled back from
`U`. -/
private theorem exists_pow_eq_app_of_isAffineOpen {Z : Scheme.{u}} (hZ : (p : Γ(Z, ⊤)) = 0)
    {U : Z.Opens} (hU : IsAffineOpen U)
    (s : Γ(Z.absoluteWeakNormalization, Z.absoluteWeakNormalizationHom ⁻¹ᵁ U)) :
    ∃ (n : ℕ) (a : Γ(Z, U)), s ^ p ^ n = Z.absoluteWeakNormalizationHom.app U a := by
  have _ : IsAffine U.toScheme := hU
  have hq : UniversalHomeomorphism (Z.absoluteWeakNormalizationHom ∣_ U) := by
    have hπ := universalHomeomorphism_absoluteWeakNormalizationHom Z
    rw [universalHomeomorphism_iff] at hπ ⊢
    exact MorphismProperty.of_isPullback
      (isPullback_morphismRestrict Z.absoluteWeakNormalizationHom U).flip hπ
  have hUp : (p : Γ(U.toScheme, ⊤)) = 0 := by
    simpa using congrArg (fun t => U.topIso.inv t)
      (Stacks.Frobenius.cast_eq_zero_of_isInCharacteristic hZ U)
  obtain ⟨n, a', ha'⟩ := exists_pow_eq_appTop_of_universalHomeomorphism p
    (Z.absoluteWeakNormalizationHom ∣_ U) hq
    (isAbsolutelyWeaklyNormal_open (isAbsolutelyWeaklyNormal_absoluteWeakNormalization Z) _) hUp
    ((Z.absoluteWeakNormalizationHom ⁻¹ᵁ U).topIso.inv s)
  refine ⟨n, U.topIso.hom a', ?_⟩
  have key : U.topIso.hom ≫ Z.absoluteWeakNormalizationHom.appLE U
        (Z.absoluteWeakNormalizationHom ⁻¹ᵁ U) le_rfl =
      (Z.absoluteWeakNormalizationHom.resLE U (Z.absoluteWeakNormalizationHom ⁻¹ᵁ U)
        le_rfl).appTop ≫ (Z.absoluteWeakNormalizationHom ⁻¹ᵁ U).topIso.hom :=
    Arrow.w (arrowResLEAppIso Z.absoluteWeakNormalizationHom U
      (Z.absoluteWeakNormalizationHom ⁻¹ᵁ U) le_rfl).hom
  rw [Scheme.Hom.resLE_eq_morphismRestrict] at key
  have h := congrArg (fun t => (Z.absoluteWeakNormalizationHom ⁻¹ᵁ U).topIso.hom t) ha'
  simp only [map_pow, Iso.inv_hom_id_apply] at h
  rw [h, Scheme.Hom.app_eq_appLE, ← ConcreteCategory.comp_apply, ← key]
  rfl

/-- A quasi-compact scheme is covered by finitely many affine opens. -/
private theorem exists_finset_affineOpens_top_le (Z : Scheme.{u}) [CompactSpace Z] :
    ∃ t : Finset Z.affineOpens, (⊤ : Z.Opens) ≤ ⨆ i : { V // V ∈ t }, i.1.1 := by
  have hmem (x : Z) : ∃ V : Z.affineOpens, x ∈ (V : Z.Opens) := by
    have hx : x ∈ (⨆ V : Z.affineOpens, (V : Z.Opens)) := by
      rw [iSup_affineOpens_eq_top Z]
      trivial
    exact TopologicalSpace.Opens.mem_iSup.mp hx
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : Z.affineOpens => ((V : Z.Opens) : Set Z)) (fun V => (V : Z.Opens).isOpen)
    (fun x _ => Set.mem_iUnion.mpr (hmem x))
  refine ⟨t, ?_⟩
  intro x _
  obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ x))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨V, hV⟩, hx⟩

/-- The preimages of a covering family of opens cover the source. -/
private theorem top_le_iSup_preimage {X Y : Scheme.{u}} (f : X ⟶ Y) {ι : Type*}
    {U : ι → Y.Opens} (hU : (⊤ : Y.Opens) ≤ iSup U) : (⊤ : X.Opens) ≤ ⨆ i, f ⁻¹ᵁ U i := by
  intro y _
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp (hU (Set.mem_univ (f y)))
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨i, hi⟩

/-- On the absolute weak normalization of a quasi-compact quasi-separated scheme in which the
prime `p` vanishes, every global function has a `pⁿ`-th power pulled back from the scheme.

The affine case is glued along a finite affine open covering: the local preimages agree on the
pairwise intersections up to a nilpotent section, which a further `pᵏ`-th power kills because
the intersections are quasi-compact. -/
private theorem exists_pow_eq_appTop_of_compactSpace (Z : Scheme.{u}) [CompactSpace Z]
    [QuasiSeparatedSpace Z] (hZ : (p : Γ(Z, ⊤)) = 0) (g : Γ(Z.absoluteWeakNormalization, ⊤)) :
    ∃ (n : ℕ) (a : Γ(Z, ⊤)), g ^ p ^ n = Z.absoluteWeakNormalizationHom.appTop a := by
  classical
  let π := Z.absoluteWeakNormalizationHom
  let Y := Z.absoluteWeakNormalization
  obtain ⟨t, hcov⟩ := exists_finset_affineOpens_top_le Z
  let U : { V // V ∈ t } → Z.Opens := fun i => i.1.1
  choose n a ha using fun i : { V // V ∈ t } =>
    exists_pow_eq_app_of_isAffineOpen p hZ i.1.2
      (Y.presheaf.map (homOfLE le_top : π ⁻¹ᵁ U i ⟶ ⊤).op g)
  let N := Finset.univ.sup n
  have hN (i : { V // V ∈ t }) : n i ≤ N := Finset.le_sup (Finset.mem_univ i)
  have ha' (i : { V // V ∈ t }) :
      (Y.presheaf.map (homOfLE le_top : π ⁻¹ᵁ U i ⟶ ⊤).op g) ^ p ^ N =
        π.app (U i) (a i ^ p ^ (N - n i)) := by
    rw [map_pow, ← ha, ← pow_mul, ← pow_add, Nat.add_sub_cancel' (hN i)]
  have hres (i : { V // V ∈ t }) (W : Z.Opens) (hW : W ≤ U i) :
      π.app W (Z.presheaf.map (homOfLE hW).op (a i ^ p ^ (N - n i))) =
        (Y.presheaf.map (homOfLE le_top : π ⁻¹ᵁ W ⟶ ⊤).op g) ^ p ^ N := by
    rw [app_map_apply, ← ha', map_pow, ← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl
  -- the local preimages differ by nilpotents on the overlaps
  have hd (i j : { V // V ∈ t }) : IsNilpotent
      (Z.presheaf.map (homOfLE inf_le_left : U i ⊓ U j ⟶ U i).op (a i ^ p ^ (N - n i)) -
        Z.presheaf.map (homOfLE inf_le_right : U i ⊓ U j ⟶ U j).op (a j ^ p ^ (N - n j))) := by
    refine isNilpotent_of_absoluteWeakNormalizationHom_app_eq_zero
      (QuasiSeparatedSpace.inter_isCompact _ _ (U i).isOpen i.1.2.isCompact (U j).isOpen
        j.1.2.isCompact) _ ?_
    change π.app _ (_ - _) = 0
    rw [map_sub, hres, hres, sub_self]
  choose k hk using fun i j => exists_pow_prime_pow_eq_zero p (hd i j)
  let K := Finset.univ.sup fun i => Finset.univ.sup fun j => k i j
  have hK (i j : { V // V ∈ t }) : k i j ≤ K :=
    (Finset.le_sup (f := fun j => k i j) (Finset.mem_univ j)).trans
      (Finset.le_sup (f := fun i => Finset.univ.sup fun j => k i j) (Finset.mem_univ i))
  have hcompat : TopCat.Presheaf.IsCompatible Z.sheaf.1 U
      (fun i => (a i ^ p ^ (N - n i)) ^ p ^ K) := by
    intro i j
    have h := pow_prime_pow_eq_of_sub_pow_eq_zero p
      (Stacks.Frobenius.cast_eq_zero_of_isInCharacteristic hZ _) (hk i j) (hK i j)
    rwa [← map_pow, ← map_pow] at h
  obtain ⟨c, hc, -⟩ := Z.sheaf.existsUnique_gluing' U ⊤ (fun i => homOfLE le_top) hcov _ hcompat
  refine ⟨N + K, c, ?_⟩
  refine Y.sheaf.eq_of_locally_eq' (fun i => π ⁻¹ᵁ U i) ⊤ (fun i => homOfLE le_top)
    (top_le_iSup_preimage π hcov) _ _ fun i => ?_
  have hc' : Z.presheaf.map (homOfLE le_top : U i ⟶ ⊤).op c = (a i ^ p ^ (N - n i)) ^ p ^ K :=
    hc i
  have hci := app_map_apply π (le_top : U i ≤ ⊤) c
  rw [hc', map_pow, ← ha'] at hci
  change Y.presheaf.map (homOfLE le_top : π ⁻¹ᵁ U i ⟶ ⊤).op (g ^ p ^ (N + K)) = _
  rw [map_pow, pow_add, pow_mul, hci]
  rfl

end QcqsRoots

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The presheaf `colim_F Γ(-, 𝒪)` -/

/-- The presheaf of rings of global functions on the big h category over `S`. -/
public abbrev sectionsRingPresheaf : (BigHOver B S hS)ᵒᵖ ⥤ CommRingCat.{u} :=
  (BigHOver.toScheme B S hS).op ⋙ Scheme.Γ

/-- The Frobenius `a ↦ a ^ p` of the presheaf of global functions.  Over `𝔽_p` this is pullback
of functions along the absolute Frobenius. -/
public def frobeniusSectionsHom (p : ℕ) :
    globalFunctions B S hS ⟶ globalFunctions B S hS :=
  Presheaf.frobeniusForget (sectionsRingPresheaf B S hS) p

/-- The Frobenius of the presheaf of global functions raises a global function to its `p`-th
power. -/
public theorem frobeniusSectionsHom_app (p : ℕ) (X : (BigHOver B S hS)ᵒᵖ)
    (a : ToType ((sectionsRingPresheaf B S hS).obj X)) :
    (frobeniusSectionsHom B S hS p).app X a = a ^ p :=
  rfl

/-- The Frobenius tower `Γ(-, 𝒪) →^F Γ(-, 𝒪) →^F ⋯` of presheaves on the big h category. -/
public def frobeniusSectionsSequence (p : ℕ) : ℕ ⥤ ((BigHOver B S hS)ᵒᵖ ⥤ Type u) :=
  Functor.ofSequence (X := fun _ ↦ globalFunctions B S hS)
    (fun _ ↦ frobeniusSectionsHom B S hS p)

/-- Every stage of the Frobenius tower is the presheaf of global functions. -/
public theorem frobeniusSectionsSequence_obj (p : ℕ) (n : ℕ) :
    (frobeniusSectionsSequence B S hS p).obj n = globalFunctions B S hS :=
  rfl

/-- Every transition map of the Frobenius tower is the Frobenius. -/
public theorem frobeniusSectionsSequence_map_succ (p : ℕ) (n : ℕ) :
    (frobeniusSectionsSequence B S hS p).map (homOfLE n.le_succ) =
      frobeniusSectionsHom B S hS p :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- The presheaf `colim_F Γ(-, 𝒪)` on the big h category over `S`: the colimit of the Frobenius
tower of the presheaf of global functions. -/
public def frobeniusColimitSections (p : ℕ) : (BigHOver B S hS)ᵒᵖ ⥤ Type u :=
  colimit (frobeniusSectionsSequence B S hS p)

/-- The sections of `colim_F Γ(-, 𝒪)` over an object are the colimit of the Frobenius tower of
its ring of global functions: colimits of presheaves are computed objectwise. -/
public def frobeniusColimitSectionsObjIso (p : ℕ) (X : (BigHOver B S hS)ᵒᵖ) :
    (frobeniusColimitSections B S hS p).obj X ≅
      colimit (frobeniusSectionsSequence B S hS p ⋙ (evaluation _ _).obj X) :=
  colimitObjIsoColimitCompEvaluation _ _

/-! ### Locality of bijectivity on affine objects -/

/-- Part of the argument of Stacks 0EU4: every object of the big h category over `S` is covered
by objects with affine underlying scheme, that is, the inclusion of the big affine h site is
cover dense. -/
public theorem isCoverDense_inclusion :
    (BigAffineH.inclusion B S hS).IsCoverDense (BigHOver.topology B S hS) :=
  Functor.IsDenseSubsite.isCoverDense (BigAffineH.topology B S hS)
    (BigHOver.topology B S hS) (BigAffineH.inclusion B S hS)

variable {B S hS}

/-- A map of presheaves on the big h category over `S` which is injective on every object with
affine underlying scheme is locally injective for the h topology. -/
public theorem isLocallyInjective_of_injective_isAffine
    {P F : (BigHOver B S hS)ᵒᵖ ⥤ Type u} (φ : P ⟶ F)
    (h : ∀ X : BigHOver B S hS, IsAffine ((BigHOver.toScheme B S hS).obj X) →
      Function.Injective (φ.app (op X))) :
    Presheaf.IsLocallyInjective (BigHOver.topology B S hS) φ := by
  have := isCoverDense_inclusion B S hS
  constructor
  intro X a b hab
  refine (BigHOver.topology B S hS).superset_covering ?_
    ((BigAffineH.inclusion B S hS).is_cover_of_isCoverDense
      (BigHOver.topology B S hS) X.unop)
  rintro Y f ⟨⟨Z, l, m, fac⟩⟩
  change P.map f.op a = P.map f.op b
  have hm : P.map m.op a = P.map m.op b := by
    refine h ((BigAffineH.inclusion B S hS).obj Z) Z.property ?_
    rw [NatTrans.naturality_apply φ m.op a, NatTrans.naturality_apply φ m.op b, hab]
  have hf : f.op = m.op ≫ l.op := by rw [← op_comp, fac]
  rw [hf, P.map_comp, ConcreteCategory.comp_apply, ConcreteCategory.comp_apply, hm]

/-- A map of presheaves on the big h category over `S` which is surjective on every object with
affine underlying scheme is locally surjective for the h topology. -/
public theorem isLocallySurjective_of_surjective_isAffine
    {P F : (BigHOver B S hS)ᵒᵖ ⥤ Type u} (φ : P ⟶ F)
    (h : ∀ X : BigHOver B S hS, IsAffine ((BigHOver.toScheme B S hS).obj X) →
      Function.Surjective (φ.app (op X))) :
    Presheaf.IsLocallySurjective (BigHOver.topology B S hS) φ := by
  have := isCoverDense_inclusion B S hS
  constructor
  intro X s
  refine (BigHOver.topology B S hS).superset_covering ?_
    ((BigAffineH.inclusion B S hS).is_cover_of_isCoverDense (BigHOver.topology B S hS) X)
  rintro Y f ⟨⟨Z, l, m, fac⟩⟩
  obtain ⟨a, ha⟩ :=
    h ((BigAffineH.inclusion B S hS).obj Z) Z.property (F.map m.op s)
  refine ⟨P.map l.op a, ?_⟩
  have hf : f.op = m.op ≫ l.op := by rw [← op_comp, fac]
  rw [NatTrans.naturality_apply φ l.op a, ha, hf, F.map_comp, ConcreteCategory.comp_apply]

/-! ### Uniqueness -/

/-- If `φ : P ⟶ F` is locally bijective into a sheaf `F`, then maps `χ : F ⟶ G`, `χ' : G ⟶ F`
compatible with `φ` and `ψ : P ⟶ G` compose to the identity of `F`. -/
private theorem comp_eq_id_of_isLocallyBijective {C : Type*} [Category* C]
    (J : GrothendieckTopology C) {P F G : Cᵒᵖ ⥤ Type u} (φ : P ⟶ F) (ψ : P ⟶ G)
    [Presheaf.IsLocallyInjective J φ] [Presheaf.IsLocallySurjective J φ]
    (hF : Presheaf.IsSheaf J F) (χ : F ⟶ G) (χ' : G ⟶ F) (hχ : φ ≫ χ = ψ) (hχ' : ψ ≫ χ' = φ) :
    χ ≫ χ' = 𝟙 F := by
  obtain ⟨_, -, hu⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective J φ φ hF
  exact (hu _ (by change φ ≫ χ ≫ χ' = φ; rw [← Category.assoc, hχ, hχ'])).trans
    (hu (𝟙 F) (Category.comp_id φ)).symm

/-- Two sheaves on the big h site over `S` which receive a map from a common presheaf that is
bijective on every object with affine underlying scheme are isomorphic, by a unique isomorphism
compatible with the two maps. -/
public theorem existsUnique_iso_of_bijective_isAffine
    {P F G : (BigHOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigHOver.topology B S hS) G)
    (φ : P ⟶ F) (ψ : P ⟶ G)
    (hφ : ∀ X : BigHOver B S hS, IsAffine ((BigHOver.toScheme B S hS).obj X) →
      Function.Bijective (φ.app (op X)))
    (hψ : ∀ X : BigHOver B S hS, IsAffine ((BigHOver.toScheme B S hS).obj X) →
      Function.Bijective (ψ.app (op X))) :
    ∃! e : F ≅ G, φ ≫ e.hom = ψ := by
  have := isLocallyInjective_of_injective_isAffine φ fun X hX ↦ (hφ X hX).1
  have := isLocallySurjective_of_surjective_isAffine φ fun X hX ↦ (hφ X hX).2
  have := isLocallyInjective_of_injective_isAffine ψ fun X hX ↦ (hψ X hX).1
  have := isLocallySurjective_of_surjective_isAffine ψ fun X hX ↦ (hψ X hX).2
  obtain ⟨χ, hχ, hχu⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective
    (BigHOver.topology B S hS) φ ψ hG
  obtain ⟨χ', hχ', -⟩ := Presheaf.existsUnique_hom_of_isLocallyBijective
    (BigHOver.topology B S hS) ψ φ hF
  have hFF := comp_eq_id_of_isLocallyBijective _ φ ψ hF χ χ' hχ hχ'
  have hGG := comp_eq_id_of_isLocallyBijective _ ψ φ hG χ' χ hχ' hχ
  exact ⟨⟨χ, χ', hFF, hGG⟩, hχ, fun e he ↦ Iso.ext (hχu e.hom he)⟩

/-! ### The h sheaf `X ↦ Γ(Xᵃʷⁿ, 𝒪)` -/

variable (B S hS)

/-- The presheaf of sets `X ↦ Γ(Xᵃʷⁿ, 𝒪)` on the big h category over `S`. -/
public abbrev awnSections : (BigHOver B S hS)ᵒᵖ ⥤ Type u :=
  absoluteWeakNormalizationSectionsOver (BigHOver.toScheme B S hS) ⋙
    CategoryTheory.forget CommRingCat.{u}

/-- The presheaf `X ↦ Γ(Xᵃʷⁿ, 𝒪)` is a sheaf for the h topology.

This is the h analogue of Stacks 0EVT, and is proved from the same two descent statements:
Zariski descent and descent along a proper surjection onto an affine scheme, assembled by the
sheaf criterion Stacks 0EU5. -/
public theorem isSheaf_awnSections :
    Presheaf.IsSheaf (BigHOver.topology B S hS) (awnSections B S hS) := by
  let := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  have _ : PreservesLimitsOfShape WalkingCospan (BigHOver.toScheme B S hS) := inferInstance
  have hP : awnSections B S hS =
      (BigHOver.toScheme B S hS).op ⋙ absoluteWeakNormalizationSectionTypes := rfl
  have hz : IsZariskiSheaf B S hS (awnSections B S hS) := by
    intro X E hE
    rw [hP, Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks (BigHOver.toScheme B S hS)
      absoluteWeakNormalizationSectionTypes E.presieve₀, ← PreZeroHypercover.presieve₀_map]
    exact isSheafFor_absoluteWeakNormalizationSections_of_zariskiCover (E.map _).f hE
  refine (isSheaf_iff_isZariskiSheaf_and_isProperFinitePresentationSheaf B S hS _).mpr
    ⟨hz, isProperFinitePresentationSheaf_of_affine hz ?_⟩
  intro X Y f hX hf hsurj _
  have _ : IsAffine ((BigHOver.toScheme B S hS).obj X) := hX
  have _ : IsProper ((BigHOver.toScheme B S hS).map f) := hf
  have _ : Surjective ((BigHOver.toScheme B S hS).map f) := hsurj
  rw [hP, Presieve.IsSheafFor.comp_iff_of_preservesPairwisePullbacks (BigHOver.toScheme B S hS)
    absoluteWeakNormalizationSectionTypes, Presieve.map_singleton,
    ← Presieve.ofArrows_pUnit.{0}]
  exact isSheafFor_absoluteWeakNormalizationSections_of_properSurjective _

/-- The canonical map `Γ(X, 𝒪) ⟶ Γ(Xᵃʷⁿ, 𝒪)` of presheaves of sets. -/
public def awnUnit : globalFunctions B S hS ⟶ awnSections B S hS :=
  Functor.whiskerRight (absoluteWeakNormalizationSectionsMap (BigHOver.toScheme B S hS))
    (CategoryTheory.forget CommRingCat.{u})

/-- The canonical map pulls a function back along the absolute weak normalization. -/
public theorem awnUnit_app (X : BigHOver B S hS) (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) :
    (awnUnit B S hS).app (op X) a =
      ((BigHOver.toScheme B S hS).obj X).absoluteWeakNormalizationHom.appTop a :=
  rfl

/-- The Frobenius `a ↦ a ^ p` of the presheaf `X ↦ Γ(Xᵃʷⁿ, 𝒪)`. -/
public def awnFrobenius (p : ℕ) : awnSections B S hS ⟶ awnSections B S hS :=
  Presheaf.frobeniusForget (absoluteWeakNormalizationSectionsOver (BigHOver.toScheme B S hS)) p

/-- The Frobenius of `X ↦ Γ(Xᵃʷⁿ, 𝒪)` raises a function to its `p`-th power. -/
public theorem awnFrobenius_app (p : ℕ) (X : BigHOver B S hS)
    (a : Γ(((BigHOver.toScheme B S hS).obj X).absoluteWeakNormalization, ⊤)) :
    (awnFrobenius B S hS p).app (op X) a = a ^ p :=
  rfl

/-- Pulling back along the absolute weak normalization commutes with the two Frobenius maps. -/
public theorem frobeniusSectionsHom_comp_awnUnit (p : ℕ) :
    frobeniusSectionsHom B S hS p ≫ awnUnit B S hS = awnUnit B S hS ≫ awnFrobenius B S hS p := by
  ext X a
  exact map_pow ((BigHOver.toScheme B S hS).obj X.unop).absoluteWeakNormalizationHom.appTop.hom
    (show Γ((BigHOver.toScheme B S hS).obj X.unop, ⊤) from a) p

variable {B S hS}

/-- On the big h site over a scheme in which the prime `p` vanishes, every object has `p`
vanishing in its global functions. -/
public theorem natCast_eq_zero_of_isInCharacteristic {p : ℕ}
    (hSp : Stacks.Frobenius.IsInCharacteristic S p) (X : BigHOver B S hS) :
    (p : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) = 0 := by
  simpa only [map_natCast, map_zero] using
    congrArg (fun a : Γ(S, ⊤) => (B.inclusion.map X.hom).appTop.hom a) hSp

variable (B S hS)

/-- Over a scheme in characteristic `p`, the Frobenius of `X ↦ Γ(Xᵃʷⁿ, 𝒪)` is an isomorphism. -/
public theorem isIso_awnFrobenius (p : ℕ) [Fact p.Prime]
    (hSp : Stacks.Frobenius.IsInCharacteristic S p) : IsIso (awnFrobenius B S hS p) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro X
  rw [isIso_iff_bijective]
  exact pow_bijective_absoluteWeakNormalization p _
    (natCast_eq_zero_of_isInCharacteristic hSp X.unop)

/-! ### The comparison `colim_F Γ(X, 𝒪) ⟶ Γ(Xᵃʷⁿ, 𝒪)` -/

section Comparison

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)

/-- The inverse of the Frobenius of `X ↦ Γ(Xᵃʷⁿ, 𝒪)`, taking `p`-th roots. -/
public def awnFrobeniusInv : awnSections B S hS ⟶ awnSections B S hS :=
  haveI := isIso_awnFrobenius B S hS p hSp
  inv (awnFrobenius B S hS p)

/-- Taking the `p`-th power of a `p`-th root gives back the function. -/
public theorem awnFrobeniusInv_pow (X : BigHOver B S hS)
    (a : Γ(((BigHOver.toScheme B S hS).obj X).absoluteWeakNormalization, ⊤)) :
    (show Γ(((BigHOver.toScheme B S hS).obj X).absoluteWeakNormalization, ⊤) from
      (awnFrobeniusInv B S hS p hSp).app (op X) a) ^ p = a := by
  have := isIso_awnFrobenius B S hS p hSp
  exact ConcreteCategory.congr_hom (congr_app (IsIso.inv_hom_id (awnFrobenius B S hS p)) (op X)) a

/-- The stages of the comparison: the stage `n` sends `a` to the `pⁿ`-th root of its pullback to
the absolute weak normalization. -/
public def awnStage : ℕ → (globalFunctions B S hS ⟶ awnSections B S hS)
  | 0 => awnUnit B S hS
  | n + 1 => awnStage n ≫ awnFrobeniusInv B S hS p hSp

/-- The stage `n` image of a global function, as a global function on the absolute weak
normalization. -/
public def awnStageFun (n : ℕ) (X : BigHOver B S hS) (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) :
    Γ(((BigHOver.toScheme B S hS).obj X).absoluteWeakNormalization, ⊤) :=
  (awnStage B S hS p hSp n).app (op X) a

/-- The `pⁿ`-th power of the stage `n` image of `a` is the pullback of `a`. -/
public theorem awnStageFun_pow (n : ℕ) (X : BigHOver B S hS)
    (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) :
    awnStageFun B S hS p hSp n X a ^ p ^ n =
      ((BigHOver.toScheme B S hS).obj X).absoluteWeakNormalizationHom.appTop a := by
  induction n with
  | zero => exact pow_one _
  | succ n ih =>
    have h : awnStageFun B S hS p hSp (n + 1) X a ^ p =
        awnStageFun B S hS p hSp n X a :=
      awnFrobeniusInv_pow B S hS p hSp X _
    rw [pow_succ', pow_mul, h, ih]

/-- The stages are compatible with the Frobenius transition maps. -/
public theorem frobeniusSectionsHom_comp_awnStage (n : ℕ) :
    frobeniusSectionsHom B S hS p ≫ awnStage B S hS p hSp (n + 1) =
      awnStage B S hS p hSp n := by
  induction n with
  | zero =>
    have := isIso_awnFrobenius B S hS p hSp
    change frobeniusSectionsHom B S hS p ≫ awnUnit B S hS ≫ inv (awnFrobenius B S hS p) =
      awnUnit B S hS
    rw [← Category.assoc, frobeniusSectionsHom_comp_awnUnit, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  | succ n ih =>
    change frobeniusSectionsHom B S hS p ≫ awnStage B S hS p hSp (n + 1) ≫
        awnFrobeniusInv B S hS p hSp = awnStage B S hS p hSp (n + 1)
    rw [← Category.assoc, ih]
    rfl

/-- The cocone on the Frobenius tower with vertex `X ↦ Γ(Xᵃʷⁿ, 𝒪)` given by the stages. -/
public def awnCocone : Cocone (frobeniusSectionsSequence B S hS p) where
  pt := awnSections B S hS
  ι := NatTrans.ofSequence (fun n => awnStage B S hS p hSp n) (fun n => by
    rw [frobeniusSectionsSequence_map_succ]
    exact (frobeniusSectionsHom_comp_awnStage B S hS p hSp n).trans (Category.comp_id _).symm)

/-- The comparison `colim_F Γ(X, 𝒪) ⟶ Γ(Xᵃʷⁿ, 𝒪)`. -/
public def awnComparison : frobeniusColimitSections B S hS p ⟶ awnSections B S hS :=
  colimit.desc (frobeniusSectionsSequence B S hS p) (awnCocone B S hS p hSp)

end Comparison

section Elements

variable (p : ℕ)

/-- The stage `n` representative in `colim_F Γ(X, 𝒪)` of a global function on `X`. -/
public def colimitStage (n : ℕ) (X : BigHOver B S hS)
    (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) : (frobeniusColimitSections B S hS p).obj (op X) :=
  (colimit.ι (frobeniusSectionsSequence B S hS p) n).app (op X) a

/-- Every section of `colim_F Γ(-, 𝒪)` over an object is represented at some stage. -/
public theorem exists_colimitStage_eq (X : BigHOver B S hS)
    (x : (frobeniusColimitSections B S hS p).obj (op X)) :
    ∃ (n : ℕ) (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)), colimitStage B S hS p n X a = x := by
  let e := colimitObjIsoColimitCompEvaluation (frobeniusSectionsSequence B S hS p) (op X)
  obtain ⟨n, a, ha⟩ := Types.jointly_surjective' (e.hom x)
  refine ⟨n, a, ?_⟩
  have h' := ConcreteCategory.congr_hom
    (colimitObjIsoColimitCompEvaluation_ι_inv (frobeniusSectionsSequence B S hS p) n (op X)) a
  exact h'.symm.trans ((congrArg (fun t => e.inv t) ha).trans (e.hom_inv_id_apply x))

/-- Moving a representative one stage up raises it to the `p`-th power. -/
public theorem colimitStage_succ (n : ℕ) (X : BigHOver B S hS)
    (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) :
    colimitStage B S hS p n X a = colimitStage B S hS p (n + 1) X (a ^ p) := by
  have h := colimit.w (frobeniusSectionsSequence B S hS p) (homOfLE (Nat.le_add_right n 1))
  rw [frobeniusSectionsSequence_map_succ] at h
  exact (ConcreteCategory.congr_hom (congr_app h (op X)) a).symm

/-- Moving a representative `k` stages up raises it to the `pᵏ`-th power. -/
public theorem colimitStage_add (n k : ℕ) (X : BigHOver B S hS)
    (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) :
    colimitStage B S hS p n X a = colimitStage B S hS p (n + k) X (a ^ p ^ k) := by
  induction k with
  | zero =>
    rw [pow_zero, pow_one]
    rfl
  | succ k ih =>
    rw [ih, colimitStage_succ, ← pow_mul, ← pow_succ]
    rfl

end Elements

section Bijective

variable (p : ℕ) [Fact p.Prime] (hSp : Stacks.Frobenius.IsInCharacteristic S p)

/-- The comparison sends the stage `n` representative of `a` to its stage `n` image. -/
public theorem awnComparison_colimitStage (n : ℕ) (X : BigHOver B S hS)
    (a : Γ((BigHOver.toScheme B S hS).obj X, ⊤)) :
    (awnComparison B S hS p hSp).app (op X) (colimitStage B S hS p n X a) =
      awnStageFun B S hS p hSp n X a :=
  ConcreteCategory.congr_hom (congr_app (colimit.ι_desc (awnCocone B S hS p hSp) n) (op X)) a

/-- Over a scheme in characteristic `p`, the comparison `colim_F Γ(X, 𝒪) ⟶ Γ(Xᵃʷⁿ, 𝒪)` is
bijective on every object whose underlying scheme is quasi-compact and quasi-separated. -/
public theorem bijective_awnComparison_app (X : BigHOver B S hS)
    [CompactSpace ((BigHOver.toScheme B S hS).obj X)]
    [QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj X)] :
    Function.Bijective ((awnComparison B S hS p hSp).app (op X)) := by
  let Z := (BigHOver.toScheme B S hS).obj X
  have hZ : (p : Γ(Z, ⊤)) = 0 := natCast_eq_zero_of_isInCharacteristic hSp X
  let c : (frobeniusColimitSections B S hS p).obj (op X) → Γ(Z.absoluteWeakNormalization, ⊤) :=
    fun x => (awnComparison B S hS p hSp).app (op X) x
  have hpow (k : ℕ) : Function.Injective (fun s : Γ(Z.absoluteWeakNormalization, ⊤) =>
      s ^ p ^ k) := by
    induction k with
    | zero => exact fun s t hst => by simpa using hst
    | succ k ih =>
      intro s t hst
      have hst' : (s ^ p) ^ p ^ k = (t ^ p) ^ p ^ k := by
        change s ^ p ^ (k + 1) = t ^ p ^ (k + 1) at hst
        rwa [pow_succ', pow_mul, pow_mul] at hst
      exact (pow_bijective_absoluteWeakNormalization p Z hZ).1 (ih hst')
  suffices hc : Function.Bijective c from hc
  refine ⟨fun x y hxy => ?_, fun g => ?_⟩
  · obtain ⟨n, a, rfl⟩ := exists_colimitStage_eq B S hS p X x
    obtain ⟨m, b, rfl⟩ := exists_colimitStage_eq B S hS p X y
    rw [colimitStage_add B S hS p n m, colimitStage_add B S hS p m n, Nat.add_comm m n]
    have hxy' : awnStageFun B S hS p hSp (n + m) X (a ^ p ^ m) =
        awnStageFun B S hS p hSp (n + m) X (b ^ p ^ n) := by
      rw [← awnComparison_colimitStage, ← awnComparison_colimitStage, ← colimitStage_add,
        Nat.add_comm n m, ← colimitStage_add]
      exact hxy
    have hpull : Z.absoluteWeakNormalizationHom.appTop (a ^ p ^ m) =
        Z.absoluteWeakNormalizationHom.appTop (b ^ p ^ n) := by
      rw [← awnStageFun_pow B S hS p hSp (n + m), ← awnStageFun_pow B S hS p hSp (n + m), hxy']
    have hnil : IsNilpotent (a ^ p ^ m - b ^ p ^ n) := by
      refine isNilpotent_of_absoluteWeakNormalizationHom_app_eq_zero
        (W := ⊤) isCompact_univ (a ^ p ^ m - b ^ p ^ n) ?_
      have h0 : Z.absoluteWeakNormalizationHom.appTop (a ^ p ^ m - b ^ p ^ n) = 0 := by
        rw [map_sub, hpull, sub_self]
      exact h0
    obtain ⟨k, hk⟩ := exists_pow_prime_pow_eq_zero p hnil
    rw [sub_pow_prime_pow p hZ, sub_eq_zero] at hk
    rw [colimitStage_add B S hS p (n + m) k, colimitStage_add B S hS p (n + m) k, hk]
  · obtain ⟨n, a, ha⟩ := exists_pow_eq_appTop_of_compactSpace p Z hZ g
    refine ⟨colimitStage B S hS p n X a, ?_⟩
    apply hpow n
    change c (colimitStage B S hS p n X a) ^ p ^ n = g ^ p ^ n
    have h1 : c (colimitStage B S hS p n X a) = awnStageFun B S hS p hSp n X a :=
      awnComparison_colimitStage B S hS p hSp n X a
    rw [h1, awnStageFun_pow, ha]

end Bijective

variable {B S hS} in
/-- Two sheaves on the big h site over `S` whose sections over every quasi-compact
quasi-separated object are identified with `colim_F Γ(X, 𝒪_X)`, compatibly with restriction, are
isomorphic by a unique isomorphism compatible with the identifications.  This holds for every
`p` and every `S`. -/
public theorem existsUnique_iso_of_bijective_qcqs (p : ℕ)
    {F G : (BigHOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : Presheaf.IsSheaf (BigHOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigHOver.topology B S hS) G)
    (φ : frobeniusColimitSections B S hS p ⟶ F)
    (ψ : frobeniusColimitSections B S hS p ⟶ G)
    (hφ : ∀ X : BigHOver B S hS,
      CompactSpace ((BigHOver.toScheme B S hS).obj X) →
      QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj X) →
      Function.Bijective (φ.app (op X)))
    (hψ : ∀ X : BigHOver B S hS,
      CompactSpace ((BigHOver.toScheme B S hS).obj X) →
      QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj X) →
      Function.Bijective (ψ.app (op X))) :
    ∃! e : F ≅ G, φ ≫ e.hom = ψ :=
  existsUnique_iso_of_bijective_isAffine hF hG φ ψ
    (fun X hX ↦ hφ X (by have := hX; infer_instance) (by have := hX; infer_instance))
    (fun X hX ↦ hψ X (by have := hX; infer_instance) (by have := hX; infer_instance))

/-- **Stacks 0EVK.** Let `p` be a prime number, let `S` be a scheme over `𝔽_p` (that is, `p`
vanishes in `Γ(S, 𝒪_S)`), and let `(Sch/S)_h` be a big h site over `S` as in Stacks 0EU1.  There
is a unique sheaf `ℱ` on `(Sch/S)_h` such that `ℱ(X) = colim_F Γ(X, 𝒪_X)` for every quasi-compact
quasi-separated object `X`.

The identification is a morphism of presheaves `colim_F Γ(-, 𝒪) ⟶ ℱ` that is bijective on
quasi-compact quasi-separated objects, so naturality in `X` expresses compatibility with
restriction.  The first conjunct is existence and the second is uniqueness: two such sheaves are
isomorphic, by a unique isomorphism compatible with the identifications.

The sheaf constructed is `X ↦ Γ(Xᵃʷⁿ, 𝒪)`, global functions on the absolute weak normalization.
The proof does not use the criterion of Stacks 0EVI, whose sufficiency direction this
development lacks; it uses the absolute weak normalization instead.  The sheaf property comes
from the descent statements behind Stacks 0EVT and the h-sheaf criterion Stacks 0EU5.  The
comparison `colim_F Γ(X, 𝒪_X) ⟶ Γ(Xᵃʷⁿ, 𝒪)` is bijective on quasi-compact quasi-separated `X`.
On an affine open this is Stacks 0EVW, and the affine pieces glue over a finite affine covering
because the overlaps are quasi-compact. -/
@[stacks 0EVK]
public theorem existsUnique_iso_frobeniusColimitSections (p : ℕ) (hp : p.Prime)
    (hSp : Stacks.Frobenius.IsInCharacteristic S p) :
    (∃ (F : (BigHOver B S hS)ᵒᵖ ⥤ Type u) (φ : frobeniusColimitSections B S hS p ⟶ F),
      Presheaf.IsSheaf (BigHOver.topology B S hS) F ∧
        ∀ X : BigHOver B S hS, CompactSpace ((BigHOver.toScheme B S hS).obj X) →
          QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj X) →
            Function.Bijective (φ.app (op X))) ∧
    ∀ {F G : (BigHOver B S hS)ᵒᵖ ⥤ Type u}
      (φ : frobeniusColimitSections B S hS p ⟶ F) (ψ : frobeniusColimitSections B S hS p ⟶ G),
      Presheaf.IsSheaf (BigHOver.topology B S hS) F →
      Presheaf.IsSheaf (BigHOver.topology B S hS) G →
      (∀ X : BigHOver B S hS, CompactSpace ((BigHOver.toScheme B S hS).obj X) →
        QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj X) →
          Function.Bijective (φ.app (op X))) →
      (∀ X : BigHOver B S hS, CompactSpace ((BigHOver.toScheme B S hS).obj X) →
        QuasiSeparatedSpace ((BigHOver.toScheme B S hS).obj X) →
          Function.Bijective (ψ.app (op X))) →
      ∃! e : F ≅ G, φ ≫ e.hom = ψ := by
  have : Fact p.Prime := ⟨hp⟩
  refine ⟨⟨awnSections B S hS, awnComparison B S hS p hSp, isSheaf_awnSections B S hS,
    fun X _ _ ↦ bijective_awnComparison_app B S hS p hSp X⟩, ?_⟩
  intro F G φ ψ hF hG hφ hψ
  exact existsUnique_iso_of_bijective_qcqs p hF hG φ ψ hφ hψ

end BigHOver

end AlgebraicGeometry

end
