module

public import Mathlib.AlgebraicGeometry.GammaSpecAdjunction
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.FieldTheory.Galois.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EquivalenceRelations
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# The twisted doubled origin of a quadratic Galois extension

Let `K/k` be a degree two Galois extension with nonidentity automorphism `σ`, let
`S = Spec k[x]` and let `U = Spec K[x]`.  The fibre product `U ×_S U` is the disjoint union
of the diagonal `Δ(U)` and of the twisted diagonal `Δ'(U)`, the graph of `σ`.  Retaining
the diagonal in full but the twisted diagonal only away from the `K`-rational origin of `U`
gives an étale equivalence relation `R = Δ(U) ⨿ Δ'(U ∖ {0})` on `U` over `S`, and the
quotient `X = U/R` is an algebraic space over `S` which is not a scheme.

This file constructs the data of that example: the two affine lines, the puncture, the
Galois automorphism of the chart, the relation scheme, the pre-relation it defines over the
base, and the quotient sheaf.

## Main definitions

* `AlgebraicGeometry.TwistedDoubledOrigin.base` and
  `AlgebraicGeometry.TwistedDoubledOrigin.cover` are the affine lines `S = Spec k[x]` and
  `U = Spec K[x]`, and `AlgebraicGeometry.TwistedDoubledOrigin.coverMap` is the map `U ⟶ S`
  induced by the extension.
* `AlgebraicGeometry.TwistedDoubledOrigin.puncturedCover` is the basic open `D(x)` of `U`,
  the complement of its `K`-rational origin, and
  `AlgebraicGeometry.TwistedDoubledOrigin.puncturedBase` is the corresponding open of `S`,
  with `AlgebraicGeometry.TwistedDoubledOrigin.baseOverBase`,
  `AlgebraicGeometry.TwistedDoubledOrigin.puncturedBaseOverBase` and
  `AlgebraicGeometry.TwistedDoubledOrigin.puncturedBaseInclusion` the corresponding objects
  and morphism over `S`.
* `AlgebraicGeometry.TwistedDoubledOrigin.galoisAction` is the automorphism of `U` induced
  by a Galois automorphism of `K`, and
  `AlgebraicGeometry.TwistedDoubledOrigin.galoisActionPuncturedMap` is its restriction to
  the puncture.
* `AlgebraicGeometry.TwistedDoubledOrigin.relationScheme` is `U ⨿ (U ∖ {0})`, and
  `AlgebraicGeometry.TwistedDoubledOrigin.relationOverBase` makes it a scheme over `S`.
* `AlgebraicGeometry.TwistedDoubledOrigin.relationFirst` and
  `AlgebraicGeometry.TwistedDoubledOrigin.relationSecond` are its two projections to `U`,
  the second one twisted by `σ`, and
  `AlgebraicGeometry.TwistedDoubledOrigin.twistedRelation` is the pre-relation they define.
* `AlgebraicGeometry.TwistedDoubledOrigin.quadraticGaloisTwistedDoubledOrigin` is the
  quotient sheaf `X = U/R` on a big fppf site over `S`.

## Main results

* `AlgebraicGeometry.TwistedDoubledOrigin.galoisAction_coverMap`: the Galois automorphism
  of the chart lies over the base, and
  `AlgebraicGeometry.TwistedDoubledOrigin.galoisAction_involutive` says that for a
  quadratic extension it is an involution.
* `AlgebraicGeometry.TwistedDoubledOrigin.coverMap_preimage_puncturedBase` and
  `AlgebraicGeometry.TwistedDoubledOrigin.galoisAction_preimage_puncturedCover`: the
  puncture of the chart is the preimage of the puncture of the base and is preserved by the
  Galois automorphism.
* `AlgebraicGeometry.TwistedDoubledOrigin.twistedRelation_target` and
  `AlgebraicGeometry.TwistedDoubledOrigin.twistedRelation_source` identify the two maps to
  `U` which the pre-relation induces, and `relationFirst_inl`, `relationFirst_inr`,
  `relationSecond_inl`, `relationSecond_inr` compute them on each summand.

## Implementation notes

The nonidentity Galois automorphism is supplied explicitly rather than extracted from the
degree hypothesis, and the degree hypothesis itself is carried only by the quotient, where
the example needs it.  The puncture is the principal open `D(x)`, which is exactly the
complement of the rational origin.  The quotient is formed on a big fppf site over the
ground affine line, along the canonical inclusion of that site into `S`-schemes; the site
and the proof that it contains the base remain explicit data.  The four projection lemmas
identify the summands without unfolding the pre-relation.

## References

* [Stacks Project, Tag 03FN](https://stacks.math.columbia.edu/tag/03FN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.TwistedDoubledOrigin

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The affine line over the ground field, the base `S = Spec k[x]` of the example. -/
abbrev base : Scheme.{u} := Spec (.of (Polynomial k))

/-- The affine line over the quadratic extension, the chart `U = Spec K[x]` of the
example. -/
abbrev cover : Scheme.{u} := Spec (.of (Polynomial K))

/-- The map of affine lines `U ⟶ S` induced by the field extension. -/
def coverMap : cover K ⟶ base k :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k K)))

/-- The principal open `D(x)` of the chart, the complement of its rational origin. -/
abbrev puncturedCover : (cover K).Opens :=
  PrimeSpectrum.basicOpen (Polynomial.X : Polynomial K)

/-- The automorphism of the chart induced by a Galois automorphism of the extension. -/
def galoisAction (σ : K ≃ₐ[k] K) : cover K ⟶ cover K :=
  Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom σ.toRingEquiv.toRingHom))

/-- The automorphism of the chart induced by a Galois automorphism lies over the base,
because a `k`-algebra automorphism of `K` fixes `k`. -/
lemma galoisAction_coverMap (σ : K ≃ₐ[k] K) :
    galoisAction k K σ ≫ coverMap k K = coverMap k K := by
  dsimp [galoisAction, coverMap]
  rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, Polynomial.mapRingHom_comp,
    show (σ : K →+* K).comp (algebraMap k K) = algebraMap k K from
      RingHom.ext fun x => σ.commutes x]

/-- For a quadratic Galois extension the automorphism of the chart induced by any
automorphism of the extension is an involution. -/
lemma galoisAction_involutive [FiniteDimensional k K] [IsGalois k K]
    (hdegree : Module.finrank k K = 2) (σ : K ≃ₐ[k] K) :
    galoisAction k K σ ≫ galoisAction k K σ = 𝟙 _ := by
  have hσsq : σ.trans σ = 1 := by
    change σ * σ = 1
    simpa only [IsGalois.card_aut_eq_finrank, hdegree, pow_two] using
      (pow_card_eq_one' (x := σ))
  have hσring : (σ : K →+* K).comp (σ : K →+* K) = RingHom.id K :=
    RingHom.ext (AlgEquiv.ext_iff.mp hσsq)
  dsimp [galoisAction]
  rw [← Spec.map_comp, ← Spec.map_id, Spec.map_injective.eq_iff, ← CommRingCat.ofHom_comp,
    Polynomial.mapRingHom_comp, hσring]
  simp

/-- The automorphism of the chart induced by a Galois automorphism is an isomorphism, being
induced by a ring isomorphism. -/
instance isIso_galoisAction (σ : K ≃ₐ[k] K) : IsIso (galoisAction k K σ) := by
  let e : Polynomial K ≃+* Polynomial K := Polynomial.mapEquiv σ.toRingEquiv
  have he : (Scheme.Spec.mapIso e.toCommRingCatIso.op).hom = galoisAction k K σ := by
    dsimp [galoisAction]
    congr 1
  exact he ▸ (Scheme.Spec.mapIso e.toCommRingCatIso.op).isIso_hom

/-- The complement of the origin in the base. -/
abbrev puncturedBase : (base k).Opens :=
  PrimeSpectrum.basicOpen (Polynomial.X : Polynomial k)

/-- The base regarded as an object of its own slice category. -/
abbrev baseOverBase : Over (base k) := Over.mk (𝟙 (base k))

/-- The punctured base regarded as a scheme over the base. -/
abbrev puncturedBaseOverBase : Over (base k) := Over.mk (puncturedBase k).ι

/-- The inclusion of the punctured base into the base, as a morphism over the base. -/
def puncturedBaseInclusion : puncturedBaseOverBase k ⟶ baseOverBase k :=
  Over.homMk (puncturedBase k).ι (by simp [puncturedBaseOverBase, baseOverBase])

/-- The preimage of the principal open `D(x)` under the map of affine lines induced by a ring
homomorphism is again `D(x)`. -/
private theorem preimage_basicOpen_X {A B : Type u} [CommRing A] [CommRing B] (f : A →+* B) :
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom f)) ⁻¹ᵁ
      PrimeSpectrum.basicOpen (Polynomial.X : Polynomial A) =
        PrimeSpectrum.basicOpen (Polynomial.X : Polynomial B) := by
  rw [SpecMap_preimage_basicOpen]
  exact congrArg PrimeSpectrum.basicOpen (Polynomial.map_X f)

/-- The puncture of the chart is the preimage of the puncture of the base. -/
lemma coverMap_preimage_puncturedBase :
    (coverMap k K) ⁻¹ᵁ puncturedBase k = puncturedCover K :=
  preimage_basicOpen_X (algebraMap k K)

/-- The automorphism of the chart induced by a Galois automorphism preserves the
puncture. -/
lemma galoisAction_preimage_puncturedCover (σ : K ≃ₐ[k] K) :
    (galoisAction k K σ) ⁻¹ᵁ puncturedCover K = puncturedCover K :=
  preimage_basicOpen_X σ.toRingEquiv.toRingHom

/-- The restriction to the puncture of the automorphism of the chart induced by a Galois
automorphism. -/
def galoisActionPuncturedMap (σ : K ≃ₐ[k] K) :
    (puncturedCover K).toScheme ⟶ (puncturedCover K).toScheme :=
  ((cover K).isoOfEq (galoisAction_preimage_puncturedCover k K σ)).inv ≫
    morphismRestrict (galoisAction k K σ) (puncturedCover K)

/-- The restricted Galois automorphism of the puncture is compatible with the inclusion of
the puncture into the chart. -/
theorem galoisActionPuncturedMap_ι (σ : K ≃ₐ[k] K) :
    galoisActionPuncturedMap k K σ ≫ (puncturedCover K).ι =
      (puncturedCover K).ι ≫ galoisAction k K σ := by
  simp [galoisActionPuncturedMap]

/-- The restricted Galois automorphism of the puncture is an isomorphism. -/
instance isIso_galoisActionPuncturedMap (σ : K ≃ₐ[k] K) :
    IsIso (galoisActionPuncturedMap k K σ) := by
  dsimp [galoisActionPuncturedMap]
  infer_instance

/-- The relation scheme `R = U ⨿ (U ∖ {0})`, carrying the diagonal on the first summand and
the twisted diagonal on the second. -/
abbrev relationScheme : Scheme.{u} := cover K ⨿ (puncturedCover K).toScheme

/-- The chart regarded as a scheme over the base. -/
abbrev coverOverBase : Over (base k) := Over.mk (coverMap k K)

/-- The relation scheme regarded as a scheme over the base. -/
abbrev relationOverBase : Over (base k) :=
  Over.mk (coprod.desc (coverMap k K) ((puncturedCover K).ι ≫ coverMap k K))

/-- The projection of the relation to its first coordinate: the identity on the diagonal
summand and the inclusion of the puncture on the other. -/
def relationFirst : relationOverBase k K ⟶ coverOverBase k K :=
  Over.homMk (coprod.desc (𝟙 (cover K)) (puncturedCover K).ι) (by
    apply coprod.hom_ext <;> simp [relationOverBase, coverOverBase])

/-- The projection of the relation to its second coordinate, twisted by the Galois
automorphism on the punctured summand. -/
def relationSecond (σ : K ≃ₐ[k] K) : relationOverBase k K ⟶ coverOverBase k K :=
  Over.homMk (coprod.desc (𝟙 (cover K)) ((puncturedCover K).ι ≫ galoisAction k K σ)) (by
    apply coprod.hom_ext <;> simp [relationOverBase, coverOverBase, galoisAction_coverMap])

/-- The diagonal together with the twisted diagonal away from zero, as a pre-relation on the
chart over the base. -/
def twistedRelation (σ : K ≃ₐ[k] K) :
    Stacks.Groupoids.PreRelation (relationOverBase k K) (coverOverBase k K) :=
  prod.lift (relationFirst k K) (relationSecond k K σ)

/-- The target of the twisted relation is the first projection `relationFirst`. -/
@[simp]
theorem twistedRelation_target (σ : K ≃ₐ[k] K) :
    (twistedRelation k K σ).target = relationFirst k K := by
  simp [twistedRelation, Stacks.Groupoids.PreRelation.target]

/-- The source of the twisted relation is the second projection `relationSecond`. -/
@[simp]
theorem twistedRelation_source (σ : K ≃ₐ[k] K) :
    (twistedRelation k K σ).source = relationSecond k K σ := by
  simp [twistedRelation, Stacks.Groupoids.PreRelation.source]

/-- The first projection restricts to the identity on the diagonal summand. -/
@[simp]
theorem relationFirst_inl :
    (coprod.inl : cover K ⟶ relationScheme K) ≫ (relationFirst k K).left = 𝟙 (cover K) := by
  simp [relationFirst]

/-- The first projection restricts to the inclusion of the puncture on the punctured summand. -/
@[simp]
theorem relationFirst_inr :
    (coprod.inr : (puncturedCover K).toScheme ⟶ relationScheme K) ≫ (relationFirst k K).left =
      (puncturedCover K).ι := by
  simp [relationFirst]

/-- The second projection restricts to the identity on the diagonal summand. -/
@[simp]
theorem relationSecond_inl (σ : K ≃ₐ[k] K) :
    (coprod.inl : cover K ⟶ relationScheme K) ≫ (relationSecond k K σ).left =
      𝟙 (cover K) := by
  simp [relationSecond]

/-- The second projection restricts on the punctured summand to the inclusion of the puncture
followed by the Galois automorphism. -/
@[simp]
theorem relationSecond_inr (σ : K ≃ₐ[k] K) :
    (coprod.inr : (puncturedCover K).toScheme ⟶ relationScheme K) ≫
        (relationSecond k K σ).left =
      (puncturedCover K).ι ≫ galoisAction k K σ := by
  simp [relationSecond]

/-- The quotient `X = U/R` of the affine line over a quadratic Galois extension by the diagonal
together with the twisted diagonal away from zero. -/
@[stacks 03FN "quadratic_galois_twisted_doubled_origin"]
abbrev quadraticGaloisTwistedDoubledOrigin
    [FiniteDimensional k K] [IsGalois k K] (_hdegree : Module.finrank k K = 2)
    (σ : K ≃ₐ[k] K) (_hσ : σ ≠ 1)
    (B : BigFppfSite.{u}) (hS : B.Contains (base k))
    [HasSheafify (BigFppfOver.topology B (base k) hS) (Type u)] :
    Sheaf (BigFppfOver.topology B (base k) hS) (Type u) :=
  Stacks.Groupoids.quotientSheaf (BigFppfOver.topology B (base k) hS)
    (Over.post B.inclusion : BigFppfOver B (base k) hS ⥤ Over (base k))
    (twistedRelation k K σ)

end AlgebraicGeometry.TwistedDoubledOrigin

end
