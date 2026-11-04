module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.LocalStructure.InfinitesimalSections

/-!
# Composition of infinitesimal sections is addition on the conormal module of the unit

In the local model `Stacks.Groupoids.LocalGroupoidAlgebra` of a groupoid at an identity, two
sections `δ₁`, `δ₂` of the source compose by `δ₁ ∘ δ₂ = c(δ₁ ∘ t ∘ δ₂, δ₂)`.  On local rings the
composite is read off the ring `C` of composable pairs: it is `c` followed by the map `C → A`
determined by `b₁ ⊗ b₂ ↦ δ₂(t(δ₁(b₁)))·δ₂(b₂)`, which is `CompositionDatum` below.

**For sections infinitesimally close to the unit this composition is addition on the conormal
module `I/I²` of the identity**: the `A`-linear map `I/I² → K` attached to a composite by the
bijection `Stacks.Groupoids.infinitesimalSectionEquiv` of [Stacks Project, Tag 0CKE] is the sum
of the two `A`-linear maps, and conversely the bijection carries a sum to a composite.  So that
bijection is an isomorphism of groups, which is [Stacks Project, Tag 0CKF].  Composition adds
the two first-order directions because `c` does, by [Stacks Project, Tag 0CK4].

## Main definitions

All in the namespace `Stacks.Groupoids.LocalGroupoidAlgebra`.

* `CompositionDatum`: the map on the ring of composable pairs which computes the composite of
  two sections of the source.
* `CompositionDatum.compose`: the ring map of the composite section.
* `CompositionDatum.toInfinitesimalSection`: the composite of two infinitesimal sections, again
  an infinitesimal section.

## Main results

All in the namespace `Stacks.Groupoids.LocalGroupoidAlgebra`.

* `CompositionDatum.compose_coe_apply`: on the ideal of the unit the composite is
  `(δ₂ ∘ t) ∘ δ₁ + δ₂`.  This is unconditional.
* `CompositionDatum.toInfinitesimalSection_eq`: the composite does not depend on the datum
  computing it, so the group law is well defined.
* **Stacks 0CKF**, that the bijection of Tag 0CKE takes addition to composition, is
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.unitVAddEquiv_add` and
  `AlgebraicGeometry.GroupoidInAlgebraicSpaces.unitVAddMulEquiv`.

## Implementation notes

**Why the composite needs a datum.**  The ring `C` of the local model is an abstract ring with
two maps `first, second : B → C`; the local model records no universal property of it, so there
is no operation on `B →+* A` computing the composite of two sections.  The map
`b₁ ⊗ b₂ ↦ δ₂(t(δ₁(b₁)))·δ₂(b₂)` of the source is therefore supplied as data, pinned down by
its restrictions along `first` and `second` — which do determine it, as the source notes, since
a local homomorphism out of `C` is determined by its values on the elements `b₁ ⊗ b₂`.  The
results below hold for every such datum, so nothing is chosen from an existence statement.

**The hypotheses `hid` and `hsrc`.**  An infinitesimal section is an `A`-algebra map `B → A`
agreeing with `algebraMap B A` modulo `K`, so the retraction and the structure map of
`Stacks.Groupoids.InfinitesimalSection` are `algebraMap B A` and `algebraMap A B`, while the
local model carries its own `identity` and `source`; `hid` and `hsrc` say the two pairs agree.
They are bookkeeping and not mathematics: at a use site one takes the instances
`G.identity.toAlgebra` and `G.source.toAlgebra`, for which both hold by `rfl`, and then
`IsScalarTower A B A` follows from `identity_source` by
`Stacks.Groupoids.isScalarTower_of_retraction`.  Granting `hid`,
`Stacks.Groupoids.LocalGroupoidAlgebra.identityIdeal_eq_augmentationIdeal` identifies the ideal
`I` of the identity with the ideal of the unit of the retraction.

**The hypothesis `hsc`.**  `hsc` says that the source of a composition is the source of its
second entry, `s ∘ c = s ∘ pr₂`, an identity holding in every groupoid which
`Stacks.Groupoids.LocalGroupoidAlgebra` does not record among its fields.  It is a statement
about the data of the local model alone, and it is what makes the composite of two sections a
section.  It is not derivable from the recorded laws: the retractions `rightUnit` and `leftUnit`
of the local model see only the two images of `c(s(a))` and `second(s(a))` in `B`, which already
agree, and they do not determine an element of `C`.

**The hypothesis `htarget`.**  `htarget` says that an infinitesimal section composed with the
target is the identity on `K`, quantified over all infinitesimal sections.  This is
[Stacks Project, Tag 0CKD], proved for groupoids in algebraic spaces as
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.conormalMap_sectionTarget_eq_conormalMap_id`, and
it is the last step of the source's proof.  It is not available in the local model.  Writing `δ = e + θ · d` by the bijection of Tag 0CKE, the defect
`δ(t(k)) - k` of an infinitesimal section at `k ∈ K` is the value of `θ` on the class of
`t(k) - s(k)` in `I/I²`; so `htarget` asks that every `A`-linear map `I/I² → K` kill those
classes.  The local model records no compatibility between `source` and `target` on `K`, that is,
it does not say that the first order thickening cut out by `K` is invariant, and nothing among
its laws forces those classes to vanish or to be multiples of `K`; invariance is part of the
setup of the source and is what the flatness argument of Tag 0CKD uses.  Everything the local
model does give is proved without it, in `CompositionDatum.compose_coe_apply`, which is the
source's formula
`D(ζ) = (δ₂ ∘ t)(D₁(ζ)) + D₂(ζ)`; `htarget` is used only to rewrite `(δ₂ ∘ t)(D₁(ζ))` as
`D₁(ζ)`.

**Coverage: the sheaf-level statement is not covered.**  As in `InfinitesimalSections`, the
statements are those of the local model at a geometric point, which is where the source's own
proof of Tag 0CKF takes place.  The sheaf-level statement has no carrier in this library, and
needs the same three missing prerequisites: [Stacks Project, Tag
0618], the derivation attached to two morphisms of first order thickenings agreeing on the
closed subspace; [Stacks Project, Tag 04D0], the correspondence between those derivations and
the morphisms of first order thickenings; and the stalk comparisons identifying the stalk of
`e₀^*Ω_{R₀/U₀}` with `I/I² ⊗_A A/K` and the stalk of `𝒞_{U₀/U}` with `K`.  The half that is
proved is [Stacks Project, Tag 0619], as
`AlgebraicGeometry.Space.derivationDirectImageEquiv`.

## References

* [Stacks Project, Tag 0CKF](https://stacks.math.columbia.edu/tag/0CKF)
* [Stacks Project, Tag 0CKE](https://stacks.math.columbia.edu/tag/0CKE)
* [Stacks Project, Tag 0CKD](https://stacks.math.columbia.edu/tag/0CKD)
* [Stacks Project, Tag 0CK4](https://stacks.math.columbia.edu/tag/0CK4)
* [Stacks Project, Tag 0618](https://stacks.math.columbia.edu/tag/0618)
* [Stacks Project, Tag 0619](https://stacks.math.columbia.edu/tag/0619)
* [Stacks Project, Tag 04D0](https://stacks.math.columbia.edu/tag/04D0)
-/

@[expose] public noncomputable section

universe u v w

namespace Stacks.Groupoids.LocalGroupoidAlgebra

variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]

section Bridge

variable [Algebra B A] {K : Ideal A}

/-- The retraction `B → A` of the local model undoes the target, `e ∘ t = id`. -/
theorem algebraMap_target (G : LocalGroupoidAlgebra A B C)
    (hid : (algebraMap B A : B →+* A) = G.identity) (a : A) :
    algebraMap B A (G.target a) = a := by
  rw [hid]
  exact DFunLike.congr_fun G.identity_target a

/-- An infinitesimal section carries `K` back into `K` along the target. -/
theorem map_target_mem [Algebra A B] (G : LocalGroupoidAlgebra A B C)
    (hid : (algebraMap B A : B →+* A) = G.identity) (δ : InfinitesimalSection A B K) {k : A}
    (hk : k ∈ K) : δ.1 (G.target k) ∈ K := by
  have h := δ.2 (G.target k)
  rw [G.algebraMap_target hid k] at h
  simpa using add_mem h hk

end Bridge

/-- The datum computing the composite of two sections `δ₁`, `δ₂` of the source: a ring map on
the ring of composable pairs which is `δ₂ ∘ t ∘ δ₁` on the first factor and `δ₂` on the second,
that is to say `b₁ ⊗ b₂ ↦ δ₂(t(δ₁(b₁)))·δ₂(b₂)`. -/
structure CompositionDatum (G : LocalGroupoidAlgebra A B C) (δ₁ δ₂ : B →+* A) where
  /-- The map on the ring of composable pairs. -/
  map : C →+* A
  /-- On the first factor the map is `δ₂ ∘ t ∘ δ₁`. -/
  map_comp_first : map.comp G.first = δ₂.comp (G.target.comp δ₁)
  /-- On the second factor the map is `δ₂`. -/
  map_comp_second : map.comp G.second = δ₂

namespace CompositionDatum

section RingHom

variable {G : LocalGroupoidAlgebra A B C} {δ₁ δ₂ : B →+* A} (φ : CompositionDatum G δ₁ δ₂)

/-- The value of the datum on the first factor. -/
theorem map_first_apply (b : B) : φ.map (G.first b) = δ₂ (G.target (δ₁ b)) :=
  DFunLike.congr_fun φ.map_comp_first b

/-- The value of the datum on the second factor. -/
theorem map_second_apply (b : B) : φ.map (G.second b) = δ₂ b :=
  DFunLike.congr_fun φ.map_comp_second b

/-- The composite section `δ₁ ∘ δ₂ = c(δ₁ ∘ t ∘ δ₂, δ₂)`, read on local rings: composition
followed by the map of the datum. -/
def compose : B →+* A := φ.map.comp G.comp

/-- The composite section is composition followed by the map of the datum. -/
theorem compose_apply (b : B) : φ.compose b = φ.map (G.comp b) := rfl

end RingHom

section Infinitesimal

variable [Algebra A B] [Algebra B A] {G : LocalGroupoidAlgebra A B C}
  {K : Ideal A} {δ₁ δ₂ : InfinitesimalSection A B K}
  (φ : CompositionDatum G (δ₁.1 : B →+* A) (δ₂.1 : B →+* A))

/-- The datum of a composite of infinitesimal sections carries the ideal of the pair of
identities into `K`. -/
theorem pairIdeal_le_comap (hid : (algebraMap B A : B →+* A) = G.identity) :
    G.pairIdeal ≤ K.comap φ.map := by
  rw [G.pairIdeal_eq_sup]
  refine sup_le (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_)
    (Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_)
  · change φ.map (G.first x) ∈ K
    rw [φ.map_first_apply]
    exact map_target_mem G hid δ₂
      (δ₁.map_mem ((G.identityIdeal_eq_augmentationIdeal hid).le hx))
  · change φ.map (G.second x) ∈ K
    rw [φ.map_second_apply]
    exact δ₂.map_mem ((G.identityIdeal_eq_augmentationIdeal hid).le hx)

/-- The datum of a composite of infinitesimal sections sends the ideal of the pair of identities
into `K`. -/
theorem map_mem_of_mem_pairIdeal (hid : (algebraMap B A : B →+* A) = G.identity) {c : C}
    (hc : c ∈ G.pairIdeal) : φ.map c ∈ K :=
  φ.pairIdeal_le_comap hid hc

/-- A composite of infinitesimal sections carries the ideal of the unit into `K`. -/
theorem compose_mem (hid : (algebraMap B A : B →+* A) = G.identity) {b : B}
    (hb : b ∈ (augmentationIdeal A : Ideal B)) : φ.compose b ∈ K := by
  rw [compose_apply]
  refine φ.map_mem_of_mem_pairIdeal hid ?_
  rw [G.pairIdeal_eq_sup]
  exact G.comp_mem ⟨b, (G.identityIdeal_eq_augmentationIdeal hid).ge hb⟩

/-- **The first-order part of a composite of infinitesimal sections.**  On the ideal of the unit
the composite is `(δ₂ ∘ t) ∘ δ₁ + δ₂`, the source's formula
`D(ζ) = (δ₂ ∘ t)(D₁(ζ)) + D₂(ζ)`.  It holds because composition adds the two first-order
directions, [Stacks Project, Tag 0CK4]. -/
theorem compose_coe_apply (hid : (algebraMap B A : B →+* A) = G.identity) (hK : K ^ 2 = ⊥)
    (x : ↥(augmentationIdeal A : Ideal B)) :
    φ.compose (x : B) = δ₂.1 (G.target (δ₁.1 (x : B))) + δ₂.1 (x : B) := by
  have hx : (x : B) ∈ G.identityIdeal := (G.identityIdeal_eq_augmentationIdeal hid).ge x.2
  have hmc := G.mapCotangent_comp ⟨(x : B), hx⟩
  rw [← map_add, Ideal.toCotangent_eq] at hmc
  have hJ2 : G.comp (x : B) - (G.first (x : B) + G.second (x : B)) ∈ G.pairIdeal ^ 2 := hmc
  have hle : G.pairIdeal ^ 2 ≤ (K ^ 2).comap φ.map := by
    refine Ideal.map_le_iff_le_comap.mp ?_
    rw [Ideal.map_pow]
    exact pow_le_pow_left' (Ideal.map_le_iff_le_comap.mpr (φ.pairIdeal_le_comap hid)) 2
  have hmem := hle hJ2
  rw [hK] at hmem
  have h0 : φ.map (G.comp (x : B) - (G.first (x : B) + G.second (x : B))) = 0 := hmem
  rw [map_sub, map_add, sub_eq_zero] at h0
  simp only [compose_apply, h0, φ.map_first_apply, φ.map_second_apply, AlgHom.coe_toRingHom]

/-- A composite of sections splits the source, because the source of a composition is the source
of its second entry. -/
theorem compose_source (hsrc : (algebraMap A B : A →+* B) = G.source)
    (hsc : G.comp.comp G.source = G.second.comp G.source) (a : A) :
    φ.compose (algebraMap A B a) = a := by
  have hs : algebraMap A B a = G.source a := by rw [hsrc]
  have h2 : δ₂.1 (G.source a) = a := by
    rw [← hs, δ₂.1.commutes, Algebra.algebraMap_self_apply]
  rw [hs, compose_apply,
    show G.comp (G.source a) = G.second (G.source a) from DFunLike.congr_fun hsc a,
    φ.map_second_apply]
  exact h2

variable [IsScalarTower A B A]

/-- **The composite of two infinitesimal sections is an infinitesimal section.**  It splits the
source because the source of a composition is the source of its second entry, the hypothesis
`hsc`, and it agrees with the retraction modulo `K` because `c` carries the ideal of the unit
into the ideal of the pair of identities. -/
def toInfinitesimalSection (hid : (algebraMap B A : B →+* A) = G.identity)
    (hsrc : (algebraMap A B : A →+* B) = G.source)
    (hsc : G.comp.comp G.source = G.second.comp G.source) : InfinitesimalSection A B K :=
  ⟨{ φ.compose with
     commutes' := fun a ↦ by simpa using φ.compose_source hsrc hsc a },
   fun b ↦ by
     change φ.compose b - algebraMap B A b ∈ K
     have key : φ.compose (augmentationProj A b : B) = φ.compose b - algebraMap B A b := by
       rw [augmentationProj_coe, map_sub, φ.compose_source hsrc hsc]
     rw [← key]
     exact φ.compose_mem hid (augmentationProj A b).2⟩

/-- The composite of two infinitesimal sections is computed by the datum. -/
@[simp] theorem coe_toInfinitesimalSection (hid : (algebraMap B A : B →+* A) = G.identity)
    (hsrc : (algebraMap A B : A →+* B) = G.source)
    (hsc : G.comp.comp G.source = G.second.comp G.source) (b : B) :
    (φ.toInfinitesimalSection hid hsrc hsc).1 b = φ.compose b :=
  rfl

/-- **The composite of two infinitesimal sections does not depend on the datum computing it**,
so the group law is well defined.  Two data agree on the ideal of the unit by `compose_coe_apply`
and on the image of `A` by `compose_source`, and `B` is the sum of the two. -/
theorem toInfinitesimalSection_eq (hid : (algebraMap B A : B →+* A) = G.identity)
    (hsrc : (algebraMap A B : A →+* B) = G.source) (hK : K ^ 2 = ⊥)
    (hsc : G.comp.comp G.source = G.second.comp G.source)
    (φ' : CompositionDatum G (δ₁.1 : B →+* A) (δ₂.1 : B →+* A)) :
    φ.toInfinitesimalSection hid hsrc hsc = φ'.toInfinitesimalSection hid hsrc hsc := by
  refine Subtype.ext (AlgHom.ext fun b ↦ ?_)
  have key : ∀ ψ : CompositionDatum G (δ₁.1 : B →+* A) (δ₂.1 : B →+* A), ψ.compose b =
      algebraMap B A b + (δ₂.1 (G.target (δ₁.1 (augmentationProj A b : B))) +
        δ₂.1 (augmentationProj A b : B)) := by
    intro ψ
    have hb : algebraMap A B (algebraMap B A b) + (augmentationProj A b : B) = b := by simp
    conv_lhs => rw [← hb]
    rw [map_add, ψ.compose_source hsrc hsc, ψ.compose_coe_apply hid hK]
  simp only [coe_toInfinitesimalSection, key φ, key φ']

end Infinitesimal

end CompositionDatum

section Addition

variable [Algebra A B] [Algebra B A] [IsScalarTower A B A] {G : LocalGroupoidAlgebra A B C}
  {K : Ideal A}

end Addition

end Stacks.Groupoids.LocalGroupoidAlgebra

end
