module

public import Mathlib.Algebra.DirectSum.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.Bivariant

/-!
# Chow cohomology of a good algebraic space

In the situation of Stacks 0EDT let `X/B` be good. The *Chow cohomology* of `X` is the graded
group

  `A^*(X) = ⊕_p A^p(X)`,  where  `A^p(X) = A^p(X ⟶ X)`,

whose degree `p` part is the group of bivariant classes of degree `p` for the identity morphism
of `X`.

## Main definitions

* `AlgebraicGeometry.Space.chowCohomologyComponent` — **Stacks 0ERK**, the degree `p` part
  `A^p(X)` of the Chow cohomology of `X`, namely `A^p(X ⟶ X)`.
* `AlgebraicGeometry.Space.chowCohomology` — **Stacks 0ERK**, the graded group `A^*(X)`.
* `AlgebraicGeometry.Space.restrictionComparisonIso` — the identification `Y ×_Y X' ≅ X ×_X X'`
  of a test space over `X` viewed over `Y` through `f : X ⟶ Y` with itself viewed over `X`.
* `AlgebraicGeometry.Space.chowCohomologyRestrictionCap` and
  `AlgebraicGeometry.Space.chowCohomologyRestrictionCapHom` — **Stacks 0ERL**, the cap
  operations of the pullback `f^*c` of a class `c ∈ A^p(Y)` along `f : X ⟶ Y`, and their
  additivity in `c`.

## Implementation notes

Both are abbreviations, so the pointwise abelian group structure on
`AlgebraicGeometry.Space.BivariantClass` propagates to `A^*(X)` through the `DirectSum`
instances with no further declaration. Degrees range over `ℤ` and a class has finite support.

The development is stated against an `AlgebraicGeometry.Space.ChowGroupSystem`, the parameter
`AlgebraicGeometry.Space.BivariantClass` carries, because the Chow groups of chapter 82 and the
three operations on them that a bivariant class must commute with are not constructed in this
repository; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Chow.Bivariant`.

### The multiplication is not carried

Stacks 0ERK calls `A^*(X)` a graded `ℤ`-algebra. Its ring structure is composition of bivariant
classes, `A^p(X ⟶ X) × A^q(X ⟶ X) ⟶ A^{p+q}(X ⟶ X)`, which this repository does not construct
for algebraic spaces: producing the composite needs the Gysin naturality of Stacks 0ERJ for the
composed cap operation, and that is not available — on the scheme side even the characterization
of a composite does not yield one. So what is defined here is the graded group, and the
`@[stacks 0ERK]` attributes say so. The non-commutativity warning following Stacks 0ERK, and the
assertion that Chern classes lie in the centre, are therefore not stated either.

### The pullback of Stacks 0ERL is given by its cap operations

Stacks 0ERL asserts a `ℤ`-algebra map `A^*(Y) ⟶ A^*(X)`, and defines it by the rule
`(f^*c) ∩ α = c ∩ α`, reading a test space `X' ⟶ X` as a space over `Y`. That rule is
`AlgebraicGeometry.Space.chowCohomologyRestrictionCap`, and it is additive in `c`. Two further
assertions of the tag are not formalized here. Multiplicativity is composition of bivariant
classes, which is absent for the same reason as above. Assembling the cap operations into an
element of `A^p(X)` asks them to satisfy the three naturality axioms of Stacks 0ERJ; each of
those reduces to a compatibility of the parameterized
`AlgebraicGeometry.Space.ChowGroupSystem` with proper pushforward along the comparison
isomorphism — functoriality of proper pushforward, its commutation with flat pullback and with
the Gysin maps — and a `ChowGroupSystem` carries no such axiom, there being nothing in this
repository to prove one from. On the scheme side, where the Chow groups and the three
operations are constructed, those compatibilities are available and the assembly is carried
out in `StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomology` as Stacks 0B7F.

## References

* [Stacks Project, Tag 0ERK](https://stacks.math.columbia.edu/tag/0ERK)
* [Stacks Project, Tag 0ERL](https://stacks.math.columbia.edu/tag/0ERL)
* [Stacks Project, Tag 0B7F](https://stacks.math.columbia.edu/tag/0B7F)
* [Stacks Project, Tag 0ERJ](https://stacks.math.columbia.edu/tag/0ERJ)
* [Stacks Project, Tag 0EDT](https://stacks.math.columbia.edu/tag/0EDT)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

/-- **Stacks 0ERK.** The degree `p` part `A^p(X)` of the Chow cohomology of a good algebraic
space `X/B`: the group `A^p(X ⟶ X)` of bivariant classes of degree `p` for the identity morphism
of `X`. -/
@[stacks 0ERK "the degree p part"]
abbrev chowCohomologyComponent (D : BaseSpaceDimensionSituation.{u}) (G : ChowGroupSystem D)
    {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX) (p : ℤ) : Type (u + 1) :=
  BivariantClass D G sX hX sX hX (𝟙 X) (Category.id_comp sX) p

/-- **Stacks 0ERK.** The Chow cohomology `A^*(X)` of a good algebraic space `X/B`: the graded
group whose degree `p` part is the group `A^p(X ⟶ X)` of bivariant classes of degree `p` for the
identity morphism of `X`. -/
@[stacks 0ERK "the graded group, not the ℤ-algebra: composition is absent"]
abbrev chowCohomology (D : BaseSpaceDimensionSituation.{u}) (G : ChowGroupSystem D)
    {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX) : Type (u + 1) :=
  DirectSum ℤ fun p ↦ chowCohomologyComponent D G sX hX p

/-! ### The pullback of a Chow cohomology class along a morphism -/

section Restriction

open CategoryTheory.Limits

variable (D : BaseSpaceDimensionSituation.{u}) (G : ChowGroupSystem D) {X Y : D.Ambient}
  (sX : X ⟶ D.space) (sY : Y ⟶ D.space) (hY : D.IsGood sY) (f : X ⟶ Y) (hf : f ≫ sY = sX)
  (p : ℤ) {X' : D.Ambient} (g : X' ⟶ X)

/-- The canonical isomorphism `Y ×_Y X' ≅ X ×_X X'` identifying a test space `g : X' ⟶ X`
viewed over `Y` through `f : X ⟶ Y` with the same test space viewed over `X`: both projections
to `X'` are base changes of an identity, hence isomorphisms. -/
abbrev restrictionComparisonIso : pullback (𝟙 Y) (g ≫ f) ≅ pullback (𝟙 X) g :=
  (asIso (pullback.snd (𝟙 Y) (g ≫ f))).trans (asIso (pullback.snd (𝟙 X) g)).symm

include hf in
/-- The comparison isomorphism of a test space viewed over `Y` and over `X` is a morphism over
the base. -/
theorem restrictionComparisonIso_hom_comp_base :
    (restrictionComparisonIso D f g).hom ≫ pullback.fst (𝟙 X) g ≫ sX =
      pullback.fst (𝟙 Y) (g ≫ f) ≫ sY := by
  have key {A B : D.Ambient} (h : A ⟶ B) :
      pullback.fst (𝟙 B) h = pullback.snd (𝟙 B) h ≫ h := by
    simpa using pullback.condition (f := 𝟙 B) (g := h)
  rw [key g, key (g ≫ f), ← hf]
  simp [restrictionComparisonIso]

/-- **Stacks 0ERL.** The cap operations of the pullback `f^*c` of a Chow cohomology class
`c ∈ A^p(Y)` along a morphism `f : X ⟶ Y` of good algebraic spaces over the base: on a good
test space `g : X' ⟶ X` it is the cap operation of `c` on `X'` viewed over `Y`, carried to
`X ×_X X'` along the comparison isomorphism. -/
@[stacks 0ERL "the cap operations of the pullback f^*c"]
def chowCohomologyRestrictionCap (c : chowCohomologyComponent D G sY hY p)
    (hg : D.IsGood (g ≫ sX)) (hpbY : D.IsGood (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY))
    (hpbX : D.IsGood (pullback.fst (𝟙 X) g ≫ sX))
    (hκ : IsProper D.site D.base D.base_mem (restrictionComparisonIso D f g).hom) (k : ℤ) :
    G.chow (g ≫ sX) hg k →+ G.chow (pullback.fst (𝟙 X) g ≫ sX) hpbX (k - p) :=
  (G.properPushforward (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY) hpbY
      (pullback.fst (𝟙 X) g ≫ sX) hpbX (restrictionComparisonIso D f g).hom
      (restrictionComparisonIso_hom_comp_base D sX sY f hf g) hκ (k - p)).comp
    ((c.cap (g ≫ f) (by rw [Category.assoc, hf]; exact hg) hpbY k).comp
      (G.chowCongr hg (by rw [Category.assoc, hf]; exact hg)
        (by rw [Category.assoc, hf]) k).toAddMonoidHom)

/-- The pullback of the zero Chow cohomology class caps to zero. -/
@[simp]
theorem chowCohomologyRestrictionCap_zero (hg : D.IsGood (g ≫ sX))
    (hpbY : D.IsGood (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY))
    (hpbX : D.IsGood (pullback.fst (𝟙 X) g ≫ sX))
    (hκ : IsProper D.site D.base D.base_mem (restrictionComparisonIso D f g).hom) (k : ℤ) :
    chowCohomologyRestrictionCap D G sX sY hY f hf p g 0 hg hpbY hpbX hκ k = 0 := by
  refine AddMonoidHom.ext fun α => ?_
  simp [chowCohomologyRestrictionCap]

/-- The pullback of a sum of Chow cohomology classes caps to the sum of their pullbacks. -/
@[simp]
theorem chowCohomologyRestrictionCap_add (c d : chowCohomologyComponent D G sY hY p)
    (hg : D.IsGood (g ≫ sX)) (hpbY : D.IsGood (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY))
    (hpbX : D.IsGood (pullback.fst (𝟙 X) g ≫ sX))
    (hκ : IsProper D.site D.base D.base_mem (restrictionComparisonIso D f g).hom) (k : ℤ) :
    chowCohomologyRestrictionCap D G sX sY hY f hf p g (c + d) hg hpbY hpbX hκ k =
      chowCohomologyRestrictionCap D G sX sY hY f hf p g c hg hpbY hpbX hκ k +
        chowCohomologyRestrictionCap D G sX sY hY f hf p g d hg hpbY hpbX hκ k := by
  refine AddMonoidHom.ext fun α => ?_
  simp [chowCohomologyRestrictionCap]

/-- **Stacks 0ERL.** The pullback along `f : X ⟶ Y` of the cap operation of a Chow cohomology
class on a fixed good test space over `X`, as an additive map in the class. -/
@[stacks 0ERL "the pullback of cap operations is additive in the class"]
def chowCohomologyRestrictionCapHom (hg : D.IsGood (g ≫ sX))
    (hpbY : D.IsGood (pullback.fst (𝟙 Y) (g ≫ f) ≫ sY))
    (hpbX : D.IsGood (pullback.fst (𝟙 X) g ≫ sX))
    (hκ : IsProper D.site D.base D.base_mem (restrictionComparisonIso D f g).hom) (k : ℤ) :
    chowCohomologyComponent D G sY hY p →+
      (G.chow (g ≫ sX) hg k →+ G.chow (pullback.fst (𝟙 X) g ≫ sX) hpbX (k - p)) where
  toFun c := chowCohomologyRestrictionCap D G sX sY hY f hf p g c hg hpbY hpbX hκ k
  map_zero' := chowCohomologyRestrictionCap_zero D G sX sY hY f hf p g hg hpbY hpbX hκ k
  map_add' c d := chowCohomologyRestrictionCap_add D G sX sY hY f hf p g c d hg hpbY hpbX hκ k

end Restriction

end AlgebraicGeometry.Space

end
