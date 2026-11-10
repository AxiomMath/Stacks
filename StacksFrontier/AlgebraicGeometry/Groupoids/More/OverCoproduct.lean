module

public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.OverPullback
public import StacksFrontier.AlgebraicGeometry.SigmaPoints
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Coproducts of schemes over a base, and their base changes

A family `U i` of schemes over `S` has a coproduct in `Over S`: its underlying scheme is the
disjoint union `∐ (U i).left` and its structure morphism is the one glued from the structure
morphisms of the members.  This file constructs that coproduct, proves that it is one, and
proves that a fibre product over the coproduct is the coproduct of the fibre products over the
members.

## Main definitions

* `AlgebraicGeometry.sigmaOver` is the coproduct of a family of schemes over `S`, with its
  injections `AlgebraicGeometry.sigmaOverι` and the morphism
  `AlgebraicGeometry.sigmaOverDesc` it determines out of a family of morphisms.

## Main results

* `AlgebraicGeometry.isColimitCofanMkOfLeft`: a cofan in `Over S` whose underlying cofan of
  schemes is a coproduct is a coproduct.
* `AlgebraicGeometry.sigmaOverIsColimit`: `AlgebraicGeometry.sigmaOver` is the coproduct.
* `AlgebraicGeometry.nonempty_isColimit_cofanMk_of_isPullback_sigmaDesc`: the base change of a
  coproduct of morphisms along a morphism is the coproduct of the base changes.

## Implementation notes

The coproduct in `Over S` is built by hand from the coproduct of schemes rather than taken from
a general construction of colimits in an over category, so that the underlying scheme of
`AlgebraicGeometry.sigmaOver` is the disjoint union on the nose and the underlying morphism of
each injection is a coproduct injection on the nose.  That the result is a coproduct in
`Over S` is then an instance of `AlgebraicGeometry.isColimitCofanMkOfLeft`, which says that the
forgetful functor to schemes reflects coproducts: a morphism out of a coproduct in `Over S` is
a morphism out of the coproduct of the underlying schemes which is compatible with the
structure morphisms, and the compatibility is checked on the injections.

`AlgebraicGeometry.nonempty_isColimit_cofanMk_of_isPullback_sigmaDesc` is stated for arbitrary
cartesian squares rather than for the chosen fibre products, so that it applies to the images
under `CategoryTheory.Over.forget` of chosen fibre products of `Over S`, which are cartesian but
not chosen.  The comparison morphism from the `i`-th partial fibre product is the base change of
the `i`-th coproduct injection, so the comparison morphisms are open immersions whose ranges are
the preimages of the ranges of the injections; these cover and are pairwise disjoint because the
injections are.

## References

* [Stacks Project, Tag 01JA](https://stacks.math.columbia.edu/tag/01JA)
* [Stacks Project, Tag 04MP](https://stacks.math.columbia.edu/tag/04MP)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {S : Scheme.{u}} {ι : Type v} [Small.{u} ι]

/-! ### The coproduct of a family of schemes over a base -/

/-- The coproduct of a family of schemes over `S`: the disjoint union of the members, with the
structure morphism glued from theirs. -/
@[ega "IV 1.1.6" "more general", ega "IV 1.6.5" "more general", ega "IV 11.10.3"]
noncomputable def sigmaOver (U : ι → Over S) : Over S :=
  Over.mk (Sigma.desc fun i => (U i).hom)

/-- The underlying scheme of `sigmaOver U` is the coproduct of the underlying schemes. -/
@[simp]
lemma sigmaOver_left (U : ι → Over S) : (sigmaOver U).left = ∐ fun i => (U i).left := rfl

/-- The structure morphism of `sigmaOver U` is glued from the structure morphisms of the
members. -/
@[simp]
lemma sigmaOver_hom (U : ι → Over S) :
    (sigmaOver U).hom = Sigma.desc fun i => (U i).hom := rfl

/-- The `i`-th injection into the coproduct of a family of schemes over `S`. -/
noncomputable def sigmaOverι (U : ι → Over S) (i : ι) : U i ⟶ sigmaOver U :=
  Over.homMk (Sigma.ι (fun i => (U i).left) i) (Sigma.ι_comp_desc _ _)

/-- The underlying morphism of `sigmaOverι U i` is the `i`-th coproduct injection of schemes. -/
@[simp]
lemma sigmaOverι_left (U : ι → Over S) (i : ι) :
    (sigmaOverι U i).left = Sigma.ι (fun i => (U i).left) i := rfl

/-- The morphism out of a coproduct of schemes over `S` determined by a family of morphisms. -/
noncomputable def sigmaOverDesc {U : ι → Over S} {T : Over S} (h : ∀ i, U i ⟶ T) :
    sigmaOver U ⟶ T :=
  Over.homMk (Sigma.desc fun i => (h i).left) (by
    change (Sigma.desc fun i => (h i).left) ≫ T.hom = Sigma.desc fun i => (U i).hom
    exact Sigma.hom_ext _ _ fun i => by simp [Over.w])

/-- The underlying morphism of `sigmaOverDesc h` is the morphism of schemes out of the
coproduct determined by the underlying morphisms of the `h i`. -/
@[simp]
lemma sigmaOverDesc_left {U : ι → Over S} {T : Over S} (h : ∀ i, U i ⟶ T) :
    (sigmaOverDesc h).left = Sigma.desc fun i => (h i).left := rfl

/-- The composite of the `i`-th injection with `sigmaOverDesc h` is `h i`. -/
@[reassoc (attr := simp)]
lemma sigmaOverι_desc {U : ι → Over S} {T : Over S} (h : ∀ i, U i ⟶ T) (i : ι) :
    sigmaOverι U i ≫ sigmaOverDesc h = h i := by
  ext : 1
  simp

/-- A cofan in `Over S` whose underlying cofan of schemes is a coproduct is itself a
coproduct. -/
noncomputable def isColimitCofanMkOfLeft {U : ι → Over S} {V : Over S} (j : ∀ i, U i ⟶ V)
    (h : IsColimit (Cofan.mk V.left fun i => (j i).left)) :
    IsColimit (Cofan.mk V j) := by
  refine Cofan.IsColimit.mk _
    (fun t => Over.homMk (h.desc (Cofan.mk t.pt.left fun i => (t.inj i).left)) ?_)
    (fun t i => ?_) (fun t m hm => ?_)
  · refine h.hom_ext fun ⟨i⟩ => ?_
    have h2 : (j i).left ≫ h.desc (Cofan.mk t.pt.left fun i => (t.inj i).left) =
        (t.inj i).left := h.fac (Cofan.mk t.pt.left fun i => (t.inj i).left) ⟨i⟩
    change (j i).left ≫ h.desc (Cofan.mk t.pt.left fun i => (t.inj i).left) ≫ t.pt.hom =
      (j i).left ≫ V.hom
    rw [← Category.assoc, h2, Over.w, Over.w]
  · ext : 1
    exact h.fac (Cofan.mk t.pt.left fun i => (t.inj i).left) ⟨i⟩
  · ext : 1
    refine h.hom_ext fun ⟨i⟩ => ?_
    have h3 : (j i).left ≫ m.left = (t.inj i).left := by
      rw [← Over.comp_left]; exact congrArg Over.Hom.left (hm i)
    change (j i).left ≫ m.left =
      (j i).left ≫ h.desc (Cofan.mk t.pt.left fun i => (t.inj i).left)
    rw [h3]
    exact (h.fac (Cofan.mk t.pt.left fun i => (t.inj i).left) ⟨i⟩).symm

/-- `AlgebraicGeometry.sigmaOver` is the coproduct of the family in `Over S`. -/
noncomputable def sigmaOverIsColimit (U : ι → Over S) :
    IsColimit (Cofan.mk (sigmaOver U) (sigmaOverι U)) :=
  isColimitCofanMkOfLeft _ (coproductIsCoproduct fun i => (U i).left)

/-! ### Base changes of a coproduct -/

/-- Precomposition with an isomorphism does not change the range of a morphism of schemes. -/
private lemma range_iso_comp {A B C : Scheme.{u}} (e : A ≅ B) (f : B ⟶ C) :
    Set.range (e.hom ≫ f) = Set.range f := by
  refine Set.ext fun y => ⟨?_, ?_⟩
  · rintro ⟨x, rfl⟩
    exact ⟨e.hom x, by simp⟩
  · rintro ⟨x, rfl⟩
    obtain ⟨w, rfl⟩ := e.hom.surjective x
    exact ⟨w, by simp⟩

variable {X : ι → Scheme.{u}} {Y Z : Scheme.{u}}

/-- **The base change of a coproduct of morphisms is the coproduct of the base changes.**

Let `f i : X i ⟶ Y` be a family of morphisms of schemes and `t : Z ⟶ Y` a morphism, let the
square with legs `a` and `b` be a fibre product of `∐ f i` and `t`, and let the square with
legs `a' i` and `b' i` be a fibre product of `f i` and `t`.  Then any family of comparison
morphisms `k i` over the coproduct injections exhibits the total fibre product as the
coproduct of the partial ones. -/
theorem nonempty_isColimit_cofanMk_of_isPullback_sigmaDesc
    {f : ∀ i, X i ⟶ Y} {t : Z ⟶ Y}
    {A : Scheme.{u}} {a : A ⟶ ∐ X} {b : A ⟶ Z} (hA : IsPullback a b (Sigma.desc f) t)
    {A' : ι → Scheme.{u}} {a' : ∀ i, A' i ⟶ X i} {b' : ∀ i, A' i ⟶ Z}
    (hA' : ∀ i, IsPullback (a' i) (b' i) (f i) t)
    (k : ∀ i, A' i ⟶ A) (hk : ∀ i, k i ≫ a = a' i ≫ Sigma.ι X i)
    (hk' : ∀ i, k i ≫ b = b' i) :
    Nonempty (IsColimit (Cofan.mk A k)) := by
  have hpb : ∀ i, IsPullback (k i) (a' i) a (Sigma.ι X i) := fun i => by
    refine IsPullback.of_right ?_ (hk i) hA.flip
    rw [hk' i, Sigma.ι_comp_desc]
    exact (hA' i).flip
  have hoi : ∀ i, IsOpenImmersion (k i) := fun i =>
    MorphismProperty.of_isPullback (P := @IsOpenImmersion) (hpb i).flip inferInstance
  have hrange : ∀ i, Set.range (k i) = a ⁻¹' Set.range (Sigma.ι X i) := fun i => by
    rw [← (hpb i).isoPullback_hom_fst, range_iso_comp]
    simpa using IsOpenImmersion.range_pullbackFst (Sigma.ι X i) a
  have hopens : ∀ i, (k i).opensRange = a ⁻¹ᵁ (Sigma.ι X i).opensRange := fun i =>
    Opens.ext (by simpa using hrange i)
  refine nonempty_isColimit_cofanMk_of k ?_ ?_
  · refine top_le_iff.mp fun x _ => ?_
    obtain ⟨i, y, hy⟩ := exists_sigmaι_eq X (a x)
    refine Opens.mem_iSup.mpr ⟨i, ?_⟩
    rw [hopens i]
    exact ⟨y, hy⟩
  · intro i j hij
    simp only [hopens]
    refine disjoint_iff_inf_le.mpr fun x hx => ?_
    have hm : a x ∈ ((Sigma.ι X i).opensRange ⊓ (Sigma.ι X j).opensRange : (∐ X).Opens) :=
      ⟨hx.1, hx.2⟩
    exact disjoint_iff_inf_le.mp (disjoint_opensRange_sigmaι X i j hij) hm

end AlgebraicGeometry

end
