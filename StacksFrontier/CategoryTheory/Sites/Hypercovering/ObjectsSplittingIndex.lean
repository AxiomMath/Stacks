module

public import StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectsSplitting

/-!
# The index combinatorics of a splitting, and the induction step of Tag 0DAV

`Stacks.CategoryTheory.Hypercovering.isTruncatedHypercoveringOver_extend_splitting` extends a
split `M`-truncated hypercovering of `X` by objects of `B`
([Stacks, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV)) to an `(M + 1)`-truncated one,
*given* a covering `u` of the matching object by objects of `B` through which the degenerate part
maps. That covering is supplied by
`Stacks.CategoryTheory.Hypercovering.exists_isCoveringOver_objects_in`, which asks for the index
map of the morphism from the degenerate part to the matching object to be **injective**: at most
one degenerate summand over each summand of the matching object. The hypothesis cannot be dropped,
because it is what makes the second hypothesis on `B` -- which adjoins a single arrow to a
covering -- sufficient.

This file proves that injectivity, and with it assembles the induction step. It also discharges the
base case of the induction: a `0`-truncated simplicial object is split.

**Why the injectivity is provable at all.** The matching object is an abstract pointwise right Kan
extension throughout this development -- the instance is a hypothesis -- so its index type has no
description, and none is used here. Only the *functorial* direction is needed: two indices with the
same image have the same image under every cone leg, i.e. the same face family. The splitting then
recovers the summand from its face family, which is the uniqueness half of the Eilenberg--Zilber
decomposition and is exactly what the source asserts when it says that the inverse image of a
degenerate index is `J_{i'} ⨿ {(φ, i)}` "for a unique pair `(φ, i)`".

The argument runs through the sections of the epimorphisms of `SimplexCategory`:

* along a section `s` of the epimorphism `j.hom` of a degenerate index, the face family of that
  index is the *nondegenerate* summand inclusion;
* a general simplicial operator can land in the nondegenerate summand only if it is a
  monomorphism (`Splitting.mono_of_incl_f_eq_ι_f`), the epimorphic half of its image factorization
  being forced to split;
* two epimorphisms out of `⦋M + 1⦌` with the same sections are equal
  (`SimplexCategory.eq_of_forall_section`).

## Main definitions

* `CategoryTheory.SimplicialObject.Truncated.EpiOut.id`: the identity epimorphism, as an index.
* `CategoryTheory.SimplicialObject.Truncated.splittingOfZero`: the splitting of a `0`-truncated
  simplicial object.
* `CategoryTheory.SimplicialObject.Truncated.Splitting.slotObj`,
  `Splitting.toSlot`, `Splitting.slot`, `Splitting.slotIndex`: the identification of a degree of
  `Y` with the coproduct of the nondegenerate parts along the epimorphisms out of it, in the
  direction that computes indices, and the two components of the index it computes.
* `CategoryTheory.Limits.FormalCoproduct.cofanOfType`: the explicit coproduct of a family of formal
  coproducts indexed by a type in the lowest universe, together with
  `isColimitCofanOfType`. Mathlib's `FormalCoproduct.cofan` asks for an index type in the index
  universe `w` of the formal coproducts, which `EpiOut M S : Type` is not.
* `SimplexCategory.sectionHom`: a right inverse of the underlying map of a morphism of
  `SimplexCategory`, as a morphism.

## Main results

* `SimplexCategory.eq_of_forall_section`: an epimorphism of `SimplexCategory` is determined by its
  sections.
* `CategoryTheory.Limits.FormalCoproduct.exists_eq_ι_f`: every index of a coproduct of formal
  coproducts is an index of one of the summands.
* `CategoryTheory.SimplicialObject.Truncated.Splitting.eq_of_inj_f_eq`: the summand inclusions of
  a splitting have pairwise disjoint images on indices and are injective.
* `CategoryTheory.SimplicialObject.Truncated.Splitting.toSlot_map_f`: a degeneracy of `Y` acts on
  indices by precomposition of slots.
* `CategoryTheory.SimplicialObject.Truncated.Splitting.eq_of_degenLeg_f_eq`: the face family of a
  summand of the degenerate part of degree `M + 1` determines that summand -- uniqueness of the
  Eilenberg--Zilber decomposition, in the form the covering half of Tag 0DAV needs.
* `CategoryTheory.SimplicialObject.Truncated.Splitting.degenToMatching_injective`: the morphism
  from the degenerate part to the matching object is injective on indices.
* `Stacks.CategoryTheory.Hypercovering.exists_isTruncatedHypercoveringOver_succ_of_splitting`: the
  induction step of Tag 0DAV -- a split `M`-truncated hypercovering of `X` by objects of `B` whose
  nondegenerate parts have their summands in `B` extends to an `(M + 1)`-truncated one.

## Implementation notes

**What is still missing for Tag 0DAV**, and it is the only thing: the extension produced by
`exists_isTruncatedHypercoveringOver_succ_of_splitting` has to be shown *split again*, so that the
step can be iterated. That is the auxiliary invariant `Q` of
`Stacks.CategoryTheory.Hypercovering.exists_hypercovering_of_objects_in_of_extensionData`, which is
a parameter precisely because the invariant the source carries is splitness. Accordingly no
declaration here carries the tag `0DAV`, and none carries `0DAU` either: `Splitting` is the data
half of that tag and is deliberately untagged, and `splittingOfZero` is one instance of it rather
than the equivalence of the three conditions that `0DAU` states.

Two facts will be wanted by whoever propagates splitness. First, the degree-`M + 1` summand
inclusion of the extension at the degenerate index `EpiOut.comp e (EpiOut.id M x)` is
`Sigma.ι _ (EpiOut.comp e (EpiOut.id M x)) ≫ s`, because the extension's degeneracy along `e` is
`Splitting.degenEpi x e ≫ s` and `Splitting.inj_epiOutId` together with
`Splitting.inj_comp_degenEpi` give `S.ι x ≫ S.degenEpi x e
= Sigma.ι S.degenFamily (EpiOut.comp e (EpiOut.id M x))` in one rewrite. So the degree-`M + 1` half
of the new splitting is exactly a binary coproduct decomposition
`P ≅ Z' ⊔ Splitting.degenPart` of the covering, with `s` the second injection -- which is the shape
the construction inside `exists_isCoveringOver_objects_in` has, hidden behind its existential.
Second, `EpiOut (M + 1) x.obj` is `EpiOut M x.obj` for `x.obj.len ≤ M`, because an epimorphism out
of `x.obj` has target of dimension at most `x.obj.len`, and `EpiOut (M + 1) ⦋M + 1⦌` is the
identity index together with `EpiOut M ⦋M + 1⦌`.

**`B` is not closed under isomorphism**, so the membership hypotheses must be about the objects
that literally occur. `Splitting.degenPart` is Mathlib's chosen coproduct `∐`, whose summand
objects are only *isomorphic* to the nondegenerate parts; the induction step therefore applies
`exists_isCoveringOver_objects_in` to the explicit coproduct `(cofanOfType _).pt`, whose summand
objects are the nondegenerate parts on the nose, and transports the factorization along
`coproductIsoCofanOfTypePt`. Taking the hypothesis on `∐` instead would have needed `B` to be
iso-closed, which is a different theorem.

Three steps use that a proof of a `Prop` is definitionally any other proof of the same `Prop`, so
that an `eqToHom` of an equality between definitionally equal objects is definitionally the
identity: the two `exact`s closing `isColimitCofanOfType`, and the final `rfl` of
`Splitting.toSlot_map_f`. This is why those steps are `exact`/`rfl` and not `rw` or `simp`, which
refuse at `implicit` transparency with a message naming a pattern rather than the cause.

**Universes.** `D : Type u` with `[Category.{v} D]` and a free index universe `w` for the formal
coproducts, as in `StacksFrontier.CategoryTheory.Sites.Hypercovering.ObjectsSplitting`; `A : Type u`
with `[Category.{v} A]` for the part that mentions no formal coproduct. No universe is narrowed.

## References

* [Stacks Project, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV)
* [Stacks Project, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU)
* [Stacks Project, Tag 017R](https://stacks.math.columbia.edu/tag/017R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open CategoryTheory.SimplicialObject

universe v u w

namespace SimplexCategory

/-- A right inverse of the underlying map of a morphism of `SimplexCategory` is automatically
monotone, hence a morphism: two elements of the source with distinct images are separated the same
way round as their images. -/
def sectionHom {x y : SimplexCategory} (p : x ⟶ y) (g : Fin (y.len + 1) → Fin (x.len + 1))
    (hg : ∀ j, p.toOrderHom (g j) = j) : y ⟶ x :=
  mkHom
    { toFun := g
      monotone' := by
        intro a b hab
        by_contra hlt
        have h1 : g b < g a := lt_of_not_ge hlt
        have h2 := p.toOrderHom.monotone h1.le
        rw [hg a, hg b] at h2
        exact absurd (le_antisymm hab h2) (by rintro rfl; exact absurd h1 (lt_irrefl _)) }

/-- **An epimorphism of `SimplexCategory` is determined by its sections.** If every section of an
epimorphism `p` is also a section of `q`, then `q = p`: a surjection has, through any prescribed
element of its source, a section passing through that element. -/
theorem eq_of_forall_section {x y : SimplexCategory} (p q : x ⟶ y) [Epi p]
    (h : ∀ s : y ⟶ x, s ≫ p = 𝟙 y → s ≫ q = 𝟙 y) : q = p := by
  have hsurj : Function.Surjective p.toOrderHom := epi_iff_surjective.1 ‹Epi p›
  choose r hr using hsurj
  classical
  refine Hom.ext _ _ (OrderHom.ext _ _ (funext fun a ↦ ?_))
  set g : Fin (y.len + 1) → Fin (x.len + 1) := Function.update r (p.toOrderHom a) a with hgdef
  have hg : ∀ j, p.toOrderHom (g j) = j := by
    intro j
    by_cases hj : j = p.toOrderHom a
    · subst hj
      rw [hgdef, Function.update_self]
    · rw [hgdef, Function.update_of_ne hj]
      exact hr j
  have hfac : sectionHom p g hg ≫ q = 𝟙 y :=
    h _ (Hom.ext _ _ (OrderHom.ext _ _ (funext hg)))
  have hid := congr_toOrderHom_apply hfac (p.toOrderHom a)
  rw [comp_toOrderHom, id_toOrderHom] at hid
  simp only [OrderHom.comp_coe, Function.comp_apply, sectionHom, mkHom, Hom.toOrderHom_mk,
    OrderHom.coe_mk, hgdef, Function.update_self, OrderHom.id_coe, id_eq] at hid
  exact hid

/-- Every epimorphism of `SimplexCategory` has a section, `SimplexCategory` being a split-epi
category. -/
theorem exists_comp_eq_id_of_epi {x y : SimplexCategory} (p : x ⟶ y) [Epi p] :
    ∃ s : y ⟶ x, s ≫ p = 𝟙 y :=
  have := isSplitEpi_of_epi p
  ⟨section_ p, IsSplitEpi.id p⟩

end SimplexCategory

namespace CategoryTheory.Limits.FormalCoproduct

variable {D : Type u} [Category.{v} D] {𝒜 : Type} (g : 𝒜 → FormalCoproduct.{w} D)

/-- The explicit coproduct of a family of formal coproducts indexed by a type in the lowest
universe: its index type is the sigma type of the index types. Mathlib's `FormalCoproduct.cofan`
asks for an index type in the index universe of the formal coproducts. -/
def cofanOfType : Cofan g :=
  Cofan.mk ⟨(a : 𝒜) × (g a).I, fun p ↦ (g p.1).obj p.2⟩
    fun a ↦ ⟨fun k ↦ ⟨a, k⟩, fun k ↦ 𝟙 ((g a).obj k)⟩

/-- The index map of the coprojection of `cofanOfType g` at `a` sends `k` to `⟨a, k⟩`. -/
@[simp] theorem cofanOfType_inj_f (a : 𝒜) (k : (g a).I) :
    ((cofanOfType g).inj a).f k = ⟨a, k⟩ := rfl

/-- The component morphisms of the coprojection of `cofanOfType g` at `a` are identities. -/
@[simp] theorem cofanOfType_inj_φ (a : 𝒜) (k : (g a).I) :
    ((cofanOfType g).inj a).φ k = 𝟙 ((g a).obj k) := rfl

/-- Equal morphisms of formal coproducts have equal index maps. -/
private theorem congr_f_apply {X Y : FormalCoproduct.{w} D} {f g : X ⟶ Y} (h : f = g) (k : X.I) :
    f.f k = g.f k :=
  congrArg (fun r ↦ Hom.f r k) h

/-- `cofanOfType` is a coproduct. -/
def isColimitCofanOfType : IsColimit (cofanOfType g) := by
  refine Cofan.IsColimit.mk _
    (fun t ↦ ⟨fun p ↦ (t.inj p.1).f p.2, fun p ↦ (t.inj p.1).φ p.2⟩) ?_ ?_
  · intro t j
    refine hom_ext rfl fun k ↦ ?_
    have h : (𝟙 ((g j).obj k) ≫ (t.inj j).φ k) ≫ 𝟙 (t.pt.obj ((t.inj j).f k))
        = (t.inj j).φ k := by
      rw [Category.id_comp, Category.comp_id]
    exact h
  · intro t m hm
    refine hom_ext (funext fun p ↦ congrArg (fun r ↦ Hom.f r p.2) (hm p.1)) fun p ↦ ?_
    rw [← Category.id_comp (m.φ p)]
    exact ((hom_ext_iff' _ _).1 (hm p.1) p.2).2

section Coproduct

variable [HasCoproduct g]

/-- Mathlib's chosen coproduct of a `Type`-indexed family of formal coproducts agrees with the
explicit one. -/
noncomputable def coproductIsoCofanOfTypePt : ∐ g ≅ (cofanOfType g).pt :=
  colimit.isoColimitCocone ⟨_, isColimitCofanOfType g⟩

/-- The coprojection `Sigma.ι g a` followed by `coproductIsoCofanOfTypePt g` is the coprojection
of `cofanOfType g` at `a`. -/
@[reassoc] theorem ι_comp_coproductIsoCofanOfTypePt (a : 𝒜) :
    Sigma.ι g a ≫ (coproductIsoCofanOfTypePt g).hom = (cofanOfType g).inj a :=
  colimit.isoColimitCocone_ι_hom _ _

/-- **Every index of a coproduct of formal coproducts is an index of one of the summands.** -/
theorem exists_eq_ι_f (z : (∐ g).I) : ∃ (a : 𝒜) (k : (g a).I), (Sigma.ι g a).f k = z := by
  have hinv : ∀ y : (∐ g).I,
      (coproductIsoCofanOfTypePt g).inv.f ((coproductIsoCofanOfTypePt g).hom.f y) = y :=
    fun y ↦ congr_f_apply (coproductIsoCofanOfTypePt g).hom_inv_id y
  have hι : ∀ (a : 𝒜) (k : (g a).I),
      (coproductIsoCofanOfTypePt g).inv.f ⟨a, k⟩ = (Sigma.ι g a).f k := by
    intro a k
    have h : (coproductIsoCofanOfTypePt g).hom.f ((Sigma.ι g a).f k) = ⟨a, k⟩ :=
      congr_f_apply (ι_comp_coproductIsoCofanOfTypePt g a) k
    rw [← h, hinv]
  exact ⟨_, _, (hι _ _).symm.trans (hinv z)⟩

/-- The inverse index map of `coproductIsoCofanOfTypePt` is injective. -/
theorem injective_coproductIsoCofanOfTypePt_inv_f :
    Function.Injective (coproductIsoCofanOfTypePt g).inv.f := by
  intro a b hab
  have h : ∀ y, (coproductIsoCofanOfTypePt g).hom.f ((coproductIsoCofanOfTypePt g).inv.f y) = y :=
    fun y ↦ congr_f_apply (coproductIsoCofanOfTypePt g).inv_hom_id y
  rw [← h a, ← h b, hab]

end Coproduct

end CategoryTheory.Limits.FormalCoproduct

namespace CategoryTheory.SimplicialObject.Truncated

open CategoryTheory.Limits.FormalCoproduct

variable {M : ℕ}

section Any

variable {A : Type u} [Category.{v} A]

/-- The identity epimorphism, as an index. -/
abbrev EpiOut.id (M : ℕ) (x : SimplexCategory.Truncated M) : EpiOut M x.obj :=
  ⟨x, 𝟙 x.obj, inferInstance⟩

/-- In the `0`-truncated simplex category the only epimorphism out of an object is its
identity. -/
instance uniqueEpiOutZero (x : SimplexCategory.Truncated 0) : Unique (EpiOut 0 x.obj) where
  default := EpiOut.id 0 x
  uniq j := by
    obtain ⟨t, p, hp⟩ := j
    obtain rfl : t = x := by
      refine ObjectProperty.FullSubcategory.ext (SimplexCategory.ext ?_)
      have h1 := t.property
      have h2 := x.property
      omega
    have hpi : p = 𝟙 _ := SimplexCategory.eq_id_of_epi p
    simp only [EpiOut.id, hpi]
    rfl

/-- If an epimorphism `e` out of `x` composed with an index out of its target is the identity
index, then `e` is a split monomorphism, hence a monomorphism. -/
theorem mono_of_comp_eq_epiOutId {x z : SimplexCategory.Truncated M} (e : x.obj ⟶ z.obj)
    [Epi e] (η : EpiOut M z.obj) (h : EpiOut.comp e η = EpiOut.id M x) : Mono e := by
  obtain ⟨t, p, hp⟩ := η
  obtain rfl : t = x := congrArg Sigma.fst h
  have h2 : (⟨t, ⟨e ≫ p, epi_comp _ _⟩⟩ : (y : SimplexCategory.Truncated M) ×
      {q : t.obj ⟶ y.obj // Epi q}) = ⟨t, ⟨𝟙 t.obj, inferInstance⟩⟩ := h
  have h' : e ≫ p = 𝟙 _ := by
    simpa only [Sigma.mk.injEq, heq_eq_eq, Subtype.mk.injEq, true_and] using h2
  have : IsSplitMono e := IsSplitMono.mk' ⟨p, h'⟩
  infer_instance

/-- **Every `0`-truncated simplicial object is split**, the nondegenerate part in the single degree
being the object itself. This is the base case of the induction of
[Stacks, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV), where the source observes it as an
instance of [Stacks, Tag 0DAU](https://stacks.math.columbia.edu/tag/0DAU): the colimit condition is
indexed by the epimorphisms out of `⦋0⦌`, of which there is only the identity. -/
def splittingOfZero (Y : SimplicialObject.Truncated A 0) : Splitting Y where
  N x := Y.obj (op x)
  ι _ := 𝟙 _
  isColimit x := by
    have hleg : (𝟙 (Y.obj (op x)) ≫ Y.map (ObjectProperty.homMk (𝟙 x.obj)).op)
        = 𝟙 (Y.obj (op x)) := by
      rw [Category.id_comp, show (ObjectProperty.homMk (𝟙 x.obj) : x ⟶ x) = 𝟙 x from rfl,
        op_id, CategoryTheory.Functor.map_id]
    refine Cofan.IsColimit.mk _ (fun t ↦ t.inj default) (fun t j ↦ ?_) (fun t m hm ↦ ?_)
    · obtain rfl : j = default := Unique.uniq _ j
      change (𝟙 (Y.obj (op x)) ≫ Y.map (ObjectProperty.homMk (𝟙 x.obj)).op) ≫ t.inj default
        = t.inj default
      rw [hleg, Category.id_comp]
    · have h := hm default
      change (𝟙 (Y.obj (op x)) ≫ Y.map (ObjectProperty.homMk (𝟙 x.obj)).op) ≫ m
        = t.inj default at h
      rw [hleg, Category.id_comp] at h
      exact h

namespace Splitting

variable {Y : SimplicialObject.Truncated A M} (S : Splitting Y)

/-- A nondegenerate part read into its own degree along the identity is its inclusion. -/
theorem incl_id (x : SimplexCategory.Truncated M) : S.incl x (𝟙 x.obj) = S.ι x := by
  simp only [incl]
  rw [show (ObjectProperty.homMk (𝟙 x.obj) : x ⟶ x) = 𝟙 x from rfl, op_id,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- The summand at the identity index is the inclusion of the nondegenerate part. -/
theorem inj_epiOutId (x : SimplexCategory.Truncated M) : S.inj (EpiOut.id M x) = S.ι x :=
  S.incl_id x

end Splitting

end Any

namespace Splitting

variable {D : Type u} [Category.{v} D]
  {Y : SimplicialObject.Truncated (FormalCoproduct.{w} D) M} (S : Splitting Y)

/-- The coproduct of the nondegenerate parts along the epimorphisms out of `x`, with its
tautological index type. -/
def slotObj (x : SimplexCategory.Truncated M) : FormalCoproduct.{w} D :=
  ⟨(η : EpiOut M x.obj) × (S.N η.target).I, fun p ↦ (S.N p.1.target).obj p.2⟩

/-- The identification of `Y_x` with the coproduct of the nondegenerate parts along the
epimorphisms out of `x`, in the direction that computes indices. -/
noncomputable def toSlot (x : SimplexCategory.Truncated M) : Y.obj (op x) ⟶ S.slotObj x :=
  Cofan.IsColimit.desc (S.isColimit x) fun η ↦ ⟨fun k ↦ ⟨η, k⟩, fun _ ↦ 𝟙 _⟩

/-- `toSlot x` sends the index `k` of the summand along `η` to `⟨η, k⟩`. -/
theorem toSlot_inj_f (x : SimplexCategory.Truncated M) (η : EpiOut M x.obj)
    (k : (S.N η.target).I) : (S.toSlot x).f ((S.inj η).f k) = ⟨η, k⟩ :=
  congr_f_apply (Cofan.IsColimit.fac (S.isColimit x) _ η) k

/-- The epimorphism out of `x` in whose summand a given index of `Y_x` lies. -/
noncomputable def slot (x : SimplexCategory.Truncated M) (z : (Y.obj (op x)).I) :
    EpiOut M x.obj := ((S.toSlot x).f z).1

/-- The index inside its own summand of a given index of `Y_x`. -/
noncomputable def slotIndex (x : SimplexCategory.Truncated M) (z : (Y.obj (op x)).I) :
    (S.N (S.slot x z).target).I := ((S.toSlot x).f z).2

/-- **The summand inclusions of a splitting have pairwise disjoint images on indices and are
injective.** -/
theorem eq_of_inj_f_eq {x : SimplexCategory.Truncated M} {η η' : EpiOut M x.obj}
    {k : (S.N η.target).I} {k' : (S.N η'.target).I} (h : (S.inj η).f k = (S.inj η').f k') :
    (⟨η, k⟩ : (η : EpiOut M x.obj) × (S.N η.target).I) = ⟨η', k'⟩ := by
  rw [← S.toSlot_inj_f x η k, ← S.toSlot_inj_f x η' k', h]

/-- **A degeneracy of `Y` acts on indices by precomposition of slots.** No surjectivity of the
summand inclusions on indices is needed: both sides are morphisms out of `Y_z`, so the colimit
condition compares them. -/
theorem toSlot_map_f {x z : SimplexCategory.Truncated M} (e : x.obj ⟶ z.obj) [Epi e]
    (ζ : (Y.obj (op z)).I) :
    (S.toSlot x).f ((Y.map (ObjectProperty.homMk e).op).f ζ)
      = ⟨EpiOut.comp e (S.slot z ζ), S.slotIndex z ζ⟩ := by
  have key : Y.map (ObjectProperty.homMk e).op ≫ S.toSlot x
      = S.toSlot z ≫ (⟨fun p ↦ ⟨EpiOut.comp e p.1, p.2⟩, fun _ ↦ 𝟙 _⟩ :
          S.slotObj z ⟶ S.slotObj x) := by
    refine Cofan.IsColimit.hom_ext (S.isColimit z) _ _ fun η ↦ ?_
    show S.inj η ≫ Y.map (ObjectProperty.homMk e).op ≫ S.toSlot x
        = S.inj η ≫ S.toSlot z ≫ _
    have hl : S.inj η ≫ Y.map (ObjectProperty.homMk e).op ≫ S.toSlot x
        = (⟨fun k ↦ ⟨EpiOut.comp e η, k⟩, fun _ ↦ 𝟙 _⟩ : S.N η.target ⟶ S.slotObj x) := by
      rw [← Category.assoc, inj, S.incl_comp_map e η.target η.hom]
      exact Cofan.IsColimit.fac (S.isColimit x) _ (EpiOut.comp e η)
    have hr : S.inj η ≫ S.toSlot z
        = (⟨fun k ↦ ⟨η, k⟩, fun _ ↦ 𝟙 _⟩ : S.N η.target ⟶ S.slotObj z) :=
      Cofan.IsColimit.fac (S.isColimit z) _ η
    rw [hl, ← Category.assoc, hr]
    exact FormalCoproduct.hom_ext rfl fun _ ↦ rfl
  exact congr_f_apply key ζ

/-- **A simplicial operator can carry a nondegenerate index into the nondegenerate part only if it
is a monomorphism.** If the `k`-th nondegenerate part read into degree `x` along `f` has its index
in the nondegenerate summand of `Y_x`, then `f` is a monomorphism: the epimorphic half of the image
factorization of `f` is forced to be a split monomorphism. -/
theorem mono_of_incl_f_eq_ι_f {x k : SimplexCategory.Truncated M} (f : x.obj ⟶ k.obj)
    {t : (S.N k).I} {i : (S.N x).I} (h : (S.incl k f).f t = (S.ι x).f i) : Mono f := by
  have hle : (image f).len ≤ M :=
    le_trans (SimplexCategory.len_le_of_epi (factorThruImage f)) x.property
  have hfac : factorThruImage f ≫ image.ι f = f := image.fac f
  have hcomp : S.incl k (image.ι f) ≫ Y.map (ObjectProperty.homMk
        (Y := (⟨image f, hle⟩ : SimplexCategory.Truncated M)) (factorThruImage f)).op
      = S.incl k f := by
    rw [S.incl_comp_map (y := ⟨image f, hle⟩) (factorThruImage f) k (image.ι f), hfac]
  have hrhs : (S.toSlot x).f ((S.ι x).f i) = ⟨EpiOut.id M x, i⟩ := by
    rw [← S.inj_epiOutId x, S.toSlot_inj_f]
  have heq : (S.toSlot x).f ((Y.map (ObjectProperty.homMk
        (Y := (⟨image f, hle⟩ : SimplexCategory.Truncated M)) (factorThruImage f)).op).f
        ((S.incl k (image.ι f)).f t)) = ⟨EpiOut.id M x, i⟩ := by
    rw [← hrhs, ← h, ← hcomp]
    rfl
  rw [S.toSlot_map_f (x := x) (z := ⟨image f, hle⟩)] at heq
  have h2 : EpiOut.comp (factorThruImage f)
      (S.slot (⟨image f, hle⟩ : SimplexCategory.Truncated M)
        ((S.incl k (image.ι f)).f t)) = EpiOut.id M x := congrArg Sigma.fst heq
  have : Mono (factorThruImage f) := mono_of_comp_eq_epiOutId _ _ h2
  rw [← hfac]
  exact mono_comp _ _

/-- One step of the uniqueness argument: if two summands of the degenerate part of degree `M + 1`
have the same face family on indices, then along a section of the first index's epimorphism the
second index's epimorphism becomes a monomorphism. -/
theorem mono_comp_of_degenLeg_f_eq (j j' : EpiOut M ⦋M + 1⦌) {i : (S.N j.target).I}
    {i' : (S.N j'.target).I}
    (key : ∀ (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌),
      (S.incl j.target (m ≫ j.hom)).f i = (S.incl j'.target (m ≫ j'.hom)).f i')
    (s : j.target.obj ⟶ ⦋M + 1⦌) (hs : s ≫ j.hom = 𝟙 j.target.obj) : Mono (s ≫ j'.hom) := by
  have h := key j.target s
  rw [hs, S.incl_id] at h
  exact S.mono_of_incl_f_eq_ι_f _ h.symm

/-- **The face family of a summand of the degenerate part of degree `M + 1` determines that
summand.** This is the uniqueness of the Eilenberg--Zilber decomposition, in the form the covering
half of [Stacks, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV) needs. -/
theorem eq_of_degenLeg_f_eq (j j' : EpiOut M ⦋M + 1⦌) {i : (S.N j.target).I}
    {i' : (S.N j'.target).I}
    (key : ∀ (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌),
      (S.incl j.target (m ≫ j.hom)).f i = (S.incl j'.target (m ≫ j'.hom)).f i') :
    (⟨j, i⟩ : (jj : EpiOut M ⦋M + 1⦌) × (S.N jj.target).I) = ⟨j', i'⟩ := by
  obtain ⟨s, hs⟩ := SimplexCategory.exists_comp_eq_id_of_epi j.hom
  obtain ⟨s', hs'⟩ := SimplexCategory.exists_comp_eq_id_of_epi j'.hom
  have m1 : Mono (s ≫ j'.hom) := S.mono_comp_of_degenLeg_f_eq j j' key s hs
  have m2 : Mono (s' ≫ j.hom) :=
    S.mono_comp_of_degenLeg_f_eq j' j (fun x m ↦ (key x m).symm) s' hs'
  obtain ⟨jt, p, hp⟩ := j
  obtain ⟨jt', q, hq⟩ := j'
  obtain rfl : jt' = jt := by
    refine ObjectProperty.FullSubcategory.ext (SimplexCategory.ext (le_antisymm ?_ ?_))
    · exact SimplexCategory.len_le_of_mono (s' ≫ p)
    · exact SimplexCategory.len_le_of_mono (s ≫ q)
  obtain rfl : q = p := by
    refine SimplexCategory.eq_of_forall_section p q fun σ hσ ↦ ?_
    have : Mono (σ ≫ q) := S.mono_comp_of_degenLeg_f_eq _ _ key σ hσ
    exact SimplexCategory.eq_id_of_mono (σ ≫ q)
  have hi : i = i' := by
    have h := key _ s
    rw [hs, S.incl_id] at h
    have h2 : (S.inj (EpiOut.id M _)).f i = (S.inj (EpiOut.id M _)).f i' := by
      rw [S.inj_epiOutId, h]
    have h3 := S.eq_of_inj_f_eq h2
    simpa only [Sigma.mk.injEq, heq_eq_eq, true_and] using h3
  rw [hi]

section Matching

variable [∀ F : (SimplexCategory.Truncated M)ᵒᵖ ⥤ FormalCoproduct.{w} D,
  (SimplexCategory.Truncated.inclusion M).op.HasPointwiseRightKanExtension F]

/-- **The morphism from the degenerate part of degree `M + 1` to the matching object is injective
on indices**: at most one degenerate summand lies over each summand of the matching object.

This is the hypothesis `Function.Injective v.f` of
`Stacks.CategoryTheory.Hypercovering.exists_isCoveringOver_objects_in`, and it is what makes the
second hypothesis on `B` in [Stacks, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV) -- which
adjoins only *one* arrow to a covering -- sufficient. The source states it as "the inverse image of
`i'` in `I_{n + 1}` is `J_{i'} ⨿ {(φ, i)}` for a unique pair `(φ, i)`".

No description of the index type of the matching object is used, and none is available: the
matching object is an abstract pointwise right Kan extension here. Only the *functorial* direction
is needed -- equal images have equal face families -- after which the splitting recovers the
summand from its face family (`Splitting.eq_of_degenLeg_f_eq`). -/
theorem degenToMatching_injective [HasCoproduct S.degenFamily] :
    Function.Injective S.degenToMatching.f := by
  intro z z' hz
  obtain ⟨j, i, rfl⟩ := FormalCoproduct.exists_eq_ι_f S.degenFamily z
  obtain ⟨j', i', rfl⟩ := FormalCoproduct.exists_eq_ι_f S.degenFamily z'
  have hleg : ∀ (jj : EpiOut M ⦋M + 1⦌) (ii : (S.N jj.target).I)
      (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌),
      (coskFace Y (𝟙 (matchingObj Y)) x m).f
          (S.degenToMatching.f ((Sigma.ι S.degenFamily jj).f ii))
        = (S.incl jj.target (m ≫ jj.hom)).f ii := by
    intro jj ii x m
    have hc : Sigma.ι S.degenFamily jj ≫ S.degenToMatching ≫ coskFace Y (𝟙 (matchingObj Y)) x m
        = S.incl jj.target (m ≫ jj.hom) := by
      rw [comp_coskFace, Category.comp_id, comp_coskFace, S.coskFace_degenToMatching]
    exact congr_f_apply hc ii
  have key : ∀ (x : SimplexCategory.Truncated M) (m : x.obj ⟶ ⦋M + 1⦌),
      (S.incl j.target (m ≫ j.hom)).f i = (S.incl j'.target (m ≫ j'.hom)).f i' := by
    intro x m
    rw [← hleg j i x m, ← hleg j' i' x m, hz]
  exact congrArg (fun p ↦ (Sigma.ι S.degenFamily p.1).f p.2) (S.eq_of_degenLeg_f_eq j j' key)

end Matching

end Splitting

end CategoryTheory.SimplicialObject.Truncated

namespace Stacks.CategoryTheory.Hypercovering

open CategoryTheory.SimplicialObject.Truncated CategoryTheory.Limits.FormalCoproduct

variable {C : Type u} [Category.{v} C] [HasPullbacks C] {M : ℕ} {X : C}

/-- **The one-step extension of a split truncated hypercovering by objects of `B` exists.** Only
the splitness of `Y` and the membership in `B` of the summands of the nondegenerate parts are
assumed; the covering of the matching object and the factorization of the degeneracies through it
are produced here, the injectivity hypothesis of `exists_isCoveringOver_objects_in` being supplied
by `CategoryTheory.SimplicialObject.Truncated.Splitting.degenToMatching_injective`.

This is the induction step of [Stacks, Tag 0DAV](https://stacks.math.columbia.edu/tag/0DAV) except
for the propagation of splitness to the extension, which is the one remaining obligation of that
tag.

The hypothesis on the nondegenerate parts is stated about *their* summands rather than about those
of `Y`, and the proof passes through the explicit coproduct `(cofanOfType _).pt` rather than
through `Splitting.degenPart`, because `B` is not assumed closed under isomorphism. -/
theorem exists_isTruncatedHypercoveringOver_succ_of_splitting
    [∀ (k : ℕ) (F : (SimplexCategory.Truncated k)ᵒᵖ ⥤ FormalCoproduct.{w} (Over X)),
      (SimplexCategory.Truncated.inclusion k).op.HasPointwiseRightKanExtension F]
    (J : Pretopology C) (B : Set C)
    (hcover : ∀ U : C, ∃ (ι : Type w) (A : ι → C) (a : ∀ i, A i ⟶ U),
      (∀ i, A i ∈ B) ∧ Presieve.ofArrows A a ∈ J U)
    (hadjoin : ∀ {ι : Type w} (A : ι → C) {U : C} (a : ∀ i, A i ⟶ U),
      (∀ i, A i ∈ B) → Presieve.ofArrows A a ∈ J U →
      ∀ {U' : C}, U' ∈ B → ∀ b : U' ⟶ U,
        (fun {_} h ↦ Presieve.ofArrows A a h ∨ Presieve.singleton b h) ∈ J U)
    {Y : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) M}
    (hY : IsTruncatedHypercoveringOver.{w} J B M Y) (S : Splitting Y)
    (hN : ∀ (x : SimplexCategory.Truncated M) (k : (S.N x).I), ((S.N x).obj k).left ∈ B) :
    ∃ Z : SimplicialObject.Truncated (FormalCoproduct.{w} (Over X)) (M + 1),
      (SimplicialObject.Truncated.trunc (FormalCoproduct.{w} (Over X)) (M + 1) M).obj Z = Y ∧
        IsTruncatedHypercoveringOver.{w} J B (M + 1) Z := by
  set e := coproductIsoCofanOfTypePt S.degenFamily
  obtain ⟨P, u, s', hPB, hu, hsu⟩ := exists_isCoveringOver_objects_in J B hcover hadjoin
    (matchingObj Y) (cofanOfType S.degenFamily).pt (fun k ↦ hN _ _)
    (e.inv ≫ S.degenToMatching)
    (S.degenToMatching_injective.comp (injective_coproductIsoCofanOfTypePt_inv_f _))
  refine ⟨_, CategoryTheory.SimplicialObject.Truncated.ExtensionData.trunc_extend _,
    isTruncatedHypercoveringOver_extend_splitting J B hY S u (e.hom ≫ s') ?_ hPB hu⟩
  rw [Category.assoc, hsu, ← Category.assoc, e.hom_inv_id, Category.id_comp]

end Stacks.CategoryTheory.Hypercovering

end
