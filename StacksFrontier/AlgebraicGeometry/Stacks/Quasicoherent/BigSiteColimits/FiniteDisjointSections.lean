module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.H1Vanishing

/-!
# Sections of a sheaf of modules over a disjoint union

Restriction to the members of a covering family is injective on sections of a sheaf of modules,
and if the members are disjoint and each is a subobject of the target it is also surjective.
Together these two statements say that the sections over a disjoint union of the members of a
covering family are the product of the sections over the members, which is the sheaf condition
for that decomposition.

The two halves cost different hypotheses, and it is worth keeping them apart.  Injectivity is
separatedness and needs nothing but the covering property.  Surjectivity needs the family to be
compatible with itself: a section of the target over each member has to restrict to one section
on each object mapping into two members over the base, and that is what disjointness buys.  The
disjointness hypothesis is stated as the assertion that the empty sieve covers any object mapping
compatibly into two distinct members, which is the site-level statement that their intersection
is empty; the sheaf condition then makes the sections over such an object trivial, so the two
restrictions agree there for free.

Neither statement needs the family to be finite, and neither needs a coproduct to exist in the
site: what is used of a disjoint union is exactly that its pieces cover it, are subobjects of
it, and meet in nothing.  Finiteness matters only to the consumer, which needs the disjoint
union to be an object of the site.

The conclusions are stated as surjectivity and injectivity of the map which restricts a section
to all the members at once, which is the shape
`SheafOfModules.jointlyDetectsRange_of_detectsRange` consumes.

## Main results

* `SheafOfModules.injective_restrict`: **restriction to the members of a covering family is
  injective on sections.**
* `SheafOfModules.surjective_restrict`: **restriction to the members of a covering family of
  pairwise disjoint subobjects is surjective on sections.**
* `SheafOfModules.jointlyDetectsRange_of_detectsRange_of_disjoint`: the two combined with
  `SheafOfModules.jointlyDetectsRange_of_detectsRange`, which is what they were proved for.
* `SheafOfModules.subsingleton_of_bot_mem`: a sheaf of modules has only one section over an
  object covered by the empty sieve.

## Implementation notes

The sheaf condition of a `SheafOfModules` is a condition on its underlying presheaf of abelian
groups, so elementwise statements go through the presheaf of types obtained by composing with
the forgetful functor; `SheafOfModules.isSheaf_sections` records that composite as a sheaf, and
all the element-level reasoning happens in `CategoryTheory.Presieve.IsSheafFor` for it.  The
values and restriction maps of that composite are definitionally the values and restriction maps
of the sheaf of modules, so no translation lemma is needed between them.

Compatibility of a family of sections indexed by the members is `Presieve.Arrows.Compatible`,
the form in which `CategoryTheory.Presieve.isSheafFor_arrows_iff` states the sheaf condition for
a presieve of arrows.  That avoids choosing a factorisation for every arrow of the generated
sieve, which is the only reason the disjointness hypothesis can be stated for the members
themselves rather than for arbitrary arrows below them.

## References

* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 06WN](https://stacks.math.columbia.edu/tag/06WN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w u v r m

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{r}}

/-- The presheaf of sets of sections of a sheaf of modules is a sheaf: the sheaf condition of a
sheaf of modules is one on its underlying presheaf of abelian groups, and the forgetful functor
to sets preserves it. -/
lemma isSheaf_sections (M : SheafOfModules.{m} R) :
    Presheaf.IsSheaf J (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m}) :=
  ((sheafCompose J (CategoryTheory.forget AddCommGrpCat.{m})).obj
    ⟨M.val.presheaf, M.isSheaf⟩).2

/-- The sections of a sheaf of modules satisfy the sheaf condition for a covering family of
arrows. -/
lemma isSheafFor_ofArrows (M : SheafOfModules.{m} R) {W : C} {I : Type w} {V : I → C}
    (a : ∀ i, V i ⟶ W) (ha : Sieve.ofArrows V a ∈ J W) :
    Presieve.IsSheafFor (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m})
      (Presieve.ofArrows V a) := by
  rw [Presieve.isSheafFor_iff_generate]
  exact M.isSheaf_sections.isSheafFor _ ha

/-- **A sheaf of modules has only one section over an object covered by the empty sieve.**  Any
two sections are amalgamations of the empty family, which has a unique one. -/
lemma subsingleton_of_bot_mem (M : SheafOfModules.{m} R) {Z : C}
    (hZ : (⊥ : Sieve Z) ∈ J Z) : Subsingleton (M.val.obj (op Z)) :=
  ⟨fun _ _ ↦ (M.isSheaf_sections.isSheafFor ⊥ hZ).isSeparatedFor.ext
    (fun _ _ hf ↦ hf.elim)⟩

/-- The restrictions of a single section to the members of a family are a compatible family. -/
lemma compatible_restrict (M : SheafOfModules.{m} R) {W : C} {I : Type w} {V : I → C}
    (a : ∀ i, V i ⟶ W) (n : M.val.obj (op W)) :
    Presieve.Arrows.Compatible (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m}) a
      (fun i ↦ M.val.restrictₛₗ (a i).op n) := by
  intro i j Z gi gj hcomm
  change M.val.map gi.op (M.val.map (a i).op n) = M.val.map gj.op (M.val.map (a j).op n)
  rw [← M.val.map_comp_apply, ← M.val.map_comp_apply, ← op_comp, ← op_comp, hcomm]

/-- **Restriction to the members of a covering family is injective on the sections of a sheaf of
modules.**  Two sections with the same restrictions are amalgamations of the same compatible
family, and an amalgamation is unique.  No disjointness and no finiteness are involved: this is
separatedness. -/
theorem injective_restrict (M : SheafOfModules.{m} R) {W : C} {I : Type w} {V : I → C}
    (a : ∀ i, V i ⟶ W) (ha : Sieve.ofArrows V a ∈ J W) :
    Function.Injective
      fun n : M.val.obj (op W) ↦ fun i ↦ M.val.restrictₛₗ (a i).op n := by
  intro n n' h
  obtain ⟨t, -, huniq⟩ := (Presieve.isSheafFor_arrows_iff _ a).1
    (M.isSheafFor_ofArrows a ha) (fun i ↦ M.val.restrictₛₗ (a i).op n)
    (M.compatible_restrict a n)
  exact (huniq n (fun _ ↦ rfl)).trans (huniq n' (fun i ↦ (congrFun h i).symm)).symm

/-- **Restriction to the members of a covering family of pairwise disjoint subobjects is
surjective on the sections of a sheaf of modules.**  An arbitrary family of sections over the
members is compatible: two arrows into the same member agreeing over the base are equal because
that member is a subobject, and an object mapping into two distinct members is covered by the
empty sieve, so it carries only one section.  A compatible family has an amalgamation, which is
the required section.

For the members of a finite disjoint union and the union itself, the three hypotheses are
exactly that the pieces cover it, inject into it, and meet in nothing; together with
`SheafOfModules.injective_restrict` this is the sheaf condition for that decomposition. -/
theorem surjective_restrict (M : SheafOfModules.{m} R) {W : C} {I : Type w} {V : I → C}
    (a : ∀ i, V i ⟶ W) (ha : Sieve.ofArrows V a ∈ J W) (hmono : ∀ i, Mono (a i))
    (hdisj : ∀ ⦃Z : C⦄ ⦃i j : I⦄ (gi : Z ⟶ V i) (gj : Z ⟶ V j), i ≠ j →
      gi ≫ a i = gj ≫ a j → (⊥ : Sieve Z) ∈ J Z) :
    Function.Surjective
      fun n : M.val.obj (op W) ↦ fun i ↦ M.val.restrictₛₗ (a i).op n := by
  intro p
  have hcompat : Presieve.Arrows.Compatible
      (M.val.presheaf ⋙ CategoryTheory.forget AddCommGrpCat.{m}) a p := by
    intro i j Z gi gj hcomm
    by_cases hij : i = j
    · subst hij
      have := hmono i
      rw [(cancel_mono (a i)).1 hcomm]
    · have := M.subsingleton_of_bot_mem (hdisj gi gj hij hcomm)
      exact @Subsingleton.elim _ this _ _
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ a).1
    (M.isSheafFor_ofArrows a ha) p hcompat
  exact ⟨t, funext ht⟩

/-- **A family of pairwise disjoint subobjects covering an object which detects images jointly
detects images.**  This is `SheafOfModules.jointlyDetectsRange_of_detectsRange` with its two
conditions on restriction supplied by `SheafOfModules.surjective_restrict` and
`SheafOfModules.injective_restrict`. -/
theorem jointlyDetectsRange_of_detectsRange_of_disjoint {P N : SheafOfModules.{m} R} (b : P ⟶ N)
    {T W : C} {I : Type w} {V : I → C} (g : ∀ i, V i ⟶ T) (h : W ⟶ T) (a : ∀ i, V i ⟶ W)
    (hcomm : ∀ i, a i ≫ h = g i) (ha : Sieve.ofArrows V a ∈ J W) (hmono : ∀ i, Mono (a i))
    (hdisj : ∀ ⦃Z : C⦄ ⦃i j : I⦄ (gi : Z ⟶ V i) (gj : Z ⟶ V j), i ≠ j →
      gi ≫ a i = gj ≫ a j → (⊥ : Sieve Z) ∈ J Z)
    (hdet : DetectsRange b h) : JointlyDetectsRange.{w} b g :=
  jointlyDetectsRange_of_detectsRange.{w} b g h a hcomm
    (P.surjective_restrict a ha hmono hdisj) (N.injective_restrict a ha) hdet

end SheafOfModules

end
