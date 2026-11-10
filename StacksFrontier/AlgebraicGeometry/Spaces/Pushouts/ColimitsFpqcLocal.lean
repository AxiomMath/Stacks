module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcCoveringBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.FpqcMorphismDescent

/-!
# Fpqc-local detection of colimits of algebraic spaces

Let `T` be an algebraic space over a scheme `S` of a big fppf site, and let `i ↦ X i` be a
diagram of algebraic spaces over `T` with a cocone `c`. The cocone is a colimit as soon as it
becomes one after base change to every member of an fpqc covering of its vertex and to every
pairwise overlap of that covering.

This is the fpqc-local nature of the property of being a colimit: a cocone may be tested
locally, in the same way that a morphism out of the vertex may be descended along an fpqc
covering by [Stacks, Tag 04P2].

## Main results

* `AlgebraicGeometry.Space.isColimit_of_fpqc_local`: **[Stacks, Tag 0GFQ]**, the detection of a
  colimit of algebraic spaces from its base changes to an fpqc covering of the vertex and to
  the pairwise overlaps of that covering.

## Implementation notes

The source's base algebraic space is called `B` there and `T` here, the letter `B` being
reserved throughout this library for the big fppf site.

The base-changed cocones are presented by diagrams `E a` together with cartesian natural
transformations `E a ⟶ D`, rather than by a chosen pullback functor. This keeps their canonical
maps to the original cocone visible and avoids choosing fibre products in the slice category
`Over T`. The hypotheses `hbase`, `hoverlap` and `hbaseOverlap` are exactly the cartesianness of
the squares involved, each stated with `CategoryTheory.IsPullback` on the underlying algebraic
spaces, so no comparison isomorphism has to be transported.

All the colimits concerned are colimits in `CategoryTheory.Over T`, the category of algebraic
spaces over `T`, and the fpqc covering is a covering of the underlying algebraic space `c.pt.left`
of the vertex.

## References

* [Stacks Project, Tag 0GFQ](https://stacks.math.columbia.edu/tag/0GFQ)
* [Stacks Project, Tag 04P2](https://stacks.math.columbia.edu/tag/04P2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w t

namespace AlgebraicGeometry.Space

/-- Two morphisms out of the target of an fpqc covering agree as soon as they agree after
composing with every member of the covering. This is the uniqueness half of [Stacks, Tag 04P2]
applied to the common composite. -/
private theorem eq_of_fpqcCovering_precomp
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {A : Type t}
    {X : A → AlgebraicSpaces B S hS} {Y Z : AlgebraicSpaces B S hS}
    (f : ∀ a, X a ⟶ Y)
    (hf : IsFpqcCovering B S hS fun a => (f a).hom)
    (g₁ g₂ : Y ⟶ Z)
    (h : ∀ a, f a ≫ g₁ = f a ≫ g₂) : g₁ = g₂ := by
  have hcompat : ∀ a b,
      (ObjectProperty.homMk (pullback.fst (f a).hom (f b).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f a) (f b) ⟶ X a) ≫ (f a ≫ g₁) =
      (ObjectProperty.homMk (pullback.snd (f a).hom (f b).hom) :
        AlgebraicSpaces.fiberProduct B S hS (f a) (f b) ⟶ X b) ≫ (f b ≫ g₁) := by
    intro a b
    apply ObjectProperty.hom_ext
    exact congrArg (fun q => q ≫ g₁.hom) pullback.condition
  obtain ⟨q, -, hqu⟩ :=
    existsUnique_desc_of_fpqcCovering B S hS (fun a => f a) hf Z (fun a => f a ≫ g₁) hcompat
  exact (hqu g₁ fun _ => rfl).trans (hqu g₂ fun a => (h a).symm).symm

/-- **[Stacks, Tag 0GFQ].** Let `T` be an algebraic space over a scheme `S` of a big fppf site
and let `D` be a diagram of algebraic spaces over `T` with a cocone `c`. Suppose given an fpqc
covering `f a : (d a).pt ⟶ c.pt` of the vertex such that

* every `d a` is a cocone on a diagram `E a` whose squares over `D` are cartesian, and `d a` is
  a colimit; and
* every pairwise overlap `d₂ a b` of the covering is likewise a cocone on a cartesian diagram
  `E₂ a b` over `D` and is a colimit.

Then `c` is a colimit of `D` in the category of algebraic spaces over `T`.

The base algebraic space is the source's `B`; it is called `T` here because `B` names the big
fppf site throughout this library. -/
@[stacks 0GFQ]
theorem isColimit_of_fpqc_local
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T : AlgebraicSpaces B S hS}
    {I : Type v} [Category.{w} I] (D : I ⥤ Over T) (c : Cocone D)
    {A : Type t}
    (E : A → I ⥤ Over T) (d : ∀ a, Cocone (E a))
    (p : ∀ a, E a ⟶ D)
    (f : ∀ a, (d a).pt ⟶ c.pt)
    (hcover : IsFpqcCovering B S hS fun a => ((f a).left).hom)
    (hbase : ∀ (a : A) (i : I),
      IsPullback ((p a).app i).left ((d a).ι.app i).left (c.ι.app i).left (f a).left)
    (hlocal : ∀ a, Nonempty (IsColimit (d a)))
    (E₂ : A → A → I ⥤ Over T)
    (d₂ : ∀ a b, Cocone (E₂ a b))
    (p₂ : ∀ a b, E₂ a b ⟶ D)
    (toFirst : ∀ a b, (d₂ a b).pt ⟶ (d a).pt)
    (toSecond : ∀ a b, (d₂ a b).pt ⟶ (d b).pt)
    (hoverlap : ∀ a b, IsPullback (toFirst a b).left (toSecond a b).left (f a).left (f b).left)
    (hbaseOverlap : ∀ (a b : A) (i : I),
      IsPullback ((p₂ a b).app i).left ((d₂ a b).ι.app i).left
        (c.ι.app i).left (toFirst a b ≫ f a).left)
    (hoverlapColimit : ∀ a b, Nonempty (IsColimit (d₂ a b))) :
    Nonempty (IsColimit c) := by
  classical
  let hd : ∀ a, IsColimit (d a) := fun a => Classical.choice (hlocal a)
  let hd₂ : ∀ a b, IsColimit (d₂ a b) := fun a b => Classical.choice (hoverlapColimit a b)
  let localMap (s : Cocone D) (a : A) : (d a).pt ⟶ s.pt :=
    (hd a).desc (Cocone.mk s.pt ((p a) ≫ s.ι))
  have localFacLeft (s : Cocone D) (a : A) (i : I) :
      ((d a).ι.app i).left ≫ (localMap s a).left =
        ((p a).app i).left ≫ (s.ι.app i).left :=
    congrArg Over.Hom.left ((hd a).fac (Cocone.mk s.pt ((p a) ≫ s.ι)) i)
  have localCompat (s : Cocone D) (a b : A) :
      (toFirst a b).left ≫ (localMap s a).left =
        (toSecond a b).left ≫ (localMap s b).left := by
    have hcol : toFirst a b ≫ localMap s a = toSecond a b ≫ localMap s b := by
      apply (hd₂ a b).hom_ext
      intro i
      let liftA : ((E₂ a b).obj i).left ⟶ ((E a).obj i).left :=
        (hbase a i).lift ((p₂ a b).app i).left
          (((d₂ a b).ι.app i).left ≫ (toFirst a b).left) (by
            simpa [Category.assoc] using (hbaseOverlap a b i).w)
      let liftB : ((E₂ a b).obj i).left ⟶ ((E b).obj i).left :=
        (hbase b i).lift ((p₂ a b).app i).left
          (((d₂ a b).ι.app i).left ≫ (toSecond a b).left) (by
            calc
              ((p₂ a b).app i).left ≫ (c.ι.app i).left =
                  ((d₂ a b).ι.app i).left ≫ (toFirst a b).left ≫ (f a).left :=
                    (hbaseOverlap a b i).w
              _ = ((d₂ a b).ι.app i).left ≫ (toSecond a b).left ≫ (f b).left := by
                    simpa [Category.assoc] using
                      congrArg (fun q => ((d₂ a b).ι.app i).left ≫ q) (hoverlap a b).w)
      have liftA_fst : liftA ≫ ((p a).app i).left = ((p₂ a b).app i).left :=
        (hbase a i).lift_fst _ _ _
      have liftA_snd : liftA ≫ ((d a).ι.app i).left =
          ((d₂ a b).ι.app i).left ≫ (toFirst a b).left :=
        (hbase a i).lift_snd _ _ _
      have liftB_fst : liftB ≫ ((p b).app i).left = ((p₂ a b).app i).left :=
        (hbase b i).lift_fst _ _ _
      have liftB_snd : liftB ≫ ((d b).ι.app i).left =
          ((d₂ a b).ι.app i).left ≫ (toSecond a b).left :=
        (hbase b i).lift_snd _ _ _
      have hleg : ((d₂ a b).ι.app i).left ≫ (toFirst a b).left ≫ (localMap s a).left =
          ((d₂ a b).ι.app i).left ≫ (toSecond a b).left ≫ (localMap s b).left := by
        calc
            ((d₂ a b).ι.app i).left ≫ (toFirst a b).left ≫ (localMap s a).left =
                ((p₂ a b).app i).left ≫ (s.ι.app i).left := by
                  rw [← Category.assoc, ← liftA_snd, Category.assoc, localFacLeft,
                    ← Category.assoc, liftA_fst]
            _ = ((d₂ a b).ι.app i).left ≫ (toSecond a b).left ≫ (localMap s b).left := by
                  rw [← Category.assoc, ← liftB_snd, Category.assoc, localFacLeft,
                    ← Category.assoc, liftB_fst]
      exact Over.OverMorphism.ext hleg
    simpa only [Over.comp_left] using congrArg Over.Hom.left hcol
  let pull (a b : A) : AlgebraicSpaces B S hS :=
    AlgebraicSpaces.fiberProduct B S hS (f a).left (f b).left
  let fst (a b : A) : pull a b ⟶ (d a).pt.left :=
    ObjectProperty.homMk (pullback.fst (f a).left.hom (f b).left.hom)
  let snd (a b : A) : pull a b ⟶ (d b).pt.left :=
    ObjectProperty.homMk (pullback.snd (f a).left.hom (f b).left.hom)
  have hpair (s : Cocone D) (a b : A) :
      fst a b ≫ (localMap s a).left = snd a b ≫ (localMap s b).left := by
    let hp := AlgebraicSpaces.isPullback_fiberProduct B S hS (f a).left (f b).left
    let e := (hoverlap a b).isoIsPullback ((d a).pt.left) ((d b).pt.left) hp
    apply (cancel_epi e.hom).mp
    calc
      e.hom ≫ fst a b ≫ (localMap s a).left =
          (toFirst a b).left ≫ (localMap s a).left := by
            rw [← Category.assoc,
              (hoverlap a b).isoIsPullback_hom_fst ((d a).pt.left) ((d b).pt.left) hp]
      _ = (toSecond a b).left ≫ (localMap s b).left := localCompat s a b
      _ = e.hom ≫ snd a b ≫ (localMap s b).left := by
            rw [← Category.assoc,
              (hoverlap a b).isoIsPullback_hom_snd ((d a).pt.left) ((d b).pt.left) hp]
  have hex (s : Cocone D) := existsUnique_desc_of_fpqcCovering B S hS (fun a => (f a).left)
    hcover s.pt.left (fun a => (localMap s a).left) (hpair s)
  let descLeft (s : Cocone D) : c.pt.left ⟶ s.pt.left := (hex s).choose
  have descLeftFac (s : Cocone D) (a : A) : (f a).left ≫ descLeft s = (localMap s a).left :=
    (hex s).choose_spec.1 a
  have descOver (s : Cocone D) : descLeft s ≫ s.pt.hom = c.pt.hom := by
    refine eq_of_fpqcCovering_precomp B S hS (fun a => (f a).left) hcover _ _ fun a => ?_
    rw [← Category.assoc, descLeftFac, (localMap s a).w, (f a).w]
  let desc (s : Cocone D) : c.pt ⟶ s.pt := Over.homMk (descLeft s) (descOver s)
  have fac (s : Cocone D) (i : I) : c.ι.app i ≫ desc s = s.ι.app i := by
    apply Over.OverMorphism.ext
    apply eq_of_fpqcCovering_precomp B S hS
      (fun a => (ObjectProperty.homMk
        (pullback.snd (f a).left.hom ((c.ι.app i).left).hom) :
          AlgebraicSpaces.fiberProduct B S hS (f a).left (c.ι.app i).left ⟶ (D.obj i).left))
      (by
        simpa [AlgebraicSpaces.fiberProduct] using
          isFpqcCovering_pullback B S hS (fun a => (f a).left) (c.ι.app i).left hcover)
    intro a
    let q : AlgebraicSpaces.fiberProduct B S hS (f a).left (c.ι.app i).left ⟶ (D.obj i).left :=
      ObjectProperty.homMk (pullback.snd (f a).left.hom ((c.ι.app i).left).hom)
    let r : AlgebraicSpaces.fiberProduct B S hS (f a).left (c.ι.app i).left ⟶ (d a).pt.left :=
      ObjectProperty.homMk (pullback.fst (f a).left.hom ((c.ι.app i).left).hom)
    let k := (hbase a i).lift q r (by
      apply ObjectProperty.hom_ext
      change (pullback.snd (f a).left.hom ((c.ι.app i).left).hom ≫ ((c.ι.app i).left).hom) =
        (pullback.fst (f a).left.hom ((c.ι.app i).left).hom ≫ (f a).left.hom)
      exact pullback.condition.symm)
    have hk₁ : k ≫ ((p a).app i).left = q := (hbase a i).lift_fst _ _ _
    change q ≫ (c.ι.app i).left ≫ descLeft s = q ≫ (s.ι.app i).left
    calc
        q ≫ (c.ι.app i).left ≫ descLeft s =
            k ≫ ((p a).app i).left ≫ (c.ι.app i).left ≫ descLeft s := by
              simp only [← Category.assoc, hk₁]
        _ = k ≫ ((d a).ι.app i).left ≫ (f a).left ≫ descLeft s := by
              simpa [Category.assoc] using
                congrArg (fun z => k ≫ z ≫ descLeft s) (hbase a i).w
        _ = k ≫ ((d a).ι.app i).left ≫ (localMap s a).left := by
              simpa [Category.assoc] using
                congrArg (fun z => k ≫ ((d a).ι.app i).left ≫ z) (descLeftFac s a)
        _ = k ≫ ((p a).app i).left ≫ (s.ι.app i).left := by
              simpa [Category.assoc] using congrArg (fun z => k ≫ z) (localFacLeft s a i)
        _ = q ≫ (s.ι.app i).left := by simp only [← Category.assoc, hk₁]
  have uniq (s : Cocone D) (m : c.pt ⟶ s.pt) (hm : ∀ i, c.ι.app i ≫ m = s.ι.app i) :
      m = desc s := by
    refine Over.OverMorphism.ext <| eq_of_fpqcCovering_precomp B S hS (fun a => (f a).left)
      hcover _ _ fun a => ?_
    have hloc : f a ≫ m = localMap s a := (hd a).hom_ext fun i => Over.OverMorphism.ext <| by
      simp only [Over.comp_left]
      rw [← Category.assoc, ← (hbase a i).w, Category.assoc, localFacLeft]
      exact congrArg (((p a).app i).left ≫ ·) (congrArg Over.Hom.left (hm i))
    exact (congrArg Over.Hom.left hloc).trans (descLeftFac s a).symm
  exact ⟨IsColimit.mk desc fac uniq⟩

end AlgebraicGeometry.Space

end
