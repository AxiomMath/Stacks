module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.AffineCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.LimitPreservingOfFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.SurjectiveCriterion

/-!
# Local finite presentation is relative limit preservation

A morphism of algebraic spaces over a scheme `S` is locally of finite presentation exactly
when it is relatively limit preserving as a transformation of functors on the big fppf site
of `S`. This is **Stacks 04AK**.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving`, in
  `StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Representable`, is the implication
  (2) ⇒ (1) of Stacks 04AK; this file uses it.
* `AlgebraicGeometry.Space.isLocallyOfFinitePresentation_iff_relativelyLimitPreserving` is
  Stacks 04AK, the equivalence of its two conditions.

## Implementation notes

The implication (1) ⇒ (2) is
`AlgebraicGeometry.relativelyLimitPreserving_of_isLocallyOfFinitePresentation`.

The converse is obtained from the two criteria already available, and not from the source's
own route. The affine-limit criterion of Tag 06BC turns relative limit preservation into the
statement that the comparison square of a cofiltered inverse limit of affine objects is
cartesian; a cartesian square of sets is in particular surjective onto the fibre product of
its other two corners, which is exactly the hypothesis of the surjective affine-limit
criterion of Tag 0CM6, and that criterion concludes local finite presentation. Injectivity
of the comparison map, which Tag 06BC also delivers, is not needed.

That route discharges the set-theoretic caveat the source's proof of Stacks 04AK closes with
— only affine schemes isomorphic to objects of the site may be used, and there are enough of
them — because it is Tag 0CM6 which builds the required inverse systems inside the
size-bounded site, out of the spectra of the finitely presented subalgebras of a ring of
functions. The source instead reduces along étale charts to the scheme-level statement of
Stacks 01ZC, whose own implication (2) ⇒ (1) tests inverse systems of arbitrary affine
schemes and so cannot be fed a hypothesis which only sees systems internal to the site.

*Index universes.* Both sides are read at index categories in the universe `u` of the
schemes, which is the size at which the inverse systems of the source — directed systems of
affine objects of the site — arise, and the common size of the criteria of Tags 06BC and
0CM6. Relative limit preservation at a larger index universe specialises to this one, so the
hypothesis of the converse is the weakest of that family.

*The two shapes of the comparison condition.* Tag 06BC states the cartesian square after
applying `CategoryTheory.uliftFunctor`, so that the colimits exist without a
universe-inclusion hypothesis, while Tag 0CM6 asks for surjectivity of the unlifted
comparison map. At the index universe used here the lift is
`CategoryTheory.uliftFunctor.{u, u}`, and the two transformations `uliftUpNat` and
`uliftDownNat` move elements between the two shapes. They are phrased as transformations of
presheaves rather than as `ULift.up` and `ULift.down` so that the elements they produce carry
the type the composite functor assigns, which is what the colimit of the composite expects.

## References

* [Stacks Project, Tag 04AK](https://stacks.math.columbia.edu/tag/04AK)
* [Stacks Project, Tag 049J](https://stacks.math.columbia.edu/tag/049J)
* [Stacks Project, Tag 06BC](https://stacks.math.columbia.edu/tag/06BC)
* [Stacks Project, Tag 0CM6](https://stacks.math.columbia.edu/tag/0CM6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

section Ulift

variable {C : Type*} [Category C]

/-- Lifting the values of a functor to types, as a transformation into its composite with
`CategoryTheory.uliftFunctor.{u, u}`. -/
private def uliftUpNat (Z : C ⥤ Type u) : Z ⟶ Z ⋙ CategoryTheory.uliftFunctor.{u, u} where
  app _ := ↾ULift.up
  naturality _ _ _ := rfl

/-- Unlifting the values of a functor to types, as a transformation out of its composite with
`CategoryTheory.uliftFunctor.{u, u}`. -/
private def uliftDownNat (Z : C ⥤ Type u) : Z ⋙ CategoryTheory.uliftFunctor.{u, u} ⟶ Z where
  app _ := ↾ULift.down
  naturality _ _ _ := rfl

end Ulift

/-- The map of colimits induced by a transformation acts on classes through the
transformation. -/
private theorem colimMap_apply_ι {J : Type u} [Category.{u} J] {F G : J ⥤ Type u}
    [HasColimit F] [HasColimit G] (α : F ⟶ G) (j : J) (z : F.obj j) :
    colimMap α (colimit.ι F j z) = colimit.ι G j (α.app j z) :=
  congrArg (fun g : F.obj j ⟶ colimit G => g z) (ι_colimMap α j)

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The surjectivity hypothesis of Tag 0CM6 holds for a relatively limit-preserving
transformation of presheaves on the big fppf site of `S`.

The affine-limit criterion of Tag 06BC makes the comparison square of the inverse system
cartesian after lifting the values along `CategoryTheory.uliftFunctor.{u, u}`; a cartesian
square of sets is surjective onto the fibre product of its other two corners, and the
unlifting transformation carries the resulting antecedent back down. -/
private theorem affineLimit_surjective_of_relativelyLimitPreserving
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Y)
    (hf : RelativelyLimitPreserving.{u, u, u, u} B S hS f)
    (I : Type u) [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ BigFppfOver B S hS) (c : Cone D)
    (hc : IsLimit ((BigFppfOver.toScheme B S hS).mapCone c))
    (hD : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (D.obj i)))
    (hpt : IsAffine ((BigFppfOver.toScheme B S hS).obj c.pt))
    (x : X.obj (op c.pt)) (y : colimit (D.op ⋙ Y))
    (hxy : f.app (op c.pt) x = colimit.desc (D.op ⋙ Y) (Y.mapCocone c.op) y) :
    ∃ z : colimit (D.op ⋙ X),
      colimit.desc (D.op ⋙ X) (X.mapCocone c.op) z = x ∧
      colimMap (Functor.whiskerLeft D.op f) z = y := by
  have hsq : IsPullback
      (colimit.desc (D.op ⋙ X ⋙ CategoryTheory.uliftFunctor.{u, u})
        ((X ⋙ CategoryTheory.uliftFunctor.{u, u}).mapCocone c.op))
      (colimMap (Functor.whiskerLeft D.op
        (Functor.whiskerRight f CategoryTheory.uliftFunctor.{u, u})))
      (CategoryTheory.uliftFunctor.{u, u}.map (f.app (op c.pt)))
      (colimit.desc (D.op ⋙ Y ⋙ CategoryTheory.uliftFunctor.{u, u})
        ((Y ⋙ CategoryTheory.uliftFunctor.{u, u}).mapCocone c.op)) :=
    (relativelyLimitPreserving_iff_affineLimit_isPullback.{u, u, u, u} B S hS f).mp hf
      I D c hc hD hpt
  obtain ⟨i, yi, hyi⟩ :=
    Types.jointly_surjective_of_isColimit (colimit.isColimit (D.op ⋙ Y)) y
  rw [colimit.cocone_ι] at hyi
  -- the lifted section of the target at the stage `i`
  set yi' := (Functor.whiskerLeft D.op (uliftUpNat Y)).app i yi with hyi'
  have hbase : f.app (op c.pt) x = (Y.mapCocone c.op).ι.app i yi := by
    rw [hxy, ← hyi]
    exact colimit.ι_desc_apply ..
  have key : CategoryTheory.uliftFunctor.{u, u}.map (f.app (op c.pt))
        ((uliftUpNat X).app (op c.pt) x) =
      colimit.desc (D.op ⋙ Y ⋙ CategoryTheory.uliftFunctor.{u, u})
          ((Y ⋙ CategoryTheory.uliftFunctor.{u, u}).mapCocone c.op)
        (colimit.ι (D.op ⋙ Y ⋙ CategoryTheory.uliftFunctor.{u, u}) i yi') :=
    (congrArg (fun t => (uliftUpNat Y).app (op c.pt) t) hbase).trans
      (colimit.ι_desc_apply
        ((Y ⋙ CategoryTheory.uliftFunctor.{u, u}).mapCocone c.op) i yi').symm
  obtain ⟨e, he₁, he₂⟩ :=
    Types.exists_of_isPullback hsq ((uliftUpNat X).app (op c.pt) x) _ key
  obtain ⟨j, w, hw⟩ := Types.jointly_surjective_of_isColimit
    (colimit.isColimit (D.op ⋙ X ⋙ CategoryTheory.uliftFunctor.{u, u})) e
  rw [colimit.cocone_ι] at hw
  subst hw
  refine ⟨colimit.ι (D.op ⋙ X) j
    ((Functor.whiskerLeft D.op (uliftDownNat X)).app j w), ?_, ?_⟩
  · have h₁ : ((X ⋙ CategoryTheory.uliftFunctor.{u, u}).mapCocone c.op).ι.app j w =
        (uliftUpNat X).app (op c.pt) x :=
      (colimit.ι_desc_apply ..).symm.trans he₁
    exact (colimit.ι_desc_apply ..).trans
      (congrArg (fun t => (uliftDownNat X).app (op c.pt) t) h₁)
  · have h₂ : colimit.ι (D.op ⋙ Y ⋙ CategoryTheory.uliftFunctor.{u, u}) j
          ((Functor.whiskerLeft D.op
            (Functor.whiskerRight f CategoryTheory.uliftFunctor.{u, u})).app j w) =
        colimit.ι (D.op ⋙ Y ⋙ CategoryTheory.uliftFunctor.{u, u}) i yi' :=
      (colimMap_apply_ι _ j w).symm.trans he₂
    calc colimMap (Functor.whiskerLeft D.op f)
            (colimit.ι (D.op ⋙ X) j ((Functor.whiskerLeft D.op (uliftDownNat X)).app j w))
        = colimit.ι (D.op ⋙ Y) j ((Functor.whiskerLeft D.op f).app j
            ((Functor.whiskerLeft D.op (uliftDownNat X)).app j w)) :=
          colimMap_apply_ι _ j _
      _ = colimMap (Functor.whiskerLeft D.op (uliftDownNat Y))
            (colimit.ι (D.op ⋙ Y ⋙ CategoryTheory.uliftFunctor.{u, u}) j
              ((Functor.whiskerLeft D.op
                (Functor.whiskerRight f CategoryTheory.uliftFunctor.{u, u})).app j w)) :=
          (colimMap_apply_ι (Functor.whiskerLeft D.op (uliftDownNat Y)) j
            ((Functor.whiskerLeft D.op
              (Functor.whiskerRight f CategoryTheory.uliftFunctor.{u, u})).app j w)).symm
      _ = colimMap (Functor.whiskerLeft D.op (uliftDownNat Y))
            (colimit.ι (D.op ⋙ Y ⋙ CategoryTheory.uliftFunctor.{u, u}) i yi') :=
          congrArg (fun t => colimMap (Functor.whiskerLeft D.op (uliftDownNat Y)) t) h₂
      _ = colimit.ι (D.op ⋙ Y) i yi := colimMap_apply_ι _ i _
      _ = y := hyi

/-- **Stacks 04AK.** A morphism of algebraic spaces over a scheme `S` is locally of finite
presentation if and only if it is relatively limit preserving as a transformation of functors
on the big fppf site of `S`.

Both conditions are read at index categories in the universe of the schemes. -/
@[stacks 04AK]
theorem isLocallyOfFinitePresentation_iff_relativelyLimitPreserving
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsLocallyOfFinitePresentation B S hS f ↔
      RelativelyLimitPreserving.{u, u, u, u} B S hS f :=
  ⟨relativelyLimitPreserving_of_isLocallyOfFinitePresentation B S hS hX hY,
    fun hf =>
      _root_.AlgebraicGeometry.Space.isLocallyOfFinitePresentation_of_relativelyLimitPreserving
        B S hS hf⟩

end AlgebraicGeometry.Space

end
