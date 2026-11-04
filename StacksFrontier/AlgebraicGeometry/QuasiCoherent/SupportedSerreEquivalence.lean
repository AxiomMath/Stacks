module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.FinitePresentationEquivalence
public import StacksFrontier.CategoryTheory.Abelian.SerreCoproductClosure

/-!
# An equivalence of quasi-coherent modules preserves support containment

Let `X` and `Y` be quasi-compact and quasi-separated schemes and let
`e : QCoh(𝒪_X) ≌ QCoh(𝒪_Y)` be an equivalence of their categories of quasi-coherent modules.
If `G` is a finitely presented quasi-coherent module on `X`, then `e` carries the
quasi-coherent modules supported on the support of `G` onto the quasi-coherent modules
supported on the support of `e.functor.obj G`, bijectively.

## Main results

* `AlgebraicGeometry.isSupportedOn_map_equivalence_iff` — a quasi-coherent module is supported
  on the support of `G` exactly when its image is supported on the support of the image of `G`.
* `AlgebraicGeometry.supportContained_map_equivalence` — **the same statement as an equality of
  classes of objects**: the modules supported on the support of the image of `G` are exactly the
  inverse image, along the inverse equivalence, of the modules supported on the support of `G`.

## Implementation notes

The only input beyond formal category theory is [Stacks, Tag 0GPG]
(`AlgebraicGeometry.supportContained_eq_serreCoproductClosure`), which identifies the modules
supported on the support of a finitely presented module with the Serre–coproduct closure of
that module.  The latter description is purely categorical, hence transported by an equivalence
(`AlgebraicGeometry.serreCoproductClosure_map_functor`); conjugating with [Stacks, Tag 0GPG] at
`X` and at `Y` turns that transport back into a statement about supports.

Applying [Stacks, Tag 0GPG] on `Y` needs the image `e.functor.obj G` to be finitely presented
too; that is not a hypothesis but a consequence of
`AlgebraicGeometry.isFinitePresentation_map_of_equivalence`, which is [Stacks, Tag 0GPE] on
both schemes together with the categorical invariance of compactness.

The generator of the closure is written `⟨G.obj, _⟩` in the statement of [Stacks, Tag 0GPG]
and `G` here; the two agree because quasi-coherence is a proposition, so the two objects of the
full subcategory are definitionally equal.

## References

* [Stacks Project, Lemma 56.2.2 (Tag 0GPG)](https://stacks.math.columbia.edu/tag/0GPG)
* [Stacks Project, Proposition 56.6.6 (Tag 0GPJ)](https://stacks.math.columbia.edu/tag/0GPJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
  [QuasiSeparatedSpace Y]
  (e : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ≌
    (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory)
  (G : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)
  [SheafOfModules.IsFinitePresentation (R := X.ringCatSheaf) G.obj]

/-- The modules supported on the support of the image of `G` form the Serre–coproduct closure of
the image of `G`. -/
private theorem supportContained_image_eq :
    (fun E' : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ↦
        IsSupportedOn E'.obj (e.functor.obj G).obj) =
      serreCoproductClosure (e.functor.obj G) :=
  have : SheafOfModules.IsFinitePresentation (R := Y.ringCatSheaf) (e.functor.obj G).obj :=
    isFinitePresentation_map_of_equivalence e G
  supportContained_eq_serreCoproductClosure Y (e.functor.obj G).obj

/-- **An equivalence of categories of quasi-coherent modules preserves and reflects support
containment in the support of a finitely presented module.** By [Stacks, Tag 0GPG] both sides
are membership in a Serre–coproduct closure, and such a closure is transported by an
equivalence. -/
theorem isSupportedOn_map_equivalence_iff
    (E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory) :
    IsSupportedOn (e.functor.obj E).obj (e.functor.obj G).obj ↔ IsSupportedOn E.obj G.obj := by
  rw [show IsSupportedOn (e.functor.obj E).obj (e.functor.obj G).obj =
        serreCoproductClosure (e.functor.obj G) (e.functor.obj E) from
      congrFun (supportContained_image_eq e G) _,
    show IsSupportedOn E.obj G.obj = serreCoproductClosure G E from
      congrFun (supportContained_eq_serreCoproductClosure X G.obj) _]
  exact serreCoproductClosure_map_obj_iff e G E

/-- **An equivalence of categories of quasi-coherent modules carries the modules supported on
the support of `G` onto the modules supported on the support of the image of `G`,
bijectively.** This is the equality of classes of objects underlying
`AlgebraicGeometry.isSupportedOn_map_equivalence_iff`. -/
theorem supportContained_map_equivalence :
    (fun E' : (SheafOfModules.isQuasicoherent Y.ringCatSheaf).FullSubcategory ↦
        IsSupportedOn E'.obj (e.functor.obj G).obj)
      = ObjectProperty.inverseImage
        (fun E : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ↦
          IsSupportedOn E.obj G.obj) e.inverse :=
  (supportContained_image_eq e G).trans
    ((serreCoproductClosure_map_functor e G).trans
      (congrArg
        (fun P : ObjectProperty
            (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory ↦
          ObjectProperty.inverseImage P e.inverse)
        (supportContained_eq_serreCoproductClosure X G.obj).symm))

end AlgebraicGeometry

end
