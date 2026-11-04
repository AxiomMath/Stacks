module

public import StacksFrontier.CategoryTheory.Sites.Localization.RelocalizeFibre

/-!
# The fibre over a section is a fibre product on the smaller slice

Let `C` be a category, let `a : A ⟶ X` be a morphism of `C`, let `α : F ⟶ G` be a morphism of
presheaves on `C/X` and let `β : h_{A → X} ⟶ G` be a section of `G` over `A → X`. The *fibre of
`α` over `β`* of `CategoryTheory.OverShriek.fibreOfSection` is a presheaf on the smaller slice
`C/A`. This file identifies it there: the square

```text
  fibreOfSection a α β  --ι-->  j^{-1} F
         |                          |
         v                          v  j^{-1} α
   h_{A → A}   ---------------->  j^{-1} G
```

whose bottom edge is the point of `j^{-1}G` named by `β`, is cartesian, `j^{-1}` denoting
restriction along `CategoryTheory.Over.map a`.

The representable presheaf of the terminal object `A → A` of `C/A` is the terminal presheaf, so
the square says that a section of the fibre over an object `W` of `C/A` is a section of `F` over
`(Over.map a).obj W` matching the restriction of `β` — which is the definition. It exhibits the
fibre as a fibre product of presheaves *on `C/A`*.

`CategoryTheory.OverShriek.isPullback_relocalizeFibreOfSectionMap` is the companion statement one
slice up: it exhibits the *relocalization* of the fibre as a fibre product of presheaves on `C/X`.

## Main definitions

* `CategoryTheory.OverShriek.pointOfSection`: the point of `j^{-1}G` over the terminal presheaf
  named by a section `β` of `G` over `A → X`, namely the family of restrictions of `β` along the
  tautological morphisms.
* `CategoryTheory.OverShriek.fibreOfSectionToId`: the structural morphism of the fibre to the
  representable presheaf of the terminal object `A → A`.

## Main results

* `CategoryTheory.OverShriek.pointOfSection_eq`: the point named by `β` is the point named by the
  identity, followed by the restriction of `β`.
* `CategoryTheory.OverShriek.isPullback_fibreOfSectionι`: the square above is cartesian.

## References

* [Stacks Project, Tag 03I5](https://stacks.math.columbia.edu/tag/03I5)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits

namespace CategoryTheory.OverShriek

universe v u

variable {C : Type u} [Category.{v} C] {X A : C} (a : A ⟶ X) {F G : (Over X)ᵒᵖ ⥤ Type v}

/-- **The point of `j^{-1}G` named by a section `β` of `G` over `A → X`**, where `j^{-1}` is
restriction along `CategoryTheory.Over.map a`: over an object `W` of `C/A` it is the restriction
of `β` along the tautological morphism `CategoryTheory.OverShriek.overMapTautHom` of `W`. Its
source is the representable presheaf of the terminal object `A → A` of `C/A`, so it carries no
information beyond that family of sections. -/
def pointOfSection (β : yoneda.obj (Over.mk a) ⟶ G) :
    yoneda.obj (Over.mk (𝟙 A)) ⟶ (relocalizeRestrict a).obj G where
  app W := ↾fun _ => β.app (op ((Over.map a).obj (unop W))) (overMapTautHom a (unop W))
  naturality W W' g := by
    ext _
    exact (congrArg (fun z => β.app (op ((Over.map a).obj (unop W'))) z)
        (overMap_map_comp_overMapTautHom a g.unop)).symm.trans
      (NatTrans.naturality_apply β ((Over.map a).map g.unop).op
        (overMapTautHom a (unop W)))

/-- The point named by `β` is the point named by the identity of `h_{A → X}`, followed by the
restriction of `β`. -/
theorem pointOfSection_eq (β : yoneda.obj (Over.mk a) ⟶ G) :
    pointOfSection a β =
      pointOfSection a (𝟙 (yoneda.obj (Over.mk a))) ≫ (relocalizeRestrict a).map β :=
  rfl

variable (α : F ⟶ G) (β : yoneda.obj (Over.mk a) ⟶ G)

/-- The structural morphism of the fibre of `α` over `β` to the representable presheaf of the
terminal object `A → A` of `C/A`. It is the unique such morphism. -/
def fibreOfSectionToId : fibreOfSection a α β ⟶ yoneda.obj (Over.mk (𝟙 A)) where
  app W := ↾fun _ => Over.homMk (unop W).hom (Category.comp_id (unop W).hom)
  naturality _ _ _ := by
    ext _
    exact Over.mkIdTerminal.hom_ext _ _

/-- **The fibre of `α : F ⟶ G` over a section `β` of `G` over `A → X` is a fibre product on the
slice `C/A`.** Its inclusion into the restriction of `F` along `CategoryTheory.Over.map a` and its
structural morphism to the representable presheaf of the terminal object `A → A` exhibit it as
the fibre product of the restriction of `α` and of the point of the restriction of `G` named by
`β`. -/
theorem isPullback_fibreOfSectionι :
    IsPullback (fibreOfSectionι a α β) (fibreOfSectionToId a α β)
      ((relocalizeRestrict a).map α) (pointOfSection a β) := by
  refine IsPullback.of_forall_isPullback_app fun W ↦ ?_
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext s
    exact s.2
  · rintro s s' ⟨h, -⟩
    exact Subtype.ext h
  · intro s _ hs
    exact ⟨⟨s, hs⟩, rfl, Over.mkIdTerminal.hom_ext _ _⟩

end CategoryTheory.OverShriek

end
