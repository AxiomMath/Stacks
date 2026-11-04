module

public import StacksFrontier.AlgebraicGeometry.Chow.ChangeBaseScheme.Cycles
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.DisjointSections
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProjectiveLineBaseChange

/-!
# The family of projective lines under a change of the base scheme

Let `f : X ⟶ S` be a morphism and let `g : S' ⟶ S` be a second morphism of base schemes, with
`X' = X ×_S S'`. The two families of projective lines

  `X ×_S 𝐏¹_S`  and  `X' ×_{S'} 𝐏¹_{S'}`

are related by a morphism over the projection `X' ⟶ X`, and that morphism is a base change: the
second family is the first pulled back along `g`. This file builds that morphism, proves that the
resulting square is cartesian, and records that a locally finite family of closed subschemes of
the first family stays locally finite when pulled back to the second.

The content is geometry of the ambient family only; nothing here mentions cycles.

## Main definitions

* `Stacks.Chow.projectiveLineProductBaseChange` — the morphism
  `X' ×_{S'} 𝐏¹_{S'} ⟶ X ×_S 𝐏¹_S`.
* `Stacks.Chow.baseChangedFamily` — a closed subscheme of `X ×_S 𝐏¹_S` pulled back along it.
* `Stacks.Chow.projectiveLineProductMap` — the morphism `Y ×_{S'} 𝐏¹_{S'} ⟶ X ×_S 𝐏¹_S`
  attached to a commuting square `p ≫ f = q ≫ g`.
* `Stacks.Chow.baseChangedFamilyOfSquare` — a closed subscheme of `X ×_S 𝐏¹_S` pulled back
  along that morphism.

## Main results

* `Stacks.Chow.isPullback_projectiveLineProductBaseChange` — the morphism exhibits
  `X' ×_{S'} 𝐏¹_{S'}` as the base change of `X ×_S 𝐏¹_S` along `g`.
* `Stacks.Chow.locallyFinite_support_baseChangedFamily` — a locally finite family of closed
  subschemes stays locally finite after the base change.
* `Stacks.Chow.isPullback_projectiveLineProductMap` — for a cartesian square the induced
  morphism of families is again a base change along `g`.

## Implementation notes

The `𝐏¹`-direction of the morphism is
`Stacks.Chow.projectiveLineBaseChange g : 𝐏¹_{S'} ⟶ 𝐏¹_S` of
`StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProjectiveLineBaseChange`, whose cartesian square
`Stacks.Chow.isPullback_projectiveLineBaseChange` is what makes the square below cartesian after
two pastings. Everything is stated as a cartesian square rather than through composites of
isomorphisms, for the reason recorded in that file: `Stacks.Chow.relativeProjectiveLine` is itself
a pullback, and a definition whose body composes canonical isomorphisms out of it makes the kernel
unfold its limit cone.

### What is not here

The compatibility of the two distinguished sections with
`Stacks.Chow.projectiveLineProductBaseChange`, and hence of the zero and infinity fibres of a
closed subscheme, is not proved here. It is the next statement a cycle-level argument needs, and
it meets a transparency crossing: `relativeProjectiveLine S ↘ S` is the first projection of a
pullback only up to the `CategoryTheory.Over` instance — that is
`Stacks.Chow.relativeProjectiveLine_over_hom`, which is `rfl` — so `pullback.lift_fst` does not
fire at it, and unfolding the instance makes `simp` expand the limit cone. Stating it needs each
spelling of the structure morphism given its own declaration, as
`StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.ProjectiveLineBaseChange` records for the same
object.

## References

* [Stacks Project, Tag 0FVG](https://stacks.math.columbia.edu/tag/0FVG)
* [Stacks Project, Tag 0FVI](https://stacks.math.columbia.edu/tag/0FVI)
* [Stacks Project, Tag 02S5](https://stacks.math.columbia.edu/tag/02S5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

section Map

variable {X S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)

/-- The morphism `X' ×_{S'} 𝐏¹_{S'} ⟶ X ×_S 𝐏¹_S` over the projection `X' ⟶ X`, for
`X' = X ×_S S'`: it is that projection on the first factor and
`Stacks.Chow.projectiveLineBaseChange g` on the `𝐏¹`-factor. -/
def projectiveLineProductBaseChange :
    projectiveLineProduct (pullback.snd f g) ⟶ projectiveLineProduct f :=
  pullback.lift
    (pullback.fst (pullback.snd f g) (relativeProjectiveLine S' ↘ S') ≫ pullback.fst f g)
    (pullback.snd (pullback.snd f g) (relativeProjectiveLine S' ↘ S') ≫
      projectiveLineBaseChange g)
    (by
      calc (pullback.fst (pullback.snd f g) (relativeProjectiveLine S' ↘ S') ≫
              pullback.fst f g) ≫ f
          = pullback.fst (pullback.snd f g) (relativeProjectiveLine S' ↘ S') ≫
              pullback.snd f g ≫ g := by
            rw [Category.assoc, pullback.condition]
        _ = (pullback.fst (pullback.snd f g) (relativeProjectiveLine S' ↘ S') ≫
              pullback.snd f g) ≫ g := by rw [Category.assoc]
        _ = (pullback.snd (pullback.snd f g) (relativeProjectiveLine S' ↘ S') ≫
              (relativeProjectiveLine S' ↘ S')) ≫ g := by rw [pullback.condition]
        _ = (pullback.snd (pullback.snd f g) (relativeProjectiveLine S' ↘ S') ≫
              projectiveLineBaseChange g) ≫ (relativeProjectiveLine S ↘ S) := by
            rw [Category.assoc, Category.assoc, projectiveLineBaseChange_over])

/-- On the first factor, `projectiveLineProductBaseChange f g` is the projection `X' ⟶ X` composed
with the first projection of `X' ×_{S'} 𝐏¹_{S'}`. -/
@[reassoc (attr := simp)]
theorem projectiveLineProductBaseChange_comp_fst :
    projectiveLineProductBaseChange f g ≫ pullback.fst f (relativeProjectiveLine S ↘ S) =
      pullback.fst (pullback.snd f g) (relativeProjectiveLine S' ↘ S') ≫ pullback.fst f g :=
  pullback.lift_fst _ _ _

/-- On the `𝐏¹`-factor, `projectiveLineProductBaseChange f g` is
`Stacks.Chow.projectiveLineBaseChange g` composed with the second projection of
`X' ×_{S'} 𝐏¹_{S'}`. -/
@[reassoc (attr := simp)]
theorem projectiveLineProductBaseChange_comp_snd :
    projectiveLineProductBaseChange f g ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      pullback.snd (pullback.snd f g) (relativeProjectiveLine S' ↘ S') ≫
        projectiveLineBaseChange g :=
  pullback.lift_snd _ _ _

/-- A morphism of families `Y ×_{S'} 𝐏¹_{S'} ⟶ X ×_S 𝐏¹_S` that is `p` on the first factor and
`Stacks.Chow.projectiveLineBaseChange g` on the `𝐏¹`-factor is a base change along `g`. -/
private theorem isPullback_projectiveLineProduct_of_comp {X Y S S' : Scheme.{u}} {f : X ⟶ S}
    {g : S' ⟶ S} {p : Y ⟶ X} {q : Y ⟶ S'} (sq : IsPullback p q f g)
    (φ : projectiveLineProduct q ⟶ projectiveLineProduct f)
    (h₁ : φ ≫ pullback.fst f (relativeProjectiveLine S ↘ S) =
      pullback.fst q (relativeProjectiveLine S' ↘ S') ≫ p)
    (h₂ : φ ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      pullback.snd q (relativeProjectiveLine S' ↘ S') ≫ projectiveLineBaseChange g) :
    IsPullback φ (pullback.fst q (relativeProjectiveLine S' ↘ S') ≫ q)
      (pullback.fst f (relativeProjectiveLine S ↘ S) ≫ f) g := by
  have hfam := (IsPullback.of_hasPullback q (relativeProjectiveLine S' ↘ S')).flip
  have hline := (isPullback_projectiveLineBaseChange g).flip
  have hpaste := hfam.paste_horiz hline
  have hbase := (IsPullback.of_hasPullback f (relativeProjectiveLine S ↘ S)).flip
  rw [← sq.w, ← h₂] at hpaste
  exact (hpaste.of_right h₁ hbase).paste_vert sq

/-- **The family of projective lines is stable under a change of the base scheme.** The square

```
X' ×_{S'} 𝐏¹_{S'} ---> X ×_S 𝐏¹_S
        |                   |
        v                   v
       S' ------ g ------>  S
```

is cartesian, the vertical maps being the structure morphisms of the two families. -/
theorem isPullback_projectiveLineProductBaseChange :
    IsPullback (projectiveLineProductBaseChange f g)
      (pullback.fst (pullback.snd f g) (relativeProjectiveLine S' ↘ S') ≫ pullback.snd f g)
      (pullback.fst f (relativeProjectiveLine S ↘ S) ≫ f) g :=
  isPullback_projectiveLineProduct_of_comp (IsPullback.of_hasPullback f g) _
    (projectiveLineProductBaseChange_comp_fst f g) (projectiveLineProductBaseChange_comp_snd f g)

/-- A closed subscheme of `X ×_S 𝐏¹_S`, pulled back to the family over the new base. -/
def baseChangedFamily (W : (projectiveLineProduct f).IdealSheafData) :
    (projectiveLineProduct (pullback.snd f g)).IdealSheafData :=
  W.comap (projectiveLineProductBaseChange f g)

/-- The support of the base-changed family is the preimage of the support. -/
theorem coe_support_baseChangedFamily (W : (projectiveLineProduct f).IdealSheafData) :
    ((baseChangedFamily f g W).support : Set (projectiveLineProduct (pullback.snd f g))) =
      projectiveLineProductBaseChange f g ⁻¹'
        ((W.support : Set (projectiveLineProduct f))) := by
  rw [baseChangedFamily, Scheme.IdealSheafData.support_comap]
  rfl

/-- The base change of a locally finite family of closed subschemes is locally finite: the
supports are the preimages of the supports along a continuous map. -/
theorem locallyFinite_support_baseChangedFamily {J : Type u}
    (W : J → (projectiveLineProduct f).IdealSheafData)
    (hLoc : LocallyFinite fun j ↦ ((W j).support : Set (projectiveLineProduct f))) :
    LocallyFinite fun j ↦ ((baseChangedFamily f g (W j)).support :
      Set (projectiveLineProduct (pullback.snd f g))) := by
  have hsupp : (fun j ↦ ((baseChangedFamily f g (W j)).support :
      Set (projectiveLineProduct (pullback.snd f g)))) =
      fun j ↦ projectiveLineProductBaseChange f g ⁻¹'
        ((W j).support : Set (projectiveLineProduct f)) :=
    funext fun j ↦ coe_support_baseChangedFamily f g (W j)
  rw [hsupp]
  exact hLoc.preimage_continuous (projectiveLineProductBaseChange f g).continuous

end Map

section Square

variable {X Y S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) {p : Y ⟶ X} {q : Y ⟶ S'}

/-- The morphism `Y ×_{S'} 𝐏¹_{S'} ⟶ X ×_S 𝐏¹_S` attached to a commuting square
`p ≫ f = q ≫ g`: it is `p` on the first factor and `Stacks.Chow.projectiveLineBaseChange g` on
the `𝐏¹`-factor. For the chosen fibre product it is
`Stacks.Chow.projectiveLineProductBaseChange`. -/
def projectiveLineProductMap (w : p ≫ f = q ≫ g) :
    projectiveLineProduct q ⟶ projectiveLineProduct f :=
  pullback.lift (pullback.fst q (relativeProjectiveLine S' ↘ S') ≫ p)
    (pullback.snd q (relativeProjectiveLine S' ↘ S') ≫ projectiveLineBaseChange g)
    (by
      calc (pullback.fst q (relativeProjectiveLine S' ↘ S') ≫ p) ≫ f
          = pullback.fst q (relativeProjectiveLine S' ↘ S') ≫ q ≫ g := by
            rw [Category.assoc, w]
        _ = (pullback.fst q (relativeProjectiveLine S' ↘ S') ≫ q) ≫ g := by rw [Category.assoc]
        _ = (pullback.snd q (relativeProjectiveLine S' ↘ S') ≫
              (relativeProjectiveLine S' ↘ S')) ≫ g := by rw [pullback.condition]
        _ = (pullback.snd q (relativeProjectiveLine S' ↘ S') ≫
              projectiveLineBaseChange g) ≫ (relativeProjectiveLine S ↘ S) := by
            rw [Category.assoc, Category.assoc, projectiveLineBaseChange_over])

/-- The first factor of the morphism of families attached to a commuting square is `p`. -/
@[reassoc (attr := simp)]
theorem projectiveLineProductMap_comp_fst (w : p ≫ f = q ≫ g) :
    projectiveLineProductMap f g w ≫ pullback.fst f (relativeProjectiveLine S ↘ S) =
      pullback.fst q (relativeProjectiveLine S' ↘ S') ≫ p :=
  pullback.lift_fst _ _ _

/-- The `𝐏¹`-factor of the morphism of families attached to a commuting square is
`Stacks.Chow.projectiveLineBaseChange g`. -/
@[reassoc (attr := simp)]
theorem projectiveLineProductMap_comp_snd (w : p ≫ f = q ≫ g) :
    projectiveLineProductMap f g w ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      pullback.snd q (relativeProjectiveLine S' ↘ S') ≫ projectiveLineBaseChange g :=
  pullback.lift_snd _ _ _

/-- At the chosen fibre product the morphism of families attached to a commuting square is
`Stacks.Chow.projectiveLineProductBaseChange`. -/
theorem projectiveLineProductMap_pullback_condition :
    projectiveLineProductMap f g (pullback.condition (f := f) (g := g)) =
      projectiveLineProductBaseChange f g := by
  apply pullback.hom_ext
  · rw [projectiveLineProductMap_comp_fst, projectiveLineProductBaseChange_comp_fst]
  · rw [projectiveLineProductMap_comp_snd, projectiveLineProductBaseChange_comp_snd]

/-- **The family of projective lines is stable along an arbitrary cartesian square.** If `Y` is
the base change of `X` along `g : S' ⟶ S`, presented by the cartesian square `p ≫ f = q ≫ g`,
then the square

```
Y ×_{S'} 𝐏¹_{S'} ---> X ×_S 𝐏¹_S
        |                   |
        v                   v
       S' ------ g ------>  S
```

is cartesian, the vertical maps being the structure morphisms of the two families. -/
theorem isPullback_projectiveLineProductMap (sq : IsPullback p q f g) :
    IsPullback (projectiveLineProductMap f g sq.w)
      (pullback.fst q (relativeProjectiveLine S' ↘ S') ≫ q)
      (pullback.fst f (relativeProjectiveLine S ↘ S) ≫ f) g :=
  isPullback_projectiveLineProduct_of_comp sq _ (projectiveLineProductMap_comp_fst f g sq.w)
    (projectiveLineProductMap_comp_snd f g sq.w)

/-- A closed subscheme of `X ×_S 𝐏¹_S`, pulled back to the family over `S'` along the morphism
attached to a commuting square `p ≫ f = q ≫ g`. -/
def baseChangedFamilyOfSquare (w : p ≫ f = q ≫ g)
    (W : (projectiveLineProduct f).IdealSheafData) :
    (projectiveLineProduct q).IdealSheafData :=
  W.comap (projectiveLineProductMap f g w)

end Square

end Stacks.Chow

end

