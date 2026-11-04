module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangePastingOnRingedTopoi
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.BaseChangeMatePasting

/-!
# Horizontal pasting of the base change mate

Two commutative squares sharing a vertical edge paste to a commutative rectangle:

```
        g''        g'
  X'' ———→ X' ———→ X
   | f''     | f'    | f
   v         v       v
  Y'' ———→ Y' ———→ Y
         h         g
```

This file proves that the underived base change map of the rectangle is the composite of the
two base change maps of the squares, read through the composition comparisons of the two
composite horizontal inverse images.  This is the underived shape of the horizontal pasting
law, **Stacks 0E47**, for the base change map `Stacks.Cohomology.BaseChange.mate`.

## Main results

* `Stacks.Cohomology.BaseChange.mate_horizontal`: the pasting law — the base change map of the
  rectangle is the composite of the two base change maps of the squares.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 0736](https://stacks.math.columbia.edu/tag/0736)
* [Stacks Project, Tag 03D8](https://stacks.math.columbia.edu/tag/03D8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace Stacks.Cohomology.BaseChange

section Horizontal

variable {A B C D C₂ D₂ : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
    [Category* C₂] [Category* D₂]
    {Lf : B ⥤ A} {F : A ⥤ B} (adjf : Lf ⊣ F)
    {Lf' : D ⥤ C} {F' : C ⥤ D} (adjf' : Lf' ⊣ F')
    {Lf'' : D₂ ⥤ C₂} {F'' : C₂ ⥤ D₂} (adjf'' : Lf'' ⊣ F'')
    {G : B ⥤ D} {P : D ⥤ B} (adjg : G ⊣ P)
    {G' : A ⥤ C} {P' : C ⥤ A} (adjg' : G' ⊣ P')
    {H : D ⥤ D₂} {Q : D₂ ⥤ D} (adjh : H ⊣ Q)
    {H' : C ⥤ C₂} {Q' : C₂ ⥤ C} (adjh' : H' ⊣ Q')
    {G₀ : B ⥤ D₂} {P₀ : D₂ ⥤ B} (adjg₀ : G₀ ⊣ P₀)
    {G'₀ : A ⥤ C₂} {P'₀ : C₂ ⥤ A} (adjg'₀ : G'₀ ⊣ P'₀)
    (e : P' ⋙ F ≅ F' ⋙ P) (e₂ : Q' ⋙ F' ≅ F'' ⋙ Q) (e₀ : P'₀ ⋙ F ≅ F'' ⋙ P₀)
    (eH : G ⋙ H ≅ G₀) (eG : G' ⋙ H' ≅ G'₀)
    (α : TwoSquare G Lf Lf' G') (α₂ : TwoSquare H Lf' Lf'' H')
    (α₀ : TwoSquare G₀ Lf Lf'' G'₀)

/-- Horizontal pasting of the base change mate, the underived shape of **Stacks 0E47**: for two
commutative squares sharing a vertical edge, the base change map of the composite rectangle is
the composite of the two base change maps, read through the composition comparisons `eH` and
`eG` of the two composite horizontal inverse images.

The three squares are presented by their comparisons `α`, `α₂`, `α₀` of composite inverse
images, each the conjugate of the corresponding comparison of composite direct images
(**Stacks 03D8**), and `hs` is the cocycle condition expressing the rectangle's comparison as
the pasting of the two squares' through `eH` and `eG`. -/
theorem mate_horizontal
    (hα : conjugateEquiv (adjf.comp adjg') (adjg.comp adjf') α = e.hom)
    (hα₂ : conjugateEquiv (adjf'.comp adjh') (adjh.comp adjf'') α₂ = e₂.hom)
    (hα₀ : conjugateEquiv (adjf.comp adjg'₀) (adjg₀.comp adjf'') α₀ = e₀.hom)
    (hs : ∀ M : B, Lf''.map (eH.inv.app M) ≫ α₂.app (G.obj M) ≫
      H'.map (α.app M) ≫ eG.hom.app (Lf.obj M) = α₀.app M)
    (K : A) :
    eH.inv.app (F.obj K) ≫ H.map ((mate adjg adjg' F F' e).app K) ≫
        (mate adjh adjh' F' F'' e₂).app (G'.obj K) ≫ F''.map (eG.hom.app K) =
      (mate adjg₀ adjg'₀ F F'' e₀).app K :=
  Stacks.Cohomology.DerivedBaseChangePasting.baseChangeMate_horizontal adjf adjf' adjf''
    eG eH (fun M => α.app M) α₂ (𝟙 _) (𝟙 _) (fun M => α₀.app M)
    (fun M => by simpa using hs M) K _ _ _
    (homEquiv_symm_mate_app adjg adjg' e adjf adjf' α hα K)
    (by
      simpa using homEquiv_symm_mate_app adjh adjh' e₂ adjf' adjf'' α₂ hα₂ (G'.obj K))
    (homEquiv_symm_mate_app adjg₀ adjg'₀ e₀ adjf adjf'' α₀ hα₀ K)

end Horizontal

end Stacks.Cohomology.BaseChange

end
