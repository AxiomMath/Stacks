module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangePastingOnRingedTopoi
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.TwoIsoCoherenceOfToposHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Pasting of derived base change maps along morphisms of ringed topoi

Consider a diagram of ringed topoi

```
                 g'                  g
  (Sh(C''), 𝒪_C'') ———→ (Sh(C'), 𝒪_C') ———→ (Sh(C), 𝒪_C)
         │ f''                  │ f'                │ f
         v                      v                   v
  (Sh(D''), 𝒪_D'') ———→ (Sh(D'), 𝒪_D') ———→ (Sh(D), 𝒪_D)
                 h'                  h
```

whose two squares commute up to given 2-isomorphisms `s : h ∘ f' ≅ f ∘ g` and
`s' : h' ∘ f'' ≅ f' ∘ g'` (Stacks 04IC), the outer rectangle commuting up to their pasting
`AlgebraicGeometry.RingedToposHom.TwoIso.pasteHorizontal s s'`.  Stacks 0E47 says that the base
change maps of Remark 07A7 for the two squares compose to the base change map of the rectangle:
the composite

`L(h ∘ h')^* Rf_* = L(h')^* Lh^* Rf_* ⟶ L(h')^* Rf'_* Lg^* ⟶ Rf''_* L(g')^* Lg^*
  = Rf''_* L(g ∘ g')^*`

is the base change map of the rectangle.  This file proves it for arbitrary morphisms of ringed
topoi in the sense of Stacks 01D3, part (2), at free universes.

## Main results

* `squareComparison_paste`: the formal pasting identity for the comparisons of iterated derived
  pullbacks around the two squares, on abstract functors.
* `derivedBaseChangeMapOfTwoIso_horizontal`: **Stacks 0E47**.

## Implementation notes

The base change map of a square is the mate, under the derived adjunctions `Lf^* ⊣ Rf_*` of
Stacks 07A6, of the comparison of the two iterated derived pullbacks around the square, and
mates of horizontally pasted squares paste
(`Stacks.Cohomology.DerivedBaseChangePasting.baseChangeMate_horizontal`).  What has to be shown
is therefore that the comparison for the rectangle is the pasting of the comparisons of the two
squares, and `squareComparison_paste` reduces that to five identities: the cocycle identity of
Stacks 0D6D for the three bracketings met on the way, and the naturality of the composition
isomorphism of Stacks 0D6D in a 2-isomorphism of either factor, all proved in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/TwoIsoCoherenceOfToposHom.lean`.

The assembly `derivedBaseChangeMap_paste_of_iso` is stated over the derived categories of the six
ringed topoi with every functor and adjunction a variable, for the reason recorded in that file:
its instance at the derived functors is then checked by the kernel syntactically.

## References

* [Stacks Project, Tag 0E47](https://stacks.math.columbia.edu/tag/0E47)
* [Stacks Project, Tag 07A7](https://stacks.math.columbia.edu/tag/07A7)
* [Stacks Project, Tag 0D6D](https://stacks.math.columbia.edu/tag/0D6D)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.DerivedPullbackCompositionOfToposHom

namespace Stacks.Cohomology.DerivedBaseChangeOfToposHom

universe vC uC wC vC' uC' wC' vC'' uC'' wC'' vD uD wD vD' uD' wD' vD'' uD'' wD''

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

noncomputable section

/-- **The pasting identity for the comparisons of iterated derived pullbacks, on abstract
functors.**  For a rectangle made of two 2-commutative squares, the comparison of the two
iterated derived pullbacks around the rectangle is the horizontal composite of those of the two
squares, provided the five structural compatibilities hold: the three cocycle identities `hA₁`,
`hA₂`, `hA₃` (one for each bracketing met on the way, the associator 2-isomorphism being carried
by `a₁`, `a₂`, `a₃`), the naturality `hW`, `hL` of the composition comparisons in a
2-isomorphism of one factor, and the description `hT` of the comparison of the rectangle's
2-isomorphism as the composite of the five pieces it is pasted from. -/
theorem squareComparison_paste {DY DY' DY'' DX DX' DX'' : Type*}
    [Category* DY] [Category* DY'] [Category* DY''] [Category* DX] [Category* DX']
    [Category* DX'']
    {Lh : DY ⥤ DY'} {Lh' : DY' ⥤ DY''} {Lhh : DY ⥤ DY''} {Lf : DY ⥤ DX} {Lf' : DY' ⥤ DX'}
    {Lf'' : DY'' ⥤ DX''} {Lg : DX ⥤ DX'} {Lg' : DX' ⥤ DX''} {Lgg : DX ⥤ DX''}
    {A₁ B₁ : DY' ⥤ DX''} {A₂ B₂ : DY ⥤ DX'} {R₀ R₁ R₂ R₃ R₄ R₅ : DY ⥤ DX''}
    (cH : Lh ⋙ Lh' ≅ Lhh) (cG : Lg ⋙ Lg' ≅ Lgg)
    (c₁ : Lh' ⋙ Lf'' ≅ A₁) (T₁ : B₁ ≅ A₁) (d₁ : Lf' ⋙ Lg' ≅ B₁)
    (c₂ : Lh ⋙ Lf' ≅ A₂) (T₂ : B₂ ≅ A₂) (d₂ : Lf ⋙ Lg ≅ B₂)
    (c₀ : Lhh ⋙ Lf'' ≅ R₀) (T₀ : R₅ ≅ R₀) (d₀ : Lf ⋙ Lgg ≅ R₅)
    (e₁ : Lh ⋙ A₁ ≅ R₁) (e₂ : Lh ⋙ B₁ ≅ R₂) (e₃ : A₂ ⋙ Lg' ≅ R₃) (e₄ : B₂ ⋙ Lg' ≅ R₄)
    (a₁ : R₁ ≅ R₀) (w₁ : R₁ ≅ R₂) (a₂ : R₂ ≅ R₃) (w₂ : R₃ ≅ R₄) (a₃ : R₅ ≅ R₄)
    (hA₁ : ∀ N, c₁.hom.app (Lh.obj N) ≫ e₁.hom.app N ≫ a₁.hom.app N =
      Lf''.map (cH.hom.app N) ≫ c₀.hom.app N)
    (hW : ∀ N, e₁.hom.app N ≫ w₁.hom.app N = T₁.inv.app (Lh.obj N) ≫ e₂.hom.app N)
    (hA₂ : ∀ N, d₁.hom.app (Lh.obj N) ≫ e₂.hom.app N ≫ a₂.hom.app N =
      Lg'.map (c₂.hom.app N) ≫ e₃.hom.app N)
    (hL : ∀ N, e₃.hom.app N ≫ w₂.hom.app N = Lg'.map (T₂.inv.app N) ≫ e₄.hom.app N)
    (hA₃ : ∀ N, cG.hom.app (Lf.obj N) ≫ d₀.hom.app N ≫ a₃.hom.app N =
      Lg'.map (d₂.hom.app N) ≫ e₄.hom.app N)
    (hT : ∀ N, T₀.inv.app N =
      a₁.inv.app N ≫ w₁.hom.app N ≫ a₂.hom.app N ≫ w₂.hom.app N ≫ a₃.inv.app N)
    (M : DY) :
    Lf''.map (cH.inv.app M) ≫
        (c₁.hom.app (Lh.obj M) ≫ T₁.inv.app (Lh.obj M) ≫ d₁.inv.app (Lh.obj M)) ≫
        Lg'.map (c₂.hom.app M ≫ T₂.inv.app M ≫ d₂.inv.app M) ≫ cG.hom.app (Lf.obj M) =
      c₀.hom.app M ≫ T₀.inv.app M ≫ d₀.inv.app M := by
  have h₁ : c₀.hom.app M = Lf''.map (cH.inv.app M) ≫ c₁.hom.app (Lh.obj M) ≫ e₁.hom.app M ≫
      a₁.hom.app M := by
    rw [hA₁ M, ← Functor.map_comp_assoc, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id,
        Category.id_comp]
  have h₂ : e₂.hom.app M ≫ a₂.hom.app M =
      d₁.inv.app (Lh.obj M) ≫ Lg'.map (c₂.hom.app M) ≫ e₃.hom.app M := by
    rw [← hA₂ M, Iso.inv_hom_id_app_assoc]
  have h₃ : e₄.hom.app M ≫ a₃.inv.app M ≫ d₀.inv.app M =
      Lg'.map (d₂.inv.app M) ≫ cG.hom.app (Lf.obj M) := by
    rw [← cancel_epi (Lg'.map (d₂.hom.app M)), ← reassoc_of% (hA₃ M), ← Functor.map_comp_assoc,
      Iso.hom_inv_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
    simp only [Iso.hom_inv_id_app_assoc, Iso.hom_inv_id_app]
    exact Category.comp_id _
  rw [hT M, h₁]
  simp only [Category.assoc, Iso.hom_inv_id_app_assoc, Functor.map_comp]
  rw [reassoc_of% (hW M), reassoc_of% h₂, reassoc_of% (hL M), h₃]

section Paste

variable {X : RingedTopos.{vC, uC, wC}} {X' : RingedTopos.{vC', uC', wC'}}
  {X'' : RingedTopos.{vC'', uC'', wC''}} {Y : RingedTopos.{vD, uD, wD}}
  {Y' : RingedTopos.{vD', uD', wD'}} {Y'' : RingedTopos.{vD'', uD'', wD''}}
  [X.J.HasSheafCompose (forget RingCat.{wC})]
  [X'.J.HasSheafCompose (forget RingCat.{wC'})]
  [X''.J.HasSheafCompose (forget RingCat.{wC''})]
  [Y.J.HasSheafCompose (forget RingCat.{wD})]
  [Y'.J.HasSheafCompose (forget RingCat.{wD'})]
  [Y''.J.HasSheafCompose (forget RingCat.{wD''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [X''.J.HasSheafCompose (forget₂ CommRingCat.{wC''} RingCat.{wC''})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{wD'} RingCat.{wD'})]
  [Y''.J.HasSheafCompose (forget₂ CommRingCat.{wD''} RingCat.{wD''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [X''.J.HasSheafCompose (forget AddCommGrpCat.{wC''})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{wD})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{wD'})]
  [Y''.J.HasSheafCompose (forget AddCommGrpCat.{wD''})]
  [HasSheafify X.J AddCommGrpCat.{wC}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify X'.J AddCommGrpCat.{wC'}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify X''.J AddCommGrpCat.{wC''}] [X''.J.WEqualsLocallyBijective AddCommGrpCat.{wC''}]
  [HasSheafify Y.J AddCommGrpCat.{wD}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{wD}]
  [HasSheafify Y'.J AddCommGrpCat.{wD'}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{wD'}]
  [HasSheafify Y''.J AddCommGrpCat.{wD''}] [Y''.J.WEqualsLocallyBijective AddCommGrpCat.{wD''}]
  [HasSheafify X.J (Type wC)] [HasSheafify X'.J (Type wC')] [HasSheafify X''.J (Type wC'')]
  [HasSheafify Y.J (Type wD)] [HasSheafify Y'.J (Type wD')] [HasSheafify Y''.J (Type wD'')]

omit [X.J.HasSheafCompose (forget RingCat.{wC})]
  [X'.J.HasSheafCompose (forget RingCat.{wC'})]
  [X''.J.HasSheafCompose (forget RingCat.{wC''})]
  [Y.J.HasSheafCompose (forget RingCat.{wD})]
  [Y'.J.HasSheafCompose (forget RingCat.{wD'})]
  [Y''.J.HasSheafCompose (forget RingCat.{wD''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [X''.J.HasSheafCompose (forget₂ CommRingCat.{wC''} RingCat.{wC''})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{wD'} RingCat.{wD'})]
  [Y''.J.HasSheafCompose (forget₂ CommRingCat.{wD''} RingCat.{wD''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [X''.J.HasSheafCompose (forget AddCommGrpCat.{wC''})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{wD})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{wD'})]
  [Y''.J.HasSheafCompose (forget AddCommGrpCat.{wD''})]
  [HasSheafify X.J (Type wC)] [HasSheafify X'.J (Type wC')] [HasSheafify X''.J (Type wC'')]
  [HasSheafify Y.J (Type wD)] [HasSheafify Y'.J (Type wD')] [HasSheafify Y''.J (Type wD'')] in
/-- **The pasting law for base change maps, over the derived categories of six ringed topoi.**
With every functor and adjunction a variable: if the comparisons of iterated pullbacks satisfy
the five identities of `squareComparison_paste`, the base change maps `bc₂`, `bc₁`, `bc₀` of the
two squares and of the rectangle, each given by its adjoint description, compose. -/
theorem derivedBaseChangeMap_paste_of_iso
    {Lh : DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{wD'} (SheafOfModules.Tensor.ringSheaf Y'.O))}
    {Lh' : DerivedCategory (SheafOfModules.{wD'} (SheafOfModules.Tensor.ringSheaf Y'.O)) ⥤
      DerivedCategory (SheafOfModules.{wD''} (SheafOfModules.Tensor.ringSheaf Y''.O))}
    {Lhh : DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{wD''} (SheafOfModules.Tensor.ringSheaf Y''.O))}
    {Lf : DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf X.O))}
    {Lf' : DerivedCategory (SheafOfModules.{wD'} (SheafOfModules.Tensor.ringSheaf Y'.O)) ⥤
      DerivedCategory (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf X'.O))}
    {Lf'' : DerivedCategory (SheafOfModules.{wD''} (SheafOfModules.Tensor.ringSheaf Y''.O)) ⥤
      DerivedCategory (SheafOfModules.{wC''} (SheafOfModules.Tensor.ringSheaf X''.O))}
    {Lg : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf X'.O))}
    {Lg' : DerivedCategory (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf X'.O)) ⥤
      DerivedCategory (SheafOfModules.{wC''} (SheafOfModules.Tensor.ringSheaf X''.O))}
    {Lgg : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{wC''} (SheafOfModules.Tensor.ringSheaf X''.O))}
    {Rf : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf Y.O))}
    {Rf' : DerivedCategory (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf X'.O)) ⥤
      DerivedCategory (SheafOfModules.{wD'} (SheafOfModules.Tensor.ringSheaf Y'.O))}
    {Rf'' : DerivedCategory (SheafOfModules.{wC''} (SheafOfModules.Tensor.ringSheaf X''.O)) ⥤
      DerivedCategory (SheafOfModules.{wD''} (SheafOfModules.Tensor.ringSheaf Y''.O))}
    (adj : Lf ⊣ Rf) (adj' : Lf' ⊣ Rf') (adj'' : Lf'' ⊣ Rf'')
    {A₁ B₁ : DerivedCategory (SheafOfModules.{wD'} (SheafOfModules.Tensor.ringSheaf Y'.O)) ⥤
      DerivedCategory (SheafOfModules.{wC''} (SheafOfModules.Tensor.ringSheaf X''.O))}
    {A₂ B₂ : DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf X'.O))}
    {R₀ R₁ R₂ R₃ R₄ R₅ :
      DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{wC''} (SheafOfModules.Tensor.ringSheaf X''.O))}
    (cH : Lh ⋙ Lh' ≅ Lhh) (cG : Lg ⋙ Lg' ≅ Lgg)
    (c₁ : Lh' ⋙ Lf'' ≅ A₁) (T₁ : B₁ ≅ A₁) (d₁ : Lf' ⋙ Lg' ≅ B₁)
    (c₂ : Lh ⋙ Lf' ≅ A₂) (T₂ : B₂ ≅ A₂) (d₂ : Lf ⋙ Lg ≅ B₂)
    (c₀ : Lhh ⋙ Lf'' ≅ R₀) (T₀ : R₅ ≅ R₀) (d₀ : Lf ⋙ Lgg ≅ R₅)
    (e₁ : Lh ⋙ A₁ ≅ R₁) (e₂ : Lh ⋙ B₁ ≅ R₂) (e₃ : A₂ ⋙ Lg' ≅ R₃) (e₄ : B₂ ⋙ Lg' ≅ R₄)
    (a₁ : R₁ ≅ R₀) (w₁ : R₁ ≅ R₂) (a₂ : R₂ ≅ R₃) (w₂ : R₃ ≅ R₄) (a₃ : R₅ ≅ R₄)
    (hA₁ : ∀ N, c₁.hom.app (Lh.obj N) ≫ e₁.hom.app N ≫ a₁.hom.app N =
      Lf''.map (cH.hom.app N) ≫ c₀.hom.app N)
    (hW : ∀ N, e₁.hom.app N ≫ w₁.hom.app N = T₁.inv.app (Lh.obj N) ≫ e₂.hom.app N)
    (hA₂ : ∀ N, d₁.hom.app (Lh.obj N) ≫ e₂.hom.app N ≫ a₂.hom.app N =
      Lg'.map (c₂.hom.app N) ≫ e₃.hom.app N)
    (hL : ∀ N, e₃.hom.app N ≫ w₂.hom.app N = Lg'.map (T₂.inv.app N) ≫ e₄.hom.app N)
    (hA₃ : ∀ N, cG.hom.app (Lf.obj N) ≫ d₀.hom.app N ≫ a₃.hom.app N =
      Lg'.map (d₂.hom.app N) ≫ e₄.hom.app N)
    (hT : ∀ N, T₀.inv.app N =
      a₁.inv.app N ≫ w₁.hom.app N ≫ a₂.hom.app N ≫ w₂.hom.app N ≫ a₃.inv.app N)
    (K : DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf X.O)))
    (bc₂ : Lh.obj (Rf.obj K) ⟶ Rf'.obj (Lg.obj K))
    (bc₁ : Lh'.obj (Rf'.obj (Lg.obj K)) ⟶ Rf''.obj (Lg'.obj (Lg.obj K)))
    (bc₀ : Lhh.obj (Rf.obj K) ⟶ Rf''.obj (Lgg.obj K))
    (hbc₂ : (adj'.homEquiv _ _).symm bc₂ =
      c₂.hom.app (Rf.obj K) ≫ (d₂ ≪≫ T₂).inv.app (Rf.obj K) ≫ Lg.map (adj.counit.app K))
    (hbc₁ : (adj''.homEquiv _ _).symm bc₁ =
      c₁.hom.app (Rf'.obj (Lg.obj K)) ≫ (d₁ ≪≫ T₁).inv.app (Rf'.obj (Lg.obj K)) ≫
        Lg'.map (adj'.counit.app (Lg.obj K)))
    (hbc₀ : (adj''.homEquiv _ _).symm bc₀ =
      c₀.hom.app (Rf.obj K) ≫ (d₀ ≪≫ T₀).inv.app (Rf.obj K) ≫ Lgg.map (adj.counit.app K)) :
    cH.inv.app (Rf.obj K) ≫ Lh'.map bc₂ ≫ bc₁ ≫ Rf''.map (cG.hom.app K) = bc₀ :=
  Stacks.Cohomology.DerivedBaseChangePasting.baseChangeMate_horizontal adj adj' adj'' cG cH
    (fun N => c₂.hom.app N ≫ T₂.inv.app N ≫ d₂.inv.app N) c₁.hom T₁.inv d₁.inv
    (fun N => c₀.hom.app N ≫ T₀.inv.app N ≫ d₀.inv.app N)
    (squareComparison_paste cH cG c₁ T₁ d₁ c₂ T₂ d₂ c₀ T₀ d₀ e₁ e₂ e₃ e₄ a₁ w₁ a₂ w₂ a₃
      hA₁ hW hA₂ hL hA₃ hT)
    K bc₂ bc₁ bc₀
    (by simp [hbc₂])
    (by simp [hbc₁])
    (by simp [hbc₀])

end Paste

section TwoIso

variable {X' : RingedTopos.{vC', uC', wC'}} {Y : RingedTopos.{vD, uD, wD}}
  [X'.J.HasSheafCompose (forget RingCat.{wC'})] [Y.J.HasSheafCompose (forget RingCat.{wD})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{wD})]
  [HasSheafify X'.J AddCommGrpCat.{wC'}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify Y.J AddCommGrpCat.{wD}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{wD}]
  [HasSheafify X'.J (Type wC')] [HasSheafify Y.J (Type wD)]

/-- The inverse of the derived pullback isomorphism of the inverse of a 2-isomorphism is the
derived pullback isomorphism of the 2-isomorphism. -/
theorem derivedPullbackIsoOfTwoIso_symm_inv_app {m₁ m₂ : RingedToposHom X' Y}
    (s : RingedToposHom.TwoIso m₁ m₂) (N :
      DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullbackIsoOfTwoIso s.symm).inv.app N = (derivedPullbackIsoOfTwoIso s).hom.app N := by
  rw [derivedPullbackIsoOfTwoIso_symm]
  rfl

end TwoIso

section Horizontal

variable {X : RingedTopos.{vC, uC, wC}} {X' : RingedTopos.{vC', uC', wC'}}
  {X'' : RingedTopos.{vC'', uC'', wC''}} {Y : RingedTopos.{vD, uD, wD}}
  {Y' : RingedTopos.{vD', uD', wD'}} {Y'' : RingedTopos.{vD'', uD'', wD''}}
  [X.J.HasSheafCompose (forget RingCat.{wC})]
  [X'.J.HasSheafCompose (forget RingCat.{wC'})]
  [X''.J.HasSheafCompose (forget RingCat.{wC''})]
  [Y.J.HasSheafCompose (forget RingCat.{wD})]
  [Y'.J.HasSheafCompose (forget RingCat.{wD'})]
  [Y''.J.HasSheafCompose (forget RingCat.{wD''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{wC} RingCat.{wC})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{wC'} RingCat.{wC'})]
  [X''.J.HasSheafCompose (forget₂ CommRingCat.{wC''} RingCat.{wC''})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{wD} RingCat.{wD})]
  [Y'.J.HasSheafCompose (forget₂ CommRingCat.{wD'} RingCat.{wD'})]
  [Y''.J.HasSheafCompose (forget₂ CommRingCat.{wD''} RingCat.{wD''})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [X''.J.HasSheafCompose (forget AddCommGrpCat.{wC''})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{wD})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{wD'})]
  [Y''.J.HasSheafCompose (forget AddCommGrpCat.{wD''})]
  [HasSheafify X.J AddCommGrpCat.{wC}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify X'.J AddCommGrpCat.{wC'}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify X''.J AddCommGrpCat.{wC''}] [X''.J.WEqualsLocallyBijective AddCommGrpCat.{wC''}]
  [HasSheafify Y.J AddCommGrpCat.{wD}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{wD}]
  [HasSheafify Y'.J AddCommGrpCat.{wD'}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{wD'}]
  [HasSheafify Y''.J AddCommGrpCat.{wD''}] [Y''.J.WEqualsLocallyBijective AddCommGrpCat.{wD''}]
  [HasSheafify X.J (Type wC)] [HasSheafify X'.J (Type wC')] [HasSheafify X''.J (Type wC'')]
  [HasSheafify Y.J (Type wD)] [HasSheafify Y'.J (Type wD')] [HasSheafify Y''.J (Type wD'')]
  [IsGrothendieckAbelian.{wC} (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf X.O))]
  [IsGrothendieckAbelian.{wC'} (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf X'.O))]
  [IsGrothendieckAbelian.{wC''} (SheafOfModules.{wC''} (SheafOfModules.Tensor.ringSheaf X''.O))]

variable (f : RingedToposHom X Y) (f' : RingedToposHom X' Y') (f'' : RingedToposHom X'' Y'')
  (g : RingedToposHom X' X) (g' : RingedToposHom X'' X') (h : RingedToposHom Y' Y)
  (h' : RingedToposHom Y'' Y')

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{wC})]
  [X'.J.HasSheafCompose (forget AddCommGrpCat.{wC'})]
  [Y'.J.HasSheafCompose (forget AddCommGrpCat.{wD'})]
  [Y''.J.HasSheafCompose (forget AddCommGrpCat.{wD''})]
  [HasSheafify X.J AddCommGrpCat.{wC}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{wC}]
  [HasSheafify X'.J AddCommGrpCat.{wC'}] [X'.J.WEqualsLocallyBijective AddCommGrpCat.{wC'}]
  [HasSheafify Y'.J AddCommGrpCat.{wD'}] [Y'.J.WEqualsLocallyBijective AddCommGrpCat.{wD'}]
  [HasSheafify Y''.J AddCommGrpCat.{wD''}] [Y''.J.WEqualsLocallyBijective AddCommGrpCat.{wD''}]
  [HasSheafify X.J (Type wC)] [HasSheafify X'.J (Type wC')]
  [HasSheafify Y'.J (Type wD')] [HasSheafify Y''.J (Type wD'')]
  [IsGrothendieckAbelian.{wC} (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf X.O))]
  [IsGrothendieckAbelian.{wC'} (SheafOfModules.{wC'} (SheafOfModules.Tensor.ringSheaf X'.O))]
  [IsGrothendieckAbelian.{wC''} (SheafOfModules.{wC''} (SheafOfModules.Tensor.ringSheaf X''.O))] in
/-- The derived pullback isomorphism of the pasted 2-isomorphism of a rectangle, read through the
inverse of the rectangle's 2-isomorphism: it is the composite of the derived pullback isomorphisms
of the five pieces the rectangle's 2-isomorphism is pasted from. -/
theorem derivedPullbackIsoOfTwoIso_pasteHorizontal_symm_inv_app
    (s : RingedToposHom.TwoIso (h.comp f') (f.comp g))
    (s' : RingedToposHom.TwoIso (h'.comp f'') (f'.comp g')) (N :
      DerivedCategory (SheafOfModules.{wD} (SheafOfModules.Tensor.ringSheaf Y.O))) :
    (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.pasteHorizontal s s').symm).inv.app N =
      (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator f'' h' h)).inv.app N ≫
        (derivedPullbackIsoOfTwoIso (s'.whiskerRight h)).hom.app N ≫
        (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator g' f' h)).hom.app N ≫
        (derivedPullbackIsoOfTwoIso (s.whiskerLeft g')).hom.app N ≫
        (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator g' g f)).inv.app N := by
  rw [derivedPullbackIsoOfTwoIso_symm_inv_app, RingedToposHom.TwoIso.pasteHorizontal,
    derivedPullbackIsoOfTwoIso_trans, derivedPullbackIsoOfTwoIso_trans,
    derivedPullbackIsoOfTwoIso_trans, derivedPullbackIsoOfTwoIso_trans,
    derivedPullbackIsoOfTwoIso_symm, derivedPullbackIsoOfTwoIso_symm]
  simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]

/-- **Stacks 0E47.**  Consider a commutative diagram of ringed topoi

```
            g'              g
  (Sh(C''), 𝒪) ———→ (Sh(C'), 𝒪) ———→ (Sh(C), 𝒪)
       │ f''              │ f'              │ f
       v                  v                 v
  (Sh(D''), 𝒪) ———→ (Sh(D'), 𝒪) ———→ (Sh(D), 𝒪)
            h'              h
```

in which each square commutes up to the given 2-isomorphism (Stacks 04IC):
`s : h ∘ f' ≅ f ∘ g` and `s' : h' ∘ f'' ≅ f' ∘ g'`, the outer rectangle commuting up to their
pasting `AlgebraicGeometry.RingedToposHom.TwoIso.pasteHorizontal s s'`.  Then the base change
maps of Remark 07A7 for the two squares compose to the base change map of the rectangle: for
`K` in `D(𝒪_C)`, the composite

`L(h ∘ h')^* Rf_* K = L(h')^* Lh^* Rf_* K ⟶ L(h')^* Rf'_* Lg^* K ⟶ Rf''_* L(g')^* Lg^* K
  = Rf''_* L(g ∘ g')^* K`

is the base change map of the rectangle.  The two identifications `=` are the composition
isomorphisms of Stacks 0D6D.

The six morphisms are arbitrary morphisms of ringed topoi in the sense of Stacks 01D3,
part (2), the two 2-isomorphisms are arbitrary, and the eighteen universes of the six ringed topoi
are free.  As for the base change map of Remark 07A7 itself (`derivedBaseChangeMapOfTwoIso`), the
module categories of the three upper ringed topoi carry the instance
`CategoryTheory.IsGrothendieckAbelian` at their section universes, which is what makes the
unbounded `Rf_*` exist at free universes (see the implementation notes of
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/Existence.lean`). -/
@[stacks 0E47]
theorem derivedBaseChangeMapOfTwoIso_horizontal
    (s : RingedToposHom.TwoIso (h.comp f') (f.comp g))
    (s' : RingedToposHom.TwoIso (h'.comp f'') (f'.comp g')) (K :
      DerivedCategory (SheafOfModules.{wC} (SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPullbackCompIso h' h).inv.app ((derivedPushforward f).obj K) ≫
        (derivedPullback h').map (derivedBaseChangeMapOfTwoIso f g f' h s K) ≫
        derivedBaseChangeMapOfTwoIso f' g' f'' h' s' ((derivedPullback g).obj K) ≫
        (derivedPushforward f'').map ((derivedPullbackCompIso g' g).hom.app K) =
      derivedBaseChangeMapOfTwoIso f (g.comp g') f'' (h.comp h')
        (RingedToposHom.TwoIso.pasteHorizontal s s') K :=
  derivedBaseChangeMap_paste_of_iso (derivedAdjunction f) (derivedAdjunction f')
    (derivedAdjunction f'') (derivedPullbackCompIso h' h) (derivedPullbackCompIso g' g)
    (derivedPullbackCompIsoLeft f'' h') (derivedPullbackIsoOfTwoIso s'.symm)
    (derivedPullbackCompIso g' f')
    (derivedPullbackCompIsoLeft f' h) (derivedPullbackIsoOfTwoIso s.symm)
    (derivedPullbackCompIso g f)
    (derivedPullbackCompIsoLeft f'' (h.comp h'))
    (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.pasteHorizontal s s').symm)
    (derivedPullbackCompIso (g.comp g') f)
    (derivedPullbackCompIso (h'.comp f'') h) (derivedPullbackCompIso (f'.comp g') h)
    (derivedPullbackCompIso g' (h.comp f')) (derivedPullbackCompIso g' (f.comp g))
    (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator f'' h' h))
    (derivedPullbackIsoOfTwoIso (s'.whiskerRight h))
    (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator g' f' h))
    (derivedPullbackIsoOfTwoIso (s.whiskerLeft g'))
    (derivedPullbackIsoOfTwoIso (RingedToposHom.TwoIso.associator g' g f))
    (derivedPullbackCompComparison_assoc_associator f'' h' h)
    (fun N => by
      rw [derivedPullbackIsoOfTwoIso_symm_inv_app]
      exact derivedPullbackCompComparison_whiskerRight s' h N)
    (derivedPullbackCompComparison_assoc_associator g' f' h)
    (fun N => by
      rw [derivedPullbackIsoOfTwoIso_symm_inv_app]
      exact derivedPullbackCompComparison_whiskerLeft g' s N)
    (derivedPullbackCompComparison_assoc_associator g' g f)
    (derivedPullbackIsoOfTwoIso_pasteHorizontal_symm_inv_app f f' f'' g g' h h' s s')
    K _ _ _
    (derivedBaseChangeMapOfTwoIso_adjoint f g f' h s K)
    (derivedBaseChangeMapOfTwoIso_adjoint f' g' f'' h' s' ((derivedPullback g).obj K))
    (derivedBaseChangeMapOfTwoIso_adjoint f (g.comp g') f'' (h.comp h')
      (RingedToposHom.TwoIso.pasteHorizontal s s') K)

end Horizontal

end

end Stacks.Cohomology.DerivedBaseChangeOfToposHom

end
