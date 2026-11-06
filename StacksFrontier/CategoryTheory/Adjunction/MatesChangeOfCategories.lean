module

public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Basic

/-!
# Transporting a mate along a change of the four categories

Mates do not transport for free.  For a square of adjunctions `L₁ ⊣ R₁`, `L₂ ⊣ R₂` and a 2-cell
`β` between composites of the right adjoints, the invertibility of `β` and the invertibility of
its mate `(CategoryTheory.mateEquiv adj₁ adj₂).symm β` are genuinely different conditions: that
is the Beck–Chevalley phenomenon, and in the étale setting it is the content of a base change
theorem rather than a formality.  What does transport is a mate along a change of the four
*categories* of the square.

The data is a cube.  Its front face is
```
      L₁
   C ----→ D
 G |       | H
   v       v
   E ----→ F
      L₂
```
with `L₁ ⊣ R₁` and `L₂ ⊣ R₂`; its back face is the same picture with primes, carrying `L₁' ⊣ R₁'`
and `L₂' ⊣ R₂'`; and four functors `ΦC`, `ΦD`, `ΦE`, `ΦF` run from the front corners to the back
corners.  The two side faces through `L₁` and `L₂` carry 2-cells
`τ₁ : ΦC ⋙ L₁' ⟶ L₁ ⋙ ΦD` and `τ₂ : ΦE ⋙ L₂' ⟶ L₂ ⋙ ΦF`, and the two side faces through `G`
and `H` carry 2-cells `σG : G ⋙ ΦE ⟶ ΦC ⋙ G'` and `σH : ΦD ⋙ H' ⟶ H ⋙ ΦF`.

Given 2-cells `β : R₁ ⋙ G ⟶ H ⋙ R₂` on the front and `β' : R₁' ⋙ G' ⟶ H' ⋙ R₂'` on the back,
there are two ways to paste a 2-cell `R₁ ⋙ G ⋙ ΦE ⟶ H ⋙ ΦF ⋙ R₂'` out of this data: through
`β` and the mate of `τ₂`, or through the mate of `τ₁` and `β'`, corrected by `σG` and `σH`.  The
hypothesis of the main result is that the two agree, and its conclusion is the corresponding
agreement for the mates of `β` and `β'`.  Since every comparison in sight is an isomorphism in
the intended applications, the upshot is a transfer of invertibility: if the mate of `β'` is
invertible, so is the mate of `β`.

The transfer is stated with `ΦF` only required to **reflect** isomorphisms, not to be an
equivalence.  The application that forces this is the passage from sheaves of sets to sheaves of
abelian groups, where the functor relating the two squares is composition with the forgetful
functor: it is not an equivalence, but a morphism of abelian sheaves whose underlying morphism of
sheaves of sets is invertible is itself invertible.

## Main results

* `Stacks.CategoryTheory.mateEquiv_symm_hComp_eq` — **the cube identity.**  If `β` and `β'`
  correspond under the four comparisons, then their mates correspond.
* `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms` — the invertibility
  transfer read off from it, with `ΦF` only reflecting isomorphisms.
* `Stacks.CategoryTheory.mateEquiv_symm_eq_whiskerLeft_whiskerRight` and
  `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_isIso_mateEquiv_symm` — **a mate does not depend
  on which left adjoints the two adjunctions use.**  Changing the two left adjoints, with the two
  right adjoints fixed, whiskers the mate by the canonical comparisons of left adjoints, so its
  invertibility is unaffected.  This is not an instance of the cube transfer above: there the
  four categories change and the 2-cell is carried along, whereas here the categories and the
  2-cell are fixed and only the adjunctions move.

## Implementation notes

The proof of the cube identity is the calculus of mates and nothing else.  Applying
`CategoryTheory.mateEquiv` for the adjunctions `L₁ ⊣ R₁` and `L₂' ⊣ R₂'` to both sides turns
each into a vertical pasting of 2-cells between right adjoints, by Mathlib's
`CategoryTheory.mateEquiv_vcomp`, which says that the mate of a horizontal pasting is the
vertical pasting of the mates; the two correcting whiskerings pass through the mate operation by
the private lemma `mateEquiv_whiskerTop_whiskerBottom` below.  What is left is exactly the
hypothesis, and `CategoryTheory.mateEquiv` is injective, being an equivalence of types.

**The directions of the four comparisons** are not uniform: `τ₁`, `τ₂` and `σH` point from the
composite through the back face to the composite through the front face, while `σG` points the
other way.  This is forced, not chosen: a 2-square `CategoryTheory.TwoSquare T L R B` is a
transformation `T ⋙ R ⟶ L ⋙ B`, and these are the only directions in which the six faces paste
into the two 2-cells being compared.  In the applications all four are isomorphisms, so the
asymmetry costs nothing.

**Why the whiskering lemma is proved here.** Mathlib's
`CategoryTheory.mateEquiv_conjugateEquiv_vcomp` and
`CategoryTheory.conjugateEquiv_mateEquiv_vcomp` whisker a 2-square by transformations of the two
*horizontal* functors `L₁` and `L₂`, which is a different operation: the mate then picks up the
conjugates of those transformations.  Whiskering by transformations of the two *vertical*
functors `G` and `H` passes through the mate operation with no conjugation at all, because `G`
and `H` are untouched by the construction, and that is the form needed here.

## References

* [nLab, *mate*](https://ncatlab.org/nlab/show/mate)
* [Stacks Project, Tag 0959](https://stacks.math.columbia.edu/tag/0959)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.TwoSquare

universe v₁ v₂ v₃ v₄ v₅ v₆ v₇ v₈ u₁ u₂ u₃ u₄ u₅ u₆ u₇ u₈

namespace Stacks.CategoryTheory

section Pasting

variable {C₁ C₂ C₃ C₄ C₅ C₆ : Type*} [Category* C₁] [Category* C₂] [Category* C₃]
  [Category* C₄] [Category* C₅] [Category* C₆]

/-- The component of a horizontal pasting of 2-squares at an object. -/
private theorem hComp_natTrans_app {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆}
    (w : TwoSquare T L R B) (w' : TwoSquare T' R R' B') (c : C₁) :
    (w ≫ₕ w').natTrans.app c = w'.natTrans.app (T.obj c) ≫ B'.map (w.natTrans.app c) := by
  simp [TwoSquare.hComp]

/-- A horizontal pasting of two invertible 2-squares is invertible. -/
private theorem isIso_hComp_natTrans {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄}
    {T' : C₂ ⥤ C₅} {R' : C₅ ⥤ C₆} {B' : C₄ ⥤ C₆}
    (w : TwoSquare T L R B) (w' : TwoSquare T' R R' B')
    [IsIso w.natTrans] [IsIso w'.natTrans] : IsIso (w ≫ₕ w').natTrans := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro c
  rw [hComp_natTrans_app]
  infer_instance

/-- Whiskering an invertible 2-square by invertible transformations of its top and bottom gives
an invertible 2-square. -/
private theorem isIso_whiskerTop_whiskerBottom_natTrans {T T' : C₁ ⥤ C₂} {L : C₁ ⥤ C₃}
    {R : C₂ ⥤ C₄} {B B' : C₃ ⥤ C₄} (w : TwoSquare T' L R B) (φ : T ⟶ T') (ψ : B ⟶ B')
    [IsIso w.natTrans] [IsIso φ] [IsIso ψ] :
    IsIso ((w.whiskerTop φ).whiskerBottom ψ).natTrans := by
  show IsIso ((Functor.whiskerRight φ R ≫ w.natTrans) ≫ Functor.whiskerLeft L ψ)
  infer_instance

end Pasting

section Whisker

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}

/-- Taking mates commutes with whiskering the two vertical functors of a 2-square: the vertical
functors are the ones the mate construction leaves alone, so no conjugate appears, and
whiskering the top and bottom of the square becomes whiskering the right and left of its
mate. -/
private theorem mateEquiv_whiskerTop_whiskerBottom (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂)
    {G G' : C ⥤ E} {H H' : D ⥤ F} (α : TwoSquare G L₁ L₂ H) (φ : G' ⟶ G) (ψ : H ⟶ H') :
    mateEquiv adj₁ adj₂ ((α.whiskerTop φ).whiskerBottom ψ) =
      ((mateEquiv adj₁ adj₂ α).whiskerRight φ).whiskerLeft ψ := by
  refine TwoSquare.ext _ _ fun d => ?_
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, mateEquiv]

end Whisker

section Cube

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  {C' : Type u₅} {D' : Type u₆} {E' : Type u₇} {F' : Type u₈}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  [Category.{v₅} C'] [Category.{v₆} D'] [Category.{v₇} E'] [Category.{v₈} F']
  {L₁ : C ⥤ D} {R₁ : D ⥤ C} {L₂ : E ⥤ F} {R₂ : F ⥤ E}
  {L₁' : C' ⥤ D'} {R₁' : D' ⥤ C'} {L₂' : E' ⥤ F'} {R₂' : F' ⥤ E'}
  {G : C ⥤ E} {H : D ⥤ F} {G' : C' ⥤ E'} {H' : D' ⥤ F'}
  {ΦC : C ⥤ C'} {ΦD : D ⥤ D'} {ΦE : E ⥤ E'} {ΦF : F ⥤ F'}
  (adj₁ : L₁ ⊣ R₁) (adj₂ : L₂ ⊣ R₂) (adj₁' : L₁' ⊣ R₁') (adj₂' : L₂' ⊣ R₂')
  (τ₁ : TwoSquare ΦC L₁ L₁' ΦD) (τ₂ : TwoSquare ΦE L₂ L₂' ΦF)
  (σG : G ⋙ ΦE ⟶ ΦC ⋙ G') (σH : ΦD ⋙ H' ⟶ H ⋙ ΦF)
  (β : TwoSquare R₁ H G R₂) (β' : TwoSquare R₁' H' G' R₂')

/-- **A mate transports along a change of the four categories of its square.**

For two squares of adjunctions joined by functors `ΦC`, `ΦD`, `ΦE`, `ΦF` at the four corners,
with comparisons `τ₁`, `τ₂` of the two horizontal left adjoints and `σG`, `σH` of the two
vertical functors, the hypothesis says that the 2-cells `β` and `β'` between the composites of
right adjoints paste to the same 2-cell `R₁ ⋙ G ⋙ ΦE ⟶ H ⋙ ΦF ⋙ R₂'`; the conclusion says
that their mates then paste to the same 2-cell `G ⋙ ΦE ⋙ L₂' ⟶ L₁ ⋙ H ⋙ ΦF`.

This is the transport that the invertibility of a Beck–Chevalley 2-cell does *not* enjoy under a
change of the 2-cell, but does enjoy under a change of the ambient categories: it is how an
identification of a direct image with its base change, proved for one presentation of a site and
one coefficient category, is moved to another. -/
public theorem mateEquiv_symm_hComp_eq
    (h : ((mateEquiv adj₁ adj₁' τ₁ ≫ᵥ β').whiskerRight σG).whiskerLeft σH =
      β ≫ᵥ mateEquiv adj₂ adj₂' τ₂) :
    (mateEquiv adj₁ adj₂).symm β ≫ₕ τ₂ =
      ((τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β').whiskerTop σG).whiskerBottom σH := by
  refine (mateEquiv adj₁ adj₂').injective ?_
  rw [mateEquiv_vcomp adj₁ adj₂ adj₂', Equiv.apply_symm_apply,
    mateEquiv_whiskerTop_whiskerBottom, mateEquiv_vcomp adj₁ adj₁' adj₂',
    Equiv.apply_symm_apply, h]

/-- **Invertibility of a mate transports along a change of the four categories of its square.**

In the situation of `Stacks.CategoryTheory.mateEquiv_symm_hComp_eq`, if all four comparisons are
invertible and the mate of `β'` is invertible, then so is the mate of `β`, provided only that the
functor `ΦF` at the lower right corner reflects isomorphisms.  It is not required to be an
equivalence, nor are the other three `Φ` required to be anything at all. -/
public theorem isIso_mateEquiv_symm_of_reflectsIsomorphisms [ΦF.ReflectsIsomorphisms]
    [IsIso τ₁.natTrans] [IsIso τ₂.natTrans] [IsIso σG] [IsIso σH]
    [IsIso ((mateEquiv adj₁' adj₂').symm β').natTrans]
    (h : ((mateEquiv adj₁ adj₁' τ₁ ≫ᵥ β').whiskerRight σG).whiskerLeft σH =
      β ≫ᵥ mateEquiv adj₂ adj₂' τ₂) :
    IsIso ((mateEquiv adj₁ adj₂).symm β).natTrans := by
  have : IsIso (τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β').natTrans :=
    isIso_hComp_natTrans _ _
  have hr := isIso_whiskerTop_whiskerBottom_natTrans
    (τ₁ ≫ₕ (mateEquiv adj₁' adj₂').symm β') σG σH
  rw [← mateEquiv_symm_hComp_eq adj₁ adj₂ adj₁' adj₂' τ₁ τ₂ σG σH β β' h] at hr
  rw [NatTrans.isIso_iff_isIso_app]
  intro c
  have := hr
  have hcomp : IsIso (((mateEquiv adj₁ adj₂).symm β ≫ₕ τ₂).natTrans.app c) := inferInstance
  rw [hComp_natTrans_app] at hcomp
  have : IsIso (ΦF.map (((mateEquiv adj₁ adj₂).symm β).natTrans.app c)) :=
    IsIso.of_isIso_comp_left (τ₂.natTrans.app (G.obj c)) _
  exact isIso_of_reflects_iso _ ΦF

end Cube

section LeftAdjointChoice

variable {C : Type u₁} {D : Type u₂} {E : Type u₃} {F : Type u₄}
  [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] [Category.{v₄} F]
  {L L' : C ⥤ D} {R₁ : D ⥤ C} {M M' : E ⥤ F} {R₂ : F ⥤ E} {G : C ⥤ E} {H : D ⥤ F}
  (adjL : L ⊣ R₁) (adjL' : L' ⊣ R₁) (adjM : M ⊣ R₂) (adjM' : M' ⊣ R₂)
  (β : TwoSquare R₁ H G R₂)

/-- **Changing the two left adjoints whiskers the mate by the canonical comparisons of left
adjoints.**  A left adjoint of a functor is determined only up to isomorphism, and two
developments can perfectly well arrive at the same right adjoint through different left ones —
an abstract `CategoryTheory.Functor.sheafPullback` on one side and a left Kan extension followed
by sheafification on the other.  The mate of a 2-cell `β` between composites of the right
adjoints is then formed twice, and the two results differ by whiskering with
`CategoryTheory.conjugateEquiv` of the identity of the right adjoint, which is the canonical
comparison of the two left adjoints.

The proof is Mathlib's two half-naturalities of the mates equivalence in the left adjoints,
`CategoryTheory.mateEquiv_conjugateEquiv_vcomp` for the right-hand adjunction and
`CategoryTheory.conjugateEquiv_mateEquiv_vcomp` for the left-hand one, each applied with the
comparison whose conjugate is an identity. -/
public theorem mateEquiv_symm_eq_whiskerLeft_whiskerRight :
    (mateEquiv adjL' adjM').symm β =
      (((mateEquiv adjL adjM).symm β).whiskerRight
          ((conjugateEquiv adjM adjM').symm (𝟙 R₂))).whiskerLeft
        ((conjugateEquiv adjL' adjL).symm (𝟙 R₁)) := by
  have h1 : mateEquiv adjL adjM'
      (((mateEquiv adjL adjM).symm β).whiskerRight
        ((conjugateEquiv adjM adjM').symm (𝟙 R₂))) = β.whiskerBottom (𝟙 R₂) := by
    rw [mateEquiv_conjugateEquiv_vcomp adjL adjM adjM' ((mateEquiv adjL adjM).symm β)
      ((conjugateEquiv adjM adjM').symm (𝟙 R₂)), Equiv.apply_symm_apply,
      Equiv.apply_symm_apply]
  refine (Equiv.symm_apply_eq _).2 ?_
  rw [conjugateEquiv_mateEquiv_vcomp adjL' adjL adjM'
    ((conjugateEquiv adjL' adjL).symm (𝟙 R₁))
    (((mateEquiv adjL adjM).symm β).whiskerRight
      ((conjugateEquiv adjM adjM').symm (𝟙 R₂))), h1, Equiv.apply_symm_apply]
  refine (TwoSquare.ext _ _ fun d => ?_).symm
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom]

/-- **Invertibility of a mate does not depend on which left adjoints the two adjunctions use.**
The two mates differ by whiskering with the canonical comparisons of the left adjoints,
`mateEquiv_symm_eq_whiskerLeft_whiskerRight`, and those are isomorphisms because the identity of
a right adjoint is one. -/
public theorem isIso_mateEquiv_symm_of_isIso_mateEquiv_symm
    (hβ : IsIso ((mateEquiv adjL adjM).symm β).natTrans) :
    IsIso ((mateEquiv adjL' adjM').symm β).natTrans := by
  have := hβ
  rw [mateEquiv_symm_eq_whiskerLeft_whiskerRight adjL adjL' adjM adjM' β]
  show IsIso ((Functor.whiskerLeft G ((conjugateEquiv adjM adjM').symm (𝟙 R₂)) ≫
    ((mateEquiv adjL adjM).symm β).natTrans) ≫
      Functor.whiskerRight ((conjugateEquiv adjL' adjL).symm (𝟙 R₁)) H)
  infer_instance

end LeftAdjointChoice

end Stacks.CategoryTheory

end
