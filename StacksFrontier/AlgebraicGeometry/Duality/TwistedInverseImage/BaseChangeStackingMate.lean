module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.BaseChangeStacking
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeComposition
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangePastingOnRingedTopoi
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.CompositionExtra

/-!
# Base change for the twisted inverse image along a vertical stack of two squares

Let

```
X' --k--> X
|f'       |f
Y' --l--> Y
|g'       |g
Z' --m--> Z
```

be two cartesian squares of schemes stacked vertically. [Stacks, Tag 0ATQ] (Lemma 48.5.1) says
that, for quasi-compact quasi-separated schemes and with `f`, `l` and `g`, `m` Tor-independent,
the base change maps of [Stacks, Tag 0AA6] for the two squares compose to the base change map for
the outer rectangle. That is what is proved here.

## Main results

All in the namespace `Stacks.Duality`.

* `twistedInverseImagePushforwardBaseChange_vcomp` — the identity `ξ_rect = ξ_bot ≫ₕ ξ_top` for
  the transformation `ξ` of [Stacks, Tag 0A9K], read through the comparison of
  [Stacks, Tag 0ATX] for each composite vertical. This is where the source's proof ends.
* `isIso_twistedInverseImagePushforwardBaseChange_vcomp` — `ξ` for the rectangle is invertible as
  soon as it is for the two squares, so the rectangle's base change map needs no third input.
* `twistedInverseImageBaseChangeMap_vcomp` — **[Stacks, Tag 0ATQ]**.

## Route

Both steps are the mates calculus. `ξ` is by construction the mate of the comparison of derived
direct image around the square (`Stacks.Duality.twistedInverseImagePushforwardBaseChange`), so the
first identity is the compatibility of `CategoryTheory.mateEquiv` with pasting —
`Stacks.Cohomology.DerivedBaseChangePasting.mate_twoSquare_paste` — applied to the vertical
stacking of those comparisons, `Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso_vcomp`.
Pasting delivers the mate under the *composite* adjunction of
`Stacks.Duality.twistedInverseImageCompAdjunction`, whose right adjoint is `g^× ⋙ f^×`, and the
trade for the adjunction of `f ≫ g`, whose right adjoint is `(f ≫ g)^×`, is the conjugate
computation `Stacks.Duality.twistedInverseImageCompIso_hom_eq` of [Stacks, Tag 0ATX] in its two
directions.

The base change map is the mate of `ξ⁻¹` by
`Stacks.Duality.twistedInverseImageBaseChangeMap_eq_mateEquiv_symm`, and a horizontal composite of
2-squares of left adjoints inverts to the vertical composite of the inverses, so the second step is
`CategoryTheory.mateEquiv_vcomp` together with `Stacks.CategoryTheory.mateEquiv_whisker` for the
two legs the correspondence carries over unchanged.

## Implementation notes

*Term mode.* The functors here are derived functors on quasi-coherent derived categories, and the
two spellings of the rectangle's threefold composite are identified only at default transparency;
`rw` on the assembled goal leaves it ill-typed at reducible transparency and fails. The final
assembly is therefore a term, built from `Eq.trans` and `congrArg`, and every rearrangement is
hoisted into a lemma whose data are variables.

*What the `@[stacks 0ATQ]` attribute claims.* The quasi-coherence and adjointness inputs are the
ones [Stacks, Tag 08D5] part (1) and [Stacks, Tag 0A9E] produce for a quasi-compact
quasi-separated morphism, as everywhere in this directory;
`Stacks.Duality.twistedInverseImageCompIsoOfQcqs` is the pattern that discharges them from
quasi-compactness and quasi-separatedness alone. Invertibility of `ξ` for each of the two squares
is an instance argument, as it already is in `Stacks.Duality.twistedInverseImageBaseChangeMap`,
where the base change map of [Stacks, Tag 0AA6] is defined and where it is what makes `ξ⁻¹` exist;
[Stacks, Tag 0A9K] is the statement that produces it from Tor-independence, and it is not proved
in this repository. The rectangle needs no third such input, by
`isIso_twistedInverseImagePushforwardBaseChange_vcomp`. The statement is about the right adjoint
`f^×` of [Stacks, Tag 0A9E], not about the `f^!` of a general compactification.

## References

* [Stacks Project, Tag 0ATQ](https://stacks.math.columbia.edu/tag/0ATQ)
* [Stacks Project, Tag 0AA6](https://stacks.math.columbia.edu/tag/0AA6)
* [Stacks Project, Tag 0A9K](https://stacks.math.columbia.edu/tag/0A9K)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.ObjectProperty
open Stacks.Cohomology.DerivedBaseChangePasting (mate_twoSquare_paste)
open Stacks.CategoryTheory (mateEquiv_whisker)
open scoped CategoryTheory.TwoSquare

universe u

namespace Stacks.Duality

/-! ### Bookkeeping, with variable data -/

section Generic

universe v₁ v₂ v₃ v₄ v₅ v₆ u₁ u₂ u₃ u₄ u₅ u₆

variable {A : Type u₁} {B : Type u₂} {C : Type u₃} {D : Type u₄} {E : Type u₅} {F : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C] [Category.{v₄} D] [Category.{v₅} E]
  [Category.{v₆} F]

/-- A 2-square is the whiskered vertical composite of two 2-squares as soon as the underlying
isomorphisms compose that way. Stated with variable data, so that the application site pays no
unfolding of a derived functor. -/
private theorem twoSquare_vcomp_of_iso
    {Tl : A ⥤ B} {Ll : A ⥤ C} {Rl : B ⥤ D} {Tu : C ⥤ D} {Lu : C ⥤ E} {Ru : D ⥤ F}
    {Bu : E ⥤ F} {Lo : A ⥤ E} {Ro : B ⥤ F}
    (So : Tl ⋙ Ro ≅ Lo ⋙ Bu) (Sl : Tl ⋙ Rl ≅ Ll ⋙ Tu) (Su : Tu ⋙ Ru ≅ Lu ⋙ Bu)
    (cL : Ll ⋙ Lu ≅ Lo) (cR : Rl ⋙ Ru ≅ Ro)
    (h : So = isoWhiskerLeft Tl cR.symm ≪≫ (associator Tl Rl Ru).symm ≪≫
      isoWhiskerRight Sl Ru ≪≫ associator Ll Tu Ru ≪≫ isoWhiskerLeft Ll Su ≪≫
      (associator Ll Lu Bu).symm ≪≫ isoWhiskerRight cL Bu) :
    TwoSquare.mk Tl Lo Ro Bu So.hom =
      ((TwoSquare.mk Tl Ll Rl Tu Sl.hom ≫ᵥ
        TwoSquare.mk Tu Lu Ru Bu Su.hom).whiskerLeft cL.hom).whiskerRight cR.inv := by
  subst h
  refine TwoSquare.ext _ _ fun Xa => ?_
  simp [TwoSquare.vComp, TwoSquare.whiskerLeft, TwoSquare.whiskerRight]

variable {T : A ⥤ B} {Lb : A ⥤ C} {R : B ⥤ D} {Bm : C ⥤ D} {T' : B ⥤ E} {R' : E ⥤ F}
  {B' : D ⥤ F} {To : A ⥤ E} {Bo : C ⥤ F}

/-- **The inverse of a horizontal composite of two invertible 2-squares, whiskered at the top and
at the bottom by isomorphisms, is the vertical composite of the inverses**, whiskered at the right
and at the left. In the bodies of `CategoryTheory.TwoSquare.hComp` and
`CategoryTheory.TwoSquare.vComp` the two composites are the same chain of associators and
whiskerings read in opposite order, so the identity is componentwise immediate. First half. -/
private theorem hComp_whiskered_hom_inv_id (w : TwoSquare T Lb R Bm) (w' : TwoSquare T' R R' B')
    (dL : To ≅ T ⋙ T') (dR : Bm ⋙ B' ≅ Bo) [IsIso w.natTrans] [IsIso w'.natTrans] :
    (((w ≫ₕ w').whiskerTop dL.hom).whiskerBottom dR.hom).natTrans ≫
        ((TwoSquare.mk Lb T Bm R (inv w.natTrans) ≫ᵥ
          TwoSquare.mk R T' B' R' (inv w'.natTrans)).whiskerRight dR.inv).whiskerLeft
            dL.inv = 𝟙 _ := by
  refine NatTrans.ext (funext fun Xa => ?_)
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.hComp, TwoSquare.vComp]

/-- The second half of `Stacks.Duality.hComp_whiskered_hom_inv_id`. -/
private theorem hComp_whiskered_inv_hom_id (w : TwoSquare T Lb R Bm) (w' : TwoSquare T' R R' B')
    (dL : To ≅ T ⋙ T') (dR : Bm ⋙ B' ≅ Bo) [IsIso w.natTrans] [IsIso w'.natTrans] :
    ((TwoSquare.mk Lb T Bm R (inv w.natTrans) ≫ᵥ
          TwoSquare.mk R T' B' R' (inv w'.natTrans)).whiskerRight dR.inv).whiskerLeft
            dL.inv ≫ (((w ≫ₕ w').whiskerTop dL.hom).whiskerBottom dR.hom).natTrans = 𝟙 _ := by
  refine NatTrans.ext (funext fun Xa => ?_)
  simp [TwoSquare.whiskerTop, TwoSquare.whiskerBottom, TwoSquare.whiskerLeft,
    TwoSquare.whiskerRight, TwoSquare.hComp, TwoSquare.vComp]

end Generic

/-! ### The compositor and the comparison of Tag 0ATX -/

section Conjugate

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
  (hpushfg : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward (f ≫ g)).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward g hpushg).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (f ≫ g) hpushfg).IsLeftAdjoint]

/-- **The conjugate of the inverse compositor of derived direct image is the inverse comparison
of [Stacks, Tag 0ATX].** `Stacks.Duality.twistedInverseImageCompIso_hom_eq` is the same statement
for the compositor itself; the two directions are exchanged by
`CategoryTheory.conjugateEquiv_comm`, which is what the mates calculus needs for the leg of a
2-square that the correspondence carries over rather than trades. -/
private theorem conjugateEquiv_quasiCoherentDerivedPushforwardCompIso_inv :
    conjugateEquiv ((twistedInverseImageAdjunction f hpushf).comp
          (twistedInverseImageAdjunction g hpushg))
        (twistedInverseImageAdjunction (f ≫ g) hpushfg)
        (quasiCoherentDerivedPushforwardCompIso f g hpushf hpushg hpushfg).inv =
      (twistedInverseImageCompIso f g hpushf hpushg hpushfg).inv := by
  refine (Iso.hom_comp_eq_id (twistedInverseImageCompIso f g hpushf hpushg hpushfg)).1 ?_
  rw [twistedInverseImageCompIso_hom_eq]
  exact conjugateEquiv_comm _ _ (Iso.inv_hom_id _)

end Conjugate

/-! ### The transformation of Tag 0A9K -/

section Xi

variable {X' X Y' Y Z' Z : Scheme.{u}} (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y)
  (g' : Y' ⟶ Z') (g : Y ⟶ Z) (m : Z' ⟶ Z)
  (hpushk : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward k).obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y'.Modules i).obj
      ((derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushl : ∀ (K : quasiCoherentDerivedCategory Y') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward l).obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
  (hpushg' : ∀ (K : quasiCoherentDerivedCategory Y') (i : ℤ),
    ((DerivedCategory.homologyFunctor Z'.Modules i).obj
      ((derivedPushforward g').obj K.obj)).IsQuasicoherent)
  (hpushm : ∀ (K : quasiCoherentDerivedCategory Z') (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward m).obj K.obj)).IsQuasicoherent)
  (hpushfg : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward (f ≫ g)).obj K.obj)).IsQuasicoherent)
  (hpushf'g' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor Z'.Modules i).obj
      ((derivedPushforward (f' ≫ g')).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward g hpushg).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward g' hpushg').IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (f ≫ g) hpushfg).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (f' ≫ g') hpushf'g').IsLeftAdjoint]

/-- **The transformation `ξ` of [Stacks, Tag 0A9K] for a vertical stack of two cartesian squares
is the horizontal composite of the transformations of the two squares**, the twisted inverse
images along the two composite verticals being read through the comparison of
[Stacks, Tag 0ATX]. This is the identity the source's proof of its Lemma 48.5.1 reduces to,
"it suffices to prove that ... is equal to `ξ_rect`".

`ξ` is the mate of the comparison of derived direct image around the square, so this is the
compatibility of `CategoryTheory.mateEquiv` with pasting applied to
`Stacks.Duality.quasiCoherentDerivedPushforwardSquareIso_vcomp`, with the adjunction of each
composite vertical traded for the composite of the two adjunctions. -/
theorem twistedInverseImagePushforwardBaseChange_vcomp (sq₁ : IsPullback k f' f l)
    (sq₂ : IsPullback l g' g m) :
    twistedInverseImagePushforwardBaseChange k (f' ≫ g') (f ≫ g) m hpushk hpushfg hpushf'g'
        hpushm (sq₁.paste_vert sq₂) =
      ((TwoSquare.mk _ _ _ _ (twistedInverseImagePushforwardBaseChange l g' g m hpushl hpushg
              hpushg' hpushm sq₂) ≫ₕ
          TwoSquare.mk _ _ _ _ (twistedInverseImagePushforwardBaseChange k f' f l hpushk hpushf
            hpushf' hpushl sq₁)).whiskerTop
        (twistedInverseImageCompIso f' g' hpushf' hpushg' hpushf'g').hom).whiskerBottom
        (twistedInverseImageCompIso f g hpushf hpushg hpushfg).inv :=
  mate_twoSquare_paste (twistedInverseImageAdjunction f' hpushf')
    (twistedInverseImageAdjunction f hpushf) (twistedInverseImageAdjunction g' hpushg')
    (twistedInverseImageAdjunction g hpushg)
    (twistedInverseImageAdjunction (f' ≫ g') hpushf'g')
    (twistedInverseImageAdjunction (f ≫ g) hpushfg) _ _ _ _ _ _ _
    (twoSquare_vcomp_of_iso _ _ _ _ _
      (quasiCoherentDerivedPushforwardSquareIso_vcomp k f' f l g' g m hpushk hpushf hpushf'
        hpushl hpushg hpushg' hpushm hpushfg hpushf'g' (sq₁.paste_vert sq₂).w sq₁.w sq₂.w))
    (twistedInverseImageCompIso_hom_eq f' g' hpushf' hpushg' hpushf'g').symm
    (conjugateEquiv_quasiCoherentDerivedPushforwardCompIso_inv f g hpushf hpushg hpushfg)

/-- **The transformation `ξ` for the outer rectangle is invertible as soon as it is invertible for
the two squares**, which is what makes the base change map of [Stacks, Tag 0AA6] for the rectangle
available from the two Tor-independences of [Stacks, Tag 0ATQ] and no further input. By
`Stacks.Duality.twistedInverseImagePushforwardBaseChange_vcomp` it is a horizontal composite of
the two, whiskered by the two comparisons of [Stacks, Tag 0ATX]. -/
theorem isIso_twistedInverseImagePushforwardBaseChange_vcomp (sq₁ : IsPullback k f' f l)
    (sq₂ : IsPullback l g' g m)
    [IsIso (twistedInverseImagePushforwardBaseChange k f' f l hpushk hpushf hpushf' hpushl sq₁)]
    [IsIso (twistedInverseImagePushforwardBaseChange l g' g m hpushl hpushg hpushg' hpushm sq₂)] :
    IsIso (twistedInverseImagePushforwardBaseChange k (f' ≫ g') (f ≫ g) m hpushk hpushfg
      hpushf'g' hpushm (sq₁.paste_vert sq₂)) := by
  rw [twistedInverseImagePushforwardBaseChange_vcomp k f' f l g' g m hpushk hpushf hpushf'
    hpushl hpushg hpushg' hpushm hpushfg hpushf'g' sq₁ sq₂]
  exact ⟨_, hComp_whiskered_hom_inv_id _ _ (twistedInverseImageCompIso f' g' hpushf' hpushg'
      hpushf'g') (twistedInverseImageCompIso f g hpushf hpushg hpushfg).symm,
    hComp_whiskered_inv_hom_id _ _ (twistedInverseImageCompIso f' g' hpushf' hpushg' hpushf'g')
      (twistedInverseImageCompIso f g hpushf hpushg hpushfg).symm⟩

end Xi

/-! ### The base change map of Tag 0AA6 -/

section Gamma

variable {X' X Y' Y Z' Z : Scheme.{u}} (k : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (l : Y' ⟶ Y)
  (g' : Y' ⟶ Z') (g : Y ⟶ Z) (m : Z' ⟶ Z)
  (hpushk : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor X.Modules i).obj
      ((derivedPushforward k).obj K.obj)).IsQuasicoherent)
  (hpushf : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward f).obj K.obj)).IsQuasicoherent)
  (hpushf' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y'.Modules i).obj
      ((derivedPushforward f').obj K.obj)).IsQuasicoherent)
  (hpushl : ∀ (K : quasiCoherentDerivedCategory Y') (i : ℤ),
    ((DerivedCategory.homologyFunctor Y.Modules i).obj
      ((derivedPushforward l).obj K.obj)).IsQuasicoherent)
  (hpushg : ∀ (K : quasiCoherentDerivedCategory Y) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward g).obj K.obj)).IsQuasicoherent)
  (hpushg' : ∀ (K : quasiCoherentDerivedCategory Y') (i : ℤ),
    ((DerivedCategory.homologyFunctor Z'.Modules i).obj
      ((derivedPushforward g').obj K.obj)).IsQuasicoherent)
  (hpushm : ∀ (K : quasiCoherentDerivedCategory Z') (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward m).obj K.obj)).IsQuasicoherent)
  (hpushfg : ∀ (K : quasiCoherentDerivedCategory X) (i : ℤ),
    ((DerivedCategory.homologyFunctor Z.Modules i).obj
      ((derivedPushforward (f ≫ g)).obj K.obj)).IsQuasicoherent)
  (hpushf'g' : ∀ (K : quasiCoherentDerivedCategory X') (i : ℤ),
    ((DerivedCategory.homologyFunctor Z'.Modules i).obj
      ((derivedPushforward (f' ≫ g')).obj K.obj)).IsQuasicoherent)
  [(quasiCoherentDerivedPushforward f hpushf).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward f' hpushf').IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward g hpushg).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward g' hpushg').IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (f ≫ g) hpushfg).IsLeftAdjoint]
  [(quasiCoherentDerivedPushforward (f' ≫ g') hpushf'g').IsLeftAdjoint]

/-- The mate of the base change map of a square under the derived adjunctions of its horizontal
edges is the inverse of the transformation `ξ`. -/
private theorem mateEquiv_twistedInverseImageBaseChangeMap (sq : IsPullback k f' f l)
    [IsIso (twistedInverseImagePushforwardBaseChange k f' f l hpushk hpushf hpushf' hpushl sq)] :
    mateEquiv
        (quasiCoherentDerivedAdjunction l (isQuasicoherent_homology_derivedPullback' l) hpushl)
        (quasiCoherentDerivedAdjunction k (isQuasicoherent_homology_derivedPullback' k) hpushk)
        (TwoSquare.mk _ _ _ _ (twistedInverseImageBaseChangeMap k f' f l hpushk hpushf hpushf'
          hpushl sq)) =
      TwoSquare.mk _ _ _ _ (inv (twistedInverseImagePushforwardBaseChange k f' f l hpushk hpushf
        hpushf' hpushl sq)) := by
  rw [twistedInverseImageBaseChangeMap_eq_mateEquiv_symm]
  exact Equiv.apply_symm_apply _ _

/-- **[Stacks, Tag 0ATQ] (Lemma 48.5.1): the base change maps of a vertical stack of two
cartesian squares compose to the base change map of the outer rectangle.** For

```
X' --k--> X
|f'       |f
Y' --l--> Y
|g'       |g
Z' --m--> Z
```

with both squares cartesian, the base change map `Stacks.Duality.twistedInverseImageBaseChangeMap`
of [Stacks, Tag 0AA6] for the rectangle — the square with horizontal edges `k` and `m` and
vertical edges `f' ≫ g'` and `f ≫ g` — is the horizontal composite of the base change maps of the
lower and of the upper square, the twisted inverse images along the two composite verticals being
read through the comparison `Stacks.Duality.twistedInverseImageCompIso` of [Stacks, Tag 0ATX].

The source's proof reduces the statement to the identity `ξ_rect = ξ_bot ≫ₕ ξ_top`, which is
`Stacks.Duality.twistedInverseImagePushforwardBaseChange_vcomp`; the passage from that identity to
this one is the compatibility of `CategoryTheory.mateEquiv` with vertical composition, because
each base change map is the mate of the inverse of the corresponding `ξ`
(`Stacks.Duality.twistedInverseImageBaseChangeMap_eq_mateEquiv_symm`). -/
@[stacks 0ATQ "for the base change map of Stacks 0AA6 attached to the twisted inverse image \
  f^x of Stacks 0A9E -- the right adjoint of Rf_* on D_QCoh -- and for the comparison \
  (f then g)^x = g^x then f^x of Stacks 0ATX: the map of the outer rectangle of a vertical \
  stack of two cartesian squares is the horizontal composite of the maps of the two squares, \
  read through those comparisons. The source's quasi-compactness and quasi-separatedness enter \
  as the preservation of quasi-coherent cohomology by derived direct and inverse image along \
  the morphisms of the diagram and as the existence of the six right adjoints, which is what \
  Stacks 08D5 part (1) and Stacks 0A9E produce for a quasi-compact quasi-separated morphism; \
  Stacks.Duality.twistedInverseImageCompIsoOfQcqs is the pattern that discharges them. \
  Invertibility of the transformation xi of Stacks 0A9K for each of the two squares is an \
  instance argument, exactly as in Stacks.Duality.twistedInverseImageBaseChangeMap where the \
  base change map is defined, and it is Stacks 0A9K that produces it for a Tor-independent \
  square. What is NOT claimed is the passage from f^x to the f^! of a general \
  compactification, Stacks.Duality.upperShriek, which needs the independence of the chosen \
  compactification, Stacks 0AA0"]
theorem twistedInverseImageBaseChangeMap_vcomp (sq₁ : IsPullback k f' f l)
    (sq₂ : IsPullback l g' g m)
    [IsIso (twistedInverseImagePushforwardBaseChange k f' f l hpushk hpushf hpushf' hpushl sq₁)]
    [IsIso (twistedInverseImagePushforwardBaseChange l g' g m hpushl hpushg hpushg' hpushm sq₂)] :
    letI := isIso_twistedInverseImagePushforwardBaseChange_vcomp k f' f l g' g m hpushk hpushf
      hpushf' hpushl hpushg hpushg' hpushm hpushfg hpushf'g' sq₁ sq₂
    twistedInverseImageBaseChangeMap k (f' ≫ g') (f ≫ g) m hpushk hpushfg hpushf'g' hpushm
        (sq₁.paste_vert sq₂) =
      ((TwoSquare.mk _ _ _ _ (twistedInverseImageBaseChangeMap l g' g m hpushl hpushg hpushg'
              hpushm sq₂) ≫ₕ
          TwoSquare.mk _ _ _ _ (twistedInverseImageBaseChangeMap k f' f l hpushk hpushf hpushf'
            hpushl sq₁)).whiskerTop
        (twistedInverseImageCompIso f g hpushf hpushg hpushfg).hom).whiskerBottom
        (twistedInverseImageCompIso f' g' hpushf' hpushg' hpushf'g').inv := by
  let := isIso_twistedInverseImagePushforwardBaseChange_vcomp k f' f l g' g m hpushk hpushf
    hpushf' hpushl hpushg hpushg' hpushm hpushfg hpushf'g' sq₁ sq₂
  have hinv : TwoSquare.mk _ _ _ _
        (inv (twistedInverseImagePushforwardBaseChange k (f' ≫ g') (f ≫ g) m hpushk hpushfg
          hpushf'g' hpushm (sq₁.paste_vert sq₂))) =
      ((TwoSquare.mk _ _ _ _ (inv (twistedInverseImagePushforwardBaseChange l g' g m hpushl
            hpushg hpushg' hpushm sq₂)) ≫ᵥ
        TwoSquare.mk _ _ _ _ (inv (twistedInverseImagePushforwardBaseChange k f' f l hpushk
          hpushf hpushf' hpushl sq₁))).whiskerRight
          (twistedInverseImageCompIso f g hpushf hpushg hpushfg).hom).whiskerLeft
        (twistedInverseImageCompIso f' g' hpushf' hpushg' hpushf'g').inv := by
    refine IsIso.inv_eq_of_hom_inv_id ?_
    rw [twistedInverseImagePushforwardBaseChange_vcomp k f' f l g' g m hpushk hpushf hpushf'
      hpushl hpushg hpushg' hpushm hpushfg hpushf'g' sq₁ sq₂]
    exact hComp_whiskered_hom_inv_id _ _ (twistedInverseImageCompIso f' g' hpushf' hpushg'
      hpushf'g') (twistedInverseImageCompIso f g hpushf hpushg hpushfg).symm
  have step : mateEquiv
        (quasiCoherentDerivedAdjunction m (isQuasicoherent_homology_derivedPullback' m) hpushm)
        (quasiCoherentDerivedAdjunction k (isQuasicoherent_homology_derivedPullback' k) hpushk)
        (TwoSquare.mk _ _ _ _ (twistedInverseImageBaseChangeMap l g' g m hpushl hpushg hpushg'
            hpushm sq₂) ≫ₕ
          TwoSquare.mk _ _ _ _ (twistedInverseImageBaseChangeMap k f' f l hpushk hpushf hpushf'
            hpushl sq₁)) =
      TwoSquare.mk _ _ _ _ (inv (twistedInverseImagePushforwardBaseChange l g' g m hpushl hpushg
          hpushg' hpushm sq₂)) ≫ᵥ
        TwoSquare.mk _ _ _ _ (inv (twistedInverseImagePushforwardBaseChange k f' f l hpushk
          hpushf hpushf' hpushl sq₁)) := by
    rw [mateEquiv_vcomp
      (quasiCoherentDerivedAdjunction m (isQuasicoherent_homology_derivedPullback' m) hpushm)
      (quasiCoherentDerivedAdjunction l (isQuasicoherent_homology_derivedPullback' l) hpushl)
      (quasiCoherentDerivedAdjunction k (isQuasicoherent_homology_derivedPullback' k) hpushk),
      mateEquiv_twistedInverseImageBaseChangeMap l g' g m hpushl hpushg hpushg' hpushm sq₂,
      mateEquiv_twistedInverseImageBaseChangeMap k f' f l hpushk hpushf hpushf' hpushl sq₁]
  exact (twistedInverseImageBaseChangeMap_eq_mateEquiv_symm k (f' ≫ g') (f ≫ g) m hpushk
    hpushfg hpushf'g' hpushm (sq₁.paste_vert sq₂)).trans
      ((congrArg (fun z => (mateEquiv
          (quasiCoherentDerivedAdjunction m (isQuasicoherent_homology_derivedPullback' m) hpushm)
          (quasiCoherentDerivedAdjunction k (isQuasicoherent_homology_derivedPullback' k)
            hpushk)).symm z)
        (hinv.trans ((congrArg (fun z => (TwoSquare.whiskerRight z
              (twistedInverseImageCompIso f g hpushf hpushg hpushfg).hom).whiskerLeft
            (twistedInverseImageCompIso f' g' hpushf' hpushg' hpushf'g').inv)
          step.symm).trans
            (mateEquiv_whisker
              (quasiCoherentDerivedAdjunction m (isQuasicoherent_homology_derivedPullback' m)
                hpushm)
              (quasiCoherentDerivedAdjunction k (isQuasicoherent_homology_derivedPullback' k)
                hpushk)
              _ _ _).symm))).trans
        (Equiv.symm_apply_apply _ _))

end Gamma

end Stacks.Duality

end
