module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ConstantSheafInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystemIdentity
public import StacksFrontier.AlgebraicGeometry.Picard.FrobeniusTorsion
public import StacksFrontier.CategoryTheory.Adjunction.Mates

/-!
# The Frobenius coherence of a restricted sheaf

Let `pr : Y ⟶ X` be a morphism of schemes of characteristic `p`, and let `ga, gb` be two
self-maps of `Y` whose composite is the `n`-fold absolute Frobenius `F_Y^n`, with `ga` a
morphism over `X` and `gb` lying over the `n`-fold absolute Frobenius `F_X^n`.  This file
proves the coherence at the level of the small étale sites which underlies the statement that
the two restriction endomorphisms of the cohomology of a sheaf pulled back along `pr` are
mutually inverse.

Every comparison in sight is a morphism into a base change along `pr` of a base change along
`F_X^n`, and is therefore determined by its two first projections; those projections are the
`n`-fold absolute Frobenius on both sides, so the coherence comes down to naturality of the
`n`-fold absolute Frobenius against `pr`.

## Main definitions

* `Stacks.EtaleCohomology.frobeniusRestrictionCoeffFrob` — the identification of a sheaf pulled
  back along `pr` with its inverse image along `gb`.
* `Stacks.EtaleCohomology.frobeniusRestrictionUnit` — the identification of the composite of
  the two inverse images with the identity functor.

## Main results

* `Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_inv_fst` — the first projection of the
  inverse of the base-change comparison for a composite.
* `Stacks.EtaleCohomology.frobeniusRestrictionSiteCoherence` — the site coherence.
* `Stacks.EtaleCohomology.etaleAbelianDirectImageFrobeniusCoherence` — the identity between
  direct images that it induces.
* `Stacks.EtaleCohomology.frobeniusRestrictionConstantCoherence` and
  `Stacks.EtaleCohomology.frobeniusRestrictionCoeffCoherence` — the two coherences of the
  restriction endomorphisms: on the constant sheaf out of which cohomology is computed, and on
  the coefficients.
* `Stacks.EtaleCohomology.frobeniusRestrictionCoeffCoherence'` — the coefficient coherence with
  the roles of `ga` and `gb` exchanged, which is what makes the two endomorphisms mutually
  inverse in both orders rather than only one.

## Implementation notes

The rearrangement of the five-fold composite is isolated as
`Stacks.EtaleCohomology.frobeniusChainRearrange`, a statement about an arbitrary category: the
objects of a small étale site are objects of a `MorphismProperty.Comma` category whose
morphism property is a class rather than a term of `MorphismProperty`, so goals mentioning
their structure morphisms are not type-correct at `implicit` transparency and `rw` cannot
operate on them.  All the rewriting therefore happens on abstract variables, and the concrete
proof only applies the resulting lemma to the nine projection formulas.

## References

* [Stacks Project, Tag 03SV](https://stacks.math.columbia.edu/tag/03SV)
-/

@[expose] public noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

namespace Stacks.EtaleCohomology

/-- Composition in the small étale site is computed on the underlying schemes. -/
private lemma etaleCompLeft {Z : Scheme.{u}} {A B C : Z.Etale} (q : A ⟶ B) (r : B ⟶ C) :
    (q ≫ r).left = q.left ≫ r.left := rfl

/-- The identity of the small étale site is the identity on the underlying scheme. -/
private lemma etaleIdLeft {Z : Scheme.{u}} (A : Z.Etale) :
    (𝟙 A : A ⟶ A).left = 𝟙 A.left := rfl

/-- The first projection of the inverse of the base-change comparison for a composite: the two
projections of the iterated base change.  This is
`Stacks.EtaleCohomology.smallEtaleBaseChangeComp'_fst_fst` read through the isomorphism. -/
public lemma smallEtaleBaseChangeComp'_inv_fst {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    (fg : W ⟶ Y) (hfg : fg = f ≫ g) (U : Y.Etale) :
    ((smallEtaleBaseChangeComp' f g fg hfg).inv.app U).left ≫ pullback.fst U.hom fg =
      pullback.fst ((smallEtaleBaseChange g).obj U).hom f ≫ pullback.fst U.hom g := by
  rw [← smallEtaleBaseChangeComp'_fst_fst f g fg hfg U, ← Category.assoc, ← etaleCompLeft,
    (smallEtaleBaseChangeComp' f g fg hfg).inv_hom_id_app, etaleIdLeft]
  exact Category.id_comp _

/-- A morphism into a twice-iterated base change is determined by its composite first
projection onto the original object. -/
private lemma smallEtaleBaseChangeDoubleHomExt {W X Y : Scheme.{u}} (f : W ⟶ X) (g : X ⟶ Y)
    {A : W.Etale} {V : Y.Etale}
    {a b : A ⟶ (smallEtaleBaseChange f).obj ((smallEtaleBaseChange g).obj V)}
    (hab : a.left ≫ pullback.fst ((smallEtaleBaseChange g).obj V).hom f ≫
        pullback.fst V.hom g =
      b.left ≫ pullback.fst ((smallEtaleBaseChange g).obj V).hom f ≫
        pullback.fst V.hom g) :
    a = b :=
  smallEtaleBaseChange_hom_ext f (pullback.hom_ext hab
    ((smallEtaleBaseChange_fst_snd f g a).trans (smallEtaleBaseChange_fst_snd f g b).symm))

/-- **The rearrangement of the five-fold composite of the site coherence.**  Nine projection
formulas, chained, identify the composite with its last factor's projection, and the final
naturality square closes the comparison.  Stated for an arbitrary category: see the
implementation notes. -/
public theorem frobeniusChainRearrange {D : Type*} [Category* D]
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ : D} {x₀ : O₁ ⟶ O₆} {x₁ : O₁ ⟶ O₂} {x₂ : O₂ ⟶ O₃}
    {x₃ : O₃ ⟶ O₄} {x₄ : O₄ ⟶ O₅} {x₅ : O₅ ⟶ O₆} {c₁ : O₆ ⟶ O₇} {c₂ : O₇ ⟶ O₈}
    {y₅ : O₅ ⟶ O₆} {y₄ : O₄ ⟶ O₉} {z₄ : O₉ ⟶ O₆} {y₃ : O₃ ⟶ O₁₀} {z₃ : O₁₀ ⟶ O₉}
    {u : O₉ ⟶ O₈} {e : O₁₀ ⟶ O₁} {k : O₁ ⟶ O₈} {d : O₂ ⟶ O₁} {l : O₈ ⟶ O₇}
    {φ : O₁ ⟶ O₁} {ψ : O₈ ⟶ O₈}
    (hA : x₅ ≫ c₁ = y₅ ≫ c₁) (hB : x₄ ≫ y₅ = y₄ ≫ z₄) (hC : z₄ ≫ c₁ ≫ c₂ = u)
    (hD : x₃ ≫ y₄ = y₃ ≫ z₃) (hE : z₃ ≫ u = e ≫ k) (hF : x₂ ≫ y₃ ≫ e = d)
    (hG : x₁ ≫ d = φ) (hH : x₀ ≫ c₁ = k ≫ l) (hI : l ≫ c₂ = ψ) (hJ : φ ≫ k = k ≫ ψ) :
    (x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅) ≫ c₁ ≫ c₂ = x₀ ≫ c₁ ≫ c₂ := by
  simp only [Category.assoc]
  rw [reassoc_of% hA, reassoc_of% hB, hC, reassoc_of% hD, hE, reassoc_of% hF,
    reassoc_of% hG, hJ, reassoc_of% hH, hI]

section Site

variable {X Y : Scheme.{u}} (pr : Y ⟶ X) (p : ℕ) [Fact p.Prime]
  (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) {n : ℕ} (hn : n ≠ 0)
  (ga gb : Y ⟶ Y) (hga : pr = ga ≫ pr) (m : Y ⟶ X) (hgb : m = gb ≫ pr)
  (hm : m = pr ≫ absoluteFrobeniusPow X p hX n)
  (hcomp : absoluteFrobeniusPow Y p hY n = ga ≫ gb)

/-- **The site-level Frobenius coherence.**  For an étale `U` over `X`, the relative Frobenius
of `U ×_X Y`, followed by the comparison of the base change along `F_Y^n = ga ∘ gb` with the two
base changes, the comparison of the base changes along `gb ∘ pr = pr ∘ F_X^n`, and the
comparison of the base change along `ga ∘ pr = pr`, is the base change along `pr` of the
relative Frobenius of `U`.

Both sides are morphisms into a twice-iterated base change, hence determined by their composite
first projection; that projection is the `n`-fold absolute Frobenius on both sides, and the
claim is its naturality against the first projection of `U ×_X Y`. -/
public lemma frobeniusRestrictionSiteCoherence (U : X.Etale) :
    (absoluteFrobeniusPowEtaleSiteIso Y p hY hn).hom.app
          ((smallEtaleBaseChange pr).obj U) ≫
        (smallEtaleBaseChangeComp' ga gb (absoluteFrobeniusPow Y p hY n) hcomp).hom.app
          ((smallEtaleBaseChange pr).obj U) ≫
        (smallEtaleBaseChange ga).map ((smallEtaleBaseChangeComp' gb pr m hgb).inv.app U) ≫
        (smallEtaleBaseChange ga).map
          ((smallEtaleBaseChangeComp' pr (absoluteFrobeniusPow X p hX n) m hm).hom.app U) ≫
        (smallEtaleBaseChangeComp' ga pr pr hga).inv.app
          ((smallEtaleBaseChange (absoluteFrobeniusPow X p hX n)).obj U) =
      (smallEtaleBaseChange pr).map
        ((absoluteFrobeniusPowEtaleSiteIso X p hX hn).hom.app U) :=
  smallEtaleBaseChangeDoubleHomExt pr (absoluteFrobeniusPow X p hX n)
    (frobeniusChainRearrange
      (smallEtaleBaseChangeComp'_inv_fst ga pr pr hga
        ((smallEtaleBaseChange (absoluteFrobeniusPow X p hX n)).obj U))
      (smallEtaleBaseChange_map_left_fst ga
        ((smallEtaleBaseChangeComp' pr (absoluteFrobeniusPow X p hX n) m hm).hom.app U))
      (smallEtaleBaseChangeComp'_fst_fst pr (absoluteFrobeniusPow X p hX n) m hm U)
      (smallEtaleBaseChange_map_left_fst ga
        ((smallEtaleBaseChangeComp' gb pr m hgb).inv.app U))
      (smallEtaleBaseChangeComp'_inv_fst gb pr m hgb U)
      (smallEtaleBaseChangeComp'_fst_fst ga gb (absoluteFrobeniusPow Y p hY n) hcomp
        ((smallEtaleBaseChange pr).obj U))
      (absoluteFrobeniusPowEtaleSiteIso_hom_app_left_fst Y p hY hn
        ((smallEtaleBaseChange pr).obj U))
      (smallEtaleBaseChange_map_left_fst pr
        ((absoluteFrobeniusPowEtaleSiteIso X p hX hn).hom.app U))
      (absoluteFrobeniusPowEtaleSiteIso_hom_app_left_fst X p hX hn U)
      (absoluteFrobeniusPow_naturality (pullback.fst U.hom pr) p _ _ n))

/-- If `ehh ≫ wh ≫ Q = prh` with `wi` and `ehi` left inverse to `wh` and `ehh`, then `Q` is
`wi ≫ ehi ≫ prh`. -/
private theorem eq_comp_of_inv_form {D : Type*} [Category* D] {O₁ O₄ O₅ O₆ : D}
    {Q : O₁ ⟶ O₅} {prh : O₄ ⟶ O₅} {ehh : O₄ ⟶ O₆} {ehi : O₆ ⟶ O₄} {wh : O₆ ⟶ O₁}
    {wi : O₁ ⟶ O₆} (hcoh : ehh ≫ wh ≫ Q = prh) (hwi : wi ≫ wh = 𝟙 O₁)
    (heh : ehi ≫ ehh = 𝟙 O₆) : Q = wi ≫ ehi ≫ prh := by
  have h₁ : wh ≫ Q = ehi ≫ prh := by
    rw [← hcoh]
    simp only [← Category.assoc, heh, Category.id_comp]
  rw [← h₁, ← Category.assoc wi wh, hwi, Category.id_comp]

/-- **The site coherence, read with the inverses of the two Frobenius identifications.**  This
is the form in which it transports to direct images of sheaves.  Stated for an arbitrary
category: see the implementation notes. -/
public theorem invFormRearrange {D : Type*} [Category* D] {O₁ O₁' O₂ O₃ O₄ O₅ O₆ : D}
    {P₁ : O₁ ⟶ O₁'} {P₂ : O₁' ⟶ O₂} {r : O₂ ⟶ O₃} {du : O₃ ⟶ O₄} {dl : O₂ ⟶ O₅}
    {prhi : O₅ ⟶ O₄} {prh : O₄ ⟶ O₅} {ehh : O₄ ⟶ O₆} {ehi : O₆ ⟶ O₄}
    {wh : O₆ ⟶ O₁} {wi : O₁ ⟶ O₆}
    (hnat : r ≫ du = dl ≫ prhi) (hcoh : ehh ≫ wh ≫ P₁ ≫ P₂ ≫ dl = prh)
    (hprh : prh ≫ prhi = 𝟙 O₄) (hwi : wi ≫ wh = 𝟙 O₁) (heh : ehi ≫ ehh = 𝟙 O₆) :
    P₁ ≫ P₂ ≫ r ≫ du = wi ≫ ehi := by
  have h₂ := eq_comp_of_inv_form hcoh hwi heh
  rw [hnat, reassoc_of% h₂, hprh, Category.comp_id]

/-- **The site-level Frobenius coherence in inverse form.**  The two coefficient
identifications of a sheaf pulled back along `pr` — one along `ga`, over `X`, and one along
`gb`, over the `n`-fold absolute Frobenius of `X` — compose to the identification coming from
Frobenius descent on `Y`.  This is
`Stacks.EtaleCohomology.frobeniusRestrictionSiteCoherence` with the three isomorphisms
inverted. -/
public lemma frobeniusRestrictionSiteCoherence_inv (U : X.Etale) :
    (smallEtaleBaseChange ga).map ((smallEtaleBaseChangeComp' gb pr m hgb).inv.app U) ≫
        (smallEtaleBaseChange ga).map
          ((smallEtaleBaseChangeComp' pr (absoluteFrobeniusPow X p hX n) m hm).hom.app U) ≫
        (smallEtaleBaseChange ga).map
          ((smallEtaleBaseChange pr).map
            ((absoluteFrobeniusPowEtaleSiteIso X p hX hn).inv.app U)) ≫
        (smallEtaleBaseChangeComp' ga pr pr hga).inv.app U =
      (smallEtaleBaseChangeComp' ga gb (absoluteFrobeniusPow Y p hY n) hcomp).inv.app
          ((smallEtaleBaseChange pr).obj U) ≫
        (absoluteFrobeniusPowEtaleSiteIso Y p hY hn).inv.app
          ((smallEtaleBaseChange pr).obj U) :=
  invFormRearrange
    ((smallEtaleBaseChangeComp' ga pr pr hga).inv.naturality
      ((absoluteFrobeniusPowEtaleSiteIso X p hX hn).inv.app U))
    (frobeniusRestrictionSiteCoherence pr p hX hY hn ga gb hga m hgb hm hcomp U)
    (((smallEtaleBaseChange pr).mapIso
      ((absoluteFrobeniusPowEtaleSiteIso X p hX hn).app U)).hom_inv_id)
    ((smallEtaleBaseChangeComp' ga gb (absoluteFrobeniusPow Y p hY n) hcomp).inv_hom_id_app
      ((smallEtaleBaseChange pr).obj U))
    ((absoluteFrobeniusPowEtaleSiteIso Y p hY hn).inv_hom_id_app
      ((smallEtaleBaseChange pr).obj U))

end Site

/-! ### Transport to direct images of abelian sheaves -/

section Transport

/-- Composition of morphisms of sheaves is computed section by section. -/
private alias sheafCompHomApp := sheaf_comp_hom_app

/-- The identity of a sheaf is the identity on sections. -/
private lemma sheafIdHomApp {W : Type u} [Category.{v} W] {K : GrothendieckTopology W}
    {B : Type*} [Category B] (F : Sheaf K B) (U : Wᵒᵖ) :
    (𝟙 F : F ⟶ F).hom.app U = 𝟙 _ := rfl

/-- The two spellings of the opposite of a morphism agree. -/
private lemma opEqHomOp {C : Type*} [Category* C] {A B : C} (k : A ⟶ B) :
    @Opposite.op (A ⟶ B) k = k.op := rfl

/-- The sections of a direct image are the sections over the base change. -/
private lemma directImageObjMap {W Z : Scheme.{u}} (i : W ⟶ Z)
    (G : Sheaf W.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) {A B : Z.Etale} (k : A ⟶ B) :
    ((etaleAbelianDirectImage.{u, v} i).obj G).obj.map k.op =
      G.obj.map ((smallEtaleBaseChange i).map k).op := rfl

/-- The direct image of a morphism of sheaves is the morphism on sections over the base
change. -/
private lemma directImageMapHomApp {W Z : Scheme.{u}} (i : W ⟶ Z)
    {G H : Sheaf W.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}} (ψ : G ⟶ H) (U : Z.Etale) :
    ((etaleAbelianDirectImage.{u, v} i).map ψ).hom.app (op U) =
      ψ.hom.app (op ((smallEtaleBaseChange i).obj U)) := rfl

/-- The sections of the comparison for a composite direct image of abelian sheaves. -/
public lemma etaleAbelianDirectImageCompIso'_hom_app_hom_app {W Z T : Scheme.{u}} (f : W ⟶ Z)
    (g : Z ⟶ T) (fg : W ⟶ T) (hfg : fg = f ≫ g)
    (F : Sheaf W.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) (U : (T.Etale)ᵒᵖ) :
    ((etaleAbelianDirectImageCompIso'.{u, v} f g fg hfg).hom.app F).hom.app U =
      F.obj.map (op ((smallEtaleBaseChangeComp' f g fg hfg).hom.app U.unop)) :=
  smallEtalePushforwardComp'_hom_app_hom_app f g fg hfg AddCommGrpCat.{max (u + 1) v} F U

variable {X Y : Scheme.{u}} (pr : Y ⟶ X) (p : ℕ) [Fact p.Prime]
  (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) {n : ℕ} (hn : n ≠ 0)
  (ga gb : Y ⟶ Y) (hga : pr = ga ≫ pr) (m : Y ⟶ X) (hgb : m = gb ≫ pr)
  (hm : m = pr ≫ absoluteFrobeniusPow X p hX n)
  (hcomp : absoluteFrobeniusPow Y p hY n = ga ≫ gb)

/-- **The Frobenius coherence between direct images.**  This is the conjugate, under the
inverse-image/direct-image adjunctions, of the coefficient coherence
`Stacks.EtaleCohomology.frobeniusRestrictionCoeffCoherence`; it is the site coherence
`Stacks.EtaleCohomology.frobeniusRestrictionSiteCoherence_inv` read on sections, direct image
being restriction along base change. -/
public theorem etaleAbelianDirectImageFrobeniusCoherence :
    (etaleAbelianDirectImageCompIso'.{u, v} ga pr pr hga).inv ≫
        Functor.whiskerLeft (etaleAbelianDirectImage.{u, v} ga)
          ((Functor.rightUnitor (etaleAbelianDirectImage.{u, v} pr)).inv ≫
            Functor.whiskerLeft (etaleAbelianDirectImage.{u, v} pr)
                (etaleSheafPushforwardComparison X (absoluteFrobeniusPow X p hX n)
                    (absoluteFrobeniusPowEtaleSiteIso X p hX hn)
                    AddCommGrpCat.{max (u + 1) v}).hom ≫
              (etaleAbelianDirectImageCompIso'.{u, v} pr
                  (absoluteFrobeniusPow X p hX n) m hm).hom ≫
                (etaleAbelianDirectImageCompIso'.{u, v} gb pr m hgb).inv) =
      (Functor.leftUnitor (etaleAbelianDirectImage.{u, v} pr)).inv ≫
        Functor.whiskerRight
            ((etaleSheafPushforwardComparison Y (absoluteFrobeniusPow Y p hY n)
                  (absoluteFrobeniusPowEtaleSiteIso Y p hY hn)
                  AddCommGrpCat.{max (u + 1) v}).hom ≫
              (etaleAbelianDirectImageCompIso'.{u, v} ga gb
                (absoluteFrobeniusPow Y p hY n) hcomp).inv)
            (etaleAbelianDirectImage.{u, v} pr) ≫
          (Functor.associator (etaleAbelianDirectImage.{u, v} ga)
            (etaleAbelianDirectImage.{u, v} gb) (etaleAbelianDirectImage.{u, v} pr)).hom := by
  refine NatTrans.ext (funext fun G ↦ Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_)))
  obtain ⟨U⟩ := U
  have h := congrArg (fun z ↦ G.obj.map (Quiver.Hom.op z))
    (frobeniusRestrictionSiteCoherence_inv pr p hX hY hn ga gb hga m hgb hm hcomp U)
  simp only [op_comp, Functor.map_comp, Category.assoc] at h
  simp only [sheafCompHomApp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_inv_app, etaleAbelianDirectImageCompIso'_inv_app_hom_app,
    etaleAbelianDirectImageCompIso'_hom_app_hom_app,
    etaleSheafPushforwardComparison_hom_app_hom_app, opEqHomOp, directImageObjMap,
    directImageMapHomApp, Category.id_comp, Category.comp_id]
  exact h

end Transport

/-! ### The coefficient coherence -/

section Coefficient

/-- **The conjugate of the Frobenius-descent identification of inverse images is the one for
direct images.**  The inverse-image identification is by construction the comparison of left
adjoints attached to the direct-image identification, and this reads that construction back. -/
public theorem conjugateEquiv_etaleSheafInverseImageComparison_hom {X : Scheme.{u}} (g : X ⟶ X)
    (e : 𝟭 X.Etale ≅ smallEtaleBaseChange g)
    [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
    [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
      (smallEtaleBaseChange g).op.HasLeftKanExtension F] :
    conjugateEquiv Adjunction.id (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
        (etaleSheafInverseImageComparison X g e AddCommGrpCat.{max (u + 1) v}).hom =
      (etaleSheafPushforwardComparison X g e AddCommGrpCat.{max (u + 1) v}).hom := by
  have hu : conjugateEquiv
      (Adjunction.id.ofNatIsoRight
        (etaleSheafPushforwardComparison X g e AddCommGrpCat.{max (u + 1) v}))
      (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
      (etaleSheafInverseImageComparison X g e AddCommGrpCat.{max (u + 1) v}).hom = 𝟙 _ := by
    simp only [etaleSheafInverseImageComparison]
    exact Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_hom _ _
  have h := conjugateEquiv_comp
    (Adjunction.id.ofNatIsoRight
      (etaleSheafPushforwardComparison X g e AddCommGrpCat.{max (u + 1) v}))
    (Adjunction.id (C := Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}))
    (etaleAbelianInverseImageDirectImageAdj.{u, v} g)
    (𝟙 (𝟭 (Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v})))
    (etaleSheafInverseImageComparison X g e AddCommGrpCat.{max (u + 1) v}).hom
  rw [Stacks.CategoryTheory.conjugateEquiv_ofNatIsoRight_id, Category.comp_id, hu] at h
  have h' := congrArg
    (fun t ↦ (etaleSheafPushforwardComparison X g e AddCommGrpCat.{max (u + 1) v}).hom ≫ t) h
  simpa using h'

variable {X Y : Scheme.{u}} (pr : Y ⟶ X) (p : ℕ) [Fact p.Prime]
  (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) {n : ℕ} (hn : n ≠ 0)
  (ga gb : Y ⟶ Y) (hga : pr = ga ≫ pr) (m : Y ⟶ X) (hgb : m = gb ≫ pr)
  (hm : m = pr ≫ absoluteFrobeniusPow X p hX n)
  (hcomp : absoluteFrobeniusPow Y p hY n = ga ≫ gb)
  [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
    (smallEtaleBaseChange (absoluteFrobeniusPow X p hX n)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
    (smallEtaleBaseChange (absoluteFrobeniusPow Y p hY n)).op.HasLeftKanExtension F]

/-- **The coefficient identification along the Frobenius factor.**  A sheaf pulled back along
`pr` is identified with its inverse image along `gb`: the composite `gb ∘ pr` is `pr ∘ F_X^n`,
and Frobenius descent on `X` identifies the inverse image along `F_X^n` with the identity. -/
public def frobeniusRestrictionCoeffFrob :
    etaleAbelianInverseImage.{u, v} pr ⋙ etaleAbelianInverseImage.{u, v} gb ⟶
      etaleAbelianInverseImage.{u, v} pr :=
  (etaleAbelianInverseImageCompIso'.{u, v} gb pr m hgb).inv ≫
    (etaleAbelianInverseImageCompIso'.{u, v} pr (absoluteFrobeniusPow X p hX n) m hm).hom ≫
      Functor.whiskerRight
          (etaleSheafInverseImageComparison X (absoluteFrobeniusPow X p hX n)
            (absoluteFrobeniusPowEtaleSiteIso X p hX hn)
            AddCommGrpCat.{max (u + 1) v}).hom (etaleAbelianInverseImage.{u, v} pr) ≫
        (Functor.leftUnitor (etaleAbelianInverseImage.{u, v} pr)).hom

/-- **The identification of the composite of the two inverse images with the identity.**  The
composite of `ga` and `gb` is the `n`-fold absolute Frobenius of `Y`, whose inverse image is
identified with the identity functor by Frobenius descent on `Y`.  It is not invertible as a
pair of separate identifications: only the composite is. -/
public def frobeniusRestrictionUnit :
    etaleAbelianInverseImage.{u, v} gb ⋙ etaleAbelianInverseImage.{u, v} ga ⟶
      𝟭 (Sheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :=
  (etaleAbelianInverseImageCompIso'.{u, v} ga gb (absoluteFrobeniusPow Y p hY n) hcomp).inv ≫
    (etaleSheafInverseImageComparison Y (absoluteFrobeniusPow Y p hY n)
      (absoluteFrobeniusPowEtaleSiteIso Y p hY hn) AddCommGrpCat.{max (u + 1) v}).hom

/-- **The constant-sheaf coherence of the two restrictions.**  The two constant-sheaf
comparisons compose to the identification of the composite inverse image with the identity.
This is the hypothesis on the source data of
`Stacks.EtaleCohomology.etaleCohomologyEndo_comp`. -/
public theorem frobeniusRestrictionConstantCoherence (A : AddCommGrpCat.{max (u + 1) v}) :
    ((etaleAbelianInverseImageConstantIso.{u, v} ga).app A).inv ≫
        (etaleAbelianInverseImage.{u, v} ga).map
            ((etaleAbelianInverseImageConstantIso.{u, v} gb).app A).inv ≫
          (frobeniusRestrictionUnit.{u, v} p hY hn ga gb hcomp).app
            ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) =
      𝟙 ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) := by
  have h : ((etaleAbelianInverseImage.{u, v} ga).mapIso
          ((etaleAbelianInverseImageConstantIso.{u, v} gb).app A) ≪≫
        (etaleAbelianInverseImageConstantIso.{u, v} ga).app A).symm.hom =
      (((etaleAbelianInverseImageCompIso'.{u, v} ga gb
              (absoluteFrobeniusPow Y p hY n) hcomp).app
            ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A)).symm ≪≫
        (etaleAbelianInverseImageConstantIso.{u, v}
          (absoluteFrobeniusPow Y p hY n)).app A).symm.hom :=
    congrArg Iso.hom (congrArg Iso.symm (Iso.ext
      (etaleAbelianInverseImageConstantIso_comp.{u, v} gb ga
        (absoluteFrobeniusPow Y p hY n) hcomp A)))
  have hw : (frobeniusRestrictionUnit.{u, v} p hY hn ga gb hcomp).app
        ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) =
      (etaleAbelianInverseImageCompIso'.{u, v} ga gb
            (absoluteFrobeniusPow Y p hY n) hcomp).inv.app
          ((constantSheaf Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}).obj A) ≫
        (etaleAbelianInverseImageConstantIso.{u, v}
          (absoluteFrobeniusPow Y p hY n)).hom.app A := by
    rw [frobeniusRestrictionUnit, NatTrans.comp_app,
      etaleSheafInverseImageComparison_app_constantSheaf]
  simp only [Iso.symm_hom, Iso.trans_inv, Functor.mapIso_inv, Iso.symm_inv] at h
  rw [← Category.assoc, h, hw]
  simp

/-- The conjugate of the coefficient identification along the Frobenius factor: the three
comparisons of inverse images it is built from conjugate to the three comparisons of direct
images, and the unitor to the other unitor. -/
public theorem conjugateEquiv_frobeniusRestrictionCoeffFrob :
    conjugateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v} pr)
        ((etaleAbelianInverseImageDirectImageAdj.{u, v} pr).comp
          (etaleAbelianInverseImageDirectImageAdj.{u, v} gb))
        (frobeniusRestrictionCoeffFrob.{u, v} pr p hX hn gb m hgb hm) =
      (Functor.rightUnitor (etaleAbelianDirectImage.{u, v} pr)).inv ≫
        Functor.whiskerLeft (etaleAbelianDirectImage.{u, v} pr)
            (etaleSheafPushforwardComparison X (absoluteFrobeniusPow X p hX n)
              (absoluteFrobeniusPowEtaleSiteIso X p hX hn)
              AddCommGrpCat.{max (u + 1) v}).hom ≫
          (etaleAbelianDirectImageCompIso'.{u, v} pr
              (absoluteFrobeniusPow X p hX n) m hm).hom ≫
            (etaleAbelianDirectImageCompIso'.{u, v} gb pr m hgb).inv := by
  simp only [frobeniusRestrictionCoeffFrob]
  rw [← conjugateEquiv_comp _ (etaleAbelianInverseImageDirectImageAdj.{u, v} m) _,
    conjugateEquiv_etaleAbelianInverseImageCompIso'_inv,
    ← conjugateEquiv_comp _
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} (absoluteFrobeniusPow X p hX n)).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} pr)) _,
    conjugateEquiv_etaleAbelianInverseImageCompIso'_hom,
    ← conjugateEquiv_comp _
      (Adjunction.id.comp (etaleAbelianInverseImageDirectImageAdj.{u, v} pr)) _,
    conjugateEquiv_leftUnitor_hom,
    conjugateEquiv_whiskerRight Adjunction.id
      (etaleAbelianInverseImageDirectImageAdj.{u, v} (absoluteFrobeniusPow X p hX n))
      (etaleAbelianInverseImageDirectImageAdj.{u, v} pr) _,
    conjugateEquiv_etaleSheafInverseImageComparison_hom]
  simp only [Category.assoc]

/-- The conjugate of the identification of the composite inverse image with the identity: the
Frobenius descent on `Y`, followed by the comparison of the two direct images. -/
public theorem conjugateEquiv_frobeniusRestrictionUnit :
    conjugateEquiv Adjunction.id
        ((etaleAbelianInverseImageDirectImageAdj.{u, v} gb).comp
          (etaleAbelianInverseImageDirectImageAdj.{u, v} ga))
        (frobeniusRestrictionUnit.{u, v} p hY hn ga gb hcomp) =
      (etaleSheafPushforwardComparison Y (absoluteFrobeniusPow Y p hY n)
            (absoluteFrobeniusPowEtaleSiteIso Y p hY hn)
            AddCommGrpCat.{max (u + 1) v}).hom ≫
        (etaleAbelianDirectImageCompIso'.{u, v} ga gb
          (absoluteFrobeniusPow Y p hY n) hcomp).inv := by
  simp only [frobeniusRestrictionUnit]
  rw [← conjugateEquiv_comp _
      (etaleAbelianInverseImageDirectImageAdj.{u, v} (absoluteFrobeniusPow Y p hY n)) _,
    conjugateEquiv_etaleAbelianInverseImageCompIso'_inv,
    conjugateEquiv_etaleSheafInverseImageComparison_hom]

/-- **The coefficient coherence, as an identity of transformations of functors.**  The
identification along `gb` followed by the one along `ga` is the identification of the composite
inverse image with the identity.  Both sides are transformations of left adjoints, and their
conjugates are the two sides of
`Stacks.EtaleCohomology.etaleAbelianDirectImageFrobeniusCoherence`. -/
public theorem frobeniusRestrictionCoeffCoherenceNat :
    Functor.whiskerRight
          (frobeniusRestrictionCoeffFrob.{u, v} pr p hX hn gb m hgb hm)
          (etaleAbelianInverseImage.{u, v} ga) ≫
        (etaleAbelianInverseImageCompIso'.{u, v} ga pr pr hga).inv =
      (Functor.associator (etaleAbelianInverseImage.{u, v} pr)
            (etaleAbelianInverseImage.{u, v} gb)
            (etaleAbelianInverseImage.{u, v} ga)).hom ≫
        Functor.whiskerLeft (etaleAbelianInverseImage.{u, v} pr)
            (frobeniusRestrictionUnit.{u, v} p hY hn ga gb hcomp) ≫
          (Functor.rightUnitor (etaleAbelianInverseImage.{u, v} pr)).hom := by
  refine (conjugateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v} pr)
    (((etaleAbelianInverseImageDirectImageAdj.{u, v} pr).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} gb)).comp
      (etaleAbelianInverseImageDirectImageAdj.{u, v} ga))).injective ?_
  rw [← conjugateEquiv_comp _ ((etaleAbelianInverseImageDirectImageAdj.{u, v} pr).comp
      (etaleAbelianInverseImageDirectImageAdj.{u, v} ga)) _,
    conjugateEquiv_etaleAbelianInverseImageCompIso'_inv,
    conjugateEquiv_whiskerRight (etaleAbelianInverseImageDirectImageAdj.{u, v} pr)
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} pr).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} gb))
      (etaleAbelianInverseImageDirectImageAdj.{u, v} ga) _,
    conjugateEquiv_frobeniusRestrictionCoeffFrob,
    ← conjugateEquiv_comp _ ((etaleAbelianInverseImageDirectImageAdj.{u, v} pr).comp
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} gb).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} ga))) _,
    conjugateEquiv_associator_hom,
    ← conjugateEquiv_comp _
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} pr).comp Adjunction.id) _,
    conjugateEquiv_rightUnitor_hom,
    conjugateEquiv_whiskerLeft Adjunction.id
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} gb).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} ga))
      (etaleAbelianInverseImageDirectImageAdj.{u, v} pr) _,
    conjugateEquiv_frobeniusRestrictionUnit]
  simp only [Category.assoc]
  exact etaleAbelianDirectImageFrobeniusCoherence pr p hX hY hn ga gb hga m hgb hm hcomp

/-- **The coefficient coherence at a single sheaf.**  This is the hypothesis that
`Stacks.EtaleCohomology.etaleCohomologyEndo_comp` asks of the two coefficient
identifications. -/
public theorem frobeniusRestrictionCoeffCoherence
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImage.{u, v} ga).map
          ((frobeniusRestrictionCoeffFrob.{u, v} pr p hX hn gb m hgb hm).app F) ≫
        (etaleAbelianInverseImageCompIso'.{u, v} ga pr pr hga).inv.app F =
      (frobeniusRestrictionUnit.{u, v} p hY hn ga gb hcomp).app
        ((etaleAbelianInverseImage.{u, v} pr).obj F) := by
  have h := congrArg (fun t ↦ NatTrans.app t F)
    (frobeniusRestrictionCoeffCoherenceNat.{u, v} pr p hX hY hn ga gb hga m hgb hm hcomp)
  simpa using h

end Coefficient

/-! ### The coherences in the other order

The two restriction endomorphisms are inverse to each other in both orders, because both
composites `ga ∘ gb` and `gb ∘ ga` are the `n`-fold absolute Frobenius of `Y`.  The coherence
with the roles of `ga` and `gb` exchanged is not an instance of the one above: `ga` is a
morphism over `X` and `gb` is not, so exchanging them moves the Frobenius descent on `X` past
a different comparison.  Everything else is the same, and the geometric content is again
naturality of the `n`-fold absolute Frobenius against `pr`. -/

section Swapped

/-- **The rearrangement of the five-fold composite of the site coherence in the other
order.**  Stated for an arbitrary category: see the implementation notes. -/
public theorem frobeniusChainRearrange' {D : Type*} [Category* D]
    {O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ : D} {x₀ : O₁ ⟶ O₆} {x₁ : O₁ ⟶ O₂} {x₂ : O₂ ⟶ O₃}
    {x₃ : O₃ ⟶ O₄} {x₄ : O₄ ⟶ O₅} {x₅ : O₅ ⟶ O₆} {c₁ : O₆ ⟶ O₇} {c₂ : O₇ ⟶ O₈}
    {u : O₅ ⟶ O₈} {e : O₄ ⟶ O₁} {k : O₁ ⟶ O₈} {e' : O₃ ⟶ O₉} {z : O₉ ⟶ O₁} {e'' : O₉ ⟶ O₁}
    {d : O₂ ⟶ O₁} {l : O₈ ⟶ O₇} {φ : O₁ ⟶ O₁} {ψ : O₈ ⟶ O₈}
    (hA : x₅ ≫ c₁ ≫ c₂ = u) (hB : x₄ ≫ u = e ≫ k) (hC : x₃ ≫ e = e' ≫ z)
    (hD : z ≫ k = e'' ≫ k) (hE : x₂ ≫ e' ≫ e'' = d) (hF : x₁ ≫ d = φ)
    (hG : x₀ ≫ c₁ = k ≫ l) (hH : l ≫ c₂ = ψ) (hI : φ ≫ k = k ≫ ψ) :
    (x₁ ≫ x₂ ≫ x₃ ≫ x₄ ≫ x₅) ≫ c₁ ≫ c₂ = x₀ ≫ c₁ ≫ c₂ := by
  simp only [Category.assoc]
  rw [hA, hB, reassoc_of% hC, hD, reassoc_of% hE, reassoc_of% hF, hI, reassoc_of% hG, hH]

/-- **The site coherence in the other order, read with the inverses of the two Frobenius
identifications.**  Stated for an arbitrary category: see the implementation notes. -/
public theorem invFormRearrange' {D : Type*} [Category* D] {O₁ O₂ O₃ O₄ O₅ O₆ : D}
    {P₁ : O₁ ⟶ O₂} {P₂ : O₂ ⟶ O₃} {P₃ : O₃ ⟶ O₄} {prhi : O₄ ⟶ O₅} {prh : O₅ ⟶ O₄}
    {ehh : O₅ ⟶ O₆} {ehi : O₆ ⟶ O₅} {wh : O₆ ⟶ O₁} {wi : O₁ ⟶ O₆}
    (hcoh : ehh ≫ wh ≫ P₁ ≫ P₂ ≫ P₃ = prh) (hprh : prh ≫ prhi = 𝟙 O₅)
    (hwi : wi ≫ wh = 𝟙 O₁) (heh : ehi ≫ ehh = 𝟙 O₆) :
    P₁ ≫ P₂ ≫ P₃ ≫ prhi = wi ≫ ehi := by
  have h₂ := eq_comp_of_inv_form hcoh hwi heh
  rw [reassoc_of% h₂, hprh, Category.comp_id]

section SwappedSite

variable {X Y : Scheme.{u}} (pr : Y ⟶ X) (p : ℕ) [Fact p.Prime]
  (hX : IsInCharacteristic X p) (hY : IsInCharacteristic Y p) {n : ℕ} (hn : n ≠ 0)
  (ga gb : Y ⟶ Y) (hga : pr = ga ≫ pr) (m : Y ⟶ X) (hgb : m = gb ≫ pr)
  (hm : m = pr ≫ absoluteFrobeniusPow X p hX n)
  (hswap : absoluteFrobeniusPow Y p hY n = gb ≫ ga)

/-- **The site-level Frobenius coherence, with `ga` applied first.** -/
public lemma frobeniusRestrictionSiteCoherence' (U : X.Etale) :
    (absoluteFrobeniusPowEtaleSiteIso Y p hY hn).hom.app
          ((smallEtaleBaseChange pr).obj U) ≫
        (smallEtaleBaseChangeComp' gb ga (absoluteFrobeniusPow Y p hY n) hswap).hom.app
          ((smallEtaleBaseChange pr).obj U) ≫
        (smallEtaleBaseChange gb).map ((smallEtaleBaseChangeComp' ga pr pr hga).inv.app U) ≫
        (smallEtaleBaseChangeComp' gb pr m hgb).inv.app U ≫
        (smallEtaleBaseChangeComp' pr (absoluteFrobeniusPow X p hX n) m hm).hom.app U =
      (smallEtaleBaseChange pr).map
        ((absoluteFrobeniusPowEtaleSiteIso X p hX hn).hom.app U) :=
  smallEtaleBaseChangeDoubleHomExt pr (absoluteFrobeniusPow X p hX n)
    (frobeniusChainRearrange'
      (smallEtaleBaseChangeComp'_fst_fst pr (absoluteFrobeniusPow X p hX n) m hm U)
      (smallEtaleBaseChangeComp'_inv_fst gb pr m hgb U)
      (smallEtaleBaseChange_map_left_fst gb
        ((smallEtaleBaseChangeComp' ga pr pr hga).inv.app U))
      (smallEtaleBaseChangeComp'_inv_fst ga pr pr hga U)
      (smallEtaleBaseChangeComp'_fst_fst gb ga (absoluteFrobeniusPow Y p hY n) hswap
        ((smallEtaleBaseChange pr).obj U))
      (absoluteFrobeniusPowEtaleSiteIso_hom_app_left_fst Y p hY hn
        ((smallEtaleBaseChange pr).obj U))
      (smallEtaleBaseChange_map_left_fst pr
        ((absoluteFrobeniusPowEtaleSiteIso X p hX hn).hom.app U))
      (absoluteFrobeniusPowEtaleSiteIso_hom_app_left_fst X p hX hn U)
      (absoluteFrobeniusPow_naturality (pullback.fst U.hom pr) p _ _ n))

/-- **The site-level Frobenius coherence in the other order, in inverse form.** -/
public lemma frobeniusRestrictionSiteCoherence'_inv (U : X.Etale) :
    (smallEtaleBaseChange gb).map ((smallEtaleBaseChangeComp' ga pr pr hga).inv.app U) ≫
        (smallEtaleBaseChangeComp' gb pr m hgb).inv.app U ≫
        (smallEtaleBaseChangeComp' pr (absoluteFrobeniusPow X p hX n) m hm).hom.app U ≫
        (smallEtaleBaseChange pr).map
          ((absoluteFrobeniusPowEtaleSiteIso X p hX hn).inv.app U) =
      (smallEtaleBaseChangeComp' gb ga (absoluteFrobeniusPow Y p hY n) hswap).inv.app
          ((smallEtaleBaseChange pr).obj U) ≫
        (absoluteFrobeniusPowEtaleSiteIso Y p hY hn).inv.app
          ((smallEtaleBaseChange pr).obj U) :=
  invFormRearrange'
    (frobeniusRestrictionSiteCoherence' pr p hX hY hn ga gb hga m hgb hm hswap U)
    (((smallEtaleBaseChange pr).mapIso
      ((absoluteFrobeniusPowEtaleSiteIso X p hX hn).app U)).hom_inv_id)
    ((smallEtaleBaseChangeComp' gb ga (absoluteFrobeniusPow Y p hY n) hswap).inv_hom_id_app
      ((smallEtaleBaseChange pr).obj U))
    ((absoluteFrobeniusPowEtaleSiteIso Y p hY hn).inv_hom_id_app
      ((smallEtaleBaseChange pr).obj U))

/-- **The Frobenius coherence between direct images, in the other order.** -/
public theorem etaleAbelianDirectImageFrobeniusCoherence' :
    ((Functor.rightUnitor (etaleAbelianDirectImage.{u, v} pr)).inv ≫
          Functor.whiskerLeft (etaleAbelianDirectImage.{u, v} pr)
              (etaleSheafPushforwardComparison X (absoluteFrobeniusPow X p hX n)
                (absoluteFrobeniusPowEtaleSiteIso X p hX hn)
                AddCommGrpCat.{max (u + 1) v}).hom ≫
            (etaleAbelianDirectImageCompIso'.{u, v} pr
                (absoluteFrobeniusPow X p hX n) m hm).hom ≫
              (etaleAbelianDirectImageCompIso'.{u, v} gb pr m hgb).inv) ≫
        Functor.whiskerLeft (etaleAbelianDirectImage.{u, v} gb)
          (etaleAbelianDirectImageCompIso'.{u, v} ga pr pr hga).inv =
      (Functor.leftUnitor (etaleAbelianDirectImage.{u, v} pr)).inv ≫
        Functor.whiskerRight
            ((etaleSheafPushforwardComparison Y (absoluteFrobeniusPow Y p hY n)
                  (absoluteFrobeniusPowEtaleSiteIso Y p hY hn)
                  AddCommGrpCat.{max (u + 1) v}).hom ≫
              (etaleAbelianDirectImageCompIso'.{u, v} gb ga
                (absoluteFrobeniusPow Y p hY n) hswap).inv)
            (etaleAbelianDirectImage.{u, v} pr) ≫
          (Functor.associator (etaleAbelianDirectImage.{u, v} gb)
            (etaleAbelianDirectImage.{u, v} ga) (etaleAbelianDirectImage.{u, v} pr)).hom := by
  refine NatTrans.ext (funext fun G ↦ Sheaf.hom_ext (NatTrans.ext (funext fun U ↦ ?_)))
  obtain ⟨U⟩ := U
  have h := congrArg (fun z ↦ G.obj.map (Quiver.Hom.op z))
    (frobeniusRestrictionSiteCoherence'_inv pr p hX hY hn ga gb hga m hgb hm hswap U)
  simp only [op_comp, Functor.map_comp, Category.assoc] at h
  simp only [sheafCompHomApp, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.leftUnitor_inv_app,
    Functor.rightUnitor_inv_app, etaleAbelianDirectImageCompIso'_inv_app_hom_app,
    etaleAbelianDirectImageCompIso'_hom_app_hom_app,
    etaleSheafPushforwardComparison_hom_app_hom_app, opEqHomOp, directImageObjMap,
    directImageMapHomApp, Category.id_comp, Category.comp_id, Category.assoc]
  exact h

variable [HasSheafify X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
  [HasSheafify Y.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}]
variable [∀ F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
    (smallEtaleBaseChange (absoluteFrobeniusPow X p hX n)).op.HasLeftKanExtension F]
  [∀ F : Y.Etaleᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v},
    (smallEtaleBaseChange (absoluteFrobeniusPow Y p hY n)).op.HasLeftKanExtension F]

/-- **The coefficient coherence in the other order, as an identity of transformations of
functors.** -/
public theorem frobeniusRestrictionCoeffCoherenceNat' :
    Functor.whiskerRight (etaleAbelianInverseImageCompIso'.{u, v} ga pr pr hga).inv
          (etaleAbelianInverseImage.{u, v} gb) ≫
        frobeniusRestrictionCoeffFrob.{u, v} pr p hX hn gb m hgb hm =
      (Functor.associator (etaleAbelianInverseImage.{u, v} pr)
            (etaleAbelianInverseImage.{u, v} ga)
            (etaleAbelianInverseImage.{u, v} gb)).hom ≫
        Functor.whiskerLeft (etaleAbelianInverseImage.{u, v} pr)
            (frobeniusRestrictionUnit.{u, v} p hY hn gb ga hswap) ≫
          (Functor.rightUnitor (etaleAbelianInverseImage.{u, v} pr)).hom := by
  refine (conjugateEquiv (etaleAbelianInverseImageDirectImageAdj.{u, v} pr)
    (((etaleAbelianInverseImageDirectImageAdj.{u, v} pr).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} ga)).comp
      (etaleAbelianInverseImageDirectImageAdj.{u, v} gb))).injective ?_
  rw [← conjugateEquiv_comp _ ((etaleAbelianInverseImageDirectImageAdj.{u, v} pr).comp
      (etaleAbelianInverseImageDirectImageAdj.{u, v} gb)) _,
    conjugateEquiv_frobeniusRestrictionCoeffFrob,
    conjugateEquiv_whiskerRight (etaleAbelianInverseImageDirectImageAdj.{u, v} pr)
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} pr).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} ga))
      (etaleAbelianInverseImageDirectImageAdj.{u, v} gb) _,
    conjugateEquiv_etaleAbelianInverseImageCompIso'_inv,
    ← conjugateEquiv_comp _ ((etaleAbelianInverseImageDirectImageAdj.{u, v} pr).comp
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} ga).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} gb))) _,
    conjugateEquiv_associator_hom,
    ← conjugateEquiv_comp _
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} pr).comp Adjunction.id) _,
    conjugateEquiv_rightUnitor_hom,
    conjugateEquiv_whiskerLeft Adjunction.id
      ((etaleAbelianInverseImageDirectImageAdj.{u, v} ga).comp
        (etaleAbelianInverseImageDirectImageAdj.{u, v} gb))
      (etaleAbelianInverseImageDirectImageAdj.{u, v} pr) _,
    conjugateEquiv_frobeniusRestrictionUnit]
  simp only [Category.assoc]
  exact etaleAbelianDirectImageFrobeniusCoherence' pr p hX hY hn ga gb hga m hgb hm hswap

/-- **The coefficient coherence in the other order, at a single sheaf.** -/
public theorem frobeniusRestrictionCoeffCoherence'
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{max (u + 1) v}) :
    (etaleAbelianInverseImage.{u, v} gb).map
          ((etaleAbelianInverseImageCompIso'.{u, v} ga pr pr hga).inv.app F) ≫
        (frobeniusRestrictionCoeffFrob.{u, v} pr p hX hn gb m hgb hm).app F =
      (frobeniusRestrictionUnit.{u, v} p hY hn gb ga hswap).app
        ((etaleAbelianInverseImage.{u, v} pr).obj F) := by
  have h := congrArg (fun t ↦ NatTrans.app t F)
    (frobeniusRestrictionCoeffCoherenceNat'.{u, v} pr p hX hY hn ga gb hga m hgb hm hswap)
  simpa using h

end SwappedSite

end Swapped

end Stacks.EtaleCohomology

end
