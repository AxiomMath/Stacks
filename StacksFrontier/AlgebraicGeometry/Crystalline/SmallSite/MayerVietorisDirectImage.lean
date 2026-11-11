module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedPlusInjectiveTriangle
public import StacksFrontier.Algebra.Homology.RightDerivedBiprod
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.CrisModuleDirectImageOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.MayerVietorisSequence

/-!
# Mayer--Vietoris for the higher direct images `Rf_{cris, *}`

This file proves the remark of [Stacks, Tag 07ML]: in the situation of [Stacks, Tag 07MJ], let
`X = X' ∪ X''` be an open covering with `X''' = X' ∩ X''`, let `f'`, `f''`, `f'''` be the
restrictions of `f` to `X'`, `X''`, `X'''` and `F'`, `F''`, `F'''` the restrictions of an
`𝒪_{X/S}`-module `F` to the crystalline sites of `X'`, `X''`, `X'''`.  Then there is a
distinguished triangle

`Rf_{cris, *}F ⟶ Rf'_{cris, *}F' ⊕ Rf''_{cris, *}F'' ⟶ Rf'''_{cris, *}F''' ⟶ Rf_{cris, *}F[1]`

in `D(𝒪_{X'/S'})`.

## The objects

* `f_{cris, *} : Mod(𝒪_{X/S}) ⥤ Mod(𝒪_{X'/S'})` is `...SmallSite.crisModuleDirectImage`, and
  `Rf_{cris, *}` is its right derived functor on bounded below derived categories,
  `derivedCrisModuleDirectImage`; the object `Rf_{cris, *}F` is the value at `F` placed in degree
  zero, read in the unbounded derived category `D(𝒪_{X'/S'})` of sheaves of
  `𝒪_{X'/S'}`-modules through the fully faithful inclusion of `D⁺`.
* The restriction of `f` to an open `V` of `X` is the morphism of situations `V/S ⟶ X'/S'` given by
  `V ⟶ X ⟶ X'` over the same morphism of divided power bases `S ⟶ S'`, where `V/S` is
  `Crystalline.GlobalCrystallineSituation.openSubspace S V`, whose crystalline site is
  `Cris(V/S)`; the restriction of `F` to it is `...SmallSite.openSubspaceModuleRestriction`.

## The proof

The hint of the source — that `Cris(X'/S)`, `Cris(X''/S)` and `Cris(X'''/S)` are localizations of
`Cris(X/S)` at open subobjects of the final sheaf, the last the intersection of the first two — is
used in the following form.  Restriction to `Cris(V/S)` has a right adjoint `j_{V, *}`
(`...SmallSite.openSubspaceRestrictionAdjunction`), and

1. the Mayer--Vietoris sequence `0 ⟶ F ⟶ j_{X', *}F' ⊕ j_{X'', *}F'' ⟶ j_{X''', *}F''' ⟶ 0` is
   short exact (`...SmallSite.mayerVietorisShortComplex_shortExact`), hence split when `F` is
   injective, so `f_{cris, *}` keeps it short exact;
2. `f'_{cris, *} = f_{cris, *} ∘ j_{X', *}`, and similarly for `X''`, `X'''`
   (`...SmallSite.crisModuleDirectImageOpenSubspaceIso`);
3. restriction to `Cris(V/S)` is exact and preserves injective objects
   (`...SmallSite.openSubspaceModuleRestriction_preservesInjectiveObjects`), so restricting an
   injective resolution of `F` computes `Rf'_{cris, *}F'`.

Applying the three functors `f_{cris, *}`, `f'_{cris, *}(-|_{X'}) ⊕ f''_{cris, *}(-|_{X''})` and
`f'''_{cris, *}(-|_{X'''})` to an injective resolution of `F` therefore gives a short exact
sequence of complexes, whose distinguished triangle
(`CategoryTheory.triangleOfInjectiveCochainComplex_distinguished`) has the three derived direct
images as its vertices.

## Main definitions

* `derivedCrisModuleDirectImage` — `Rf_{cris, *} : D⁺(𝒪_{X/S}) ⥤ D⁺(𝒪_{X'/S'})`.
* `mayerVietorisDirectImageComplex` — the short complex of functors
  `f_{cris, *} ⟶ f_{cris, *}j_{X', *}(-|_{X'}) ⊕ f_{cris, *}j_{X'', *}(-|_{X''}) ⟶
  f_{cris, *}j_{X''', *}(-|_{X'''})`.

## Main results

* `exists_distinguished_triangle_derivedCrisModuleDirectImage` — **[Stacks, Tag 07ML]**.

## References

* [Stacks Project, Tag 07ML](https://stacks.math.columbia.edu/tag/07ML)
* [Stacks Project, Tag 07MJ](https://stacks.math.columbia.edu/tag/07MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
  Opposite

universe w w' u

noncomputable section

attribute [local instance] preservesBinaryBiproducts_of_preservesBiproducts

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S S' : GlobalCrystallineSituation.{u}} {fS : S.S ⟶ S'.S} {fX : S.X ⟶ S'.X}
  (hf : S.toClosedFiber ≫ DividedPowerScheme.closedFiberMap fS = fX ≫ S'.toClosedFiber)

/-- **The derived direct image `Rf_{cris, *} : D⁺(𝒪_{X/S}) ⥤ D⁺(𝒪_{X'/S'})`** of sheaves of
modules, the right derived functor of `...SmallSite.crisModuleDirectImage` on bounded below
derived categories.  It exists because sheaves of `𝒪_{X/S}`-modules form an abelian category with
enough injectives, `...SmallSite.instEnoughInjectivesModuleSheaf`. -/
def derivedCrisModuleDirectImage [HasDerivedCategory.{w} (ModuleSheaf S)]
    [HasDerivedCategory.{w'} (ModuleSheaf S')] :
    DerivedCategory.Plus (ModuleSheaf S) ⥤ DerivedCategory.Plus (ModuleSheaf S') :=
  (crisModuleDirectImage S S' fS fX hf).rightDerivedFunctorPlus

/-! ### The short complex of functors -/

/-- The direct image of `F ↦ j_{V, *}(F|_V)`: `F ↦ f_{cris, *}j_{V, *}(F|_V)`. -/
abbrev mayerVietorisDirectImageTerm (V : S.X.Opens) : ModuleSheaf S ⥤ ModuleSheaf S' :=
  openSubspaceRestrictModule V ⋙ crisModuleDirectImage S S' fS fX hf

variable (V₁ V₂ : S.X.Opens)

/-- **The Mayer--Vietoris short complex of direct images**
`f_{cris, *} ⟶ f_{cris, *}j_{X', *}(-|_{X'}) ⊕ f_{cris, *}j_{X'', *}(-|_{X''}) ⟶
f_{cris, *}j_{X''', *}(-|_{X'''})`, a short complex of functors
`Mod(𝒪_{X/S}) ⥤ Mod(𝒪_{X'/S'})`: the direct image of the Mayer--Vietoris sequence. -/
def mayerVietorisDirectImageComplex :
    ShortComplex (ModuleSheaf S ⥤ ModuleSheaf S') :=
  ShortComplex.mk
    (biprod.lift
      (Functor.whiskerRight (openSubspaceRestrictModuleUnit V₁)
        (crisModuleDirectImage S S' fS fX hf))
      (Functor.whiskerRight (openSubspaceRestrictModuleUnit V₂)
        (crisModuleDirectImage S S' fS fX hf)) :
      crisModuleDirectImage S S' fS fX hf ⟶
        mayerVietorisDirectImageTerm hf V₁ ⊞ mayerVietorisDirectImageTerm hf V₂)
    (biprod.desc
      (Functor.whiskerRight (openSubspaceRestrictModuleLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁))
        (crisModuleDirectImage S S' fS fX hf))
      (-Functor.whiskerRight (openSubspaceRestrictModuleLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂))
        (crisModuleDirectImage S S' fS fX hf)) :
      mayerVietorisDirectImageTerm hf V₁ ⊞ mayerVietorisDirectImageTerm hf V₂ ⟶
        mayerVietorisDirectImageTerm hf (V₁ ⊓ V₂))
    (by
      rw [biprod.lift_desc, Preadditive.comp_neg, ← Functor.whiskerRight_comp,
        ← Functor.whiskerRight_comp, openSubspaceRestrictModuleUnit_comp_LE,
        openSubspaceRestrictModuleUnit_comp_LE, add_neg_cancel])

theorem mayerVietorisDirectImageComplex_f_app (M : ModuleSheaf S) :
    (biprod.lift
      (Functor.whiskerRight (openSubspaceRestrictModuleUnit V₁)
        (crisModuleDirectImage S S' fS fX hf))
      (Functor.whiskerRight (openSubspaceRestrictModuleUnit V₂)
        (crisModuleDirectImage S S' fS fX hf)) :
      crisModuleDirectImage S S' fS fX hf ⟶
        mayerVietorisDirectImageTerm hf V₁ ⊞ mayerVietorisDirectImageTerm hf V₂).app M ≫
        (Stacks.RightDerivedPlusTriangle.biprodObjIso (mayerVietorisDirectImageTerm hf V₁)
          (mayerVietorisDirectImageTerm hf V₂) M).hom =
      (crisModuleDirectImage S S' fS fX hf).map
          (biprod.lift ((openSubspaceRestrictModuleUnit V₁).app M)
            ((openSubspaceRestrictModuleUnit V₂).app M)) ≫
        ((crisModuleDirectImage S S' fS fX hf).mapBiprod _ _).hom := by
  rw [Functor.mapBiprod_hom]
  apply biprod.hom_ext
  · simp only [Stacks.RightDerivedPlusTriangle.biprodObjIso, Category.assoc, biprod.lift_fst]
    rw [← NatTrans.comp_app, biprod.lift_fst, Functor.whiskerRight_app]
    exact ((crisModuleDirectImage S S' fS fX hf).congr_map (biprod.lift_fst _ _)).symm.trans
      (((crisModuleDirectImage S S' fS fX hf).map_comp _ _).trans
        (congrArg (fun k ↦ (crisModuleDirectImage S S' fS fX hf).map _ ≫ k)
          (biprod.lift_fst _ _).symm))
  · simp only [Stacks.RightDerivedPlusTriangle.biprodObjIso, Category.assoc, biprod.lift_snd]
    rw [← NatTrans.comp_app, biprod.lift_snd, Functor.whiskerRight_app]
    exact ((crisModuleDirectImage S S' fS fX hf).congr_map (biprod.lift_snd _ _)).symm.trans
      (((crisModuleDirectImage S S' fS fX hf).map_comp _ _).trans
        (congrArg (fun k ↦ (crisModuleDirectImage S S' fS fX hf).map _ ≫ k)
          (biprod.lift_snd _ _).symm))

theorem mayerVietorisDirectImageComplex_g_app (M : ModuleSheaf S) :
    ((crisModuleDirectImage S S' fS fX hf).mapBiprod _ _).inv ≫
        (crisModuleDirectImage S S' fS fX hf).map
          (biprod.desc ((openSubspaceRestrictModuleLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁)).app M)
            (-(openSubspaceRestrictModuleLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂)).app M)) =
      (Stacks.RightDerivedPlusTriangle.biprodObjIso (mayerVietorisDirectImageTerm hf V₁)
          (mayerVietorisDirectImageTerm hf V₂) M).inv ≫
        (biprod.desc
          (Functor.whiskerRight (openSubspaceRestrictModuleLE (inf_le_left : V₁ ⊓ V₂ ≤ V₁))
            (crisModuleDirectImage S S' fS fX hf))
          (-Functor.whiskerRight (openSubspaceRestrictModuleLE (inf_le_right : V₁ ⊓ V₂ ≤ V₂))
            (crisModuleDirectImage S S' fS fX hf)) :
          mayerVietorisDirectImageTerm hf V₁ ⊞ mayerVietorisDirectImageTerm hf V₂ ⟶
            mayerVietorisDirectImageTerm hf (V₁ ⊓ V₂)).app M := by
  rw [Functor.mapBiprod_inv]
  apply biprod.hom_ext'
  · simp only [Stacks.RightDerivedPlusTriangle.biprodObjIso, biprod.inl_desc_assoc]
    rw [← Functor.map_comp, ← NatTrans.comp_app, biprod.inl_desc, biprod.inl_desc,
      Functor.whiskerRight_app]
  · simp only [Stacks.RightDerivedPlusTriangle.biprodObjIso, biprod.inr_desc_assoc]
    rw [← Functor.map_comp, ← NatTrans.comp_app, biprod.inr_desc, biprod.inr_desc,
      Functor.map_neg, NatTrans.app_neg, Functor.whiskerRight_app]

/-- The value of the Mayer--Vietoris short complex of direct images at a module `M` is the direct
image of the Mayer--Vietoris sequence of `M`. -/
def mayerVietorisDirectImageComplexAppIso (M : ModuleSheaf S) :
    (mayerVietorisShortComplex V₁ V₂ M).map (crisModuleDirectImage S S' fS fX hf) ≅
      NatTrans.appShortComplex (mayerVietorisDirectImageComplex hf V₁ V₂).f
        (mayerVietorisDirectImageComplex hf V₁ V₂).g (mayerVietorisDirectImageComplex hf V₁ V₂).zero
        M :=
  ShortComplex.isoMk (Iso.refl _)
    ((crisModuleDirectImage S S' fS fX hf).mapBiprod _ _ ≪≫
      (Stacks.RightDerivedPlusTriangle.biprodObjIso (mayerVietorisDirectImageTerm hf V₁)
        (mayerVietorisDirectImageTerm hf V₂) M).symm)
    (Iso.refl _)
    ((Category.id_comp _).trans
      (((Iso.eq_comp_inv _).2 (mayerVietorisDirectImageComplex_f_app hf V₁ V₂ M)).trans
        (Category.assoc _ _ _)))
    (((Category.assoc _ _ _).trans
      ((Iso.inv_comp_eq _).1 (mayerVietorisDirectImageComplex_g_app hf V₁ V₂ M)).symm).trans
        (Category.comp_id _).symm)

/-- `F ↦ j_{V, *}(F|_V)` is additive: it acts on sections by restriction. -/
instance additive_openSubspaceRestrictModule (V : S.X.Opens) :
    (openSubspaceRestrictModule V).Additive where
  map_add := by intros; rfl

/-- The first term of the Mayer--Vietoris short complex of direct images is additive. -/
instance additive_mayerVietorisDirectImageComplex_X₁ :
    (mayerVietorisDirectImageComplex hf V₁ V₂).X₁.Additive :=
  inferInstanceAs (crisModuleDirectImage S S' fS fX hf).Additive

/-- The middle term of the Mayer--Vietoris short complex of direct images is additive. -/
instance additive_mayerVietorisDirectImageComplex_X₂ :
    (mayerVietorisDirectImageComplex hf V₁ V₂).X₂.Additive :=
  inferInstanceAs (mayerVietorisDirectImageTerm hf V₁ ⊞ mayerVietorisDirectImageTerm hf V₂).Additive

/-- The last term of the Mayer--Vietoris short complex of direct images is additive. -/
instance additive_mayerVietorisDirectImageComplex_X₃ :
    (mayerVietorisDirectImageComplex hf V₁ V₂).X₃.Additive :=
  inferInstanceAs (mayerVietorisDirectImageTerm hf (V₁ ⊓ V₂)).Additive

variable {V₁ V₂} in
/-- **The Mayer--Vietoris short complex of direct images is short exact at every injective
module**: the Mayer--Vietoris sequence of an injective module is short exact
(`mayerVietorisShortComplex_shortExact`) with injective first term, hence split, and a split short
exact sequence stays short exact under the additive functor `f_{cris, *}`. -/
theorem mayerVietorisDirectImageComplex_shortExact (hV : V₁ ⊔ V₂ = ⊤) (I : ModuleSheaf S)
    (hI : Injective I) :
    (NatTrans.appShortComplex (mayerVietorisDirectImageComplex hf V₁ V₂).f
      (mayerVietorisDirectImageComplex hf V₁ V₂).g
      (mayerVietorisDirectImageComplex hf V₁ V₂).zero I).ShortExact := by
  have h := mayerVietorisShortComplex_shortExact hV I
  have : Injective (mayerVietorisShortComplex V₁ V₂ I).X₁ := hI
  exact ShortComplex.shortExact_of_iso (mayerVietorisDirectImageComplexAppIso hf V₁ V₂ I)
    (h.splittingOfInjective.map (crisModuleDirectImage S S' fS fX hf)).shortExact

/-- **`f_{cris, *}j_{V, *}(F|_V) ≅ (f|_V)_{cris, *}(F|_V)`**, naturally in `F`. -/
def mayerVietorisDirectImageTermIso (V : S.X.Opens) :
    mayerVietorisDirectImageTerm hf V ≅
      openSubspaceModuleRestriction S V ⋙
        crisModuleDirectImage (openSubspace S V) S' fS (V.ι ≫ fX)
          (openSubspaceRestrictCondition hf V) :=
  Functor.isoWhiskerRight (openSubspaceRestrictModuleIso V).symm _ ≪≫ Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (crisModuleDirectImageOpenSubspaceIso hf V).symm

section Derived

variable [HasDerivedCategory.{w} (ModuleSheaf S)]
  [∀ V : S.X.Opens, HasDerivedCategory.{w} (ModuleSheaf (openSubspace S V))]
  [HasDerivedCategory.{w'} (ModuleSheaf S')]

/-- The value of `f_{cris, *}j_{V, *}(-|_V)` on an injective resolution of `F` computes
`R(f|_V)_{cris, *}(F|_V)`. -/
def mayerVietorisDirectImageTermQIso (V : S.X.Opens)
    (J : CochainComplex.Plus (InjectiveObject (ModuleSheaf S))) {F : ModuleSheaf S}
    (e : DerivedCategory.Plus.Q.obj ((InjectiveObject.ι _).mapCochainComplexPlus.obj J) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj F) :
    DerivedCategory.Plus.ι.obj
        ((derivedCrisModuleDirectImage (openSubspaceRestrictCondition hf V)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((openSubspaceModuleRestriction S V).obj F))) ≅
      DerivedCategory.Q.obj (((mayerVietorisDirectImageTerm hf V).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (((InjectiveObject.ι _).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj J.obj)) :=
  (Stacks.RightDerivedPlusTriangle.qIsoRightDerivedFunctorPlusOfExact
      (openSubspaceModuleRestriction S V)
      (crisModuleDirectImage (openSubspace S V) S' fS (V.ι ≫ fX)
        (openSubspaceRestrictCondition hf V)) J e).symm ≪≫
    DerivedCategory.Q.mapIso
      ((Functor.mapHomologicalComplexCompIso (mayerVietorisDirectImageTermIso hf V).symm _).app _)

variable {V₁ V₂} in
/-- **Stacks Project, Tag 07ML (Mayer--Vietoris for `Rf_{cris, *}`).**  In the situation of
[Stacks, Tag 07MJ] — a morphism `f : X ⟶ X'` over a morphism of divided power schemes
`(S, I, γ) ⟶ (S', I', γ')` over `ℤ_(p)`, `p` locally nilpotent on `X` and `X'` — let
`X = X₁ ∪ X₂` be an open covering (`V₁ ⊔ V₂ = ⊤`) with `X₁₂ = X₁ ∩ X₂`, and let `F` be an
`𝒪_{X/S}`-module on `Cris(X/S)`.  Writing `f₁`, `f₂`, `f₁₂` for the restrictions of `f` to `X₁`,
`X₂`, `X₁₂` (morphisms of situations `X₁/S ⟶ X'/S'` etc. over the same `S ⟶ S'`) and `F₁`,
`F₂`, `F₁₂` for the restrictions of `F` to the crystalline sites `Cris(X₁/S)`, `Cris(X₂/S)`,
`Cris(X₁₂/S)`, there is a distinguished triangle

`Rf_{cris, *}F ⟶ Rf₁_{cris, *}F₁ ⊕ Rf₂_{cris, *}F₂ ⟶ Rf₁₂_{cris, *}F₁₂ ⟶ Rf_{cris, *}F[1]`

in `D(𝒪_{X'/S'})`, the derived category of sheaves of `𝒪_{X'/S'}`-modules on `Cris(X'/S')`.
(The source names the opens `X'`, `X''`, `X'''`, the target of `f` also being `X'`.)

Here `Rf_{cris, *}` is `derivedCrisModuleDirectImage`, the right derived functor of the
module-valued direct image `...SmallSite.crisModuleDirectImage` on `D⁺`, applied to `F` in degree
zero and read in `D(𝒪_{X'/S'})` through `DerivedCategory.Plus.ι`; `X₁/S` is
`Crystalline.GlobalCrystallineSituation.openSubspace S V₁`, `f₁` is `V₁.ι ≫ fX` over `fS`, and
`F₁` is `...SmallSite.openSubspaceModuleRestriction S V₁` of `F`.  The statement holds for every
choice of the derived category models. -/
@[stacks 07ML "the distinguished triangle Rf_{cris,*}F → Rf'_{cris,*}F' ⊕ Rf''_{cris,*}F'' → \
  Rf'''_{cris,*}F''' → Rf_{cris,*}F[1] in D(O_{X'/S'}), for an open covering X = X' ∪ X'' in the \
  situation of 07MJ, with Rf_{cris,*} the right derived functor of the module-valued direct image \
  and F', F'', F''' the restrictions of the O_{X/S}-module F to Cris(X'/S), Cris(X''/S), \
  Cris(X'''/S)"]
theorem exists_distinguished_triangle_derivedCrisModuleDirectImage (hV : V₁ ⊔ V₂ = ⊤)
    (F : ModuleSheaf S) :
    ∃ (a : DerivedCategory.Plus.ι.obj ((derivedCrisModuleDirectImage hf).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) ⟶
        DerivedCategory.Plus.ι.obj ((derivedCrisModuleDirectImage
          (openSubspaceRestrictCondition hf V₁)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((openSubspaceModuleRestriction S V₁).obj F))) ⊞
        DerivedCategory.Plus.ι.obj ((derivedCrisModuleDirectImage
          (openSubspaceRestrictCondition hf V₂)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((openSubspaceModuleRestriction S V₂).obj F))))
      (b : DerivedCategory.Plus.ι.obj ((derivedCrisModuleDirectImage
          (openSubspaceRestrictCondition hf V₁)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((openSubspaceModuleRestriction S V₁).obj F))) ⊞
        DerivedCategory.Plus.ι.obj ((derivedCrisModuleDirectImage
          (openSubspaceRestrictCondition hf V₂)).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((openSubspaceModuleRestriction S V₂).obj F))) ⟶
        DerivedCategory.Plus.ι.obj ((derivedCrisModuleDirectImage
          (openSubspaceRestrictCondition hf (V₁ ⊓ V₂))).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((openSubspaceModuleRestriction S (V₁ ⊓ V₂)).obj F))))
      (c : DerivedCategory.Plus.ι.obj ((derivedCrisModuleDirectImage
          (openSubspaceRestrictCondition hf (V₁ ⊓ V₂))).obj
            ((DerivedCategory.Plus.singleFunctor _ 0).obj
              ((openSubspaceModuleRestriction S (V₁ ⊓ V₂)).obj F))) ⟶
        (DerivedCategory.Plus.ι.obj ((derivedCrisModuleDirectImage hf).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))⟦(1 : ℤ)⟧),
      Triangle.mk a b c ∈ distTriang (DerivedCategory (ModuleSheaf S')) := by
  obtain ⟨J, -, ⟨e⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso
    ((DerivedCategory.Plus.singleFunctor (ModuleSheaf S) 0).obj F) 0
  let K := ((InjectiveObject.ι (ModuleSheaf S)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    J.obj
  have hK : ∀ n, Injective (K.X n) := fun n ↦ (J.obj.X n).property
  have hE := mayerVietorisDirectImageComplex_shortExact hf hV
  exact Stacks.RightDerivedPlusTriangle.exists_distinguished_of_iso
    (triangleOfInjectiveCochainComplex (mayerVietorisDirectImageComplex hf V₁ V₂).f
      (mayerVietorisDirectImageComplex hf V₁ V₂).g (mayerVietorisDirectImageComplex hf V₁ V₂).zero
      hE K hK)
    (triangleOfInjectiveCochainComplex_distinguished _ _ _ hE K hK)
    (Stacks.RightDerivedPlusTriangle.qIsoRightDerivedFunctorPlus
      (crisModuleDirectImage S S' fS fX hf) J e).symm
    (biprod.mapIso (mayerVietorisDirectImageTermQIso hf V₁ J e)
        (mayerVietorisDirectImageTermQIso hf V₂ J e) ≪≫
      (DerivedCategory.Q.mapBiprod _ _).symm ≪≫
      DerivedCategory.Q.mapIso (Stacks.RightDerivedPlusTriangle.mapHomologicalComplexBiprodIso
        (mayerVietorisDirectImageTerm hf V₁) (mayerVietorisDirectImageTerm hf V₂) _ K).symm)
    (mayerVietorisDirectImageTermQIso hf (V₁ ⊓ V₂) J e)

end Derived

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
