module

public import StacksFrontier.AlgebraicGeometry.BaseChange.FlatSource.RestrictScalarsPasting
public import StacksFrontier.AlgebraicGeometry.DeRham.DeRhamComplexBaseChangeGraded
public import StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothDeRhamPerfect
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Algebra.Homology.StupidTruncationFunctorial
public import StacksFrontier.CategoryTheory.Triangulated.ComparisonFiveLemma
import StacksCore.Tactic.StacksAttribute

/-!
# Base change for the derived direct image of the relative de Rham complex

For a proper smooth morphism `f : X ⟶ S` and a cartesian square with base change `g : S' ⟶ S`,
the derived base change map for `Rf_*Ω^•_{X/S}`, the derived direct image of the relative de
Rham complex along `(X, f^{-1}𝒪_S) ⟶ S`, followed by the canonical map of de Rham complexes, is
an isomorphism: `isIso_derivedBaseChangeMap_deRhamComplex`, the base change assertion of
[Stacks, Tag 0FM0] for the de Rham complex.

The proof follows the source. The question is local on `S'`; over an affine open of `S'` mapping
into an affine open of `S` the forms of high degree vanish, and the stupid filtration of the de
Rham complex is descended with the five lemma for comparisons
(`Stacks.CategoryTheory.ComparisonFiveLemma`). The graded pieces are `Ω^p_{X/S}[-p]` read as
`f^{-1}𝒪_S`-modules, and base change for them reduces, through the exact pushforward
`(X, 𝒪_X) ⟶ (X, f^{-1}𝒪_S)`, to base change for `Rf_*Ω^p_{X/S}`
(`isIso_derivedBaseChangeMap_forms`).
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Stacks.Modules (toShHom_comm)
open TopologicalSpace RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces Stacks.Cohomology.DerivedBaseChange
open Stacks.AlgebraicGeometry.FlatSourceBaseChange Stacks.DeRhamDirectImage Stacks.DeRhamBaseChange

universe u

namespace AlgebraicGeometry.ProperSmoothDeRham

noncomputable section

attribute [local instance 10000] HasDerivedCategory.standard

variable {X X' S S' : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ S') (f : X ⟶ S) (g : S' ⟶ S)
  (w : g' ≫ f = f' ≫ g)

/-- The canonical map `(g')^*(Ω^p_{X/S}[-p]) ⟶ Ω^p_{X'/S'}[-p]` of complexes placed in degree `p`
attached to a commutative square of schemes. -/
def formsSingleMap (p : ℕ) :
    ((modulePullback g'.toLRSHom.toShHom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ) (p : ℤ)).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) ⟶
      (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
          (ComplexShape.up ℤ) (p : ℤ)).obj (Scheme.Hom.relativeDifferentialForms f' (p : ℤ)) :=
  (HomologicalComplex.singleMapHomologicalComplex (modulePullback g'.toLRSHom.toShHom)
      (ComplexShape.up ℤ) (p : ℤ)).hom.app (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) ≫
    (HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
      (ComplexShape.up ℤ) (p : ℤ)).map (Scheme.Hom.relativeDifferentialFormsMap g' f f' g w (p : ℤ))

variable {g' f' f g}

/-- For a cartesian square with `f` smooth the canonical map of `formsSingleMap` is invertible
(Stacks 0FL5). -/
theorem isIso_formsSingleMap (hsq : IsPullback g' f' f g) [Smooth f] (p : ℕ) :
    IsIso (formsSingleMap g' f' f g hsq.w p) := by
  have h₁ : @IsIso (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) _ _ _
      (Scheme.Hom.relativeDifferentialFormsMap g' f f' g hsq.w (p : ℤ)) :=
    Scheme.Hom.isIso_relativeDifferentialFormsMap_of_isPullback g' f f' g hsq (p : ℤ)
  exact IsIso.comp_isIso' (Iso.isIso_hom ((HomologicalComplex.singleMapHomologicalComplex
    (modulePullback g'.toLRSHom.toShHom) (ComplexShape.up ℤ) (p : ℤ)).app _))
    (Iso.isIso_hom ((HomologicalComplex.single
      (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) (ComplexShape.up ℤ) (p : ℤ)).mapIso
        (@asIso (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace)) _ _ _ _ h₁)))

/-- An object placed in degree zero and shifted by `-k + n` is the object placed in degree `k`
and shifted by `n`. -/
def singleZeroShiftIso {A : Type*} [Category* A] [Preadditive A] [HasZeroObject A] (M : A)
    (k n : ℤ) :
    ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj M)⟦-k + n⟧ ≅
      ((HomologicalComplex.single A (ComplexShape.up ℤ) k).obj M)⟦n⟧ :=
  (shiftFunctorAdd' _ (-k) n (-k + n) rfl).app _ ≪≫
    (shiftFunctor _ n).mapIso (((CochainComplex.singleFunctors A).shiftIso (-k) k 0
      (by omega)).app M)

/-- The comparison of derived and underived pullback along `g'` is invertible at every shift of
`Ω^p_{X/S}` placed in any degree, for `f` smooth: `Ω^p_{X/S}` is flat. -/
theorem isIso_derivedPullbackComparison_single_shift [Smooth f] (p : ℕ) (k n : ℤ) :
    IsIso ((derivedPullbackComparison g'.toLRSHom.toShHom).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ) k).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))⟦n⟧))) := by
  have h₁ := isIso_app_shift_of_isIso (derivedPullbackComparison g'.toLRSHom.toShHom) _
    (-k + n) (isIso_derivedPullbackComparison_single_of_isFlat g'.toLRSHom.toShHom _
      (isFlat_relativeDifferentialForms f p))
  let e' : ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ) 0).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ))))⟦-k + n⟧ ≅
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
          (ComplexShape.up ℤ) k).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))⟦n⟧) :=
    (((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).commShiftIso (-k + n)).app _).symm ≪≫
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
        (singleZeroShiftIso (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) k n)
  exact (NatTrans.isIso_app_iff_of_iso (derivedPullbackComparison g'.toLRSHom.toShHom) e').1 h₁

open Stacks.CategoryTheory.ComparisonFiveLemma in
/-- **Base change for `Ω^p_{X/S}` placed in degree `p`, at every shift**: for a proper smooth `f`
and a cartesian square, the derived base change map at `Ω^p_{X/S}[-p][n]` followed by `Rf'_*`
of the comparison along `g'` and of the shift of `formsSingleMap` is invertible. -/
theorem isIso_derivedBaseChangeMap_formsSingle_shift (hsq : IsPullback g' f' f g) [IsProper f]
    [Smooth f] (p : ℕ) (n : ℤ) :
    IsIso (derivedBaseChangeMap g'.toLRSHom.toShHom f'.toLRSHom.toShHom f.toLRSHom.toShHom
        g.toLRSHom.toShHom (toShHom_comm hsq.w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ) (p : ℤ)).obj
              (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))⟦n⟧))) ≫
      (derivedPushforward f'.toLRSHom.toShHom).map ((derivedPullbackComparison
          g'.toLRSHom.toShHom).app ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ) (p : ℤ)).obj
              (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))⟦n⟧)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (shiftData ((modulePullback g'.toLRSHom.toShHom).mapHomologicalComplex
              (ComplexShape.up ℤ))
            (formsSingleMap g' f' f g hsq.w p) n)))) := by
  have hBC := isIso_derivedBaseChangeMap_single_shift hsq
    ⟨Scheme.Hom.relativeDifferentialForms f (p : ℤ),
      Scheme.Hom.isQuasicoherent_relativeDifferentialForms f p⟩
    (isFlatOver_relativeDifferentialForms f p) (isFlat_relativeDifferentialForms f p)
    (-(p : ℤ) + n)
  have hBC' := isIso_derivedBaseChangeMap_of_iso g'.toLRSHom.toShHom f'.toLRSHom.toShHom
    f.toLRSHom.toShHom g.toLRSHom.toShHom (toShHom_comm hsq.w)
    (DerivedCategory.Qh.mapIso ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      (singleZeroShiftIso (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) (p : ℤ) n))) hBC
  have hcmp := isIso_derivedPullbackComparison_single_shift (g' := g') (f := f) p (p : ℤ) n
  have hχ : IsIso (shiftData ((modulePullback g'.toLRSHom.toShHom).mapHomologicalComplex
      (ComplexShape.up ℤ)) (formsSingleMap g' f' f g hsq.w p) n) := by
    have := isIso_formsSingleMap hsq p
    dsimp only [shiftData]
    infer_instance
  exact IsIso.comp_isIso' hBC' (@Functor.map_isIso _ _ _ _ _ _ _ _
    (IsIso.comp_isIso' hcmp (@Functor.map_isIso _ _ _ _ _ _ _ _
      (@Functor.map_isIso _ _ _ _ _ _ _ _ hχ))))

/-- The inverse of an isomorphism written as a composite of two isomorphisms. -/
theorem inv_eq_of_hom_eq {C : Type*} [Category* C] {A B M : C} (e : A ≅ B) (a : A ≅ M)
    (b : M ≅ B) (h : e.hom = a.hom ≫ b.hom) : e.inv = b.inv ≫ a.inv := by
  rw [← cancel_epi e.hom, Iso.hom_inv_id, h]
  simp

/-- Cancellation of two pairs of mutually inverse isomorphisms around a morphism. -/
theorem inv_comp_hom_comp_comp_inv_comp_hom {C : Type*} [Category* C] {A B M N : C}
    (a : A ≅ B) (b : N ≅ M) (y : B ⟶ M) : a.inv ≫ (a.hom ≫ y ≫ b.inv) ≫ b.hom = y := by
  simp

variable (f) in
/-- The relative de Rham complex `Ω^•_{X/S}` indexed by `ℕ`, as a complex of `f^{-1}𝒪_S`-modules
written over `structureSheafRing (X, f^{-1}𝒪_S)`. -/
abbrev deRhamComplexNat :
    CochainComplex (SheafOfModules.{u} (structureSheafRing (inverseImageBase f))) ℕ :=
  Scheme.Hom.deRhamComplex f

variable (g' f' f g) in
/-- **The canonical map of extended de Rham complexes `g₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}`** of
`f'^{-1}𝒪_{S'}`-modules attached to a commutative square of schemes, where
`g₀ : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` is the induced morphism of inverse-image ringed
spaces: the canonical map `deRhamPullbackChain` extended by zero to `ℤ`. -/
def deRhamPullbackInt :
    ((modulePullback (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (deRhamComplexInt f) ⟶ deRhamComplexInt f' :=
  (HomologicalComplex.mapHomologicalComplexExtendIso
      (modulePullback (inverseImageBaseMap g' f' f g w))
      (deRhamComplexNat f)
      ComplexShape.embeddingUpNat).inv ≫
    HomologicalComplex.extendMap (deRhamPullbackChain g' f' f g w) ComplexShape.embeddingUpNat

/-- **The degree-`p` component of the extended canonical map of de Rham complexes** is the
degree-`p` component of `deRhamPullbackChain`. -/
theorem deRhamPullbackInt_f (p : ℕ) :
    (modulePullback (inverseImageBaseMap g' f' f g w)).map
        ((deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom ≫
      (deRhamPullbackChain g' f' f g w).f p =
      (deRhamPullbackInt g' f' f g w).f p ≫
        ((deRhamComplexNat f').extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom := by
  have hi := HomologicalComplex.mapHomologicalComplexExtendIso_hom_f
    (modulePullback (inverseImageBaseMap g' f' f g w))
    (deRhamComplexNat f) ComplexShape.embeddingUpNat (i := p) rfl
  have hinv : (HomologicalComplex.mapHomologicalComplexExtendIso
      (modulePullback (inverseImageBaseMap g' f' f g w))
      (deRhamComplexNat f) ComplexShape.embeddingUpNat).inv.f p =
      (modulePullback (inverseImageBaseMap g' f' f g w)).map
          ((deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom ≫
        ((((modulePullback (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (deRhamComplexNat f)).extendXIso
            ComplexShape.embeddingUpNat (i := p) rfl).inv :=
    inv_eq_of_hom_eq ((HomologicalComplex.eval _ _ (p : ℤ)).mapIso
      (HomologicalComplex.mapHomologicalComplexExtendIso
        (modulePullback (inverseImageBaseMap g' f' f g w))
        (deRhamComplexNat f) ComplexShape.embeddingUpNat))
      ((((modulePullback (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (deRhamComplexNat f)).extendXIso
            ComplexShape.embeddingUpNat (i := p) rfl)
      ((modulePullback (inverseImageBaseMap g' f' f g w)).mapIso
        ((deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat (i := p) rfl).symm) hi
  have he := HomologicalComplex.extendMap_f (deRhamPullbackChain g' f' f g w)
    ComplexShape.embeddingUpNat (i := p) (i' := (p : ℤ)) rfl
  show _ = ((HomologicalComplex.mapHomologicalComplexExtendIso
      (modulePullback (inverseImageBaseMap g' f' f g w))
      (deRhamComplexNat f) ComplexShape.embeddingUpNat).inv.f p ≫
    (HomologicalComplex.extendMap (deRhamPullbackChain g' f' f g w)
      ComplexShape.embeddingUpNat).f p) ≫
        ((deRhamComplexNat f').extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom
  rw [hinv, he]
  show _ = ((modulePullback (inverseImageBaseMap g' f' f g w)).map
          ((deRhamComplexNat f).extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom ≫
        ((((modulePullback (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (deRhamComplexNat f)).extendXIso
            ComplexShape.embeddingUpNat (i := p) rfl).inv) ≫
        (((((modulePullback (inverseImageBaseMap g' f' f g w)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (deRhamComplexNat f)).extendXIso
            ComplexShape.embeddingUpNat (i := p) rfl).hom ≫ (deRhamPullbackChain g' f' f g w).f p ≫
          ((deRhamComplexNat f').extendXIso ComplexShape.embeddingUpNat (i := p) rfl).inv) ≫
        ((deRhamComplexNat f').extendXIso ComplexShape.embeddingUpNat (i := p) rfl).hom
  rw [Category.assoc]
  exact (congrArg (_ ≫ ·) (inv_comp_hom_comp_comp_inv_comp_hom _ _ _)).symm

/-- The degree-`p` component of `deRhamPullbackChain` is the underived base change map of the
structural square at `Ω^p_{X/S}` followed by the canonical map `(g')^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}`. -/
theorem deRhamPullbackChain_f (p : ℕ) :
    (deRhamPullbackChain g' f' f g w).f p =
      (structuralBaseChange g' f' f g w).app (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) ≫
        (modulePushforward (toInverseImageBase f')).map
          (Scheme.Hom.relativeDifferentialFormsMap g' f f' g w p) := by
  have hc : (deRhamPullbackChain g' f' f g w).f p =
      ((modulePullbackPushforwardAdjunction (inverseImageBaseMap g' f' f g w)).homEquiv _ _).symm
        (formsPushforward g' f' f g w p) := by
    simp only [deRhamPullbackChain]
    rfl
  rw [hc, ← homEquiv_structuralBaseChange_comp]
  exact Equiv.symm_apply_apply _ _

variable (g' f' f g) in
/-- **The base change comparison for complexes of `f^{-1}𝒪_S`-modules** attached to a commutative
square of schemes: the natural transformation `derivedBaseChangeComplexTrans` of the square of
inverse-image ringed spaces `(X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` over `g`. -/
abbrev deRhamBaseChangeTrans :=
  derivedBaseChangeComplexTrans (inverseImageBaseMap g' f' f g w) (inverseImageBaseProjection f')
    (inverseImageBaseProjection f) g.toLRSHom.toShHom
    (inverseImageBaseMap_comp_inverseImageBaseProjection g' f' f g w)

open Stacks.CategoryTheory.ComparisonFiveLemma in
/-- **Base change for the graded pieces of the stupid filtration, at every shift**: the base
change comparison over the inverse-image ringed spaces at the restriction of scalars of
`Ω^p_{X/S}[-p][n]`, followed by the underived base change map of the structural square and the
shift of `formsSingleMap`, is invertible. -/
theorem isIso_comparison_restrictScalars_formsSingle_shift (hsq : IsPullback g' f' f g)
    [IsProper f] [Smooth f] (p : ℕ) (n : ℤ) :
    IsIso (comparison (deRhamBaseChangeTrans g' f' f g hsq.w)
      (E := ((modulePushforward (toInverseImageBase f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ) (p : ℤ)).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))⟦n⟧))
      (E' := ((modulePushforward (toInverseImageBase f')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          (((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
            (ComplexShape.up ℤ) (p : ℤ)).obj (Scheme.Hom.relativeDifferentialForms f' (p : ℤ)))⟦n⟧))
      ((NatTrans.mapHomologicalComplex (structuralBaseChange g' f' f g hsq.w)
          (ComplexShape.up ℤ)).app
          (((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ) (p : ℤ)).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ)))⟦n⟧) ≫
        ((modulePushforward (toInverseImageBase f')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
          (shiftData ((modulePullback g'.toLRSHom.toShHom).mapHomologicalComplex
            (ComplexShape.up ℤ)) (formsSingleMap g' f' f g hsq.w p) n))) := by
  have h := isIso_derivedBaseChangeMap_formsSingle_shift hsq p n
  have h' := isIso_derivedBaseChangeMap_comp_map_congr g'.toLRSHom.toShHom g.toLRSHom.toShHom
    (toInverseImageBase_comp f) (toInverseImageBase_comp f')
    (comp_square g'.toLRSHom.toShHom (toInverseImageBase f') (toInverseImageBase f)
      (inverseImageBaseMap g' f' f g hsq.w) (inverseImageBaseProjection f')
      (inverseImageBaseProjection f) g.toLRSHom.toShHom
      (toShHom_comp_toInverseImageBase g' f' f g hsq.w)
      (inverseImageBaseMap_comp_inverseImageBaseProjection g' f' f g hsq.w))
    (toShHom_comm hsq.w) _ _ h
  have key := isIso_derivedBaseChangeMap_comp_of_exact_pushforward_complex g'.toLRSHom.toShHom
    (toInverseImageBase f') (toInverseImageBase f) (inverseImageBaseMap g' f' f g hsq.w)
    (inverseImageBaseProjection f') (inverseImageBaseProjection f) g.toLRSHom.toShHom
    (toShHom_comp_toInverseImageBase g' f' f g hsq.w)
    (inverseImageBaseMap_comp_inverseImageBaseProjection g' f' f g hsq.w) _ _ _ h'
  rwa [Functor.map_comp, ← Category.assoc] at key

open Stacks.CategoryTheory.ComparisonFiveLemma in
/-- **Base change for the graded pieces of the stupid filtration**, in the form of the five
lemma: the base change comparison at the restriction of scalars of `Ω^p_{X/S}[-p]`, along the
underived base change map of the structural square and `formsSingleMap`, is invertible at every
shift. -/
theorem allShifts_restrictScalars_formsSingle (hsq : IsPullback g' f' f g) [IsProper f]
    [Smooth f] (p : ℕ) :
    AllShifts (deRhamBaseChangeTrans g' f' f g hsq.w)
      (E := ((modulePushforward (toInverseImageBase f)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ) (p : ℤ)).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ))))
      (E' := ((modulePushforward (toInverseImageBase f')).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
          ((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))
            (ComplexShape.up ℤ) (p : ℤ)).obj (Scheme.Hom.relativeDifferentialForms f' (p : ℤ))))
      ((NatTrans.mapHomologicalComplex (structuralBaseChange g' f' f g hsq.w)
          (ComplexShape.up ℤ)).app
          ((HomologicalComplex.single (SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
            (ComplexShape.up ℤ) (p : ℤ)).obj (Scheme.Hom.relativeDifferentialForms f (p : ℤ))) ≫
        ((modulePushforward (toInverseImageBase f')).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (formsSingleMap g' f' f g hsq.w p)) := by
  intro n
  refine (isIso_comparison_iff_of_hom (deRhamBaseChangeTrans g' f' f g hsq.w) _ _
    ((((modulePushforward (toInverseImageBase f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).commShiftIso n).hom.app _)
    ((((modulePushforward (toInverseImageBase f')).mapHomologicalComplex
      (ComplexShape.up ℤ)).commShiftIso n).hom.app _) ?_).1
    (isIso_comparison_restrictScalars_formsSingle_shift hsq p n)
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  simp only [shiftData, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    Functor.mapHomologicalComplex_commShiftIso_hom_app_f, CochainComplex.shiftFunctor_map_f',
    NatTrans.mapHomologicalComplex_app_f, CategoryTheory.Functor.map_id,
    Category.comp_id, Functor.map_comp]
  dsimp only [Functor.comp_obj]
  simp only [Category.id_comp, CategoryTheory.Functor.map_id]
  exact (Category.id_comp _).trans (congrArg (_ ≫ ·) (Category.id_comp _).symm)

/-- The derived pushforward along a morphism of ringed spaces is additive. -/
private theorem additive_derivedPushforward {Y Z : RingedSpace.{u, u}} (φ : Y ⟶ Z) :
    (derivedPushforward φ).Additive :=
  (derivedAdjunction φ).right_adjoint_additive

open Stacks.CategoryTheory.ComparisonFiveLemma StacksDraft.StupidTruncation in
/-- **Base change for the graded pieces of the stupid filtration of the de Rham complex**: the
base change comparison along the map induced by `deRhamPullbackInt` on `Ω^q[-q]` is invertible at
every shift. -/
theorem allShifts_stupidTruncGEGradedMap (hsq : IsPullback g' f' f g) [IsProper f] [Smooth f]
    (q : ℤ) :
    AllShifts (deRhamBaseChangeTrans g' f' f g hsq.w)
      (stupidTruncGEGradedMap (modulePullback (inverseImageBaseMap g' f' f g hsq.w))
        (deRhamPullbackInt g' f' f g hsq.w) q) := by
  by_cases hq : q < 0
  · have := additive_derivedPushforward (inverseImageBaseProjection f)
    have := additive_derivedPushforward (inverseImageBaseProjection f')
    have := additive_derivedPushforward g.toLRSHom.toShHom
    exact allShifts_of_isZero _ _
      (Functor.map_isZero _ (Functor.map_isZero (HomologicalComplex.single _ _ q)
        (isZero_deRhamComplexInt_X_of_neg f q hq)))
      (Functor.map_isZero _ (Functor.map_isZero (HomologicalComplex.single _ _ q)
        (isZero_deRhamComplexInt_X_of_neg f' q hq)))
  · obtain ⟨p, rfl⟩ : ∃ p : ℕ, (p : ℤ) = q := ⟨q.toNat, by omega⟩
    let u := deRhamComplexIntXIso f p
    let u' := deRhamComplexIntXIso f' p
    have h : (modulePullback (inverseImageBaseMap g' f' f g hsq.w)).map u.hom ≫
        (structuralBaseChange g' f' f g hsq.w).app
          (Scheme.Hom.relativeDifferentialForms f (p : ℤ)) ≫
          (modulePushforward (toInverseImageBase f')).map
            (Scheme.Hom.relativeDifferentialFormsMap g' f f' g hsq.w p) =
        (deRhamPullbackInt g' f' f g hsq.w).f p ≫ u'.hom :=
      (congrArg (_ ≫ ·) (deRhamPullbackChain_f hsq.w p).symm).trans
        (deRhamPullbackInt_f hsq.w p)
    have key := mapHomologicalComplex_single_comp_eq_iso
      (modulePushforward (toInverseImageBase f)) (modulePushforward (toInverseImageBase f'))
      (modulePullback (inverseImageBaseMap g' f' f g hsq.w))
      (modulePullback g'.toLRSHom.toShHom) (structuralBaseChange g' f' f g hsq.w)
      (M := Scheme.Hom.relativeDifferentialForms f (p : ℤ))
      (M' := Scheme.Hom.relativeDifferentialForms f' (p : ℤ)) u u'
      ((deRhamPullbackInt g' f' f g hsq.w).f p)
      (Scheme.Hom.relativeDifferentialFormsMap g' f f' g hsq.w p) h (p : ℤ)
    exact (allShifts_iff_of_hom (deRhamBaseChangeTrans g' f' f g hsq.w) _ _ _ _ key).2
      (allShifts_restrictScalars_formsSingle hsq p)

/-- The truncations of the extended de Rham complex in degrees above a vanishing bound restrict
to zero over an open of the base. -/
theorem isZero_modulePullback_stupidTrunc_deRhamComplexInt_X (V : S.Opens) {N : ℕ}
    (hN : ∀ p : ℕ, N < p → ∀ W : X.Opens, W ≤ f ⁻¹ᵁ V →
      Subsingleton ((Scheme.Hom.relativeDifferentialForms f (p : ℤ)).val.obj (Opposite.op W)))
    (n : ℤ) :
    IsZero ((modulePullback ((inverseImageBase f).ofRestrict
      (Stacks.Cohomology.DerivedPushforwardOverOpen.preimageOpen
        (inverseImageBaseProjection f) V).isOpenEmbedding)).obj
          (((deRhamComplexInt f).stupidTrunc (ComplexShape.embeddingUpIntGE ((N : ℤ) + 1))).X
              n)) := by
  by_cases hn : (N : ℤ) + 1 ≤ n
  · exact IsZero.of_iso (isZero_modulePullback_deRhamComplexInt_X f V hN n (by omega))
      ((modulePullback _).mapIso (StacksDraft.StupidTruncation.stupidTruncGEXIso _ _ n hn))
  · exact Functor.map_isZero _ (CochainComplex.isZero_of_isStrictlyGE _ ((N : ℤ) + 1) n
      (by omega))

open Stacks.CategoryTheory.ComparisonFiveLemma StacksDraft.StupidTruncation in
/-- The base change comparison over an open `W'` of `S'` vanishes at the top of the stupid
filtration of the de Rham complex, above a degree bound for the vanishing of the forms. -/
theorem allShifts_stupidTruncGELift_of_vanishing (hsq : IsPullback g' f' f g) (V : S.Opens)
    (W' : S'.Opens) (hWV : W' ≤ g ⁻¹ᵁ V) (N : ℕ)
    (hN₁ : ∀ p : ℕ, N < p → ∀ W : X.Opens, W ≤ f ⁻¹ᵁ V →
      Subsingleton ((Scheme.Hom.relativeDifferentialForms f (p : ℤ)).val.obj (Opposite.op W)))
    (hN₂ : ∀ p : ℕ, N < p → ∀ W : X'.Opens, W ≤ f' ⁻¹ᵁ W' →
      Subsingleton ((Scheme.Hom.relativeDifferentialForms f' (p : ℤ)).val.obj (Opposite.op W))) :
    AllShifts (whiskerComparison (deRhamBaseChangeTrans g' f' f g hsq.w)
      (derivedPullback (S'.toRingedSpace.ofRestrict W'.isOpenEmbedding)))
      (stupidTruncGELift (modulePullback (inverseImageBaseMap g' f' f g hsq.w))
        (deRhamPullbackInt g' f' f g hsq.w) ((N : ℤ) + 1)) := by
  have := additive_derivedPushforward (inverseImageBaseProjection f)
  have := additive_derivedPushforward (inverseImageBaseProjection f')
  have := additive_derivedPushforward g.toLRSHom.toShHom
  have := additive_derivedPushforward
    (S'.toRingedSpace.ofRestrict W'.isOpenEmbedding)
  refine allShifts_of_isZero _ _ ?_ ?_
  · exact Stacks.Cohomology.DerivedPushforwardOverOpen.isZero_derivedPullback_derivedPullback_of_le
      g.toLRSHom.toShHom V W' hWV _
      (Stacks.Cohomology.DerivedPushforwardOverOpen.isZero_derivedPullback_derivedPushforward
        (inverseImageBaseProjection f) V _
        (isZero_modulePullback_stupidTrunc_deRhamComplexInt_X (f := f) V hN₁))
  · exact Stacks.Cohomology.DerivedPushforwardOverOpen.isZero_derivedPullback_derivedPushforward
      (inverseImageBaseProjection f') W' _
      (isZero_modulePullback_stupidTrunc_deRhamComplexInt_X (f := f') W' hN₂)

open Stacks.CategoryTheory.ComparisonFiveLemma StacksDraft.StupidTruncation in
/-- One step of the descent along the stupid filtration of the de Rham complex: over an open `W'`
of `S'`, the base change comparison is invertible at every shift on `σ_{≥ q}` as soon as it is
on `σ_{≥ q + 1}`. -/
theorem allShifts_stupidTruncGELift_of_succ (hsq : IsPullback g' f' f g) [IsProper f] [Smooth f]
    (W' : S'.Opens) (q : ℤ)
    (hq : AllShifts (whiskerComparison (deRhamBaseChangeTrans g' f' f g hsq.w)
      (derivedPullback (S'.toRingedSpace.ofRestrict W'.isOpenEmbedding)))
      (stupidTruncGELift (modulePullback (inverseImageBaseMap g' f' f g hsq.w))
        (deRhamPullbackInt g' f' f g hsq.w) (q + 1))) :
    AllShifts (whiskerComparison (deRhamBaseChangeTrans g' f' f g hsq.w)
      (derivedPullback (S'.toRingedSpace.ofRestrict W'.isOpenEmbedding)))
      (stupidTruncGELift (modulePullback (inverseImageBaseMap g' f' f g hsq.w))
        (deRhamPullbackInt g' f' f g hsq.w) q) := by
  let := derivedPushforwardCommShift (inverseImageBaseProjection f)
  let := derivedPushforwardCommShift (inverseImageBaseProjection f')
  have := derivedPushforward_isTriangulated (inverseImageBaseProjection f)
  have := derivedPushforward_isTriangulated (inverseImageBaseProjection f')
  have := additive_derivedPushforward (inverseImageBaseProjection f)
  have := additive_derivedPushforward (inverseImageBaseProjection f')
  have := additive_derivedPushforward g.toLRSHom.toShHom
  have := additive_derivedPushforward
    (S'.toRingedSpace.ofRestrict W'.isOpenEmbedding)
  have hT := mapTriangle_comp_distinguished _
    (derivedPullback (S'.toRingedSpace.ofRestrict W'.isOpenEmbedding)) _
    (mapTriangle_comp_distinguished (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (DerivedCategory.Qh ⋙ derivedPushforward (inverseImageBaseProjection f) ⋙
        derivedPullback g.toLRSHom.toShHom) _
      (CochainComplex.trianglehOfDegreewiseSplit_distinguished _
        (stupidTruncGESplitting (deRhamComplexInt f) q)))
  have hT' := mapTriangle_comp_distinguished _
    (derivedPullback (S'.toRingedSpace.ofRestrict W'.isOpenEmbedding)) _
    (mapTriangle_comp_distinguished (HomotopyCategory.quotient _ (ComplexShape.up ℤ))
      (DerivedCategory.Qh ⋙ derivedPushforward (inverseImageBaseProjection f')) _
      (CochainComplex.trianglehOfDegreewiseSplit_distinguished _
        (stupidTruncGESplitting (deRhamComplexInt f') q)))
  exact allShifts_hom₂ _ _ _ hT hT' (stupidTruncGETriangleHom _ _ q) hq
    ((allShifts_stupidTruncGEGradedMap hsq q).whisker _ _)

open Stacks.CategoryTheory.ComparisonFiveLemma StacksDraft.StupidTruncation in
/-- **Base change for the de Rham complex over an affine open of `S'` mapping into an affine
open of `S`**: after restriction to such an open, the base change comparison at the de Rham
complex along `deRhamPullbackInt` is invertible at every shift. The forms of high degree vanish
over both opens, and the stupid filtration is descended through the five lemma, the graded
pieces being handled by `allShifts_stupidTruncGEGradedMap`. -/
theorem allShifts_deRhamPullbackInt_restrict (hsq : IsPullback g' f' f g) [IsProper f]
    [Smooth f] (V : S.Opens) (hV : IsAffineOpen V) (W' : S'.Opens) (hW' : IsAffineOpen W')
    (hWV : W' ≤ g ⁻¹ᵁ V) :
    AllShifts (whiskerComparison (deRhamBaseChangeTrans g' f' f g hsq.w)
      (derivedPullback (S'.toRingedSpace.ofRestrict W'.isOpenEmbedding)))
      (deRhamPullbackInt g' f' f g hsq.w) := by
  have : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact) hsq inferInstance
  have hc : IsCompact ((f ⁻¹ᵁ V : X.Opens) : Set X) :=
    QuasiCompact.isCompact_preimage (f := f) _ V.isOpen hV.isCompact
  have hc' : IsCompact ((f' ⁻¹ᵁ W' : X'.Opens) : Set X') :=
    QuasiCompact.isCompact_preimage (f := f') _ W'.isOpen hW'.isCompact
  have : Smooth f' := MorphismProperty.of_isPullback (P := @Smooth) hsq inferInstance
  obtain ⟨N₁, hN₁⟩ := exists_forall_subsingleton_relativeDifferentialForms f _ hc
  obtain ⟨N₂, hN₂⟩ := exists_forall_subsingleton_relativeDifferentialForms f' _ hc'
  have := additive_derivedPushforward (inverseImageBaseProjection f)
  have := additive_derivedPushforward (inverseImageBaseProjection f')
  have := additive_derivedPushforward g.toLRSHom.toShHom
  have := additive_derivedPushforward
    (S'.toRingedSpace.ofRestrict W'.isOpenEmbedding)
  let α := whiskerComparison (deRhamBaseChangeTrans g' f' f g hsq.w)
      (derivedPullback (S'.toRingedSpace.ofRestrict W'.isOpenEmbedding))
  let G₀ := modulePullback (inverseImageBaseMap g' f' f g hsq.w)
  let ψ := deRhamPullbackInt g' f' f g hsq.w
  have hall (m : ℕ) : AllShifts α (stupidTruncGELift G₀ ψ ((N₁ + N₂ : ℕ) + 1 - m)) := by
    induction m with
    | zero =>
      rw [Nat.cast_zero, sub_zero]
      exact allShifts_stupidTruncGELift_of_vanishing hsq V W' hWV (N₁ + N₂)
        (fun p hp => hN₁ p (by omega)) (fun p hp => hN₂ p (by omega))
    | succ m ih =>
      have := allShifts_stupidTruncGELift_of_succ hsq W' ((N₁ + N₂ : ℕ) + 1 - (m + 1 : ℕ))
      rw [show ((N₁ + N₂ : ℕ) : ℤ) + 1 - ((m + 1 : ℕ) : ℤ) + 1 = (N₁ + N₂ : ℕ) + 1 - m by
        omega] at this
      exact this ih
  have h0 := hall (N₁ + N₂ + 1)
  rw [show ((N₁ + N₂ : ℕ) : ℤ) + 1 - ((N₁ + N₂ + 1 : ℕ) : ℤ) = 0 by omega] at h0
  have : (deRhamComplexInt f).IsStrictlyGE 0 :=
    inferInstanceAs ((deRhamCochainComplex f).IsStrictlyGE 0)
  have : (deRhamComplexInt f').IsStrictlyGE 0 :=
    inferInstanceAs ((deRhamCochainComplex f').IsStrictlyGE 0)
  have := StacksDraft.StupidFiltration.isIso_ιStupidTruncGE (deRhamComplexInt f) 0
  have := StacksDraft.StupidFiltration.isIso_ιStupidTruncGE (deRhamComplexInt f') 0
  exact (allShifts_iff_of_hom α _ _ _ _ (stupidTruncGELift_ι G₀ ψ 0).symm).1 h0

variable (g' f' f g) in
/-- **The canonical comparison `Lg₀^*Ω^•_{X/S} ⟶ Ω^•_{X'/S'}`** attached to a commutative square of
schemes, where `g₀ : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` is the induced morphism of inverse-image
ringed spaces: the comparison of the derived and the termwise pullback along `g₀`, followed by
the canonical map of de Rham complexes `deRhamPullbackInt` (built from the maps
`(g')^*Ω^p_{X/S} ⟶ Ω^p_{X'/S'}` of Stacks 07HX). -/
def deRhamBaseChangeComparison :
    (derivedPullback (inverseImageBaseMap g' f' f g w)).obj
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (deRhamComplexInt f))) ⟶
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (deRhamComplexInt f')) :=
  (derivedPullbackComparison (inverseImageBaseMap g' f' f g w)).app
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (deRhamComplexInt f)) ≫
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (deRhamPullbackInt g' f' f g w))

open Stacks.CategoryTheory.ComparisonFiveLemma in
/-- **Base change for `Rf_*Ω^•_{X/S}`.** Let `f : X ⟶ S` be a proper smooth morphism of schemes
and let

```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```

be a cartesian square. Write `π : (X, f^{-1}𝒪_S) ⟶ S` and `π' : (X', f'^{-1}𝒪_{S'}) ⟶ S'`, so that
`Rπ_*Ω^•_{X/S}` is `Rf_*Ω^•_{X/S}` as an object of `D(𝒪_S)`, and let
`g₀ : (X', f'^{-1}𝒪_{S'}) ⟶ (X, f^{-1}𝒪_S)` be the induced morphism, lying over `g`. Then the
canonical map

`Lg^*Rπ_*Ω^•_{X/S} ⟶ Rπ'_*Lg₀^*Ω^•_{X/S} ⟶ Rπ'_*Ω^•_{X'/S'}`

— the derived base change map of Stacks 08HY followed by `Rπ'_*` of
`deRhamBaseChangeComparison` — is an isomorphism. -/
@[stacks 0FM0 "formation of Rf_*Omega^bullet_X/S commutes with arbitrary change of base: for a \
proper smooth f and any cartesian square the derived base change map of Tag 08HY along the \
inverse-image ringed spaces, followed by the canonical map of de Rham complexes, is an \
isomorphism"]
theorem isIso_derivedBaseChangeMap_deRhamComplex (hsq : IsPullback g' f' f g) [IsProper f]
    [Smooth f] :
    IsIso (derivedBaseChangeMap (inverseImageBaseMap g' f' f g hsq.w)
        (inverseImageBaseProjection f') (inverseImageBaseProjection f) g.toLRSHom.toShHom
        (inverseImageBaseMap_comp_inverseImageBaseProjection g' f' f g hsq.w)
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (deRhamComplexInt f))) ≫
      (derivedPushforward (inverseImageBaseProjection f')).map
        (deRhamBaseChangeComparison g' f' f g hsq.w)) := by
  let I := {W' : S'.affineOpens // ∃ V : S.Opens, IsAffineOpen V ∧ W'.1 ≤ g ⁻¹ᵁ V}
  have hU : iSup (fun i : I => (i.1.1 : S'.Opens)) = ⊤ := by
    refine eq_top_iff.2 fun s' _ => ?_
    obtain ⟨V, hV, hgV, -⟩ := exists_isAffineOpen_mem_and_subset (x := g s') (U := ⊤) trivial
    obtain ⟨W, hW, hsW, hWV⟩ := exists_isAffineOpen_mem_and_subset (x := s') (U := g ⁻¹ᵁ V) hgV
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨W, hW⟩, V, hV, hWV⟩, hsW⟩
  have key : IsIso (comparison (deRhamBaseChangeTrans g' f' f g hsq.w)
      (deRhamPullbackInt g' f' f g hsq.w)) := by
    have hloc : ∀ i : I, IsIso ((derivedPullback (S'.toRingedSpace.ofRestrict
        (i.1.1 : S'.Opens).isOpenEmbedding)).map (comparison (deRhamBaseChangeTrans g' f' f g hsq.w)
          (deRhamPullbackInt g' f' f g hsq.w))) := by
      rintro ⟨⟨W, hW⟩, V, hV, hWV⟩
      have := (allShifts_deRhamPullbackInt_restrict hsq V hV W hW hWV).isIso
      rwa [comparison_whiskerComparison] at this
    exact Stacks.Cohomology.isIso_of_isIso_jStar_mapDerivedCategory_map
      (structureSheafRing S'.toRingedSpace) (fun i : I => (i.1.1 : S'.Opens)) hU _ fun i =>
        (NatIso.isIso_map_iff
          (Stacks.Cohomology.DerivedOpenImmersion.derivedPullbackOpenRestrictionIso
            S'.toRingedSpace (i.1.1 : S'.Opens)) _).mp (hloc i)
  simp only [comparison, deRhamBaseChangeTrans, derivedBaseChangeComplexTrans_app,
    Functor.comp_map] at key
  rwa [deRhamBaseChangeComparison, Functor.map_comp, ← Category.assoc]

end

end AlgebraicGeometry.ProperSmoothDeRham
