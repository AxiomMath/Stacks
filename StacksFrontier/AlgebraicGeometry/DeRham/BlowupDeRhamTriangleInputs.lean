module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangleDistinguished
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsExceptionalComparison
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupSmoothCentreFormsDirectImage
public import StacksFrontier.AlgebraicGeometry.DeRham.PullbackComplexDegreewise
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedUnitExact

/-!
# The inputs of the blowup triangle, from the clauses of Stacks 0FUU

`Stacks.DeRham.BlowupTriangle.exists_distTriang_of_isIso` proves the triangle of [Stacks, Tag 0FUV]
from three facts about the canonical maps of de Rham complexes of `f^{-1}𝒪_S`-modules. The three
clauses of [Stacks, Tag 0FUU] are statements about sheaves of `𝒪`-modules: the comparison maps
`Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` and `Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}` of `𝒪_X`- and `𝒪_Z`-modules, and the
comparison `Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` in `D(𝒪_X)`. This file translates them.

Clauses (1) and (2) translate degreewise: the components of the canonical maps of de Rham complexes
are the graded homomorphisms of Section 07HX, whose adjoint transposes are the comparison maps.
Clause (3) needs that the cohomology sheaves of `Rb_*` do not depend on the ring of coefficients:
restricting the coefficients of `𝒪_{X'}`-modules to `(X' → S)^{-1}𝒪_S` is exact and commutes with
`Rb_*` by [Stacks, Tag 0D5T] (both composites are derived direct images along the same morphism of
ringed spaces), and an exact functor commutes with cohomology sheaves. The canonical map
`Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}` of `f^{-1}𝒪_S`-modules is the comparison map on direct images of forms
along `j` with its coefficients restricted; this is checked on sections.

## Main results

* `Stacks.DeRham.BlowupTriangle.isIso_chain`: invertibility of the canonical map of de Rham
  complexes from that of its components.
* `Stacks.DeRham.BlowupTriangle.isIso_homologyFunctor_map_inclusionChain_f`: clause (3) of
  [Stacks, Tag 0FUU], read on `f^{-1}𝒪_S`-modules.
* `Stacks.DeRham.BlowupTriangle.exists_distTriang_of_formsDirectImage`: the triangle of
  [Stacks, Tag 0FUV] from the three clauses of [Stacks, Tag 0FUU] as stated for `𝒪`-modules.

## Implementation notes

All derived categories are arbitrary models. Several identifications are proved on sections and
phrased with `HEq`, the categories involved being spelled `Modules`, `Scheme.Modules` and
`ModuleSheaves`, which agree only at default transparency. Where a definition's body contains an
`eqToHom`, it is unfolded in a hypothesis and peeled with a lemma whose arguments are found by
unification, rather than retyped: a retyped `eqToHom` carries a different proof term, and the
kernel then compares the two by unfolding.

## References

* [Stacks Project, Tag 0FUV](https://stacks.math.columbia.edu/tag/0FUV)
* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
* [Stacks Project, Section 07HX](https://stacks.math.columbia.edu/tag/07HX)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamSmooth
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham.BlowupTriangle

/-! ### Generalities -/

/-- Extending a map of complexes along an embedding preserves invertibility of the components in
the range of the embedding. -/
lemma isIso_extendMap_f {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} {K L : HomologicalComplex C c}
    (φ : K ⟶ L) (e : c.Embedding c') (k : ι) [IsIso (φ.f k)] :
    IsIso ((HomologicalComplex.extendMap φ e).f (e.f k)) := by
  rw [HomologicalComplex.extendMap_f φ e rfl]
  infer_instance

/-- Morphisms of sheaves of modules between equal objects which agree on sections, up to the
transports, are equal as arrows. -/
lemma arrow_mk_eq_of_val_app_heq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} {M M' N N' : SheafOfModules.{u} R} (hM : M = M') (hN : N = N')
    (φ : M ⟶ N) (ψ : M' ⟶ N')
    (h : ∀ (U : Cᵒᵖ) (x : M.val.obj U) (x' : M'.val.obj U), HEq x x' →
      HEq (φ.val.app U x) (ψ.val.app U x')) :
    Arrow.mk φ = Arrow.mk ψ := by
  subst hM hN
  congr 1
  ext U x
  exact eq_of_heq (h U x x HEq.rfl)

/-- A term of a complex extended along an embedding, in a degree in the range of the embedding, is
the corresponding term of the complex. -/
lemma extend_X_eq {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {ι ι' : Type*} {c : ComplexShape ι} {c' : ComplexShape ι'} (K : HomologicalComplex C c)
    (e : c.Embedding c') {k : ι} {k' : ι'} (hk : e.f k = k') : (K.extend e).X k' = K.X k := by
  show HomologicalComplex.extend.X K (e.r k') = _
  rw [e.r_eq_some hk]
  rfl

/-- Pushing a sheaf of modules forward along `g` and then along `h` is pushing it forward along
`g ≫ h`, on the nose. -/
lemma modulePushforward_comp_obj {A B C : RingedSpace.{u, u}} (g : A ⟶ B) (h : B ⟶ C)
    (M : ModuleSheaves A) :
    (RingedSpaceModuleAdjunction.modulePushforward h).obj
        ((RingedSpaceModuleAdjunction.modulePushforward g).obj M) =
      (RingedSpaceModuleAdjunction.modulePushforward (g ≫ h)).obj M :=
  rfl

/-- If a functor carries `c ≫ t` to an isomorphism and `t` is invertible, it carries `c` to an
isomorphism. -/
lemma isIso_map_of_isIso_map_comp {C D : Type*} [Category C] [Category D] (Φ : C ⥤ D) {A B E : C}
    (c : A ⟶ B) (t : B ⟶ E) [IsIso t] (h : IsIso (Φ.map (c ≫ t))) : IsIso (Φ.map c) := by
  rw [Φ.map_comp] at h
  exact IsIso.of_isIso_comp_right _ (Φ.map t)

/-! ### The canonical map of de Rham complexes, degreewise -/

section Chain

/-- A map from a negative term of an extended de Rham complex to the image under a functor of a
negative term of another is invertible, both being zero. -/
private lemma isIso_of_deRhamCochainComplex_X_negSucc {S Y Y' : Scheme.{u}} {s : Y ⟶ S}
    {s' : Y' ⟶ S} (Φ : ModuleSheaves (inverseImageBase s') ⥤ ModuleSheaves (inverseImageBase s))
    [Φ.PreservesZeroMorphisms] (k : ℕ)
    (φ : (deRhamCochainComplex s).X (Int.negSucc k) ⟶
      Φ.obj ((deRhamCochainComplex s').X (Int.negSucc k))) : IsIso φ :=
  isIso_of_source_target_iso_zero _
    ((deRhamCochainComplex s).isZero_of_isStrictlyGE 0 _ (by omega)).isoZero
    (Functor.map_isZero Φ
      ((deRhamCochainComplex s').isZero_of_isStrictlyGE 0 _ (by omega))).isoZero

variable {S Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (s : Y ⟶ S)

/-- **The canonical map of de Rham complexes is an isomorphism as soon as its components are**:
if every component `Ω^k_{Y/S} ⟶ g_*Ω^k_{Y'/S}` of the graded homomorphism of Section 07HX is
invertible, so is `Ω^•_{Y/S} ⟶ g_*Ω^•_{Y'/S}`. -/
lemma isIso_chain (h : ∀ k : ℕ, IsIso ((Scheme.Hom.deRhamFormsPushforwardHom g s (g ≫ s) (𝟙 S)
    (Category.comp_id _).symm).app k)) : IsIso (chain g s) := by
  suffices hc : ∀ n : ℤ, IsIso ((chain g s).f n) from
    @HomologicalComplex.Hom.isIso_of_components _ _ _ _ _ _ _ (chain g s) hc
  intro n
  rcases n with k | k
  · have hD : IsIso ((Stacks.DeRhamPullback.deRhamPushforwardChain g s).f k) :=
      @IsIso.comp_isIso _ _ _ _ _ _ _
        (((_root_.pushforward (toInverseImageBase s)).mapIso (@asIso _ _ _ _ _ (h k))).isIso_hom)
        (((Stacks.DeRhamPullback.pushforwardSquareIso g s).app _).isIso_inv)
    have hE : IsIso ((HomologicalComplex.extendMap
        (Stacks.DeRhamPullback.deRhamPushforwardChain g s)
        ComplexShape.embeddingUpNat).f (k : ℤ)) :=
      isIso_extendMap_f (Stacks.DeRhamPullback.deRhamPushforwardChain g s)
        ComplexShape.embeddingUpNat k
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ hE
      (HomologicalComplex.Hom.isoApp (Stacks.DerivedIndexing.mapExtendIso
        (RingedSpaceModuleAdjunction.modulePushforward (relativeBase g s))
        ComplexShape.embeddingUpNat
        (show CochainComplex (SheafOfModules.{u} (structureSheafRing (inverseImageBase (g ≫ s)))) ℕ
          from Scheme.Hom.deRhamComplex (g ≫ s))) (k : ℤ)).isIso_hom
  · exact isIso_of_deRhamCochainComplex_X_negSucc
      (RingedSpaceModuleAdjunction.modulePushforward (relativeBase g s)) k _

end Chain

/-! ### Restriction of coefficients to the base -/

section Scalars

variable {S : Scheme.{u}}

/-- Restricting the coefficients to the base is the identity on spaces. -/
lemma isClosedEmbedding_toInverseImageBase_base {Y : Scheme.{u}} (s : Y ⟶ S) :
    Topology.IsClosedEmbedding (toInverseImageBase s).hom.base :=
  Topology.IsClosedEmbedding.id

/-- **Restriction of scalars to `s^{-1}𝒪_S` preserves isomorphisms on cohomology sheaves**, on
derived categories. -/
lemma isIso_homologyFunctor_map_derivedPushforward_toInverseImageBase {Y : Scheme.{u}}
    (s : Y ⟶ S) [HasDerivedCategory (ModuleSheaves Y.toRingedSpace)]
    [HasDerivedCategory (ModuleSheaves (inverseImageBase s))]
    {M N : DerivedCategory (ModuleSheaves Y.toRingedSpace)} (α : M ⟶ N) (n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor _ n).map α)) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((derivedPushforward (toInverseImageBase s)).map α)) :=
  have := Stacks.ClosedImmersion.preservesFiniteColimits_modulePushforward _
    (isClosedEmbedding_toInverseImageBase_base s)
  StacksDraft.DerivedUnitSquare.isIso_homologyFunctor_map_map
    (RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase s))
    (derivedPushforwardUnit (toInverseImageBase s))
    (isIso_unit_of_isClosedEmbedding _ (isClosedEmbedding_toInverseImageBase_base s)) α n h

/-- **The derived direct image commutes with restriction of scalars to the base**, as far as
invertibility on cohomology sheaves is concerned: for `g : Y' ⟶ Y` over `s : Y ⟶ S`, the two
composites `Rg_*` then restriction to `s^{-1}𝒪_S`, and restriction to `(g ≫ s)^{-1}𝒪_S` then
`Rg_*`, are identified by [Stacks, Tag 0D5T]. -/
lemma isIso_homologyFunctor_map_derivedPushforward_relativeBase {Y Y' : Scheme.{u}}
    (g : Y' ⟶ Y) (s : Y ⟶ S) [HasDerivedCategory (ModuleSheaves Y'.toRingedSpace)]
    [HasDerivedCategory (ModuleSheaves Y.toRingedSpace)]
    [HasDerivedCategory (ModuleSheaves (inverseImageBase (g ≫ s)))]
    [HasDerivedCategory (ModuleSheaves (inverseImageBase s))]
    {M N : DerivedCategory (ModuleSheaves Y'.toRingedSpace)} (α : M ⟶ N) (n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((derivedPushforward g.toLRSHom.toShHom).map α))) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((derivedPushforward (relativeBase g s)).map
        ((derivedPushforward (toInverseImageBase (g ≫ s))).map α))) := by
  let e : derivedPushforward (toInverseImageBase (g ≫ s)) ⋙ derivedPushforward (relativeBase g s) ≅
      derivedPushforward g.toLRSHom.toShHom ⋙ derivedPushforward (toInverseImageBase s) :=
    (compIso _ _).symm ≪≫
      eqToIso (congrArg (fun k => derivedPushforward k)
        (Stacks.DeRhamPullback.toInverseImageBase_relativeBase g s)) ≪≫
      compIso _ _
  exact (NatIso.isIso_map_iff (Functor.isoWhiskerRight e (DerivedCategory.homologyFunctor _ n)) α).2
    (isIso_homologyFunctor_map_derivedPushforward_toInverseImageBase s _ n h)

/-- **The derived direct image along a closed embedding, on a map of sheaves in degree `0`, is the
direct image**, up to isomorphism of arrows: for a functor `Φ` out of the derived category,
`Φ(Q(g_*φ))` is invertible exactly when `Φ(Rg_*(Q(φ)))` is. -/
lemma isIso_map_Q_single_map_iff {A B : RingedSpace.{u, u}} (g : A ⟶ B)
    (hg : Topology.IsClosedEmbedding g.hom.base) [HasDerivedCategory (ModuleSheaves A)]
    [HasDerivedCategory (ModuleSheaves B)] {E : Type*} [Category E]
    (Φ : DerivedCategory (ModuleSheaves B) ⥤ E) {F G : ModuleSheaves A} (φ : F ⟶ G) :
    IsIso (Φ.map (DerivedCategory.Q.map ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
        ((RingedSpaceModuleAdjunction.modulePushforward g).map φ)))) ↔
      IsIso (Φ.map ((derivedPushforward g).map (DerivedCategory.Q.map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ)))) := by
  have hu := isIso_unit_of_isClosedEmbedding g hg
  let e : ∀ F' : ModuleSheaves A, DerivedCategory.Q.obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
        ((RingedSpaceModuleAdjunction.modulePushforward g).obj F')) ≅
      (derivedPushforward g).obj (DerivedCategory.Q.obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F')) := fun F' =>
    DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
      (RingedSpaceModuleAdjunction.modulePushforward g) (ComplexShape.up ℤ) 0).app F').symm ≪≫
      @asIso _ _ _ _ _ (hu _)
  refine (MorphismProperty.isomorphisms E).arrow_mk_iso_iff
    (Φ.mapArrow.mapIso (Arrow.isoMk' _ _ (e F) (e G) ?_))
  have h₁ := (HomologicalComplex.singleMapHomologicalComplex
    (RingedSpaceModuleAdjunction.modulePushforward g) (ComplexShape.up ℤ) 0).inv.naturality φ
  have h₂ := StacksDraft.DerivedUnitSquare.unitQ_naturality
    (RingedSpaceModuleAdjunction.modulePushforward g) (derivedPushforwardUnit g)
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ)
  dsimp [e] at h₁ ⊢
  rw [← Functor.map_comp_assoc, h₁, Functor.map_comp_assoc, Category.assoc]
  exact congrArg (DerivedCategory.Q.map _ ≫ ·) h₂.symm

/-- The term of the extended de Rham complex in degree `a ≥ 0` is the sheaf of `a`-forms with its
coefficients restricted to the base. -/
lemma deRhamCochainComplex_X_eq {Y : Scheme.{u}} (s : Y ⟶ S) (a : ℕ) :
    (show ModuleSheaves (inverseImageBase s) from (deRhamCochainComplex s).X a) =
      (RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase s)).obj
        (Scheme.Hom.relativeDifferentialForms s a) :=
  extend_X_eq (Scheme.Hom.deRhamComplex s) ComplexShape.embeddingUpNat (k := a) rfl

/-- Restricting the coefficients to the base along equal structure morphisms. -/
lemma toInverseImageBase_comp_eqToHom {E : Scheme.{u}} {e₁ e₂ : E ⟶ S} (h : e₁ = e₂) :
    toInverseImageBase e₂ ≫ eqToHom (congrArg inverseImageBase h.symm) = toInverseImageBase e₁ := by
  subst h
  simp

/-- The comparison map on direct images of forms is the component of the graded homomorphism of
Section 07HX. -/
lemma formsDirectImageComparison_eq {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (s : Y ⟶ S) (a : ℤ) :
    Scheme.Hom.formsDirectImageComparison g s a =
      (Scheme.Hom.deRhamFormsPushforwardHom g s (g ≫ s) (𝟙 S) (Category.comp_id _).symm).app a :=
  ((Scheme.Modules.pullbackPushforwardAdjunction g).homEquiv_unit _ _ _).symm.trans
    (Scheme.Hom.homEquiv_relativeDifferentialFormsMap _ _ _ _ _ a)

end Scalars

/-! ### The blowup square -/

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- Restricting the coefficients of `𝒪_E` to the base and then pushing forward along `j` is pushing
forward along `j` and then restricting the coefficients of `𝒪_{X'}`. -/
lemma toInverseImageBase_comp_coefficientInclusion :
    toInverseImageBase (exceptionalStructure f i) ≫ coefficientInclusion f i =
      (exceptionalInclusion i).toLRSHom.toShHom ≫ toInverseImageBase (blowupMap i ≫ f) := by
  rw [coefficientInclusion, ← Category.assoc,
    toInverseImageBase_comp_eqToHom (exceptionalInclusion_comp f i)]
  exact Stacks.DeRhamPullback.toInverseImageBase_relativeBase _ _

/-- **The canonical map `Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S}` of `f^{-1}𝒪_S`-modules is the comparison map on
direct images of forms along `j`, with its coefficients restricted to the base**, as arrows. -/
lemma arrow_mk_inclusionChain_f (a : ℕ) :
    Arrow.mk (show (show ModuleSheaves (inverseImageBase (blowupMap i ≫ f)) from
        (deRhamCochainComplex (blowupMap i ≫ f)).X a) ⟶
          (((RingedSpaceModuleAdjunction.modulePushforward
              (coefficientInclusion f i)).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj (deRhamCochainComplex (exceptionalStructure f i))).X a from
        (inclusionChain f i).f a) =
      Arrow.mk ((RingedSpaceModuleAdjunction.modulePushforward
        (toInverseImageBase (blowupMap i ≫ f))).map
          (Scheme.Hom.formsDirectImageComparison (exceptionalInclusion i)
            (blowupMap i ≫ f) a)) := by
  have hB : (((RingedSpaceModuleAdjunction.modulePushforward
          (coefficientInclusion f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (deRhamCochainComplex (exceptionalStructure f i))).X a =
      (RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase (blowupMap i ≫ f))).obj
        ((Scheme.Modules.pushforward (exceptionalInclusion i)).obj
          (Scheme.Hom.relativeDifferentialForms (exceptionalInclusion i ≫ blowupMap i ≫ f) a)) :=
    (congrArg (RingedSpaceModuleAdjunction.modulePushforward (coefficientInclusion f i)).obj
      (deRhamCochainComplex_X_eq (exceptionalStructure f i) a)).trans
      ((modulePushforward_comp_obj _ _ _).trans
        ((congrArg (fun g => (RingedSpaceModuleAdjunction.modulePushforward g).obj
          (Scheme.Hom.relativeDifferentialForms (exceptionalStructure f i) a))
          (toInverseImageBase_comp_coefficientInclusion f i)).trans
          ((modulePushforward_comp_obj _ _ _).symm.trans
            (congrArg (fun π => (RingedSpaceModuleAdjunction.modulePushforward
              (toInverseImageBase (blowupMap i ≫ f))).obj
                ((Scheme.Modules.pushforward (exceptionalInclusion i)).obj
                  (Scheme.Hom.relativeDifferentialForms π a)))
              (exceptionalInclusion_comp f i).symm))))
  refine arrow_mk_eq_of_val_app_heq (deRhamCochainComplex_X_eq _ a) hB
    ((inclusionChain f i).f a)
    ((RingedSpaceModuleAdjunction.modulePushforward (toInverseImageBase (blowupMap i ≫ f))).map
      (Scheme.Hom.formsDirectImageComparison (exceptionalInclusion i) (blowupMap i ≫ f) a))
    (fun U x x' hx => ?_)
  exact (inclusionChain_f_apply_heq f i a U x x' hx).trans (heq_of_eq (congrArg
    (fun φ => φ.val.app U x')
    (formsDirectImageComparison_eq (exceptionalInclusion i) (blowupMap i ≫ f) a)).symm)

section Clause3

variable [HasDerivedCategory (ModuleSheaves X.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (Stacks.Blowup.blowUp i.ker).toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves Z.toRingedSpace)]
  [HasDerivedCategory (ModuleSheaves (Stacks.Blowup.exceptionalDivisor i.ker).toRingedSpace)]

/-- The comparison of [Stacks, Tag 0FUU] clause (3) is `Rb_*` of the restriction of forms placed in
degree `0`, followed by isomorphisms: if it is invertible on `Hⁿ`, so is `Rb_*` of the restriction
of forms. -/
lemma isIso_homologyFunctor_map_derivedPushforward_blowupFormsRestriction (a n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor _ n).map
      (Stacks.DeRham.blowupFormsRestrictionDerivedComparison f i a))) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((derivedPushforward (blowupMap i).toLRSHom.toShHom).map (DerivedCategory.Q.map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          (Stacks.DeRham.blowupFormsRestriction f i a))))) := by
  unfold Stacks.DeRham.blowupFormsRestrictionDerivedComparison at h
  exact isIso_map_of_isIso_map_comp (DerivedCategory.homologyFunctor _ n) _ _ h

/-- `isIso_homologyFunctor_map_derivedPushforward_blowupFormsRestriction`, for the comparison map
on direct images of forms along `j`, of which the restriction of forms is the transport to the
structure morphism of the exceptional divisor through the centre. -/
lemma isIso_homologyFunctor_map_derivedPushforward_formsDirectImageComparison (a n : ℤ)
    (h : IsIso ((DerivedCategory.homologyFunctor _ n).map
      (Stacks.DeRham.blowupFormsRestrictionDerivedComparison f i a))) :
    IsIso ((DerivedCategory.homologyFunctor _ n).map
      ((derivedPushforward (blowupMap i).toLRSHom.toShHom).map (DerivedCategory.Q.map
        ((HomologicalComplex.single (ModuleSheaves (Stacks.Blowup.blowUp i.ker).toRingedSpace)
          (ComplexShape.up ℤ) 0).map
          (Scheme.Hom.formsDirectImageComparison (exceptionalInclusion i)
            (blowupMap i ≫ f) a))))) := by
  have h₁ := isIso_homologyFunctor_map_derivedPushforward_blowupFormsRestriction f i a n h
  unfold Stacks.DeRham.blowupFormsRestriction at h₁
  exact @isIso_map_of_isIso_map_comp _ _ _ _
    (HomologicalComplex.single (ModuleSheaves (Stacks.Blowup.blowUp i.ker).toRingedSpace)
      (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q ⋙
        derivedPushforward (blowupMap i).toLRSHom.toShHom ⋙
        DerivedCategory.homologyFunctor _ n) _ _ _ _ _ (Functor.map_isIso _ _) h₁

variable [HasDerivedCategory (ModuleSheaves (inverseImageBase f))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (blowupMap i ≫ f)))]

/-- **Clause (3) of [Stacks, Tag 0FUU], read on `f^{-1}𝒪_S`-modules**: if the comparison
`Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` of `𝒪_X`-modules is invertible on cohomology sheaves in
positive degrees for every `a ≥ 0`, then `Rb_*` of the canonical map `Ω^p_{X'/S} ⟶ j_*Ω^p_{E/S}` of
`f^{-1}𝒪_S`-modules is invertible on cohomology sheaves in positive degrees for every `p`. -/
theorem isIso_homologyFunctor_map_inclusionChain_f
    (h : ∀ (a : ℕ) (q : ℤ), 0 < q → IsIso ((DerivedCategory.homologyFunctor _ q).map
      (Stacks.DeRham.blowupFormsRestrictionDerivedComparison f i a))) (p q : ℤ) (hq : 0 < q) :
    IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((derivedPushforward (coefficientBlowup f i)).map (DerivedCategory.Q.map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map
          ((inclusionChain f i).f p))))) := by
  rcases p with a | a
  · have hE := isIso_homologyFunctor_map_derivedPushforward_formsDirectImageComparison f i a q
      (h a q hq)
    have hB := isIso_homologyFunctor_map_derivedPushforward_relativeBase (blowupMap i) f _ q hE
    have hC := (isIso_map_Q_single_map_iff (toInverseImageBase (blowupMap i ≫ f))
      (isClosedEmbedding_toInverseImageBase_base _)
      (derivedPushforward (coefficientBlowup f i) ⋙ DerivedCategory.homologyFunctor _ q)
      (Scheme.Hom.formsDirectImageComparison (exceptionalInclusion i) (blowupMap i ≫ f) a)).2 hB
    exact (congrArg (fun g : Arrow (ModuleSheaves (inverseImageBase (blowupMap i ≫ f))) =>
      IsIso ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q ⋙
        derivedPushforward (coefficientBlowup f i) ⋙
          DerivedCategory.homologyFunctor _ q).map g.hom))
      (arrow_mk_inclusionChain_f f i a)).mpr hC
  · have := isIso_of_deRhamCochainComplex_X_negSucc
      (RingedSpaceModuleAdjunction.modulePushforward (coefficientInclusion f i)) a
      ((inclusionChain f i).f (Int.negSucc a))
    exact ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0 ⋙ DerivedCategory.Q ⋙
      derivedPushforward (coefficientBlowup f i) ⋙ DerivedCategory.homologyFunctor _ q).mapIso
        (@asIso _ _ _ _ _ this)).isIso_hom

variable [HasDerivedCategory (ModuleSheaves (inverseImageBase (i ≫ f)))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (exceptionalStructure f i)))]

/-- **The blowup triangle, from the three clauses of [Stacks, Tag 0FUU] as stated for
`𝒪`-modules**: if for every `a ≥ 0` the comparison maps `Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` and
`Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}` are isomorphisms and `Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` is invertible
on cohomology sheaves in positive degrees, then the four canonical maps, with the sign of the last
one reversed, form a distinguished triangle
`Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S} ⊕ i_*Ω^•_{Z/S} ⟶ i_*Rp_*Ω^•_{E/S} ⟶ Ω^•_{X/S}[1]` in
`D(X, f^{-1}𝒪_S)`. -/
theorem exists_distTriang_of_formsDirectImage
    (h₁ : ∀ a : ℕ, IsIso (Stacks.DeRham.blowupFormsDirectImage i f a))
    (h₂ : ∀ a : ℕ, IsIso (Stacks.DeRham.exceptionalFormsDirectImage i f a))
    (h₃ : ∀ (a : ℕ) (q : ℤ), 0 < q → IsIso ((DerivedCategory.homologyFunctor _ q).map
      (Stacks.DeRham.blowupFormsRestrictionDerivedComparison f i a))) :
    ∃ δ, Triangle.mk (biprod.lift (toBlowUp f i) (toCentre f i))
      (biprod.desc (blowUpToExceptional f i) (-centreToExceptional f i)) δ ∈ distTriang _ :=
  exists_distTriang_of_isIso f i
    (isIso_chain _ _ fun k => (Scheme.Hom.homEquiv_relativeDifferentialFormsMap _ _ _ _ _ k) ▸ h₁ k)
    (isIso_chain _ _ fun k => (Scheme.Hom.homEquiv_relativeDifferentialFormsMap _ _ _ _ _ k) ▸ h₂ k)
    (isIso_homologyFunctor_map_inclusionChain_f f i h₃)

end Clause3

end Stacks.DeRham.BlowupTriangle

end
