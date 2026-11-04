module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDifferentialsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartSchemeModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRepresentableBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSharpChartPullback
import StacksCore.Tactic.StacksAttribute

/-!
# **Stacks 04CS** for a morphism of schemes of the site, on the small étale site of the
represented algebraic space

Let `α : U ⟶ V` be a morphism of schemes of the big fppf site over `S`.  Stacks 04CS is already
proved on the small étale site of the *scheme* `U`:
`AlgebraicGeometry.SmallEtale.differentialsIso` is the canonical isomorphism
`(Ω_{U/V})^a ≅ Ω_{U_étale/V_étale}`.  What the consumers of the final sentence of Stacks 04CU
need is the same statement for the sheaf of differentials of `α` read as a morphism of
*represented algebraic spaces*, `AlgebraicGeometry.Space.sheafOfDifferentials` of
`AlgebraicGeometry.schemeSpaceMap α`.  This module carries the isomorphism across, which proves
`AlgebraicGeometry.Space.SheafOfDifferentialsSchemeComparison` and so supplies the scheme-chart comparison that Stacks 04CV,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_sheafOfDifferentials`, needs.

The two sides live on two identified sites, not on one: the small étale site of the algebraic
space `yoneda.obj U` is the small étale site of the scheme underlying `U` by
`AlgebraicGeometry.Space.representedSmallEtaleEquivalence`, and the transport of modules along
that identification is `AlgebraicGeometry.Space.representedModulePushforward`, which is half of
the equivalence of module categories
`AlgebraicGeometry.Space.representedModuleEquivalence`, imported from
`StacksFrontier/AlgebraicGeometry/Spaces/AffineChartSchemeModuleComparison.lean`.  The transport
carries no content about derivations; what it needs is

* that the identification acts trivially on the structure sheaf, which is what makes that
  equivalence an equivalence: its counit is the *identity*, so the identification composes with
  its inverse to the identity functor on objects and on morphisms alike — the two coherence
  identities are
  `AlgebraicGeometry.Space.representedStructureMap_counit_whiskerRight` and
  `AlgebraicGeometry.Space.representedStructureMap_unit_whiskerRight`; and
* that the two descriptions of the class of relative derivations agree.  Spaces-side the
  vanishing condition is tested on the chartwise pullbacks of regular functions
  (`AlgebraicGeometry.Space.Derivation'.ofChartPullback`); scheme-side it is tested on the
  global functions pulled back along the base-change projections
  (`AlgebraicGeometry.SmallEtale.d_etaleStructureMap_eq_zero`).  Both families are pullbacks of
  regular functions along a projection from a fibre product, and
  `AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent` identifies the two fibre
  products; that identification is the whole of the comparison.

## Main definitions

* `AlgebraicGeometry.Space.transportDerivation` and
  `AlgebraicGeometry.Space.transportDerivationInverse` read a derivation on either of the two
  small étale sites as a derivation on the other.
* `AlgebraicGeometry.Space.transportedDifferentials` is `Ω_{U_étale/V_étale}` transported to the
  small étale site of `yoneda.obj U`, and
  `AlgebraicGeometry.Space.transportedUniversalDerivation` its universal derivation, read as a
  `yoneda.obj V`-derivation.
* `AlgebraicGeometry.Space.chartComparisonMap` is the comparison of the two base changes of a
  chart, read as a morphism of charts of `yoneda.obj U`.
* `AlgebraicGeometry.Space.schemeDifferentialsIso` is the comparison isomorphism itself.

## Main results

* `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_counit_app`: the counit of the
  identification of sites is the identity.  Everything else about the identification used here
  follows from this, in particular
  `AlgebraicGeometry.Space.representedSmallEtaleEquivalence_functor_map_inverse_map`.
* `AlgebraicGeometry.Space.chartPullback_chartBaseChangeArrow`: **the chartwise pullback at the
  base-changed chart is the scheme-level structure map**, restricted along the comparison of the
  two base changes, and `AlgebraicGeometry.Space.structureSharp_eq_map_chartPullback` the same
  read backwards.
* `AlgebraicGeometry.Space.transportDerivation_d_chartPullback_eq_zero` and
  `AlgebraicGeometry.Space.transportDerivationInverse_d_structureSharp_eq_zero`: the two classes
  of derivations agree.
* `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison`: **Stacks 04CS, the
  invertibility clause, for every morphism of schemes of the site**, and
  `AlgebraicGeometry.Space.sheafOfDifferentialsSchemeVanishing` the same at zero objects.

## Implementation notes

The identification of sites is a composite of the Yoneda identification of scheme charts of a
representable presheaf with a slice category and of the comparison of the two étale-ness
conditions, so `e.inverse.obj (e.functor.obj W)` is *not* `W`; the unit is a genuine
isomorphism, and `AlgebraicGeometry.Space.derivation_d_map_unit` is what moves a derivation
across it.  In the other direction `e.functor.obj (e.inverse.obj W)` *is* `W`, and
`e.functor.map (e.inverse.map k)` *is* `k`, which is why
`AlgebraicGeometry.Space.transportDerivation` has an inverse at all and why
`AlgebraicGeometry.Space.transportDerivation_injective` needs nothing.

Two spellings of the small étale site of `yoneda.obj V` occur — the one `chartBaseChange` is
stated at and the one `representedSmallEtaleEquivalence` is stated at — and they are
definitionally but not syntactically equal.  A `rw` whose motive crosses that boundary is not
type-correct at `implicit` transparency, so the comparison of the two descriptions of the
generating sections is assembled from `Eq.trans` and `congrArg` with the intermediate terms
written out, rather than by rewriting.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), whose final sentence is
  that comparison read on a square of étale charts.
* [Stacks Project, Tag 03ED](https://stacks.math.columbia.edu/tag/03ED), the small étale site of
  an algebraic space, and [Tag 03G2](https://stacks.math.columbia.edu/tag/03G2), base change of
  étale charts.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the morphism of small
  étale ringed topoi of a morphism of algebraic spaces, and
  [Tag 070R](https://stacks.math.columbia.edu/tag/070R), the one of a morphism of schemes.
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU), the associated module on
  the small étale site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u u₁ v₁

namespace AlgebraicGeometry.Space

attribute [local instance] BigFppfSite.hasPullbacks_schemes

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section OneObject

variable (U : BigFppfOver B S hS)

/-! ### The equivalence of small étale sites acts trivially on the structure sheaf -/

/-- The counit of the identification of the small étale site of a representable algebraic space
with the small étale site of the underlying scheme is the identity. -/
theorem representedSmallEtaleEquivalence_counit_app
    (W : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property) :
    (representedSmallEtaleEquivalence B S hS U).counitIso.hom.app W = 𝟙 W := rfl

/-- Because the counit is the identity, the functor of the identification carries the unit to an
identity. -/
theorem representedSmallEtaleEquivalence_functor_map_unit (W : SmallEtale B S hS (yoneda.obj U)) :
    (representedSmallEtaleEquivalence B S hS U).functor.map
        ((representedSmallEtaleEquivalence B S hS U).unitIso.hom.app W) =
      𝟙 ((representedSmallEtaleEquivalence B S hS U).functor.obj W) := by
  have h : (representedSmallEtaleEquivalence B S hS U).functor.map
        ((representedSmallEtaleEquivalence B S hS U).unitIso.hom.app W) ≫
      𝟙 ((representedSmallEtaleEquivalence B S hS U).functor.obj W) = 𝟙 _ :=
    (representedSmallEtaleEquivalence B S hS U).functor_unitIso_comp W
  exact (Category.comp_id _).symm.trans h

/-- Because the counit is the identity, the functor of the identification is a retraction of its
inverse on morphisms. -/
theorem representedSmallEtaleEquivalence_functor_map_inverse_map
    {W W' : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property} (k : W ⟶ W') :
    (representedSmallEtaleEquivalence B S hS U).functor.map
        ((representedSmallEtaleEquivalence B S hS U).inverse.map k) = k := by
  have h : (representedSmallEtaleEquivalence B S hS U).functor.map
        ((representedSmallEtaleEquivalence B S hS U).inverse.map k) ≫ 𝟙 W' = 𝟙 W ≫ k :=
    (representedSmallEtaleEquivalence B S hS U).counit.naturality k
  exact (Category.comp_id _).symm.trans (h.trans (Category.id_comp k))

/-- The functor of the identification carries the inverse of the unit to an identity as well. -/
theorem representedSmallEtaleEquivalence_functor_map_unitInv
    (W : SmallEtale B S hS (yoneda.obj U)) :
    (representedSmallEtaleEquivalence B S hS U).functor.map
        ((representedSmallEtaleEquivalence B S hS U).unitIso.inv.app W) = 𝟙 _ := by
  have h1 : (representedSmallEtaleEquivalence B S hS U).functor.map
        ((representedSmallEtaleEquivalence B S hS U).unitIso.inv.app W) ≫
      (representedSmallEtaleEquivalence B S hS U).functor.map
        ((representedSmallEtaleEquivalence B S hS U).unitIso.hom.app W) = 𝟙 _ :=
    Eq.trans (((representedSmallEtaleEquivalence B S hS U).functor.map_comp _ _).symm)
      (Eq.trans (congrArg (representedSmallEtaleEquivalence B S hS U).functor.map
        ((representedSmallEtaleEquivalence B S hS U).unitIso.inv_hom_id_app W))
        (CategoryTheory.Functor.map_id _ _))
  refine (Category.comp_id _).symm.trans (Eq.trans (congrArg
    (fun m => (representedSmallEtaleEquivalence B S hS U).functor.map
      ((representedSmallEtaleEquivalence B S hS U).unitIso.inv.app W) ≫ m)
    (representedSmallEtaleEquivalence_functor_map_unit B S hS U W).symm) h1)

/-- **Restriction of a regular function along the unit of the identification is the identity.**
The functor of the identification carries the unit to an identity, and the structure sheaf of the
small étale site of `yoneda.obj U` is the structure sheaf of the small étale site of the scheme
underlying `U` restricted along that functor, so this is all the unit does to sections. -/
theorem commRingStructureSheaf_map_unit_apply (W : SmallEtale B S hS (yoneda.obj U))
    (x : (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.obj
        (op ((representedSmallEtaleEquivalence B S hS U).functor.obj W))) :
    ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map
      ((representedSmallEtaleEquivalence B S hS U).functor.map
        ((representedSmallEtaleEquivalence B S hS U).unitIso.hom.app W)).op).hom x = x := by
  rw [representedSmallEtaleEquivalence_functor_map_unit]
  change ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map
    (𝟙 (op ((representedSmallEtaleEquivalence B S hS U).functor.obj W)))).hom x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-- **Restriction along the unit of the identification acts as the identity on the sections of a
module on the small étale site of the scheme underlying `U`,** for the same reason. -/
theorem presheaf_map_unit_apply
    (M : SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property))
    (W : SmallEtale B S hS (yoneda.obj U))
    (x : M.val.presheaf.obj (op ((representedSmallEtaleEquivalence B S hS U).functor.obj W))) :
    (M.val.presheaf.map ((representedSmallEtaleEquivalence B S hS U).functor.map
      ((representedSmallEtaleEquivalence B S hS U).unitIso.hom.app W)).op).hom x = x := by
  rw [representedSmallEtaleEquivalence_functor_map_unit]
  change (M.val.presheaf.map
    (𝟙 (op ((representedSmallEtaleEquivalence B S hS U).functor.obj W)))).hom x = x
  rw [CategoryTheory.Functor.map_id]
  rfl

/-! ### Transport of derivations along the identification of small étale sites -/

section Derivations

variable {R : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property)ᵒᵖ ⥤ CommRingCat.{u}}
  (ψ : R ⟶ (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj)
  {M M' : SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
    (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)}

/-- The base of a derivation, transported along the identification of the small étale site of
`yoneda.obj U` with the small étale site of the scheme underlying `U`. -/
noncomputable def transportBase :
    (representedSmallEtaleEquivalence B S hS U).functor.op ⋙ R ⟶
      structurePresheaf B S hS (yoneda.obj U) :=
  Functor.whiskerLeft (representedSmallEtaleEquivalence B S hS U).functor.op ψ

/-- **A derivation on the small étale site of the scheme underlying `U`, read on the small étale
site of the algebraic space `yoneda.obj U`.**  The two sites are identified and the
identification carries the structure sheaf to the structure sheaf, so the sections, the
multiplication and the vanishing condition are unchanged: only the indexing object moves. -/
noncomputable def transportDerivation
    (D : PresheafOfModules.Derivation'
      (R := (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property).obj) M.val ψ) :
    PresheafOfModules.Derivation'
      (R := structurePresheaf B S hS (yoneda.obj U))
      ((representedModulePushforward B S hS U).obj M).val
      (transportBase B S hS U ψ) where
  d {W} := D.d (X := op ((representedSmallEtaleEquivalence B S hS U).functor.obj W.unop))
  d_mul := fun {W} a b =>
    D.d_mul (X := op ((representedSmallEtaleEquivalence B S hS U).functor.obj W.unop)) a b
  d_map := fun {W W'} f x =>
    D.d_map (X := op ((representedSmallEtaleEquivalence B S hS U).functor.obj W.unop))
      (Y := op ((representedSmallEtaleEquivalence B S hS U).functor.obj W'.unop))
      ((representedSmallEtaleEquivalence B S hS U).functor.op.map f) x
  d_app := fun {W} a =>
    D.d_app (X := op ((representedSmallEtaleEquivalence B S hS U).functor.obj W.unop)) a

variable {R' : (SmallEtale B S hS (yoneda.obj U))ᵒᵖ ⥤ CommRingCat.{u}}
  (χ : R' ⟶ structurePresheaf B S hS (yoneda.obj U))
  {N : Modules.{u, u} B S hS (yoneda.obj U) (schemeSpace U).property}

/-- The base of a derivation on the small étale site of `yoneda.obj U`, transported back along
the identification.  The identification composes with its inverse to the identity functor, so
the structure sheaf of the scheme's site is recovered. -/
noncomputable def transportBaseInverse :
    (representedSmallEtaleEquivalence B S hS U).inverse.op ⋙ R' ⟶
      (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj :=
  Functor.whiskerLeft (representedSmallEtaleEquivalence B S hS U).inverse.op χ

/-- **A derivation on the small étale site of `yoneda.obj U`, read on the small étale site of
the scheme underlying `U`**, with values in the module transported along the inverse
identification. -/
noncomputable def transportDerivationInverse
    (D : PresheafOfModules.Derivation'
      (R := structurePresheaf B S hS (yoneda.obj U)) N.val χ) :
    PresheafOfModules.Derivation'
      (R := (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj)
      ((representedModuleRestriction B S hS U).obj N).val
      (transportBaseInverse B S hS U χ) where
  d {W} := D.d (X := op ((representedSmallEtaleEquivalence B S hS U).inverse.obj W.unop))
  d_mul := fun {W} a b =>
    D.d_mul (X := op ((representedSmallEtaleEquivalence B S hS U).inverse.obj W.unop)) a b
  d_map := fun {W W'} f x =>
    D.d_map (X := op ((representedSmallEtaleEquivalence B S hS U).inverse.obj W.unop))
      (Y := op ((representedSmallEtaleEquivalence B S hS U).inverse.obj W'.unop))
      ((representedSmallEtaleEquivalence B S hS U).inverse.op.map f) x
  d_app := fun {W} a =>
    D.d_app (X := op ((representedSmallEtaleEquivalence B S hS U).inverse.obj W.unop)) a

/-- **The unit of the identification shifts the index of a derivation.**  A derivation of a
module on the small étale site of `yoneda.obj U`, evaluated at the image of an object under the
identification and its inverse, is the derivation at the object itself, restricted along the
unit. -/
theorem derivation_d_map_unit
    {N : Modules.{u, u} B S hS (yoneda.obj U) (schemeSpace U).property}
    (D : PresheafOfModules.Derivation'
      (R := structurePresheaf B S hS (yoneda.obj U)) N.val χ)
    (V : (SmallEtale B S hS (yoneda.obj U))ᵒᵖ)
    (x : (structurePresheaf B S hS (yoneda.obj U)).obj V) :
    (N.val.presheaf.map
          ((representedSmallEtaleEquivalence B S hS U).unitIso.hom.app V.unop).op).hom
        (D.d (X := op ((representedSmallEtaleEquivalence B S hS U).inverse.obj
          ((representedSmallEtaleEquivalence B S hS U).functor.obj V.unop))) x) =
      D.d (X := V) x := by
  have h : D.d (X := V)
        (((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map
          ((representedSmallEtaleEquivalence B S hS U).functor.map
            ((representedSmallEtaleEquivalence B S hS U).unitIso.hom.app V.unop)).op).hom x) =
      (N.val.presheaf.map
          ((representedSmallEtaleEquivalence B S hS U).unitIso.hom.app V.unop).op).hom
        (D.d (X := op ((representedSmallEtaleEquivalence B S hS U).inverse.obj
          ((representedSmallEtaleEquivalence B S hS U).functor.obj V.unop))) x) :=
    D.d_map ((representedSmallEtaleEquivalence B S hS U).unitIso.hom.app V.unop).op x
  exact h.symm.trans (congrArg (fun y => D.d (X := V) y)
    (commRingStructureSheaf_map_unit_apply B S hS U V.unop x))

/-- Transport of derivations commutes with postcomposition by a morphism of modules. -/
theorem transportDerivation_postcomp
    (D : PresheafOfModules.Derivation'
      (R := (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property).obj) M.val ψ) (k : M ⟶ M') :
    transportDerivation B S hS U ψ (D.postcomp k.val) =
      (transportDerivation B S hS U ψ D).postcomp
        ((representedModulePushforward B S hS U).map k).val := rfl

/-- **Transport of derivations is injective.**  Every object of the small étale site of the
scheme underlying `U` is the image of one of the small étale site of `yoneda.obj U` — the
identification composes with its inverse to the identity functor — so a derivation is determined
by its transport. -/
theorem transportDerivation_injective
    {D D' : PresheafOfModules.Derivation'
      (R := (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property).obj) M.val ψ}
    (h : transportDerivation B S hS U ψ D = transportDerivation B S hS U ψ D') : D = D' :=
  PresheafOfModules.Derivation.ext (funext fun W => AddMonoidHom.ext fun x =>
    PresheafOfModules.Derivation.congr_d (M := ((representedModulePushforward B S hS U).obj M).val)
      h (X := op ((representedSmallEtaleEquivalence B S hS U).inverse.obj W.unop)) x)

end Derivations

end OneObject

/-- Restriction along an isomorphism of the site, then along its inverse, is the identity on
sections of a presheaf of commutative rings. -/
theorem commRingPresheaf_map_iso_inv_hom_apply {C : Type u₁} [Category.{v₁} C]
    (F : Cᵒᵖ ⥤ CommRingCat.{u}) {W W' : C} (c : W ≅ W') (x : F.obj (op W')) :
    (F.map c.inv.op).hom ((F.map c.hom.op).hom x) = x := by
  have h : F.map c.hom.op ≫ F.map c.inv.op = 𝟙 _ := by
    rw [← F.map_comp, ← op_comp, Iso.inv_hom_id, op_id, CategoryTheory.Functor.map_id]
  exact congrArg (fun f : F.obj (op W') ⟶ F.obj (op W') => f.hom x) h

/-! ### The chartwise pullbacks and the scheme-level structure map -/

section Comparison

variable {U V : BigFppfOver B S hS} (α : U ⟶ V)

/-- Pullback of a global regular function along a composite of morphisms of schemes, on
sections. -/
theorem gamma_comp_apply {X Y Z : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ Z)
    (t : Scheme.Γ.obj (op Z)) :
    (Scheme.Γ.map (a ≫ b).op).hom t = (Scheme.Γ.map a.op).hom ((Scheme.Γ.map b.op).hom t) := by
  rw [op_comp, Scheme.Γ.map_comp]
  rfl

/-- Pullback of a global regular function along equal morphisms of schemes agrees. -/
theorem gamma_congr_apply {X Y : Scheme.{u}} {a b : X ⟶ Y} (h : a = b)
    (t : Scheme.Γ.obj (op Y)) :
    (Scheme.Γ.map a.op).hom t = (Scheme.Γ.map b.op).hom t := by rw [h]

/-- The chartwise pullback of a regular function is pullback along the induced morphism of
schemes. -/
theorem chartPullback_eq_gamma (V₀ : SmallEtale B S hS (schemeSpace V).obj)
    (j : StructuredArrow (op (chartBaseChange B S hS (schemeSpaceMap α) V₀))
      (comparisonFunctor B S hS (schemeSpace U)).op)
    (t : (structureSetSheaf B S hS (schemeSpace V)).obj.obj (op V₀)) :
    chartPullback B S hS (schemeSpaceMap α) V₀ j t =
      (Scheme.Γ.map ((associatedBigEtaleSite B).inclusion.map
        (chartBaseChangeMap B S hS (schemeSpaceMap α) V₀ j).left).op).hom t := rfl

/-- Restriction along a morphism of the small étale site of a scheme of the site is pullback of
global regular functions. -/
theorem commRingStructureSheaf_map_eq_gamma (X : Scheme.{u})
    (hX : (associatedBigEtaleSite B).Contains X)
    {W W' : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B) X hX} (k : W ⟶ W')
    (x : (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
      (associatedBigEtaleSite B) X hX).obj.obj (op W')) :
    ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
        (associatedBigEtaleSite B) X hX).obj.map k.op).hom x =
      (Scheme.Γ.map ((associatedBigEtaleSite B).inclusion.map k.hom.left).op).hom x := rfl

/-- The scheme-level structure map is pullback of global regular functions along the base-change
projection, on sections. -/
theorem structureSharp_app_eq_gamma
    (W : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property)
    (t : (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj V) V.left.property).obj.obj (op W)) :
    ((_root_.AlgebraicGeometry.structureSharp (associatedBigEtaleSite B) α.left).hom.app
        (op W)).hom t =
      (Scheme.Γ.map ((associatedBigEtaleSite B).inclusion.map
        (pullback.fst W.obj.hom α.left)).op).hom t := rfl

/-- Restriction along equal morphisms of the small étale site of a scheme of the site agrees on
sections. -/
theorem commRingStructureSheaf_map_congr_apply (X : Scheme.{u})
    (hX : (associatedBigEtaleSite B).Contains X)
    {W W' : _root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B) X hX} {k k' : W ⟶ W'}
    (h : k = k')
    (x : (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
      (associatedBigEtaleSite B) X hX).obj.obj (op W')) :
    ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
        (associatedBigEtaleSite B) X hX).obj.map k.op).hom x =
      ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
        (associatedBigEtaleSite B) X hX).obj.map k'.op).hom x := by
  rw [h]

/-- The comparison of the two base changes of a chart is compatible with the projections to the
chart. -/
theorem component_hom_comp_fst (V₀ : SmallEtale B S hS (schemeSpace V).obj) :
    (representedSmallEtaleBaseChangeComponent B S hS α
          (relativelyRepresentable_yoneda_map B S hS α) V₀).hom.hom.left ≫
        pullback.fst ((representedSmallEtaleEquivalence B S hS V).functor.obj V₀).obj.hom α.left =
      ((relativelyRepresentable_yoneda_map B S hS α).snd V₀.1.hom).left :=
  (isPullback_representedChart_schemes B S hS α
    (relativelyRepresentable_yoneda_map B S hS α) V₀).isoIsPullback_hom_fst _ _ _

/-- **The chartwise pullback at the base-changed chart is the scheme-level structure map**,
restricted along the comparison of the two base changes.

The base-changed chart of the represented morphism and the base change of the underlying scheme
chart are two fibre products of one cospan, and
`AlgebraicGeometry.Space.representedSmallEtaleBaseChangeComponent` identifies them over the
chart; both the chartwise pullback of Stacks 03G8 and the scheme-level structure map of
Stacks 070R are pullback of global regular functions along the projection to the chart. -/
theorem chartPullback_chartBaseChangeArrow (V₀ : SmallEtale B S hS (schemeSpace V).obj)
    (t : (structureSetSheaf B S hS (schemeSpace V)).obj.obj (op V₀)) :
    chartPullback B S hS (schemeSpaceMap α) V₀
        (chartBaseChangeArrow B S hS (schemeSpaceMap α)
          (relativelyRepresentable_yoneda_map B S hS α) V₀) t =
      ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
            ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map
          (representedSmallEtaleBaseChangeComponent B S hS α
            (relativelyRepresentable_yoneda_map B S hS α) V₀).hom.op).hom
        (((_root_.AlgebraicGeometry.structureSharp (associatedBigEtaleSite B) α.left).hom.app
          (op ((representedSmallEtaleEquivalence B S hS V).functor.obj V₀))).hom t) := by
  have key : (associatedBigEtaleSite B).inclusion.map
        (chartBaseChangeMap B S hS (schemeSpaceMap α) V₀
          (chartBaseChangeArrow B S hS (schemeSpaceMap α)
            (relativelyRepresentable_yoneda_map B S hS α) V₀)).left =
      (associatedBigEtaleSite B).inclusion.map
          (representedSmallEtaleBaseChangeComponent B S hS α
            (relativelyRepresentable_yoneda_map B S hS α) V₀).hom.hom.left ≫
        (associatedBigEtaleSite B).inclusion.map
          (pullback.fst ((representedSmallEtaleEquivalence B S hS V).functor.obj V₀).obj.hom
            α.left) := by
    refine Eq.trans (congrArg (fun m => (associatedBigEtaleSite B).inclusion.map m.left)
      (chartBaseChangeMap_chartBaseChangeArrow B S hS (schemeSpaceMap α)
        (relativelyRepresentable_yoneda_map B S hS α) V₀)) ?_
    exact Eq.trans (congrArg (associatedBigEtaleSite B).inclusion.map
        (component_hom_comp_fst B S hS α V₀).symm)
      ((associatedBigEtaleSite B).inclusion.map_comp _ _)
  refine Eq.trans (chartPullback_eq_gamma B S hS α V₀ _ t) ?_
  refine Eq.trans (gamma_congr_apply key t) ?_
  refine Eq.trans (gamma_comp_apply ((associatedBigEtaleSite B).inclusion.map
      (representedSmallEtaleBaseChangeComponent B S hS α
        (relativelyRepresentable_yoneda_map B S hS α) V₀).hom.hom.left)
    ((associatedBigEtaleSite B).inclusion.map
      (pullback.fst ((representedSmallEtaleEquivalence B S hS V).functor.obj V₀).obj.hom α.left))
    t) ?_
  refine Eq.trans ?_ (congrArg (fun y =>
    ((_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj.map
      (representedSmallEtaleBaseChangeComponent B S hS α
        (relativelyRepresentable_yoneda_map B S hS α) V₀).hom.op).hom y)
    (structureSharp_app_eq_gamma B S hS α
      ((representedSmallEtaleEquivalence B S hS V).functor.obj V₀) t).symm)
  exact (commRingStructureSheaf_map_eq_gamma B ((BigFppfOver.toScheme B S hS).obj U)
    U.left.property (representedSmallEtaleBaseChangeComponent B S hS α
      (relativelyRepresentable_yoneda_map B S hS α) V₀).hom _).symm

/-- A derivation kills every restriction of a section that it kills. -/
private theorem derivation_d_eq_zero_of_eq_map
    {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}
    {M : PresheafOfModules.{u} (R ⋙ forget₂ _ _)} {S' : Cᵒᵖ ⥤ CommRingCat.{u}} {φ' : S' ⟶ R}
    (D : PresheafOfModules.Derivation' (R := R) M φ') {X Y : Cᵒᵖ} (f : X ⟶ Y)
    {x : R.obj X} {y : R.obj Y} (h : y = R.map f x) (hx : D.d x = 0) : D.d y = 0 := by
  rw [h, D.d_map, hx]
  exact map_zero _

/-- **A derivation of a module on the small étale site of the scheme underlying `U` which kills
the image of the scheme-level structure map of `α` transports to one which kills every chartwise
pullback of a regular function.**

At the base-changed chart the chartwise pullback *is* the scheme-level structure map, restricted
along the comparison of the two base changes
(`AlgebraicGeometry.Space.chartPullback_chartBaseChangeArrow`); every other chart of `U` above
`U ×_V V₀` receives a morphism from the base-changed one, which is initial, so its chartwise
pullback is a restriction of that one. -/
theorem transportDerivation_d_chartPullback_eq_zero
    {M : SheafOfModules.{u} (_root_.AlgebraicGeometry.SmallEtale.structureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property)}
    {R : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property)ᵒᵖ ⥤ CommRingCat.{u}}
    {ψ : R ⟶ (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
      (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj}
    (D : PresheafOfModules.Derivation'
      (R := (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
        (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj U)
        U.left.property).obj) M.val ψ)
    (hD : ∀ (W : (_root_.AlgebraicGeometry.SmallEtale (associatedBigEtaleSite B)
        ((BigFppfOver.toScheme B S hS).obj V) V.left.property)ᵒᵖ)
        (t : (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf
          (associatedBigEtaleSite B) ((BigFppfOver.toScheme B S hS).obj V)
          V.left.property).obj.obj W),
      D.d (X := op ((_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B)
          α.left).obj W.unop))
        (((_root_.AlgebraicGeometry.structureSharp (associatedBigEtaleSite B)
          α.left).hom.app W).hom t) = 0)
    (V₀ : SmallEtale B S hS (schemeSpace V).obj)
    (j : StructuredArrow (op (chartBaseChange B S hS (schemeSpaceMap α) V₀))
      (comparisonFunctor B S hS (schemeSpace U)).op)
    (t : (structureSetSheaf B S hS (schemeSpace V)).obj.obj (op V₀)) :
    (transportDerivation B S hS U ψ D).d
      (chartPullback B S hS (schemeSpaceMap α) V₀ j t) = 0 := by
  have hinit : (transportDerivation B S hS U ψ D).d
      (chartPullback B S hS (schemeSpaceMap α) V₀
        (chartBaseChangeArrow B S hS (schemeSpaceMap α)
          (relativelyRepresentable_yoneda_map B S hS α) V₀) t) = 0 :=
    derivation_d_eq_zero_of_eq_map D (representedSmallEtaleBaseChangeComponent B S hS α
      (relativelyRepresentable_yoneda_map B S hS α) V₀).hom.op
      (chartPullback_chartBaseChangeArrow B S hS α V₀ t)
      (hD (op ((representedSmallEtaleEquivalence B S hS V).functor.obj V₀)) t)
  exact derivation_d_eq_zero_of_eq_map (transportDerivation B S hS U ψ D)
    (chartBaseChangeArrowHom B S hS (schemeSpaceMap α)
      (relativelyRepresentable_yoneda_map B S hS α) V₀ j).right
    (congrArg (fun f => f t) (chartPullback_comp B S hS (schemeSpaceMap α) V₀
      (chartBaseChangeArrowHom B S hS (schemeSpaceMap α)
        (relativelyRepresentable_yoneda_map B S hS α) V₀ j))) hinit

/-- The comparison of the two base changes of a chart, read as a morphism of charts of
`yoneda.obj U`: the base change of the underlying scheme chart, pulled back along the
identification of sites, maps to the chart base change. -/
noncomputable def chartComparisonMap (V₀ : SmallEtale B S hS (schemeSpace V).obj) :
    (representedSmallEtaleEquivalence B S hS U).inverse.obj
        ((_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B) α.left).obj
          ((representedSmallEtaleEquivalence B S hS V).functor.obj V₀)) ⟶
      (smallBaseChange B S hS (schemeSpaceMap α)
        (relativelyRepresentable_yoneda_map B S hS α)).obj V₀ :=
  (representedSmallEtaleEquivalence B S hS U).inverse.map
      (representedSmallEtaleBaseChangeComponent B S hS α
        (relativelyRepresentable_yoneda_map B S hS α) V₀).inv ≫
    (representedSmallEtaleEquivalence B S hS U).unitIso.inv.app _

/-- The identification of small étale sites carries
`AlgebraicGeometry.Space.chartComparisonMap` to the inverse of the comparison of the two base
changes: it is that inverse, transported along the inverse identification, and the unit becomes
an identity. -/
theorem functor_map_chartComparisonMap (V₀ : SmallEtale B S hS (schemeSpace V).obj) :
    (representedSmallEtaleEquivalence B S hS U).functor.map (chartComparisonMap B S hS α V₀) =
      (representedSmallEtaleBaseChangeComponent B S hS α
        (relativelyRepresentable_yoneda_map B S hS α) V₀).inv := by
  refine Eq.trans ((representedSmallEtaleEquivalence B S hS U).functor.map_comp _ _) ?_
  refine Eq.trans (congrArg (fun m => m ≫ (representedSmallEtaleEquivalence B S hS U).functor.map
      ((representedSmallEtaleEquivalence B S hS U).unitIso.inv.app
        ((smallBaseChange B S hS (schemeSpaceMap α)
          (relativelyRepresentable_yoneda_map B S hS α)).obj V₀)))
    (representedSmallEtaleEquivalence_functor_map_inverse_map B S hS U
      (representedSmallEtaleBaseChangeComponent B S hS α
        (relativelyRepresentable_yoneda_map B S hS α) V₀).inv)) ?_
  refine Eq.trans (congrArg (fun m => (representedSmallEtaleBaseChangeComponent B S hS α
      (relativelyRepresentable_yoneda_map B S hS α) V₀).inv ≫ m)
    (representedSmallEtaleEquivalence_functor_map_unitInv B S hS U
      ((smallBaseChange B S hS (schemeSpaceMap α)
        (relativelyRepresentable_yoneda_map B S hS α)).obj V₀))) ?_
  exact Category.comp_id _

/-- **The scheme-level structure map of `α` is a chartwise pullback of a regular function,**
restricted along `AlgebraicGeometry.Space.chartComparisonMap`.  This is
`AlgebraicGeometry.Space.chartPullback_chartBaseChangeArrow` read backwards, the comparison of
the two base changes being invertible. -/
theorem structureSharp_eq_map_chartPullback (V₀ : SmallEtale B S hS (schemeSpace V).obj)
    (t : (structureSetSheaf B S hS (schemeSpace V)).obj.obj (op V₀)) :
    ((structurePresheaf B S hS (yoneda.obj U)).map
          (chartComparisonMap B S hS α V₀).op).hom
        (chartPullback B S hS (schemeSpaceMap α) V₀
          (chartBaseChangeArrow B S hS (schemeSpaceMap α)
            (relativelyRepresentable_yoneda_map B S hS α) V₀) t) =
      ((_root_.AlgebraicGeometry.structureSharp (associatedBigEtaleSite B) α.left).hom.app
        (op ((representedSmallEtaleEquivalence B S hS V).functor.obj V₀))).hom t := by
  refine Eq.trans (congrArg (fun y => ((structurePresheaf B S hS (yoneda.obj U)).map
      (chartComparisonMap B S hS α V₀).op).hom y)
    (chartPullback_chartBaseChangeArrow B S hS α V₀ t)) ?_
  refine Eq.trans (commRingStructureSheaf_map_congr_apply B
    ((BigFppfOver.toScheme B S hS).obj U) U.left.property
    (functor_map_chartComparisonMap B S hS α V₀) _) ?_
  exact commRingPresheaf_map_iso_inv_hom_apply
    (_root_.AlgebraicGeometry.SmallEtale.commRingStructureSheaf (associatedBigEtaleSite B)
      ((BigFppfOver.toScheme B S hS).obj U) U.left.property).obj
    (representedSmallEtaleBaseChangeComponent B S hS α
      (relativelyRepresentable_yoneda_map B S hS α) V₀) _

/-- **A derivation of a module on the small étale site of `yoneda.obj U` which kills every
chartwise pullback of a regular function transports back to one which kills the image of the
scheme-level structure map of `α`.**

By `AlgebraicGeometry.Space.structureSharp_eq_map_chartPullback` the structure map at a chart is
the chartwise pullback at the base-changed chart, restricted along a morphism of charts, and a
derivation commutes with restriction. -/
theorem transportDerivationInverse_d_structureSharp_eq_zero
    {N : Modules.{u, u} B S hS (yoneda.obj U) (schemeSpace U).property}
    {R' : (SmallEtale B S hS (yoneda.obj U))ᵒᵖ ⥤ CommRingCat.{u}}
    (χ : R' ⟶ structurePresheaf B S hS (yoneda.obj U))
    (D : PresheafOfModules.Derivation'
      (R := structurePresheaf B S hS (yoneda.obj U)) N.val χ)
    (hD : ∀ (V₁ : SmallEtale B S hS (schemeSpace V).obj)
        (j : StructuredArrow (op (chartBaseChange B S hS (schemeSpaceMap α) V₁))
          (comparisonFunctor B S hS (schemeSpace U)).op)
        (s : (structureSetSheaf B S hS (schemeSpace V)).obj.obj (op V₁)),
      D.d (chartPullback B S hS (schemeSpaceMap α) V₁ j s) = 0)
    (V₀ : SmallEtale B S hS (schemeSpace V).obj)
    (t : (structureSetSheaf B S hS (schemeSpace V)).obj.obj (op V₀)) :
    (transportDerivationInverse B S hS U χ D).d
        (X := op ((_root_.AlgebraicGeometry.smallEtaleBaseChange (associatedBigEtaleSite B)
          α.left).obj ((representedSmallEtaleEquivalence B S hS V).functor.obj V₀)))
      (((_root_.AlgebraicGeometry.structureSharp (associatedBigEtaleSite B) α.left).hom.app
        (op ((representedSmallEtaleEquivalence B S hS V).functor.obj V₀))).hom t) = 0 := by
  exact derivation_d_eq_zero_of_eq_map D (chartComparisonMap B S hS α V₀).op
    (structureSharp_eq_map_chartPullback B S hS α V₀ t).symm
    (hD V₀ (chartBaseChangeArrow B S hS (schemeSpaceMap α)
      (relativelyRepresentable_yoneda_map B S hS α) V₀) t)

/-! ### The comparison -/

/-- **`Ω_{U_étale/V_étale}`, transported to the small étale site of the represented algebraic
space `yoneda.obj U`.** -/
noncomputable abbrev transportedDifferentials :
    Modules.{u, u} B S hS (yoneda.obj U) (schemeSpace U).property :=
  (representedModulePushforward B S hS U).obj
    (_root_.AlgebraicGeometry.SmallEtale.sheafOfDifferentials (associatedBigEtaleSite B) α.left)

/-- **The universal `V_étale`-derivation, transported to the small étale site of `yoneda.obj U`
and read as a `yoneda.obj V`-derivation.**  Its values are those of
`AlgebraicGeometry.SmallEtale.universalDerivation`; what has to be checked is the vanishing
condition over the spaces-level structure map, and that is
`AlgebraicGeometry.Space.transportDerivation_d_chartPullback_eq_zero` together with
`AlgebraicGeometry.Space.Derivation'.ofChartPullback`. -/
noncomputable def transportedUniversalDerivation :
    PresheafOfModules.Derivation' (R := structurePresheaf B S hS (yoneda.obj U))
      (transportedDifferentials B S hS α).val
      (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom :=
  Derivation'.ofChartPullback B S hS (schemeSpaceMap α)
    (transportDerivation B S hS U
      (_root_.AlgebraicGeometry.SmallEtale.etaleStructureMap (associatedBigEtaleSite B)
        α.left).hom
      (_root_.AlgebraicGeometry.SmallEtale.universalDerivation (associatedBigEtaleSite B) α.left))
    (transportDerivation_d_chartPullback_eq_zero B S hS α
      (_root_.AlgebraicGeometry.SmallEtale.universalDerivation (associatedBigEtaleSite B) α.left)
      (fun W t => _root_.AlgebraicGeometry.SmallEtale.d_structureSharp_eq_zero
        (associatedBigEtaleSite B) α.left
        (_root_.AlgebraicGeometry.SmallEtale.universalDerivation
          (associatedBigEtaleSite B) α.left)
        (fun _ s => PresheafOfModules.Derivation'.d_app _ s) W t))

/-- **The universal `yoneda.obj V`-derivation of `𝒪_{yoneda.obj U}`, read on the small étale site
of the scheme underlying `U` as a `V_étale`-derivation.**  Again the values are unchanged; the
vanishing condition over the scheme-level structure map is
`AlgebraicGeometry.Space.transportDerivationInverse_d_structureSharp_eq_zero` together with
`AlgebraicGeometry.SmallEtale.d_etaleStructureMap_eq_zero`. -/
noncomputable def inverseEtaleDerivation :
    _root_.AlgebraicGeometry.SmallEtale.EtaleDerivation (associatedBigEtaleSite B) α.left
      ((representedModuleRestriction B S hS U).obj
        (sheafOfDifferentials B S hS (schemeSpaceMap α))) where
  d := (transportDerivationInverse B S hS U
    (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom
    (universalDerivation B S hS (schemeSpaceMap α))).d
  d_mul := (transportDerivationInverse B S hS U
    (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom
    (universalDerivation B S hS (schemeSpaceMap α))).d_mul
  d_map := (transportDerivationInverse B S hS U
    (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom
    (universalDerivation B S hS (schemeSpaceMap α))).d_map
  d_app := fun {W} s =>
    _root_.AlgebraicGeometry.SmallEtale.d_etaleStructureMap_eq_zero (associatedBigEtaleSite B)
      α.left
      (transportDerivationInverse B S hS U
        (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom
        (universalDerivation B S hS (schemeSpaceMap α)))
      (fun W' t => transportDerivationInverse_d_structureSharp_eq_zero B S hS α
        (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom
        (universalDerivation B S hS (schemeSpaceMap α))
        (fun V₁ j s => derivation_d_chartPullback_eq_zero B S hS (schemeSpaceMap α)
          (universalDerivation B S hS (schemeSpaceMap α)) V₁ j s)
        ((representedSmallEtaleEquivalence B S hS V).inverse.obj W'.unop) t)
      W s

/-- The universal `V_étale`-derivation of `𝒪_{U_étale}`, transported to the small étale site of
`yoneda.obj U` but still read over the scheme-level structure map. -/
noncomputable abbrev transportedEtaleDerivation :=
  transportDerivation B S hS U
    (_root_.AlgebraicGeometry.SmallEtale.etaleStructureMap (associatedBigEtaleSite B) α.left).hom
    (_root_.AlgebraicGeometry.SmallEtale.universalDerivation (associatedBigEtaleSite B) α.left)

/-- **The comparison morphism** `Ω_{yoneda U/yoneda V} ⟶ Ω_{U_étale/V_étale}`: the morphism
through which the transported universal derivation factors. -/
noncomputable def schemeDifferentialsHom :
    sheafOfDifferentials B S hS (schemeSpaceMap α) ⟶ transportedDifferentials B S hS α :=
  Classical.choose (universalDerivation_isUniversal B S hS (schemeSpaceMap α)
    (transportedDifferentials B S hS α) (transportedUniversalDerivation B S hS α))

/-- The comparison morphism carries the universal `yoneda.obj V`-derivation to the transported
universal `V_étale`-derivation. -/
theorem postcomp_schemeDifferentialsHom :
    (universalDerivation B S hS (schemeSpaceMap α)).postcomp
        (schemeDifferentialsHom B S hS α).val =
      transportedUniversalDerivation B S hS α :=
  (Classical.choose_spec (universalDerivation_isUniversal B S hS (schemeSpaceMap α)
    (transportedDifferentials B S hS α) (transportedUniversalDerivation B S hS α))).1

/-- **The comparison morphism in the other direction**: the transport of the morphism through
which the universal `yoneda.obj V`-derivation, read on the scheme side, factors. -/
noncomputable def schemeDifferentialsInv :
    transportedDifferentials B S hS α ⟶ sheafOfDifferentials B S hS (schemeSpaceMap α) :=
  (representedModulePushforward B S hS U).map
      (Classical.choose (_root_.AlgebraicGeometry.SmallEtale.universalDerivation_isUniversal
        (associatedBigEtaleSite B) α.left
        ((representedModuleRestriction B S hS U).obj
          (sheafOfDifferentials B S hS (schemeSpaceMap α)))
        (inverseEtaleDerivation B S hS α))) ≫
    (representedModuleEquivalence.{u, u} B S hS U).counit.app
      (sheafOfDifferentials B S hS (schemeSpaceMap α))

/-- The second comparison morphism carries the transported universal `V_étale`-derivation to the
universal `yoneda.obj V`-derivation.

On sections this is the factorization on the scheme side, followed by the counit of the
equivalence of module categories, which is restriction along the unit of the identification of
sites; `AlgebraicGeometry.Space.derivation_d_map_unit` is what that restriction does to a
derivation. -/
theorem postcomp_schemeDifferentialsInv :
    (transportedUniversalDerivation B S hS α).postcomp (schemeDifferentialsInv B S hS α).val =
      universalDerivation B S hS (schemeSpaceMap α) := by
  refine PresheafOfModules.Derivation.ext (funext fun Vop => AddMonoidHom.ext fun x => ?_)
  refine Eq.trans (congrArg (fun z => (((representedModuleEquivalence.{u, u} B S hS U).counit.app
      (sheafOfDifferentials B S hS (schemeSpaceMap α))).val.app Vop).hom z)
    (PresheafOfModules.Derivation.congr_d
      (Classical.choose_spec (_root_.AlgebraicGeometry.SmallEtale.universalDerivation_isUniversal
        (associatedBigEtaleSite B) α.left
        ((representedModuleRestriction B S hS U).obj
          (sheafOfDifferentials B S hS (schemeSpaceMap α)))
        (inverseEtaleDerivation B S hS α))).1
      (X := op ((representedSmallEtaleEquivalence B S hS U).functor.obj Vop.unop)) x)) ?_
  exact derivation_d_map_unit B S hS U
    (structureSharpInverseImage B S hS (schemeSpaceMap α)).hom
    (universalDerivation B S hS (schemeSpaceMap α)) Vop x

/-- Postcomposing a derivation by a composite, when each of the two steps is known on sections. -/
private theorem derivation_postcomp_comp_eq
    {C : Type u₁} [Category.{v₁} C] {R S' S'' : Cᵒᵖ ⥤ CommRingCat.{u}} {φ' : S' ⟶ R}
    {φ'' : S'' ⟶ R} {M M' M'' : PresheafOfModules.{u} (R ⋙ forget₂ _ _)}
    {D : PresheafOfModules.Derivation' (R := R) M φ'}
    {D' : PresheafOfModules.Derivation' (R := R) M' φ''}
    {D'' : PresheafOfModules.Derivation' (R := R) M'' φ'} {f : M ⟶ M'} {g : M' ⟶ M''}
    (h : ∀ {X} (x : R.obj X), (f.app X).hom (D.d x) = D'.d x)
    (h' : ∀ {X} (x : R.obj X), (g.app X).hom (D'.d x) = D''.d x) : D.postcomp (f ≫ g) = D'' :=
  PresheafOfModules.Derivation.ext (funext fun _ => AddMonoidHom.ext fun x =>
    (congrArg (g.app _).hom (h x)).trans (h' x))

/-- The two comparison morphisms compose to the identity of `Ω_{yoneda U/yoneda V}`: both that
composite and the identity carry the universal derivation to itself, and only one morphism
does. -/
theorem schemeDifferentialsHom_comp_inv :
    schemeDifferentialsHom B S hS α ≫ schemeDifferentialsInv B S hS α = 𝟙 _ := by
  obtain ⟨g, hg, hu⟩ := universalDerivation_isUniversal B S hS (schemeSpaceMap α)
    (sheafOfDifferentials B S hS (schemeSpaceMap α))
    (universalDerivation B S hS (schemeSpaceMap α))
  refine (hu _ ?_).trans (hu _ ?_).symm
  · exact derivation_postcomp_comp_eq
      (fun x => PresheafOfModules.Derivation.congr_d (postcomp_schemeDifferentialsHom B S hS α) x)
      (fun x => PresheafOfModules.Derivation.congr_d (postcomp_schemeDifferentialsInv B S hS α) x)
  · exact PresheafOfModules.Derivation.ext (funext fun _ => AddMonoidHom.ext fun _ => rfl)

/-- The two comparison morphisms compose to the identity of the transported module as well.
Transport of modules along the identification of the two small étale sites is an equivalence, so
the composite is the transport of a unique endomorphism of `Ω_{U_étale/V_étale}`; that
endomorphism carries the universal derivation to itself, so it is the identity. -/
theorem schemeDifferentialsInv_comp_hom :
    schemeDifferentialsInv B S hS α ≫ schemeDifferentialsHom B S hS α = 𝟙 _ := by
  have : (representedModulePushforward B S hS U).Full :=
    Equivalence.full_functor (representedModuleEquivalence.{u, u} B S hS U)
  obtain ⟨m, hGm⟩ : ∃ m, (representedModulePushforward B S hS U).map m =
      schemeDifferentialsInv B S hS α ≫ schemeDifferentialsHom B S hS α :=
    ⟨(representedModulePushforward B S hS U).preimage _, Functor.map_preimage _ _⟩
  obtain ⟨g, hg, hu⟩ := _root_.AlgebraicGeometry.SmallEtale.universalDerivation_isUniversal
    (associatedBigEtaleSite B) α.left
    (_root_.AlgebraicGeometry.SmallEtale.sheafOfDifferentials (associatedBigEtaleSite B) α.left)
    (_root_.AlgebraicGeometry.SmallEtale.universalDerivation (associatedBigEtaleSite B) α.left)
  have hm : m = 𝟙 _ := by
    refine (hu m ?_).trans (hu (𝟙 _) ?_).symm
    · refine transportDerivation_injective B S hS U
        (_root_.AlgebraicGeometry.SmallEtale.etaleStructureMap (associatedBigEtaleSite B)
          α.left).hom ?_
      refine Eq.trans (transportDerivation_postcomp B S hS U
        (_root_.AlgebraicGeometry.SmallEtale.etaleStructureMap (associatedBigEtaleSite B)
          α.left).hom
        (_root_.AlgebraicGeometry.SmallEtale.universalDerivation (associatedBigEtaleSite B)
          α.left) m) ?_
      refine Eq.trans (congrArg (fun n => (transportedEtaleDerivation B S hS α).postcomp n.val)
        hGm) ?_
      exact derivation_postcomp_comp_eq
        (fun x => PresheafOfModules.Derivation.congr_d (postcomp_schemeDifferentialsInv B S hS α) x)
        (fun x => PresheafOfModules.Derivation.congr_d (postcomp_schemeDifferentialsHom B S hS α) x)
    · exact PresheafOfModules.Derivation.ext (funext fun _ => AddMonoidHom.ext fun _ => rfl)
  exact hGm.symm.trans ((congrArg (representedModulePushforward B S hS U).map hm).trans
    ((representedModulePushforward B S hS U).map_id _))

/-- **The invertibility clause of Stacks 04CS for a morphism `α : U ⟶ V` of schemes of the big
fppf site over `S`**, in the form of the transported module of differentials: the sheaf of
differentials of `α` read as a morphism of represented algebraic spaces is
`Ω_{U_étale/V_étale}`, transported along the identification of the small étale site of
`yoneda.obj U` with that of the scheme underlying `U`. -/
noncomputable def schemeDifferentialsIso :
    sheafOfDifferentials B S hS (schemeSpaceMap α) ≅ transportedDifferentials B S hS α where
  hom := schemeDifferentialsHom B S hS α
  inv := schemeDifferentialsInv B S hS α
  hom_inv_id := schemeDifferentialsHom_comp_inv B S hS α
  inv_hom_id := schemeDifferentialsInv_comp_hom B S hS α

end Comparison

/-! ### Stacks 04CS, spaces-side -/

/-- **Stacks 04CS, the invertibility clause, for every morphism of schemes of the big fppf site
over `S`.**  For a morphism `α : U ⟶ V` of schemes of the site, the sheaf of differentials of
`α` read as a morphism of represented algebraic spaces — the module of differentials on the
small étale site of `yoneda.obj U` — is the small-étale module attached by Stacks 03DU (4) to
the Zariski sheaf of relative differentials `Ω_{U/V}` of Stacks 01US.

This is the hypothesis `AlgebraicGeometry.Space.SheafOfDifferentialsSchemeComparison`, which the
consumers of the final sentence of Stacks 04CU need.  It is
`AlgebraicGeometry.SmallEtale.differentialsIso`, the canonical isomorphism
`(Ω_{U/V})^a ≅ Ω_{U_étale/V_étale}` of Stacks 04CS, transported along the identification of the
small étale site of `yoneda.obj U` with the small étale site of the scheme underlying `U`
(`AlgebraicGeometry.Space.schemeDifferentialsIso`). -/
@[stacks 04CS "the invertibility clause, for a morphism of schemes of the site read on the small
  étale site of the represented algebraic space"]
theorem sheafOfDifferentialsSchemeComparison :
    SheafOfDifferentialsSchemeComparison B S hS := fun U _ α =>
  ⟨schemeDifferentialsIso B S hS α ≪≫ (representedModulePushforward B S hS U).mapIso
    (_root_.AlgebraicGeometry.SmallEtale.differentialsIso (associatedBigEtaleSite B)
      α.left).symm⟩

add_to_stacks 04CU "the 'in particular' clause: for `U` and `V` schemes of the site the sheaf of
  differentials of `U ⟶ V` read on the small étale site agrees with the usual sheaf of
  differentials of the morphism of schemes, through the associated module of 03DU (4).  The
  identification `Ω_{X/Y}|_{U_étale} = Ω_{U/V}` itself is elsewhere, on
  `AlgebraicGeometry.Space.sheafOfDifferentialsEtaleLocalizationIso` and its chart form"
  AlgebraicGeometry.Space.sheafOfDifferentialsSchemeComparison

/-- **Stacks 04CS at zero objects**, the vanishing comparison that Stacks 04G9 needs:
for a morphism `ψ : U ⟶ V` of schemes of the site, the spaces-level sheaf of differentials of
`ψ` vanishes exactly when `Ω_{U/V}` does. -/
@[stacks 04CS "the vanishing comparison for a morphism of schemes of the site"]
theorem sheafOfDifferentialsSchemeVanishing :
    SheafOfDifferentialsSchemeVanishing B S hS :=
  sheafOfDifferentialsSchemeVanishing_of_comparison B S hS
    (sheafOfDifferentialsSchemeComparison B S hS)



end AlgebraicGeometry.Space

end
