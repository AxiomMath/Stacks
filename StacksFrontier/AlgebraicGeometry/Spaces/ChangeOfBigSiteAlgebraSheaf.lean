module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChangeOfBigSiteSmallEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderSpecialCocontinuous

/-!
# Sheaves of algebras on an algebraic space after enlarging the big fppf site

Let `B` be a big fppf site contained in a larger one `B'`, let `X` be an algebraic space over a
scheme `S` defined using `B`, and let `X'` be the algebraic space defined using `B'` that Stacks
03FP attaches to it. The transport of étale charts
`AlgebraicGeometry.Space.changeBigSiteSmallEtale : X_{étale} ⥤ X'_{étale}` is a cocontinuous
dense subsite inclusion, and it carries the structure sheaf of `X'` to the structure sheaf of `X`
on the nose. So the Comparison Lemma moves sheaves of `𝒪`-algebras back and forth between the two
small étale sites, and Stacks 03DM moves quasi-coherence with them.

## Main definitions

* `AlgebraicGeometry.Space.AlgebraSheaf.changeBigSiteRestrict`: restriction of a sheaf of
  `𝒪_{X'}`-algebras to the charts of `X`.
* `AlgebraicGeometry.Space.AlgebraSheaf.changeBigSiteExtend`: the extension of a sheaf of
  `𝒪_X`-algebras to the small étale site of `X'`, by the right Kan extension of the Comparison
  Lemma.
* `AlgebraicGeometry.Space.AlgebraSheaf.changeBigSiteRestrictExtendIso`: restricting the
  extension recovers the algebra.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_changeBigSiteRestrict_iff`: a sheaf of
  `𝒪_{X'}`-algebras is quasi-coherent exactly when its restriction is.
* `AlgebraicGeometry.Space.AlgebraSheaf.isQuasicoherent_changeBigSiteExtend`: the extension of a
  quasi-coherent algebra is quasi-coherent.

## Implementation notes

Quasi-coherence is transported by
`Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff`, the clause 03DL (6) of Stacks 03DM
for a special cocontinuous functor. Its restriction of modules is restriction of scalars along the
identity of the restricted structure sheaf, which on the underlying module of an algebra sheaf is
the underlying module of the restricted algebra sheaf up to an identity isomorphism.

## References

* [Stacks Project, Tag 03FP](https://stacks.math.columbia.edu/tag/03FP)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B B' : BigFppfSite.{u}) (h : IsContained (τ := .fppf) B B') (S : Scheme.{u})
  (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- A scheme of a big fppf site belongs to every big fppf site containing it, with the membership
stated in the form `AlgebraicGeometry.BigFppfSite.Contains`, which instance search can match. -/
theorem BigFppfSite.contains_of_isContained {B B' : BigFppfSite.{u}}
    (h : IsContained (τ := .fppf) B B') {S : Scheme.{u}} (hS : B.Contains S) : B'.Contains S :=
  largerContains h hS

/-- The comparison categories of the Comparison Lemma along the transport of charts are
essentially small, so sheaves of commutative rings have the limits it needs. -/
instance changeBigSiteSmallEtale_hasLimitsOfShape_commRingCat
    (V : (SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (changeBigSiteSmallEtale B B' h S hS X).op)
      CommRingCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- The comparison categories of the Comparison Lemma along the transport of charts are
essentially small, so sheaves of abelian groups have the limits the lemma needs. -/
instance changeBigSiteSmallEtale_hasLimitsOfShape_addCommGrpCat
    (V : (SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (changeBigSiteSmallEtale B B' h S hS X).op)
      AddCommGrpCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- The comparison categories of the Comparison Lemma along the transport of charts over a chart
`U` of `X` are essentially small, so sheaves of abelian groups have the limits the lemma needs. -/
instance changeBigSiteSmallEtale_over_hasLimitsOfShape_addCommGrpCat (U : SmallEtale B S hS X.obj)
    (V : (Over ((changeBigSiteSmallEtale B B' h S hS X).obj U))ᵒᵖ) :
    HasLimitsOfShape
      (StructuredArrow V (Over.post (X := U) (changeBigSiteSmallEtale B B' h S hS X)).op)
      AddCommGrpCat.{u} :=
  hasLimitsOfShape_of_essentiallySmall.{u} _ _

/-- Presheaves of abelian groups on the small étale site of `X'` localized at a chart `V` have a
sheafification. -/
instance changeBigSite_smallEtale_over_hasWeakSheafify
    (V : SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj) :
    HasWeakSheafify ((SmallEtale.topology B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj).over V) AddCommGrpCat.{u} := by
  have : HasSheafify ((SmallEtale.topology B' S (BigFppfSite.contains_of_isContained h hS)
      ((changeBigSite B B' h S hS).obj X).obj).over V) AddCommGrpCat.{u} := inferInstance
  exact this.isRightAdjoint

/-- On the small étale site of `X'` localized at a chart `V`, a morphism of presheaves of abelian
groups becomes an isomorphism after sheafification if and only if it is locally bijective. -/
instance changeBigSite_smallEtale_over_wEqualsLocallyBijective
    (V : SmallEtale B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj) :
    ((SmallEtale.topology B' S (largerContains h hS)
      ((changeBigSite B B' h S hS).obj X).obj).over V).WEqualsLocallyBijective
        AddCommGrpCat.{u} := by
  have : ((SmallEtale.topology B' S (BigFppfSite.contains_of_isContained h hS)
      ((changeBigSite B B' h S hS).obj X).obj).over V).WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstance
  exact this

/-- The structure sheaf of `X'` restricts to the structure sheaf of `X`: both send a chart to
the regular functions on its scheme, and the scheme of a transported chart is the scheme of the
chart. -/
theorem changeBigSite_structureSheaf_restrict :
    ((changeBigSiteSmallEtale B B' h S hS X).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.obj)
        (SmallEtale.topology B' S (largerContains h hS)
          ((changeBigSite B B' h S hS).obj X).obj)).obj
      (structureSheaf B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj
        ((changeBigSite B B' h S hS).obj X).property) =
      structureSheaf B S hS X.obj X.property :=
  rfl

namespace AlgebraSheaf

/-- **Restriction of a sheaf of `𝒪_{X'}`-algebras to the charts of `X`.** Its ring of sections
over a chart is the ring of sections over the transported chart, with the same structure map,
the structure sheaf of `X'` restricting to that of `X`. -/
def changeBigSiteRestrict
    (A : AlgebraSheaf.{u, u} B' S (BigFppfSite.contains_of_isContained h hS)
      ((changeBigSite B B' h S hS).obj X).obj
      ((changeBigSite B B' h S hS).obj X).property) :
    AlgebraSheaf.{u, u} B S hS X.obj X.property where
  right := ((changeBigSiteSmallEtale B B' h S hS X).sheafPushforwardContinuous CommRingCat.{u}
      (SmallEtale.topology B S hS X.obj)
      (SmallEtale.topology B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj)).obj
    A.right
  algebraMap U := A.algebraMap (op ((changeBigSiteSmallEtale B B' h S hS X).obj U.unop))
  algebraMap_natural f r :=
    A.algebraMap_natural ((changeBigSiteSmallEtale B B' h S hS X).op.map f) r

/-- Restriction of algebra sheaves to the charts of `X`, as a functor. -/
def changeBigSiteRestrictFunctor :
    AlgebraSheaf.{u, u} B' S (BigFppfSite.contains_of_isContained h hS)
      ((changeBigSite B B' h S hS).obj X).obj
        ((changeBigSite B B' h S hS).obj X).property ⥤
      AlgebraSheaf.{u, u} B S hS X.obj X.property where
  obj A := changeBigSiteRestrict B B' h S hS X A
  map f := ⟨((changeBigSiteSmallEtale B B' h S hS X).sheafPushforwardContinuous CommRingCat.{u}
      (SmallEtale.topology B S hS X.obj)
      (SmallEtale.topology B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj)).map
        f.right, fun U r => f.comm (op ((changeBigSiteSmallEtale B B' h S hS X).obj U.unop)) r⟩

/-- An isomorphism of sheaves of rings compatible with the structure maps is an isomorphism of
algebra sheaves. -/
def isoOfRight {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}
    {A C : AlgebraSheaf.{u, u} B S hS F hF} (e : A.right ≅ C.right)
    (he : ∀ U r, e.hom.hom.app U (A.algebraMap U r) = C.algebraMap U r) : A ≅ C where
  hom := ⟨e.hom, he⟩
  inv := ⟨e.inv, fun U r => by
    rw [← he U r]
    exact ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app U) e.hom_inv_id) _⟩
  hom_inv_id := Hom.ext e.hom_inv_id
  inv_hom_id := Hom.ext e.inv_hom_id

/-- The adjunction of the Comparison Lemma for sheaves of commutative rings along the transport
of charts: restriction to the charts of `X` is left adjoint to the right Kan extension. -/
abbrev changeBigSiteRingAdjunction :=
  (changeBigSiteSmallEtale B B' h S hS X).sheafAdjunctionCocontinuous CommRingCat.{u}
    (SmallEtale.topology B S hS X.obj)
    (SmallEtale.topology B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj)

/-- **The extension of a sheaf of `𝒪_X`-algebras to the small étale site of `X'`.** Its sheaf of
rings is the right Kan extension of the Comparison Lemma, and its structure map is the adjoint of
the structure map of the algebra, the structure sheaf of `X'` restricting to that of `X`. -/
def changeBigSiteExtend (A : AlgebraSheaf.{u, u} B S hS X.obj X.property) :
    AlgebraSheaf.{u, u} B' S (BigFppfSite.contains_of_isContained h hS)
      ((changeBigSite B B' h S hS).obj X).obj ((changeBigSite B B' h S hS).obj X).property :=
  AlgebraSheaf.ofHom ((changeBigSiteRingAdjunction B B' h S hS X).homEquiv
    (structureSheaf B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj
      ((changeBigSite B B' h S hS).obj X).property) A.right A.hom)

/-- The counit of the Comparison Lemma adjunction for sheaves of commutative rings along the
transport of charts is an isomorphism at every sheaf of rings on the small étale site of `X`. -/
instance (A : Sheaf (SmallEtale.topology B S hS X.obj) CommRingCat.{u}) :
    IsIso ((changeBigSiteRingAdjunction B B' h S hS X).counit.app A) :=
  inferInstance

/-- **Restricting the extension of an algebra sheaf recovers it**, by the counit of the
Comparison Lemma, which is an isomorphism. -/
def changeBigSiteRestrictExtendIso (A : AlgebraSheaf.{u, u} B S hS X.obj X.property) :
    changeBigSiteRestrict B B' h S hS X (changeBigSiteExtend B B' h S hS X A) ≅ A := by
  let c := (changeBigSiteRingAdjunction B B' h S hS X).counit.app A.right
  have hc : IsIso c := inferInstance
  refine isoOfRight B S hS (A := changeBigSiteRestrict B B' h S hS X
    (changeBigSiteExtend B B' h S hS X A)) (C := A) (@asIso _ _ _ _ c hc) (fun U r => ?_)
  have key := (changeBigSiteRingAdjunction B B' h S hS X).homEquiv_counit
    (g := (changeBigSiteRingAdjunction B B' h S hS X).homEquiv
      (structureSheaf B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj
        ((changeBigSite B B' h S hS).obj X).property) A.right A.hom)
  exact (ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app U)
    ((Equiv.symm_apply_apply _ _).symm.trans key)) r).symm

/-- The restriction of modules of the Comparison Lemma, applied to the underlying module of a
sheaf of `𝒪_{X'}`-algebras, is the underlying module of its restriction: both have the sections of
the algebra over the transported charts, with scalars acting through the structure map. -/
theorem changeBigSiteModuleRestrict_eq
    (A : AlgebraSheaf.{u, u} B' S (BigFppfSite.contains_of_isContained h hS)
      ((changeBigSite B B' h S hS).obj X).obj ((changeBigSite B B' h S hS).obj X).property) :
    (Stacks.DenseSubsiteModules.moduleRestriction (SmallEtale.topology B S hS X.obj)
        (SmallEtale.topology B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj)
        (changeBigSiteSmallEtale B B' h S hS X)
        (Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B' S (BigFppfSite.contains_of_isContained h hS)
            ((changeBigSite B B' h S hS).obj X).obj
            ((changeBigSite B B' h S hS).obj X).property).O)).obj
      (underlyingModule A) = underlyingModule (changeBigSiteRestrict B B' h S hS X A) :=
  rfl

/-- **Quasi-coherence is unchanged by restriction to the charts of `X`.** This is the clause
03DL (6) of Stacks 03DM along the cocontinuous dense subsite inclusion of the charts of `X`
into those of `X'` (`Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff`). -/
theorem isQuasicoherent_changeBigSiteRestrict_iff
    (A : AlgebraSheaf.{u, u} B' S (BigFppfSite.contains_of_isContained h hS)
      ((changeBigSite B B' h S hS).obj X).obj ((changeBigSite B B' h S hS).obj X).property) :
    A.IsQuasicoherent ↔ (changeBigSiteRestrict B B' h S hS X A).IsQuasicoherent :=
  Stacks.Sheaves.SpecialCocontinuous.isQuasicoherentOnSite_iff (SmallEtale.topology B S hS X.obj)
    (SmallEtale.topology B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj)
    (changeBigSiteSmallEtale B B' h S hS X)
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B' S (BigFppfSite.contains_of_isContained h hS)
        ((changeBigSite B B' h S hS).obj X).obj ((changeBigSite B B' h S hS).obj X).property).O)
    (underlyingModule A)

/-- **The extension of a quasi-coherent algebra is quasi-coherent.** -/
theorem isQuasicoherent_changeBigSiteExtend (A : AlgebraSheaf.{u, u} B S hS X.obj X.property)
    (hA : A.IsQuasicoherent) : (changeBigSiteExtend B B' h S hS X A).IsQuasicoherent :=
  (isQuasicoherent_changeBigSiteRestrict_iff B B' h S hS X _).2
    (IsQuasicoherent.of_iso (changeBigSiteRestrictExtendIso B B' h S hS X A).symm hA)

/-- Restriction of the structure map of an algebra sheaf is the structure map of its
restriction. -/
theorem changeBigSiteRestrict_hom
    (A : AlgebraSheaf.{u, u} B' S (BigFppfSite.contains_of_isContained h hS)
      ((changeBigSite B B' h S hS).obj X).obj ((changeBigSite B B' h S hS).obj X).property) :
    (changeBigSiteRestrict B B' h S hS X A).hom =
      ((changeBigSiteSmallEtale B B' h S hS X).sheafPushforwardContinuous CommRingCat.{u}
        (SmallEtale.topology B S hS X.obj)
        (SmallEtale.topology B' S (largerContains h hS)
          ((changeBigSite B B' h S hS).obj X).obj)).map A.hom :=
  rfl

/-- **Every sheaf of `𝒪_{X'}`-algebras is the extension of its restriction**, by the unit of the
Comparison Lemma, which is an isomorphism because restriction is fully faithful. -/
def changeBigSiteExtendRestrictIso
    (A : AlgebraSheaf.{u, u} B' S (BigFppfSite.contains_of_isContained h hS)
      ((changeBigSite B B' h S hS).obj X).obj ((changeBigSite B B' h S hS).obj X).property) :
    changeBigSiteExtend B B' h S hS X (changeBigSiteRestrict B B' h S hS X A) ≅ A := by
  let adj := changeBigSiteRingAdjunction B B' h S hS X
  have hu : IsIso adj.unit := inferInstance
  let c := adj.unit.app A.right
  have hc : IsIso c := inferInstance
  refine (isoOfRight B' S (BigFppfSite.contains_of_isContained h hS) (A := A)
    (C := changeBigSiteExtend B B' h S hS X (changeBigSiteRestrict B B' h S hS X A))
    (@asIso _ _ _ _ c hc) (fun U r => ?_)).symm
  have key : A.hom ≫ c = adj.homEquiv _ _ (changeBigSiteRestrict B B' h S hS X A).hom :=
    (adj.unit.naturality A.hom).trans (adj.homEquiv_unit _ _ _).symm
  exact ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app U) key) r

/-- **The extension respects isomorphisms of algebra sheaves.** -/
def changeBigSiteExtendIso {A C : AlgebraSheaf.{u, u} B S hS X.obj X.property} (e : A ≅ C) :
    changeBigSiteExtend B B' h S hS X A ≅ changeBigSiteExtend B B' h S hS X C := by
  let adj := changeBigSiteRingAdjunction B B' h S hS X
  let R := (changeBigSiteSmallEtale B B' h S hS X).sheafPushforwardCocontinuous CommRingCat.{u}
    (SmallEtale.topology B S hS X.obj)
    (SmallEtale.topology B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj)
  refine isoOfRight B' S (BigFppfSite.contains_of_isContained h hS)
    (A := changeBigSiteExtend B B' h S hS X A) (C := changeBigSiteExtend B B' h S hS X C)
    (R.mapIso ((AlgebraSheaf.forget).mapIso e)) (fun U r => ?_)
  have hAC : A.hom ≫ e.hom.right = C.hom := by
    apply Sheaf.hom_ext
    ext U r
    exact e.hom.comm U r
  let O' := structureSheaf B' S (largerContains h hS) ((changeBigSite B B' h S hS).obj X).obj
    ((changeBigSite B B' h S hS).obj X).property
  have key : adj.homEquiv O' A.right A.hom ≫ R.map e.hom.right = adj.homEquiv O' C.right C.hom :=
    (adj.homEquiv_naturality_right _ _).symm.trans (congrArg (adj.homEquiv O' C.right) hAC)
  exact ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app U) key) r

end AlgebraSheaf

end AlgebraicGeometry.Space

end
