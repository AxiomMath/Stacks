module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQuasicoherentPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleFirstOrderIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicRepresentableComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardChartComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.EtaleCohomologyInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.UnitsShortExactSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ShortExactLongExactSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject

/-!
# Regular functions lift across a first-order thickening of an affine algebraic space

Let `Z ⊂ X` be a first-order thickening of algebraic spaces over a scheme `S`, with defining
ideal sheaf `𝓘`, and suppose that `Z` is affine, represented by an object `T` of the site with
affine underlying scheme.  This file proves that every regular function on `T` is the
restriction of a compatible family of regular functions on the étale charts of `X`: the map
`Γ(X, 𝒪_X) → Γ(Z, 𝒪_Z)` is surjective.

This is the first step of the proof for finite order thickenings of Stacks 05ZR, and the
argument is the source's (the proof for finite order thickenings of Stacks 05ZQ): the long
exact cohomology sequence of
`0 → 𝓘 → 𝒪_X → i_*𝒪_Z → 0`
on the small étale site of `X`, and the vanishing of `H¹(X, 𝓘)`.  That vanishing holds because
`𝓘` is the direct image of the conormal module `𝒞_{Z/X}`, a quasi-coherent `𝒪_Z`-module
(Stacks 04CJ), because the cohomology of a direct image along a thickening is the cohomology on
the closed member (Stacks 05ZM), and because a quasi-coherent module on an affine étale chart
has no higher cohomology (Stacks 03DW).

## Main definitions

* `AlgebraicGeometry.Space.thickeningStructureSequence`: the sequence `0 → 𝓘 → 𝒪_X → i_*𝒪_Z → 0`
  of sheaves of abelian groups on the small étale site of `X`.
* `Stacks.Cohomology.GlobalSectionsZero.eval`: the value of a degree-zero cohomology class of
  an abelian sheaf at an object of the site.

## Main results

* `AlgebraicGeometry.Space.thickeningStructureSequence_shortExact`: the sequence is short exact.
* `AlgebraicGeometry.Space.subsingleton_H_one_thickeningIdealAddSheaf`: `H¹(X, 𝓘) = 0` when the
  closed member is affine.
* `AlgebraicGeometry.Space.exists_lift_of_isFirstOrderThickening_of_isTerminal`: every regular
  function on the affine closed member lifts to a compatible family of regular functions on the
  étale charts of `X`.

## References

* [Stacks Project, Tag 05ZQ](https://stacks.math.columbia.edu/tag/05ZQ)
* [Stacks Project, Tag 05ZR](https://stacks.math.columbia.edu/tag/05ZR)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 05ZM](https://stacks.math.columbia.edu/tag/05ZM)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

universe u v t w'

/-! ### Degree-zero cohomology classes and compatible families of sections -/

namespace Stacks.Cohomology.GlobalSectionsZero

open Stacks.Cohomology.Torsors

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasSheafify J AddCommGrpCat.{t}] [HasExt.{w'} (Sheaf J AddCommGrpCat.{t})]

/-- The value at an object of the site of a degree-zero cohomology class of an abelian sheaf:
the class is a morphism out of the constant sheaf of integers, evaluated at the constant
section `1`. -/
def eval {F : Sheaf J AddCommGrpCat.{t}} (x : Sheaf.H.{w'} F 0) (U : Cᵒᵖ) : F.obj.obj U :=
  (Ext.addEquiv₀ x).hom.app U ((constantUnit (J := J) (C := C)).app U ⟨1⟩)

/-- Evaluation commutes with the map on degree-zero cohomology induced by a morphism of
sheaves. -/
theorem eval_map {F G : Sheaf J AddCommGrpCat.{t}} (f : F ⟶ G) (x : Sheaf.H.{w'} F 0)
    (U : Cᵒᵖ) : eval (Sheaf.H.map f 0 x) U = f.hom.app U (eval x U) := by
  unfold eval
  rw [Sheaf.H.addEquiv₀_map]
  rfl

/-- The degree-zero cohomology class of a compatible family of sections. -/
def ofFamily (F : Sheaf J AddCommGrpCat.{t}) (s : ∀ U, F.obj.obj U)
    (hs : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), F.obj.map f (s U) = s V) : Sheaf.H.{w'} F 0 :=
  Ext.addEquiv₀.symm
    (((sheafificationAdjunction J AddCommGrpCat.{t}).homEquiv _ F).symm
      (morphismOfSectionFamily F.obj s hs))

/-- The class of a compatible family evaluates to the family. -/
theorem eval_addEquiv₀_symm {F : Sheaf J AddCommGrpCat.{t}}
    (φ : (constantSheaf J AddCommGrpCat.{t}).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ F)
    (U : Cᵒᵖ) :
    eval (Ext.addEquiv₀.symm φ : Sheaf.H.{w'} F 0) U =
      φ.hom.app U ((constantUnit (J := J) (C := C)).app U ⟨1⟩) := by
  unfold eval
  rw [AddEquiv.apply_symm_apply]

/-- The class of a compatible family evaluates to the family. -/
theorem eval_ofFamily (F : Sheaf J AddCommGrpCat.{t}) (s : ∀ U, F.obj.obj U)
    (hs : ∀ {U V : Cᵒᵖ} (f : U ⟶ V), F.obj.map f (s U) = s V) (U : Cᵒᵖ) :
    eval (ofFamily F s hs : Sheaf.H.{w'} F 0) U = s U := by
  let adj := sheafificationAdjunction J AddCommGrpCat.{t}
  let P := (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))
  have h : constantUnit (J := J) (C := C) ≫
      (sheafToPresheaf J AddCommGrpCat.{t}).map
        ((adj.homEquiv P F).symm (morphismOfSectionFamily F.obj s hs)) =
        morphismOfSectionFamily F.obj s hs := by
    unfold constantUnit
    rw [← adj.homEquiv_naturality_right, Category.id_comp, Equiv.apply_symm_apply]
  have h1 := congrArg (fun φ => φ.app U ⟨1⟩) h
  simp only [NatTrans.comp_app] at h1
  exact (eval_addEquiv₀_symm _ U).trans (h1.trans (morphismOfSectionFamily_one F.obj s hs U))

/-- The values of a degree-zero class form a compatible family of sections. -/
theorem eval_restrict {F : Sheaf J AddCommGrpCat.{t}} (x : Sheaf.H.{w'} F 0) {U V : Cᵒᵖ}
    (f : U ⟶ V) : F.obj.map f (eval x U) = eval x V := by
  unfold eval
  refine (NatTrans.naturality_apply (Ext.addEquiv₀ x).hom f _).symm.trans ?_
  exact congrArg (ConcreteCategory.hom ((Ext.addEquiv₀ x).hom.app V))
    (NatTrans.naturality_apply (constantUnit (J := J) (C := C)) f ⟨1⟩).symm

end Stacks.Cohomology.GlobalSectionsZero

namespace AlgebraicGeometry.Space

attribute [local instance] enoughInjectives_sheaf_smallEtale hasExt_sheaf_smallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X : AlgebraicSpaces B S hS} {G : Subfunctor X.1}

/-! ### The sequence `0 → 𝓘 → 𝒪_X → i_*𝒪_Z → 0` -/

/-- The structure sheaf of an algebraic space, as a sheaf of abelian groups. -/
abbrev structureAddSheaf (X : AlgebraicSpaces B S hS) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} :=
  (SheafOfModules.toSheaf (structureRingSheaf B S hS X)).obj
    (SheafOfModules.unit (structureRingSheaf B S hS X))

/-- The direct image `i_*𝒪_Z` of the structure sheaf of the closed member of a first-order
thickening, as a sheaf of abelian groups on the small étale site of the ambient space: its
sections over an étale chart `U` are the regular functions on `Z ×_X U`. -/
abbrev thickeningRestrictStructureAddSheaf (hG : IsFirstOrderThickening B S hS X G) :
    Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u} :=
  (thickeningRestrictAddSheaf B S hS hG.1).obj
    (structureAddSheaf B S hS (IsThickening.space B S hS hG.1))

/-- The inclusion `𝓘 ⟶ 𝒪_X` of the defining ideal sheaf. -/
def thickeningIdealInclusion (hG : IsFirstOrderThickening B S hS X G) :
    thickeningIdealAddSheaf B S hS hG ⟶ structureAddSheaf B S hS X :=
  (SheafOfModules.toSheaf (structureRingSheaf B S hS X)).map
    (definingIdealSheaf B S hS X (firstOrderThickeningSubspace B S hS hG)).ι

/-- The reduction `𝒪_X ⟶ i_*𝒪_Z`, pullback of regular functions along the cartesian
projections `Z ×_X U ⟶ U`. -/
def thickeningReduction (hG : IsFirstOrderThickening B S hS X G) :
    structureAddSheaf B S hS X ⟶ thickeningRestrictStructureAddSheaf B S hS hG :=
  ObjectProperty.homMk
    { app := fun U ↦ AddCommGrpCat.ofHom
        ((thickeningStructureSharp B S hS hG).hom.app U).hom.toAddMonoidHom
      naturality := fun U V f ↦ by
        ext x
        exact congrArg (fun φ => φ.hom x)
          ((thickeningStructureSharp B S hS hG).hom.naturality f) }

/-- The component of `thickeningReduction` over an étale chart `U` sends a regular function to
its image under `thickeningStructureSharp` at `U`. -/
theorem thickeningReduction_app (hG : IsFirstOrderThickening B S hS X G)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (x : ToType ((structureAddSheaf B S hS X).obj.obj U)) :
    (thickeningReduction B S hS hG).hom.app U x =
      ((thickeningStructureSharp B S hS hG).hom.app U).hom x :=
  rfl

/-- **The sequence `0 → 𝓘 → 𝒪_X → i_*𝒪_Z → 0` of a first-order thickening**, as sheaves of
abelian groups on the small étale site of the ambient space. -/
def thickeningStructureSequence (hG : IsFirstOrderThickening B S hS X G) :
    ShortComplex (Sheaf (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u}) :=
  ShortComplex.mk (thickeningIdealInclusion B S hS hG) (thickeningReduction B S hS hG) <| by
    refine ObjectProperty.hom_ext _ ?_
    ext U f
    change ((thickeningStructureSharp B S hS hG).hom.app U).hom f.1 = 0
    have h : (f.1 : _) ∈ definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG)
        (op U.unop) := f.2
    rwa [← ker_thickeningStructureSharp_app B S hS hG U.unop] at h

/-- **The sequence `0 → 𝓘 → 𝒪_X → i_*𝒪_Z → 0` of a first-order thickening is short exact.** -/
theorem thickeningStructureSequence_shortExact (hG : IsFirstOrderThickening B S hS X G) :
    (thickeningStructureSequence B S hS hG).ShortExact := by
  have hmono : Mono (thickeningStructureSequence B S hS hG).f :=
    Sheaf.mono_of_injective _ fun U x y h ↦ Subtype.ext h
  have hloc : Sheaf.IsLocallySurjective (thickeningStructureSequence B S hS hG).g := by
    refine ⟨fun {U} t ↦ ?_⟩
    obtain ⟨_, Y, a, haff, hcov, -⟩ := SmallEtale.exists_affine_etale_ofArrows B S hS X.1 U
    have key : ∀ j, (Presheaf.imageSieve (thickeningStructureSequence B S hS hG).g.hom t).arrows
        (a j) := fun j ↦
      surjective_thickeningStructureSharp_app_of_isAffine B S hS hG (Y j) (haff j) _
    refine (SmallEtale.topology B S hS X.1).superset_covering ?_ hcov
    rintro V f ⟨_, h, _, ⟨j⟩, rfl⟩
    exact (Presheaf.imageSieve (thickeningStructureSequence B S hS hG).g.hom t).downward_closed
      (key j) h
  have hepi : Epi (thickeningStructureSequence B S hS hG).g := Sheaf.epi_of_isLocallySurjective _
  refine { exact := (thickeningStructureSequence B S hS hG).exact_iff_epi_kernel_lift.mpr ?_ }
  have : Sheaf.IsLocallySurjective (kernel.lift (thickeningStructureSequence B S hS hG).g
      (thickeningStructureSequence B S hS hG).f
      (thickeningStructureSequence B S hS hG).zero) := by
    refine Presheaf.isLocallySurjective_of_surjective _ _ fun U w ↦ ?_
    have hzero : (thickeningStructureSequence B S hS hG).g.hom.app U
        ((kernel.ι (thickeningStructureSequence B S hS hG).g).hom.app U w) = 0 :=
      congrArg (fun k : kernel (thickeningStructureSequence B S hS hG).g ⟶
          (thickeningStructureSequence B S hS hG).X₃ ↦ k.hom.app U w)
        (kernel.condition (thickeningStructureSequence B S hS hG).g)
    have hmem : (kernel.ι (thickeningStructureSequence B S hS hG).g).hom.app U w ∈
        definingIdealAt B S hS X (firstOrderThickeningSubspace B S hS hG) U := by
      rwa [← ker_thickeningStructureSharp_app B S hS hG U.unop]
    refine ⟨⟨_, hmem⟩, injective_kernel_ι_app B S hS _ U ?_⟩
    exact congrArg (fun k : (thickeningStructureSequence B S hS hG).X₁ ⟶
        (thickeningStructureSequence B S hS hG).X₂ ↦ k.hom.app U ⟨_, hmem⟩)
      (kernel.lift_ι (thickeningStructureSequence B S hS hG).g
        (thickeningStructureSequence B S hS hG).f
        (thickeningStructureSequence B S hS hG).zero)
  exact Sheaf.epi_of_isLocallySurjective _

/-! ### The terminal chart of an affine closed member -/

section Terminal

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T₀ : BigFppfOver B S hS}
  (e : yoneda.obj T₀ ≅ Y)

/-- The étale chart `yoneda T₀ ≅ Y` of a presheaf isomorphic to a representable one. -/
def thickeningIsoChart : SmallEtale B S hS Y :=
  ⟨CostructuredArrow.mk e.hom, isEtaleChart_of_isIso B S hS T₀ e.hom⟩

/-- **The chart `yoneda T₀ ≅ Y` is a terminal object of the small étale site of `Y`.** -/
def isTerminalIsoChart : IsTerminal (thickeningIsoChart B S hS e) :=
  IsTerminal.ofUniqueHom
    (fun A ↦ ObjectProperty.homMk (CostructuredArrow.homMk
      (yoneda.preimage (A.obj.hom ≫ e.inv)) (by simp [thickeningIsoChart])))
    (fun A m ↦ by
      refine ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ ?_)
      apply yoneda.map_injective
      have hw : yoneda.map m.hom.left ≫ e.hom = A.obj.hom := CostructuredArrow.w m.hom
      change yoneda.map m.hom.left = yoneda.map (yoneda.preimage (A.obj.hom ≫ e.inv))
      rw [Functor.map_preimage, ← hw]
      exact ((Iso.comp_inv_eq e).2 rfl).symm)

end Terminal

/-! ### Vanishing of `H¹(X, 𝓘)` over an affine closed member -/

/-- **The defining ideal sheaf of a first-order thickening is, as a sheaf of abelian groups, the
restriction along base change of étale charts of the conormal module.**  This is Stacks 04CJ in
the form `𝓘 ≅ i_*i^*𝓘` (`AlgebraicGeometry.Space.firstOrderConormalModuleIso`), with the direct
image read as base change of charts (`AlgebraicGeometry.Space.modulePushforwardChartIso`). -/
def thickeningIdealAddSheafIso (hG : IsFirstOrderThickening B S hS X G) :
    thickeningIdealAddSheaf B S hS hG ≅
      (thickeningRestrictAddSheaf B S hS hG.1).obj
        ((SheafOfModules.toSheaf _).obj
          (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG))) :=
  (SheafOfModules.toSheaf (structureRingSheaf B S hS X)).mapIso
    (firstOrderConormalModuleIso B S hS (firstOrderThickeningSubspace B S hS hG) hG ≪≫
      (modulePushforwardChartIso B S hS
        (subspaceInclusion B S hS X (firstOrderThickeningSubspace B S hS hG))
        (firstOrderThickeningSubspace B S hS hG).2.2.rep).app
          (conormalModule B S hS X (firstOrderThickeningSubspace B S hS hG)))

/-- **`H¹(X, 𝓘) = 0` for a first-order thickening whose closed member is affine.**  The ideal
sheaf is the restriction of the conormal module (`thickeningIdealAddSheafIso`), the cohomology
of a restriction along a thickening is the cohomology on the closed member
(`AlgebraicGeometry.Space.thickeningCohomologyAddEquiv`, Stacks 05ZM), that cohomology is the
cohomology over the terminal chart, and the conormal module is quasi-coherent (Stacks 04CN by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isClosedImmersion`), so its
higher cohomology over an affine chart vanishes
(`AlgebraicGeometry.Space.isZero_sheafCohomology_succ_of_isAffineChart`). -/
theorem subsingleton_H_one_thickeningIdealAddSheaf (hG : IsFirstOrderThickening B S hS X G)
    {T₀ : BigFppfOver B S hS} (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (e : yoneda.obj T₀ ≅ G.toFunctor) :
    Subsingleton (Sheaf.H.{u + 1} (thickeningIdealAddSheaf B S hS hG) 1) := by
  let Z := firstOrderThickeningSubspace B S hS hG
  let 𝒞 := conormalModule B S hS X Z
  have hqc : 𝒞.IsQuasicoherentOnSite :=
    isQuasicoherentOnSite_modulePullback_of_isClosedImmersion B S hS (subspaceInclusion B S hS X Z)
      Z.2.2 _ (isQuasicoherentOnSite_definingIdealSheaf B S hS X Z)
  let W := IsThickening.space B S hS hG.1
  let F𝒞 : Sheaf (SmallEtale.topology B S hS W.1) AddCommGrpCat.{u} :=
    (SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS W.1 W.2).O)).obj 𝒞
  have hzero : IsZero (Sheaf.H'.{u + 1} F𝒞 1 (thickeningIsoChart B S hS (Y := W.1) e)) :=
    isZero_sheafCohomology_succ_of_isAffineChart B S hS W.1 W.2 𝒞 hqc
      (thickeningIsoChart B S hS (Y := W.1) e) hT₀ 1 one_pos
  have : Subsingleton (Sheaf.H.{u + 1} F𝒞 1) :=
    (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H' _ F𝒞 1
      (thickeningIsoChart B S hS (Y := W.1) e) (isTerminalIsoChart B S hS (Y := W.1) e)).2
      (AddCommGrpCat.isZero_iff_subsingleton.1 hzero)
  have h2 := (thickeningCohomologyAddEquiv B S hS hG.1 F𝒞 1).symm.toEquiv.subsingleton
  let i := thickeningIdealAddSheafIso B S hS hG
  refine ⟨fun x y => ?_⟩
  have key : ∀ z, z = Sheaf.H.map i.inv 1 (Sheaf.H.map i.hom 1 z) := fun z ↦ by
    rw [← Sheaf.H.map_comp_apply, i.hom_inv_id, Sheaf.H.map_id_apply]
  rw [key x, key y, h2.elim (Sheaf.H.map i.hom 1 x) (Sheaf.H.map i.hom 1 y)]

/-! ### Lifting regular functions -/

/-- **Regular functions lift across a first-order thickening of an affine algebraic space.**
Let `Z ⊂ X` be a first-order thickening of algebraic spaces whose closed member is represented
by an object `T₀` of the site with affine underlying scheme, through `e : yoneda T₀ ≅ Z`.  Then
every regular function `a` on `T₀` is the restriction of a compatible family `φ` of regular
functions on the étale charts of `X`: on every chart `V` of `X`, the reduction of `φ V` is the
pullback of `a` along the unique morphism from `Z ×_X V` to the terminal chart `T₀`.

This is the surjectivity of `Γ(X, 𝒪_X) → Γ(Z, 𝒪_Z)` used in the proof for finite order
thickenings of Stacks 05ZR, proved as in the source: by the long exact cohomology sequence of
`0 → 𝓘 → 𝒪_X → i_*𝒪_Z → 0` and the vanishing of `H¹(X, 𝓘)`. -/
theorem exists_lift_of_isFirstOrderThickening (hG : IsFirstOrderThickening B S hS X G)
    {T₀ : BigFppfOver B S hS} (hT₀ : IsAffine ((BigFppfOver.toScheme B S hS).obj T₀))
    (e : yoneda.obj T₀ ≅ G.toFunctor)
    (a : ToType ((structureAddSheaf B S hS (IsThickening.space B S hS hG.1)).obj.obj
      (op (thickeningIsoChart B S hS (Y := (IsThickening.space B S hS hG.1).1) e)))) :
    ∃ φ : ∀ V : (SmallEtale B S hS X.1)ᵒᵖ, ToType ((structureAddSheaf B S hS X).obj.obj V),
      (∀ {V W : (SmallEtale B S hS X.1)ᵒᵖ} (f : V ⟶ W),
        (structureAddSheaf B S hS X).obj.map f (φ V) = φ W) ∧
      ∀ V, (thickeningReduction B S hS hG).hom.app V (φ V) =
        (structureAddSheaf B S hS (IsThickening.space B S hS hG.1)).obj.map
          ((isTerminalIsoChart B S hS (Y := (IsThickening.space B S hS hG.1).1) e).from
            ((thickeningChartBaseChange B S hS hG.1).obj V.unop)).op a := by
  let W := IsThickening.space B S hS hG.1
  let tT := isTerminalIsoChart B S hS (Y := W.1) e
  let Sq := thickeningStructureSequence B S hS hG
  let s : ∀ V : (SmallEtale B S hS X.1)ᵒᵖ, ToType (Sq.X₃.obj.obj V) := fun V ↦
    (structureAddSheaf B S hS W).obj.map
      (tT.from ((thickeningChartBaseChange B S hS hG.1).obj V.unop)).op a
  have hs : ∀ {V V' : (SmallEtale B S hS X.1)ᵒᵖ} (f : V ⟶ V'), Sq.X₃.obj.map f (s V) = s V' := by
    intro V V' f
    change ConcreteCategory.hom ((structureAddSheaf B S hS W).obj.map
        ((thickeningChartBaseChange B S hS hG.1).map f.unop).op)
        (ConcreteCategory.hom ((structureAddSheaf B S hS W).obj.map
          (tT.from ((thickeningChartBaseChange B S hS hG.1).obj V.unop)).op) a) = s V'
    rw [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
      tT.hom_ext ((thickeningChartBaseChange B S hS hG.1).map f.unop ≫ tT.from _) (tT.from _)]
  let y : Sheaf.H.{u + 1} Sq.X₃ 0 := Stacks.Cohomology.GlobalSectionsZero.ofFamily Sq.X₃ s hs
  have : Subsingleton (Sheaf.H.{u + 1} Sq.X₁ (0 + 1)) :=
    subsingleton_H_one_thickeningIdealAddSheaf B S hS hG hT₀ e
  obtain ⟨x, hx⟩ := (Stacks.Cohomology.GlobalLongExactSequence.exact_map_boundary
    (thickeningStructureSequence_shortExact B S hS hG) 0 y).1 (Subsingleton.elim _ _)
  refine ⟨fun V ↦ Stacks.Cohomology.GlobalSectionsZero.eval x V,
    fun f ↦ Stacks.Cohomology.GlobalSectionsZero.eval_restrict x f, fun V ↦ ?_⟩
  have := Stacks.Cohomology.GlobalSectionsZero.eval_map Sq.g x V
  rw [hx, Stacks.Cohomology.GlobalSectionsZero.eval_ofFamily] at this
  exact this.symm

end AlgebraicGeometry.Space

end
