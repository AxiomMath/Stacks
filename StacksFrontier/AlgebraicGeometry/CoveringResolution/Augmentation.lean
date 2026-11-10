module

public import StacksFrontier.AlgebraicGeometry.CoveringResolution.Basic

/-!
# The augmentation of the Čech resolution (towards Tag 02FU)

`StacksDraft.Ch20.Sec25.Tag02FU` builds the Čech complex
  `Stacks.CechTotalComplex.CoveringResolution.coveringComplex` of an
open covering `U` of a ringed space `(X, R)` with values in the direct images of the
restrictions of a sheaf of modules, and
`StacksDraft.AlgebraicGeometry.F3.CoveringResolution.Basic` supplies its product coordinates
and reduces `Stacks.CechTotalComplex.CoveringResolution` to three hypotheses.
  This file discharges two of
them, `augmentation` and `augmentation_f_zero`.

## Main definitions

* `infUnit X R F W` is restriction of sections to the intersection with a fixed open set: the
  morphism of sheaves of modules from the enlargement of `F` to
  `Stacks.CechTotalComplex.CoveringResolution.infPushforward X R F W`, which on sections over `V`
    is the restriction map
  `F(V) ⟶ F(V ⊓ W)`.
* `infUnitIso X R F hW` and `moduleUniverseLiftIso X R hW` upgrade `infUnit` to an
  isomorphism, and to a natural isomorphism of functors, when the open set contains
  everything; `terminalInfUnitIso X R F` is the case of the terminal open set.
* `augZero X R U F` is the composite of `infUnit` at the terminal open set with
  `Stacks.CechTotalComplex.CoveringResolution.coveringAugmentation`: the canonical map from the
    enlargement of `F` into the
  degree-zero term of the Čech complex.
* `augmentationNatTrans X R U` is `augZero` read as a morphism out of the single complex,
  natural in the sheaf of modules.

## Main results

* `augmentation_naturality`: the Čech augmentation of
  `Stacks.Cohomology.CechZero.aug` is natural in the coefficient presheaf.
  This is stated for an arbitrary family in an arbitrary category, as the rest of that file is.
* `augmentation_f_zero`: the degree-zero formula of
  `Stacks.CechTotalComplex.CoveringResolution` for
  `augmentationNatTrans`, namely that in the product coordinates of
  `StacksDraft.AlgebraicGeometry.F3.CoveringResolution.Basic` the augmentation is the family
  of restriction maps.
* `coveringResolutionOfQuasiIso` assembles eight of the nine fields of
  `Stacks.CechTotalComplex.CoveringResolution`, leaving only `quasiIso` as a
    hypothesis.

## Implementation notes

The module docstring of
`StacksDraft.AlgebraicGeometry.F3.CoveringResolution.Basic` says that what the `augmentation`
field needs is *an isomorphism* between `Stacks.CechTotalComplex.CoveringResolution.infPushforward
  X R F (⊤_ (Opens X))` and
`Stacks.CechTotalComplex.CoveringResolution.moduleUniverseLift X R` applied to `F`, resting on
`Stacks.CategoryTheory.CechComplex.terminal_eq_top`. That over-asks twice over.

First, the two fields discharged here use only the map `F(V) ⟶ F(V ⊓ ⊤_)`, which is
restriction along `inf_le_left` and is available for *every* open set in place of `⊤_`, with
no identification of `⊤_ (Opens X)` with `⊤`; and the `augmentation_f_zero` field states its
right-hand side with exactly `homOfLE inf_le_left`, so no such identification enters the
formula either. Accordingly `infUnit` is defined for an arbitrary open set.

Second, the isomorphism itself does not need `terminal_eq_top`. Its inverse needs an
inequality `V ≤ V ⊓ W`, that is `⊤ ≤ W`, and for `W = ⊤_ (Opens X)` that inequality is
`leOfHom (terminal.from ⊤)` — the unique map out of `⊤`, which is one of the two halves
`terminal_eq_top` is proved from. So `infUnitIso` is stated with the hypothesis `⊤ ≤ W`, and
`terminal_eq_top` is not used anywhere in this file. What the isomorphism is *for* is the
comparison of the degree-zero homology with the global sections, which is part of the
remaining `quasiIso` field.

As in `Basic.lean`, every coordinate computation is `F.val.map` of an inclusion of open sets
and every coherence between two such is `Subsingleton.elim` in the thin category `Opens X`;
no `eqToHom` occurs.

## What is not proved here

`Stacks.CechTotalComplex.CoveringResolution.quasiIso`, the mathematical core,
  and nothing here bears on it.
`Basic.lean`'s account of it stands: the device is
`CategoryTheory.Limits.FormalCoproduct.extraDegeneracyCech`, which applies to a *split*
covering, and the missing input is a locality criterion for exactness of complexes of sheaves
of modules. In particular **this file attaches no tag for 02FU**: the tag carries a single
label covering all nine fields of the structure, and the field `quasiIso` remains open.

## References

* [Stacks Project, Tag 02FU](https://stacks.math.columbia.edu/tag/02FU)
* [Stacks Project, Equation 01EE](https://stacks.math.columbia.edu/tag/01EE)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite CategoryTheory.Limits
open Stacks.CategoryTheory.CechComplex
open Stacks.Cohomology.CechZero (aug aug_comp_π aug_comp_d)

universe u v w t iw uC vC uA vA

namespace Stacks.AlgebraicGeometry.CoveringResolution

open Stacks.CechTotalComplex.CoveringResolution

/-! ### Naturality of the Čech augmentation -/

section CechNaturality

variable {C : Type uC} [Category.{vC} C] {A : Type uA} [Category.{vA} A]
  [HasProducts.{iw} A] [HasFiniteProducts C] [Preadditive A] {ι : Type iw} (U : ι → C)
  {P Q : Cᵒᵖ ⥤ A} (ψ : P ⟶ Q)

/-- The Čech projections are natural in the coefficient presheaf, in the generality of
`Stacks.CategoryTheory.CechComplex`. -/
theorem cech_map_f_comp_π (n : ℕ) (y : Fin (n + 1) → ι) :
    ((cechComplexFunctor U).map ψ).f n ≫ π U Q n y =
      π U P n y ≫ ψ.app (op (inter U y)) :=
  Pi.map_π (fun x : Fin (n + 1) → ι => ψ.app (op (inter U x))) y

/-- **The Čech augmentation is natural in the coefficient presheaf.** -/
theorem augmentation_naturality :
    aug U P terminalIsTerminal ≫ ((cechComplexFunctor U).map ψ).f 0 =
      ψ.app (op (⊤_ C)) ≫ aug U Q terminalIsTerminal := by
  refine hom_ext U Q (n := 0) fun x => ?_
  rw [Category.assoc, cech_map_f_comp_π U ψ 0 x, ← Category.assoc, aug_comp_π,
    Category.assoc, aug_comp_π]
  exact ψ.naturality (terminalIsTerminal.from (inter U x)).op

end CechNaturality

variable (X : TopCat.{u}) (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})

/-! ### Restriction to the intersection with a fixed open set -/

/-- Restriction of sections to the intersection with a fixed open set, as a morphism of
presheaves of abelian groups. -/
noncomputable def infUnitPresheafMap (F : SheafOfModules.{w} R) (W : Opens X) :
    (uliftSheaf.{u, v, w, t} X R F).val.presheaf ⟶
      (infPushforward.{u, v, w, t} X R F W).presheaf where
  app V := (uliftSheaf.{u, v, w, t} X R F).val.presheaf.map
    (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op
  naturality _ _ _ :=
    ((((uliftSheaf.{u, v, w, t} X R F).val.presheaf.map_comp _ _).symm.trans
        (congrArg (uliftSheaf.{u, v, w, t} X R F).val.presheaf.map
          (Subsingleton.elim _ _))).trans
      ((uliftSheaf.{u, v, w, t} X R F).val.presheaf.map_comp _ _))

/-- Restriction of sections to the intersection with a fixed open set, as a morphism of
presheaves of modules: it is linear once the target has its scalars restricted along
`R(V) ⟶ R(V ⊓ W)`, which is exactly how `Stacks.CechTotalComplex.CoveringResolution.infPushforward`
  carries them. -/
noncomputable def infUnitVal (F : SheafOfModules.{w} R) (W : Opens X) :
    (uliftSheaf.{u, v, w, t} X R F).val ⟶ infPushforward.{u, v, w, t} X R F W :=
  PresheafOfModules.homMk (infUnitPresheafMap.{u, v, w, t} X R F W)
    (fun V r m => (uliftSheaf.{u, v, w, t} X R F).val.map_smul
      (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op r m)

/-- **Restriction of sections to the intersection with a fixed open set**, as a morphism of
sheaves of modules out of the enlargement of `F`. -/
noncomputable def infUnit (F : SheafOfModules.{w} R) (W : Opens X) :
    (moduleUniverseLift.{u, v, w, t} X R).obj F ⟶
      (infPushforwardFunctor.{u, v, w, t} X R W).obj F :=
  ⟨infUnitVal.{u, v, w, t} X R F W⟩

/-- `infUnit` is restriction of sections of `F`. -/
theorem infUnit_apply (F : SheafOfModules.{w} R) (W V : Opens X)
    (x : ((moduleUniverseLift.{u, v, w, t} X R).obj F).val.obj (op V)) :
    (infUnit.{u, v, w, t} X R F W).val.app (op V) x =
      ULift.up (F.val.map (homOfLE (inf_le_left : V ⊓ W ≤ V)).op x.down) := rfl

/-- `infUnit` is natural in the sheaf of modules. -/
theorem infUnit_naturality {F G : SheafOfModules.{w} R} (φ : F ⟶ G) (W : Opens X) :
    (moduleUniverseLift.{u, v, w, t} X R).map φ ≫ infUnit.{u, v, w, t} X R G W =
      infUnit.{u, v, w, t} X R F W ≫ (infPushforwardFunctor.{u, v, w, t} X R W).map φ := by
  apply SheafOfModules.hom_ext
  ext V x
  exact congrArg ULift.up (PresheafOfModules.naturality_apply φ.val
    (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op x.down).symm

/-! ### Restriction to an open set containing everything is invertible -/

/-- Restriction *back* from the intersection with an open set that contains everything, as a
morphism of presheaves of abelian groups. -/
noncomputable def infUnitInvPresheafMap (F : SheafOfModules.{w} R) {W : Opens X} (hW : ⊤ ≤ W) :
    (infPushforward.{u, v, w, t} X R F W).presheaf ⟶
      (uliftSheaf.{u, v, w, t} X R F).val.presheaf where
  app V := (uliftSheaf.{u, v, w, t} X R F).val.presheaf.map
    (homOfLE (le_inf le_rfl (le_top.trans hW) : V.unop ≤ V.unop ⊓ W)).op
  naturality _ _ _ :=
    ((((uliftSheaf.{u, v, w, t} X R F).val.presheaf.map_comp _ _).symm.trans
        (congrArg (uliftSheaf.{u, v, w, t} X R F).val.presheaf.map
          (Subsingleton.elim _ _))).trans
      ((uliftSheaf.{u, v, w, t} X R F).val.presheaf.map_comp _ _))

/-- Restriction back from the intersection with an open set that contains everything, as a
morphism of presheaves of modules. Its linearity is the statement that restricting from `V` to
`V ⊓ W` and back is the identity on `R(V)`, which holds because `Opens X` is thin. -/
noncomputable def infUnitInvVal (F : SheafOfModules.{w} R) {W : Opens X} (hW : ⊤ ≤ W) :
    infPushforward.{u, v, w, t} X R F W ⟶ (uliftSheaf.{u, v, w, t} X R F).val :=
  PresheafOfModules.homMk (infUnitInvPresheafMap.{u, v, w, t} X R F hW)
    (fun V r m => by
      refine ((uliftSheaf.{u, v, w, t} X R F).val.map_smul
        (homOfLE (le_inf le_rfl (le_top.trans hW) : V.unop ≤ V.unop ⊓ W)).op _ m).trans ?_
      refine congrArg (fun ρ => ρ • _) ?_
      have key : R.obj.map (homOfLE (inf_le_left : V.unop ⊓ W ≤ V.unop)).op ≫
            R.obj.map (homOfLE
              (le_inf le_rfl (le_top.trans hW) : V.unop ≤ V.unop ⊓ W)).op = 𝟙 _ :=
        (R.obj.map_comp _ _).symm.trans
          ((congrArg R.obj.map (Subsingleton.elim _ (𝟙 (op V.unop)))).trans (R.obj.map_id _))
      exact ConcreteCategory.congr_hom key r)

/-- **Restriction to the intersection with an open set that contains everything is an
isomorphism.**

Only `⊤ ≤ W` is used, never `W = ⊤`, so for `W = ⊤_ (Opens X)` the input is
`top_le_terminal` — the single map out of `⊤` — and not
`Stacks.CategoryTheory.CechComplex.terminal_eq_top`. -/
noncomputable def infUnitIso (F : SheafOfModules.{w} R) {W : Opens X} (hW : ⊤ ≤ W) :
    (moduleUniverseLift.{u, v, w, t} X R).obj F ≅
      (infPushforwardFunctor.{u, v, w, t} X R W).obj F where
  hom := infUnit.{u, v, w, t} X R F W
  inv := ⟨infUnitInvVal.{u, v, w, t} X R F hW⟩
  hom_inv_id := by
    apply SheafOfModules.hom_ext
    ext V x
    exact (((uliftSheaf.{u, v, w, t} X R F).val.map_comp_apply _ _ x).symm.trans
        ((uliftSheaf.{u, v, w, t} X R F).val.congr_map_apply
          (Subsingleton.elim _ (𝟙 V)) x)).trans
      (map_id_apply X R (uliftSheaf.{u, v, w, t} X R F).val V x)
  inv_hom_id := by
    apply SheafOfModules.hom_ext
    ext V x
    exact (((uliftSheaf.{u, v, w, t} X R F).val.map_comp_apply _ _ x).symm.trans
        ((uliftSheaf.{u, v, w, t} X R F).val.congr_map_apply
          (Subsingleton.elim _ (𝟙 _)) x)).trans
      (map_id_apply X R (infPushforward.{u, v, w, t} X R F W) V x)

/-- **The enlargement of `F` is naturally isomorphic to its direct image under intersection
with an open set containing everything.** -/
noncomputable def moduleUniverseLiftIso {W : Opens X} (hW : ⊤ ≤ W) :
    moduleUniverseLift.{u, v, w, t} X R ≅ infPushforwardFunctor.{u, v, w, t} X R W :=
  NatIso.ofComponents (fun F => infUnitIso.{u, v, w, t} X R F hW)
    (fun {_ _} φ => infUnit_naturality.{u, v, w, t} X R φ W)

/-- The top open set maps to the terminal one, so the terminal open set contains everything.
This is the half of `Stacks.CategoryTheory.CechComplex.terminal_eq_top` that the augmentation
needs, and it is the only half it needs. -/
theorem top_le_terminal : (⊤ : Opens X) ≤ ⊤_ (Opens X) :=
  leOfHom (terminal.from (⊤ : Opens X))

/-- **Restriction to the intersection with the terminal open set is an isomorphism**, so the
sections of the Čech complex over the terminal open set are the sections of `F` itself. -/
noncomputable def terminalInfUnitIso (F : SheafOfModules.{w} R) :
    (moduleUniverseLift.{u, v, w, t} X R).obj F ≅
      (infPushforwardFunctor.{u, v, w, t} X R (⊤_ (Opens X))).obj F :=
  infUnitIso.{u, v, w, t} X R F (top_le_terminal X)

/-- The restriction of sections of `F` to their intersection with the terminal open set is an
isomorphism. -/
instance isIso_infUnit_terminal (F : SheafOfModules.{w} R) :
    IsIso (infUnit.{u, v, w, t} X R F (⊤_ (Opens X))) :=
  ⟨(terminalInfUnitIso.{u, v, w, t} X R F).inv,
    (terminalInfUnitIso.{u, v, w, t} X R F).hom_inv_id,
    (terminalInfUnitIso.{u, v, w, t} X R F).inv_hom_id⟩

/-! ### The augmentation in degree zero -/

variable {ι : Type t} (U : ι → Opens X)

/-- **The augmentation of the Čech complex in degree zero**: restriction of sections to the
intersection with the terminal open set, followed by the Čech augmentation. -/
noncomputable def augZero (F : SheafOfModules.{w} R) :
    (moduleUniverseLift.{u, v, w, t} X R).obj F ⟶
      ((coveringComplex.{u, v, w, t} X R U).obj F).X 0 :=
  infUnit.{u, v, w, t} X R F (⊤_ (Opens X)) ≫ coveringAugmentation.{u, v, w, t} X R U F

/-- `augZero` unfolded. -/
theorem augZero_eq (F : SheafOfModules.{w} R) :
    augZero.{u, v, w, t} X R U F =
      infUnit.{u, v, w, t} X R F (⊤_ (Opens X)) ≫
        aug U (infPushforwardOpens.{u, v, w, t} X R F) terminalIsTerminal := rfl

/-- `augZero` is a cycle in degree zero.

The proof is in term mode on purpose:
  `Stacks.CechTotalComplex.CoveringResolution.infPushforwardOpens` is a semireducible
definition, so a goal mentioning `infUnit ≫ aug U (infPushforwardOpens X R F) hT` is not
type-correct at the `instances` transparency at which `rw` builds its motive, and every
`rewrite` after an unfolding step fails. Term-mode `Eq.trans` has no motive to build. -/
theorem augZero_comp_d (F : SheafOfModules.{w} R) :
    augZero.{u, v, w, t} X R U F ≫ ((coveringComplex.{u, v, w, t} X R U).obj F).d 0 1 = 0 :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun z => infUnit.{u, v, w, t} X R F (⊤_ (Opens X)) ≫ z)
        (aug_comp_d U (infPushforwardOpens.{u, v, w, t} X R F) terminalIsTerminal)).trans
      (Limits.comp_zero))

/-- `augZero` is natural in the sheaf of modules. -/
theorem augZero_naturality {F G : SheafOfModules.{w} R} (φ : F ⟶ G) :
    (moduleUniverseLift.{u, v, w, t} X R).map φ ≫ augZero.{u, v, w, t} X R U G =
      augZero.{u, v, w, t} X R U F ≫ ((coveringComplex.{u, v, w, t} X R U).map φ).f 0 :=
  ((Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ aug U (infPushforwardOpens.{u, v, w, t} X R G) terminalIsTerminal)
        (infUnit_naturality.{u, v, w, t} X R φ (⊤_ (Opens X))))).trans
    ((Category.assoc _ _ _).trans
      ((congrArg (fun z => infUnit.{u, v, w, t} X R F (⊤_ (Opens X)) ≫ z)
          (augmentation_naturality U ((cechDiagram.{u, v, w, t} X R).map φ)).symm).trans
        (Category.assoc _ _ _).symm))

/-- `augZero` is a cycle, in the form the constructor for morphisms out of a single complex
asks for. -/
theorem augZero_comp_d_rel (F : SheafOfModules.{w} R) (k : ℕ)
    (hk : (ComplexShape.up ℕ).Rel 0 k) :
    augZero.{u, v, w, t} X R U F ≫ ((coveringComplex.{u, v, w, t} X R U).obj F).d 0 k = 0 := by
  obtain rfl : k = 1 := by simpa using hk.symm
  exact augZero_comp_d.{u, v, w, t} X R U F

/-! ### The augmentation as a morphism out of the single complex -/

section Single

variable {A : Type uA} [Category.{vA} A] [Limits.HasZeroMorphisms A] [Limits.HasZeroObject A]

/-- The degree-zero component of the morphism out of a single cochain complex determined by a
cycle in degree zero. -/
theorem mkHomFromSingle_f_zero {K : CochainComplex A ℕ} {M : A} (φ : M ⟶ K.X 0)
    (hφ : ∀ k : ℕ, (ComplexShape.up ℕ).Rel 0 k → φ ≫ K.d 0 k = 0) :
    (HomologicalComplex.mkHomFromSingle φ hφ).f 0 = φ := by
  rw [HomologicalComplex.mkHomFromSingle_f]
  exact Category.id_comp φ

end Single

/-- **The `augmentation` field of
  `Stacks.CechTotalComplex.CoveringResolution`.** The canonical
augmentation, as a natural transformation from the enlargement of a sheaf of modules placed
in degree zero to the Čech complex of the covering. -/
noncomputable def augmentationNatTrans :
    moduleUniverseLift.{u, v, w, t} X R ⋙
        HomologicalComplex.single (SheafOfModules.{max u v w t} R) (ComplexShape.up ℕ) 0 ⟶
      coveringComplex.{u, v, w, t} X R U where
  app F := HomologicalComplex.mkHomFromSingle (augZero.{u, v, w, t} X R U F)
    (augZero_comp_d_rel.{u, v, w, t} X R U F)
  naturality F G φ := by
    refine HomologicalComplex.from_single_hom_ext (j := 0) ?_
    simp only [Functor.comp_map, HomologicalComplex.comp_f, CochainComplex.single₀_map_f_zero,
      mkHomFromSingle_f_zero]
    exact augZero_naturality.{u, v, w, t} X R U φ

/-- The degree-zero component of `augmentationNatTrans` is `augZero`. -/
theorem augmentationNatTrans_f_zero (F : SheafOfModules.{w} R) :
    ((augmentationNatTrans.{u, v, w, t} X R U).app F).f 0 = augZero.{u, v, w, t} X R U F :=
  mkHomFromSingle_f_zero (augZero.{u, v, w, t} X R U F)
    (augZero_comp_d_rel.{u, v, w, t} X R U F)

/-! ### The degree-zero formula -/

/-- Equal morphisms of sheaves of modules agree on sections. -/
private theorem hom_val_app_congr {M N : SheafOfModules R} {f g : M ⟶ N}
    (h : f = g) (V : Opens X) (x : M.val.obj (op V)) : f.val.app (op V) x = g.val.app (op V) x :=
  h ▸ rfl

/-- The composite of `augZero` with a Čech projection, on a section: two restrictions of a
section of `F`.

The morphism-level statement `augZero ≫ π = infUnit ≫ _` is deliberately *not* formed. Its
right-hand side makes the elaborator solve `(infPushforwardOpens X R F).obj ?A` against
`(infPushforwardFunctor X R (⊤_ (Opens X))).obj F`, and the resulting
`Opposite.unop ?A =?= ⊤_ (Opens X)` problem sends `whnf` into the unexposed `getLimitCone`
behind `HasTerminal (Opens X)` until the heartbeat limit. The composite is
instead evaluated at the section `(infUnit …).val.app (op V) x`, where every type is already
determined. -/
theorem augZero_comp_π_down (F : SheafOfModules.{w} R) (V : Opens X) (s : Fin 1 → ι)
    (x : ((moduleUniverseLift.{u, v, w, t} X R).obj F).val.obj (op V)) :
    ((π U (infPushforwardOpens.{u, v, w, t} X R F) 0 s).val.app (op V)
        ((augZero.{u, v, w, t} X R U F).val.app (op V) x)).down =
      F.val.map (homOfLE (inf_le_inf_left V
          (leOfHom (terminal.from (inter U s))))).op
        (F.val.map (homOfLE (inf_le_left : V ⊓ (⊤_ (Opens X)) ≤ V)).op x.down) :=
  congrArg ULift.down
    (hom_val_app_congr X R
      (aug_comp_π U (infPushforwardOpens.{u, v, w, t} X R F) terminalIsTerminal s) V
      ((infUnit.{u, v, w, t} X R F (⊤_ (Opens X))).val.app (op V) x))

/-- The degree-zero formula, stated for `augZero`: in the product coordinates the `s`-th
coordinate of the augmentation of a section is its restriction to `V ⊓ cechIntersection`. -/
theorem augZero_coord (F : SheafOfModules.{w} R) (V : Opens X) (s : Fin 1 → ι)
    (x : ((moduleUniverseLift.{u, v, w, t} X R).obj F).val.obj (op V)) :
    (termIso.{u, v, w, t} X R U F 0 V).hom
        ((augZero.{u, v, w, t} X R U F).val.app (op V) x) s =
      ULift.up (F.val.map (homOfLE inf_le_left :
        V ⊓ cechIntersection X U 0 s ⟶ V).op x.down) := by
  refine (termIso_hom_apply.{u, v, w, t} X R U F 0 V _ s).trans
    ((coordπ_apply.{u, v, w, t} X R U F 0 V s _).trans (congrArg ULift.up ?_))
  rw [augZero_comp_π_down.{u, v, w, t} X R U F V s x, ← F.val.map_comp_apply,
    ← F.val.map_comp_apply]
  exact F.val.congr_map_apply (Subsingleton.elim _ _) _

/-- **The `augmentation_f_zero` field of
  `Stacks.CechTotalComplex.CoveringResolution`.** In the product
coordinates of `Basic.lean`, the augmentation is the family of restriction maps. -/
theorem augmentation_f_zero (F : SheafOfModules.{w} R) (V : Opens X)
    (x : (((moduleUniverseLift.{u, v, w, t} X R ⋙ HomologicalComplex.single
      (SheafOfModules.{max u v w t} R) (ComplexShape.up ℕ) 0).obj F).X 0).val.obj (op V))
    (s : Fin 1 → ι) :
    (termIso.{u, v, w, t} X R U F 0 V).hom
        ((((augmentationNatTrans.{u, v, w, t} X R U).app F).f 0).val.app (op V) x) s =
      ULift.up (F.val.map (homOfLE inf_le_left :
        V ⊓ cechIntersection X U 0 s ⟶ V).op
        (((HomologicalComplex.singleObjXSelf (ComplexShape.up ℕ) 0
          ((moduleUniverseLift.{u, v, w, t} X R).obj F)).hom.val.app (op V) x).down)) :=
  (congrArg (fun y => (termIso.{u, v, w, t} X R U F 0 V).hom y s)
      (hom_val_app_congr X R
        (augmentationNatTrans_f_zero.{u, v, w, t} X R U F) V x)).trans
    (augZero_coord.{u, v, w, t} X R U F V s x)

/-! ### Assembling the `CoveringResolution` structure -/

/-- **Eight of the nine fields of `Stacks.CechTotalComplex.CoveringResolution`,
  discharged.** Only the
quasi-isomorphism property is left as a hypothesis. -/
noncomputable def coveringResolutionOfQuasiIso
    (hqi : ∀ F : SheafOfModules.{w} R,
      haveI : ∀ q : ℕ, ((coveringComplex.{u, v, w, t} X R U).obj F).HasHomology q :=
        fun q => hasHomology_of_enlarged.{u, v, max w t} X R _ q
      QuasiIso ((augmentationNatTrans.{u, v, w, t} X R U).app F)) :
    Stacks.CechTotalComplex.CoveringResolution.{u, v, w, t} X R U :=
  coveringResolutionOfAugmentation.{u, v, w, t} X R U
    (augmentationNatTrans.{u, v, w, t} X R U)
    (augmentation_f_zero.{u, v, w, t} X R U) hqi

end Stacks.AlgebraicGeometry.CoveringResolution
