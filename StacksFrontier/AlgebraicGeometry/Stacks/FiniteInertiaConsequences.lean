module

public import StacksFrontier.AlgebraicGeometry.Stacks.InertiaStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.WellNighAffine
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationRelativeInertia
public import StacksFrontier.AlgebraicGeometry.Stacks.DeligneMumfordRelativeInertiaConverse
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsoluteDMEquivalence
public import StacksFrontier.AlgebraicGeometry.Stacks.UniversallyClosedCriterion
public import StacksFrontier.AlgebraicGeometry.Stacks.ProperAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.AutomorphismGroupFibre
public import StacksFrontier.AlgebraicGeometry.Stacks.EtaleLocalStructureChart
public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteProperQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.StrongSplittingDerealizationSubgroupoid

/-!
# Consequences of a finite inertia projection

Let `𝒳` be an algebraic stack over `S` whose inertia projection `I_𝒳 ⟶ 𝒳` is finite, the
hypothesis of Stacks 0DUE and of the Keel–Mori theorem (Stacks 0DUT). Then:

* `𝒳` is quasi-DM (Stacks 050D), since `I_𝒳 ⟶ 𝒳` is locally quasi-finite (Stacks 0CL0, part (5));
* the diagonal `Δ_{𝒳/S}` is separated, since `I_𝒳 ⟶ 𝒳` is separated (Stacks 0CL0, part (1));
* `I_𝒳 ⟶ 𝒳` is universally closed in the sense of Stacks 0513 (Stacks 0512);
* the automorphism group of `𝒳` at every point is finite (Remark 0DTU): the automorphism group
  algebraic space of a field-valued point is the base change of `I_𝒳 ⟶ 𝒳` along it.

Stacks 0CL0 is stated for relative inertia; it applies here because the inertia of `𝒳` is the
relative inertia of its structure 1-morphism
(`AlgebraicGeometry.Stack.relativeProperty_relativeInertiaProjection_structureMorphism`).

## Main results

* `AlgebraicGeometry.Stack.isAbsolutelyQuasiDM_of_isFinite_inertia`
* `AlgebraicGeometry.Stack.isSeparated_relativeDiagonal_structureMorphism_of_isFinite_inertia`
* `AlgebraicGeometry.Stack.universallyClosed_inertiaProjection_of_isFinite`
* `AlgebraicGeometry.Stack.automorphismGroupHasProperty_isFiniteOverBase_of_isFinite_inertia`
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)
  (hI : AlgebraicStacks.IsFinite B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳))

/-- A finite morphism in the category of algebraic spaces is proper and locally quasi-finite. -/
private theorem isProper_and_isLocallyQuasiFinite_of_isFinite' {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : Space.IsFinite B S hS f.hom) :
    Space.IsProper B S hS f.hom ∧ Space.IsLocallyQuasiFinite B S hS f.hom :=
  Space.isProper_and_isLocallyQuasiFinite_of_isFinite B S hS
    (ObjectProperty.FullSubcategory.property _) (ObjectProperty.FullSubcategory.property _) _ hf

include hI

/-- **A finite inertia projection makes the stack quasi-DM over `S`** (Stacks 0CL0, part (5), at
the structure 1-morphism). -/
theorem isQuasiDMOver_of_isFinite_inertia : IsQuasiDMOver B S hS 𝒳 :=
  (isLocallyQuasiFinite_relativeInertiaProjection_iff_isQuasiDM_unconditional B S hS
    (structureMorphism B S hS 𝒳)).1 fun U y hy F hF he =>
      (isProper_and_isLocallyQuasiFinite_of_isFinite' B S hS _
        (relativeProperty_relativeInertiaProjection_structureMorphism B S hS 𝒳
          (fun _ _ m => Space.IsFinite B S hS m.hom) hI.2 U y hy F hF he)).2

/-- **A finite inertia projection makes the stack quasi-DM** in the absolute sense of
Stacks 050D (Stacks 050N, part (2)). -/
theorem isAbsolutelyQuasiDM_of_isFinite_inertia :
    AlgebraicStacks.IsAbsolutelyQuasiDM B S hS B.contains_terminal 𝒳 :=
  AlgebraicStacks.isAbsolutelyQuasiDM_of_isQuasiDMOver B S hS B.contains_terminal 𝒳
    (isQuasiDMOver_of_isFinite_inertia B S hS 𝒳 hI)

/-- **A finite inertia projection makes the diagonal `Δ_{𝒳/S}` separated** (Stacks 0CL0,
part (1), at the structure 1-morphism). -/
theorem isSeparated_relativeDiagonal_structureMorphism_of_isFinite_inertia :
    Stack.IsSeparated.{u, u, u + 1} B S hS
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳.val
        (schemeStack.{u, w} B S hS (Over.mk (𝟙 (B.obj hS)))).val
        (structureMorphism B S hS 𝒳).hom) :=
  (isSeparated_relativeInertiaProjection_iff_relativeDiagonal B S hS
    (structureMorphism B S hS 𝒳)).1 fun U y hy F hF he =>
      (isProper_and_isLocallyQuasiFinite_of_isFinite' B S hS _
        (relativeProperty_relativeInertiaProjection_structureMorphism B S hS 𝒳
          (fun _ _ m => Space.IsFinite B S hS m.hom) hI.2 U y hy F hF he)).1.1

/-- **A finite inertia projection is universally closed** in the sense of Stacks 0513 (by
Stacks 0512, a finite morphism of algebraic spaces being proper). -/
theorem universallyClosed_inertiaProjection_of_isFinite :
    AlgebraicStacks.UniversallyClosed B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳) := by
  have hUC : UniversallyClosed B S hS (inertiaProjectionAlgebraicStacks B S hS 𝒳).hom :=
    fun U y hy F hF he => (isProper_and_isLocallyQuasiFinite_of_isFinite' B S hS _
      (hI.2 U y hy F hF he)).1.2.2
  intro 𝒵 g
  exact (representable_universallyClosed_iff_closedMap_baseChange B S hS _ hI.1).1 hUC 𝒵 g

/-- **A finite inertia projection makes every automorphism group finite** (Remark 0DTU): the
automorphism group algebraic space `G_x = Isom_𝒳(x, x)` of a field-valued point `x` over `U` is
the base change of `I_𝒳 ⟶ 𝒳` along `x`, so it is finite over `S`, hence proper and locally
quasi-finite over `S`; both read over `U` (Stacks 04SG), and together they are finiteness over
`U` (Stacks 0A4X). -/
theorem automorphismGroupHasProperty_isFiniteOverBase_of_isFinite_inertia
    (x : AlgebraicStacks.points B S hS 𝒳) :
    AutomorphismGroupHasProperty B S hS (EtaleLocalStructure.IsFiniteOverBase B S hS) x := by
  intro p _
  let U := p.base
  let F := pointAutomorphismSpace B S hS 𝒳.val p
  have hF : IsAlgebraicSpace B U.left.1 U.left.2 F :=
    isAlgebraicSpace_pointAutomorphismSpace B S hS 𝒳.val 𝒳.property p
  have hfin : Space.IsFinite B S hS (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨F, hF⟩)).hom :=
    prop_isomSpace_of_inertiaProjection B S hS 𝒳 U (Functor.Fiber.mk p.over)
      (fun _ _ m => Space.IsFinite B S hS m.hom) hI.2
  obtain ⟨hpr, hlqf⟩ := isProper_and_isLocallyQuasiFinite_of_isFinite' B S hS _ hfin
  have : (Space.properProperty B S hS).RespectsIso :=
    (Space.isProper_isStableUnderBaseChange B S hS).respectsIso
  have h₁ : Space.IsProper B S hS (OverShriek.relocalizeToYoneda U.hom F) :=
    (prop_algebraicSpaceMap_iff B S hS (Space.properProperty B S hS) U F hF).mp hpr
  have h₂ := (Space.isProper_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom F hF).mp h₁
  have h₃ : Space.IsLocallyQuasiFinite B U.left.1 U.left.2
      ((Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2).from F) :=
    isLocallyQuasiFinite_of_algebraicSpaceMap hF hlqf
  have e : Space.toYonedaId B U.left.1 U.left.2 F =
      (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2).from F :=
    (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2).hom_ext _ _
  rw [e] at h₂
  have h₄ := Space.isFinite_of_isProper_of_isLocallyQuasiFinite B U.left.1 U.left.2 hF
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 _) _ h₂ h₃
  let t := (isTerminal_siteTerminalSpace B S hS U).from
    (yoneda.obj (Over.mk (𝟙 (B.obj U.left.2))))
  have : IsIso t := ⟨(Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2).from _,
    (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2).hom_ext _ _,
    (isTerminal_siteTerminalSpace B S hS U).hom_ext _ _⟩
  have e' : (isTerminal_siteTerminalSpace B S hS U).from F =
      (Space.isTerminal_yoneda_obj_base B U.left.1 U.left.2).from F ≫ t :=
    (isTerminal_siteTerminalSpace B S hS U).hom_ext _ _
  change Space.IsFinite B U.left.1 U.left.2 ((isTerminal_siteTerminalSpace B S hS U).from F)
  rw [e']
  exact Space.isFinite_comp B U.left.1 U.left.2 h₄ (Space.isFinite_of_isIso B U.left.1 U.left.2 t)

end AlgebraicGeometry.Stack

end
