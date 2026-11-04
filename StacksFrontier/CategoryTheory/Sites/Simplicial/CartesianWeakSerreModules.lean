module

public import Mathlib.AlgebraicTopology.SimplexCategory.MorphismProperty
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardRightExact
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionCocycle
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionNatural
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousDefs
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianWeakSerre
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToSheafColimits
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cartesian sheaves of modules form a weak Serre subcategory

Part (2) of Stacks 0D7J is the same statement one level up, for a sheaf of rings `O` on the
total site whose face transitions `f_{δ^n_j}` are flat: the cartesian `O`-modules form a weak
Serre subcategory of `Mod(O)`, and colimits of systems of cartesian `O`-modules are cartesian.
The transition whose invertibility is cartesianness is the one of Stacks 09WF on sheaves of
modules, `CategoryTheory.SimplicialSiteSituation.fiberTransitionModules`, and
`CategoryTheory.SimplicialSiteSituation.componentModuleTransition` presents it as a natural
transformation `g_m^* ⋙ f_φ^* ⟶ g_n^*` of the two restriction functors, which is the form the
four lemma consumes — exactly as `abelianFiberTransition` does for part (1).

The exactness inputs are four. Restriction `g_m^*` of sheaves of modules to a component
preserves finite limits for every continuous functor of sites, the left exact half of
Stacks 04BD (2); it preserves finite colimits because the component inclusion is cocontinuous,
hence almost cocontinuous (Stacks 04B7), which is the right exact half of Stacks 04BD (2). The
transition pullback `f_φ^*` preserves finite colimits with no hypothesis, being a left adjoint
(Stacks 03DC (2)). Its left exactness is where flatness enters, through Stacks 04JC, and by the
reduction to the face maps it is needed only at those.

For colimits, restriction of modules to a component preserves colimits indexed by a small
category: on underlying abelian sheaves it is restriction along the component inclusion, a left
adjoint since that inclusion is continuous and cocontinuous, and forgetting the module structure
preserves those colimits and reflects isomorphisms. The pullback `f_φ^*` is a left adjoint.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isCartesianModule_iff_faces`: **Stacks 07TG (3)**,
  the face criterion for a sheaf of modules.
* `CategoryTheory.SimplicialSiteSituation.isCartesianModule_isWeakSerreClass`: the weak Serre
  property, under left exactness of the face pullbacks.
* `CategoryTheory.SimplicialSiteSituation.isCartesianModule_isClosedUnderColimitsOfShape`:
  colimits of cartesian modules are cartesian.
* `CategoryTheory.SimplicialSiteSituation.isCartesianModule_weakSerre_colimits`:
  **Stacks 0D7J (2)**.

## Implementation notes

**Flatness and the pullback of modules.** Stacks 04JC is available as
`Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`, stated for the pullback
built over `AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom`, whereas
`Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules`, over which
`fiberTransitionModules` and hence `IsCartesianModule` are stated, is built over
`AlgebraicGeometry.RingedToposHom.toModulesHom`. The two data are equal by
`AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom`, which is how
`CategoryTheory.SimplicialSiteSituation.preservesFiniteLimits_transitionPullbackModules_of_isFlat`
transfers Stacks 04JC to a transition morphism.

**Why the face criterion is proved here.** The source checks the weak Serre conditions only at
the face maps, which is what makes flatness of the faces enough; the reduction is Stacks 07TG.
For sheaves of sets and of abelian groups that reduction is
`StacksFrontier/CategoryTheory/Sites/Simplicial/CartesianFaceCriterion.lean`, which does not import
the machinery of sheaves of modules used here, so the module case is proved in this module
rather than added there. Its proof is the same: the
simplex maps with invertible transition form a multiplicative class by the unit and cocycle laws
`fiberTransitionModules_id` and `fiberTransitionModules_comp`, every arrow of the simplex
category is a composite of faces and degeneracies, and `SimplexCategory.δ_comp_σ_self` reduces
the degeneracies to the faces.

**Why the instances are passed explicitly.** The structure sheaf of a component has two
spellings, `CategoryTheory.SimplicialSiteSituation.componentRingSheaf (S.totalRingSheaf O) n`
and `Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O`, equal by
`rfl` but only after unfolding the category of sheaves of modules over each; the first is the
codomain of the restriction functor and the second is the domain of the transition pullback, so
the two occur in one composite and instance search, which matches only up to reducible
unfolding, does not cross them. The exactness and zero-preservation facts are therefore handed
to the four lemma as explicit arguments, through the primed variants below, instead of being
found by instance resolution; the same reason is recorded in the implementation notes of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleTransition.lean`.

**Systems.** A system is indexed by a category whose objects form a set, read here as a
`u`-small category, `u` being the universe of the sections; that is what makes colimits of
abelian groups, and hence of sheaves of modules, exist.

## References

* [Stacks Project, Tag 0D7J](https://stacks.math.columbia.edu/tag/0D7J)
* [Stacks Project, Tag 07TG](https://stacks.math.columbia.edu/tag/07TG)
* [Stacks Project, Tag 04BD](https://stacks.math.columbia.edu/tag/04BD)
* [Stacks Project, Tag 04B7](https://stacks.math.columbia.edu/tag/04B7)
* [Stacks Project, Tag 03DC](https://stacks.math.columbia.edu/tag/03DC)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites
open scoped ZeroObject

universe u

namespace CategoryTheory.SimplicialSiteSituation

section Modules

open AlgebraicGeometry Stacks.Sheaves.RingedToposModules
open Stacks.SheafOfModules.PushforwardRightExact

/-- A functor carries an isomorphism to an isomorphism, with the hypothesis explicit. -/
@[sga "1 VI 6.12" "partial"]
private theorem isIso_map' {C : Type*} [Category C] {D : Type*} [Category D] (F : C ⥤ D)
    {X Y : C} {f : X ⟶ Y} (hf : IsIso f) : IsIso (F.map f) :=
  have := hf; inferInstance

/-- A composite of three isomorphisms is an isomorphism, with the hypotheses explicit. -/
private theorem isIso_comp₃' {C : Type*} [Category C] {W X Y Z : C} {f : W ⟶ X} {g : X ⟶ Y}
    {h : Y ⟶ Z} (hf : IsIso f) (hg : IsIso g) (hh : IsIso h) : IsIso (f ≫ g ≫ h) :=
  have := hf; have := hg; have := hh; inferInstance

/-- Cancelling an invertible first factor, with the hypotheses explicit. -/
private theorem isIso_of_isIso_comp_left' {C : Type*} [Category C] {X Y Z : C} (f : X ⟶ Y)
    (g : Y ⟶ Z) (hf : IsIso f) (h : IsIso (f ≫ g)) : IsIso g :=
  have := hf; (isIso_comp_left_iff f g).mp h

/-- An additive functor preserves zero morphisms, with the hypothesis explicit. -/
private theorem preservesZeroMorphisms_of_additive' {C : Type*} [Category C] {D : Type*}
    [Category D] [Preadditive C] [Preadditive D] {F : C ⥤ D} (hF : F.Additive) :
    F.PreservesZeroMorphisms :=
  have := hF; inferInstance

/-- A composite of two functors preserving zero morphisms preserves zero morphisms, with the
hypotheses explicit. -/
private theorem preservesZeroMorphisms_comp' {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] [Preadditive C] [Preadditive D] [Preadditive E]
    (F : C ⥤ D) (G : D ⥤ E) (hF : F.PreservesZeroMorphisms)
    (hG : G.PreservesZeroMorphisms) : (F ⋙ G).PreservesZeroMorphisms :=
  have := hF; have := hG; inferInstance

/-- `CategoryTheory.Limits.comp_preservesFiniteLimits` with its hypotheses explicit. -/
private theorem comp_preservesFiniteLimits' {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] (F : C ⥤ D) (G : D ⥤ E) (hF : PreservesFiniteLimits F)
    (hG : PreservesFiniteLimits G) : PreservesFiniteLimits (F ⋙ G) :=
  have := hF; have := hG; comp_preservesFiniteLimits F G

/-- `CategoryTheory.Limits.comp_preservesFiniteColimits` with its hypotheses explicit. -/
private theorem comp_preservesFiniteColimits' {C : Type*} [Category C] {D : Type*} [Category D]
    {E : Type*} [Category E] (F : C ⥤ D) (G : D ⥤ E) (hF : PreservesFiniteColimits F)
    (hG : PreservesFiniteColimits G) : PreservesFiniteColimits (F ⋙ G) :=
  have := hF; have := hG; comp_preservesFiniteColimits F G

/-- `CategoryTheory.Limits.comp_preservesColimitsOfShape` with its hypotheses explicit. -/
private theorem comp_preservesColimitsOfShape' {C : Type*} [Category C] {D : Type*}
    [Category D] {E : Type*} [Category E] (J : Type*) [Category J] (F : C ⥤ D) (G : D ⥤ E)
    (hF : PreservesColimitsOfShape J F) (hG : PreservesColimitsOfShape J G) :
    PreservesColimitsOfShape J (F ⋙ G) :=
  have := hF; have := hG; inferInstance

/-- A natural transformation between functors preserving zero morphisms is invertible at a zero
object, both values being zero. -/
private theorem isIso_app_zero' {C : Type*} [Category C] {D : Type*} [Category D]
    [Preadditive C] [Preadditive D] [HasZeroObject C] [HasZeroObject D]
    (F G : C ⥤ D) (hF : F.PreservesZeroMorphisms) (hG : G.PreservesZeroMorphisms)
    (η : F ⟶ G) : IsIso (η.app 0) :=
  have := hF; have := hG
  IsZero.isIso (Functor.map_isZero _ (isZero_zero _)) (Functor.map_isZero _ (isZero_zero _)) _

/-- `CategoryTheory.SimplicialSiteSituation.isIso_app_obj'_two_of_exact` with the exactness of
the two functors and the abelianness of the target as explicit arguments. -/
private theorem isIso_app_obj'_two_of_exact' {C : Type*} [Category C] {D : Type*} [Category D]
    [HasZeroObject C] [Preadditive C] (hD : Abelian D) (F G : C ⥤ D)
    (hFl : PreservesFiniteLimits F) (hFc : PreservesFiniteColimits F)
    (hGl : PreservesFiniteLimits G) (hGc : PreservesFiniteColimits G)
    (η : F ⟶ G) (T : ComposableArrows C 4) (hT : T.Exact)
    (h₀ : Epi (η.app (T.obj' 0))) (h₁ : IsIso (η.app (T.obj' 1)))
    (h₃ : IsIso (η.app (T.obj' 3))) (h₄ : Mono (η.app (T.obj' 4))) :
    IsIso (η.app (T.obj' 2)) :=
  have := hD; have := hFl; have := hFc; have := hGl; have := hGc
  isIso_app_obj'_two_of_exact F G η T hT h₀ h₁ h₃ h₄

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-- Abelian sheaves on the total site are sheafifiable at the site universe, the total category
being small there. This is what makes `Mod(O)` abelian. -/
noncomputable local instance hasSheafifyTotalModule :
    HasSheafify S.totalTopology AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} S.totalTopology

/-- On the total site at the site universe, sheafification of abelian sheaves inverts exactly
the locally bijective morphisms. -/
local instance wEqualsLocallyBijectiveTotalModule :
    S.totalTopology.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} S.totalTopology

/-- Abelian sheaves on a simplicial component are sheafifiable at the site universe. -/
noncomputable local instance hasSheafifyComponentModule (n : SimplexCategory) :
    HasSheafify (S.componentTopology n) AddCommGrpCat.{u} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat.{u, u, u} (S.componentTopology n)

/-- On a simplicial component at the site universe, sheafification of abelian sheaves inverts
exactly the locally bijective morphisms. -/
local instance wEqualsLocallyBijectiveComponentModule (n : SimplexCategory) :
    (S.componentTopology n).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat.{u, u, u} (S.componentTopology n)

/-- **Left exact half of Stacks 04BD (2)** at the component inclusion: restriction of sheaves of
modules to the degree-`n` component preserves finite limits. -/
local instance preservesFiniteLimits_componentModuleRestriction (n : SimplexCategory) :
    PreservesFiniteLimits (S.componentModuleRestriction (S.totalRingSheaf O) n) := by
  unfold componentModuleRestriction
  infer_instance

/-- **Right exact half of Stacks 04BD (2)** at the component inclusion: restriction of sheaves
of modules to the degree-`n` component preserves finite colimits. The component inclusion is
cocontinuous, hence almost cocontinuous in the sense of Stacks 04B7, which is the hypothesis
that half consumes. -/
local instance preservesFiniteColimits_componentModuleRestriction (n : SimplexCategory) :
    PreservesFiniteColimits (S.componentModuleRestriction (S.totalRingSheaf O) n) := by
  unfold componentModuleRestriction
  exact preservesFiniteColimits_pushforward_of_isAlmostCocontinuous (componentFunctor S n) _
    (isAlmostCocontinuous_of_isCocontinuous _ _ _)

/-- Restriction of sheaves of modules to a component preserves zero morphisms: it reindexes
components and restricts scalars along the identity, neither of which changes the underlying
additive maps. -/
local instance preservesZero_componentModuleRestriction (n : SimplexCategory) :
    (S.componentModuleRestriction (S.totalRingSheaf O) n).PreservesZeroMorphisms :=
  have : (S.componentModuleRestriction (S.totalRingSheaf O) n).Additive := ⟨rfl⟩
  inferInstance

variable {m n : SimplexCategory} (φ : m ⟶ n)

/-- The zero sheaf of `O`-modules has invertible transition along every simplex map: both
restrictions of it are zero. -/
theorem isIso_fiberTransitionModules_zero
    (hzero :
      ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules).PreservesZeroMorphisms) :
    IsIso (S.fiberTransitionModules O φ (0 : SheafOfModules.{u} (S.totalRingSheaf O))) := by
  rw [← S.componentModuleTransition_app O φ]
  exact isIso_app_zero' _ _
    (preservesZeroMorphisms_comp' (S.componentModuleRestriction (S.totalRingSheaf O) m)
      ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules) inferInstance hzero)
    (S.preservesZero_componentModuleRestriction O n) (S.componentModuleTransition O φ)

/-- **The four lemma at one simplex map.** If the transition along `φ` is invertible at the four
outer terms of a five term exact sequence of sheaves of `O`-modules, and the pullback `f_φ^*` of
sheaves of modules is left exact, then the transition along `φ` is invertible at the middle
term.

The transition is read as the natural transformation `componentModuleTransition` between the two
restriction functors; both are exact, the restrictions by Stacks 04BD (2) and `f_φ^*` by the
hypothesis together with Stacks 03DC (2). -/
theorem isIso_fiberTransitionModules_obj'_two
    (hlim : PreservesFiniteLimits ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules))
    (T : ComposableArrows (SheafOfModules.{u} (S.totalRingSheaf O)) 4) (hT : T.Exact)
    (h₀ : IsIso (S.fiberTransitionModules O φ (T.obj' 0)))
    (h₁ : IsIso (S.fiberTransitionModules O φ (T.obj' 1)))
    (h₃ : IsIso (S.fiberTransitionModules O φ (T.obj' 3)))
    (h₄ : IsIso (S.fiberTransitionModules O φ (T.obj' 4))) :
    IsIso (S.fiberTransitionModules O φ (T.obj' 2)) := by
  simp only [← S.componentModuleTransition_app O φ] at h₀ h₁ h₃ h₄ ⊢
  refine isIso_app_obj'_two_of_exact' inferInstance _ _
    (comp_preservesFiniteLimits' (S.componentModuleRestriction (S.totalRingSheaf O) m)
      ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules) inferInstance hlim)
    (comp_preservesFiniteColimits' (S.componentModuleRestriction (S.totalRingSheaf O) m)
      ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules) inferInstance
      (AlgebraicGeometry.RingedToposHom.pullbackModules_preservesFiniteColimits
        (S.transitionRingedToposHom O φ)))
    (S.preservesFiniteLimits_componentModuleRestriction O n)
    (S.preservesFiniteColimits_componentModuleRestriction O n)
    (S.componentModuleTransition O φ) T hT
    inferInstance h₁ h₃ inferInstance

/-- **Stacks 07TG (3).** A sheaf of `O`-modules on the total site of a simplicial site is
cartesian if and only if the canonical transition along every face map is an isomorphism.

The simplex maps whose transition is invertible form a multiplicative class, the identity and
composition laws being the unit and cocycle laws `fiberTransitionModules_id` and
`fiberTransitionModules_comp` of Stacks 09WF for modules. Every arrow of the simplex category is
a composite of faces and degeneracies, and `SimplexCategory.δ_comp_σ_self` exhibits each
degeneracy as the second factor of a composite that is an identity, so no separate hypothesis on
the degeneracies is needed. -/
@[stacks 07TG "face criterion for sheaves of modules"]
theorem isCartesianModule_iff_faces (M : SheafOfModules.{u} (S.totalRingSheaf O)) :
    IsCartesianModule S O M ↔
      ∀ (k : ℕ) (i : Fin (k + 2)),
        IsIso (S.fiberTransitionModules O (SimplexCategory.δ i) M) := by
  refine ⟨fun h k i => h _, fun h => ?_⟩
  have hid : ∀ k : SimplexCategory, IsIso (S.fiberTransitionModules O (𝟙 k) M) := by
    intro k
    rw [fiberTransitionModules_id]
    exact NatIso.hom_app_isIso _ _
  have hcomp : ∀ {l p q : SimplexCategory} (ψ : l ⟶ p) (χ : p ⟶ q),
      IsIso (S.fiberTransitionModules O ψ M) → IsIso (S.fiberTransitionModules O χ M) →
        IsIso (S.fiberTransitionModules O (ψ ≫ χ) M) := by
    intro l p q ψ χ hψ hχ
    rw [fiberTransitionModules_comp]
    exact isIso_comp₃' (NatIso.hom_app_isIso _ _) (isIso_map' _ hψ) hχ
  let W : MorphismProperty SimplexCategory :=
    fun _ _ χ => IsIso (S.fiberTransitionModules O χ M)
  have : W.ContainsIdentities := ⟨hid⟩
  have : W.IsStableUnderComposition := ⟨hcomp⟩
  have : W.IsMultiplicative := ⟨⟩
  have hσ : ∀ {k : ℕ} (i : Fin (k + 1)), W (SimplexCategory.σ i) := by
    intro k i
    have hc : IsIso (S.fiberTransitionModules O
        (SimplexCategory.δ i.castSucc ≫ SimplexCategory.σ i) M) := by
      rw [SimplexCategory.δ_comp_σ_self]
      exact hid _
    rw [fiberTransitionModules_comp] at hc
    exact isIso_of_isIso_comp_left' _ _ (isIso_map' _ (h _ i.castSucc))
      (isIso_of_isIso_comp_left' _ _
        (NatIso.hom_app_isIso (S.transitionPullbackModulesCompIso O
          (SimplexCategory.δ i.castSucc) (SimplexCategory.σ i)) _) hc)
  have hW := SimplexCategory.morphismProperty_eq_top W (fun i => h _ i) hσ
  intro p q χ
  exact show W χ by rw [hW]; trivial

/-- Let `O` be a sheaf of rings on the total site of a simplicial site such that the pullback of
sheaves of modules along the transition morphism of every face map is left exact. Then the
cartesian `O`-modules form a weak Serre subcategory of `Mod(O)`.

By Stacks 07TG (3) it is enough to test the face maps, which is why only the face transitions
occur in the hypothesis; at a face the conditions are the zero module, which is cartesian with
no hypothesis, and the four lemma applied to the transition read as a natural transformation of
the two restriction functors. -/
@[stacks 0D7J "part (2), cartesian modules are a weak Serre subcategory of Mod(O). The
hypothesis is left exactness of the pullback of sheaves of modules along the transition morphism
of each face map, which for a flat face transition is Stacks 04JC and is weaker than flatness of
the face transitions, so the statement is more general than the source's; the implementation
notes record why flatness itself cannot be fed in at this pullback. NOT covered here: the second
sentence of part (2), that colimits of systems of cartesian O-modules are cartesian, for which
the argument needs restriction of modules to a component to preserve colimits of arbitrary shape
and this development has only the finite case"]
theorem isCartesianModule_isWeakSerreClass
    (hflat : ∀ (k : ℕ) (i : Fin (k + 2)),
      PreservesFiniteLimits
        ((S.transitionRingedToposHom O (SimplexCategory.δ i)).toModulesHom.pullbackModules)) :
    ObjectProperty.IsWeakSerreClass (IsCartesianModule S O) := by
  refine (ObjectProperty.isWeakSerreClass_iff_prop_obj₂_of_exact (IsCartesianModule S O)).2 ?_
  constructor
  · refine ⟨(0 : SheafOfModules.{u} (S.totalRingSheaf O)), fun p q χ => ?_⟩
    exact S.isIso_fiberTransitionModules_zero O χ
      (preservesZeroMorphisms_of_additive'
        (AlgebraicGeometry.RingedToposHom.pullbackModules_additive
          (S.transitionRingedToposHom O χ)))
  · intro T hT h₀ h₁ h₃ h₄
    rw [S.isCartesianModule_iff_faces O (T.obj' 2)]
    intro k i
    exact S.isIso_fiberTransitionModules_obj'_two O (SimplexCategory.δ i) (hflat k i) T hT
      (h₀ _) (h₁ _) (h₃ _) (h₄ _)

/-! ### Colimits -/

/-- **Stacks 04JC** at a transition morphism: pullback of sheaves of modules along a flat
transition morphism of ringed topoi preserves finite limits. -/
theorem preservesFiniteLimits_transitionPullbackModules_of_isFlat
    {m n : SimplexCategory} (φ : m ⟶ n) (flat : (S.transitionRingedToposHom O φ).IsFlat) :
    PreservesFiniteLimits ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules) := by
  rw [AlgebraicGeometry.RingedToposHom.toModulesHom_eq_toRingedToposModulesHom
    (S.transitionRingedToposHom O φ)]
  exact ((exactFunctor_iff _).mp
    (Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap
      (S.transitionRingedToposHom O φ) flat)).1

/-- Restriction of sheaves of modules to a component preserves colimits indexed by a small
category. On underlying abelian sheaves it is restriction along the component inclusion, which
is a left adjoint because the inclusion is continuous and cocontinuous; forgetting the module
structure preserves such colimits and reflects isomorphisms. -/
theorem preservesColimitsOfShape_componentModuleRestriction (n : SimplexCategory)
    (J : Type*) [Category* J] [Small.{u} J] :
    PreservesColimitsOfShape J (S.componentModuleRestriction (S.totalRingSheaf O) n) := by
  let Rab := (componentFunctor S n).sheafPushforwardContinuous AddCommGrpCat.{u}
    (S.componentTopology n) S.totalTopology
  have hRab : PreservesColimitsOfShape J Rab :=
    let := ((componentFunctor S n).sheafAdjunctionCocontinuous AddCommGrpCat.{u}
      (S.componentTopology n) S.totalTopology).leftAdjoint_preservesColimits
    inferInstance
  have hT : PreservesColimitsOfShape J (SheafOfModules.toSheaf.{u} (S.totalRingSheaf O)) :=
    SheafOfModules.preservesColimitsOfShape_toSheaf _
  have hTn : PreservesColimitsOfShape J
      (SheafOfModules.toSheaf.{u} (S.componentRingSheaf (S.totalRingSheaf O) n)) :=
    SheafOfModules.preservesColimitsOfShape_toSheaf _
  have hcomp : PreservesColimitsOfShape J
      (S.componentModuleRestriction (S.totalRingSheaf O) n ⋙
        SheafOfModules.toSheaf.{u} (S.componentRingSheaf (S.totalRingSheaf O) n)) :=
    comp_preservesColimitsOfShape (SheafOfModules.toSheaf.{u} (S.totalRingSheaf O)) Rab
  have hrefl : ReflectsColimitsOfShape J
      (SheafOfModules.toSheaf.{u} (S.componentRingSheaf (S.totalRingSheaf O) n)) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  exact preservesColimitsOfShape_of_reflects_of_preserves _
    (SheafOfModules.toSheaf.{u} (S.componentRingSheaf (S.totalRingSheaf O) n))

/-- Colimits of cartesian sheaves of `O`-modules indexed by a small category are cartesian: both
restriction functors compared by the transition of Stacks 09WF preserve them, the pullback of
modules being a left adjoint. -/
theorem isCartesianModule_isClosedUnderColimitsOfShape (J : Type*) [Category* J]
    [Small.{u} J] : ObjectProperty.IsClosedUnderColimitsOfShape (IsCartesianModule S O) J := by
  constructor
  rintro X ⟨p⟩ m n φ
  have hP : PreservesColimitsOfShape J
      ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules) :=
    let := (S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules
      |>.leftAdjoint_preservesColimits
    inferInstance
  have hF : PreservesColimit p.diag (S.componentModuleRestriction (S.totalRingSheaf O) m ⋙
      (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules) :=
    (comp_preservesColimitsOfShape' J _ _
      (S.preservesColimitsOfShape_componentModuleRestriction O m J) hP).preservesColimit
  have hterm : ∀ j, IsIso ((S.componentModuleTransition O φ).app (p.diag.obj j)) := fun j => by
    rw [S.componentModuleTransition_app]
    exact p.prop_diag_obj j φ
  rw [← S.componentModuleTransition_app]
  exact @isIso_app_of_isColimit _ _ _ _ _ _ (S.componentModuleTransition O φ) J _ p.diag
    (Cocone.mk X p.ι) p.isColimit hF
    (S.preservesColimitsOfShape_componentModuleRestriction O n J).preservesColimit hterm

/-- **Stacks 0D7J (2).** Let `O` be a sheaf of rings on the total site of a simplicial site such
that the morphisms of ringed topoi `f_{δ^n_j} : (Sh(C_n), O_n) ⟶ (Sh(C_{n-1}), O_{n-1})` are
flat. Then the cartesian `O`-modules form a weak Serre subcategory of `Mod(O)`, and colimits of
systems of cartesian `O`-modules are cartesian.

Flatness of a face transition makes its pullback of modules exact (Stacks 04JC), which is what
the four lemma consumes; the colimit statement holds with no hypothesis. -/
@[stacks 0D7J "part (2)"]
theorem isCartesianModule_weakSerre_colimits
    (flat : ∀ (k : ℕ) (i : Fin (k + 2)),
      (S.transitionRingedToposHom O (SimplexCategory.δ i)).IsFlat) :
    ObjectProperty.IsWeakSerreClass (IsCartesianModule S O) ∧
      ∀ (J : Type*) [Category* J] [Small.{u} J],
        ObjectProperty.IsClosedUnderColimitsOfShape (IsCartesianModule S O) J :=
  ⟨S.isCartesianModule_isWeakSerreClass O fun k i =>
      S.preservesFiniteLimits_transitionPullbackModules_of_isFlat O _ (flat k i),
    fun J _ _ => S.isCartesianModule_isClosedUnderColimitsOfShape O J⟩

end Modules

end CategoryTheory.SimplicialSiteSituation

end
