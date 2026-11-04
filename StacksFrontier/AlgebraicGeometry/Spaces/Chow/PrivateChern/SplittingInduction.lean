module

public import Mathlib.Algebra.Category.Grp.Zero
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SplittingKernel
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SplittingTower
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeRankLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedInjective
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank
public import StacksFrontier.CategoryTheory.Sites.VanishingOnCovering
public import StacksFrontier.CategoryTheory.Subobject.FiltrationOfLength

/-!
# The induction of the splitting principle

In Situation 0EDT let `X/B` be good and let `E_1, …, E_n` be locally free `𝒪_X`-modules of ranks
`r_1, …, r_n`. The splitting principle (Stacks 0ESC) produces a morphism `π : P → X`, flat of
some relative dimension, with injective flat pullback on Chow groups after every base change,
such that every `π^*E_i` has a filtration with invertible successive quotients. Its proof is an
induction on `∑ r_i` whose step is the projective bundle of one `E_{i_0}` of positive rank: on
`𝐏(E_{i_0})` the kernel `E'` of the tautological quotient `π^*E_{i_0} → 𝒪(1)` has rank one less,
and it suffices to split `E'` together with the inverse images of the other `E_i`.

This file carries out that induction for an arbitrary *splitting step*: a morphism with the
required properties together with a submodule of `π^*E` of rank one less with invertible
quotient. The step itself, the projective bundle and the injectivity of its flat pullback, is
supplied separately.

## Main definitions

* `AlgebraicGeometry.Space.PrivateChern.HasSplittingStep`: a splitting step for one module.
* `AlgebraicGeometry.Space.PrivateChern.IsSplitting`: a splitting of a finite family of modules.

## Main results

* `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank.isZero_of_rank_zero`: a module of
  rank `0` is zero.
* `AlgebraicGeometry.Space.PrivateChern.isFiniteLocallyFreeOfRank_modulePullback`: the inverse
  image of a module of rank `r` along any morphism of algebraic spaces has rank `r`.
* `AlgebraicGeometry.Space.PrivateChern.hasFiltrationOfLength_modulePullback`: the inverse image
  along a flat morphism of a filtration with invertible quotients is one.
* `AlgebraicGeometry.Space.PrivateChern.hasSplittingStep_of_epi`: an epimorphism from `π^*E` onto
  an invertible module of rank one gives a splitting step, its kernel being the submodule.
* `AlgebraicGeometry.Space.PrivateChern.isSplitting_of_hasSplittingStep`: every finite family of
  locally free modules has a splitting, as soon as every module of positive rank has a splitting
  step.

## Implementation notes

The class of morphisms the splitting is to belong to (projective morphisms, in Stacks 0ESC) is a
parameter `Q`, asked only to contain the identities and to be stable under composition.

## References

* [Stacks Project, Tag 0ESC](https://stacks.math.columbia.edu/tag/0ESC)
* [Stacks Project, Tag 0ERV](https://stacks.math.columbia.edu/tag/0ERV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u u₁ v₁ w₁

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u₁, v₁, w₁})

/-- **A module of rank `0` is zero.** Over every member of a covering family it is a coproduct of
no copies of the structure sheaf, hence zero, so all its sections vanish. -/
theorem IsFiniteLocallyFreeOfRank.isZero_of_rank_zero
    {F : SheafOfModules.{w₁} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : IsFiniteLocallyFreeOfRank X F 0) : IsZero F := by
  have hsec : ∀ U : X.C, Subsingleton (F.val.obj (op U)) := by
    intro U
    obtain ⟨I, V, f, hcov, hfree⟩ := h U
    have hV : ∀ i, IsZero (((SheafOfModules.toSheaf _).obj F).obj.obj (op (V i))) := by
      intro i
      obtain ⟨ι, ⟨hc⟩⟩ := hfree i
      have h0 : 𝟙 (F.over (V i)) = 0 := Cofan.IsColimit.hom_ext hc _ _ (fun j => j.elim0)
      rw [AddCommGrpCat.isZero_iff_subsingleton]
      refine ⟨fun a b => ?_⟩
      have key : ∀ c : F.val.obj (op (V i)), c = 0 := fun c => by
        have := congrArg (fun φ : F.over (V i) ⟶ F.over (V i) =>
          (φ.val.app (op (Over.mk (𝟙 (V i))))).hom c) h0
        simp only [show (0 : F.over (V i) ⟶ F.over (V i)).val = 0 from rfl] at this
        exact this
      exact (key a).trans (key b).symm
    have hU := Sheaf.isZero_sections_of_isZero_sections_of_covering
      ((SheafOfModules.toSheaf _).obj F) (Presieve.ofArrows V f) hcov
      (fun Y g hg => by
        obtain ⟨i⟩ := hg
        exact hV i)
    rwa [AddCommGrpCat.isZero_iff_subsingleton] at hU
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact (hsec U.unop).elim _ _

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space.PrivateChern

attribute [local instance 10000] smallEtaleModulesAbelian

attribute [local instance 10000] abelian_modules

/-- The `𝒪_F`-modules on an algebraic space `F` have a zero object. -/
local instance (priority := 10000) hasZeroObject_modules {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasZeroObject (Modules.{u, u} B S hS F hF) :=
  @Abelian.hasZeroObject _ _ (abelian_modules B S hS F hF)

/-- The `𝒪_F`-modules on an algebraic space `F` have an initial object. -/
local instance (priority := 10000) hasInitial_modules {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasInitial (Modules.{u, u} B S hS F hF) :=
  @HasZeroObject.hasInitial _ _ (hasZeroObject_modules F hF)

/-- The initial morphisms of `𝒪_F`-modules are monomorphisms. -/
local instance (priority := 10000) initialMonoClass_modules {B : BigFppfSite.{u}}
    {S : Scheme.{u}} {hS : B.Contains S} (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) : InitialMonoClass (Modules.{u, u} B S hS F hF) :=
  @HasZeroObject.initialMonoClass _ _ (hasZeroObject_modules F hF)

/-- The `𝒪_F`-modules on an algebraic space have cokernels, from their abelian structure. -/
local instance (priority := 10000) hasCokernels_modules {B : BigFppfSite.{u}} {S : Scheme.{u}}
    {hS : B.Contains S} (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F) :
    HasCokernels (Modules.{u, u} B S hS F hF) :=
  letI := smallEtaleModulesAbelian B S hS (X := (⟨F, hF⟩ : AlgebraicSpaces B S hS))
  inferInstance

/-! ### Modules along morphisms of good spaces -/

section Modules

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The inverse image of a module of rank `r` has rank `r`**, along any morphism of algebraic
spaces: the rank is read on points, and every point of the target is in the rank locus of `r`. -/
theorem isFiniteLocallyFreeOfRank_modulePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {M : Modules.{u, u} B S hS Y.1 Y.2} {r : ℕ}
    (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS Y.1 Y.2) M r) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2)
      ((modulePullback B S hS f).obj M) r :=
  (isFiniteLocallyFreeOfRank_modulePullback_iff f h.isFiniteLocallyFreeOnSite r).2
    (fun _ _ => mem_rankLocus_of_isFiniteLocallyFreeOfRank h _)

/-- The invertible `𝒪_Z`-modules on an algebraic space `Z`, as a property of objects. -/
def invertibleModules (Z : AlgebraicSpaces B S hS) :
    ObjectProperty (Modules.{u, u} B S hS Z.1 Z.2) :=
  fun L => IsInvertibleModule Z L

/-- A module isomorphic to an invertible `𝒪_Z`-module is invertible. -/
instance isClosedUnderIsomorphisms_invertibleModules (Z : AlgebraicSpaces B S hS) :
    (invertibleModules B S hS Z).IsClosedUnderIsomorphisms where
  of_iso {L L'} e h := by
    have : IsInvertibleModule Z L := h
    exact Stacks.SheafOfModules.isInvertible_of_iso _ _ e

/-- The inverse image along a flat morphism of algebraic spaces preserves monomorphisms. -/
theorem preservesMonomorphisms_modulePullback_of_isFlat {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hf : IsFlat B S hS f.hom) : (modulePullback B S hS f).PreservesMonomorphisms :=
  have := preservesFiniteLimits_modulePullback_of_isFlat_hom B S hS f hf
  ⟨fun g _ => preserves_mono_of_preservesLimit _ g⟩

/-- **Inverse images of filtrations along a flat morphism.** The inverse image along a flat
morphism of algebraic spaces carries a filtration with invertible successive quotients to a
filtration with invertible successive quotients. -/
theorem hasFiltrationOfLength_modulePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFlat B S hS f.hom) {r : ℕ} {M : Modules.{u, u} B S hS Y.1 Y.2}
    (h : (invertibleModules B S hS Y).HasFiltrationOfLength r M) :
    (invertibleModules B S hS X).HasFiltrationOfLength r ((modulePullback B S hS f).obj M) := by
  have := preservesMonomorphisms_modulePullback_of_isFlat B S hS f hf
  have := (modulePullbackAdjunction B S hS f).isLeftAdjoint
  have := (modulePullbackAdjunction B S hS f).leftAdjoint_preservesColimits
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint (modulePullback B S hS f)
  exact h.map (Q := invertibleModules B S hS X) (modulePullback B S hS f)
    (fun L hL => modulePullbackInvertible f L hL)

/-- **Extending a filtration along a flat inverse image.** If `ι : E' → M` is a monomorphism with
invertible cokernel and the inverse image of `E'` along a flat morphism `f` has a filtration of
length `s` with invertible quotients, then the inverse image of `M` has one of length `s + 1`. -/
theorem hasFiltrationOfLength_succ_modulePullback {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    (hf : IsFlat B S hS f.hom) {s : ℕ} {E' M : Modules.{u, u} B S hS Y.1 Y.2} (ι : E' ⟶ M)
    [Mono ι] (hι : IsInvertibleModule Y (cokernel ι))
    (h : (invertibleModules B S hS X).HasFiltrationOfLength s ((modulePullback B S hS f).obj E')) :
    (invertibleModules B S hS X).HasFiltrationOfLength (s + 1)
      ((modulePullback B S hS f).obj M) := by
  have := preservesMonomorphisms_modulePullback_of_isFlat B S hS f hf
  have := (modulePullbackAdjunction B S hS f).isLeftAdjoint
  have := (modulePullbackAdjunction B S hS f).leftAdjoint_preservesColimits
  have : Mono ((modulePullback B S hS f).map ι) := Functor.map_mono _ _
  exact .succ ((modulePullback B S hS f).map ι) h
    ((invertibleModules B S hS X).prop_of_iso
      (PreservesCokernel.iso (modulePullback B S hS f) ι) (modulePullbackInvertible f _ hι))

end Modules

/-! ### The induction -/

/-- Lowering one term of a sum of natural numbers by one lowers the sum by one. -/
theorem sum_update_eq_of_eq_add_one {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ι → ℕ}
    {i₀ : ι} {s n : ℕ} (hs : r i₀ = s + 1) (hn : ∑ i, r i = n + 1) :
    ∑ i, Function.update r i₀ s i = n := by
  have h1 := Finset.sum_update_of_mem (Finset.mem_univ i₀) r s
  have h2 := Finset.add_sum_erase Finset.univ r (Finset.mem_univ i₀)
  rw [Finset.sdiff_singleton_eq_erase] at h1
  omega

section Induction

variable (D : BaseSpaceDimensionSituation.{u})

/-- The inverse image of modules along a morphism `π : P → X` of algebraic spaces over the base
of Situation 0EDT, given as a morphism of presheaves. -/
abbrev spaceModulePullback {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hP : IsAlgebraicSpace D.site D.base D.base_mem P) (π : P ⟶ X) :
    Modules.{u, u} D.site D.base D.base_mem X hX ⥤ Modules.{u, u} D.site D.base D.base_mem P hP :=
  modulePullback D.site D.base D.base_mem
    (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX⟩)

/-- **A splitting step** for a module `E` on a good algebraic space `X/B`: a morphism
`π : P → X` of good algebraic spaces over `B` with property `Q`, flat of relative dimension `d`,
with injective flat pullback on Chow groups after every base change, together with a submodule
`E' ⊆ π^*E` locally free of rank `s` whose quotient `π^*E / E'` is invertible.

The projective bundle of a module `E` of rank `s + 1`, with `E'` the kernel of the tautological
quotient `π^*E → 𝒪_P(1)`, is such a step (Stacks 0ERV). -/
def HasSplittingStep (Q : MorphismProperty ((BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u))
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : ℕ) : Prop :=
  ∃ (P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u) (sP : P ⟶ D.space)
    (hP : D.IsGood sP) (π : P ⟶ X) (_ : π ≫ sX = sP) (d : ℕ)
    (_ : IsFlat D.site D.base D.base_mem π)
    (_ : HasRelativeDimension d D.site D.base D.base_mem π),
    Q π ∧ HasInjectiveChowBaseChange.{v} D sX π d ∧
      ∃ (E' : Modules.{u, u} D.site D.base D.base_mem P hP.1)
        (ι : E' ⟶ (spaceModulePullback D hX.1 hP.1 π).obj E) (_ : Mono ι),
        RingedSite.IsFiniteLocallyFreeOfRank
          (smallEtaleRingedSite D.site D.base D.base_mem P hP.1) E' s ∧
        IsInvertibleModule ⟨P, hP.1⟩ (cokernel ι)

/-- **A splitting** of a finite family of modules `E_i` on a good algebraic space `X/B`, with
ranks `r_i`: a morphism `π : P → X` of good algebraic spaces over `B` with property `Q`, flat of
relative dimension `d`, with injective flat pullback on Chow groups after every base change,
such that every `π^*E_i` has a filtration of length `r_i` with invertible successive
quotients. -/
def IsSplitting (Q : MorphismProperty ((BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u))
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    {ι : Type*} (E : ι → Modules.{u, u} D.site D.base D.base_mem X hX.1) (r : ι → ℕ) : Prop :=
  ∃ (P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u) (sP : P ⟶ D.space)
    (hP : D.IsGood sP) (π : P ⟶ X) (_ : π ≫ sX = sP) (d : ℕ)
    (_ : IsFlat D.site D.base D.base_mem π)
    (_ : HasRelativeDimension d D.site D.base D.base_mem π),
    Q π ∧ HasInjectiveChowBaseChange.{v} D sX π d ∧
      ∀ i, (invertibleModules D.site D.base D.base_mem ⟨P, hP.1⟩).HasFiltrationOfLength (r i)
        ((spaceModulePullback D hX.1 hP.1 π).obj (E i))

/-- **The identity splits a family of modules of rank `0`**, since a module of rank `0` is zero. -/
theorem isSplitting_id_of_rank_eq_zero
    (Q : MorphismProperty ((BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u))
    [Q.ContainsIdentities] {ι : Type*} {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (E : ι → Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (r : ι → ℕ)
    (hE : ∀ i, RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) (E i) (r i))
    (hr : ∀ i, r i = 0) : IsSplitting.{v} D Q sX hX E r := by
  have het : IsEtale D.site D.base D.base_mem (𝟙 X) :=
    isEtale_of_isIso D.site D.base D.base_mem (𝟙 X)
  refine ⟨X, sX, hX, 𝟙 X, Category.id_comp sX, 0,
    isFlat_of_isEtale D.site D.base D.base_mem het,
    hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem (𝟙 X) hX.1 het,
    Q.id_mem X, hasInjectiveChowBaseChange_id.{v} D sX, fun i => ?_⟩
  have hz : IsZero (E i) := (hr i ▸ hE i).isZero_of_rank_zero
  have := (modulePullbackAdjunction D.site D.base D.base_mem
    (ObjectProperty.homMk (𝟙 X) : (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶
      ⟨X, hX.1⟩)).isLeftAdjoint
  have := Functor.preservesZeroMorphisms_of_isLeftAdjoint
    (spaceModulePullback D hX.1 hX.1 (𝟙 X))
  rw [hr i]
  exact .zero ((spaceModulePullback D hX.1 hX.1 (𝟙 X)).map_isZero hz)

/-- The inverse image along `π : P → X` of a module of rank `r` has rank `r`. -/
private theorem isFiniteLocallyFreeOfRank_spaceModulePullback
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hP : IsAlgebraicSpace D.site D.base D.base_mem P) (π : P ⟶ X)
    {E : Modules.{u, u} D.site D.base D.base_mem X hX} {r : ℕ}
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX) E r) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite D.site D.base D.base_mem P hP)
      ((spaceModulePullback D hX hP π).obj E) r :=
  isFiniteLocallyFreeOfRank_modulePullback D.site D.base D.base_mem
    (ObjectProperty.homMk π : (⟨P, hP⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX⟩) hE

/-- **Ranks of a family updated by a submodule.** Pulling back a family of locally free modules
along `π` and replacing the `i₀`-th member by a module of rank `s` gives a family of locally free
modules of the updated ranks. -/
theorem isFiniteLocallyFreeOfRank_update_modulePullback {ι : Type*} [DecidableEq ι]
    {X P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace D.site D.base D.base_mem X)
    (hP : IsAlgebraicSpace D.site D.base D.base_mem P) (π : P ⟶ X)
    (E : ι → Modules.{u, u} D.site D.base D.base_mem X hX) (r : ι → ℕ)
    (hE : ∀ i, RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX) (E i) (r i))
    (i₀ : ι) {E' : Modules.{u, u} D.site D.base D.base_mem P hP} {s : ℕ}
    (hE' : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem P hP) E' s) (i : ι) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite D.site D.base D.base_mem P hP)
      (Function.update (fun i => (spaceModulePullback D hX hP π).obj (E i)) i₀ E' i)
      (Function.update r i₀ s i) := by
  by_cases hi : i = i₀
  · subst hi
    simpa using hE'
  · simp only [Function.update_of_ne hi]
    exact isFiniteLocallyFreeOfRank_spaceModulePullback D hX hP π (hE i)

/-- **The splitting principle, from its inductive step.** Let `Q` be a class of morphisms
containing the identities and stable under composition, and suppose every module of rank
`s + 1` on a good algebraic space over `B` has a splitting step with property `Q`. Then every
finite family of locally free modules `E_i` of ranks `r_i` on a good algebraic space `X/B` has a
splitting with property `Q`.

This is the induction on `∑ r_i` of the proof of Stacks 0ESC: when all ranks vanish the identity
splits the family, since a module of rank `0` is zero; otherwise a splitting step for one `E_{i_0}`
of positive rank replaces `E_{i_0}` by the submodule `E'` of `π^*E_{i_0}` of rank one less, and the
other `E_i` by their inverse images, and a splitting of the new family composes with the step. -/
theorem isSplitting_of_hasSplittingStep
    (Q : MorphismProperty ((BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u))
    [Q.ContainsIdentities] [Q.IsStableUnderComposition]
    (step : ∀ {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
      (hX : D.IsGood sX) (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : ℕ),
      RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite D.site D.base D.base_mem X hX.1)
        E (s + 1) → HasSplittingStep.{v} D Q sX hX E s)
    {ι : Type*} [Finite ι] {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
    (sX : X ⟶ D.space) (hX : D.IsGood sX) (E : ι → Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (r : ι → ℕ)
    (hE : ∀ i, RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) (E i) (r i)) :
    IsSplitting.{v} D Q sX hX E r := by
  classical
  have := Fintype.ofFinite ι
  suffices key : ∀ (n : ℕ) {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u}
      (sX : X ⟶ D.space) (hX : D.IsGood sX)
      (E : ι → Modules.{u, u} D.site D.base D.base_mem X hX.1) (r : ι → ℕ),
      (∀ i, RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) (E i) (r i)) →
      ∑ i, r i = n → IsSplitting.{v} D Q sX hX E r from key _ sX hX E r hE rfl
  intro n
  induction n with
  | zero =>
    intro X sX hX E r hE hn
    exact isSplitting_id_of_rank_eq_zero D Q sX hX E r hE fun i =>
      Finset.sum_eq_zero_iff.mp hn i (Finset.mem_univ i)
  | succ n ih =>
    intro X sX hX E r hE hn
    obtain ⟨i₀, hi₀⟩ : ∃ i₀, r i₀ ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      simp [hall] at hn
    obtain ⟨s, hs⟩ : ∃ s, r i₀ = s + 1 := Nat.exists_eq_succ_of_ne_zero hi₀
    obtain ⟨P₁, sP₁, hP₁, π₁, hπ₁, d₁, hf₁, hd₁, hQ₁, hinj₁, E', ιE, hιE, hE', hcok⟩ :=
      step sX hX (E i₀) s (hs ▸ hE i₀)
    let E₁ : ι → Modules.{u, u} D.site D.base D.base_mem P₁ hP₁.1 :=
      Function.update (fun i => (spaceModulePullback D hX.1 hP₁.1 π₁).obj (E i)) i₀ E'
    let r₁ : ι → ℕ := Function.update r i₀ s
    have hE₁ : ∀ i, RingedSite.IsFiniteLocallyFreeOfRank
        (smallEtaleRingedSite D.site D.base D.base_mem P₁ hP₁.1) (E₁ i) (r₁ i) :=
      isFiniteLocallyFreeOfRank_update_modulePullback D hX.1 hP₁.1 π₁ E r hE i₀ hE'
    obtain ⟨P₂, sP₂, hP₂, π₂, hπ₂, d₂, hf₂, hd₂, hQ₂, hinj₂, hfil⟩ :=
      ih (π₁ ≫ sX) (hπ₁ ▸ hP₁) E₁ r₁ hE₁ (sum_update_eq_of_eq_add_one hs hn)
    have hcomp := isFlat_and_hasRelativeDimension_comp D sP₂ hP₂ sP₁ hP₁ sX hX π₂ π₁
      (by rwa [← hπ₁]) hπ₁ d₂ d₁ hf₂ hd₂ hf₁ hd₁
    refine ⟨P₂, sP₂, hP₂, π₂ ≫ π₁, (Category.assoc _ _ _).trans hπ₂, d₂ + d₁, hcomp.2.1,
      hcomp.2.2, Q.comp_mem _ _ hQ₂ hQ₁, HasInjectiveChowBaseChange.comp D hinj₁ hinj₂,
      fun i => ?_⟩
    let g₂ : (⟨P₂, hP₂.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨P₁, hP₁.1⟩ :=
      ObjectProperty.homMk π₂
    let g₁ : (⟨P₁, hP₁.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) ⟶ ⟨X, hX.1⟩ :=
      ObjectProperty.homMk π₁
    have := isClosedUnderIsomorphisms_invertibleModules D.site D.base D.base_mem ⟨P₂, hP₂.1⟩
    refine ObjectProperty.HasFiltrationOfLength.of_iso
      ((modulePullbackCompIso D.site D.base D.base_mem g₂ g₁).app (E i)) ?_
    rcases eq_or_ne i i₀ with rfl | hi
    · rw [hs]
      exact hasFiltrationOfLength_succ_modulePullback D.site D.base D.base_mem g₂ hf₂ ιE hcok
        (by simpa [E₁, r₁] using hfil i)
    · simpa [E₁, r₁, Function.update_of_ne hi] using hfil i

/-- **A splitting step from a quotient of rank one.** Let `π : P → X` be a morphism of good
algebraic spaces over `B` with property `Q`, flat of relative dimension `d`, with injective flat
pullback on Chow groups after every base change, and let `τ : π^*E → L` be an epimorphism onto an
invertible module locally free of rank one, for a module `E` of rank `s + 1`. Then the kernel
of `τ`, which has rank `s`, is a splitting step for `E`. For the projective bundle of `E`, `τ` is
the tautological quotient `π^*E → 𝒪_P(1)`. -/
theorem hasSplittingStep_of_epi
    (Q : MorphismProperty ((BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u))
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (s : ℕ)
    (hE : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E (s + 1))
    {P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sP : P ⟶ D.space)
    (hP : D.IsGood sP) (π : P ⟶ X) (hπ : π ≫ sX = sP) (d : ℕ)
    (hflat : IsFlat D.site D.base D.base_mem π)
    (hd : HasRelativeDimension d D.site D.base D.base_mem π) (hQ : Q π)
    (hinj : HasInjectiveChowBaseChange.{v} D sX π d)
    (L : Modules.{u, u} D.site D.base D.base_mem P hP.1)
    (τ : (spaceModulePullback D hX.1 hP.1 π).obj E ⟶ L) [Epi τ]
    (hL : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem P hP.1) L 1)
    (hLinv : IsInvertibleModule ⟨P, hP.1⟩ L) :
    HasSplittingStep.{v} D Q sX hX E s := by
  refine ⟨P, sP, hP, π, hπ, d, hflat, hd, hQ, hinj, kernel τ, kernel.ι τ, inferInstance,
    isFiniteLocallyFreeOfRank_kernel_of_epi D.site D.base D.base_mem P hP.1 τ
      (isFiniteLocallyFreeOfRank_spaceModulePullback D hX.1 hP.1 π hE) hL, ?_⟩
  have e : cokernel (kernel.ι τ) ≅ L :=
    IsColimit.coconePointUniqueUpToIso (colimit.isColimit _)
      (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel τ))
  have := isClosedUnderIsomorphisms_invertibleModules D.site D.base D.base_mem ⟨P, hP.1⟩
  exact (invertibleModules D.site D.base D.base_mem ⟨P, hP.1⟩).prop_of_iso e.symm hLinv

/-- **A splitting, in the form of the splitting principle.** A splitting of `E_i` of ranks
`r_i` gives a morphism `π : P → X` of good algebraic spaces over `B` with property `Q`, flat of
relative dimension `d`, such that for every morphism `f : Y → X` of good algebraic spaces over
`B` and every fibre product `Y ×_X P` the flat pullback `CH_k(Y) → CH_{k+d}(Y ×_X P)` is
injective, and such that every `π^*E_i` has a filtration
`0 = F_0 ⊂ F_1 ⊂ ⋯ ⊂ F_{r_i} = π^*E_i` by subobjects whose successive quotients are
invertible. -/
theorem IsSplitting.exists_subobject_filtration
    {Q : MorphismProperty ((BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u)}
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {ι : Type*} {E : ι → Modules.{u, u} D.site D.base D.base_mem X hX.1}
    {r : ι → ℕ} (h : IsSplitting.{v} D Q sX hX E r) :
    ∃ (P : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u) (sP : P ⟶ D.space)
      (hP : D.IsGood sP) (π : P ⟶ X) (hπ : π ≫ sX = sP) (d : ℕ)
      (hflat : IsFlat D.site D.base D.base_mem π)
      (hd : HasRelativeDimension d D.site D.base D.base_mem π),
      Q π ∧ HasInjectiveChowPullbacks.{v} D sX hX sP hP π hπ d hflat hd ∧
        ∀ i, ∃ (F : Fin (r i + 1) → Subobject ((spaceModulePullback D hX.1 hP.1 π).obj (E i)))
          (hF : Monotone F), F 0 = ⊥ ∧ F (Fin.last (r i)) = ⊤ ∧
            ∀ j : Fin (r i), IsInvertibleModule ⟨P, hP.1⟩
              (cokernel (Subobject.ofLE (F j.castSucc) (F j.succ) (hF j.castSucc_le_succ))) := by
  obtain ⟨P, sP, hP, π, hπ, d, hflat, hd, hQ, hinj, hfil⟩ := h
  have := isClosedUnderIsomorphisms_invertibleModules D.site D.base D.base_mem ⟨P, hP.1⟩
  exact ⟨P, sP, hP, π, hπ, d, hflat, hd, hQ, hinj.hasInjectiveChowPullbacks D hX hP hπ hflat hd,
    fun i => (hfil i).exists_subobject⟩

end Induction

end AlgebraicGeometry.Space.PrivateChern

end
