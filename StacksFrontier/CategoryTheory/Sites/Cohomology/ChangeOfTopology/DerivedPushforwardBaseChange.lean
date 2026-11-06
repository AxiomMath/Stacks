module

public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import StacksFrontier.Algebra.Homology.DerivedCategory.AcyclicPreservesHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorPlusResolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.Cohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.ComparisonClassWeakSerre
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedBaseChange
public import StacksFrontier.Homology.DerivedIndexing.Basic
import StacksCore.Tactic.StacksAttribute

/-!
# Derived base change for a change of topology

In the situation of Stacks 0EZ3 write `ε_X : C_τ/X ⟶ C_τ'/X` for the change-of-topology
morphism from the finer site to the coarser one, and let `f : X ⟶ Y` be a morphism of `C`. The
canonical derived base change map

`ε_Y^{-1} R f_{τ',*} ⟶ R f_{τ,*} ε_X^{-1}`

on bounded below derived categories is `Stacks.ComparingTopologies.derivedComparisonBaseChange`,
constructed in
`StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DerivedBaseChange`. This file
proves the **base change half of part (2) of Stacks 0EZF**: that map is an isomorphism at every
object of `D⁺(C_{τ'}/X)` all of whose cohomology sheaves lie in the weak Serre class `𝒜'_X`.

## Main results

* `Stacks.ComparingTopologies.isIso_derivedComparisonBaseChange_app`: the derived base change
  map is invertible on `D⁺_{𝒜'_X}`.
* `CategoryTheory.Functor.rightAcyclic_cycles_and_preservesLeftHomologyOf_of_isStrictlyGE`:
  Leray's acyclicity argument for a `ℤ`-indexed complex bounded below.
* `CategoryTheory.Functor.quasiIso_adjointCochainComplexMap`: the degreewise adjoint of a
  quasi-isomorphism is a quasi-isomorphism, under acyclicity hypotheses on the target and
  invertibility of the unit on the cohomology of the source.

## The shape of the argument

The vanishing conditions `(V_n)` of the situation enter in exactly one place, and are carried as
the hypothesis `hV : ∀ n, S.vanishingCondition n` — the first assertion of Stacks 0EZF, proved
elsewhere. What they give is that every sheaf of `𝒜_X` is *right acyclic* for the
change-of-topology direct image `ε_{X,*}`, which is
`CohomologyComparison.abelianComparisonPushforward_rightAcyclic_of_fineWeakSerre`
of `ChangeOfTopology/ComparisonClassWeakSerre.lean`.

The object `K'` is replaced by a bounded below complex `I` of injective sheaves on the coarse
localized site whose cohomology lies in `𝒜'_X`, which is legitimate by
`CategoryTheory.DerivedCategory.Plus.exists_injective_nonempty_iso`. Because `I` is termwise
injective the unit of right derivation of `f_{τ',*}` is invertible at `I`, so the defining
equation `derivedComparisonBaseChange_fac` reduces the claim to the invertibility of
`derivedComparisonBaseChangeOnHomotopy` at `I`.

That in turn is checked after composing with one further isomorphism. Choose a
quasi-isomorphism `φ : ε_X^{-1} I ⟶ J` with `J` bounded below and termwise injective; then the
composite of the degreewise base change map with `f_{τ,*}(φ)` is, by the mate description of the
base change map, the image under `ε_Y^{-1} f_{τ',*}` of the degreewise adjoint `I ⟶ ε_{X,*} J`
of `φ`, followed by the counit of the change-of-topology adjunction. The counit is invertible
because the change-of-topology direct image is fully faithful, and the adjoint map is a homotopy
equivalence because both `I` and `ε_{X,*} J` are K-injective and the map is a
quasi-isomorphism. That last point is the only computation: `ε_{X,*}` is left exact and right
acyclic on the terms of `J` (they are injective) and on its cohomology sheaves (they lie in
`𝒜_X`, where `(V_n)` applies), hence computes the cohomology of `ε_{X,*} J` degreewise, and the
resulting map on cohomology is the change-of-topology unit at `H^n(I)`, which is invertible
because `H^n(I)` lies in `𝒜'_X`.

## Implementation notes

Two pieces of homological algebra are proved in the generality in which they are true, before
the situation of the tag is introduced.

`rightAcyclic_cycles_and_preservesLeftHomologyOf_of_isStrictlyGE` is Leray's acyclicity argument
`CategoryTheory.Functor.rightAcyclic_cycles_and_preservesLeftHomologyOf`, which is stated for a
single short complex, run over the degrees of a `ℤ`-indexed complex bounded below. It is the
counterpart of the `ℕ`-indexed
`CategoryTheory.Functor.rightAcyclic_cycles_and_preservesLeftHomologyOf_sc`; the induction starts
at the lower bound, and the degrees below it are handled separately, the cycles being zero there.

`quasiIso_adjointCochainComplexMap` identifies the map induced on homology by a degreewise
adjoint. The identification is carried by
`CategoryTheory.ShortComplex.adjointLeftHomologyMapData`, which takes the components of a left
homology map data for `φ` and returns one for its adjoint. Its target left homology data has to
be `ShortComplex.LeftHomologyData.mapExpand` rather than `ShortComplex.LeftHomologyData.map`:
the two are the same data, but the projections of the latter do not reduce at reducible
transparency, so a goal mentioning them is not type-correct there and no rewrite inside it finds
its pattern. The components of the adjunction unit are likewise taken as an abstract natural
family, for the same reason: `(E ⋙ G).obj` does not reduce either.

The distinguished class `P` of the situation plays no role here: the base change map is
invertible on `D⁺_{𝒜'_X}` for *every* morphism `f` of `C`. It is the membership assertion of the
same clause — that `R f_{τ',*} K'` again has cohomology in `𝒜'` — which needs `f` in `P`, and
that is
`Stacks.ComparingTopologies.rightDerivedPushforward_mem_derivedCategoryBPlus`.

## References

* [Stacks Project, Tag 0EZF](https://stacks.math.columbia.edu/tag/0EZF)
* [Stacks Project, Tag 0EZ3](https://stacks.math.columbia.edu/tag/0EZ3)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

universe v u

open CategoryTheory CategoryTheory.Limits

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

namespace CategoryTheory.ShortComplex

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  {S₁ : ShortComplex A} {S₂ : ShortComplex B}
  {E : A ⥤ B} {G : B ⥤ A} [E.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]

/-- **The image of a left homology datum under a functor preserving it**, spelled out field by
field so that its projections reduce at reducible transparency.

This is `ShortComplex.LeftHomologyData.map`, whose projections are behind a definition which
reducible unfolding does not reach, with the consequence that a goal mentioning them is not
type-correct at that transparency and rewriting inside it fails to find its patterns. -/
noncomputable abbrev LeftHomologyData.mapExpand (h : S₂.LeftHomologyData)
    [h.IsPreservedBy G] : (S₂.map G).LeftHomologyData where
  K := G.obj h.K
  H := G.obj h.H
  i := G.map h.i
  π := G.map h.π
  wi := (h.map G).wi
  hi := (h.map G).hi
  wπ := (h.map G).wπ
  hπ := (h.map G).hπ

/-- The induced map to the cycles of `mapExpand` is the image of the induced map to the
cycles. -/
lemma LeftHomologyData.mapExpand_f' (h : S₂.LeftHomologyData) [h.IsPreservedBy G] :
    (h.mapExpand (G := G)).f' = G.map h.f' := by
  have : Mono (h.mapExpand (G := G)).i := mono_of_isLimit_fork (h.mapExpand (G := G)).hi
  rw [← cancel_mono (h.mapExpand (G := G)).i, LeftHomologyData.f'_i]
  show (S₂.map G).f = G.map h.f' ≫ G.map h.i
  rw [← G.map_comp, LeftHomologyData.f'_i]
  rfl

/-- **The left homology map data of a degreewise adjoint morphism.** Let `E` and `G` be
functors with a natural family `u : X ⟶ G(E(X))` satisfying the unit naturality of an
adjunction, let `φ : S₁.map E ⟶ S₂` have left homology map data with components `dK`, `dH`
relative to data `h₁` on the source and `h₂` on the target, and let `ψ : S₁ ⟶ S₂.map G` be a
morphism whose first two components are the adjoints of those of `φ`. Then `ψ` has left
homology map data relative to `h₁` and `h₂`, with components the adjoints of `dK` and `dH`.

Every commutation is the naturality of `u` together with the corresponding commutation for
`φ`. -/
noncomputable def adjointLeftHomologyMapData
    (h₁ : S₁.LeftHomologyData) (h₂ : S₂.LeftHomologyData)
    [h₂.IsPreservedBy G] {ψ : S₁ ⟶ S₂.map G}
    (u : ∀ X : A, X ⟶ G.obj (E.obj X))
    (hu : ∀ {X Y : A} (f : X ⟶ Y), u X ≫ G.map (E.map f) = f ≫ u Y)
    (dK : E.obj h₁.K ⟶ h₂.K) (dH : E.obj h₁.H ⟶ h₂.H)
    (τ₁ : E.obj S₁.X₁ ⟶ S₂.X₁) (τ₂ : E.obj S₁.X₂ ⟶ S₂.X₂)
    (hψ₁ : ψ.τ₁ = u S₁.X₁ ≫ G.map τ₁)
    (hψ₂ : ψ.τ₂ = u S₁.X₂ ≫ G.map τ₂)
    (hi : dK ≫ h₂.i = E.map h₁.i ≫ τ₂)
    (hf' : E.map h₁.f' ≫ dK = τ₁ ≫ h₂.f')
    (hπ : E.map h₁.π ≫ dH = dK ≫ h₂.π) :
    LeftHomologyMapData ψ h₁ h₂.mapExpand where
  φK := u h₁.K ≫ G.map dK
  φH := u h₁.H ≫ G.map dH
  commi := by
    change (u h₁.K ≫ G.map dK) ≫ G.map h₂.i = h₁.i ≫ ψ.τ₂
    rw [hψ₂, Category.assoc, ← G.map_comp, hi, G.map_comp, ← Category.assoc (u h₁.K), hu,
      Category.assoc]
  commf' := by
    change h₁.f' ≫ u h₁.K ≫ G.map dK = ψ.τ₁ ≫ (h₂.mapExpand (G := G)).f'
    rw [LeftHomologyData.mapExpand_f', hψ₁, Category.assoc, ← G.map_comp, ← hf', G.map_comp,
      ← Category.assoc (u S₁.X₁), hu, Category.assoc]
  commπ := by
    change h₁.π ≫ u h₁.H ≫ G.map dH = (u h₁.K ≫ G.map dK) ≫ G.map h₂.π
    rw [Category.assoc, ← G.map_comp, ← hπ, G.map_comp, ← Category.assoc (u h₁.K), hu,
      Category.assoc]

end CategoryTheory.ShortComplex

namespace CategoryTheory.Functor

variable {A B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- **Leray's acyclicity argument for a `ℤ`-indexed complex bounded below.** Let `G` be a left
exact additive functor and let `K` be a cochain complex vanishing in degrees `< n₀`. If every
term and every cohomology object of `K` is right acyclic for `G`, then every object of cycles
is too, and `G` preserves the homology of `K` in every degree.

The induction runs on the cycles, starting at the degree `n₀` where the incoming differential
vanishes; in the degrees below `n₀` the cycles are zero, hence injective, hence acyclic. -/
lemma rightAcyclic_cycles_and_preservesLeftHomologyOf_of_isStrictlyGE [EnoughInjectives A]
    (G : A ⥤ B) [G.Additive] [PreservesFiniteLimits G] (K : CochainComplex A ℤ) (n₀ : ℤ)
    [K.IsStrictlyGE n₀] (hX : ∀ n : ℤ, G.rightAcyclic (K.X n))
    (hH : ∀ n : ℤ, G.rightAcyclic (K.homology n)) (n : ℤ) :
    G.rightAcyclic (K.cycles n) ∧ G.PreservesLeftHomologyOf (K.sc n) := by
  by_cases hn : n < n₀
  · have hzero := CochainComplex.isZero_of_isStrictlyGE K n₀ n hn
    have hcycles : IsZero (K.cycles n) := IsZero.of_mono (K.iCycles n) hzero
    have : Injective (K.cycles n) := hcycles.injective
    exact ⟨G.rightAcyclic_of_injective _,
      G.preservesLeftHomology_of_zero_f (K.sc n) (hzero.eq_of_tgt _ _)⟩
  · obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = n₀ + m := ⟨(n - n₀).toNat, by omega⟩
    induction m with
    | zero =>
      have hz := CochainComplex.isZero_of_isStrictlyGE K n₀
        ((ComplexShape.up ℤ).prev (n₀ + (0 : ℕ))) (by simp)
      have hf : (K.sc (n₀ + (0 : ℕ))).f = 0 := hz.eq_of_src _ _
      have : IsIso ((K.sc (n₀ + (0 : ℕ))).homologyπ) := ShortComplex.isIso_homologyπ _ hf
      refine ⟨?_, G.preservesLeftHomology_of_zero_f _ hf⟩
      exact G.rightAcyclic.prop_of_iso (asIso ((K.sc (n₀ + (0 : ℕ))).homologyπ)).symm
        (hH (n₀ + (0 : ℕ)))
    | succ m ih =>
      have ih := ih (by omega)
      have hp : (ComplexShape.up ℤ).prev (n₀ + (m + 1 : ℕ)) = n₀ + m := by
        simp only [CochainComplex.prev]
        omega
      have hnext : (ComplexShape.up ℤ).next (n₀ + m) = n₀ + (m + 1 : ℕ) := by
        simp only [CochainComplex.next]
        omega
      -- The inclusion of the degree-`n₀ + m` cycles into the previous term of the short complex
      -- in degree `n₀ + m + 1`; the type ascription is what makes the rewrites below
      -- type-correct.
      let k : K.cycles (n₀ + m) ⟶ (K.sc (n₀ + (m + 1 : ℕ))).X₁ :=
        K.iCycles (n₀ + m) ≫ (K.XIsoOfEq hp).inv
      have wk : k ≫ (K.sc (n₀ + (m + 1 : ℕ))).f = 0 := by
        show (K.iCycles _ ≫ (K.XIsoOfEq hp).inv) ≫ K.d _ _ = 0
        rw [Category.assoc, K.XIsoOfEq_inv_comp_d, K.iCycles_d]
      have w : k ≫ (K.sc (n₀ + (m + 1 : ℕ))).toCycles = 0 := by
        rw [← cancel_mono (K.sc (n₀ + (m + 1 : ℕ))).iCycles, Category.assoc,
          ShortComplex.toCycles_i, zero_comp, wk]
      have hk0 : IsLimit (KernelFork.ofι k wk) := by
        refine IsKernel.ofIso (K.d _ _) (K.cyclesIsKernel _ _ hnext)
          (KernelFork.ofι k wk) (K.XIsoOfEq hp).symm (Iso.refl _) (Iso.refl _) ?_ ?_
        · show (K.XIsoOfEq hp).inv ≫ K.d _ _ = K.d _ _ ≫ 𝟙 _
          simp
        · simp [k]
      have hk := isKernelOfComp (K.sc (n₀ + (m + 1 : ℕ))).iCycles
        (K.sc (n₀ + (m + 1 : ℕ))).f hk0 w (K.sc (n₀ + (m + 1 : ℕ))).toCycles_i
      refine G.rightAcyclic_cycles_and_preservesLeftHomologyOf _ k w hk ih.1 ?_ (hH _)
      show G.rightAcyclic (K.X ((ComplexShape.up ℤ).prev (n₀ + (m + 1 : ℕ))))
      rw [hp]
      exact hX _

/-- **The degreewise adjoint of a map of cochain complexes.** For an adjunction `E ⊣ G` of
additive functors and a map `φ : E(I) ⟶ J` of cochain complexes, this is the map `I ⟶ G(J)`
whose component in degree `n` is the unit at `I_n` followed by `G(φ_n)`. -/
def adjointCochainComplexMap {E : A ⥤ B} {G : B ⥤ A} [E.Additive] [G.Additive] (adj : E ⊣ G)
    {I : CochainComplex A ℤ} {J : CochainComplex B ℤ}
    (φ : (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J) :
    I ⟶ (G.mapHomologicalComplex (ComplexShape.up ℤ)).obj J where
  f n := adj.unit.app (I.X n) ≫ G.map (φ.f n)
  comm' i j _ := by
    dsimp
    rw [Category.assoc, ← G.map_comp, φ.comm, G.map_comp, ← Category.assoc]
    change (adj.unit.app _ ≫ G.map (E.map (I.d i j))) ≫ _ = _
    simpa only [Category.assoc] using congrArg (fun ψ => ψ ≫ G.map (φ.f j))
      (adj.unit_naturality (I.d i j))

/-- **The degreewise adjoint of a quasi-isomorphism is a quasi-isomorphism**, under the
hypotheses of Leray's acyclicity argument. Let `E ⊣ G` with `E` exact and `G` left exact, let
`φ : E(I) ⟶ J` be a quasi-isomorphism with `J` bounded below, assume that every term and every
cohomology object of `J` is right acyclic for `G`, and that the unit of the adjunction is
invertible on every cohomology object of `I`. Then the degreewise adjoint `I ⟶ G(J)` is a
quasi-isomorphism.

In degree `n` the map induced on homology is, under the identification `H^n(G(J)) = G(H^n(J))`
supplied by the acyclicity hypothesis and the identification `H^n(E(I)) = E(H^n(I))` supplied by
exactness of `E`, the unit at `H^n(I)` followed by `G` of the invertible `H^n(φ)`. -/
lemma quasiIso_adjointCochainComplexMap [EnoughInjectives B]
    {E : A ⥤ B} {G : B ⥤ A} [E.Additive] [G.Additive] [E.PreservesHomology]
    [PreservesFiniteLimits G] (adj : E ⊣ G) (I : CochainComplex A ℤ) (J : CochainComplex B ℤ)
    (n₀ : ℤ) [J.IsStrictlyGE n₀]
    (φ : (E.mapHomologicalComplex (ComplexShape.up ℤ)).obj I ⟶ J) [QuasiIso φ]
    (hX : ∀ n : ℤ, G.rightAcyclic (J.X n)) (hH : ∀ n : ℤ, G.rightAcyclic (J.homology n))
    (hunit : ∀ n : ℤ, IsIso (adj.unit.app (I.homology n))) :
    QuasiIso (adjointCochainComplexMap adj φ) := by
  rw [quasiIso_iff]
  intro n
  have hpres : G.PreservesLeftHomologyOf (J.sc n) :=
    (G.rightAcyclic_cycles_and_preservesLeftHomologyOf_of_isStrictlyGE J n₀ hX hH n).2
  let h₁ := (I.sc n).homologyData.left
  let h₂ := (J.sc n).homologyData.left
  let φ' : (I.sc n).map E ⟶ J.sc n :=
    (HomologicalComplex.shortComplexFunctor B (ComplexShape.up ℤ) n).map φ
  let ψ' : I.sc n ⟶ (J.sc n).map G :=
    (HomologicalComplex.shortComplexFunctor A (ComplexShape.up ℤ) n).map
      (adjointCochainComplexMap adj φ)
  let d : ShortComplex.LeftHomologyMapData φ' (h₁.map E) h₂ := default
  have hdH : IsIso d.φH :=
    d.quasiIso_iff.mp ((quasiIsoAt_iff φ n).mp ((quasiIso_iff φ).mp inferInstance n))
  let adjData := ShortComplex.adjointLeftHomologyMapData h₁ h₂
    (ψ := ψ') (fun X => adj.unit.app X) (fun g => adj.unit_naturality g)
    d.φK d.φH φ'.τ₁ φ'.τ₂ rfl rfl d.commi
    (by rw [← ShortComplex.LeftHomologyData.map_f' h₁ E]; exact d.commf') d.commπ
  rw [quasiIsoAt_iff]
  refine adjData.quasiIso_iff.mpr ?_
  show IsIso (adj.unit.app h₁.H ≫ G.map d.φH)
  have hGd : IsIso (G.map d.φH) := inferInstance
  exact IsIso.comp_isIso' (hunit n) hGd

end CategoryTheory.Functor

namespace Stacks.ComparingTopologies

open Stacks.Cohomology.Localization

variable {C : Type u} [Category.{v} C]

attribute [local instance] HasDerivedCategory.standard

/-- The counit of the change-of-topology adjunction is invertible: the direct image is fully
faithful, since it does not change the underlying presheaf of a sheaf. -/
instance isIso_abelianComparisonAdjunction_counit (S : CohomologyComparison C) (X : C) :
    IsIso (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).counit :=
  Adjunction.counit_isIso_of_R_fully_faithful _

/-- The degreewise base change map of a change of topology, evaluated at a sheaf: it is the
image under `ε_Y^{-1} f_{τ',*}` of the change-of-topology unit, followed by the counit of the
change-of-topology adjunction over `Y`. -/
theorem abelianComparisonBaseChange_app (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y)
    (F : Sheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}) :
    (abelianComparisonBaseChange S f).app F =
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).map
          ((overPushforward S.coarseCoverage.toGrothendieck f).map
            ((abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
              S.coarse_le_fine X).unit.app F)) ≫
        (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
          S.coarse_le_fine Y).counit.app
            ((overPushforward S.fineCoverage.toGrothendieck f).obj
              ((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).obj F)) :=
  rfl

/-- **The degreewise base change map, composed with a map out of the change-of-topology inverse
image.** For `φ : ε_X^{-1} F ⟶ G` the base change map at `F` followed by `f_{τ,*}(φ)` is the
image under `ε_Y^{-1} f_{τ',*}` of the adjoint `F ⟶ ε_{X,*} G` of `φ`, followed by the counit of
the change-of-topology adjunction over `Y`.

This is the naturality of that counit, read through the strict identity
`f_{τ,*} ⋙ ε_{Y,*} = ε_{X,*} ⋙ f_{τ',*}` of Stacks 0EZ2, which is why the statement typechecks
at all. -/
theorem abelianComparisonBaseChange_app_comp (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y)
    {F : Sheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}}
    {G : Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}}
    (φ : (abelianComparisonPullback S.fineCoverage S.coarseCoverage X).obj F ⟶ G) :
    (abelianComparisonBaseChange S f).app F ≫
        (overPushforward S.fineCoverage.toGrothendieck f).map φ =
      (abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).map
          ((overPushforward S.coarseCoverage.toGrothendieck f).map
            ((abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
                S.coarse_le_fine X).unit.app F ≫
              (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
                S.coarse_le_fine X).map φ)) ≫
        (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
          S.coarse_le_fine Y).counit.app
            ((overPushforward S.fineCoverage.toGrothendieck f).obj G) := by
  have hnat := ((abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
    S.coarse_le_fine Y).counit_naturality
      ((overPushforward S.fineCoverage.toGrothendieck f).map φ)).symm
  have hAD := ((abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).map_comp
      ((overPushforward S.coarseCoverage.toGrothendieck f).map
        ((abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).unit.app F))
      ((overPushforward S.coarseCoverage.toGrothendieck f).map
        ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).map φ))).symm.trans
    (congrArg (abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).map
      ((overPushforward S.coarseCoverage.toGrothendieck f).map_comp
        ((abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).unit.app F)
        ((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
          S.coarse_le_fine X).map φ)).symm)
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun z => (abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).map
        ((overPushforward S.coarseCoverage.toGrothendieck f).map
          ((abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
            S.coarse_le_fine X).unit.app F)) ≫ z) hnat).trans
      (((Category.assoc _ _ _).symm).trans
        (congrArg (fun z => z ≫ (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
          S.coarse_le_fine Y).counit.app
            ((overPushforward S.fineCoverage.toGrothendieck f).obj G)) hAD)))

/-- **The degreewise base change map at a cochain complex, composed with a comparison of
resolutions.** The comparison of functors on complexes appearing here is degreewise the
identity, so this is `abelianComparisonBaseChange_app_comp` in every degree. -/
theorem baseChange_mapHomologicalComplex_comp (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y)
    (I : CochainComplex (Sheaf (S.coarseCoverage.toGrothendieck.over X) Ab.{max u v}) ℤ)
    (J : CochainComplex (Sheaf (S.fineCoverage.toGrothendieck.over X) Ab.{max u v}) ℤ)
    (φ : ((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I ⟶ J) :
    (NatTrans.mapHomologicalComplex (abelianComparisonBaseChange S f)
          (ComplexShape.up ℤ)).app I ≫
        (Functor.mapHomologicalComplexCompIso
            (Iso.refl (abelianComparisonPullback S.fineCoverage S.coarseCoverage X ⋙
              overPushforward S.fineCoverage.toGrothendieck f))
            (ComplexShape.up ℤ)).inv.app I ≫
        ((overPushforward S.fineCoverage.toGrothendieck f).mapHomologicalComplex
          (ComplexShape.up ℤ)).map φ =
      ((abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((overPushforward S.coarseCoverage.toGrothendieck f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
              (Functor.adjointCochainComplexMap (abelianComparisonAdjunction S.fineCoverage
                S.coarseCoverage S.coarse_le_fine X) φ)) ≫
        (NatTrans.mapHomologicalComplex (abelianComparisonAdjunction S.fineCoverage
            S.coarseCoverage S.coarse_le_fine Y).counit (ComplexShape.up ℤ)).app
          (((overPushforward S.fineCoverage.toGrothendieck f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj J) := by
  apply HomologicalComplex.hom_ext
  intro n
  show (abelianComparisonBaseChange S f).app (I.X n) ≫ 𝟙 _ ≫
    (overPushforward S.fineCoverage.toGrothendieck f).map (φ.f n) = _
  rw [Category.id_comp]
  exact abelianComparisonBaseChange_app_comp S f (φ.f n)

/-! ### The comparison on bounded below homotopy categories -/

/-- **A six-fold composite is invertible** when its first two and last factors are, when its
fifth factor becomes, after composition with an isomorphism `e`, a map `d₅` followed by an
isomorphism `w`, and when the third and fourth factors compose with that `d₅` to an
isomorphism.

This is the bookkeeping of `isIso_derivedComparisonBaseChangeOnHomotopy_app`, isolated so that
none of the large terms of that proof has to enter an associativity rewrite. -/
private lemma isIso_sixfold_of_isIso {D : Type*} [Category* D]
    {X₀ X₁ X₂ X₃ X₄ X₅ X₆ Z W : D}
    (t₁ : X₀ ⟶ X₁) (t₂ : X₁ ⟶ X₂) (t₃ : X₂ ⟶ X₃) (t₄ : X₃ ⟶ X₄) (t₅ : X₄ ⟶ X₅)
    (t₆ : X₅ ⟶ X₆) (e : X₅ ⟶ Z) (w : W ⟶ Z) (d₅ : X₄ ⟶ W)
    [IsIso t₁] [IsIso t₂] [IsIso t₆] [IsIso e] [IsIso w] [IsIso (t₃ ≫ t₄ ≫ d₅)]
    (h₅ : t₅ ≫ e = d₅ ≫ w) :
    IsIso (t₁ ≫ t₂ ≫ t₃ ≫ t₄ ≫ t₅ ≫ t₆) := by
  have h₁ : (t₃ ≫ t₄ ≫ t₅) ≫ e = (t₃ ≫ t₄ ≫ d₅) ≫ w := by
    simp only [Category.assoc, h₅]
  have : IsIso ((t₃ ≫ t₄ ≫ t₅) ≫ e) := by rw [h₁]; infer_instance
  have : IsIso (t₃ ≫ t₄ ≫ t₅) := IsIso.of_isIso_comp_right _ e
  have hsplit : t₁ ≫ t₂ ≫ t₃ ≫ t₄ ≫ t₅ ≫ t₆ = (t₁ ≫ t₂) ≫ (t₃ ≫ t₄ ≫ t₅) ≫ t₆ := by
    simp only [Category.assoc]
  rw [hsplit]
  infer_instance

/-- **The three-fold composite at the heart of the base change comparison is invertible.** The
degreewise base change map, the comparison of functors on complexes, and `f_{τ,*}` of a
comparison of resolutions `φ` compose, by `baseChange_mapHomologicalComplex_comp`, to the image
under `ε_Y^{-1} f_{τ',*}` of the degreewise adjoint of `φ` followed by the counit of the
change-of-topology adjunction. The counit is invertible, and the adjoint is assumed to be a
homotopy equivalence. -/
private lemma isIso_homotopyBaseChangeCore (S : CohomologyComparison C) {X Y : C} (f : X ⟶ Y)
    (I : CochainComplex.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (JP : CochainComplex.Plus (AbelianSheaves S.fineCoverage.toGrothendieck X))
    (φ : ((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I.obj ⟶ JP.obj)
    (hψiso : IsIso ((HomotopyCategory.quotient
      (AbelianSheaves S.coarseCoverage.toGrothendieck X) (ComplexShape.up ℤ)).map
        (Functor.adjointCochainComplexMap (abelianComparisonAdjunction S.fineCoverage
          S.coarseCoverage S.coarse_le_fine X) φ))) :
    IsIso ((Functor.mapHomotopyCategoryPlusNatTrans (abelianComparisonBaseChange S f)).app
          ((HomotopyCategory.Plus.quotient _).obj I) ≫
        (Functor.mapHomotopyCategoryPlusCompIso
            (Iso.refl (abelianComparisonPullback S.fineCoverage S.coarseCoverage X ⋙
              overPushforward S.fineCoverage.toGrothendieck f))).inv.app
          ((HomotopyCategory.Plus.quotient _).obj I) ≫
        (overPushforward S.fineCoverage.toGrothendieck f).mapHomotopyCategoryPlus.map
          (ObjectProperty.homMk ((HomotopyCategory.quotient
              (AbelianSheaves S.fineCoverage.toGrothendieck X) (ComplexShape.up ℤ)).map φ) :
            (abelianComparisonPullback S.fineCoverage S.coarseCoverage
                X).mapHomotopyCategoryPlus.obj ((HomotopyCategory.Plus.quotient _).obj I) ⟶
              (HomotopyCategory.Plus.quotient _).obj JP)) := by
  have hcplx : IsIso ((HomotopyCategory.quotient
      (AbelianSheaves S.fineCoverage.toGrothendieck Y) (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (abelianComparisonBaseChange S f)
            (ComplexShape.up ℤ)).app I.obj ≫
          (Functor.mapHomologicalComplexCompIso
              (Iso.refl (abelianComparisonPullback S.fineCoverage S.coarseCoverage X ⋙
                overPushforward S.fineCoverage.toGrothendieck f))
              (ComplexShape.up ℤ)).inv.app I.obj ≫
          ((overPushforward S.fineCoverage.toGrothendieck f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map φ)) := by
    rw [baseChange_mapHomologicalComplex_comp]
    rw [Functor.map_comp (HomotopyCategory.quotient
      (AbelianSheaves S.fineCoverage.toGrothendieck Y) (ComplexShape.up ℤ))
      (((abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
          (((overPushforward S.coarseCoverage.toGrothendieck f).mapHomologicalComplex
            (ComplexShape.up ℤ)).map
              (Functor.adjointCochainComplexMap (abelianComparisonAdjunction S.fineCoverage
                S.coarseCoverage S.coarse_le_fine X) φ)))
      ((NatTrans.mapHomologicalComplex (abelianComparisonAdjunction S.fineCoverage
            S.coarseCoverage S.coarse_le_fine Y).counit (ComplexShape.up ℤ)).app
          (((overPushforward S.fineCoverage.toGrothendieck f).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj JP.obj))]
    refine IsIso.comp_isIso' ?_ ?_
    · rw [← Functor.mapHomotopyCategory_map, ← Functor.mapHomotopyCategory_map]
      exact (((abelianComparisonPullback S.fineCoverage S.coarseCoverage Y).mapHomotopyCategory
          (ComplexShape.up ℤ)).mapIso
        (((overPushforward S.coarseCoverage.toGrothendieck f).mapHomotopyCategory
            (ComplexShape.up ℤ)).mapIso (@asIso _ _ _ _ _ hψiso))).isIso_hom
    · exact ((HomotopyCategory.quotient (AbelianSheaves S.fineCoverage.toGrothendieck Y)
        (ComplexShape.up ℤ)).mapIso ((NatIso.mapHomologicalComplex
        (asIso (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage
          S.coarse_le_fine Y).counit) (ComplexShape.up ℤ)).app
            (((overPushforward S.fineCoverage.toGrothendieck f).mapHomologicalComplex
              (ComplexShape.up ℤ)).obj JP.obj))).isIso_hom
  rw [← isIso_iff_of_reflects_iso _ (HomotopyCategory.Plus.ι
    (AbelianSheaves S.fineCoverage.toGrothendieck Y))]
  exact hcplx

/-- **The comparison of Stacks 0EZF part (2) on bounded below homotopy categories.** Assume the
vanishing conditions `(V_n)`. For a bounded below complex `I` of injective sheaves on the coarse
localized site over `X` whose cohomology sheaves lie in `𝒜'_X`, the transformation
`derivedComparisonBaseChangeOnHomotopy` is invertible at `I`. -/
private lemma isIso_derivedComparisonBaseChangeOnHomotopy_app (S : CohomologyComparison C)
    (hV : ∀ n : ℕ, S.vanishingCondition n) {X Y : C} (f : X ⟶ Y)
    (I : CochainComplex.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (hInj : ∀ n : ℤ, Injective (I.obj.X n))
    (hI : ∀ n : ℤ, S.weakSerre X (I.obj.homology n)) :
    IsIso ((derivedComparisonBaseChangeOnHomotopy S f).app
      ((HomotopyCategory.Plus.quotient _).obj I)) := by
  have : ∀ n : ℤ, Injective (I.obj.X n) := hInj
  obtain ⟨lower, hlower⟩ := I.property
  have hIGE : I.obj.IsStrictlyGE lower := hlower
  obtain ⟨J, φ, hφ, hJinj, hJlower⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      (((abelianComparisonPullback S.fineCoverage S.coarseCoverage X).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I.obj) lower
  have : QuasiIso φ := hφ
  have : ∀ n : ℤ, Injective (J.X n) := hJinj
  have hJGE : J.IsStrictlyGE lower := hJlower
  -- the cohomology sheaves of `J` lie in `𝒜_X`
  have hJhom : ∀ n : ℤ, S.fineWeakSerre X (J.homology n) := by
    intro n
    have hiso : IsIso (HomologicalComplex.homologyMap φ n) :=
      (quasiIsoAt_iff_isIso_homologyMap φ n).mp ((quasiIso_iff φ).mp hφ n)
    refine (S.fineWeakSerre X).prop_of_iso ?_
      (ObjectProperty.prop_map_obj (S.weakSerre X)
        (abelianComparisonPullback S.fineCoverage S.coarseCoverage X) (hI n))
    exact ((I.obj.sc n).mapHomologyIso
        (abelianComparisonPullback S.fineCoverage S.coarseCoverage X)).symm ≪≫
      @asIso _ _ _ _ (HomologicalComplex.homologyMap φ n) hiso
  -- the degreewise adjoint of `φ` is a quasi-isomorphism
  have hψ : QuasiIso (Functor.adjointCochainComplexMap
      (abelianComparisonAdjunction S.fineCoverage S.coarseCoverage S.coarse_le_fine X) φ) :=
    Functor.quasiIso_adjointCochainComplexMap _ I.obj J lower φ
      (fun _ => (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).rightAcyclic_of_injective _)
      (fun n => CohomologyComparison.abelianComparisonPushforward_rightAcyclic_of_fineWeakSerre
          S hV X _ (hJhom n))
      (fun n => isIso_abelianComparisonAdjunction_unit_of_weakSerre S X _ (hI n))
  -- and in fact a homotopy equivalence, both ends being K-injective
  have : ∀ n : ℤ, Injective
      ((((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J).X n) :=
    fun n => (abelianComparisonPushforward S.fineCoverage S.coarseCoverage
      S.coarse_le_fine X).injective_obj_of_injective (hJinj n)
  have : I.obj.IsKInjective := CochainComplex.isKInjective_of_injective I.obj lower
  have : CochainComplex.IsKInjective
      (((abelianComparisonPushforward S.fineCoverage S.coarseCoverage
        S.coarse_le_fine X).mapHomologicalComplex (ComplexShape.up ℤ)).obj J) :=
    CochainComplex.isKInjective_of_injective _ lower
  have hψiso : IsIso ((HomotopyCategory.quotient
      (AbelianSheaves S.coarseCoverage.toGrothendieck X) (ComplexShape.up ℤ)).map
      (Functor.adjointCochainComplexMap (abelianComparisonAdjunction S.fineCoverage
        S.coarseCoverage S.coarse_le_fine X) φ)) := by
    rw [HomologicalComplex.isIso_quotient_map_iff_homotopyEquivalences,
      ← CochainComplex.IsKInjective.quasiIso_iff]
    exact hψ
  -- shorthands for the six factors of the comparison at `I`
  set JP : CochainComplex.Plus (AbelianSheaves S.fineCoverage.toGrothendieck X) :=
    ⟨J, ⟨lower, hJlower⟩⟩
  set IH := (HomotopyCategory.Plus.quotient
    (AbelianSheaves S.coarseCoverage.toGrothendieck X)).obj I
  set JH := (HomotopyCategory.Plus.quotient
    (AbelianSheaves S.fineCoverage.toGrothendieck X)).obj JP
  set φH : (abelianComparisonPullback S.fineCoverage S.coarseCoverage
      X).mapHomotopyCategoryPlus.obj IH ⟶ JH :=
    ObjectProperty.homMk ((HomotopyCategory.quotient
      (AbelianSheaves S.fineCoverage.toGrothendieck X) (ComplexShape.up ℤ)).map φ)
  set b := (Functor.mapHomotopyCategoryPlusNatTrans (abelianComparisonBaseChange S f)).app IH
  set c₂ := (Functor.mapHomotopyCategoryPlusCompIso
    (Iso.refl (abelianComparisonPullback S.fineCoverage S.coarseCoverage X ⋙
      overPushforward S.fineCoverage.toGrothendieck f))).inv.app IH
  set dd := (overPushforward S.fineCoverage.toGrothendieck f).mapHomotopyCategoryPlus.map φH
  have hcore : IsIso (b ≫ c₂ ≫ dd) := isIso_homotopyBaseChangeCore S f I JP φ hψiso
  have hQphiH : IsIso (DerivedCategory.Plus.Qh.map φH) := by
    rw [← isIso_iff_of_reflects_iso _ DerivedCategory.Plus.ι]
    show IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient
      (AbelianSheaves S.fineCoverage.toGrothendieck X) (ComplexShape.up ℤ)).map φ))
    rw [DerivedCategory.isIso_Qh_map_iff, HomotopyCategory.quotient_map_mem_quasiIso_iff]
    exact hφ
  have hQcore : IsIso (DerivedCategory.Plus.Qh.map b ≫ DerivedCategory.Plus.Qh.map c₂ ≫
      DerivedCategory.Plus.Qh.map dd) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    infer_instance
  show IsIso (_ ≫ _ ≫ DerivedCategory.Plus.Qh.map b ≫ DerivedCategory.Plus.Qh.map c₂ ≫
    _ ≫ _)
  exact isIso_sixfold_of_isIso _ _ _ _ _ _
    ((overPushforward S.fineCoverage.toGrothendieck f).rightDerivedFunctorPlus.map
      (DerivedCategory.Plus.Qh.map φH))
    ((overPushforward S.fineCoverage.toGrothendieck f).rightDerivedFunctorPlusUnith.app JH)
    (DerivedCategory.Plus.Qh.map dd)
    (((overPushforward S.fineCoverage.toGrothendieck
      f).rightDerivedFunctorPlusUnith.naturality φH).symm)

/-! ### The comparison on bounded below derived categories -/

/-- **Stacks 0EZF, part (2), the base change identification.** Assume the vanishing conditions
`(V_n)` of the situation for every `n`. For a morphism `f : X ⟶ Y` of the site and an object
`K'` of `D⁺(C_{τ'}/X)` all of whose cohomology sheaves lie in the weak Serre class `𝒜'_X`, the
canonical derived base change map

`ε_Y^{-1} R f_{τ',*} K' ⟶ R f_{τ,*} (ε_X^{-1} K')`

of `Stacks.ComparingTopologies.derivedComparisonBaseChange` is an isomorphism.

`K'` is replaced by a bounded below complex of injective sheaves, which is legitimate by
`CategoryTheory.DerivedCategory.Plus.exists_injective_nonempty_iso`; the unit of right derivation
of `f_{τ',*}` is then invertible there, so the defining equation
`derivedComparisonBaseChange_fac` reduces the claim to
`isIso_derivedComparisonBaseChangeOnHomotopy_app`. -/
theorem isIso_derivedComparisonBaseChange_app_of_vanishingCondition (S : CohomologyComparison C)
    (hV : ∀ n : ℕ, S.vanishingCondition n) {X Y : C} (f : X ⟶ Y)
    (K : DerivedCategory.Plus (AbelianSheaves S.coarseCoverage.toGrothendieck X))
    (hK : ∀ n : ℤ, S.weakSerre X
      ((DerivedCategory.Plus.homologyFunctor
        (AbelianSheaves S.coarseCoverage.toGrothendieck X) n).obj K)) :
    IsIso ((derivedComparisonBaseChange S f).app K) := by
  obtain ⟨lower, hlower⟩ := K.property
  have : K.IsGE lower := (K.isGE_ι_obj_iff lower).1 hlower
  obtain ⟨L, hL, ⟨eL⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K lower
  set I := (InjectiveObject.ι
    (AbelianSheaves S.coarseCoverage.toGrothendieck X)).mapCochainComplexPlus.obj L with hIdef
  set IH := (HomotopyCategory.Plus.quotient
    (AbelianSheaves S.coarseCoverage.toGrothendieck X)).obj I with hIH
  have eK : DerivedCategory.Plus.Qh.obj IH ≅ K :=
    DerivedCategory.Plus.ι.preimageIso (Y := DerivedCategory.Plus.Q.obj I)
      ((DerivedCategory.Plus.QhCompιIsoιCompQh _).app IH ≪≫
        DerivedCategory.Qh.mapIso ((HomotopyCategory.Plus.quotientCompιIso _).app I) ≪≫
        (DerivedCategory.quotientCompQhIso _).app I.obj) ≪≫ eL
  rw [← NatTrans.isIso_app_iff_of_iso _ eK]
  have hIinj : ∀ n : ℤ, Injective (I.obj.X n) := fun n =>
    inferInstanceAs (Injective ((L.obj.X n).obj))
  have hIhom : ∀ n : ℤ, S.weakSerre X (I.obj.homology n) := by
    intro n
    exact (S.weakSerre X).prop_of_iso
      (((DerivedCategory.Plus.homologyFunctor _ n).mapIso eL).symm ≪≫
        (DerivedCategory.homologyFunctorFactors _ n).app I.obj) (hK n)
  have honhom : IsIso ((derivedComparisonBaseChangeOnHomotopy S f).app IH) :=
    isIso_derivedComparisonBaseChangeOnHomotopy_app S hV f I hIinj hIhom
  have hfac := congrArg (fun τ => τ.app IH) (derivedComparisonBaseChange_fac S f)
  dsimp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app] at hfac
  exact IsIso.of_isIso_fac_left hfac

end Stacks.ComparingTopologies

end
