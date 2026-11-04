module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EquivariantQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentModules
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackQuasicoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc

/-!
# Quasi-coherent modules on a groupoid in algebraic spaces pulled back from an algebraic space

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces and let `φ : U ⟶ X` be a morphism to an
algebraic space `X` with `t ≫ φ = s ≫ φ`.  The two inverse images `t^*φ^*ℱ` and `s^*φ^*ℱ` of a
module `ℱ` on `X` are both canonically identified with the inverse image of `ℱ` along the common
composite, so `φ^*ℱ` carries a canonical transition morphism `α : t^*φ^*ℱ ⟶ s^*φ^*ℱ`.  It
satisfies the cocycle condition on the space of composable pairs of arrows and is the identity
along the unit arrow, so `(φ^*ℱ, α)` is a quasi-coherent module on the groupoid whenever `ℱ` is
quasi-coherent; no hypothesis on `φ` is needed for that, quasi-coherence being preserved by every
inverse image.

## Main definitions

* `AlgebraicGeometry.Space.spaceBaseDescent` is the canonical transition morphism `α` of
  `φ^*ℱ`: the transport of `ℱ` along the equality `t ≫ φ = s ≫ φ`, unflattened through the
  comparisons of iterated inverse images of Stacks 03LU.
* `AlgebraicGeometry.Space.quasicoherentModuleOfSpaceBase` assembles `φ^*ℱ` and `α` into a
  quasi-coherent module on the groupoid.

## Main results

* `AlgebraicGeometry.Space.modulePullbackFlatten_reindex_spaceBaseDescent` and its named form
  `…modulePullbackFlatten'_reindex_spaceBaseDescent`: flattened, every reindexing of the
  canonical transition morphism is again a transport — along the equality
  `f ≫ t ≫ φ = f ≫ s ≫ φ`.  This single identity is what both laws below reduce to.
* `AlgebraicGeometry.Space.spaceBaseDescent_cocycle` and
  `AlgebraicGeometry.Space.spaceBaseDescent_unit` are the cocycle and unit conditions of
  Stacks 0441 for the canonical transition morphism.
* `AlgebraicGeometry.Space.spaceBaseDescent_naturality` and
  `AlgebraicGeometry.Space.quasicoherentModuleOfSpaceBase_comm`: the canonical transition
  morphism is natural in the module on the base, the second being that naturality read through
  the two projections that the compatibility field of
  `AlgebraicGeometry.Space.QuasicoherentModule.Hom` is stated with.

## What is proved and what is not

The source, Stacks 03M3, asserts for a *surjective étale* `φ : U ⟶ X` onto an algebraic space,
with `R = U ×_X U`, that `ℱ ↦ (φ^*ℱ, α)` is an **equivalence**
`QCoh(𝒪_X) ≌ QCoh(U, R, s, t, c)`.  **Only the object assignment is constructed here**, and the
attribute below says so: no declaration here asserts the equivalence, or full faithfulness, or
essential surjectivity, or even that the assignment is a functor.

As in the scheme-target half of the tag
(`Stacks.Groupoids.GroupoidScheme.quasicoherentModuleOfBaseFunctor`), neither surjectivity of
`φ` nor the identification `R = U ×_X U` is used: the transition morphism and its two laws come
from functoriality of the inverse image alone, as in the first paragraph of the source's proof.
Étaleness of `φ` *is* used, and only for the quasi-coherence of `φ^*ℱ`, through
`AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isEtale`; it is a hypothesis of
the source.

**Why the assignment is not packaged as a functor.**  Every mathematical ingredient is here:
`quasicoherentModuleOfSpaceBase` on objects, `(AlgebraicGeometry.Space.modulePullback _ _ _ φ).map`
on morphisms, and `quasicoherentModuleOfSpaceBase_comm` for the compatibility, which is stated in
exactly the shape the `comm` field of `AlgebraicGeometry.Space.QuasicoherentModule.Hom` asks for
and is proved.  What blocks the `CategoryTheory.Functor` is the kernel, not the mathematics, and
it is the obstruction already recorded in the section "What is not proved" of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentPullback.lean`: the `hom` field of
that structure is typed `M.F.obj ⟶ N.F.obj`, so building a morphism out of
`(modulePullback _ _ _ φ).map ψ` asks the kernel to identify two definitionally equal but
syntactically different inverse images underneath `CategoryTheory.CategoryStruct.comp`, which is
a projection of the `SheafOfModules` instance and is projection-reduced before congruence is
attempted.  Each of `quasicoherentModuleOfSpaceBase_F_obj`,
`quasicoherentModuleOfSpaceBase_alpha` and `quasicoherentModuleOfSpaceBase_comm` performs that
identification once, in a statement small enough for the kernel; the `Functor` bundle asks for it
again inside the `map`, `map_id` and `map_comp` fields at once, and there the kernel's budget is
exhausted.  What the remaining step needs is a form of
`AlgebraicGeometry.Space.QuasicoherentModule.Hom` whose `hom` field is indexed by the two modules
rather than by the two groupoid modules — the same respelling that the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/QuasicoherentPullback.lean` ask for.

**Why the converse direction is not here.** The source builds it by restricting a descent datum
`(ℱ, α)` to each `V` in `X_étale`, where `V' = U ×_X V ⟶ V` is a surjective étale covering of
*schemes* and `α` becomes an ordinary quasi-coherent descent datum, effective by Descent,
Proposition 023T — which this development now has with no hypothesis, as
`AlgebraicGeometry.QuasicoherentDescentData.isEffective_fpqcPrecoverage`.  The module it produces
on `V` lives on the *Zariski* site of the scheme `V`, and assembling the family `(ℱ_V)` into an
`𝒪_X`-module on the small étale site of `X` passes through the comparison
`QCoh(𝒪_V) ≌ QCoh(V_étale)` of Descent, Proposition 03DX (2) — which this development *also* now
has with no hypothesis, as `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`
and `AlgebraicGeometry.SmallEtale.associatedModuleEquivalence'`.

So **both inputs the source cites are available**, and what the converse direction still owes is
the assembly: the family `(ℱ_V)` indexed by the charts `V` of `X`, together with its transition
isomorphisms and their cocycle condition, which is a
`AlgebraicGeometry.Space.ChartModuleGlueingData` to be fed to the unconditional equivalence of
Stacks 03LZ, `AlgebraicGeometry.Space.quasicoherentChartModuleGlueingEquivalence`.  Effectivity
gives each `ℱ_V` only up to isomorphism, so the assembly has to be made functorial in `V` first —
that is, the quasi-inverse of the descent equivalence of 023T has to be used as a functor and its
naturality in `V` proved — and none of that is here.

## Implementation notes

Everything is done in the reindexing calculus of
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullbackAssoc.lean` and its named form in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EquivariantQuasicoherentPullback.lean`, never by
unfolding `AlgebraicGeometry.Space.modulePullback`, whose unfolding the kernel cannot check within
its budget.  In particular the transition morphism is *defined* as an
`AlgebraicGeometry.Space.modulePullbackUnflatten`, so that both laws can be proved after
flattening, flattening being injective; after flattening every factor is a canonical transport
and the laws are proof irrelevance.

The cocycle law is proved at `AlgebraicGeometry.Space.modulePullbackFlatten'`, the *named*
flattening, and not at `AlgebraicGeometry.Space.modulePullbackFlatten`: the two sides of the law
disagree about the bracketing of the composites underneath the inverse image, and comparing the
two bracketings underneath a `≫` is the forbidden kernel comparison described in the
implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EquivariantQuasicoherentPullback.lean`.  With the
six composites along `φ` named, the law is a five-step chain of transports.  Proving it by
`rw`-ing the two sides into canonical transports instead elaborates and then exhausts the
kernel's budget, measurably.

The associativity coherence of the comparison of inverse images, which the flattening calculus
takes as the hypothesis `AlgebraicGeometry.Space.ModulePullbackCompIsoAssoc`, is the theorem
`AlgebraicGeometry.Space.modulePullbackCompIsoAssoc`, so nothing below is conditional.

The module universe is the universe of the structure rings, because
`AlgebraicGeometry.Space.modulePullback` exists only there.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 03GA](https://stacks.math.columbia.edu/tag/03GA)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS}

/-- The canonical transition morphism `α : t^*φ^*ℱ ⟶ s^*φ^*ℱ` of a module pulled back from an
algebraic space `X` along a morphism `φ : U ⟶ X` out of the object space of a groupoid in
algebraic spaces whose composites with the target and the source of the groupoid agree.

It is the transport of `ℱ` along `t ≫ φ = s ≫ φ`, read through the comparisons of iterated
inverse images of Stacks 03LU. -/
def spaceBaseDescent (φ : G.objects ⟶ X) (hφ : G.target ≫ φ = G.source ≫ φ)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullback B S hS G.target).obj ((modulePullback B S hS φ).obj M) ⟶
      (modulePullback B S hS G.source).obj ((modulePullback B S hS φ).obj M) :=
  modulePullbackUnflatten φ (pullbackTransport M hφ)

/-- Flattened, the canonical transition morphism is the transport along `t ≫ φ = s ≫ φ`. -/
theorem modulePullbackFlatten_spaceBaseDescent (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ) (M : Modules.{u, u} B S hS X.1 X.2) :
    modulePullbackFlatten φ (spaceBaseDescent B S hS G φ hφ M) = pullbackTransport M hφ :=
  modulePullbackFlatten_unflatten φ (pullbackTransport M hφ)

/-- **Flattened, every reindexing of the canonical transition morphism is again a transport**,
along the equality `f ≫ t ≫ φ = f ≫ s ≫ φ`.  Both conditions of Stacks 0441 reduce to this
identity. -/
theorem modulePullbackFlatten_reindex_spaceBaseDescent (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ) (M : Modules.{u, u} B S hS X.1 X.2)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ G.arrows)
    (h' : (f ≫ G.target) ≫ φ = (f ≫ G.source) ≫ φ) :
    modulePullbackFlatten φ (modulePullbackReindex f (spaceBaseDescent B S hS G φ hφ M)) =
      pullbackTransport M h' := by
  rw [(modulePullbackCompIsoAssoc B S hS).modulePullbackFlatten_reindex f φ,
    modulePullbackFlatten_spaceBaseDescent, pullbackTransport_eq_eqToHom,
    modulePullbackReindex_eqToHom f M hφ, pullbackTransport_eq_eqToHom]

/-- **The named flattening of a reindexing of the canonical transition morphism is a
transport.**  This is `AlgebraicGeometry.Space.modulePullbackFlatten_reindex_spaceBaseDescent`
with the two composites along `φ` named, which is what keeps the bracketing of a composite out
of every term; see the implementation notes. -/
theorem modulePullbackFlatten'_reindex_spaceBaseDescent (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ) (M : Modules.{u, u} B S hS X.1 X.2)
    {Y : AlgebraicSpaces B S hS} (f : Y ⟶ G.arrows) {c d : Y ⟶ X}
    (hc : (f ≫ G.target) ≫ φ = c) (hd : (f ≫ G.source) ≫ φ = d) (e : c = d) :
    modulePullbackFlatten' φ hc hd
        (modulePullbackReindex f (spaceBaseDescent B S hS G φ hφ M)) =
      pullbackTransport M e := by
  have h' : (f ≫ G.target) ≫ φ = (f ≫ G.source) ≫ φ := by
    rw [Category.assoc, Category.assoc, hφ]
  rw [modulePullbackFlatten'_eq_comp,
    modulePullbackFlatten_reindex_spaceBaseDescent B S hS G φ hφ M f h',
    pullbackTransport_comp M h' hd (h'.trans hd),
    pullbackTransport_comp M hc.symm (h'.trans hd) e]

/-- **The cocycle condition of Stacks 0441 for the canonical transition morphism.** -/
theorem spaceBaseDescent_cocycle (φ : G.objects ⟶ X) (hφ : G.target ≫ φ = G.source ≫ φ)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    groupoidPullbackTransition B S hS G ((modulePullback B S hS φ).obj M)
        (spaceBaseDescent B S hS G φ hφ M) G.comp =
      groupoidTransitionComposite B S hS G ((modulePullback B S hS φ).obj M)
        (spaceBaseDescent B S hS G φ hφ M) := by
  have e₀₁ : G.comp ≫ G.target ≫ φ =
      GroupoidInAlgebraicSpaces.firstArrow G ≫ G.target ≫ φ := by
    rw [← Category.assoc, ← Category.assoc, GroupoidInAlgebraicSpaces.comp_comp_target]
  have e₁₂ : GroupoidInAlgebraicSpaces.firstArrow G ≫ G.target ≫ φ =
      GroupoidInAlgebraicSpaces.firstArrow G ≫ G.source ≫ φ := by rw [hφ]
  have e₂₃ : GroupoidInAlgebraicSpaces.firstArrow G ≫ G.source ≫ φ =
      GroupoidInAlgebraicSpaces.secondArrow G ≫ G.target ≫ φ := by
    rw [← Category.assoc, ← Category.assoc, GroupoidInAlgebraicSpaces.firstArrow_comp_source]
  have e₃₄ : GroupoidInAlgebraicSpaces.secondArrow G ≫ G.target ≫ φ =
      GroupoidInAlgebraicSpaces.secondArrow G ≫ G.source ≫ φ := by rw [hφ]
  have e₄₅ : GroupoidInAlgebraicSpaces.secondArrow G ≫ G.source ≫ φ =
      G.comp ≫ G.source ≫ φ := by
    rw [← Category.assoc, ← Category.assoc, GroupoidInAlgebraicSpaces.comp_comp_source]
  have e₀₅ : G.comp ≫ G.target ≫ φ = G.comp ≫ G.source ≫ φ := by rw [hφ]
  have K₀ : (G.comp ≫ G.target) ≫ φ = G.comp ≫ G.target ≫ φ := Category.assoc _ _ _
  have K₁ : (GroupoidInAlgebraicSpaces.firstArrow G ≫ G.target) ≫ φ =
      GroupoidInAlgebraicSpaces.firstArrow G ≫ G.target ≫ φ := Category.assoc _ _ _
  have K₂ : (GroupoidInAlgebraicSpaces.firstArrow G ≫ G.source) ≫ φ =
      GroupoidInAlgebraicSpaces.firstArrow G ≫ G.source ≫ φ := Category.assoc _ _ _
  have K₃ : (GroupoidInAlgebraicSpaces.secondArrow G ≫ G.target) ≫ φ =
      GroupoidInAlgebraicSpaces.secondArrow G ≫ G.target ≫ φ := Category.assoc _ _ _
  have K₄ : (GroupoidInAlgebraicSpaces.secondArrow G ≫ G.source) ≫ φ =
      GroupoidInAlgebraicSpaces.secondArrow G ≫ G.source ≫ φ := Category.assoc _ _ _
  have K₅ : (G.comp ≫ G.source) ≫ φ = G.comp ≫ G.source ≫ φ := Category.assoc _ _ _
  have e₂₅ : GroupoidInAlgebraicSpaces.firstArrow G ≫ G.source ≫ φ =
      G.comp ≫ G.source ≫ φ := e₂₃.trans (e₃₄.trans e₄₅)
  have c₃₅ : pullbackTransport M e₂₃ ≫ pullbackTransport M e₃₄ ≫
      pullbackTransport M e₄₅ = pullbackTransport M e₂₅ :=
    (comp₂_congr rfl (pullbackTransport_comp M e₃₄ e₄₅ (e₃₄.trans e₄₅))).trans
      (pullbackTransport_comp M e₂₃ (e₃₄.trans e₄₅) e₂₅)
  have chain : pullbackTransport M e₀₁ ≫ pullbackTransport M e₁₂ ≫
      pullbackTransport M e₂₃ ≫ pullbackTransport M e₃₄ ≫ pullbackTransport M e₄₅ =
      pullbackTransport M e₀₅ :=
    (comp₃_congr rfl rfl c₃₅).trans
      ((comp₂_congr rfl (pullbackTransport_comp M e₁₂ e₂₅ (e₁₂.trans e₂₅))).trans
        (pullbackTransport_comp M e₀₁ (e₁₂.trans e₂₅) e₀₅))
  rw [groupoidPullbackTransition_eq_transitionReindex,
    transitionReindex_eq_modulePullbackReindex, groupoidTransitionComposite_eq,
    transitionComposite_eq_comp]
  refine modulePullbackFlatten'_injective φ K₀ K₅ ?_
  calc modulePullbackFlatten' φ K₀ K₅
          (modulePullbackReindex G.comp (spaceBaseDescent B S hS G φ hφ M))
      = pullbackTransport M e₀₅ :=
        modulePullbackFlatten'_reindex_spaceBaseDescent B S hS G φ hφ M G.comp K₀ K₅ e₀₅
    _ = pullbackTransport M e₀₁ ≫ pullbackTransport M e₁₂ ≫
          pullbackTransport M e₂₃ ≫ pullbackTransport M e₃₄ ≫
          pullbackTransport M e₄₅ := chain.symm
    _ = modulePullbackFlatten' φ K₀ K₁
            (pullbackTransport ((modulePullback B S hS φ).obj M)
              (GroupoidInAlgebraicSpaces.comp_comp_target G)) ≫
          modulePullbackFlatten' φ K₁ K₂
            (modulePullbackReindex (GroupoidInAlgebraicSpaces.firstArrow G)
              (spaceBaseDescent B S hS G φ hφ M)) ≫
          modulePullbackFlatten' φ K₂ K₃
            (pullbackTransport ((modulePullback B S hS φ).obj M)
              (GroupoidInAlgebraicSpaces.firstArrow_comp_source G)) ≫
          modulePullbackFlatten' φ K₃ K₄
            (modulePullbackReindex (GroupoidInAlgebraicSpaces.secondArrow G)
              (spaceBaseDescent B S hS G φ hφ M)) ≫
          modulePullbackFlatten' φ K₄ K₅
            (pullbackTransport ((modulePullback B S hS φ).obj M)
              (GroupoidInAlgebraicSpaces.comp_comp_source G).symm) :=
        comp₅_congr
          (modulePullbackFlatten'_pullbackTransport φ K₀ K₁
            (GroupoidInAlgebraicSpaces.comp_comp_target G) M e₀₁).symm
          (modulePullbackFlatten'_reindex_spaceBaseDescent B S hS G φ hφ M
            (GroupoidInAlgebraicSpaces.firstArrow G) K₁ K₂ e₁₂).symm
          (modulePullbackFlatten'_pullbackTransport φ K₂ K₃
            (GroupoidInAlgebraicSpaces.firstArrow_comp_source G) M e₂₃).symm
          (modulePullbackFlatten'_reindex_spaceBaseDescent B S hS G φ hφ M
            (GroupoidInAlgebraicSpaces.secondArrow G) K₃ K₄ e₃₄).symm
          (modulePullbackFlatten'_pullbackTransport φ K₄ K₅
            (GroupoidInAlgebraicSpaces.comp_comp_source G).symm M e₄₅).symm
    _ = modulePullbackFlatten' φ K₀ K₅
          (pullbackTransport ((modulePullback B S hS φ).obj M)
              (GroupoidInAlgebraicSpaces.comp_comp_target G) ≫
            modulePullbackReindex (GroupoidInAlgebraicSpaces.firstArrow G)
              (spaceBaseDescent B S hS G φ hφ M) ≫
            pullbackTransport ((modulePullback B S hS φ).obj M)
              (GroupoidInAlgebraicSpaces.firstArrow_comp_source G) ≫
            modulePullbackReindex (GroupoidInAlgebraicSpaces.secondArrow G)
              (spaceBaseDescent B S hS G φ hφ M) ≫
            pullbackTransport ((modulePullback B S hS φ).obj M)
              (GroupoidInAlgebraicSpaces.comp_comp_source G).symm) :=
        (modulePullbackFlatten'_comp₅ φ K₀ K₁ K₂ K₃ K₄ K₅ _ _ _ _ _).symm
    _ = modulePullbackFlatten' φ K₀ K₅
          (pullbackTransport ((modulePullback B S hS φ).obj M)
              (GroupoidInAlgebraicSpaces.comp_comp_target G) ≫
            (modulePullbackReindex (GroupoidInAlgebraicSpaces.firstArrow G)
                (spaceBaseDescent B S hS G φ hφ M) ≫
              pullbackTransport ((modulePullback B S hS φ).obj M)
                (GroupoidInAlgebraicSpaces.firstArrow_comp_source G) ≫
              modulePullbackReindex (GroupoidInAlgebraicSpaces.secondArrow G)
                (spaceBaseDescent B S hS G φ hφ M)) ≫
            pullbackTransport ((modulePullback B S hS φ).obj M)
              (GroupoidInAlgebraicSpaces.comp_comp_source G).symm) :=
        congrArg (modulePullbackFlatten' φ K₀ K₅) (comp_assoc₅ _ _ _ _ _).symm

/-- **The unit condition of Stacks 0441 for the canonical transition morphism.** -/
theorem spaceBaseDescent_unit (φ : G.objects ⟶ X) (hφ : G.target ≫ φ = G.source ≫ φ)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    groupoidPullbackTransition B S hS G ((modulePullback B S hS φ).obj M)
        (spaceBaseDescent B S hS G φ hφ M) (GroupoidInAlgebraicSpaces.identityArrow G) =
      pullbackTransport ((modulePullback B S hS φ).obj M)
        ((GroupoidInAlgebraicSpaces.identityArrow_comp_target G).trans
          (GroupoidInAlgebraicSpaces.identityArrow_comp_source G).symm) := by
  have ee : GroupoidInAlgebraicSpaces.identityArrow G ≫ G.target ≫ φ =
      GroupoidInAlgebraicSpaces.identityArrow G ≫ G.source ≫ φ := by rw [hφ]
  have K₀ : (GroupoidInAlgebraicSpaces.identityArrow G ≫ G.target) ≫ φ =
      GroupoidInAlgebraicSpaces.identityArrow G ≫ G.target ≫ φ := Category.assoc _ _ _
  have K₁ : (GroupoidInAlgebraicSpaces.identityArrow G ≫ G.source) ≫ φ =
      GroupoidInAlgebraicSpaces.identityArrow G ≫ G.source ≫ φ := Category.assoc _ _ _
  apply modulePullbackFlatten'_injective φ K₀ K₁
  rw [groupoidPullbackTransition_eq_transitionReindex,
    transitionReindex_eq_modulePullbackReindex,
    modulePullbackFlatten'_reindex_spaceBaseDescent B S hS G φ hφ M
      (GroupoidInAlgebraicSpaces.identityArrow G) K₀ K₁ ee,
    modulePullbackFlatten'_pullbackTransport φ K₀ K₁ _ M ee]

/-- **The canonical transition morphism is natural in the module on the base.** -/
theorem spaceBaseDescent_naturality (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ) {M N : Modules.{u, u} B S hS X.1 X.2} (ψ : M ⟶ N) :
    spaceBaseDescent B S hS G φ hφ M ≫
        (modulePullback B S hS G.source).map ((modulePullback B S hS φ).map ψ) =
      (modulePullback B S hS G.target).map ((modulePullback B S hS φ).map ψ) ≫
        spaceBaseDescent B S hS G φ hφ N :=
  modulePullbackUnflatten_naturality φ ψ (pullbackTransport M hφ) (pullbackTransport N hφ)
    (pullbackTransport_naturality ψ hφ).symm

/-- **Stacks 03M3**, the descent datum, for a target which is an algebraic space.  For a
quasi-coherent module `ℱ` on an algebraic space `X` and a morphism `φ : U ⟶ X` from the
object space of a groupoid in algebraic spaces with `t ≫ φ = s ≫ φ`, the inverse image `φ^*ℱ`
together with its canonical transition morphism is a quasi-coherent module on the groupoid. -/
@[stacks 03M3 "the canonical descent datum on φ^*ℱ and the two conditions of Stacks 0441, for \
a target which is an algebraic space"]
def quasicoherentModuleOfSpaceBase (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : M.IsQuasicoherentOnSite) : QuasicoherentModule B S hS G where
  F := ⟨(modulePullback B S hS φ).obj M,
    isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS φ M hM⟩
  alpha := spaceBaseDescent B S hS G φ hφ M
  cocycle := spaceBaseDescent_cocycle B S hS G φ hφ M
  unit := spaceBaseDescent_unit B S hS G φ hφ M

/-- The underlying module of the quasi-coherent module on the groupoid attached to `ℱ` is
`φ^*ℱ`. -/
theorem quasicoherentModuleOfSpaceBase_F_obj (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) :
    (quasicoherentModuleOfSpaceBase B S hS G φ hφ M hM).F.obj =
      (modulePullback B S hS φ).obj M :=
  rfl

/-- The transition morphism of the quasi-coherent module on the groupoid attached to `ℱ` is the
canonical one.

Both this and `AlgebraicGeometry.Space.quasicoherentModuleOfSpaceBase_F_obj` hold by definition;
they are recorded because the compatibility field of a morphism of quasi-coherent modules on a
groupoid is stated through these two projections, and the equation must be reached by rewriting
with them rather than by a conversion — see the implementation notes. -/
theorem quasicoherentModuleOfSpaceBase_alpha (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ)
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : M.IsQuasicoherentOnSite) :
    (quasicoherentModuleOfSpaceBase B S hS G φ hφ M hM).alpha =
      spaceBaseDescent B S hS G φ hφ M :=
  rfl

/-- **The compatibility of a morphism of inverse images with the canonical transition
morphisms**, stated through the two projections the compatibility field of
`AlgebraicGeometry.Space.QuasicoherentModule.Hom` reads. -/
theorem quasicoherentModuleOfSpaceBase_comm (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ)
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property} (ψ : M ⟶ N) :
    (quasicoherentModuleOfSpaceBase B S hS G φ hφ M.obj M.property).alpha ≫
        (modulePullback B S hS G.source).map ((modulePullback B S hS φ).map ψ.hom) =
      (modulePullback B S hS G.target).map ((modulePullback B S hS φ).map ψ.hom) ≫
        (quasicoherentModuleOfSpaceBase B S hS G φ hφ N.obj N.property).alpha :=
  (congrArg (fun a => a ≫ (modulePullback B S hS G.source).map
          ((modulePullback B S hS φ).map ψ.hom))
        (quasicoherentModuleOfSpaceBase_alpha B S hS G φ hφ M.obj M.property)).trans
    ((spaceBaseDescent_naturality B S hS G φ hφ (M := M.obj) (N := N.obj) ψ.hom).trans
      (congrArg (fun a => (modulePullback B S hS G.target).map
            ((modulePullback B S hS φ).map ψ.hom) ≫ a)
        (quasicoherentModuleOfSpaceBase_alpha B S hS G φ hφ N.obj N.property).symm))

end AlgebraicGeometry.Space

end
