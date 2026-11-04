module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.FullnessViaSigmaSite
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.SingleMemberFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.SingleMorphismHomDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuasicoherentFromSpaceBaseEssSurj
public import StacksFrontier.CategoryTheory.Adjunction.UnitSectionProjection

/-!
# The functor from the base to the groupoid as an equivalence

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces, let `X` be an algebraic space and let
`φ : U ⟶ X` be a surjective étale morphism with `t ≫ φ = s ≫ φ` and `R = U ×_X U` with `t`, `s`
the two projections. The functor `AlgebraicGeometry.Space.quasicoherentFromSpaceBase`,
`ℱ ↦ (φ^*ℱ, α)`, is an equivalence `QCoh(𝒪_X) ≌ QCoh(U, R, s, t, c)`.

## Main definitions

* `AlgebraicGeometry.Space.spaceBaseHomPullback`: a morphism of the two attached quasi-coherent
  modules on the groupoid, as a morphism of the two inverse images along `φ`.
* `AlgebraicGeometry.Space.equivalenceQuasicoherentFromSpaceBase`: the equivalence
  `QCoh(𝒪_X) ≌ QCoh(U, R, s, t, c)` whose functor is
  `AlgebraicGeometry.Space.quasicoherentFromSpaceBase`.

## Main results

* `AlgebraicGeometry.Space.canonicalComparison_hom_eq_reindex_spaceBaseDescent`: at a pair of
  morphisms dominated by the arrow space, the canonical comparison of Stacks 04W5 is the
  reindexing of the canonical transition morphism.
* `AlgebraicGeometry.Space.map_comp_canonicalComparison_hom`: the compatibility of a morphism of
  the inverse images with the canonical transition morphisms is the pairwise condition of
  Stacks 04W3 at every pair of morphisms dominated by the arrow space.
* `AlgebraicGeometry.Space.spaceBaseHomPullback_comm`: `spaceBaseHomPullback` commutes with the
  two canonical transition morphisms.
* `AlgebraicGeometry.Space.exists_comp_target_comp_source_eq`: at a kernel pair, every pair of
  morphisms into the space of objects with equal composites to the base is dominated by the arrow
  space.
* `AlgebraicGeometry.Space.relativelyRepresentable_of_representableSource`: a morphism of
  algebraic spaces whose source is isomorphic to a represented presheaf is relatively
  representable.
* `AlgebraicGeometry.Space.faithful_quasicoherentFromSpaceBase_of_isEtaleCovering`: the functor is
  faithful when `{φ}` is an étale covering.
* `AlgebraicGeometry.Space.full_quasicoherentFromSpaceBase`: the functor is full, given descent of
  morphisms of `𝒪_X`-modules along `φ`.
* `AlgebraicGeometry.Space.full_quasicoherentFromSpaceBase_of_isPullback`: the functor is full
  when `φ` is a relatively representable étale covering with kernel pair the arrow space.
* `AlgebraicGeometry.Space.isEquivalence_quasicoherentFromSpaceBase`: the functor is an
  equivalence of categories.

## Implementation notes

The equation `spaceBaseDescent … = (canonicalComparison … ).hom` is a kernel timeout when its two
sides are written out, and so is chaining its one-step identifications inside one `rfl`; it is
reached through `AlgebraicGeometry.Space.canonicalComparison_hom_eq_unflatten`, which composes the
single delta steps with `Eq.trans`.

Instantiating the descent statements at the one-member constant family `fun _ : Unit => φ` is a
kernel timeout, which is why the descent of morphisms used here is the single-morphism one,
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_dominated`.

## References

* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 0441](https://stacks.math.columbia.edu/tag/0441)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {A : AlgebraicSpaces B S hS} (G : GroupoidInAlgebraicSpaces B S hS A)
  {X : AlgebraicSpaces B S hS}

/-- A reindexing of the canonical transition morphism is the unflattened transport along the
equality of the two composites with `φ`. -/
theorem reindex_spaceBaseDescent_eq_unflatten (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ) (M : Modules.{u, u} B S hS X.1 X.2)
    {P : AlgebraicSpaces B S hS} (v : P ⟶ G.arrows)
    (h' : (v ≫ G.target) ≫ φ = (v ≫ G.source) ≫ φ) :
    modulePullbackReindex v (spaceBaseDescent B S hS G φ hφ M) =
      modulePullbackUnflatten φ (pullbackTransport M h') := by
  rw [← modulePullbackFlatten_reindex_spaceBaseDescent B S hS G φ hφ M v h',
    modulePullbackUnflatten_flatten]

/-- The canonical comparison of Stacks 04W5 at a pair of morphisms dominated by the arrow space is
the reindexing of the canonical transition morphism. -/
theorem canonicalComparison_hom_eq_reindex_spaceBaseDescent (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ) (M : Modules.{u, u} B S hS X.1 X.2)
    {P : AlgebraicSpaces B S hS} (v : P ⟶ G.arrows)
    (hab : (v ≫ G.target) ≫ φ = (v ≫ G.source) ≫ φ) :
    (QuasiCoherentDescent.canonicalComparison (v ≫ G.target) (v ≫ G.source) φ φ hab M).hom =
      modulePullbackReindex v (spaceBaseDescent B S hS G φ hφ M) := by
  rw [canonicalComparison_hom_eq_unflatten,
    reindex_spaceBaseDescent_eq_unflatten B S hS G φ hφ M v hab]

/-- A morphism of the inverse images compatible with the canonical transition morphisms satisfies
the pairwise condition of Stacks 04W3 at every pair of morphisms `a`, `b` out of a space which are
the composites of a morphism into the arrow space with the target and the source projections. -/
theorem map_comp_canonicalComparison_hom (φ : G.objects ⟶ X)
    (hφ : G.target ≫ φ = G.source ≫ φ) {M N : Modules.{u, u} B S hS X.1 X.2}
    (ψ : (modulePullback B S hS φ).obj M ⟶ (modulePullback B S hS φ).obj N)
    (hψ : spaceBaseDescent B S hS G φ hφ M ≫ (modulePullback B S hS G.source).map ψ =
      (modulePullback B S hS G.target).map ψ ≫ spaceBaseDescent B S hS G φ hφ N)
    {P : AlgebraicSpaces B S hS} (v : P ⟶ G.arrows) {a b : P ⟶ G.objects}
    (ha : v ≫ G.target = a) (hb : v ≫ G.source = b) (hab : a ≫ φ = b ≫ φ) :
    (modulePullback B S hS a).map ψ ≫
        (QuasiCoherentDescent.canonicalComparison a b φ φ hab N).hom =
      (QuasiCoherentDescent.canonicalComparison a b φ φ hab M).hom ≫
        (modulePullback B S hS b).map ψ := by
  subst ha
  subst hb
  rw [canonicalComparison_hom_eq_reindex_spaceBaseDescent B S hS G φ hφ N v hab,
    canonicalComparison_hom_eq_reindex_spaceBaseDescent B S hS G φ hφ M v hab,
    ← transitionReindex_eq_modulePullbackReindex,
    ← transitionReindex_eq_modulePullbackReindex,
    ← groupoidPullbackTransition_eq_transitionReindex,
    ← groupoidPullbackTransition_eq_transitionReindex]
  exact groupoidPullbackTransition_naturality B S hS G ψ hψ v

section Functor

variable (φ : G.objects ⟶ X) (hφet : IsEtale B S hS φ.hom)
  (hφ : G.target ≫ φ = G.source ≫ φ)

/-- A morphism of the two quasi-coherent modules on the groupoid attached to two quasi-coherent
`𝒪_X`-modules, as a morphism of the two inverse images along `φ`: its underlying morphism. -/
def spaceBaseHomPullback {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property}
    (θ : spaceBaseObj B S hS G φ hφ M ⟶ spaceBaseObj B S hS G φ hφ N) :
    (modulePullback B S hS φ).obj M.obj ⟶ (modulePullback B S hS φ).obj N.obj :=
  θ.hom

/-- `AlgebraicGeometry.Space.spaceBaseHomPullback` commutes with the canonical transition
morphisms. -/
theorem spaceBaseHomPullback_comm
    {M N : QuasicoherentSheaves.{u, u} B S hS X.obj X.property}
    (θ : spaceBaseObj B S hS G φ hφ M ⟶ spaceBaseObj B S hS G φ hφ N) :
    spaceBaseDescent B S hS G φ hφ M.obj ≫
        (modulePullback B S hS G.source).map (spaceBaseHomPullback B S hS G φ hφ θ) =
      (modulePullback B S hS G.target).map (spaceBaseHomPullback B S hS G φ hφ θ) ≫
        spaceBaseDescent B S hS G φ hφ N.obj := by
  have h := QuasicoherentModule.compatible_hom θ
  rwa [QuasicoherentModule.Compatible, spaceBaseObj_alpha, spaceBaseObj_alpha] at h

/-- The kernel-pair identification carries the first projection of the fibre product to the target
projection of the groupoid, read backwards. -/
theorem arrowsKernelPairIso_inv_comp_target
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    (arrowsKernelPairIso B S hS G φ hpb).inv ≫ G.target =
      QuasiCoherentDescent.pairFst B S hS (fun _ : Unit => G.objects) (fun _ => φ) () () := by
  rw [Iso.inv_comp_eq, arrowsKernelPairIso_hom_comp_pairFst]

/-- The kernel-pair identification carries the second projection of the fibre product to the source
projection of the groupoid, read backwards. -/
theorem arrowsKernelPairIso_inv_comp_source
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    (arrowsKernelPairIso B S hS G φ hpb).inv ≫ G.source =
      QuasiCoherentDescent.pairSnd B S hS (fun _ : Unit => G.objects) (fun _ => φ) () () := by
  rw [Iso.inv_comp_eq, arrowsKernelPairIso_hom_comp_pairSnd]

/-- At a kernel pair `R = U ×_X U`, every pair of morphisms into the space of objects with equal
composites to the base is the pair of composites of one morphism into the arrow space with the
target and the source projections of the groupoid. -/
theorem exists_comp_target_comp_source_eq
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
    {P : AlgebraicSpaces B S hS} (a b : P ⟶ G.objects) (hab : a ≫ φ = b ≫ φ) :
    ∃ v : P ⟶ G.arrows, v ≫ G.target = a ∧ v ≫ G.source = b := by
  refine ⟨ObjectProperty.homMk (hpb.lift a.hom b.hom ?_), ?_, ?_⟩
  · exact congrArg (fun f : P ⟶ X => f.hom) hab
  · exact ObjectProperty.hom_ext _ (hpb.lift_fst _ _ _)
  · exact ObjectProperty.hom_ext _ (hpb.lift_snd _ _ _)

/-- A morphism of algebraic spaces whose source is isomorphic to a represented presheaf is
relatively representable. -/
theorem relativelyRepresentable_of_representableSource {P Z : AlgebraicSpaces B S hS}
    (ψ : P ⟶ Z) (W : BigFppfOver B S hS) (e : yoneda.obj W ≅ P.1) :
    yoneda.relativelyRepresentable ψ.hom := by
  have key : yoneda.relativelyRepresentable (e.inv ≫ e.hom ≫ ψ.hom) :=
    MorphismProperty.comp_mem _ _ _
      (Functor.relativelyRepresentable.of_isIso yoneda e.inv)
      (relativelyRepresentable_of_isAlgebraicSpace B S hS Z.2 (e.hom ≫ ψ.hom))
  simpa using key

/-- The functor from the base to the groupoid is faithful when `{φ}` is an étale covering
of `X`. -/
theorem faithful_quasicoherentFromSpaceBase_of_isEtaleCovering
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => G.objects.1) (fun _ => φ.hom)) :
    (quasicoherentFromSpaceBase B S hS G φ hφ).Faithful :=
  have : (modulePullback B S hS φ).Faithful :=
    ⟨fun {_ _} χ χ' h =>
      QuasiCoherentDescent.modulePullback_map_injective_of_isEtaleCovering B S hS
        (fun _ : Unit => G.objects) (fun _ => φ) hcov χ χ' fun _ => h⟩
  faithful_quasicoherentFromSpaceBase B S hS G φ hφ

/-- The functor from the base to the groupoid is full, given descent of morphisms of
`𝒪_X`-modules along `φ`: a morphism of the inverse images satisfying the pairwise condition at
every morphism into the arrow space is the inverse image of a morphism of `𝒪_X`-modules. -/
theorem full_quasicoherentFromSpaceBase
    (hdesc : ∀ (M N : Modules.{u, u} B S hS X.1 X.2)
      (ψ : (modulePullback B S hS φ).obj M ⟶ (modulePullback B S hS φ).obj N),
      (∀ (P : AlgebraicSpaces B S hS) (v : P ⟶ G.arrows)
          (hab : (v ≫ G.target) ≫ φ = (v ≫ G.source) ≫ φ),
          (modulePullback B S hS (v ≫ G.target)).map ψ ≫
              (QuasiCoherentDescent.canonicalComparison (v ≫ G.target) (v ≫ G.source) φ φ
                hab N).hom =
            (QuasiCoherentDescent.canonicalComparison (v ≫ G.target) (v ≫ G.source) φ φ
                hab M).hom ≫
              (modulePullback B S hS (v ≫ G.source)).map ψ) →
        ∃ χ : M ⟶ N, (modulePullback B S hS φ).map χ = ψ) :
    (quasicoherentFromSpaceBase B S hS G φ hφ).Full where
  map_surjective {M N} θ := by
    obtain ⟨χ, hχ⟩ := hdesc M.obj N.obj (spaceBaseHomPullback B S hS G φ hφ θ)
      fun _ v hab => map_comp_canonicalComparison_hom B S hS G φ hφ
        (spaceBaseHomPullback B S hS G φ hφ θ)
        (spaceBaseHomPullback_comm B S hS G φ hφ θ) v rfl rfl hab
    refine ⟨ObjectProperty.homMk χ, QuasicoherentModule.Hom.ext ?_⟩
    rw [quasicoherentFromSpaceBase_map, spaceBaseHom_hom, spaceBasePullbackMap_eq]
    exact hχ

include hφet in
/-- The functor from the base to the groupoid is full for an étale `φ` which is relatively
representable, is an étale covering, and has the arrow space as its kernel pair. -/
theorem full_quasicoherentFromSpaceBase_of_isPullback
    (hrep : yoneda.relativelyRepresentable φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom)
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => G.objects.1) (fun _ => φ.hom)) :
    (quasicoherentFromSpaceBase B S hS G φ hφ).Full :=
  full_quasicoherentFromSpaceBase B S hS G φ hφ fun _ _ ψ hψ =>
    QuasiCoherentDescent.exists_modulePullback_map_eq_of_dominated B S hS φ hφet hrep hcov ψ
      fun P a b hab => by
        obtain ⟨v, rfl, rfl⟩ := exists_comp_target_comp_source_eq B S hS G φ hpb a b hab
        exact hψ P v hab

include hφet in
/-- The functor `ℱ ↦ (φ^*ℱ, α)` from the quasi-coherent `𝒪_X`-modules to the quasi-coherent
modules on `(U, R, s, t, c)` is an equivalence of categories, for `φ : U ⟶ X` étale with
`t ≫ φ = s ≫ φ`, `{φ}` a surjective étale covering of `X`, `φ` relatively representable, and the
arrow space the kernel pair `R = U ×_X U` with `t`, `s` the two projections. -/
@[stacks 03M3 "the functor QCoh(𝒪_X) ⥤ QCoh(U, R, s, t, c) is an equivalence of categories, for \
a target which is an algebraic space: full faithfulness and essential surjectivity at the \
hypotheses of the source"]
theorem isEquivalence_quasicoherentFromSpaceBase
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => G.objects.1) (fun _ => φ.hom))
    (hrep : yoneda.relativelyRepresentable φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    (quasicoherentFromSpaceBase B S hS G φ hφ).IsEquivalence := by
  have := full_quasicoherentFromSpaceBase_of_isPullback B S hS G φ hφet hφ hrep hpb hcov
  have := faithful_quasicoherentFromSpaceBase_of_isEtaleCovering B S hS G φ hφ hcov
  have : (quasicoherentFromSpaceBase B S hS G φ hφ).EssSurj :=
    ⟨exists_spaceBaseObj_iso B S hS G φ hφet hφ hcov hrep hpb⟩
  exact { }

include hφet in
/-- The equivalence `QCoh(𝒪_X) ≌ QCoh(U, R, s, t, c)` whose functor is
`AlgebraicGeometry.Space.quasicoherentFromSpaceBase`, under the hypotheses of
`AlgebraicGeometry.Space.isEquivalence_quasicoherentFromSpaceBase`. -/
@[stacks 03M3 "the equivalence QCoh(𝒪_X) ≌ QCoh(U, R, s, t, c) itself, for a target which is an \
algebraic space, at the hypotheses of the source"]
def equivalenceQuasicoherentFromSpaceBase
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => G.objects.1) (fun _ => φ.hom))
    (hrep : yoneda.relativelyRepresentable φ.hom)
    (hpb : IsPullback G.target.hom G.source.hom φ.hom φ.hom) :
    QuasicoherentSheaves.{u, u} B S hS X.obj X.property ≌ QuasicoherentModule B S hS G :=
  haveI := isEquivalence_quasicoherentFromSpaceBase B S hS G φ hφet hφ hcov hrep hpb
  (quasicoherentFromSpaceBase B S hS G φ hφ).asEquivalence

end Functor

end AlgebraicGeometry.Space

end
