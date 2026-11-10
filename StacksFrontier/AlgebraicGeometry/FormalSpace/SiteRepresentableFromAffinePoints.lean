module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineCompletionTypes
public import StacksFrontier.AlgebraicGeometry.FormalSpace.AffineSourceRefined
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ColimitLocalFactorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.Monomorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFromAffinePoints
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTargetRefined
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedFiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteCoproductLargeValuedRefined
public import StacksFrontier.CategoryTheory.Limits.CoproductPullback
public import StacksFrontier.CategoryTheory.Sites.InfinitaryExtensive
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.SiteGluing
public import StacksFrontier.CategoryTheory.Sites.MonoSheafifiedYoneda
import all StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableFromAffinePoints

/-!
# Relative representability by objects of the site, from the affine points of the target

Let `S` be a scheme contained in a big fppf site `B` and let `Φ : X ⟶ Z` be a morphism of fppf
sheaves over `S`. Suppose that over every point of `Z` out of an **affine** object of the site
the base change of `Φ` is represented by an *open subscheme* of that affine. Then `Φ` is
relatively representable with respect to the sheafified Yoneda embedding, that is **by objects
of the site**, and the representing object over an arbitrary point is again an open subscheme of
it.

"By objects of the site" is strictly stronger than "by algebraic spaces", and the difference is
set-theoretic: an algebraic space étale over an affine scheme can be an arbitrary disjoint union
of copies of it, with no cardinal bound, whereas an object of the site is bounded by the site's
size cutoff. That is the phenomenon the condition of **Stacks 0AIS** governs, and it is why the
two criteria the library already carries from affine points —
`AlgebraicGeometry.FormalSpace.isRepresentableByAlgebraicSpacesULift_of_affine_pullback` and
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_openImmersion_over_affinePoints` —
conclude representability by algebraic spaces only. Both of them cover the test object `T` by the
*coproduct* `V` of its affine opens and compute the base change over `V`; the base change over
`T` itself is then only an algebraic space, descended along the surjective étale `V ⟶ T`.

The open-immersion hypothesis removes the need for that descent, because open subschemes of one
scheme glue inside its lattice of opens instead of into a coproduct: the representing object
over `T` is the single open

`O = ⨆ i, range (W i ⟶ T_i ⟶ T)`,

the union over the affine opens `T_i` of `T` of the images of the open subschemes `W i`
representing the base changes over them. An open immersion does not raise the size of a scheme,
so `O` lies in the site, and no cardinal bound beyond the one `T` itself supplies is needed.

## Main results

* `AlgebraicGeometry.FormalSpace.AffineOpenPullback`: the hypothesis, in the shape in which
  `AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_openImmersion_over_affinePoints`
  already states it.
* `AlgebraicGeometry.FormalSpace.mono_of_affineOpenPullback`: such a morphism is a
  monomorphism, by **Stacks 0GHV**.
* `AlgebraicGeometry.FormalSpace.exists_openImmersion_pullback_of_affineOpenPullback`: the
  hypothesis self-improves — the base change over *every* point of the target is represented by
  an open subscheme of it.
* `AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_affineOpenPullback`: hence `Φ` is
  relatively representable by objects of the site.
* `AlgebraicGeometry.FormalSpace.affineOpenPullback_colimMap` and
  `…satisfiesSetTheoreticCondition_colimit_of_openChartSystem`: the instance the chart systems
  of **Stacks 0AIU** and **Stacks 0GVN** need — the set-theoretic condition of **Stacks 0AIS**
  passes from the colimit of a directed diagram to the colimit of a chart diagram whose chart
  morphisms are representable open immersions.
* `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_openChartSystem_of_affineStages`:
  `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_openChartSystem` with its hypothesis
  `haff` — that each chart colimit be an affine formal algebraic space — proved rather than
  assumed, from affineness of the *stages* of the chart diagrams.

## Implementation notes

*Why the morphism is a monomorphism.* Over an affine point the base change is an open
subscheme, hence a monomorphism, and monomorphy of a morphism of fppf sheaves is detected on
the base changes along its affine points — **Stacks 0GHV**, condition (3) implies condition (1),
which is `AlgebraicGeometry.FormalSpace.mono_of_isMonoOnAffineBaseChanges`. That is what makes
the pieces agree on their overlaps, and it is used nowhere else.

*Why no gluing of morphisms is performed.* Rather than assemble a morphism `h_O ⟶ X` out of the
`W i` by the sheaf condition, the proof base changes the fibre product `P = X ×_Z h_T` to `h_O`
and shows the projection `P ×_{h_T} h_O ⟶ h_O` to be an isomorphism: it is a monomorphism
because `Φ` is, and it is locally surjective because the `W i` cover `O`, and a locally bijective
morphism of sheaves is an isomorphism
(`CategoryTheory.Sheaf.isLocallyBijective_iff_isIso`). The resulting section `h_O ⟶ P` is then
itself locally bijective — a monomorphism over `h_T`, and locally surjective because each
`W i ⟶ P` factors through it — so `h_O ≅ P`, which is the required cartesian square. The two
steps are the same argument run twice, which is why neither is factored out.

## References

* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AIU](https://stacks.math.columbia.edu/tag/0AIU)
* [Stacks Project, Tag 0GVM](https://stacks.math.columbia.edu/tag/0GVM)
* [Stacks Project, Tag 0GVN](https://stacks.math.columbia.edu/tag/0GVN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.FormalSpace.CartesianColimit (equifibered_colimit_isPullback)

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The affine-point hypothesis.** The base change of `Φ` along every point of its target
out of an *affine* object of the site is represented by an open subscheme of that affine.

This is the hypothesis of
`AlgebraicGeometry.FormalSpace.isRepresentableEtale_of_openImmersion_over_affinePoints`,
named so that the statements below can share it. -/
abbrev AffineOpenPullback {X Z : FppfSheaf B S hS} (Φ : X ⟶ Z) : Prop :=
  ∀ (U : BigFppfOver B S hS), IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
    ∀ ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ Z,
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ U)
      (r : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ X),
      IsPullback r ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p) Φ ξ ∧
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map p)

/-- The Yoneda embedding sends a morphism of the site that is an open immersion to a mono. -/
private theorem mono_uliftYoneda_map_of_isOpenImmersion {U V : BigFppfOver B S hS} (p : U ⟶ V)
    (hp : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map p)) :
    Mono ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p) := by
  have : Mono p := (BigFppfOver.toScheme B S hS).mono_of_mono_map inferInstance
  exact CategoryTheory.preserves_mono_of_preservesLimit _ p

/-- **A morphism satisfying the affine-point hypothesis is a monomorphism.** Over an affine
object of the site its base change is an open subscheme of that affine, hence a monomorphism,
so this is **Stacks 0GHV**, condition (3) implies condition (1), which the library carries as
`AlgebraicGeometry.FormalSpace.mono_of_isMonoOnAffineBaseChanges`.

Two base changes along one and the same point are isomorphic over it, which is what carries
monomorphy from the open subscheme the hypothesis supplies to an arbitrary represented base
change. -/
theorem mono_of_affineOpenPullback {X Z : FppfSheaf B S hS} (Φ : X ⟶ Z)
    (h : AffineOpenPullback B S hS Φ) : Mono Φ := by
  let J := BigFppfOver.topology B S hS
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  refine mono_of_isMonoOnAffineBaseChanges B S hS (fun T hT g W' p q hpb => ?_)
  obtain ⟨V, pp, r, sq, hopen⟩ := h T hT g
  have := mono_uliftYoneda_map_of_isOpenImmersion B S hS pp hopen
  set e := sq.flip.isoIsPullback _ _ hpb
  have hfac : e.inv ≫ J.uliftYoneda.{u + 1}.map pp = p :=
    sq.flip.isoIsPullback_inv_fst _ _ hpb
  refine ⟨fun {W''} g₁ g₂ hg => ?_⟩
  have key : (g₁ ≫ e.inv) ≫ J.uliftYoneda.{u + 1}.map pp =
      (g₂ ≫ e.inv) ≫ J.uliftYoneda.{u + 1}.map pp := by
    rw [Category.assoc, Category.assoc, hfac]
    exact hg
  have h2 := (cancel_mono (J.uliftYoneda.{u + 1}.map pp)).1 key
  calc g₁ = (g₁ ≫ e.inv) ≫ e.hom := by simp
    _ = (g₂ ≫ e.inv) ≫ e.hom := by rw [h2]
    _ = g₂ := by simp

/-- A monomorphism of fppf sheaves that is locally surjective is an isomorphism. -/
private theorem isIso_of_mono_of_isLocallySurjective {A A' : FppfSheaf B S hS} (f : A ⟶ A')
    [Mono f] (hf : Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) f.hom) :
    IsIso f :=
  (Sheaf.isLocallyBijective_iff_isIso f).mp
    ⟨Presheaf.isLocallyInjective_of_injective _ _
      (fun Top => Sheaf.injective_hom_app_of_mono _ _ Top), hf⟩

/-- **The affine-point hypothesis self-improves to every point of the target**: the base change
of `Φ` along an arbitrary scheme-valued point of `Z` is represented by an *open subscheme* of
that point, not merely by an algebraic space over it.

The representing open is the union, inside the lattice of opens of the test object `T`, of the
images of the open subschemes representing the base changes over the affine opens of `T`; it
lies in the site because an open immersion does not raise the size of a scheme. -/
theorem exists_openImmersion_pullback_of_affineOpenPullback
    {X Z : FppfSheaf B S hS} (Φ : X ⟶ Z) (h : AffineOpenPullback B S hS Φ)
    (T : BigFppfOver B S hS)
    (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj T ⟶ Z) :
    ∃ (W : BigFppfOver B S hS) (p : W ⟶ T)
      (r : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ X),
      IsPullback r ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map p) Φ ξ ∧
      _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map p) := by
  classical
  let J := BigFppfOver.topology B S hS
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  have hmonoΦ : Mono Φ := mono_of_affineOpenPullback B S hS Φ h
  obtain ⟨ι, Xf, gX, haff, hopenX, hcovX, -, -⟩ := exists_affineOpens_cover_site B S hS T
  choose W p r sq hopenp using fun i =>
    h (Xf i) (haff i) (J.uliftYoneda.{u + 1}.map (gX i) ≫ ξ)
  have hoi : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (p i ≫ gX i)) := by
    intro i
    rw [Functor.map_comp]
    have := hopenp i
    have := hopenX i
    infer_instance
  -- the open images of the transported affine opens, and their union
  have hOi : ∀ i, ∃ V : ((BigFppfOver.toScheme B S hS).obj T).Opens,
      (V : Set _) = Set.range ((BigFppfOver.toScheme B S hS).map (p i ≫ gX i)).base := by
    intro i
    have := hoi i
    exact ⟨((BigFppfOver.toScheme B S hS).map (p i ≫ gX i)).opensRange, rfl⟩
  choose Oi hOi using hOi
  obtain ⟨Os, oι, hoιopen, hoιrange, houniv⟩ := exists_restrict_bigFppfOver T (⨆ i, Oi i)
  have hmonooι := mono_uliftYoneda_map_of_isOpenImmersion B S hS oι hoιopen
  -- each piece lands in the union
  have hka : ∀ i, ∃ k : W i ⟶ Os, k ≫ oι = p i ≫ gX i := by
    intro i
    refine houniv (p i ≫ gX i) ?_
    intro x hx
    exact le_iSup Oi i ((hOi i).symm.subset hx)
  choose ka hka using hka
  have hkaopen : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (ka i)) := by
    intro i
    have : _root_.AlgebraicGeometry.IsOpenImmersion
        ((BigFppfOver.toScheme B S hS).map (ka i) ≫
          (BigFppfOver.toScheme B S hS).map oι) := by
      rw [← Functor.map_comp, hka i]
      exact hoi i
    exact _root_.AlgebraicGeometry.IsOpenImmersion.of_comp
      ((BigFppfOver.toScheme B S hS).map (ka i)) ((BigFppfOver.toScheme B S hS).map oι)
  have hkacov : ∀ y : (BigFppfOver.toScheme B S hS).obj Os,
      ∃ i, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ka i)).base := by
    intro y
    have hy : ((BigFppfOver.toScheme B S hS).map oι).base y ∈
        (⨆ i, Oi i : ((BigFppfOver.toScheme B S hS).obj T).Opens) :=
      hoιrange.subset ⟨y, rfl⟩
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hy
    obtain ⟨z, hz⟩ := (hOi i).subset hi
    refine ⟨i, z, ?_⟩
    refine ((BigFppfOver.toScheme B S hS).map oι).isOpenEmbedding.injective ?_
    calc ((BigFppfOver.toScheme B S hS).map oι).base
          (((BigFppfOver.toScheme B S hS).map (ka i)).base z)
        = ((BigFppfOver.toScheme B S hS).map (ka i) ≫
            (BigFppfOver.toScheme B S hS).map oι).base z := rfl
      _ = ((BigFppfOver.toScheme B S hS).map (p i ≫ gX i)).base z := by
        rw [← Functor.map_comp, hka i]
      _ = ((BigFppfOver.toScheme B S hS).map oι).base y := hz
  have hcovO : Sieve.ofArrows W ka ∈ J Os :=
    BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective B S hS W Os ka hkaopen hkacov
  have hcovT : Sieve.ofArrows Xf gX ∈ J T :=
    BigFppfOver.sieve_ofArrows_mem_topology_of_jointlySurjective B S hS Xf T gX hopenX hcovX
  -- the fibre product of `Φ` with the point, and the pieces inside it
  have hP : IsPullback (pullback.fst ξ Φ) (pullback.snd ξ Φ) ξ Φ := IsPullback.of_hasPullback ξ Φ
  have hleft : ∀ i, ∃ m : J.uliftYoneda.{u + 1}.obj (W i) ⟶ pullback ξ Φ,
      IsPullback m (J.uliftYoneda.{u + 1}.map (p i)) (pullback.fst ξ Φ)
        (J.uliftYoneda.{u + 1}.map (gX i)) :=
    fun i => ⟨_, IsPullback.of_right' (sq i) hP.flip⟩
  choose mi hmi using hleft
  have hmonoπ : Mono (pullback.fst ξ Φ) := pullback.fst_of_mono
  have hni : ∀ i, ∃ n : J.uliftYoneda.{u + 1}.obj (W i) ⟶
        pullback (J.uliftYoneda.{u + 1}.map oι) (pullback.fst ξ Φ),
      n ≫ pullback.fst (J.uliftYoneda.{u + 1}.map oι) (pullback.fst ξ Φ) =
        J.uliftYoneda.{u + 1}.map (ka i) ∧
      n ≫ pullback.snd (J.uliftYoneda.{u + 1}.map oι) (pullback.fst ξ Φ) = mi i := by
    intro i
    have hc : J.uliftYoneda.{u + 1}.map (ka i) ≫ J.uliftYoneda.{u + 1}.map oι =
        mi i ≫ pullback.fst ξ Φ := by
      rw [(hmi i).w, ← Functor.map_comp, ← Functor.map_comp, hka i]
    exact ⟨pullback.lift _ _ hc, pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩
  choose ni hni1 hni2 using hni
  -- the base change of the fibre product to the open is the open itself
  have hqls : Presheaf.IsLocallySurjective J
      (pullback.fst (J.uliftYoneda.{u + 1}.map oι) (pullback.fst ξ Φ)).hom := by
    refine ⟨fun {T'} s => ?_⟩
    set α := (GrothendieckTopology.uliftYonedaEquiv.{u + 1} J
      (X := T') (F := J.uliftYoneda.{u + 1}.obj Os)).symm s with hα
    have hmapa : J.uliftYoneda.{u + 1}.map (J.uliftYoneda.{u + 1}.preimage α) = α :=
      J.uliftYoneda.{u + 1}.map_preimage α
    refine J.superset_covering ?_
      (J.pullback_stable (J.uliftYoneda.{u + 1}.preimage α) hcovO)
    intro T'' g hg
    obtain ⟨-, b, -, ⟨i⟩, hcomp⟩ := hg
    refine ⟨GrothendieckTopology.uliftYonedaEquiv.{u + 1} J
      (J.uliftYoneda.{u + 1}.map b ≫ ni i), ?_⟩
    rw [← GrothendieckTopology.uliftYonedaEquiv_comp, Category.assoc, hni1 i,
      ← Functor.map_comp, hcomp, Functor.map_comp, hmapa,
      ← GrothendieckTopology.uliftYonedaEquiv_naturality, hα, Equiv.apply_symm_apply]
  have hmonoq : Mono (pullback.fst (J.uliftYoneda.{u + 1}.map oι) (pullback.fst ξ Φ)) :=
    pullback.fst_of_mono
  have hqiso : IsIso (pullback.fst (J.uliftYoneda.{u + 1}.map oι) (pullback.fst ξ Φ)) :=
    isIso_of_mono_of_isLocallySurjective B S hS _ hqls
  set r2 : J.uliftYoneda.{u + 1}.obj Os ⟶ pullback ξ Φ :=
    inv (pullback.fst (J.uliftYoneda.{u + 1}.map oι) (pullback.fst ξ Φ)) ≫
      pullback.snd (J.uliftYoneda.{u + 1}.map oι) (pullback.fst ξ Φ) with hr2
  have hr2π : r2 ≫ pullback.fst ξ Φ = J.uliftYoneda.{u + 1}.map oι := by
    rw [hr2, Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
  have hkar2 : ∀ i, J.uliftYoneda.{u + 1}.map (ka i) ≫ r2 = mi i := by
    intro i
    rw [hr2, ← hni1 i, Category.assoc, IsIso.hom_inv_id_assoc, hni2 i]
  have hmonor2 : Mono r2 := mono_of_mono_fac hr2π
  -- the open covers the fibre product
  have hr2ls : Presheaf.IsLocallySurjective J r2.hom := by
    refine ⟨fun {T'} s => ?_⟩
    set σ := (GrothendieckTopology.uliftYonedaEquiv.{u + 1} J
      (X := T') (F := pullback ξ Φ)).symm s with hσ
    have hmapa : J.uliftYoneda.{u + 1}.map
        (J.uliftYoneda.{u + 1}.preimage (σ ≫ pullback.fst ξ Φ)) = σ ≫ pullback.fst ξ Φ :=
      J.uliftYoneda.{u + 1}.map_preimage _
    refine J.superset_covering ?_
      (J.pullback_stable (J.uliftYoneda.{u + 1}.preimage (σ ≫ pullback.fst ξ Φ)) hcovT)
    intro T'' g hg
    obtain ⟨-, c, -, ⟨i⟩, hcomp⟩ := hg
    have hw : (J.uliftYoneda.{u + 1}.map g ≫ σ) ≫ pullback.fst ξ Φ =
        J.uliftYoneda.{u + 1}.map c ≫ J.uliftYoneda.{u + 1}.map (gX i) := by
      rw [Category.assoc, ← hmapa, ← Functor.map_comp, ← Functor.map_comp, hcomp]
    refine ⟨GrothendieckTopology.uliftYonedaEquiv.{u + 1} J
      ((hmi i).lift (J.uliftYoneda.{u + 1}.map g ≫ σ) (J.uliftYoneda.{u + 1}.map c) hw ≫
        J.uliftYoneda.{u + 1}.map (ka i)), ?_⟩
    rw [← GrothendieckTopology.uliftYonedaEquiv_comp, Category.assoc, hkar2 i,
      (hmi i).lift_fst, ← GrothendieckTopology.uliftYonedaEquiv_naturality, hσ,
      Equiv.apply_symm_apply]
  have hr2iso : IsIso r2 := isIso_of_mono_of_isLocallySurjective B S hS r2 hr2ls
  refine ⟨Os, oι, r2 ≫ pullback.snd ξ Φ, ?_, hoιopen⟩
  refine (IsPullback.of_iso_pullback ?_ (asIso r2) hr2π rfl).flip
  refine ⟨?_⟩
  change J.uliftYoneda.{u + 1}.map oι ≫ ξ = (r2 ≫ pullback.snd ξ Φ) ≫ Φ
  rw [Category.assoc, ← pullback.condition, ← Category.assoc, hr2π]

/-- **Relative representability by objects of the site, from the affine points of the target.**
A morphism of fppf sheaves over `S` whose base change along every point of its target out of an
affine object of the site is represented by an open subscheme of that affine is relatively
representable with respect to the sheafified Yoneda embedding.

This is `AlgebraicGeometry.FormalSpace.exists_openImmersion_pullback_of_affineOpenPullback`
read along the comparison isomorphism
`CategoryTheory.Sheaf.sheafifiedYonedaIsoUliftYoneda'` of the two Yoneda embeddings into
sheaves, which is available because the big fppf site is subcanonical. -/
theorem relativelyRepresentable_of_affineOpenPullback
    {X Z : FppfSheaf B S hS} (Φ : X ⟶ Z) (h : AffineOpenPullback B S hS Φ) :
    Functor.relativelyRepresentable
      (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)) Φ := by
  let J := BigFppfOver.topology B S hS
  have : J.Subcanonical := bigFppfOver_subcanonical B S hS
  intro a g
  set eG := Sheaf.sheafifiedYonedaIsoUliftYoneda' J
  obtain ⟨Os, oι, r2, hpb, -⟩ :=
    exists_openImmersion_pullback_of_affineOpenPullback B S hS Φ h a (eG.inv.app a ≫ g)
  exact ⟨Os, oι, eG.hom.app Os ≫ r2,
    hpb.of_iso (eG.symm.app Os) (Iso.refl _) (eG.symm.app a) (Iso.refl _)
      (by
        rw [Iso.refl_hom, Category.comp_id, ← Category.assoc,
          show (eG.symm.app Os).hom ≫ eG.hom.app Os = 𝟙 _ from eG.inv_hom_id_app Os,
          Category.id_comp])
      (by simpa using eG.inv.naturality oι) (by simp) (by simp)⟩

/-! ### The chart colimit of a chart system by representable open immersions -/

/-- **The chart morphism of a chart system by representable open immersions satisfies the
affine-point hypothesis.** A point of `colim E` out of an affine — hence quasi-compact — object
of the site factors through a stage
(`AlgebraicGeometry.FormalSpace.exists_factor_through_stage_of_compact`), the chart morphism of
that stage has an open subscheme as its base change by `hαopen`, and the chart base changes from
the colimit by `hsq`. -/
theorem affineOpenPullback_colimMap
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hmono : ∀ ⦃i j : Λ⦄ (f : i ⟶ j), Mono (E.map f))
    {I : Type (u + 1)} (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (hαopen : ∀ (k : I) (i : Λ) (U : BigFppfOver B S hS)
      (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ E.obj i),
      ∃ (W : BigFppfOver B S hS) (pr : W ⟶ U)
        (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ (G k).obj i),
        IsPullback c ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map pr)
          ((α k).app i) ξ ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pr))
    (hsq : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      ∀ (k : I) (i : Λ),
      IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k)) (colimit.ι E i))
    (k : I) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    AffineOpenPullback B S hS (colimMap (α k)) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  intro U hU ξ
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj U) := hU
  have : CompactSpace ((BigFppfOver.toScheme B S hS).obj U) := inferInstance
  obtain ⟨i, ξ', hξ'⟩ := exists_factor_through_stage_of_compact B S hS E hmono U ξ
  obtain ⟨W, pr, c, hpb, hopen⟩ := hαopen k i U ξ'
  refine ⟨W, pr, c ≫ colimit.ι (G k) i, ?_, hopen⟩
  have hpaste : IsPullback (c ≫ colimit.ι (G k) i)
      ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map pr) (colimMap (α k))
      (ξ' ≫ colimit.ι E i) :=
    hpb.paste_horiz (hsq k i)
  rwa [← hξ'] at hpaste

/-- **The set-theoretic condition of Stacks 0AIS for the chart colimit of a chart system by
representable open immersions.** Given the condition for `colim E`, it holds for the colimit of
each chart diagram.

The chart morphism `colim (G k) ⟶ colim E` is relatively representable by objects of the site
by `AlgebraicGeometry.FormalSpace.relativelyRepresentable_of_affineOpenPullback`, and the
condition passes to the source of such a morphism by
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_relativelyRepresentable`.

As in `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_openChartSystem`, the
cartesianness of each chart diagram is asked at the *transitions* of the index, as
equifiberedness, which is where a chart system transported across thickenings has it
(`AlgebraicGeometry.FormalSpace.isPullback_transportedOpenInclusion`); the comparison squares at
the colimit that `AlgebraicGeometry.FormalSpace.affineOpenPullback_colimMap` consumes are the
equivalent form of it supplied by
`AlgebraicGeometry.FormalSpace.CartesianColimit.equifibered_colimit_isPullback`. -/
theorem satisfiesSetTheoreticCondition_colimit_of_openChartSystem
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hmono : ∀ ⦃i j : Λ⦄ (f : i ⟶ j), Mono (E.map f))
    {I : Type (u + 1)} (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (hαopen : ∀ (k : I) (i : Λ) (U : BigFppfOver B S hS)
      (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ E.obj i),
      ∃ (W : BigFppfOver B S hS) (pr : W ⟶ U)
        (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ (G k).obj i),
        IsPullback c ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map pr)
          ((α k).app i) ξ ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pr))
    (hα : ∀ k, (α k).Equifibered)
    (hEset : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      SatisfiesSetTheoreticCondition B S hS (colimit E))
    (k : I) :
    letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
    SatisfiesSetTheoreticCondition B S hS (colimit (G k)) := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  -- the comparison squares at the colimit, from the equifiberedness of each chart diagram
  have hsq : ∀ (k : I) (i : Λ),
      IsPullback (colimit.ι (G k) i) ((α k).app i) (colimMap (α k)) (colimit.ι E i) := by
    intro k i
    have _ : IsConnected (Under i) := IsFiltered.isConnected _
    exact equifibered_colimit_isPullback (α k) (hα k) i
  exact satisfiesSetTheoreticCondition_of_relativelyRepresentable B S hS (colimMap (α k))
    (relativelyRepresentable_of_affineOpenPullback B S hS (colimMap (α k))
      (affineOpenPullback_colimMap B S hS E hmono G α hαopen hsq k)) hEset

/-- **A chart system by representable open immersions over diagrams of affine formal algebraic
spaces makes a directed colimit a formal algebraic space.**

This is `AlgebraicGeometry.FormalSpace.isFormalAlgebraicSpace_of_openChartSystem` with its
hypothesis `haff` — that each chart colimit be an affine formal algebraic space — *proved*
rather than assumed: the stages of each chart diagram are affine formal algebraic spaces and its
transition morphisms are representable thickenings, so **Stacks 0GVM**
(`AlgebraicGeometry.FormalSpace.isAffineFormalAlgebraicSpace_colimit`) applies to it once its
set-theoretic condition of **Stacks 0AIS** is known, and that is
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_colimit_of_openChartSystem`. -/
theorem isFormalAlgebraicSpace_of_openChartSystem_of_affineStages
    {Λ : Type (u + 1)} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    (E : Λ ⥤ FppfSheaf B S hS)
    (hmono : ∀ ⦃i j : Λ⦄ (f : i ⟶ j), Mono (E.map f))
    {I : Type (u + 1)} (G : I → (Λ ⥤ FppfSheaf B S hS)) (α : ∀ k, G k ⟶ E)
    (hGaff : ∀ (k : I) (i : Λ), IsAffineFormalAlgebraicSpace B S hS ((G k).obj i))
    (hGthick : ∀ (k : I) ⦃i j : Λ⦄ (g : i ⟶ j),
      MorphismProperty.relative (Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS))
        (MorphismProperty.inverseImage
          (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
          (BigFppfOver.toScheme B S hS)) ((G k).map g))
    (hαopen : ∀ (k : I) (i : Λ) (U : BigFppfOver B S hS)
      (ξ : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj U ⟶ E.obj i),
      ∃ (W : BigFppfOver B S hS) (pr : W ⟶ U)
        (c : (BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.obj W ⟶ (G k).obj i),
        IsPullback c ((BigFppfOver.topology B S hS).uliftYoneda.{u + 1}.map pr)
          ((α k).app i) ξ ∧
        _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map pr))
    (hα : ∀ k, (α k).Equifibered)
    (hcov : letI : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) :=
        Sheaf.instHasColimitsOfSize
      ∀ i : Λ, Sheaf.IsLocallySurjective (Sigma.desc (fun k ↦ (α k).app i)))
    (Z : FppfSheaf B S hS) (hZset : SatisfiesSetTheoreticCondition B S hS Z)
    (hZ : Nonempty (Z ≅ colimit E)) :
    IsFormalAlgebraicSpace B S hS Z := by
  let : HasColimitsOfSize.{u + 1, u + 1} (FppfSheaf B S hS) := Sheaf.instHasColimitsOfSize
  obtain ⟨eZ⟩ := hZ
  have hEset : SatisfiesSetTheoreticCondition B S hS (colimit E) :=
    satisfiesSetTheoreticCondition_of_iso B S hS eZ hZset
  refine isFormalAlgebraicSpace_of_openChartSystem B S hS E hmono G α (fun k ↦ ?_)
    hαopen hα hcov Z hZset ⟨eZ⟩
  exact isAffineFormalAlgebraicSpace_colimit B S hS (G k) (hGaff k) (hGthick k)
    (colimit (G k)) (Iso.refl _)
    (satisfiesSetTheoreticCondition_colimit_of_openChartSystem B S hS E hmono G α hαopen hα
      hEset k)

end AlgebraicGeometry.FormalSpace

end
