module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Topology.Simplicial.Site

/-!
# The inclusion of one degree into the site of a simplicial space

For a simplicial topological space `X` and a simplicial degree `n`, the open subsets of `X_n`
form the degree-`n` part of the site of simplicial opens of `X`. This file builds the resulting
inclusion functor, shows that it is a continuous and cocontinuous morphism of sites, and records
that it preserves fibre products and equalizers.

Continuity is expressed by Mathlib's sheaf-theoretic `Functor.IsContinuous`; it follows from
preservation of levelwise open covers and of their pullbacks. Cocontinuity is Mathlib's
`Functor.IsCocontinuous`, equivalently the lifting of covering sieves: a levelwise cover of an
open in degree `n` is already a cover inside that degree.

## Main definitions

* `Stacks.Topology.Simplicial.levelFunctor`: the inclusion of the opens in one simplicial degree
  into the category of all simplicial opens.
* `Stacks.Topology.Simplicial.componentPresheaf`: the presheaf in one degree underlying a
  presheaf on all simplicial opens.
* `Stacks.Topology.Simplicial.componentPresheafFunctor`: that restriction, as a functor.

## Main results

* `Stacks.Topology.Simplicial.levelFunctor_isContinuous`: the inclusion is continuous.
* `Stacks.Topology.Simplicial.levelFunctor_isCocontinuous`: the inclusion is cocontinuous.
* `Stacks.Topology.Simplicial.levelFunctor_preservesPullbacks` and
  `levelFunctor_preservesEqualizers`: the inclusion preserves fibre products and equalizers.

## Implementation notes

Continuity and cocontinuity are stated for an arbitrary degree `n : SimplexCategoryᵒᵖ`; Stacks
09W0 states them for the degrees `op ⦋n⦌`, and those restatements are
`Stacks.Topology.Simplicial.levelFunctor_isContinuous_mk` and
`levelFunctor_isCocontinuous_mk` in
`StacksFrontier.Topology.Simplicial.ComponentSite`.

Existence of fibre products and equalizers in a category of open subsets comes from Mathlib's
limit instances for complete lattices. Preservation is expressed by the limit-shape classes for
cospans and for parallel pairs.

## References

* [Stacks Project, Tag 09VM](https://stacks.math.columbia.edu/tag/09VM)
* [Stacks Project, Tag 09W0](https://stacks.math.columbia.edu/tag/09W0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w

namespace Stacks.Topology.Simplicial

variable {X : SimplicialObject TopCat.{u}}
variable {A : Type w} [Category.{v} A]

/-- The inclusion of the category of opens in one simplicial degree into the category of all
simplicial opens. -/
def levelFunctor (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    Opens (X.obj n) ⥤ SimplicialOpen X where
  obj U := ⟨n, U⟩
  map f :=
    { base := 𝟙 n
      le := by simpa using leOfHom f }
  map_id U := by
    apply SimplicialOpen.Hom.ext
    rfl
  map_comp f g := by
    apply SimplicialOpen.Hom.ext
    change 𝟙 n = 𝟙 n ≫ 𝟙 n
    simp

/-- The presheaf in degree `n` underlying a presheaf on all simplicial opens. -/
abbrev componentPresheaf
    (P : (SimplicialOpen X)ᵒᵖ ⥤ A) (n : SimplexCategoryᵒᵖ) :
    (Opens (X.obj n))ᵒᵖ ⥤ A :=
  (levelFunctor X n).op ⋙ P

/-- Restriction of total presheaves to one simplicial degree. -/
def componentPresheafFunctor (X : SimplicialObject TopCat.{u})
    (A : Type w) [Category.{v} A] (n : SimplexCategoryᵒᵖ) :
    ((SimplicialOpen X)ᵒᵖ ⥤ A) ⥤ ((Opens (X.obj n))ᵒᵖ ⥤ A) where
  obj P := componentPresheaf P n
  map f := Functor.whiskerLeft (levelFunctor X n).op f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inclusion of one simplicial degree is continuous for the levelwise topology. -/
theorem levelFunctor_isContinuous (X : SimplicialObject TopCat.{u})
    (n : SimplexCategoryᵒᵖ) :
    (levelFunctor X n).IsContinuous
      (Opens.grothendieckTopology (X.obj n))
      (SimplicialOpen.grothendieckTopology X) := by
  let F := levelFunctor X n
  let J := (Opens.grothendieckTopology (X.obj n)).toPrecoverage
  let K := SimplicialOpen.precoverage X
  have hmem : J ≤ K.comap F := by
    intro U R hR
    change SimplicialOpen.IsCovering (F.obj U) (R.map F)
    constructor
    · intro V g hg
      cases hg with
      | of hf => exact ⟨rfl, by rfl⟩
    · intro x hx
      dsimp [F, levelFunctor] at x hx ⊢
      rw [GrothendieckTopology.mem_toPrecoverage_iff] at hR
      obtain ⟨V, f, hf, hxV⟩ :=
        (Opens.mem_grothendieckTopology (X.obj n)).mp hR x hx
      obtain ⟨W, h, g, hg, hcomp⟩ := hf
      refine ⟨F.obj W, F.map g, Presieve.map.of hg, x, h.le hxV, ?_⟩
      change (X.map (𝟙 n)).hom x = x
      simp
  have htop : J.toGrothendieck = Opens.grothendieckTopology (X.obj n) := by
    apply le_antisymm
    · exact GrothendieckTopology.toGrothendieck_toPrecoverage_le _
    · intro U S hS
      rw [← Sieve.generate_sieve S]
      apply Precoverage.generate_mem_toGrothendieck
      exact (GrothendieckTopology.arrows_mem_toPrecoverage_iff _ _).2 hS
  have hpres : J.PullbacksPreservedBy F := by
    constructor
    intro U R hR
    let : R.HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hR
    constructor
    intro V W f g hf hg
    cases (show (F.obj V).degree = (F.obj U).degree from rfl)
    cases (show (F.obj W).degree = (F.obj U).degree from rfl)
    let : (R.map F).HasPullbacks (F.map g) :=
      K.hasPullbacks_of_mem (F.map g) (hmem U hR)
    let : HasPullback (F.map f) (F.map g) :=
      Presieve.HasPullbacks.hasPullback (R := R.map F) (f := F.map g)
        (h := F.map f) (Presieve.map.of hf)
    constructor
    intro c hc
    let : HasPullback f g := Presieve.HasPairwisePullbacks.has_pullbacks hf hg
    let l : pullback f g ⟶ c.pt := hc.lift (pullback.cone f g)
    cases (show (F.obj (pullback f g)).degree = (F.obj V).degree from rfl)
    cases (show (F.obj c.pt).degree = (F.obj V).degree from rfl)
    have base_eq (s : PullbackCone (F.map f) (F.map g)) :
        s.fst.base = s.snd.base := by
      have h := congrArg SimplicialOpen.Hom.base s.condition
      change s.fst.base ≫ (F.map f).base = s.snd.base ≫ (F.map g).base at h
      apply Quiver.Hom.unop_inj
      simpa [F, levelFunctor, unop_comp, CategoryTheory.unop_id,
        CategoryTheory.Category.id_comp] using congrArg Quiver.Hom.unop h
    let q (s : PullbackCone (F.map f) (F.map g)) :
        s.pt ⟶ F.obj (pullback f g) := by
      refine ⟨s.fst.base, ?_⟩
      intro x hx
      have hx₁ : (X.map s.fst.base).hom x ∈ V := by
        exact (Opens.mem_map.mp (by
          simpa [F, levelFunctor] using SimplicialOpen.Hom.le s.fst hx))
      have hx₂ : (X.map s.fst.base).hom x ∈ W := by
        have hh := SimplicialOpen.Hom.le s.snd hx
        rw [← base_eq s] at hh
        exact (Opens.mem_map.mp (by
          simpa [F, levelFunctor] using hh))
      let ci : PullbackCone f g :=
        PullbackCone.mk (homOfLE inf_le_left) (homOfLE inf_le_right)
          (Subsingleton.elim _ _)
      let j : V ⊓ W ⟶ pullback f g := (pullback.isLimit f g).lift ci
      exact j.le ⟨hx₁, hx₂⟩
    have hlim : IsLimit (F.mapCone c) := by
      let cF : PullbackCone (F.map f) (F.map g) :=
        (Cone.postcompose (cospanCompIso F f g).hom).obj (F.mapCone c)
      have hlim' : IsLimit cF := by
        apply PullbackCone.isLimitAux cF (fun s => q s ≫ F.map l)
        · intro s
          apply SimplicialOpen.Hom.ext
          apply Quiver.Hom.unop_inj
          change (𝟙 (Opposite.unop ((F.obj V).degree)) ≫ s.fst.base.unop) = s.fst.base.unop
          exact CategoryTheory.Category.id_comp _
        · intro s
          apply SimplicialOpen.Hom.ext
          apply Quiver.Hom.unop_inj
          change (𝟙 (Opposite.unop ((F.obj V).degree)) ≫ s.fst.base.unop) = s.snd.base.unop
          rw [CategoryTheory.Category.id_comp]
          exact congrArg Quiver.Hom.unop (base_eq s)
        · intro s m hm
          apply SimplicialOpen.Hom.ext
          have hb := congrArg SimplicialOpen.Hom.base (hm WalkingCospan.left)
          apply Quiver.Hom.unop_inj
          have hb' : m.base.unop = s.fst.base.unop := by
            have h := congrArg Quiver.Hom.unop hb
            change (𝟙 (Opposite.unop ((F.obj c.pt).degree)) ≫ m.base.unop) = s.fst.base.unop at h
            simpa only [CategoryTheory.Category.id_comp] using h
          rw [hb']
          change s.fst.base.unop = (𝟙 (Opposite.unop ((F.obj V).degree)) ≫ s.fst.base.unop)
          exact (CategoryTheory.Category.id_comp _).symm
      exact (IsLimit.postcomposeHomEquiv (cospanCompIso F f g) (F.mapCone c)) hlim'
    exact ⟨hlim⟩
  let := hpres
  simpa [J, K, htop] using
    (Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy (F := F) J K hmem)

/-- The inclusion of one simplicial degree is cocontinuous for the levelwise topology. -/
theorem levelFunctor_isCocontinuous (X : SimplicialObject TopCat.{u})
    (n : SimplexCategoryᵒᵖ) :
    (levelFunctor X n).IsCocontinuous
      (Opens.grothendieckTopology (X.obj n))
      (SimplicialOpen.grothendieckTopology X) := by
  refine ⟨?_⟩
  intro U S hS
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  rw [SimplicialOpen.mem_grothendieckTopology] at hS
  obtain ⟨R, hR, hRS⟩ := hS
  obtain ⟨V, f, hRf, y, hy, hyx⟩ := hR.2 x hx
  cases V with
  | mk vdegree Vopen =>
    obtain ⟨e, hbase⟩ := hR.1 ⟨vdegree, Vopen⟩ f hRf
    change vdegree = ((levelFunctor X n).obj U).degree at e
    cases e
    dsimp [levelFunctor] at *
    change Opens (X.obj n) at Vopen
    change ({ degree := n, toOpens := Vopen } : SimplicialOpen X) ⟶
      ({ degree := n, toOpens := U } : SimplicialOpen X) at f
    change ↑(X.obj n) at y
    have hbase' : f.base = 𝟙 n := by
      rw [hbase]
      rfl
    have hle : Vopen ≤ U := by
      have hh := SimplicialOpen.Hom.le f
      change Vopen ≤ (Opens.map (X.map f.base)).obj U at hh
      simpa [hbase'] using hh
    refine ⟨Vopen, homOfLE hle, ?_, ?_⟩
    · change S ((levelFunctor X n).map (homOfLE hle))
      apply hRS
      have hf : f = (levelFunctor X n).map (homOfLE hle) := SimplicialOpen.Hom.ext _ _ hbase'
      simpa [hf, levelFunctor] using hRf
    · rw [show X.map f.base = 𝟙 (X.obj n) by simp [hbase']] at hyx
      obtain rfl : y = x := hyx
      exact hy

/-- The two legs of a pullback cone over a pair of maps in one simplicial degree have the same
underlying map of degrees. -/
private theorem levelFunctor_pullbackCone_fst_base_eq_snd_base {n : SimplexCategoryᵒᵖ}
    {U V W : Opens (X.obj n)} {f : U ⟶ W} {g : V ⟶ W}
    (s : PullbackCone ((levelFunctor X n).map f) ((levelFunctor X n).map g)) :
    s.fst.base = s.snd.base := by
  have h := congrArg SimplicialOpen.Hom.base s.condition
  change s.fst.base ≫ 𝟙 n = s.snd.base ≫ 𝟙 n at h
  exact (cancel_mono (𝟙 n)).1 h

private theorem levelFunctor_intersection_isPullback
    (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ)
    (U V W : Opens (X.obj n)) (f : U ⟶ W) (g : V ⟶ W) :
    IsPullback
      ((levelFunctor X n).map (homOfLE inf_le_left))
      ((levelFunctor X n).map (homOfLE inf_le_right))
      ((levelFunctor X n).map f)
      ((levelFunctor X n).map g) := by
  let F := levelFunctor X n
  let c : PullbackCone (F.map f) (F.map g) :=
    PullbackCone.mk (F.map (homOfLE inf_le_left)) (F.map (homOfLE inf_le_right)) (by
      apply SimplicialOpen.Hom.ext
      rfl)
  have hc : IsLimit c := by
    change IsLimit (PullbackCone.mk c.fst c.snd c.condition)
    refine PullbackCone.IsLimit.mk c.condition (fun s => ?_) ?_ ?_ ?_
    · let fstBase : s.pt.degree ⟶ n := s.fst.base
      let sndBase : s.pt.degree ⟶ n := s.snd.base
      have hbase : fstBase = sndBase := levelFunctor_pullbackCone_fst_base_eq_snd_base s
      refine ⟨fstBase, fun x hx => ?_⟩
      have h₁ := (SimplicialOpen.Hom.le s.fst) hx
      have h₂ := (SimplicialOpen.Hom.le s.snd) hx
      change x ∈ (Opens.map (X.map fstBase)).obj U at h₁
      change x ∈ (Opens.map (X.map sndBase)).obj V at h₂
      rw [← hbase] at h₂
      change x ∈ (Opens.map (X.map fstBase)).obj (U ⊓ V)
      exact ⟨by simpa [Opens.map_def] using h₁, by simpa [Opens.map_def] using h₂⟩
    · intro s
      dsimp [F, levelFunctor] at s
      apply SimplicialOpen.Hom.ext
      change s.fst.base ≫ 𝟙 n = s.fst.base
      exact Category.comp_id _
    · intro s
      dsimp [F, levelFunctor] at s
      apply SimplicialOpen.Hom.ext
      calc
        s.fst.base ≫ 𝟙 n = s.fst.base := Category.comp_id _
        _ = s.snd.base := levelFunctor_pullbackCone_fst_base_eq_snd_base (f := f) (g := g) s
    · intro s m hm₁ hm₂
      dsimp [F, levelFunctor] at s
      apply SimplicialOpen.Hom.ext
      have h := congrArg SimplicialOpen.Hom.base hm₁
      dsimp [F, levelFunctor] at h
      change m.base ≫ 𝟙 n = s.fst.base at h
      exact (Category.comp_id m.base).symm.trans h
  change IsPullback c.fst c.snd (F.map f) (F.map g)
  exact IsPullback.of_isLimit hc

/-- The inclusion of a simplicial degree preserves fibre products. -/
@[instance] theorem levelFunctor_preservesPullbacks
    (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    PreservesLimitsOfShape WalkingCospan (levelFunctor X n) := by
  refine Limits.preservesLimitsOfShape_walkingCospan_of_forall_isPullback ?_
  intro U V W f g _
  let c : PullbackCone f g := PullbackCone.mk (homOfLE inf_le_left) (homOfLE inf_le_right)
    (Subsingleton.elim _ _)
  have hcLim : IsLimit c := by
    change IsLimit (PullbackCone.mk c.fst c.snd c.condition)
    exact PullbackCone.IsLimit.mk c.condition
      (fun s => homOfLE (le_inf (leOfHom s.fst) (leOfHom s.snd)))
      (fun _ => Subsingleton.elim _ _) (fun _ => Subsingleton.elim _ _)
      (fun _ _ _ _ => Subsingleton.elim _ _)
  exact ⟨U ⊓ V, homOfLE inf_le_left, homOfLE inf_le_right, IsPullback.of_isLimit hcLim,
    levelFunctor_intersection_isPullback X n U V W f g⟩

/-- The inclusion of a simplicial degree preserves equalizers. -/
@[instance] theorem levelFunctor_preservesEqualizers
    (X : SimplicialObject TopCat.{u}) (n : SimplexCategoryᵒᵖ) :
    PreservesLimitsOfShape WalkingParallelPair (levelFunctor X n) := by
  let F := levelFunctor X n
  refine ⟨fun {K} => ?_⟩
  let f := K.map WalkingParallelPairHom.left
  have hfg : K.map WalkingParallelPairHom.right = f := Subsingleton.elim _ _
  have hcan : PreservesLimit (parallelPair f f) F := by
    apply preservesLimit_of_preserves_limit_cone
      (Fork.IsLimit.mk (Fork.ofι (𝟙 _) (by simp)) (fun s => s.ι)
        (by intro s; simp) (by intro s m hm; simpa using hm))
    exact (isLimitMapConeForkEquiv F (by simp)).symm
      (Fork.IsLimit.mk (Fork.ofι (𝟙 _) (by simp)) (fun s => s.ι)
        (by intro s; simp) (by intro s m hm; simpa using hm))
  have hK : K ≅ parallelPair f f := by
    simpa [f, hfg] using diagramIsoParallelPair K
  exact preservesLimit_of_iso_diagram F hK.symm

end Stacks.Topology.Simplicial

end
