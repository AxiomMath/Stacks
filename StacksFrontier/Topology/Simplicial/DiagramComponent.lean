module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Spaces
public import StacksFrontier.Topology.Simplicial.DiagramSite

/-!
# The inclusion of one index into the total site of a diagram of spaces

For a diagram of topological spaces `X` indexed by a category `A` and an index `a`, the open
subsets of the space `X_a` form the degree-`a` part of the total site of `X`. This file builds the
resulting inclusion functor and shows that it is a continuous and a cocontinuous morphism of
sites, generalizing `Stacks.Topology.Simplicial.levelFunctor_isContinuous` and
`levelFunctor_isCocontinuous` from a simplicial space to an arbitrary diagram.

The generalization is what the *slice* of a total site needs: the slice at an object `(n, W)` is
the total site of the diagram over `(n, W)`, indexed by `A/n`, and its degree-`φ` component
functor for `φ : m ⟶ n` is the inclusion of the opens of `(X φ)⁻¹W` built here.

## Main definitions

* `Stacks.Topology.Simplicial.DiagramOpen.levelFunctor`: the inclusion of the opens at one index
  into the total site.
* `Stacks.Topology.Simplicial.DiagramOpen.componentPresheaf` and `.componentPresheafFunctor`:
  the presheaf at one index underlying a presheaf on the total site, and that restriction as a
  functor.

## Main results

* `Stacks.Topology.Simplicial.DiagramOpen.levelFunctor_isContinuous`: the inclusion is
  continuous.
* `Stacks.Topology.Simplicial.DiagramOpen.levelFunctor_isCocontinuous`: the inclusion is
  cocontinuous.

## Implementation notes

Continuity is Mathlib's `CategoryTheory.Functor.IsContinuous`, obtained from
`CategoryTheory.Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy`: the inclusion
carries open coverings to levelwise open coverings, and it carries the pullbacks of a covering
family — intersections of opens — to pullbacks in the total site. Cocontinuity is the lifting of
covering sieves, and holds because a levelwise open covering of an object at index `a` is already
an open covering inside that index.

The proofs are those of the simplicial case with the manipulations of arrows in
`SimplexCategoryᵒᵖ` replaced by manipulations of arrows in `A`. Where the simplicial proofs
cancel an identity by passing to `unop`, the general proofs cancel it in `A` directly, which is
shorter: composition in `SimplexCategoryᵒᵖ` is associative and unital on the nose, and in a
general category it is not, so associativity has to be used explicitly instead of being hidden
in `rfl`.

## References

* [Stacks Project, Tag 09VM](https://stacks.math.columbia.edu/tag/09VM)
* [Stacks Project, Tag 09W0](https://stacks.math.columbia.edu/tag/09W0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w v₁ u₁

namespace Stacks.Topology.Simplicial.DiagramOpen

variable {A : Type u₁} [Category.{v₁} A] {X : A ⥤ TopCat.{u}}
variable {B : Type w} [Category.{v} B]

/-- The inclusion of the category of opens at one index into the total site of a diagram of
spaces. -/
def levelFunctor (X : A ⥤ TopCat.{u}) (a : A) : Opens (X.obj a) ⥤ DiagramOpen X where
  obj V := ⟨a, V⟩
  map f :=
    { base := 𝟙 a
      le := by simpa using leOfHom f }
  map_id V := Hom.ext _ _ rfl
  map_comp f g := Hom.ext _ _ (Category.id_comp _).symm

/-- The level functor at `a` sends an open `V` of `X.obj a` to the pair `⟨a, V⟩`. -/
@[simp]
theorem levelFunctor_obj (a : A) (V : Opens (X.obj a)) :
    (levelFunctor X a).obj V = ⟨a, V⟩ := rfl

/-- The image under the level functor at `a` of an inclusion of opens has base the identity of
`a`. -/
@[simp]
theorem levelFunctor_map_base {a : A} {V W : Opens (X.obj a)} (f : V ⟶ W) :
    ((levelFunctor X a).map f).base = 𝟙 a := rfl

/-- The presheaf at one index underlying a presheaf on the total site. -/
abbrev componentPresheaf (P : (DiagramOpen X)ᵒᵖ ⥤ B) (a : A) : (Opens (X.obj a))ᵒᵖ ⥤ B :=
  (levelFunctor X a).op ⋙ P

/-- Restriction of presheaves on the total site to one index. -/
def componentPresheafFunctor (X : A ⥤ TopCat.{u}) (B : Type w) [Category.{v} B] (a : A) :
    ((DiagramOpen X)ᵒᵖ ⥤ B) ⥤ ((Opens (X.obj a))ᵒᵖ ⥤ B) where
  obj P := componentPresheaf P a
  map f := Functor.whiskerLeft (levelFunctor X a).op f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inclusion of one index is continuous for the levelwise topology. -/
instance levelFunctor_isContinuous [IsoRigid A] (X : A ⥤ TopCat.{u}) (a : A) :
    (levelFunctor X a).IsContinuous (Opens.grothendieckTopology (X.obj a))
      (grothendieckTopology X) := by
  let F := levelFunctor X a
  let J := (Opens.grothendieckTopology (X.obj a)).toPrecoverage
  let K := precoverage X
  have hmem : J ≤ K.comap F := by
    intro V R hR
    change IsCovering (F.obj V) (R.map F)
    constructor
    · intro W g hg
      cases hg with
      | of hf => exact ⟨rfl, rfl⟩
    · intro x hx
      dsimp [F, levelFunctor] at x hx ⊢
      rw [GrothendieckTopology.mem_toPrecoverage_iff] at hR
      obtain ⟨V₀, f, hf, hxV⟩ := (Opens.mem_grothendieckTopology (X.obj a)).mp hR x hx
      obtain ⟨W, h, g, hg, hcomp⟩ := hf
      refine ⟨F.obj W, F.map g, Presieve.map.of hg, x, h.le hxV, ?_⟩
      change (X.map (𝟙 a)) x = x
      exact ConcreteCategory.congr_hom (X.map_id a) x
  have htop : J.toGrothendieck = Opens.grothendieckTopology (X.obj a) := by
    apply le_antisymm
    · exact GrothendieckTopology.toGrothendieck_toPrecoverage_le _
    · intro V S hS
      rw [← Sieve.generate_sieve S]
      apply Precoverage.generate_mem_toGrothendieck
      exact (GrothendieckTopology.arrows_mem_toPrecoverage_iff _ _).2 hS
  have hpres : J.PullbacksPreservedBy F := by
    constructor
    intro V R hR
    let : R.HasPairwisePullbacks := J.hasPairwisePullbacks_of_mem hR
    constructor
    intro W Z f g hf hg
    let : (R.map F).HasPullbacks (F.map g) := K.hasPullbacks_of_mem (F.map g) (hmem V hR)
    let : HasPullback (F.map f) (F.map g) :=
      Presieve.HasPullbacks.hasPullback (R := R.map F) (f := F.map g) (h := F.map f)
        (Presieve.map.of hf)
    constructor
    intro c hc
    let : HasPullback f g := Presieve.HasPairwisePullbacks.has_pullbacks hf hg
    let l : pullback f g ⟶ c.pt := hc.lift (pullback.cone f g)
    have base_eq (s : PullbackCone (F.map f) (F.map g)) : s.fst.base = s.snd.base := by
      have h := congrArg Hom.base s.condition
      change s.fst.base ≫ 𝟙 a = s.snd.base ≫ 𝟙 a at h
      exact (Category.comp_id _).symm.trans (h.trans (Category.comp_id _))
    let q (s : PullbackCone (F.map f) (F.map g)) : s.pt ⟶ F.obj (pullback f g) := by
      refine ⟨s.fst.base, ?_⟩
      intro x hx
      have hx₁ : (X.map s.fst.base) x ∈ W := by
        exact (Opens.mem_map.mp (by simpa [F, levelFunctor] using Hom.le s.fst hx))
      have hx₂ : (X.map s.fst.base) x ∈ Z := by
        have hh := Hom.le s.snd hx
        rw [← base_eq s] at hh
        exact (Opens.mem_map.mp (by simpa [F, levelFunctor] using hh))
      let ci : PullbackCone f g :=
        PullbackCone.mk (homOfLE inf_le_left) (homOfLE inf_le_right) (Subsingleton.elim _ _)
      let j : W ⊓ Z ⟶ pullback f g := (pullback.isLimit f g).lift ci
      exact j.le ⟨hx₁, hx₂⟩
    have hlim : IsLimit (F.mapCone c) := by
      let cF : PullbackCone (F.map f) (F.map g) :=
        (Cone.postcompose (cospanCompIso F f g).hom).obj (F.mapCone c)
      have hlim' : IsLimit cF := by
        apply PullbackCone.isLimitAux cF (fun s => q s ≫ F.map l)
        · intro s
          have e : Hom.base ((q s ≫ F.map l) ≫ cF.fst) =
              (s.fst.base ≫ 𝟙 a) ≫ (𝟙 a ≫ 𝟙 a) := rfl
          refine Hom.ext _ _ (e.trans ?_)
          refine (congrArg (fun t => (s.fst.base ≫ 𝟙 a) ≫ t) (Category.id_comp (𝟙 a))).trans ?_
          exact (Category.comp_id _).trans (Category.comp_id _)
        · intro s
          have e : Hom.base ((q s ≫ F.map l) ≫ cF.snd) =
              (s.fst.base ≫ 𝟙 a) ≫ (𝟙 a ≫ 𝟙 a) := rfl
          refine Hom.ext _ _ (e.trans ?_)
          refine (congrArg (fun t => (s.fst.base ≫ 𝟙 a) ≫ t) (Category.id_comp (𝟙 a))).trans ?_
          exact ((Category.comp_id _).trans (Category.comp_id _)).trans (base_eq s)
        · intro s m hm
          have hb := congrArg Hom.base (hm WalkingCospan.left)
          have e3 : Hom.base (m ≫ cF.π.app WalkingCospan.left) =
              m.base ≫ (𝟙 a ≫ 𝟙 a) := rfl
          rw [e3] at hb
          have hb' : m.base = s.fst.base :=
            ((congrArg (fun t => m.base ≫ t) (Category.id_comp (𝟙 a))).trans
              (Category.comp_id _)).symm.trans hb
          exact Hom.ext _ _ (hb'.trans (Category.comp_id _).symm)
      exact (IsLimit.postcomposeHomEquiv (cospanCompIso F f g) (F.mapCone c)) hlim'
    exact ⟨hlim⟩
  let := hpres
  simpa [J, K, htop] using
    (Functor.isContinuous_toGrothendieck_of_pullbacksPreservedBy (F := F) J K hmem)

/-- The inclusion of one index is cocontinuous for the levelwise topology. -/
instance levelFunctor_isCocontinuous [IsoRigid A] (X : A ⥤ TopCat.{u}) (a : A) :
    (levelFunctor X a).IsCocontinuous (Opens.grothendieckTopology (X.obj a))
      (grothendieckTopology X) := by
  refine ⟨?_⟩
  intro V S hS
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  rw [mem_grothendieckTopology_iff] at hS
  obtain ⟨V₀, hV₀, hSf, hxV₀⟩ := hS x hx
  refine ⟨V₀, homOfLE hV₀, ?_, hxV₀⟩
  have hf : levelHom ((levelFunctor X a).obj V) hV₀ = (levelFunctor X a).map (homOfLE hV₀) :=
    Hom.ext _ _ rfl
  rw [hf] at hSf
  exact hSf

end Stacks.Topology.Simplicial.DiagramOpen

end
