module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousComp
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Situation

/-!
# Morphisms between simplicial sites

A morphism between two simplicial sites is given degreewise. In the continuous case its components
are morphisms of sites and their contravariantly representing functors commute with the
cosimplicial transition functors. In the cocontinuous case its components are cocontinuous functors
commuting with the simplicial transition functors. Such a morphism commutes with the transition
morphisms of topoi.

## Main definitions

* `CategoryTheory.SimplicialSite.Morphism`: a morphism between simplicial sites in case (A).
* `CategoryTheory.CocontinuousSimplicialSite.Morphism`: the same in case (B).
* `CategoryTheory.SimplicialSiteMorphism`: a morphism between two simplicial-site situations in the
  same case.
* `CategoryTheory.SimplicialSiteMorphism.componentMorphism`: its induced morphism of topoi in each
  simplicial degree.

## Main results

* `CategoryTheory.SimplicialSiteMorphism.transitionPushforwardIso`: the comparison between the two
  composites around each simplicial transition square.

## Implementation notes

The strict commutativity required in the source is expressed by a natural transformation between
the underlying diagrams in `Cat`. Its direction is reversed in case (A), since a morphism of sites
is represented by a functor in the opposite direction. A case (A) component preserves covering
families and pullbacks of covering arrows, in addition to inducing a morphism for the generated
Grothendieck topologies; these covering-level conditions are needed even when two different
covering-family structures generate the same topology. The two constructors of
`SimplicialSiteMorphism` ensure that source and target use the same one of cases (A) and (B).

The source writes equality of morphisms of topoi. Since composition of the associated sheaf
functors is only canonical up to isomorphism, the square is expressed by an isomorphism of
direct-image functors. Such an isomorphism also determines the corresponding comparison of
inverse-image functors by uniqueness of left adjoints.

## References

* [Stacks Project, Tag 0D95](https://stacks.math.columbia.edu/tag/0D95)
-/

@[expose] public section

open CategoryTheory

universe u

namespace CategoryTheory

/-- A morphism between two simplicial sites in case (A). The natural transformation points in the
opposite direction because its components represent morphisms of sites. -/
structure SimplicialSite.Morphism (C C' : SimplicialSite.{u}) where
  /-- The functors representing the degreewise morphisms of sites, together with their strict
  compatibility with all transition functors. -/
  hom : C'.underlying ⟶ C.underlying
  /-- Every component represents a morphism of the corresponding sites. -/
  isMorphismOfSites : ∀ n, (hom.app n).toFunctor.IsMorphismOfSites
    ((C'.coverage n).toGrothendieck) ((C.coverage n).toGrothendieck)
  /-- Each component takes covering families in the target site to covering families in the source
  site, as required of the functor representing a morphism of sites. -/
  coverPreserving : ∀ n, C'.coverage n ≤ (C.coverage n).comap (hom.app n).toFunctor
  /-- Each component preserves pullbacks along arrows in a covering family. -/
  preservesPullbacks : ∀ n {V : C'.underlying.obj n} {R : Presieve V}, R ∈ C'.coverage n V →
    ∀ {W : C'.underlying.obj n} {g : W ⟶ V}, R g →
      ∀ {T : C'.underlying.obj n} (f : T ⟶ V),
        CategoryTheory.Limits.PreservesLimit (CategoryTheory.Limits.cospan f g)
          (hom.app n).toFunctor

/-- A morphism between two simplicial sites in case (B). -/
structure CocontinuousSimplicialSite.Morphism
    (C C' : CocontinuousSimplicialSite.{u}) where
  /-- The degreewise functors, together with their strict compatibility with all transition
  functors. -/
  hom : C.underlying ⟶ C'.underlying
  /-- Every component is cocontinuous for the corresponding site topologies. -/
  isCocontinuous : ∀ n, (hom.app n).toFunctor.IsCocontinuous
    (topologyOfCoverings (C.coverage n)) (topologyOfCoverings (C'.coverage n))

/-- **Stacks 0D95.** A morphism between simplicial sites: degreewise morphisms of sites commuting
with the transitions in case (A), or degreewise cocontinuous functors commuting with the
transitions in case (B). -/
@[stacks 0D95 "morphism_between_simplicial_sites"]
inductive SimplicialSiteMorphism :
    SimplicialSiteSituation.{u} → SimplicialSiteSituation.{u} → Type (u + 1) where
  /-- A morphism between two situations of case (A). -/
  | ofMorphismOfSites {C C' : SimplicialSite.{u}} (h : SimplicialSite.Morphism C C') :
      SimplicialSiteMorphism ⟨Sum.inl C⟩ ⟨Sum.inl C'⟩
  /-- A morphism between two situations of case (B). -/
  | ofCocontinuous {C C' : CocontinuousSimplicialSite.{u}}
      (h : CocontinuousSimplicialSite.Morphism C C') :
      SimplicialSiteMorphism ⟨Sum.inr C⟩ ⟨Sum.inr C'⟩

namespace SimplicialSiteMorphism

/-- The morphism of topoi induced by a morphism between simplicial sites in degree `n`. -/
noncomputable def componentMorphism {S S' : SimplicialSiteSituation.{u}}
    (h : SimplicialSiteMorphism S S') (n : SimplexCategory) :
    MorphismOfTopoi (Sheaf (S.componentTopology n) (Type u))
      (Sheaf (S'.componentTopology n) (Type u)) :=
  match h with
  | .ofMorphismOfSites h => (h.isMorphismOfSites n).morphismOfTopoi
  | @ofCocontinuous C C' h => by
      let F := (h.hom.app (Opposite.op n)).toFunctor
      change MorphismOfTopoi
        (Sheaf (topologyOfCoverings (C.coverage (Opposite.op n))) (Type u))
        (Sheaf (topologyOfCoverings (C'.coverage (Opposite.op n))) (Type u))
      letI : F.IsCocontinuous (topologyOfCoverings (C.coverage (Opposite.op n)))
          (topologyOfCoverings (C'.coverage (Opposite.op n))) := h.isCocontinuous _
      exact
        { pushforward := gStar _ _ _ _ F
          inverseImage := gInv _ _ _ _ F
          adj := Classical.choice (main_adjunction00XO _ _ _ _ F)
          preservesFiniteLimits := main_left_exact _ _ _ _ F }

/-- **Stacks 0D95.** The component morphisms of a morphism between simplicial sites commute, up to
the canonical comparison, with every simplicial transition morphism of topoi. -/
@[stacks 0D95]
noncomputable def transitionPushforwardIso
    {S S' : SimplicialSiteSituation.{u}}
    (h : SimplicialSiteMorphism S S')
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (h.componentMorphism n).pushforward ⋙ (S'.transitionMorphism φ).pushforward ≅
      (S.transitionMorphism φ).pushforward ⋙ (h.componentMorphism m).pushforward := by
  cases h with
  | @ofMorphismOfSites C C' h =>
      let F₁ := (C'.underlying.map φ).toFunctor
      let G₁ := (h.hom.app n).toFunctor
      let H₁ := (h.hom.app m).toFunctor
      let F₂ := (C.underlying.map φ).toFunctor
      let J₀ := (C'.coverage m).toGrothendieck
      let J₁ := (C'.coverage n).toGrothendieck
      let K₀ := (C.coverage m).toGrothendieck
      let K₁ := (C.coverage n).toGrothendieck
      letI : F₁.IsContinuous J₀ J₁ := (C'.isMorphismOfSites φ).isContinuous
      letI : G₁.IsContinuous J₁ K₁ := (h.isMorphismOfSites n).isContinuous
      letI : H₁.IsContinuous J₀ K₀ := (h.isMorphismOfSites m).isContinuous
      letI : F₂.IsContinuous K₀ K₁ := (C.isMorphismOfSites φ).isContinuous
      letI : (F₁ ⋙ G₁).IsContinuous J₀ K₁ := Functor.isContinuous_comp F₁ G₁ J₀ J₁ K₁
      letI : (H₁ ⋙ F₂).IsContinuous J₀ K₁ := Functor.isContinuous_comp H₁ F₂ J₀ K₀ K₁
      change
        G₁.sheafPushforwardContinuous (Type u) J₁ K₁ ⋙
            F₁.sheafPushforwardContinuous (Type u) J₀ J₁ ≅
          F₂.sheafPushforwardContinuous (Type u) K₀ K₁ ⋙
            H₁.sheafPushforwardContinuous (Type u) J₀ K₀
      have hcomp : F₁ ⋙ G₁ = H₁ ⋙ F₂ :=
        congrArg (fun f => f.toFunctor) (h.hom.naturality φ)
      exact Functor.sheafPushforwardContinuousComp' (F := F₁) (G := G₁) (FG := F₁ ⋙ G₁)
          (eFG := Iso.refl _) (A := Type u) J₀ J₁ K₁ ≪≫
        Functor.sheafPushforwardContinuousIso (e := eqToIso hcomp) (A := Type u) J₀ K₁ ≪≫
        (Functor.sheafPushforwardContinuousComp' (F := H₁) (G := F₂) (FG := H₁ ⋙ F₂)
          (eFG := Iso.refl _) (A := Type u) J₀ K₀ K₁).symm
  | @ofCocontinuous C C' h =>
      let U₁ := (h.hom.app (Opposite.op n)).toFunctor
      let V₁ := (C'.underlying.map φ.op).toFunctor
      let U₂ := (C.underlying.map φ.op).toFunctor
      let V₂ := (h.hom.app (Opposite.op m)).toFunctor
      let J₀ := topologyOfCoverings (C.coverage (Opposite.op n))
      let J₁ := topologyOfCoverings (C'.coverage (Opposite.op n))
      let K₀ := topologyOfCoverings (C.coverage (Opposite.op m))
      let K₁ := topologyOfCoverings (C'.coverage (Opposite.op m))
      letI : U₁.IsCocontinuous J₀ J₁ := h.isCocontinuous (Opposite.op n)
      letI : V₁.IsCocontinuous J₁ K₁ := C'.isCocontinuous φ.op
      letI : U₂.IsCocontinuous J₀ K₀ := C.isCocontinuous φ.op
      letI : V₂.IsCocontinuous K₀ K₁ := h.isCocontinuous (Opposite.op m)
      letI : (U₁ ⋙ V₁).IsCocontinuous J₀ K₁ := isCocontinuous_comp U₁ V₁ J₀ J₁ (L := K₁)
      letI : (U₂ ⋙ V₂).IsCocontinuous J₀ K₁ := isCocontinuous_comp U₂ V₂ J₀ K₀ (L := K₁)
      have hcomp : U₁ ⋙ V₁ = U₂ ⋙ V₂ :=
        (congrArg (fun f => f.toFunctor) (h.hom.naturality φ.op)).symm
      exact (_root_.sheafPushforwardCocontinuousCompIso J₀ J₁ K₁ U₁ V₁).symm ≪≫
        SimplicialSiteSituation.cocontinuousPushforwardIsoOfEq J₀ K₁ hcomp ≪≫
        _root_.sheafPushforwardCocontinuousCompIso J₀ K₀ K₁ U₂ V₂

end SimplicialSiteMorphism

end CategoryTheory

end
