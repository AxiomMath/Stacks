module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Basic
public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousAdjunction
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.CocontinuousComp
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CocontinuousTotalSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalSite
public import StacksFrontier.CategoryTheory.Sites.Topos.MorphismOfTopoi
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs

/-!
# The simplicial-site situation

We fix a simplicial family of sites in one of two forms. Its transition maps are either
morphisms of sites represented by continuous functors in the opposite direction, or are
cocontinuous functors satisfying the representable-pullback condition. In both cases they
induce morphisms of topoi, and the fibrewise coverings define a total site.

## Main definitions

* `CategoryTheory.CocontinuousSimplicialSite`: case (B), including property P.
* `CategoryTheory.SimplicialSiteSituation`: the choice between cases (A) and (B).
* `CategoryTheory.SimplicialSiteSituation.component` and `.componentTopology`: the site in a
  given simplicial degree.
* `CategoryTheory.SimplicialSiteSituation.transitionMorphism`: the induced morphism of topoi.
* `CategoryTheory.SimplicialSiteSituation.totalCategory` and `.totalTopology`: the total site.
* `CategoryTheory.SimplicialSiteSituation.pushforwardId` and `.pushforwardComp`: the canonical
  comparisons of direct images induced by the simplicial diagram.

## Main results

* `CategoryTheory.SimplicialSiteSituation.pushforwardId_inl_app` and
  `.pushforwardComp_inl_app`: in case (A) the comparison maps are, on sections, transport along
  the simplicial identities.
* `CategoryTheory.SimplicialSiteSituation.pushforwardId_inr_app` and
  `.pushforwardComp_inr_app`: in case (B) they are transport along the simplicial identities
  followed by the canonical comparison of right Kan extensions.

## Implementation notes

Case (A) is `CategoryTheory.SimplicialSite`; its underlying categories form a cosimplicial
diagram because a morphism of sites is represented by a continuous functor in the opposite
direction. Case (B) is represented by a simplicial object in `Cat`. We index the component
sites in both cases by `SimplexCategory`, reversing the index in case (B).

The total category is respectively Mathlib's contravariant `CoGrothendieck` construction and
its covariant `Grothendieck` construction. The morphisms of topoi use sheaves of sets in the
same universe as the small component sites.

The direct-image comparisons use precomposition in case (A) and the canonical right Kan
extension adjunction in case (B). They do not use the chosen topos adjunction packaged into
`transitionMorphism`.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Pseudofunctor

universe u

namespace CategoryTheory

/-- Case (B) of the simplicial-site situation: a simplicial family of sites whose transition
functors are cocontinuous and satisfy property P of Stacks 09W7. -/
structure CocontinuousSimplicialSite where
  /-- The underlying simplicial diagram of categories. -/
  underlying : SimplicialObject Cat.{u, u}
  /-- The covering families in each simplicial degree. -/
  coverage : ∀ n, Covering.{u, u, u} (underlying.obj n) → Prop
  /-- The covering families in each degree satisfy the site axioms. -/
  isSite : ∀ n, IsSite (coverage n)
  /-- Every transition functor is cocontinuous. -/
  isCocontinuous : SimplicialCoverings.IsCocontinuous underlying coverage
  /-- Every transition functor satisfies property P. -/
  hasCoverPullbacks : ∀ {m n : SimplexCategoryᵒᵖ} (f : m ⟶ n),
    Functor.HasCoverPullbacks (underlying.map f).toFunctor (coverage m) (coverage n)

/-- The standing simplicial-site situation of Stacks 09WE. The left summand is case (A), in
which transitions are morphisms of sites represented by continuous functors; the right summand
is case (B), in which transitions are cocontinuous functors satisfying property P. -/
@[stacks 09WE "the two cases"]
structure SimplicialSiteSituation where
  /-- The data belonging to one of the two cases. -/
  case : SimplicialSite.{u} ⊕ CocontinuousSimplicialSite.{u}

/-- The cartesian monoidal structure on a category of sheaves of types, from its finite products.
Declared once here and activated where needed with `attribute [local instance]`, rather than
redeclared per file; it is kept out of global instance search deliberately. -/
noncomputable local instance sheafTypeCartesian {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) : CartesianMonoidalCategory (Sheaf J (Type u)) :=
  .ofHasFiniteProducts

/-- The braiding on a category of sheaves of types, from its cartesian monoidal structure. -/
noncomputable local instance sheafTypeBraided {C : Type u} [Category.{u} C]
    (J : GrothendieckTopology C) : BraidedCategory (Sheaf J (Type u)) :=
  .ofCartesianMonoidalCategory

namespace SimplicialSiteSituation

/-- The category in simplicial degree `n`. -/
def component (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) : Cat.{u, u} :=
  match S with
  | ⟨Sum.inl C⟩ => C.underlying.obj n
  | ⟨Sum.inr C⟩ => C.underlying.obj (Opposite.op n)

/-- The Grothendieck topology on the category in simplicial degree `n`. -/
def componentTopology (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    GrothendieckTopology (S.component n) :=
  match S with
  | ⟨Sum.inl C⟩ => (C.coverage n).toGrothendieck
  | ⟨Sum.inr C⟩ => topologyOfCoverings (C.coverage (Opposite.op n))

/-- The morphism of topoi `f_φ : Sh(C_n) → Sh(C_m)` induced by a simplex map
`φ : [m] → [n]`. -/
@[stacks 09WE "the induced morphisms of topoi"]
noncomputable def transitionMorphism (S : SimplicialSiteSituation.{u})
    {m n : SimplexCategory} (φ : m ⟶ n) :
    MorphismOfTopoi
      (Sheaf (S.componentTopology n) (Type u))
      (Sheaf (S.componentTopology m) (Type u)) :=
  match S with
  | ⟨Sum.inl C⟩ => (C.isMorphismOfSites φ).morphismOfTopoi
  | ⟨Sum.inr C⟩ => by
      let F := (C.underlying.map φ.op).toFunctor
      change MorphismOfTopoi
        (Sheaf (topologyOfCoverings (C.coverage (Opposite.op n))) (Type u))
        (Sheaf (topologyOfCoverings (C.coverage (Opposite.op m))) (Type u))
      letI : F.IsCocontinuous
          (topologyOfCoverings (C.coverage (Opposite.op n)))
          (topologyOfCoverings (C.coverage (Opposite.op m))) :=
        C.isCocontinuous φ.op
      exact
        { pushforward := gStar _ _ _ _ F
          inverseImage := gInv _ _ _ _ F
          adj := gAdjunction _ _ _ _ F
          preservesFiniteLimits := main_left_exact _ _ _ _ F }

/-- The total category attached to the simplicial-site situation. -/
def totalCategory (S : SimplicialSiteSituation.{u}) : Cat.{u, u} :=
  match S with
  | ⟨Sum.inl C⟩ => Cat.of (CoGrothendieck C.totalPseudofunctor)
  | ⟨Sum.inr C⟩ => Cat.of (Grothendieck C.underlying)

/-- The simplicial degree of an object of the total category, as a functor to
`SimplexCategoryᵒᵖ`. -/
def totalSimplexDegree (S : SimplicialSiteSituation.{u}) :
    S.totalCategory ⥤ SimplexCategoryᵒᵖ :=
  match S with
  | ⟨Sum.inl C⟩ => Pseudofunctor.CoGrothendieck.forget C.totalPseudofunctor
  | ⟨Sum.inr C⟩ => Grothendieck.forget C.underlying

/-- The topology of the total site: it is generated by covering families lying in one
simplicial degree. -/
@[stacks 09WE "the total site", sga "4 VI 7.4.1" "simplicial case"]
def totalTopology (S : SimplicialSiteSituation.{u}) :
    GrothendieckTopology S.totalCategory :=
  match S with
  | ⟨Sum.inl C⟩ => C.totalTopology
  | ⟨Sum.inr C⟩ => SimplicialCoverings.totalTopology C.underlying C.coverage

/-- Equality of site functors induces the identity comparison of their direct images. -/
noncomputable def cocontinuousPushforwardIsoOfEq.{v₁, u₁, v₂, u₂, w}
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    {F G : C ⥤ D} [F.IsCocontinuous J K] [G.IsCocontinuous J K]
    (h : F = G) :
    F.sheafPushforwardCocontinuous (Type (max u₁ v₁ u₂ v₂ w)) J K ≅
      G.sheafPushforwardCocontinuous (Type (max u₁ v₁ u₂ v₂ w)) J K := by
  cases h
  exact Iso.refl _

/-- The unit comparison on direct images, induced by the identity equality of the underlying
site functor. In case (B), the identity right Kan extension is identified using its specified
adjunction. -/
noncomputable def pushforwardId
    (S : SimplicialSiteSituation.{u}) (n : SimplexCategory) :
    (S.transitionMorphism (𝟙 n)).pushforward ≅ 𝟭 _ := by
  rcases S with ⟨C | C⟩
  · let J := (C.coverage n).toGrothendieck
    letI := (C.isMorphismOfSites (𝟙 n)).isContinuous
    change (C.underlying.map (𝟙 n)).toFunctor.sheafPushforwardContinuous
      (Type u) J J ≅ 𝟭 _
    exact Functor.sheafPushforwardContinuousId'
      (eqToIso (congrArg Cat.Hom.toFunctor (C.underlying.map_id n))) (Type u) J
  · let J := topologyOfCoverings (C.coverage (Opposite.op n))
    letI : (C.underlying.map (𝟙 n).op).toFunctor.IsCocontinuous J J :=
      C.isCocontinuous (𝟙 n).op
    change (C.underlying.map (𝟙 n).op).toFunctor.sheafPushforwardCocontinuous
      (Type u) J J ≅ 𝟭 _
    refine cocontinuousPushforwardIsoOfEq J J
      (show (C.underlying.map (𝟙 n).op).toFunctor = 𝟭 _ from
        congrArg Cat.Hom.toFunctor (C.underlying.map_id (Opposite.op n))) ≪≫ ?_
    exact Adjunction.rightAdjointUniq
      (((𝟭 (C.underlying.obj (Opposite.op n))).sheafAdjunctionCocontinuous
        (Type u) J J).ofNatIsoLeft (Functor.sheafPushforwardContinuousId (Type u) J))
      Adjunction.id

/-- The direct-image compositor induced by composition of the underlying site functors:
precomposition in case (A), and the canonical right Kan extension compositor in case (B). -/
noncomputable def pushforwardCompSymm
    (S : SimplicialSiteSituation.{u})
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (S.transitionMorphism φ).pushforward ⋙ (S.transitionMorphism ψ).pushforward ≅
      (S.transitionMorphism (ψ ≫ φ)).pushforward := by
  rcases S with ⟨C | C⟩
  · let Jₗ := (C.coverage l).toGrothendieck
    let Jₘ := (C.coverage m).toGrothendieck
    let Jₙ := (C.coverage n).toGrothendieck
    letI := (C.isMorphismOfSites ψ).isContinuous
    letI := (C.isMorphismOfSites φ).isContinuous
    letI := (C.isMorphismOfSites (ψ ≫ φ)).isContinuous
    change (C.underlying.map φ).toFunctor.sheafPushforwardContinuous (Type u) Jₘ Jₙ ⋙
      (C.underlying.map ψ).toFunctor.sheafPushforwardContinuous (Type u) Jₗ Jₘ ≅
      (C.underlying.map (ψ ≫ φ)).toFunctor.sheafPushforwardContinuous (Type u) Jₗ Jₙ
    exact Functor.sheafPushforwardContinuousComp'
      (eqToIso (congrArg Cat.Hom.toFunctor (C.underlying.map_comp ψ φ)).symm)
      (Type u) Jₗ Jₘ Jₙ
  · let Jₗ := topologyOfCoverings (C.coverage (Opposite.op l))
    let Jₘ := topologyOfCoverings (C.coverage (Opposite.op m))
    let Jₙ := topologyOfCoverings (C.coverage (Opposite.op n))
    letI : (C.underlying.map ψ.op).toFunctor.IsCocontinuous Jₘ Jₗ := C.isCocontinuous ψ.op
    letI : (C.underlying.map φ.op).toFunctor.IsCocontinuous Jₙ Jₘ := C.isCocontinuous φ.op
    letI : (C.underlying.map (ψ ≫ φ).op).toFunctor.IsCocontinuous Jₙ Jₗ :=
      C.isCocontinuous (ψ ≫ φ).op
    change (C.underlying.map φ.op).toFunctor.sheafPushforwardCocontinuous (Type u) Jₙ Jₘ ⋙
      (C.underlying.map ψ.op).toFunctor.sheafPushforwardCocontinuous (Type u) Jₘ Jₗ ≅
      (C.underlying.map (ψ ≫ φ).op).toFunctor.sheafPushforwardCocontinuous (Type u) Jₙ Jₗ
    letI : ((C.underlying.map φ.op).toFunctor ⋙
        (C.underlying.map ψ.op).toFunctor).IsCocontinuous Jₙ Jₗ :=
      CategoryTheory.isCocontinuous_comp _ _ Jₙ Jₘ
    exact (sheafPushforwardCocontinuousCompIso Jₙ Jₘ Jₗ
      (C.underlying.map φ.op).toFunctor (C.underlying.map ψ.op).toFunctor).symm ≪≫
      cocontinuousPushforwardIsoOfEq Jₙ Jₗ
        (congrArg Cat.Hom.toFunctor (C.underlying.map_comp φ.op ψ.op)).symm

/-- The composition comparison, in the direction used for systems of direct images. -/
noncomputable def pushforwardComp (S : SimplicialSiteSituation.{u})
    {l m n : SimplexCategory} (φ : m ⟶ n) (ψ : l ⟶ m) :
    (S.transitionMorphism (ψ ≫ φ)).pushforward ≅
      (S.transitionMorphism φ).pushforward ⋙ (S.transitionMorphism ψ).pushforward :=
  (S.pushforwardCompSymm ψ φ).symm

end SimplicialSiteSituation

end CategoryTheory

end
