module

public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSliceSite
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismProperty
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationMorphism
import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits

/-!
# The small étale site of an augmented simplicial algebraic space (Section 0DE7)

Let `S` be a scheme and `a : U → X` an augmented simplicial algebraic space over `S`.
Section 0DE7 of the Stacks project forms the simplicial object in sites
`n ↦ U_{n, spaces, étale}` with the base-change morphisms of sites of Stacks 03G2, takes its
total site `U_{spaces, étale}` (Stacks 09WC), the *small étale site of `U`*, and observes
that the augmentation gives a morphism of topoi `a : Sh(U_étale) → Sh(X_étale)` (Stacks 0D70).
This file builds these objects, using the strict model of the components of
`StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleComponents`.

## Main definitions

* `AlgebraicGeometry.Space.EtaleComponent.precoverage`: the coverings of the component in
  degree `n`, the families whose realizations are jointly surjective on points, exactly as in
  `U_{n, spaces, étale}` (Stacks 03G0).
* `AlgebraicGeometry.Space.etaleSimplicialSite`: the simplicial site `n ↦ U_{n, spaces, étale}`.
* `AlgebraicGeometry.Space.etaleAugmentation`: the augmentation towards `X_{spaces, étale}`,
  given by base change along `a_0 : U_0 → X`.
* `AlgebraicGeometry.Space.etaleAugmentationMorphism`: the morphism of topoi
  `a : Sh(U_étale) → Sh(X_étale)` of Section 0DE7.
* `AlgebraicGeometry.Space.fppfSurjective` and `AlgebraicGeometry.Space.IsFppfHypercovering`:
  flat, locally of finite presentation and surjective morphisms, and the fppf hypercoverings of
  Section 0DH4 defined by them.

## Main results

* `AlgebraicGeometry.Space.EtaleComponent.transition_isMorphismOfSites`: every transition is a
  morphism of sites.
* `AlgebraicGeometry.Space.EtaleComponent.transitionRealizeIso`: the transition along `ψ`,
  followed by realization, is realization followed by base change along `U(ψ)`.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 0DH4](https://stacks.math.columbia.edu/tag/0DH4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Coverings carried along cartesian squares -/

/-- If a functor `G` is related to functors `F, F'` into spaces-étale sites by cartesian squares
`F'(G g) → F g` over every arrow `g`, then `G` carries the coverings pulled back along `F` to the
coverings pulled back along `F'`: a point of the target lifts through the cartesian square. -/
theorem map_mem_comap_precoverage_of_isPullback {C C' : Type*} [Category C] [Category C']
    {T T' : AlgebraicSpaces B S hS} (F : C ⥤ SpacesEtale B S hS T) (G : C ⥤ C')
    (F' : C' ⥤ SpacesEtale B S hS T')
    (q : ∀ c, (F'.obj (G.obj c)).obj.left ⟶ (F.obj c).obj.left)
    (hq : ∀ {c d : C} (g : c ⟶ d),
      IsPullback (F'.map (G.map g)).hom.left (q c) (q d) (F.map g).hom.left)
    {W : C} {R : Presieve W} (hR : R ∈ (SpacesEtale.precoverage B S hS T).comap F W) :
    R.map G ∈ (SpacesEtale.precoverage B S hS T').comap F' (G.obj W) := by
  rw [Precoverage.mem_comap_iff, SpacesEtale.map_mem_precoverage_iff] at hR ⊢
  intro x
  obtain ⟨Z, g, hg, y, hy⟩ := hR (pointsMap B S hS _ (q W).hom x)
  obtain ⟨w, hw, -⟩ := exists_point_of_isPullback B S hS (hq g) x y hy.symm
  exact ⟨G.obj Z, G.map g, Presieve.map_map hg, w, hw⟩

/-- The square relating a base change of a morphism to the morphism, through the cartesian
projections, is cartesian. -/
theorem isPullback_spacesBaseChange_map {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {V W : SpacesEtale B S hS Y} (g : V ⟶ W) :
    IsPullback ((spacesBaseChange B S hS f).functor.map g).hom.left
      ((spacesBaseChange B S hS f).projection.app V)
      ((spacesBaseChange B S hS f).projection.app W) g.hom.left := by
  refine IsPullback.of_right ?_ ((spacesBaseChange B S hS f).projection.naturality g)
    ((spacesBaseChange B S hS f).isPullback W).flip
  rw [Over.w ((spacesBaseChange B S hS f).functor.map g).hom, Over.w g.hom]
  exact ((spacesBaseChange B S hS f).isPullback V).flip

variable (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

namespace EtaleComponent

variable {A}

/-- The component of degree `n` has pullbacks, since it is equivalent to `U_{n, spaces, étale}`
through realization. -/
instance (n : SimplexCategory) : HasPullbacks (EtaleComponent A n) :=
  Adjunction.hasLimitsOfShape_of_equivalence (realizeFunctor n)

/-- **Section 0DE7, the coverings of the components.** A family in the component of degree `n`
covers when its realizations are jointly surjective on points, as in Stacks 03G0. -/
def precoverage (n : SimplexCategory) : Precoverage (EtaleComponent A n) :=
  (SpacesEtale.precoverage B S hS (A.left.obj (op n))).comap (realizeFunctor n)

/-- Every isomorphism is a covering of the component of degree `n`. -/
instance (n : SimplexCategory) : (precoverage (A := A) n).HasIsos :=
  inferInstanceAs ((SpacesEtale.precoverage B S hS _).comap _).HasIsos

/-- The coverings of the component of degree `n` are stable under composition. -/
instance (n : SimplexCategory) : (precoverage (A := A) n).IsStableUnderComposition :=
  inferInstanceAs ((SpacesEtale.precoverage B S hS _).comap _).IsStableUnderComposition

/-- The coverings of the component of degree `n` are stable under base change. -/
instance (n : SimplexCategory) : (precoverage (A := A) n).IsStableUnderBaseChange :=
  inferInstanceAs ((SpacesEtale.precoverage B S hS _).comap _).IsStableUnderBaseChange

/-- The component at `x` of `transitionRealizeIso`: both objects are fibre products of the
realization of `x` along `U(ψ)`. -/
def transitionRealizeIsoApp {n k : SimplexCategory} (ψ : n ⟶ k) (x : EtaleComponent A n) :
    (realizeFunctor k).obj ((transition ψ).obj x) ≅
      (spacesBaseChange B S hS (A.left.map ψ.op)).functor.obj ((realizeFunctor n).obj x) :=
  (IsEtaleOver B S hS _).isoMk (Over.isoMk
    ((isPullback_comparison ψ x).isoIsPullback _ _
      ((spacesBaseChange B S hS (A.left.map ψ.op)).isPullback (realize x)))
    (IsPullback.isoIsPullback_hom_snd _ _ _ _))

/-- The component `transitionRealizeIsoApp ψ x`, followed by the projection of the base change
along `U(ψ)`, is the comparison morphism `comparison ψ x`. -/
theorem transitionRealizeIsoApp_hom_fst {n k : SimplexCategory} (ψ : n ⟶ k)
    (x : EtaleComponent A n) :
    (transitionRealizeIsoApp ψ x).hom.hom.left ≫
        (spacesBaseChange B S hS (A.left.map ψ.op)).projection.app (realize x) =
      comparison ψ x :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- The transition along `ψ`, followed by realization, is realization followed by base change
along `U(ψ) : U_k → U_n`: both are fibre products of the realization along `U(ψ)`. -/
def transitionRealizeIso {n k : SimplexCategory} (ψ : n ⟶ k) :
    transition (A := A) ψ ⋙ realizeFunctor k ≅
      realizeFunctor n ⋙ (spacesBaseChange B S hS (A.left.map ψ.op)).functor :=
  NatIso.ofComponents (transitionRealizeIsoApp ψ) (fun {x y} f ↦ by
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
    apply ((spacesBaseChange B S hS (A.left.map ψ.op)).isPullback (realize y)).hom_ext
    · have hnat : ((spacesBaseChange B S hS (A.left.map ψ.op)).functor.map f.hom).hom.left ≫
          (spacesBaseChange B S hS (A.left.map ψ.op)).projection.app (realize y) =
          (spacesBaseChange B S hS (A.left.map ψ.op)).projection.app (realize x) ≫
            f.hom.hom.left :=
        (spacesBaseChange B S hS (A.left.map ψ.op)).projection.naturality f.hom
      change (((transition ψ).map f).hom.hom.left ≫ (transitionRealizeIsoApp ψ y).hom.hom.left) ≫
          _ = ((transitionRealizeIsoApp ψ x).hom.hom.left ≫
            ((spacesBaseChange B S hS (A.left.map ψ.op)).functor.map f.hom).hom.left) ≫ _
      rw [Category.assoc, Category.assoc, transitionRealizeIsoApp_hom_fst, hnat,
        ← Category.assoc, transitionRealizeIsoApp_hom_fst]
      exact transition_map_hom_comp ψ f
    · exact ((Category.assoc _ _ _).trans ((congrArg (fun t ↦ _ ≫ t)
        (Over.w (transitionRealizeIsoApp ψ y).hom.hom)).trans
          (Over.w ((transition ψ).map f).hom.hom))).trans
        (((Over.w (transitionRealizeIsoApp ψ x).hom.hom).symm.trans (congrArg (fun t ↦ _ ≫ t)
          (Over.w ((spacesBaseChange B S hS (A.left.map ψ.op)).functor.map f.hom).hom).symm)).trans
            (Category.assoc _ _ _).symm))

/-- The transition along `ψ` preserves pullbacks. -/
instance {n k : SimplexCategory} (ψ : n ⟶ k) :
    PreservesLimitsOfShape WalkingCospan (transition (A := A) ψ) :=
  have : PreservesLimitsOfShape WalkingCospan (transition (A := A) ψ ⋙ realizeFunctor k) :=
    preservesLimitsOfShape_of_natIso (transitionRealizeIso ψ).symm
  preservesLimitsOfShape_of_reflects_of_preserves _ (realizeFunctor k)

/-- The transition along `ψ` preserves the pullback of `f` and `g`. -/
theorem transition_preservesLimit {n k : SimplexCategory} (ψ : n ⟶ k)
    {x y z : EtaleComponent A n} (f : x ⟶ y) (g : z ⟶ y) :
    PreservesLimit (cospan f g) (transition (A := A) ψ) :=
  inferInstance

/-- The comparison squares of a transition are cartesian along every arrow. -/
theorem isPullback_transition_map {n k : SimplexCategory} (ψ : n ⟶ k) {x y : EtaleComponent A n}
    (g : x ⟶ y) :
    IsPullback ((transition ψ).map g).hom.hom.left (comparison ψ x) (comparison ψ y)
      g.hom.hom.left := by
  refine IsPullback.of_right ?_ (transition_map_hom_comp ψ g) (isPullback_comparison ψ y).flip
  have e₁ : ((transition ψ).map g).hom.hom.left ≫ (realize (Index.push ψ y)).obj.hom =
      (realize (Index.push ψ x)).obj.hom := Over.w ((transition ψ).map g).hom.hom
  rw [e₁, Over.w g.hom.hom]
  exact (isPullback_comparison ψ x).flip

/-- The transition along `ψ` carries coverings of the component of degree `n` to coverings of the
component of degree `k`. -/
theorem precoverage_le_comap_transition {n k : SimplexCategory} (ψ : n ⟶ k) :
    precoverage (A := A) n ≤ (precoverage k).comap (transition ψ) :=
  fun _ _ hR ↦ map_mem_comap_precoverage_of_isPullback (realizeFunctor n) (transition ψ)
    (realizeFunctor k) (comparison ψ) (fun g ↦ isPullback_transition_map ψ g) hR

/-- The trivial formal base change of the final object of `U_{n, spaces, étale}` is final. -/
def isTerminalFinal (n : SimplexCategory) :
    IsTerminal (ofSpacesEtale (A := A) (SpacesEtale.idObj B S hS (A.left.obj (op n)))) :=
  IsTerminal.isTerminalOfObj (realizeFunctor n) _ (isTerminal_spacesBaseChange_idObj B S hS _)

/-- A pullback-preserving functor into the component of degree `n` that carries the coverings of
`K` to coverings and a terminal object to a terminal object is a morphism of sites. -/
private theorem isMorphismOfSites_toGrothendieck_precoverage {C : Type (u + 1)} [Category.{u + 1} C]
    [HasPullbacks C] {n : SimplexCategory} (K : Precoverage C) (F : C ⥤ EtaleComponent A n)
    [PreservesLimitsOfShape WalkingCospan F] (hK : K ≤ (precoverage n).comap F) {T : C}
    (hT : IsTerminal T) (hF : IsTerminal (F.obj T)) :
    F.IsMorphismOfSites K.toGrothendieck (precoverage n).toGrothendieck :=
  have : F.IsContinuous K.toGrothendieck (precoverage n).toGrothendieck :=
    Stacks.Sites.isContinuous_toGrothendieck_of_le_comap _ _ _
      (hK.trans (Precoverage.comap_monotone (Precoverage.le_toPrecoverage_toGrothendieck _)))
  Functor.isMorphismOfSites_of_isTerminal _ _ _ hT hF

/-- **Section 0DE7.** Every transition of the components is a morphism of sites. -/
theorem transition_isMorphismOfSites {n k : SimplexCategory} (ψ : n ⟶ k) :
    (transition (A := A) ψ).IsMorphismOfSites (precoverage n).toGrothendieck
      (precoverage k).toGrothendieck :=
  isMorphismOfSites_toGrothendieck_precoverage _ _ (precoverage_le_comap_transition ψ)
    (isTerminalFinal n)
    (IsTerminal.isTerminalOfObj (realizeFunctor k) _
      (isTerminal_spacesBaseChange_idObj B S hS _))

end EtaleComponent

open EtaleComponent in
/-- **Section 0DE7.** The simplicial site `n ↦ U_{n, spaces, étale}` of an augmented simplicial
algebraic space, with the base-change morphisms of sites of Stacks 03G2 as transitions. Its
total site is the small étale site `U_étale` of the simplicial algebraic space. -/
def etaleSimplicialSite : SimplicialSite.{u + 1} where
  underlying := etaleComponentsFunctor A
  coverage n := precoverage (A := A) n
  coverage_hasIsos n := inferInstanceAs (precoverage (A := A) n).HasIsos
  coverage_hasPullbacks n := inferInstanceAs (precoverage (A := A) n).HasPullbacks
  coverage_isStableUnderBaseChange n :=
    inferInstanceAs (precoverage (A := A) n).IsStableUnderBaseChange
  coverage_isStableUnderComposition n :=
    inferInstanceAs (precoverage (A := A) n).IsStableUnderComposition
  isMorphismOfSites φ := transition_isMorphismOfSites φ
  coverPreserving φ := precoverage_le_comap_transition φ
  preservesPullbacks := fun {_ _} φ {_ _} _ {_ _} _ {_} f ↦ transition_preservesLimit φ f _

namespace EtaleComponent

variable {A}

/-- An object étale over `X`, as the formal base change in degree `n` along `a_n : U_n → X`. -/
abbrev baseObj (n : SimplexCategory) (V : SpacesEtale B S hS A.right) : EtaleComponent A n :=
  (Sum.inl V : Index A n)

/-- The augmentation functor `X_{spaces, étale} ⥤` (component of degree `0`), base change along
`a_0 : U_0 → X`, realized as the formal base changes of objects étale over `X`. -/
def augmentationFunctor : SpacesEtale B S hS A.right ⥤ EtaleComponent A (SimplexCategory.mk 0)
    where
  obj V := baseObj _ V
  map f := InducedCategory.homMk
    ((spacesBaseChange B S hS (A.hom.app (op (SimplexCategory.mk 0)))).functor.map f)
  map_id V := InducedCategory.hom_ext
    ((spacesBaseChange B S hS (A.hom.app (op (SimplexCategory.mk 0)))).functor.map_id V)
  map_comp f g := InducedCategory.hom_ext
    ((spacesBaseChange B S hS (A.hom.app (op (SimplexCategory.mk 0)))).functor.map_comp f g)

/-- The augmentation functor followed by realization is base change along `a_0 : U_0 → X`. -/
theorem augmentationFunctor_comp_realize :
    augmentationFunctor (A := A) ⋙ realizeFunctor _ =
      (spacesBaseChange B S hS (A.hom.app (op (SimplexCategory.mk 0)))).functor :=
  rfl

/-- The augmentation functor preserves pullbacks. -/
instance : PreservesLimitsOfShape WalkingCospan (augmentationFunctor (A := A)) :=
  have : PreservesLimitsOfShape WalkingCospan (augmentationFunctor (A := A) ⋙ realizeFunctor _) :=
    inferInstanceAs (PreservesLimitsOfShape WalkingCospan (spacesBaseChange B S hS _).functor)
  preservesLimitsOfShape_of_reflects_of_preserves _ (realizeFunctor _)

/-- The augmentation functor carries coverings of `X_{spaces, étale}` to coverings of the
component of degree `0`. -/
theorem precoverage_le_comap_augmentationFunctor :
    SpacesEtale.precoverage B S hS A.right ≤
      (precoverage (A := A) (SimplexCategory.mk 0)).comap augmentationFunctor := by
  intro W R hR
  rw [← Precoverage.comap_id (SpacesEtale.precoverage B S hS A.right)] at hR
  exact map_mem_comap_precoverage_of_isPullback (𝟭 _) augmentationFunctor (realizeFunctor _)
    (fun V ↦ (spacesBaseChange B S hS (A.hom.app (op (SimplexCategory.mk 0)))).projection.app V)
    (fun g ↦ isPullback_spacesBaseChange_map _ g) hR

/-- The transitions act on base changes of objects étale over `X` as base change. -/
theorem transition_map_augmentationFunctor {n : SimplexCategory}
    (φ : SimplexCategory.mk 0 ⟶ n) {V W : SpacesEtale B S hS A.right} (f : V ⟶ W) :
    (transition φ).map (augmentationFunctor.map f) =
      (InducedCategory.homMk ((spacesBaseChange B S hS (A.hom.app (op n))).functor.map f) :
        baseObj n V ⟶ baseObj n W) := by
  refine InducedCategory.hom_ext ((transportAlong_eq_iff
    (isPullback_comparison φ (Sum.inl V)).toCommSq _ _ _).2 ?_)
  apply ((spacesBaseChange B S hS (A.hom.app (op (SimplexCategory.mk 0)))).isPullback W).hom_ext
  · refine ((Category.assoc _ _ _).trans ((congrArg (fun t ↦ _ ≫ t)
      (comparison_inl_fst φ W)).trans ((spacesBaseChange B S hS
        (A.hom.app (op n))).projection.naturality f))).trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    refine Eq.trans ?_ (congrArg (fun t ↦ comparison φ (Sum.inl V : Index A _) ≫ t)
      ((spacesBaseChange B S hS (A.hom.app (op (SimplexCategory.mk 0)))).projection.naturality
        f).symm)
    exact (congrArg (fun t ↦ t ≫ f.hom.left) (comparison_inl_fst φ V)).symm.trans
      (Category.assoc _ _ _)
  · refine ((Category.assoc _ _ _).trans (congrArg (fun t ↦ _ ≫ t)
      (comparison_hom φ (Sum.inl W)))).trans ?_
    refine ((Category.assoc _ _ _).symm.trans (congrArg (fun t ↦ t ≫ A.left.map φ.op)
      (Over.w ((spacesBaseChange B S hS (A.hom.app (op n))).functor.map f).hom))).trans ?_
    refine (comparison_hom φ (Sum.inl V)).symm.trans ?_
    refine Eq.trans ?_ (Category.assoc _ _ _).symm
    exact congrArg (fun t ↦ comparison φ (Sum.inl V : Index A _) ≫ t)
      (Over.w ((augmentationFunctor (A := A)).map f).hom.hom).symm

/-- The augmentation functor followed by the transition along `φ : [0] → [n]` does not depend on
`φ`. -/
theorem augmentationFunctor_comp_transition {n : SimplexCategory}
    (φ ψ : SimplexCategory.mk 0 ⟶ n) :
    augmentationFunctor (A := A) ⋙ transition φ = augmentationFunctor ⋙ transition ψ :=
  CategoryTheory.Functor.hext (fun _ ↦ rfl) (fun _ _ f ↦ by
    rw [Functor.comp_map, Functor.comp_map, transition_map_augmentationFunctor,
      transition_map_augmentationFunctor]
    exact HEq.rfl)

/-- The augmentation functor is a morphism of sites from `X_{spaces, étale}` to the component of
degree `0`. -/
theorem augmentationFunctor_isMorphismOfSites :
    (augmentationFunctor (A := A)).IsMorphismOfSites (SpacesEtale.topology B S hS A.right)
      (precoverage (SimplexCategory.mk 0)).toGrothendieck :=
  isMorphismOfSites_toGrothendieck_precoverage (SpacesEtale.precoverage B S hS A.right) _
    precoverage_le_comap_augmentationFunctor (SpacesEtale.isTerminal_idObj B S hS _)
    (IsTerminal.isTerminalOfObj (realizeFunctor _) _
      (isTerminal_spacesBaseChange_idObj B S hS _))

/-- The augmentation functor preserves the pullback of `f` and `g`. -/
theorem augmentationFunctor_preservesLimit {T V W : SpacesEtale B S hS A.right} (f : T ⟶ V)
    (g : W ⟶ V) : PreservesLimit (cospan f g) (augmentationFunctor (A := A)) :=
  inferInstance

end EtaleComponent

open EtaleComponent in
/-- **Section 0DE7, the augmentation.** The augmentation of the simplicial site
`n ↦ U_{n, spaces, étale}` towards `X_{spaces, étale}`: base change along `a_0 : U_0 → X`. -/
def etaleAugmentation :
    (etaleSimplicialSite A).ContinuousAugmentation (Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) where
  targetCoverage := SpacesEtale.precoverage B S hS A.right
  targetCoverage_hasIsos := inferInstanceAs (SpacesEtale.precoverage B S hS A.right).HasIsos
  targetCoverage_hasPullbacks :=
    inferInstanceAs (SpacesEtale.precoverage B S hS A.right).HasPullbacks
  targetCoverage_isStableUnderBaseChange :=
    inferInstanceAs (SpacesEtale.precoverage B S hS A.right).IsStableUnderBaseChange
  targetCoverage_isStableUnderComposition :=
    inferInstanceAs (SpacesEtale.precoverage B S hS A.right).IsStableUnderComposition
  targetCoverage_toGrothendieck := rfl
  functor := augmentationFunctor
  isMorphismOfSites := augmentationFunctor_isMorphismOfSites
  coverPreserving := precoverage_le_comap_augmentationFunctor
  preservesPullbacks := fun {_ _} _ {_ _} _ {_} f ↦ augmentationFunctor_preservesLimit f _
  compatibility _ φ ψ := augmentationFunctor_comp_transition φ ψ

/-- **Section 0DE7.** The morphism of topoi `a : Sh(U_étale) → Sh(X_étale)` attached to an
augmented simplicial algebraic space `a : U → X`, from the augmentation of sites by Stacks 0D70.
Here `Sh(X_étale)` is the topos of the spaces-étale site of `X`, which Section 0DE7 identifies
with the small étale topos. -/
abbrev etaleAugmentationMorphism :
    MorphismOfTopoi (Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)))
      (Sheaf (SpacesEtale.topology B S hS A.right) (Type (u + 1))) :=
  (etaleAugmentation A).totalMorphismOfTopoi

/-! ### Fppf hypercoverings -/

variable (B S hS) in
/-- The flat, locally finitely presented, surjective morphisms of algebraic spaces over `S`. -/
def fppfSurjective : MorphismProperty (AlgebraicSpaces B S hS) :=
  fun _ _ f ↦ IsFlat B S hS f.hom ∧ IsLocallyOfFinitePresentation B S hS f.hom ∧
    IsSurjective B S hS f.hom

/-- **Section 0DH4.** An augmented simplicial algebraic space `a : U → X` is an *fppf
hypercovering* of `X` when `U_0 → X`, `U_1 → U_0 ×_X U_0` and the matching morphisms
`U_{n + 1} → (cosk_n sk_n U)_{n + 1}`, `n ≥ 1`, are flat, locally of finite presentation and
surjective. -/
abbrev IsFppfHypercovering : Prop :=
  (fppfSurjective B S hS).IsHypercovering A

end AlgebraicGeometry.Space

end
