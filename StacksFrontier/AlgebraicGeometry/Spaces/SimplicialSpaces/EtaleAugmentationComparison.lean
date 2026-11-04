module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleSiteComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleRingedAugmentation
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.PhComparisonSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleSquare

/-!
# The two augmentations of the small étale site of an augmented simplicial algebraic space

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S`. Section 0DE7 of the
Stacks project attaches to it a morphism of ringed topoi
`a : (Sh(U_étale), 𝒪_U) → (Sh(X_étale), 𝒪_X)`. There are two constructions of it. The
first, `AlgebraicGeometry.Space.etaleAugmentationRingedHom`, lives on the total site of the strict
components of `U_étale`: its direct image is the limit over the simplex category of the direct
images along the augmentations of the degrees (Stacks 0D70). The second,
`AlgebraicGeometry.Space.SimplicialSpacesEtaleSite.augmentationRingedToposHom`, lives on
`SimplicialSpacesEtaleSite`: base change along `a` followed by forgetting the simplicial degree.

Through the equivalence of ringed topoi `AlgebraicGeometry.Space.etaleSiteComparisonRingedToposHom`
between the two sites they agree. On direct images: for a sheaf `F` on `SimplicialSpacesEtaleSite`
and `W` étale over `X`, both direct images are assembled from the sections of `F` over the base
changes `W ×_X U_n`, the first as the limit of the cosimplicial system of these sections and the
second as the right Kan extension along the functor forgetting the degree. The comparison map
from the second to the first has as legs the counit of that Kan extension; its inverse is the
transpose of the legs of the limit; that the two are inverse is the triangle identities of the
Kan extension adjunction. On structure maps: both pull global functions back along the
projections `W ×_X U_n → W`.

## Main definitions

* `AlgebraicGeometry.Space.etaleAugmentationPushforwardIso`: the isomorphism of direct images.
* `AlgebraicGeometry.Space.etaleAugmentationTwoIso`: the 2-isomorphism of morphisms of ringed
  topoi `a' ≅ a ∘ c`, where `a'` is the augmentation on `SimplicialSpacesEtaleSite`, `a` the
  augmentation on the strict components and `c` the comparison.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pseudofunctor

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

open EtaleComponent SimplicialSpacesEtaleSite SimplicialSiteSituation.Augmentation

/-- Two morphisms of sheaves of types on `Cat.of X_{spaces, étale}` agree as soon as they agree
on the sections over every object of `X_{spaces, étale}`. -/
private theorem spacesEtaleSheafHom_ext {X : AlgebraicSpaces B S hS}
    {F G : Sheaf (C := Cat.of (SpacesEtale B S hS X)) (SpacesEtale.topology B S hS X)
      (Type (u + 1))} {f g : F ⟶ G}
    (h : ∀ W : SpacesEtale B S hS X, f.hom.app (op W) = g.hom.app (op W)) : f = g :=
  ObjectProperty.hom_ext _ (NatTrans.ext (funext fun W => h W.unop))

/-- Two morphisms of sheaves of types on `const(X)_{spaces, étale}` agree as soon as they agree
on the sections over every `(n, W)`. -/
private theorem constSheafHom_ext {X : AlgebraicSpaces B S hS}
    {F G : Sheaf (topology ((Functor.const SimplexCategoryᵒᵖ).obj X)) (Type (u + 1))}
    {f g : F ⟶ G}
    (h : ∀ (n : SimplexCategory) (W : SpacesEtale B S hS X),
      f.hom.app (op ((degreeInclusion ((Functor.const _).obj X) n).obj W)) =
        g.hom.app (op ((degreeInclusion ((Functor.const _).obj X) n).obj W))) : f = g :=
  ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V => h V.unop.degree V.unop.obj))

/-- The sections of a composite of morphisms of sheaves. -/
private theorem sheafHom_comp_app {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G H : Sheaf J (Type (u + 1))} (f : F ⟶ G) (g : G ⟶ H) (W : Cᵒᵖ) :
    (f ≫ g).hom.app W = f.hom.app W ≫ g.hom.app W :=
  rfl

/-- If a composite of morphisms of sheaves is `h`, the composite of their sections is the sections
of `h`. -/
private theorem sheafHom_app_comp_eq {C : Type*} [Category C] {J : GrothendieckTopology C}
    {F G H : Sheaf J (Type (u + 1))} {f : F ⟶ G} {g : G ⟶ H} {h : F ⟶ H} (e : f ≫ g = h)
    (W : Cᵒᵖ) : f.hom.app W ≫ g.hom.app W = h.hom.app W :=
  (sheafHom_comp_app f g W).symm.trans (congrArg (fun t => t.hom.app W) e)

/-! ### The base changes `W ×_X U_n` in the two models -/

variable (A) in
/-- The augmentation `U ⟶ const(X)` of an augmented simplicial algebraic space, read with
source `U`. -/
abbrev augmentationToConst : A.left ⟶ (Functor.const _).obj A.right :=
  A.hom

/-- The comparison acts on underlying morphisms as the comparison functor into
`(Spaces/U)_total`. -/
theorem etaleSiteComparison_map_hom_eq {x y : EtaleTotal A} (f : x ⟶ y) :
    ((etaleSiteComparison A).map f).hom =
      (Grothendieck.Hom.fiber ((phComparisonFunctor A).map f)).left :=
  (phComparisonFunctor_map_fiber_left f).symm

/-- Base change along `a` of a morphism of `X_{spaces, étale}` in degree `n` is the comparison of
its image in degree `n` of `U_étale`. -/
theorem pullbackFunctor_map_degreeInclusion_map (n : SimplexCategory)
    {W W' : SpacesEtale B S hS A.right} (k : W ⟶ W') :
    (pullbackFunctor (augmentationToConst A)).map
        ((degreeInclusion ((Functor.const _).obj A.right) n).map k) =
      (etaleSiteComparison A).map (((etaleAugmentation A).totalComponentSiteFunctor n).map k) := by
  refine Hom.ext rfl (pullback.hom_ext ?_ ?_)
  · refine (pullback.lift_fst _ _ _).trans ?_
    refine Eq.trans ?_ ((congrArg
      (· ≫ (spacesBaseChange B S hS (A.hom.app (op n))).projection.app W')
      (etaleSiteComparison_map_hom_eq _)).trans (phBaseFunctor_map_fst n k)).symm
    rfl
  · refine (pullback.lift_snd _ _ _).trans ?_
    exact ((etaleSiteComparison A).map
      (((etaleAugmentation A).totalComponentSiteFunctor n).map k)).w.symm

variable (A) in
/-- The morphism `(n, W) ⟶ (m, W)` of `const(X)_{spaces, étale}` lying over `χ : [m] → [n]`, with
the identity of `W`. -/
def constTransition {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    (degreeInclusion ((Functor.const _).obj A.right) n).obj W ⟶
      (degreeInclusion ((Functor.const _).obj A.right) m).obj W :=
  ⟨χ, 𝟙 _, (Category.id_comp _).trans (Category.comp_id _).symm⟩

/-- Base change along `a` of the transition `(n, W) ⟶ (m, W)` is the comparison of the cartesian
arrow of `U_étale` from `W ×_X U_n` to `W ×_X U_m`. -/
theorem pullbackFunctor_map_constTransition {m n : SimplexCategory} (χ : m ⟶ n)
    (W : SpacesEtale B S hS A.right) :
    (pullbackFunctor (augmentationToConst A)).map (constTransition A χ W) =
      (etaleSiteComparison A).map ((CoGrothendieck.ιNatTrans
        (etaleSimplicialSite A).totalPseudofunctor χ.op).app (Sum.inl W : Index A m)) := by
  refine Hom.ext rfl (pullback.hom_ext ?_ ?_)
  · refine (pullback.lift_fst _ _ _).trans ?_
    refine ((Category.comp_id _).trans ?_)
    exact ((congrArg (· ≫ (spacesBaseChange B S hS (A.hom.app (op m))).projection.app W)
      (etaleSiteComparison_map_hom_eq _)).trans (phBaseTransition_fst χ W)).symm
  · refine (pullback.lift_snd _ _ _).trans ?_
    exact ((etaleSiteComparison A).map ((CoGrothendieck.ιNatTrans
      (etaleSimplicialSite A).totalPseudofunctor χ.op).app (Sum.inl W : Index A m))).w.symm

/-! ### The comparison of the direct images -/

variable (A) in
/-- The direct image of the augmentation of `SimplicialSpacesEtaleSite` followed by the
evaluation at the base changes in degree `n`: the counit of the Kan extension along the functor
forgetting the degree, at the objects `(n, W)`. These are the legs of the comparison of the
direct images. -/
def etaleAugmentationComparisonLeg (F : Sheaf (topology A.left) (Type (u + 1)))
    (n : SimplexCategory) :
    @Quiver.Hom (Sheaf (C := Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (Type (u + 1))) _
      ((constToposHom A.right).pushforward.obj
        ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F))
      ((componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) n).obj
        ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F)) :=
  ObjectProperty.homMk
    { app := fun W => ((constToposHom A.right).adj.counit.app
          ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F)).hom.app
        (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W.unop))
      naturality := fun W W' k => by
        refine (((constToposHom A.right).adj.counit.app
          ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F)).hom.naturality
          ((degreeInclusion ((Functor.const _).obj A.right) n).map k.unop).op).trans
          (congrArg (_ ≫ ·) ?_)
        exact congrArg (fun t => F.obj.map (Quiver.Hom.op t))
          (pullbackFunctor_map_degreeInclusion_map n k.unop) }

/-- The leg of the comparison in degree `n`, on sections over `W`, is the counit of the Kan
extension along the functor forgetting the degree at `(n, W)`. -/
theorem etaleAugmentationComparisonLeg_app (F : Sheaf (topology A.left) (Type (u + 1)))
    (n : SimplexCategory) (W : SpacesEtale B S hS A.right) :
    (etaleAugmentationComparisonLeg A F n).hom.app (op W) =
      ((constToposHom A.right).adj.counit.app
          ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F)).hom.app
        (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) :=
  rfl

/-- Forgetting the degree sends the transition `(n, W) ⟶ (m, W)` to the identity of `W`. -/
theorem constForget_map_constTransition {m n : SimplexCategory} (χ : m ⟶ n)
    (W : SpacesEtale B S hS A.right) :
    (constForget A.right).map (constTransition A χ W) = 𝟙 W :=
  rfl

/-- The direct image along the comparison of ringed topoi is restriction along the comparison
functor. -/
theorem etaleSiteComparisonRingedToposHom_pushforward_obj_map
    (F : Sheaf (topology A.left) (Type (u + 1))) {x y : EtaleTotal A} (t : x ⟶ y) :
    ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F).obj.map t.op =
      F.obj.map ((etaleSiteComparison A).map t).op :=
  rfl

/-- The transitions of the cosimplicial system of direct images of the restriction along the
comparison, on sections. -/
theorem pushforwardDiagram_etaleSiteComparison_map_app_aux
    (F : Sheaf (topology A.left) (Type (u + 1)))
    {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    ((componentPushforwardTransition (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) χ).app
        ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F)).hom.app
        (op W) =
      ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F).obj.map
        ((CoGrothendieck.ιNatTrans (etaleSimplicialSite A).totalPseudofunctor χ.op).app
          (Sum.inl W : Index A m)).op :=
  transition_app_eq _ χ W

/-- The direct image along base change by `a` is restriction along the base change functor. -/
theorem ringedToposHom_pushforward_obj_map (F : Sheaf (topology A.left) (Type (u + 1)))
    {x y : SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj A.right)} (t : x ⟶ y) :
    ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F).obj.map t.op =
      F.obj.map ((pullbackFunctor (augmentationToConst A)).map t).op :=
  rfl

/-- The transitions of the cosimplicial system of direct images of the restriction along the
comparison act on sections over `W` as restriction along base change of the transition
`(n, W) ⟶ (m, W)`. -/
theorem pushforwardDiagram_etaleSiteComparison_map_app (F : Sheaf (topology A.left) (Type (u + 1)))
    {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    ((componentPushforwardTransition (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) χ).app
        ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F)).hom.app
        (op W) =
      ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F).obj.map
        (constTransition A χ W).op :=
  (((pushforwardDiagram_etaleSiteComparison_map_app_aux F χ W).trans
    (etaleSiteComparisonRingedToposHom_pushforward_obj_map F _)).trans
    (congrArg (fun t => F.obj.map (Quiver.Hom.op t))
      (pullbackFunctor_map_constTransition χ W).symm)).trans
    (ringedToposHom_pushforward_obj_map F _).symm

/-- The sheaf restricted along the functor forgetting the degree does not move along the
transition `(n, W) ⟶ (m, W)`. -/
theorem constToposHom_inverseImage_map_constTransition
    (G : Sheaf (SpacesEtale.topology B S hS A.right) (Type (u + 1)))
    {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    ((constToposHom A.right).inverseImage.obj G).obj.map (constTransition A χ W).op = 𝟙 _ :=
  G.obj.map_id (op W)

/-- The counit of the Kan extension along the functor forgetting the degree, at the base change
in degree `m`, followed by restriction along the transition `(n, W) ⟶ (m, W)`, is the counit at
the base change in degree `n`. -/
theorem constToposHom_counit_app_comp_constTransition (H : Sheaf (topology
      ((Functor.const SimplexCategoryᵒᵖ).obj A.right)) (Type (u + 1)))
    {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    ((constToposHom A.right).adj.counit.app H).hom.app
        (op ((degreeInclusion ((Functor.const _).obj A.right) m).obj W)) ≫
      H.obj.map (constTransition A χ W).op =
    ((constToposHom A.right).adj.counit.app H).hom.app
        (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) :=
  (((constToposHom A.right).adj.counit.app H).hom.naturality
    (constTransition A χ W).op).symm.trans
    ((congrArg (· ≫ _) (constToposHom_inverseImage_map_constTransition _ χ W)).trans
      (Category.id_comp _))

/-- The legs of the comparison are compatible with the transitions, on sections. -/
theorem etaleAugmentationComparisonLeg_app_comp_app (F : Sheaf (topology A.left) (Type (u + 1)))
    {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    (etaleAugmentationComparisonLeg A F m).hom.app (op W) ≫
        ((componentPushforwardTransition (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) χ).app
            ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F)).hom.app
            (op W) =
      (etaleAugmentationComparisonLeg A F n).hom.app (op W) :=
  (congrArg (_ ≫ ·) (pushforwardDiagram_etaleSiteComparison_map_app F χ W)).trans
    (constToposHom_counit_app_comp_constTransition _ χ W)

/-- The sections of the composite of a leg of the comparison with a transition. -/
theorem etaleAugmentationComparisonLeg_comp_transition_app
    (F : Sheaf (topology A.left) (Type (u + 1)))
    {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    (etaleAugmentationComparisonLeg A F m ≫
        (componentPushforwardTransition (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) χ).app
          ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F)).hom.app (op W) =
      (etaleAugmentationComparisonLeg A F m).hom.app (op W) ≫
        ((componentPushforwardTransition (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) χ).app
          ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F)).hom.app (op W) :=
  sheafHom_comp_app _ _ _

/-- The legs of the comparison are compatible with the transitions, on sections. -/
theorem etaleAugmentationComparisonLeg_comp_transition_app_eq
    (F : Sheaf (topology A.left) (Type (u + 1)))
    {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    (etaleAugmentationComparisonLeg A F m ≫
        (componentPushforwardTransition (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) χ).app
          ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F)).hom.app (op W) =
      (etaleAugmentationComparisonLeg A F n).hom.app (op W) :=
  (etaleAugmentationComparisonLeg_comp_transition_app F χ W).trans
    (etaleAugmentationComparisonLeg_app_comp_app F χ W)

/-- The legs of the comparison are compatible with the transitions. -/
theorem etaleAugmentationComparisonLeg_comp (F : Sheaf (topology A.left) (Type (u + 1)))
    {m n : SimplexCategory} (χ : m ⟶ n) :
    etaleAugmentationComparisonLeg A F m ≫
        (componentPushforwardTransition (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) χ).app
          ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F) =
      etaleAugmentationComparisonLeg A F n :=
  spacesEtaleSheafHom_ext (etaleAugmentationComparisonLeg_comp_transition_app_eq F χ)

variable (A) in
/-- **The cone comparing the direct images**: its vertex is the direct image of the augmentation
of `SimplicialSpacesEtaleSite`, its legs the counits at the base changes in each degree. -/
def etaleAugmentationComparisonCone (F : Sheaf (topology A.left) (Type (u + 1))) :
    Cone (pushforwardDiagram (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)
      ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F)) where
  pt := (constToposHom A.right).pushforward.obj
      ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F)
  π :=
    { app := fun n => etaleAugmentationComparisonLeg A F n
      naturality := fun _ _ χ => (Category.id_comp _).trans
        (etaleAugmentationComparisonLeg_comp F χ).symm }

/-! ### The transpose of the legs of the limit -/

variable (A) in
/-- The direct image along the strict-model augmentation of the restriction along the comparison:
the limit of the cosimplicial system of sections over the base changes `W ×_X U_n`. -/
abbrev etaleStrictPushforward (F : Sheaf (topology A.left) (Type (u + 1))) :
    Sheaf (C := Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (Type (u + 1)) :=
  (pushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
    (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)).obj
    ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F)

variable (A) in
/-- The leg of the limit in degree `n`. -/
abbrev etaleStrictProjection (F : Sheaf (topology A.left) (Type (u + 1))) (n : SimplexCategory) :
    etaleStrictPushforward A F ⟶
      (componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) n).obj
        ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F) :=
  pushforwardProjection (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
    (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)
    ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F) n

/-- The legs of the limit are compatible with the transitions, on sections. -/
theorem etaleStrictProjection_comp_transition_app (F : Sheaf (topology A.left) (Type (u + 1)))
    {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    (etaleStrictProjection A F m ≫
        (componentPushforwardTransition (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) χ).app
          ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F)).hom.app (op W) =
      (etaleStrictProjection A F n).hom.app (op W) :=
  congrArg (fun t => t.hom.app (op W))
    (pushforwardProjection_comp (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)
      ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F) χ)

/-- The sections of the composite of a leg of the limit with a transition. -/
theorem etaleStrictProjection_comp_transition_app_eq_comp
    (F : Sheaf (topology A.left) (Type (u + 1)))
    {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    (etaleStrictProjection A F m ≫
        (componentPushforwardTransition (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) χ).app
          ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F)).hom.app (op W) =
      (etaleStrictProjection A F m).hom.app (op W) ≫
        ((componentPushforwardTransition (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) χ).app
          ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.obj F)).hom.app (op W) :=
  sheafHom_comp_app _ _ _

/-- The leg in degree `m` followed by the transition to degree `n` is the leg in degree `n`, on
sections, with the transition read as restriction along base change of `(n, W) ⟶ (m, W)`. -/
theorem etaleStrictProjection_app_comp_map (F : Sheaf (topology A.left) (Type (u + 1)))
    {m n : SimplexCategory} (χ : m ⟶ n) (W : SpacesEtale B S hS A.right) :
    (etaleStrictProjection A F m).hom.app (op W) ≫
        ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F).obj.map
          (constTransition A χ W).op =
      (etaleStrictProjection A F n).hom.app (op W) :=
  (congrArg (_ ≫ ·) (pushforwardDiagram_etaleSiteComparison_map_app F χ W)).symm.trans
    ((etaleStrictProjection_comp_transition_app_eq_comp F χ W).symm.trans
      (etaleStrictProjection_comp_transition_app F χ W))

/-- The leg in degree `n` is natural in `W`, on sections, with the restriction of the target read
as restriction along base change of `(n, W') ⟶ (n, W)`. -/
theorem etaleStrictProjection_naturality (F : Sheaf (topology A.left) (Type (u + 1)))
    (n : SimplexCategory) {W W' : SpacesEtale B S hS A.right} (k : W' ⟶ W) :
    (etaleStrictPushforward A F).obj.map k.op ≫ (etaleStrictProjection A F n).hom.app (op W') =
      (etaleStrictProjection A F n).hom.app (op W) ≫
        ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F).obj.map
          ((degreeInclusion ((Functor.const _).obj A.right) n).map k).op :=
  ((etaleStrictProjection A F n).hom.naturality k.op).trans (congrArg (_ ≫ ·)
    (congrArg (fun t => F.obj.map (Quiver.Hom.op t))
      (pullbackFunctor_map_degreeInclusion_map n k).symm))

/-- A morphism `(n', W') ⟶ (n, W)` of `const(X)_{spaces, étale}` is the morphism of degree `n'`
given by its morphism of algebraic spaces, followed by the transition `(n', W) ⟶ (n, W)`. -/
theorem const_hom_eq_degreeInclusion_map_comp_constTransition
    {V V' : SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj A.right)} (t : V' ⟶ V) :
    t = (degreeInclusion ((Functor.const _).obj A.right) V'.degree).map
        ((constForget A.right).map t) ≫ constTransition A t.base V.obj :=
  Hom.ext (Category.comp_id _).symm (Category.comp_id _).symm

/-- The legs of the limit, read on `const(X)_{spaces, étale}`, are natural: they form a morphism
from the restriction of the limit along the functor forgetting the degree. -/
theorem etaleStrictProjection_naturality_const (F : Sheaf (topology A.left) (Type (u + 1)))
    {V V' : SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj A.right)} (t : V' ⟶ V) :
    (etaleStrictPushforward A F).obj.map ((constForget A.right).map t).op ≫
        (etaleStrictProjection A F V'.degree).hom.app (op V'.obj) =
      (etaleStrictProjection A F V.degree).hom.app (op V.obj) ≫
        ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F).obj.map t.op := by
  refine (etaleStrictProjection_naturality F V'.degree ((constForget A.right).map t)).trans ?_
  refine (congrArg (· ≫ _) (etaleStrictProjection_app_comp_map F t.base V.obj).symm).trans ?_
  refine (Category.assoc _ _ _).trans (congrArg (_ ≫ ·) ?_)
  refine ((((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F).obj.map_comp
    _ _).symm).trans ?_
  exact congrArg (fun x => ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj
    F).obj.map (Quiver.Hom.op x)) (const_hom_eq_degreeInclusion_map_comp_constTransition t).symm

variable (A) in
/-- **The transpose of the legs of the limit**: the morphism from the restriction of the limit
along the functor forgetting the degree to the restriction of `F` along base change by `a`, given
at `(n, W)` by the leg of the limit in degree `n` over `W`. -/
def etaleStrictTranspose (F : Sheaf (topology A.left) (Type (u + 1))) :
    (constToposHom A.right).inverseImage.obj (etaleStrictPushforward A F) ⟶
      (ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F :=
  ObjectProperty.homMk
    { app := fun V => (etaleStrictProjection A F V.unop.degree).hom.app (op V.unop.obj)
      naturality := fun {X Y} t => by
        obtain ⟨V⟩ := X
        obtain ⟨V'⟩ := Y
        exact etaleStrictProjection_naturality_const F t.unop }

/-- The transpose of the legs of the limit, on sections over `(n, W)`, is the leg of the limit in
degree `n` over `W`. -/
theorem etaleStrictTranspose_app (F : Sheaf (topology A.left) (Type (u + 1)))
    (V : SimplicialSpacesEtaleSite B S hS ((Functor.const _).obj A.right)) :
    (etaleStrictTranspose A F).hom.app (op V) =
      (etaleStrictProjection A F V.degree).hom.app (op V.obj) :=
  rfl

/-! ### The comparison of the direct images -/

variable (A) in
/-- **The comparison of the two direct images**: from the direct image along the augmentation of
`SimplicialSpacesEtaleSite` to the limit of the cosimplicial system of the strict model, the map
whose legs are the counits at the base changes `(n, W)`. -/
def etaleAugmentationComparisonHom (F : Sheaf (topology A.left) (Type (u + 1))) :
    @Quiver.Hom (Sheaf (C := Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (Type (u + 1))) _
      ((constToposHom A.right).pushforward.obj
        ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F))
      (etaleStrictPushforward A F) :=
  pushforwardLiftCone (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
    (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)
    (etaleAugmentationComparisonCone A F)

/-- The comparison of the direct images followed by the leg of the limit in degree `n` is the leg
of the comparison in degree `n`. -/
theorem etaleAugmentationComparisonHom_comp_projection (F : Sheaf (topology A.left) (Type (u + 1)))
    (n : SimplexCategory) :
    etaleAugmentationComparisonHom A F ≫ etaleStrictProjection A F n =
      etaleAugmentationComparisonLeg A F n :=
  pushforwardLiftCone_comp_projection _ _ _ _ _ n

variable (A) in
/-- The inverse comparison: the transpose, along the Kan extension adjunction of the functor
forgetting the degree, of the legs of the limit. -/
def etaleAugmentationComparisonInv (F : Sheaf (topology A.left) (Type (u + 1))) :
    @Quiver.Hom (Sheaf (C := Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (Type (u + 1))) _
      (etaleStrictPushforward A F)
      ((constToposHom A.right).pushforward.obj
        ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F)) :=
  (constToposHom A.right).adj.homEquiv _ _ (etaleStrictTranspose A F)

/-- The inverse comparison followed by the leg of the comparison in degree `n`, on sections over
`W`, is the restriction of the inverse comparison along the functor forgetting the degree at
`(n, W)` followed by the counit there. -/
theorem constToposHom_inverseImage_map_comparisonInv_app
    (F : Sheaf (topology A.left) (Type (u + 1))) (n : SimplexCategory)
    (W : SpacesEtale B S hS A.right) :
    (etaleAugmentationComparisonInv A F).hom.app (op W) ≫
        (etaleAugmentationComparisonLeg A F n).hom.app (op W) =
      ((constToposHom A.right).inverseImage.map (etaleAugmentationComparisonInv A F)).hom.app
          (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) ≫
        ((constToposHom A.right).adj.counit.app
          ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F)).hom.app
          (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) :=
  rfl

/-- The restriction of the inverse comparison along the functor forgetting the degree, followed
by the counit, is the transpose of the legs of the limit. -/
theorem constToposHom_inverseImage_map_comparisonInv_comp_counit
    (F : Sheaf (topology A.left) (Type (u + 1))) :
    (constToposHom A.right).inverseImage.map (etaleAugmentationComparisonInv A F) ≫
        (constToposHom A.right).adj.counit.app
          ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F) =
      etaleStrictTranspose A F :=
  ((constToposHom A.right).adj.homEquiv_counit _ _ _).symm.trans
    (Equiv.symm_apply_apply _ _)

/-- The restriction of the inverse comparison along the functor forgetting the degree, followed
by the counit, is the transpose of the legs of the limit, on sections over `(n, W)`. -/
theorem constToposHom_inverseImage_map_comparisonInv_comp_counit_app
    (F : Sheaf (topology A.left) (Type (u + 1))) (n : SimplexCategory)
    (W : SpacesEtale B S hS A.right) :
    ((constToposHom A.right).inverseImage.map (etaleAugmentationComparisonInv A F)).hom.app
          (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) ≫
        ((constToposHom A.right).adj.counit.app
          ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F)).hom.app
          (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) =
      (etaleStrictTranspose A F).hom.app
        (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) :=
  sheafHom_app_comp_eq (constToposHom_inverseImage_map_comparisonInv_comp_counit F) _

/-- The sections of the composite of the inverse comparison with a leg of the comparison. -/
theorem etaleAugmentationComparisonInv_comp_leg_app (F : Sheaf (topology A.left) (Type (u + 1)))
    (n : SimplexCategory) (W : SpacesEtale B S hS A.right) :
    (etaleAugmentationComparisonInv A F ≫ etaleAugmentationComparisonLeg A F n).hom.app (op W) =
      (etaleAugmentationComparisonInv A F).hom.app (op W) ≫
        (etaleAugmentationComparisonLeg A F n).hom.app (op W) :=
  sheafHom_comp_app _ _ _

/-- A morphism followed by the comparison of the direct images is determined by its composites
with the legs of the comparison. -/
private theorem comp_etaleAugmentationComparisonHom_eq
    (F : Sheaf (topology A.left) (Type (u + 1)))
    {P : Sheaf (C := Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) (Type (u + 1))}
    {f : P ⟶ (constToposHom A.right).pushforward.obj
      ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F)}
    {g : P ⟶ etaleStrictPushforward A F}
    (h : ∀ n, f ≫ etaleAugmentationComparisonLeg A F n = g ≫ etaleStrictProjection A F n) :
    f ≫ etaleAugmentationComparisonHom A F = g :=
  pushforward_hom_ext (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
    (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) fun n =>
      (Category.assoc _ _ _).trans ((congrArg (f ≫ ·)
        (etaleAugmentationComparisonHom_comp_projection F n)).trans (h n))

/-- The inverse comparison followed by the leg of the comparison in degree `n` is the leg of the
limit in degree `n`. -/
theorem etaleAugmentationComparisonInv_comp_leg (F : Sheaf (topology A.left) (Type (u + 1)))
    (n : SimplexCategory) :
    etaleAugmentationComparisonInv A F ≫ etaleAugmentationComparisonLeg A F n =
      etaleStrictProjection A F n :=
  spacesEtaleSheafHom_ext fun W => (etaleAugmentationComparisonInv_comp_leg_app F n W).trans
    ((constToposHom_inverseImage_map_comparisonInv_app F n W).trans
      (constToposHom_inverseImage_map_comparisonInv_comp_counit_app F n W))

/-- The inverse comparison followed by the comparison is the identity of the limit. -/
theorem etaleAugmentationComparisonInv_comp_hom (F : Sheaf (topology A.left) (Type (u + 1))) :
    etaleAugmentationComparisonInv A F ≫ etaleAugmentationComparisonHom A F = 𝟙 _ :=
  comp_etaleAugmentationComparisonHom_eq F fun n =>
    (etaleAugmentationComparisonInv_comp_leg F n).trans (Category.id_comp _).symm

/-- The restriction of the comparison along the functor forgetting the degree, followed by the
transpose of the legs of the limit, on sections over `(n, W)`, is the comparison followed by the
leg of the limit in degree `n`, on sections over `W`. -/
theorem constToposHom_inverseImage_map_comparisonHom_app_comp
    (F : Sheaf (topology A.left) (Type (u + 1))) (n : SimplexCategory)
    (W : SpacesEtale B S hS A.right) :
    ((constToposHom A.right).inverseImage.map (etaleAugmentationComparisonHom A F)).hom.app
          (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) ≫
        (etaleStrictTranspose A F).hom.app
          (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) =
      (etaleAugmentationComparisonHom A F).hom.app (op W) ≫
        (etaleStrictProjection A F n).hom.app (op W) :=
  rfl

/-- The sections of the composite of the comparison with a leg of the limit. -/
theorem etaleAugmentationComparisonHom_comp_projection_app
    (F : Sheaf (topology A.left) (Type (u + 1))) (n : SimplexCategory)
    (W : SpacesEtale B S hS A.right) :
    (etaleAugmentationComparisonHom A F).hom.app (op W) ≫
        (etaleStrictProjection A F n).hom.app (op W) =
      (etaleAugmentationComparisonHom A F ≫ etaleStrictProjection A F n).hom.app (op W) :=
  (sheafHom_comp_app _ _ _).symm

/-- The comparison followed by the leg of the limit in degree `n`, on sections over `W`, is the
counit of the Kan extension along the functor forgetting the degree at `(n, W)`. -/
theorem etaleAugmentationComparisonHom_comp_projection_app_eq_counit
    (F : Sheaf (topology A.left) (Type (u + 1))) (n : SimplexCategory)
    (W : SpacesEtale B S hS A.right) :
    (etaleAugmentationComparisonHom A F ≫ etaleStrictProjection A F n).hom.app (op W) =
      ((constToposHom A.right).adj.counit.app
          ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F)).hom.app
        (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) :=
  (congrArg (fun t => t.hom.app (op W)) (etaleAugmentationComparisonHom_comp_projection F n)).trans
    (etaleAugmentationComparisonLeg_app F n W)

/-- The restriction of the comparison along the functor forgetting the degree, followed by the
transpose of the legs of the limit, is the counit of the Kan extension. -/
theorem constToposHom_inverseImage_map_comparisonHom_comp_transpose
    (F : Sheaf (topology A.left) (Type (u + 1))) :
    (constToposHom A.right).inverseImage.map (etaleAugmentationComparisonHom A F) ≫
        etaleStrictTranspose A F =
      (constToposHom A.right).adj.counit.app
        ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F) :=
  constSheafHom_ext fun n W => (sheafHom_comp_app _ _ _).trans
    ((constToposHom_inverseImage_map_comparisonHom_app_comp F n W).trans
      ((etaleAugmentationComparisonHom_comp_projection_app F n W).trans
        (etaleAugmentationComparisonHom_comp_projection_app_eq_counit F n W)))

/-- The comparison followed by the inverse comparison is the identity of the direct image along
the augmentation of `SimplicialSpacesEtaleSite`. -/
theorem etaleAugmentationComparisonHom_comp_inv (F : Sheaf (topology A.left) (Type (u + 1))) :
    etaleAugmentationComparisonHom A F ≫ etaleAugmentationComparisonInv A F = 𝟙 _ := by
  apply ((constToposHom A.right).adj.homEquiv _ _).symm.injective
  refine ((constToposHom A.right).adj.homEquiv_naturality_left_symm _ _).trans ?_
  refine (congrArg (_ ≫ ·) (Equiv.symm_apply_apply _ _)).trans ?_
  refine (constToposHom_inverseImage_map_comparisonHom_comp_transpose F).trans ?_
  refine Eq.trans ?_ ((constToposHom A.right).adj.homEquiv_counit _ _ _).symm
  exact ((Category.id_comp _).symm.trans (congrArg (· ≫ _)
    (CategoryTheory.Functor.map_id (constToposHom A.right).inverseImage _).symm))

variable (A) in
/-- The direct image of the augmentation of `SimplicialSpacesEtaleSite`, base change along `a`
followed by the Kan extension along the functor forgetting the degree, with values read in the
sheaves on `X_{spaces, étale}` of the strict model. -/
abbrev etaleSpacesPushforward :
    Sheaf (topology A.left) (Type (u + 1)) ⥤
      Sheaf (C := Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
        (Type (u + 1)) :=
  (ringedToposHom (augmentationToConst A)).toToposHom.pushforward ⋙
    (constToposHom A.right).pushforward

variable (A) in
/-- The direct image of the strict-model augmentation after restriction along the comparison. -/
abbrev etaleStrictPushforwardFunctor :
    Sheaf (topology A.left) (Type (u + 1)) ⥤
      Sheaf (C := Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
        (Type (u + 1)) :=
  (etaleSiteComparisonRingedToposHom A).toToposHom.pushforward ⋙
    pushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
      (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)

/-- The counit of the Kan extension along the functor forgetting the degree, at `(n, W)`, is
natural in the sheaf `F` on `U_étale`. -/
theorem constToposHom_counit_naturality_app {F F' : Sheaf (topology A.left) (Type (u + 1))}
    (φ : F ⟶ F') (n : SimplexCategory) (W : SpacesEtale B S hS A.right) :
    ((etaleSpacesPushforward A).map φ).hom.app (op W) ≫
        ((constToposHom A.right).adj.counit.app
          ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F')).hom.app
          (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) =
      ((constToposHom A.right).adj.counit.app
          ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.obj F)).hom.app
          (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) ≫
        φ.hom.app (op ((pullbackFunctor (augmentationToConst A)).obj
          ((degreeInclusion ((Functor.const _).obj A.right) n).obj W))) :=
  (sheafHom_app_comp_eq ((constToposHom A.right).adj.counit.naturality
    ((ringedToposHom (augmentationToConst A)).toToposHom.pushforward.map φ)) _).trans
    (sheafHom_comp_app _ _ _)

/-- The sections of the composite of the direct image of `φ` with a leg of the comparison. -/
theorem etaleSpacesPushforward_map_comp_leg_app {F F' : Sheaf (topology A.left) (Type (u + 1))}
    (φ : F ⟶ F') (n : SimplexCategory) (W : SpacesEtale B S hS A.right) :
    ((etaleSpacesPushforward A).map φ ≫ etaleAugmentationComparisonLeg A F' n).hom.app (op W) =
      ((etaleSpacesPushforward A).map φ).hom.app (op W) ≫
        (etaleAugmentationComparisonLeg A F' n).hom.app (op W) :=
  sheafHom_comp_app _ _ _

/-- The sections of the composite of a leg of the comparison with the direct image of `φ` in
degree `n`. -/
theorem etaleAugmentationComparisonLeg_comp_map_app {F F' : Sheaf (topology A.left) (Type (u + 1))}
    (φ : F ⟶ F') (n : SimplexCategory) (W : SpacesEtale B S hS A.right) :
    (etaleAugmentationComparisonLeg A F n ≫
        (componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) n).map
          ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.map φ)).hom.app (op W) =
      (etaleAugmentationComparisonLeg A F n).hom.app (op W) ≫
        ((componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) n).map
          ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.map φ)).hom.app (op W) :=
  sheafHom_comp_app _ _ _

/-- The leg of the comparison in degree `n` is natural in the sheaf `F` on `U_étale`. -/
theorem etaleAugmentationComparisonLeg_naturality {F F' : Sheaf (topology A.left) (Type (u + 1))}
    (φ : F ⟶ F') (n : SimplexCategory) :
    (etaleSpacesPushforward A).map φ ≫ etaleAugmentationComparisonLeg A F' n =
      etaleAugmentationComparisonLeg A F n ≫
        (componentPushforward (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) n).map
          ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.map φ) :=
  spacesEtaleSheafHom_ext fun W => (etaleSpacesPushforward_map_comp_leg_app φ n W).trans
    ((constToposHom_counit_naturality_app φ n W).trans
      (etaleAugmentationComparisonLeg_comp_map_app φ n W).symm)

/-- The comparison of the direct images is natural in the sheaf `F` on `U_étale`. -/
theorem etaleAugmentationComparisonHom_naturality {F F' : Sheaf (topology A.left) (Type (u + 1))}
    (φ : F ⟶ F') :
    (etaleSpacesPushforward A).map φ ≫ etaleAugmentationComparisonHom A F' =
      etaleAugmentationComparisonHom A F ≫ (etaleStrictPushforwardFunctor A).map φ :=
  comp_etaleAugmentationComparisonHom_eq F' fun n =>
    (etaleAugmentationComparisonLeg_naturality φ n).trans
      ((congrArg (· ≫ _) (etaleAugmentationComparisonHom_comp_projection F n)).symm.trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (pushforward_map_comp_projection
          (etaleSituation A) (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A)
          ((etaleSiteComparisonRingedToposHom A).toToposHom.pushforward.map φ) n)).symm.trans
          (Category.assoc _ _ _).symm)))

variable (A) in
/-- **The two direct images of the augmentation agree**: the direct image along the augmentation
of `SimplicialSpacesEtaleSite` is the direct image along the strict-model augmentation of the
restriction along the comparison. -/
def etaleAugmentationPushforwardIso :
    etaleSpacesPushforward A ≅ etaleStrictPushforwardFunctor A :=
  NatIso.ofComponents (fun F =>
    { hom := etaleAugmentationComparisonHom A F
      inv := etaleAugmentationComparisonInv A F
      hom_inv_id := etaleAugmentationComparisonHom_comp_inv F
      inv_hom_id := etaleAugmentationComparisonInv_comp_hom F })
    fun φ => etaleAugmentationComparisonHom_naturality φ

/-- The component at `F` of the isomorphism of direct images is the comparison at `F`. -/
theorem etaleAugmentationPushforwardIso_hom_app (F : Sheaf (topology A.left) (Type (u + 1))) :
    (etaleAugmentationPushforwardIso A).hom.app F = etaleAugmentationComparisonHom A F :=
  rfl

/-! ### The structure maps -/

open RingedToposHom in
/-- The counit of the Kan extension along the functor forgetting the degree, at `(n, W)`, is
natural in the sheaf on `const(X)_{spaces, étale}`. -/
theorem constToposHom_pushforward_map_comp_counit_app
    {G G' : Sheaf (topology ((Functor.const SimplexCategoryᵒᵖ).obj A.right)) (Type (u + 1))}
    (ψ : G ⟶ G') (n : SimplexCategory) (W : SpacesEtale B S hS A.right) :
    ((constToposHom A.right).pushforward.map ψ).hom.app (op W) ≫
        ((constToposHom A.right).adj.counit.app G').hom.app
          (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) =
      ((constToposHom A.right).adj.counit.app G).hom.app
          (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) ≫
        ψ.hom.app (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) :=
  (sheafHom_app_comp_eq ((constToposHom A.right).adj.counit.naturality ψ) _).trans
    (sheafHom_comp_app _ _ _)

/-- The triangle identity of the Kan extension adjunction along the functor forgetting the
degree, on sections over `W` and `(n, W)`. -/
theorem constToposHom_unit_app_comp_counit_app
    (P : Sheaf (SpacesEtale.topology B S hS A.right) (Type (u + 1))) (n : SimplexCategory)
    (W : SpacesEtale B S hS A.right) :
    ((constToposHom A.right).adj.unit.app P).hom.app (op W) ≫
        ((constToposHom A.right).adj.counit.app
          ((constToposHom A.right).inverseImage.obj P)).hom.app
          (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) = 𝟙 _ :=
  sheafHom_app_comp_eq ((constToposHom A.right).adj.left_triangle_components P) _

open RingedToposHom in
/-- The structure map of the augmentation of `SimplicialSpacesEtaleSite`, on underlying sheaves
of sets, is the unit of the Kan extension adjunction along the functor forgetting the degree
followed by the direct image of the structure map of base change along `a`. -/
theorem forgetFSharp_augmentationRingedToposHom :
    forgetFSharp (augmentationRingedToposHom (augmentationToConst A)) =
      (constToposHom A.right).adj.unit.app
          ((spacesEtaleRingedTopos B S hS A.right).forgetRing.obj
            (SpacesEtale.structureSheaf B S hS A.right)) ≫
        (constToposHom A.right).pushforward.map
          (forgetFSharp (ringedToposHom (augmentationToConst A))) :=
  (forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1}
    (constRingedToposHom A.right) (ringedToposHom (augmentationToConst A))).trans
    (congrArg (· ≫ (constToposHom A.right).pushforward.map
      (forgetFSharp (ringedToposHom (augmentationToConst A))))
      (forgetFSharp_constRingedToposHom A.right))

open RingedToposHom in
/-- The structure map of the augmentation of `SimplicialSpacesEtaleSite`, on sections over `W`,
is the unit of the Kan extension adjunction followed by the direct image of the structure map of
base change along `a`. -/
theorem forgetFSharp_augmentationRingedToposHom_app (W : SpacesEtale B S hS A.right) :
    (forgetFSharp (augmentationRingedToposHom (augmentationToConst A))).hom.app (op W) =
      ((constToposHom A.right).adj.unit.app
          ((spacesEtaleRingedTopos B S hS A.right).forgetRing.obj
            (SpacesEtale.structureSheaf B S hS A.right))).hom.app (op W) ≫
        ((constToposHom A.right).pushforward.map
          (forgetFSharp (ringedToposHom (augmentationToConst A)))).hom.app (op W) :=
  (congrArg (fun t => t.hom.app (op W)) (forgetFSharp_augmentationRingedToposHom (A := A))).trans
    (sheafHom_comp_app _ _ _)

variable (A) in
open RingedToposHom in
/-- The structure map of the augmentation of `SimplicialSpacesEtaleSite`, on underlying sheaves
of sets, read in the sheaves on `X_{spaces, étale}` of the strict model. -/
def etaleSpacesAugmentationSharpSet :
    @Quiver.Hom (Sheaf (C := Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (Type (u + 1))) _
      ((sheafCompose (SpacesEtale.topology B S hS A.right) (forget CommRingCat.{u + 1})).obj
        (SpacesEtale.structureSheaf B S hS A.right))
      ((etaleSpacesPushforward A).obj
        ((ringedTopos A.left).forgetRing.obj (ringedTopos A.left).O)) :=
  forgetFSharp (augmentationRingedToposHom (augmentationToConst A))

open RingedToposHom in
/-- The structure map of the augmentation of `SimplicialSpacesEtaleSite` followed by the leg of
the comparison in degree `n`, on sections over `W`, is the structure map of base change along `a`
on sections over `(n, W)`. -/
theorem etaleSpacesAugmentationSharpSet_app_comp_leg_app (n : SimplexCategory)
    (W : SpacesEtale B S hS A.right) :
    (etaleSpacesAugmentationSharpSet A).hom.app (op W) ≫
        (etaleAugmentationComparisonLeg A ((ringedTopos A.left).forgetRing.obj
          (ringedTopos A.left).O) n).hom.app (op W) =
      (forgetFSharp (ringedToposHom (augmentationToConst A))).hom.app
        (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) := by
  refine (congrArg (· ≫ _) (forgetFSharp_augmentationRingedToposHom_app W)).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (_ ≫ ·) (constToposHom_pushforward_map_comp_counit_app _ n W)).trans ?_
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) (constToposHom_unit_app_comp_counit_app _ n W)).trans ?_
  exact Category.id_comp _

/-- The structure map of base change along `a`, on sections over `(n, W)`, is the structure map of
the component of the strict model in degree `n` on sections over `W`. -/
theorem forgetFSharp_ringedToposHom_app_eq_etaleComponentStructureMap_app (n : SimplexCategory)
    (W : SpacesEtale B S hS A.right) :
    (RingedToposHom.forgetFSharp (ringedToposHom (augmentationToConst A))).hom.app
        (op ((degreeInclusion ((Functor.const _).obj A.right) n).obj W)) =
      (etaleComponentStructureMap A n).hom.app (op W) :=
  rfl

/-- The structure map of the augmentation of `SimplicialSpacesEtaleSite` followed by the leg of
the comparison in degree `n` is the structure map of the component of the strict model in degree
`n`. -/
theorem etaleSpacesAugmentationSharpSet_comp_leg (n : SimplexCategory) :
    etaleSpacesAugmentationSharpSet A ≫
        etaleAugmentationComparisonLeg A ((ringedTopos A.left).forgetRing.obj
          (ringedTopos A.left).O) n =
      etaleComponentStructureMap A n :=
  spacesEtaleSheafHom_ext fun W => (sheafHom_comp_app _ _ _).trans
    ((etaleSpacesAugmentationSharpSet_app_comp_leg_app n W).trans
      (forgetFSharp_ringedToposHom_app_eq_etaleComponentStructureMap_app n W))

/-- The structure map of the augmentation of `SimplicialSpacesEtaleSite` followed by the
comparison of the direct images is the structure map of the strict-model augmentation, on
underlying sheaves of sets. -/
theorem etaleSpacesAugmentationSharpSet_comp_hom :
    etaleSpacesAugmentationSharpSet A ≫
        etaleAugmentationComparisonHom A ((ringedTopos A.left).forgetRing.obj
          (ringedTopos A.left).O) =
      etaleAugmentationSharpSet A :=
  comp_etaleAugmentationComparisonHom_eq _ fun n =>
    (etaleSpacesAugmentationSharpSet_comp_leg n).trans
      (etaleAugmentationSharpSet_comp_projection A n).symm

/-- The structure map of the comparison of ringed topoi, on underlying sheaves of sets, is the
identity. -/
theorem forgetFSharp_etaleSiteComparisonRingedToposHom :
    RingedToposHom.forgetFSharp (etaleSiteComparisonRingedToposHom A) = 𝟙 _ :=
  rfl

/-- The structure map of the comparison of ringed topoi followed by the strict-model
augmentation, on underlying sheaves of sets, is the structure map of the strict-model
augmentation. -/
theorem forgetFSharp_etaleAugmentationRingedHom_comp :
    RingedToposHom.forgetFSharp (RingedToposHom.comp (X := ringedTopos A.left)
        (Y := (etaleSituation A).totalRingedTopos (etaleStructureSheaf A))
        (Z := spacesEtaleRingedTopos B S hS A.right)
        (etaleAugmentationRingedHom A) (etaleSiteComparisonRingedToposHom A)) =
      etaleAugmentationSharpSet A :=
  (RingedToposHom.forgetFSharp_comp.{u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1, u + 1,
    u + 1} (etaleAugmentationRingedHom A) (etaleSiteComparisonRingedToposHom A)).trans
    ((congrArg (_ ≫ ·) ((congrArg _ (forgetFSharp_etaleSiteComparisonRingedToposHom (A := A))).trans
      (CategoryTheory.Functor.map_id _ _))).trans
      ((Category.comp_id _).trans (forget_map_etaleAugmentationSharp A)))

variable (A) in
/-- **The two augmentations of `U_étale` agree**: the augmentation of `SimplicialSpacesEtaleSite`
is 2-isomorphic to the comparison of ringed topoi followed by the augmentation of the strict
model, `a' ≅ a ∘ c`. -/
def etaleAugmentationTwoIso :
    RingedToposHom.TwoIso (A := ringedTopos A.left) (B := spacesEtaleRingedTopos B S hS A.right)
      (augmentationRingedToposHom (augmentationToConst A))
      (RingedToposHom.comp (X := ringedTopos A.left)
        (Y := (etaleSituation A).totalRingedTopos (etaleStructureSheaf A))
        (Z := spacesEtaleRingedTopos B S hS A.right)
        (etaleAugmentationRingedHom A) (etaleSiteComparisonRingedToposHom A)) where
  e := etaleAugmentationPushforwardIso A
  commutes := etaleSpacesAugmentationSharpSet_comp_hom.trans
    (forgetFSharp_etaleAugmentationRingedHom_comp (A := A)).symm

end AlgebraicGeometry.Space

end
