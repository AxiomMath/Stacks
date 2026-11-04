module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Augmentation
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CommRingPullback
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ComponentPushforwardSections
public import StacksFrontier.CategoryTheory.Sites.Simplicial.Descent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationCechComplex
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationEqualizer

/-!
# The augmentation of a simplicial algebraic space as a morphism of ringed topoi

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S`, `U_étale` its small
étale site and `𝒪` its structure sheaf (Section 0DE7). The augmentation is a morphism of topoi
`a : Sh(U_étale) → Sh(X_étale)` (Lemma 0D70) whose inverse image has components `a_n⁻¹`. The maps
`a_n♯ : 𝒪_X → a_{n,*}𝒪_{U_n}`, pullback of global functions along the projections
`V ×_X U_n → V`, are compatible with the cosimplicial structure of Lemma 0D70, so they define a
map `a♯ : 𝒪_X → a_*𝒪` into the limit `a_*𝒪`. It is a map of sheaves of rings, because the
projection of `a_*𝒪` to degree zero, the leg of an equalizer, is injective and carries `a♯` to the
ring map `a_0♯`. This puts us in the situation of Section 0D9D and gives the morphism of ringed
topoi `a : (Sh(U_étale), 𝒪) → (Sh(X_étale), 𝒪_X)`.

## Main definitions

* `AlgebraicGeometry.Space.etaleComponentStructureSharp`: the map `a_n♯`.
* `AlgebraicGeometry.Space.etaleAugmentationSharp`: the map `a♯ : 𝒪_X ⟶ a_*𝒪`.
* `AlgebraicGeometry.Space.etaleRingedAugmentation`: the ringed augmentation of Section 0D9D.
* `AlgebraicGeometry.Space.etaleAugmentationRingedHom`: the morphism of ringed topoi `a`.
* `CategoryTheory.Sheaf.commRingHomOfInjective`: a map of underlying sheaves of sets is a map of
  sheaves of commutative rings once its composite with an injective ring map is.

## Main results

* `AlgebraicGeometry.Space.etaleComponentStructureMap_comp_transition`: the `a_n♯` form a cone
  over the cosimplicial sheaf of Lemma 0D70.
* `AlgebraicGeometry.Space.etaleAugmentationSharp_comp_projectionRing`: the component of `a♯` in
  degree `n` is `a_n♯`.

## Implementation notes

The source defines `a♯` in its inverse-image form `a⁻¹𝒪_X → 𝒪` from the `a_n♯` and passes to the
direct-image form by adjunction. The direct-image form is the one a morphism of ringed topoi
carries, and in it the condition that the `a_n♯` define a map is the cone condition over the
cosimplicial sheaf whose limit is `a_*𝒪`; the inverse-image form is then the adjoint of `a♯`.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D9D](https://stacks.math.columbia.edu/tag/0D9D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward

universe u

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget CommRingCat.{u})]

/-- A map between the underlying sheaves of sets of two sheaves of commutative rings `P` and `Q`
is a map of sheaves of commutative rings as soon as its composite with a map of sheaves of
commutative rings `Q ⟶ R` injective on sections is one. -/
def commRingHomOfInjective {P Q R : Sheaf J CommRingCat.{u}} (i : Q ⟶ R) (g : P ⟶ R)
    (f : (sheafCompose J (forget CommRingCat.{u})).obj P ⟶
      (sheafCompose J (forget CommRingCat.{u})).obj Q)
    (hi : ∀ U, Function.Injective (i.hom.app U))
    (h : ∀ U x, i.hom.app U (f.hom.app U x) = g.hom.app U x) : P ⟶ Q :=
  ObjectProperty.homMk
    { app := fun U => CommRingCat.ofHom
        { toFun := f.hom.app U
          map_one' := hi U ((h U (1 : P.obj.obj U)).trans ((map_one (g.hom.app U).hom).trans
            (map_one (i.hom.app U).hom).symm))
          map_mul' := fun x y => hi U ((h U (x * y)).trans ((map_mul (g.hom.app U).hom x y).trans
            ((congrArg₂ (· * ·) (h U x) (h U y)).symm.trans (map_mul (i.hom.app U).hom _ _).symm)))
          map_zero' := hi U ((h U (0 : P.obj.obj U)).trans ((map_zero (g.hom.app U).hom).trans
            (map_zero (i.hom.app U).hom).symm))
          map_add' := fun x y => hi U ((h U (x + y)).trans ((map_add (g.hom.app U).hom x y).trans
            ((congrArg₂ (· + ·) (h U x) (h U y)).symm.trans
              (map_add (i.hom.app U).hom _ _).symm))) }
      naturality := fun _ _ k => CommRingCat.hom_ext (RingHom.ext fun x =>
        ConcreteCategory.congr_hom (f.hom.naturality k) x) }

/-- The underlying map of sheaves of sets of `commRingHomOfInjective` is the given one. -/
theorem forget_map_commRingHomOfInjective {P Q R : Sheaf J CommRingCat.{u}} (i : Q ⟶ R)
    (g : P ⟶ R) (f : (sheafCompose J (forget CommRingCat.{u})).obj P ⟶
      (sheafCompose J (forget CommRingCat.{u})).obj Q)
    (hi : ∀ U, Function.Injective (i.hom.app U))
    (h : ∀ U x, i.hom.app U (f.hom.app U x) = g.hom.app U x) :
    (sheafCompose J (forget CommRingCat.{u})).map (commRingHomOfInjective i g f hi h) = f :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ => ConcreteCategory.hom_ext _ _ fun _ => by
    dsimp [commRingHomOfInjective]
    rfl))

omit [J.HasSheafCompose (forget CommRingCat.{u})] in
/-- The components of an isomorphism of sheaves of commutative rings are injective. -/
theorem injective_hom_app_of_iso {P Q : Sheaf J CommRingCat.{u}} (e : P ≅ Q) (U : Cᵒᵖ) :
    Function.Injective (e.hom.hom.app U) := fun x y hxy => by
  have h := fun z => ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg InducedCategory.Hom.hom e.hom_inv_id) U) z
  exact (h x).symm.trans ((congrArg (e.inv.hom.app U) hxy).trans (h y))

omit [J.HasSheafCompose (forget CommRingCat.{u})] in
/-- A composite of maps of sheaves of commutative rings acts on a section by applying the two maps
in turn. -/
theorem commRing_comp_hom_app_apply {P Q R : Sheaf J CommRingCat.{u}} (a : P ⟶ Q) (b : Q ⟶ R)
    (U : Cᵒᵖ) (x : P.obj.obj U) : (a ≫ b).hom.app U x = b.hom.app U (a.hom.app U x) :=
  rfl

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

open EtaleComponent SimplicialSiteSituation SimplicialSiteSituation.Augmentation

/-- The projection `V ×_X U_n ⟶ V` from the realization of the degree-`n` base change of an
object `V` étale over `X`. -/
abbrev etaleBaseProjection (n : SimplexCategory) (V : SpacesEtale B S hS A.right) :
    (realize (baseObj n V)).obj.left ⟶ V.obj.left :=
  (spacesBaseChange B S hS (A.hom.app (op n))).projection.app V

variable {A} in
/-- Realizing the image of a morphism of `X_{spaces, étale}` in degree `n` of `U_étale` gives the
base change of that morphism, compatibly with the projections. -/
theorem etaleTotalToSpaces_map_totalComponentSiteFunctor_comp (n : SimplexCategory)
    {V W : SpacesEtale B S hS A.right} (f : V ⟶ W) :
    (etaleTotalToSpaces A).map ((etaleAugmentation A).totalComponentSiteFunctor n |>.map f) ≫
        etaleBaseProjection A n W =
      etaleBaseProjection A n V ≫ (SpacesEtale.toSpaces B S hS A.right).map f := by
  have h := (etaleTotalToSpacesιIso A (op n)).hom.naturality
    (((etaleAugmentation A).componentSiteFunctor n).map f)
  have h' :
      (etaleTotalToSpaces A).map ((etaleAugmentation A).totalComponentSiteFunctor n |>.map f) =
      (SpacesEtale.toSpaces B S hS _).map ((realizeFunctor n).map
        ((transition (SimplexCategory.const (SimplexCategory.mk 0) n 0)).map
          (augmentationFunctor.map f))) :=
    (Category.comp_id _).symm.trans (h.trans (Category.id_comp _))
  rw [h', transition_map_augmentationFunctor]
  exact (spacesBaseChange B S hS (A.hom.app (op n))).projection.naturality f

/-- **The structure map `a_n♯` of the augmentation in degree `n`.** For `V` étale over `X`, the
pullback `Γ(V, 𝒪_V) ⟶ Γ(V ×_X U_n, 𝒪)` of global functions along the projection, as a map from
`𝒪_X` to the direct image of `𝒪` along the site functor `V ↦ V ×_X U_n` of degree `n`. -/
def etaleComponentStructureSharp (n : SimplexCategory) :
    SpacesEtale.structureSheaf B S hS A.right ⟶
      (((etaleAugmentation A).totalComponentSiteFunctor n).sheafPushforwardContinuous
        CommRingCat.{u + 1} (SpacesEtale.topology B S hS A.right)
        (etaleSimplicialSite A).totalTopology).obj (etaleStructureSheaf A) :=
  ObjectProperty.homMk
    { app := fun V => (globalFunctionsPresheaf B S hS).map (etaleBaseProjection A n V.unop).op
      naturality := fun V W g => by
        refine ((globalFunctionsPresheaf B S hS).map_comp _ _).symm.trans ?_
        have e : ((((etaleAugmentation A).totalComponentSiteFunctor n).sheafPushforwardContinuous
            CommRingCat.{u + 1} (SpacesEtale.topology B S hS A.right)
            (etaleSimplicialSite A).totalTopology).obj (etaleStructureSheaf A)).obj.map g =
            (globalFunctionsPresheaf B S hS).map ((etaleTotalToSpaces A).map
              (((etaleAugmentation A).totalComponentSiteFunctor n).map g.unop)).op := rfl
        rw [e]
        refine Eq.trans ?_ ((globalFunctionsPresheaf B S hS).map_comp _ _)
        congr 1
        apply Quiver.Hom.unop_inj
        simp only [Functor.op_map]
        exact (etaleTotalToSpaces_map_totalComponentSiteFunctor_comp (A := A) n g.unop).symm }

/-- The sections of `a_n♯` over `V` are the pullback of global functions along the projection
`V ×_X U_n ⟶ V`. -/
@[simp] theorem etaleComponentStructureSharp_app (n : SimplexCategory)
    (V : (SpacesEtale B S hS A.right)ᵒᵖ) :
    (etaleComponentStructureSharp A n).hom.app V =
      (globalFunctionsPresheaf B S hS).map (etaleBaseProjection A n V.unop).op :=
  rfl

variable {A} in
/-- Realizing the cartesian arrow over `φ : [m] → [n]` from the degree-`n` base change of `W` to
its degree-`m` base change, and projecting to `W`, is the projection in degree `n`. -/
theorem etaleTotalToSpaces_map_transitionArrow_comp {m n : SimplexCategory} (φ : m ⟶ n)
    (W : SpacesEtale B S hS A.right)
    (h : ((etaleAugmentation A).componentSiteFunctor n).obj W =
      ((etaleSimplicialSite A).underlying.map φ).toFunctor.obj
        (((etaleAugmentation A).componentSiteFunctor m).obj W)) :
    (etaleTotalToSpaces A).map
        ((Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n)).map
            (eqToHom h) ≫
          (continuousInclusionTransition (etaleSimplicialSite A) φ).app
            (((etaleAugmentation A).componentSiteFunctor m).obj W)) ≫
        etaleBaseProjection A m W =
      etaleBaseProjection A n W := by
  have e₀ : (etaleTotalToSpaces A).map
      ((Pseudofunctor.CoGrothendieck.ι (etaleSimplicialSite A).totalPseudofunctor (op n)).map
        (eqToHom h)) = 𝟙 _ := by
    have hn := (etaleTotalToSpacesιIso A (op n)).hom.naturality (eqToHom h)
    exact ((Category.comp_id _).symm.trans (hn.trans ((Category.id_comp _).trans
      (eqToHom_map _ h)))).trans rfl
  have e : (etaleTotalToSpaces A).map ((continuousInclusionTransition (etaleSimplicialSite A) φ).app
      (((etaleAugmentation A).componentSiteFunctor m).obj W)) = comparison φ (baseObj m W) := by
    dsimp only [etaleTotalToSpaces, continuousInclusionTransition]
    exact Pseudofunctor.CoGrothendieck.functorFrom_map_ιNatTrans_app _ _ _ _ φ.op _
  refine (congrArg (· ≫ etaleBaseProjection A m W) (Functor.map_comp _ _ _)).trans ?_
  refine (congrArg (fun t => (t ≫ _) ≫ etaleBaseProjection A m W) e₀).trans ?_
  refine (congrArg (· ≫ etaleBaseProjection A m W) (Category.id_comp _)).trans ?_
  refine (congrArg (· ≫ etaleBaseProjection A m W) e).trans ?_
  exact comparison_inl_fst φ W

/-- The underlying map of sheaves of sets of `a_n♯`, into the degree-`n` term
`a_{n,*}(𝒪|_{U_n})` of the cosimplicial sheaf whose limit is `a_*𝒪` (Stacks 0D70). -/
def etaleComponentStructureMap (n : SimplexCategory) :
    (sheafCompose (SpacesEtale.topology B S hS A.right) (forget CommRingCat.{u + 1})).obj
        (SpacesEtale.structureSheaf B S hS A.right) ⟶
      (componentPushforward (etaleSimplicialSite A).situation (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) n).obj
        ((sheafCompose (etaleSimplicialSite A).totalTopology (forget CommRingCat.{u + 1})).obj
          (etaleStructureSheaf A)) :=
  ObjectProperty.homMk ((sheafCompose (SpacesEtale.topology B S hS A.right)
    (forget CommRingCat.{u + 1})).map (etaleComponentStructureSharp A n)).hom

omit A in
/-- A presheaf of commutative rings, read on underlying sets, takes a commutative triangle to a
commutative triangle. -/
theorem forget_map_map_apply_of_comp_eq {C : Type*} [Category C] (G : Cᵒᵖ ⥤ CommRingCat.{u + 1})
    {X Y Z : C} (p : X ⟶ Y) (q : Z ⟶ X) (r : Z ⟶ Y) (h : q ≫ p = r)
    (s : (forget CommRingCat.{u + 1}).obj (G.obj (op Y))) :
    (forget CommRingCat.{u + 1}).map (G.map q.op)
        ((forget CommRingCat.{u + 1}).map (G.map p.op) s) =
      (forget CommRingCat.{u + 1}).map (G.map r.op) s := by
  subst h
  rw [op_comp, Functor.map_comp, Functor.map_comp]
  rfl

/-- On a section over `W`, `a_n♯` is pullback of global functions along the projection
`W ×_X U_n ⟶ W`. -/
theorem etaleComponentStructureMap_app (n : SimplexCategory)
    (W : (SpacesEtale B S hS A.right)ᵒᵖ) :
    (etaleComponentStructureMap A n).hom.app W =
      (forget CommRingCat.{u + 1}).map
        ((globalFunctionsPresheaf B S hS).map (etaleBaseProjection A n W.unop).op) :=
  rfl

/-- The restriction maps of the underlying sheaf of sets of `𝒪` are pullback of global functions
along the realization. -/
theorem forget_etaleStructureSheaf_map
    {x y : (Pseudofunctor.CoGrothendieck (etaleSimplicialSite A).totalPseudofunctor)ᵒᵖ}
    (f : x ⟶ y) :
    ((sheafCompose (etaleSimplicialSite A).totalTopology (forget CommRingCat.{u + 1})).obj
        (etaleStructureSheaf A)).obj.map f =
      (forget CommRingCat.{u + 1}).map
        ((globalFunctionsPresheaf B S hS).map ((etaleTotalToSpaces A).map f.unop).op) :=
  rfl

/-- Composing `a_n♯` with a map out of its target acts on a section by applying that map. -/
theorem etaleComponentStructureMap_comp_apply (n : SimplexCategory)
    {Y : Sheaf (SpacesEtale.topology B S hS A.right) (Type (u + 1))}
    (T : (componentPushforward (etaleSimplicialSite A).situation
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A) n).obj
        ((sheafCompose (etaleSimplicialSite A).totalTopology (forget CommRingCat.{u + 1})).obj
          (etaleStructureSheaf A)) ⟶ Y)
    (W : SpacesEtale B S hS A.right)
    (s : (SpacesEtale.structureSheaf B S hS A.right).obj.obj (op W)) :
    (etaleComponentStructureMap A n ≫ T).hom.app (op W) s =
      T.hom.app (op W) ((etaleComponentStructureMap A n).hom.app (op W) s) :=
  rfl

/-- The transition of the cosimplicial sheaf of Stacks 0D70 sends the section of `a_m♯` to that
of `a_n♯`. -/
theorem etaleComponentStructureMap_transition_apply {m n : SimplexCategory} (φ : m ⟶ n)
    (W : SpacesEtale B S hS A.right)
    (s : (SpacesEtale.structureSheaf B S hS A.right).obj.obj (op W)) :
    ((componentPushforwardTransition (etaleSimplicialSite A).situation
        (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) φ).app
        ((sheafCompose (etaleSimplicialSite A).totalTopology (forget CommRingCat.{u + 1})).obj
          (etaleStructureSheaf A))).hom.app (op W)
        ((etaleComponentStructureMap A m).hom.app (op W) s) =
      (etaleComponentStructureMap A n).hom.app (op W) s := by
  refine (ConcreteCategory.congr_hom
    (SimplicialSite.ContinuousAugmentation.componentPushforwardTransition_app_hom_app
      (etaleAugmentation A) φ
      ((sheafCompose (etaleSimplicialSite A).totalTopology (forget CommRingCat.{u + 1})).obj
        (etaleStructureSheaf A)) W) _).trans ?_
  rw [forget_etaleStructureSheaf_map, etaleComponentStructureMap_app,
    etaleComponentStructureMap_app]
  exact forget_map_map_apply_of_comp_eq (globalFunctionsPresheaf B S hS) _ _ _
    (etaleTotalToSpaces_map_transitionArrow_comp φ W _) s

/-- The maps `a_n♯` are compatible with the cosimplicial structure of Stacks 0D70: they form a
cone over the cosimplicial sheaf whose limit is `a_*𝒪`. -/
theorem etaleComponentStructureMap_comp_transition {m n : SimplexCategory} (φ : m ⟶ n) :
    etaleComponentStructureMap A m ≫
        (componentPushforwardTransition (etaleSimplicialSite A).situation
          (Cat.of (SpacesEtale B S hS A.right))
          (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) φ).app
          ((sheafCompose (etaleSimplicialSite A).totalTopology (forget CommRingCat.{u + 1})).obj
            (etaleStructureSheaf A)) =
      etaleComponentStructureMap A n := by
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext W
  induction W with | op W => ?_
  exact ConcreteCategory.hom_ext _ _ fun s =>
    (etaleComponentStructureMap_comp_apply A m _ W s).trans
      (etaleComponentStructureMap_transition_apply A φ W s)

/-- The maps `a_n♯`, as a cone over the cosimplicial sheaf of Stacks 0D70 whose limit is
`a_*𝒪`. -/
def etaleStructureCone :
    Cone (pushforwardDiagram (etaleSimplicialSite A).situation
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A)
      ((sheafCompose (etaleSimplicialSite A).totalTopology (forget CommRingCat.{u + 1})).obj
        (etaleStructureSheaf A))) where
  pt := (sheafCompose (SpacesEtale.topology B S hS A.right) (forget CommRingCat.{u + 1})).obj
    (SpacesEtale.structureSheaf B S hS A.right)
  π :=
    { app := fun n => etaleComponentStructureMap A n
      naturality := fun {_ _} φ =>
        (Category.id_comp _).trans (etaleComponentStructureMap_comp_transition A φ).symm }

/-- The underlying map of sheaves of sets of `a♯ : 𝒪_X ⟶ a_*𝒪`: the map into the limit of
Stacks 0D70, compatibility (3), given in degree `n` by `a_n♯`. -/
def etaleAugmentationSharpSet :
    (sheafCompose (SpacesEtale.topology B S hS A.right) (forget CommRingCat.{u + 1})).obj
        (SpacesEtale.structureSheaf B S hS A.right) ⟶
      (etaleAugmentationMorphism A).pushforward.obj
        ((sheafCompose (etaleSimplicialSite A).totalTopology (forget CommRingCat.{u + 1})).obj
          (etaleStructureSheaf A)) :=
  limit.lift _ (etaleStructureCone A)

/-- The projection of `a♯` to degree `n` is `a_n♯`. -/
theorem etaleAugmentationSharpSet_comp_projection (n : SimplexCategory) :
    etaleAugmentationSharpSet A ≫
        pushforwardProjection (etaleSimplicialSite A).situation
          (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
          (etaleAugmentation A)
          ((sheafCompose (etaleSimplicialSite A).totalTopology (forget CommRingCat.{u + 1})).obj
            (etaleStructureSheaf A)) n =
      etaleComponentStructureMap A n :=
  limit.lift_π _ n

/-- The site functor `V ↦ V ×_X U_n` of degree `n` is continuous. -/
instance etaleTotalComponentSiteFunctor_isContinuous (n : SimplexCategory) :
    Functor.IsContinuous (C := SpacesEtale B S hS A.right)
      ((etaleAugmentation A).totalComponentSiteFunctor n)
      (SpacesEtale.topology B S hS A.right) (etaleSimplicialSite A).totalTopology :=
  (etaleAugmentation A).totalComponentSiteFunctor_isContinuous n

/-- The direct image of sheaves of sets along the site functor of degree `n` preserves finite
products. -/
instance (n : SimplexCategory) : PreservesFiniteProducts
    (((etaleAugmentation A).totalComponentSiteFunctor n).sheafPushforwardContinuous
      (Type (u + 1)) (SpacesEtale.topology B S hS A.right)
      (etaleSimplicialSite A).totalTopology) := by
  have := Functor.preservesLimits_sheafPushforwardContinuous
    ((etaleAugmentation A).totalComponentSiteFunctor n) (Type (u + 1))
    (SpacesEtale.topology B S hS A.right) (etaleSimplicialSite A).totalTopology
  infer_instance

/-- The direct image along the augmentation of degree `n` of the restriction to degree `n` is the
direct image along the site functor `V ↦ V ×_X U_n` of degree `n`. -/
def etaleComponentPushforwardIso (n : SimplexCategory) :
    componentPushforward (etaleSimplicialSite A).situation (Cat.of (SpacesEtale B S hS A.right))
        (SpacesEtale.topology B S hS A.right) (etaleAugmentation A) n ≅
      ((etaleAugmentation A).totalComponentSiteFunctor n).sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology B S hS A.right)
        (etaleSimplicialSite A).totalTopology :=
  Functor.isoWhiskerLeft ((etaleSimplicialSite A).situation.restrict n)
      ((etaleAugmentation A).componentAugmentationPushforwardIso n) ≪≫
    (etaleAugmentation A).componentRestrictionPushforwardIso n

/-- The projection of `a_*F` to degree `n`, into the direct image along the site functor
`V ↦ V ×_X U_n`. -/
def etaleProjection (n : SimplexCategory) :
    (etaleAugmentationMorphism A).pushforward ⟶
      ((etaleAugmentation A).totalComponentSiteFunctor n).sheafPushforwardContinuous
        (Type (u + 1)) (SpacesEtale.topology B S hS A.right)
        (etaleSimplicialSite A).totalTopology :=
  pushforwardProjectionNatTrans (etaleSimplicialSite A).situation
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A) n ≫ (etaleComponentPushforwardIso A n).hom

/-- The projection of `a_*𝒪` to degree `n`, as a map of sheaves of commutative rings into the
direct image of `𝒪` along the site functor `V ↦ V ×_X U_n`. -/
def etaleProjectionRing (n : SimplexCategory) :
    (pushforwardCommRingFunctor (etaleAugmentationMorphism A)).obj (etaleStructureSheaf A) ⟶
      (((etaleAugmentation A).totalComponentSiteFunctor n).sheafPushforwardContinuous
        CommRingCat.{u + 1} (SpacesEtale.topology B S hS A.right)
        (etaleSimplicialSite A).totalTopology).obj (etaleStructureSheaf A) :=
  pullbackCommRingSheafMapOfNatTrans (SpacesEtale.topology B S hS A.right)
      (etaleProjection A n) (etaleStructureSheaf A) ≫
    (restrictionCommRingIso (SpacesEtale.topology B S hS A.right)
      (etaleSimplicialSite A).totalTopology _ (etaleStructureSheaf A)).hom

/-- The projection of `a_*𝒪` to degree zero is injective on sections: `a_*𝒪` is the equalizer of
the two vertex maps of Stacks 0D70, compatibility (3), with the projection as its leg. -/
theorem etaleProjection_zero_injective
    (F : Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)))
    (U : (SpacesEtale B S hS A.right)ᵒᵖ) :
    Function.Injective ((etaleProjection A (SimplexCategory.mk 0)).app F |>.hom.app U) := by
  have hm : Mono (pushforwardProjection (etaleSimplicialSite A).situation
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A) F (SimplexCategory.mk 0)) :=
    Fork.IsLimit.mono (totalPushforwardForkIsLimit (etaleSimplicialSite A).situation
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A) F)
  have hm' : Mono ((pushforwardProjection (etaleSimplicialSite A).situation
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A) F (SimplexCategory.mk 0)).hom.app U) :=
    (NatTrans.mono_iff_mono_app _).1 inferInstance U
  have hi : Function.Injective
      (((etaleComponentPushforwardIso A (SimplexCategory.mk 0)).hom.app F).hom.app U) :=
    fun x y hxy => by
      have h := fun z => ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg
        InducedCategory.Hom.hom
          ((etaleComponentPushforwardIso A (SimplexCategory.mk 0)).hom_inv_id_app F)) U) z
      exact (h x).symm.trans ((congrArg _ hxy).trans (h y))
  exact hi.comp ((mono_iff_injective _).1 hm')

/-- On sections, the ring-level projection of `a_*𝒪` to degree `n` is the projection of the
underlying sheaf of sets. -/
theorem etaleProjectionRing_apply (n : SimplexCategory) (U : (SpacesEtale B S hS A.right)ᵒᵖ)
    (x : ((pushforwardCommRingFunctor (etaleAugmentationMorphism A)).obj
      (etaleStructureSheaf A)).obj.obj U) :
    (etaleProjectionRing A n).hom.app U x =
      ((etaleProjection A n).app ((sheafCompose (etaleSimplicialSite A).totalTopology
        (forget CommRingCat.{u + 1})).obj (etaleStructureSheaf A))).hom.app U x :=
  rfl

/-- The ring-level projection of `a_*𝒪` to degree zero is injective on sections. -/
theorem etaleProjectionRing_zero_injective (U : (SpacesEtale B S hS A.right)ᵒᵖ) :
    Function.Injective ((etaleProjectionRing A (SimplexCategory.mk 0)).hom.app U) :=
  fun x y hxy => etaleProjection_zero_injective A _ U
    (((etaleProjectionRing_apply A _ U x).symm.trans hxy).trans (etaleProjectionRing_apply A _ U y))

omit A in
/-- A composite of maps of sheaves of sets acts on a section by applying the two maps in turn. -/
theorem sheaf_comp_hom_app_apply {C : Type*} [Category C] {J : GrothendieckTopology C}
    {P Q R : Sheaf J (Type (u + 1))} (a : P ⟶ Q) (b : Q ⟶ R) (U : Cᵒᵖ) (x : P.obj.obj U) :
    (a ≫ b).hom.app U x = b.hom.app U (a.hom.app U x) :=
  rfl

/-- **The structure map `a♯ : 𝒪_X ⟶ a_*𝒪` of the augmentation (Section 0DE7).** The map of
sheaves of commutative rings whose components in the degrees `n` of Stacks 0D70 are the maps
`a_n♯ : 𝒪_X ⟶ a_{n,*}𝒪_{U_n}`: it is the map into the limit given by the `a_n♯`, which is a ring
map because its projection to degree zero, which is injective, is the ring map `a_0♯`. -/
def etaleAugmentationSharp :
    SpacesEtale.structureSheaf B S hS A.right ⟶
      (pushforwardCommRingFunctor (etaleAugmentationMorphism A)).obj (etaleStructureSheaf A) :=
  Sheaf.commRingHomOfInjective (etaleProjectionRing A (SimplexCategory.mk 0))
    (etaleComponentStructureSharp A (SimplexCategory.mk 0)) (etaleAugmentationSharpSet A)
    (etaleProjectionRing_zero_injective A)
    (fun U x => (etaleProjectionRing_apply A _ U _).trans
      ((sheaf_comp_hom_app_apply _ _ U x).symm.trans
        (ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg InducedCategory.Hom.hom
          (etaleAugmentationSharpSet_comp_projection A (SimplexCategory.mk 0))) U) x)))

/-- The underlying map of sheaves of sets of `a♯` is the map into the limit of Stacks 0D70 given
by the `a_n♯`. -/
theorem forget_map_etaleAugmentationSharp :
    (sheafCompose (SpacesEtale.topology B S hS A.right) (forget CommRingCat.{u + 1})).map
        (etaleAugmentationSharp A) = etaleAugmentationSharpSet A :=
  Sheaf.forget_map_commRingHomOfInjective _ _ _ _ _

/-- **`a♯` is given by `a_n♯` on `X_n`.** The projection of `a♯ : 𝒪_X ⟶ a_*𝒪` to the simplicial
degree `n` is the structure map `a_n♯ : 𝒪_X ⟶ a_{n,*}𝒪_{U_n}`, pullback of global functions along
`V ×_X U_n ⟶ V`. -/
theorem etaleAugmentationSharp_comp_projectionRing (n : SimplexCategory) :
    etaleAugmentationSharp A ≫ etaleProjectionRing A n = etaleComponentStructureSharp A n := by
  refine Sheaf.hom_ext (NatTrans.ext (funext fun U => CommRingCat.hom_ext
    (RingHom.ext fun x => ?_)))
  refine (Sheaf.commRing_comp_hom_app_apply _ _ U x).trans
    ((etaleProjectionRing_apply A n U _).trans ?_)
  exact (sheaf_comp_hom_app_apply (etaleAugmentationSharpSet A)
      (pushforwardProjection (etaleSimplicialSite A).situation
        (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
        (etaleAugmentation A)
        ((sheafCompose (etaleSimplicialSite A).totalTopology (forget CommRingCat.{u + 1})).obj
          (etaleStructureSheaf A)) n) U x).symm.trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app (congrArg InducedCategory.Hom.hom
      (etaleAugmentationSharpSet_comp_projection A n)) U) x)

/-- **Section 0DE7, the ringed augmentation.** The structure sheaf `𝒪` of `U` on `U_étale`, the
structure sheaf `𝒪_X` of `X_{spaces, étale}` and `a♯ : 𝒪_X ⟶ a_*𝒪`: the situation of
Section 0D9D for the augmentation `a : Sh(U_étale) ⟶ Sh(X_étale)` of Lemma 0D70. -/
def etaleRingedAugmentation :
    SimplicialSiteSituation.RingedAugmentation (etaleSituation A)
      (Cat.of (SpacesEtale B S hS A.right)) (SpacesEtale.topology B S hS A.right)
      (etaleAugmentation A) where
  O := etaleStructureSheaf A
  OD := SpacesEtale.structureSheaf B S hS A.right
  aSharp := etaleAugmentationSharp A

/-- **Section 0DE7, the morphism of ringed topoi `a : (Sh(U_étale), 𝒪) ⟶ (Sh(X_étale), 𝒪_X)`.**
Its underlying morphism of topoi is the augmentation `a` of Lemma 0D70 and its structure map is
`a♯`. -/
abbrev etaleAugmentationRingedHom :
    RingedToposHom ((etaleSituation A).totalRingedTopos (etaleStructureSheaf A))
      (etaleRingedAugmentation A).augmentationRingedTopos :=
  (etaleRingedAugmentation A).totalRingedHom

end AlgebraicGeometry.Space

end
