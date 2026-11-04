module

public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleSite
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalContinuousMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.Augmentation
import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheaf
import StacksFrontier.CategoryTheory.Sites.MorphismOfSitesLimits
import StacksCore.Tactic.StacksAttribute

/-!
# The morphism of small étale topoi of a morphism of simplicial algebraic spaces

Let `h : X → Y` be a morphism of simplicial algebraic spaces over a scheme `S` (Section 0DE7).
The morphisms of sites `(h_n)_{spaces, étale} : X_{n, spaces, étale} → Y_{n, spaces, étale}` of
Lemma 03G2, base change along `h_n`, commute with the transitions, so by Lemma 0D96 they give a
morphism of small étale topoi `h_étale : Sh(X_étale) → Sh(Y_étale)` whose components are the
`(h_n)_{spaces, étale}`. With `h♯ : 𝒪_Y → h_{étale,*}𝒪_X` given on `Y_n` by
`h_n♯ : 𝒪_{Y_n} → h_{n,*}𝒪_{X_n}` it is a morphism of ringed topoi.

The small étale sites are those of the strict model of
`StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSpaces.EtaleComponents`, built from augmented
simplicial algebraic spaces; a morphism of augmented simplicial algebraic spaces `X → Y` acts
degreewise on formal base changes by base change along `h₋₁` and the `h_m`, with comparison maps
`mapComparison` exhibiting the realizations as fibre products.

## Main definitions

* `AlgebraicGeometry.Space.EtaleComponent.mapFunctor`: base change along `h_n` on the strict
  components.
* `AlgebraicGeometry.Space.etaleSimplicialSiteMorphism`: the morphism of simplicial sites.
* `AlgebraicGeometry.Space.etaleMorphismOfTopoi`: the morphism of topoi `h_étale`.
* `AlgebraicGeometry.Space.etaleMorphismStructureSharp` and
  `AlgebraicGeometry.Space.etaleMorphismRingedHom`: `h♯` and the morphism of ringed topoi.
* `AlgebraicGeometry.Space.augmentFinal`, `AlgebraicGeometry.Space.simplicialEtaleMorphismOfTopoi`
  and `AlgebraicGeometry.Space.simplicialEtaleRingedHom`: the same for a morphism of simplicial
  algebraic spaces, through their augmentations towards the final algebraic space.

## Main results

* `AlgebraicGeometry.Space.EtaleComponent.transition_comp_mapFunctor`: base change along `h`
  commutes strictly with the transitions.
* `AlgebraicGeometry.Space.EtaleComponent.mapFunctor_isMorphismOfSites`: it is a morphism of
  sites.
* `AlgebraicGeometry.Space.etaleMorphismComponentPushforwardIso`: the components of `h_étale`
  are the morphisms of topoi of base change along the `h_n`.

## Implementation notes

The small étale site of a simplicial algebraic space is built from an augmentation. A simplicial
algebraic space always has its augmentation towards the final algebraic space, and a morphism of
simplicial algebraic spaces is a morphism of these augmented simplicial algebraic spaces, so the
constructions for a morphism of simplicial algebraic spaces are those for that morphism of
augmented ones.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 0D96](https://stacks.math.columbia.edu/tag/0D96)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Iterated base change -/

section DoubleBaseChange

variable {X Y Z Z' : AlgebraicSpaces B S hS}

/-- For a commutative square `q ≫ p = s ≫ r`, the canonical morphism from the iterated base change
of `V` along `p` and then `q` to its base change along `r`, lying over `s`. -/
def doubleBaseChangeComparison (p : X ⟶ Y) (q : Z ⟶ X) (r : Z' ⟶ Y) (s : Z ⟶ Z')
    (e : q ≫ p = s ≫ r) (V : SpacesEtale B S hS Y) :
    ((spacesBaseChange B S hS q).functor.obj
        ((spacesBaseChange B S hS p).functor.obj V)).obj.left ⟶
      ((spacesBaseChange B S hS r).functor.obj V).obj.left :=
  ((spacesBaseChange B S hS r).isPullback V).lift
    ((spacesBaseChange B S hS q).projection.app _ ≫ (spacesBaseChange B S hS p).projection.app V)
    (((spacesBaseChange B S hS q).functor.obj
      ((spacesBaseChange B S hS p).functor.obj V)).obj.hom ≫ s) (by
    rw [Category.assoc, ((spacesBaseChange B S hS p).isPullback V).w,
      ← Category.assoc, ((spacesBaseChange B S hS q).isPullback _).w, Category.assoc, e,
      Category.assoc])

/-- The comparison of an iterated base change, followed by the projection to `V`, is the composite
of the two projections. -/
@[reassoc (attr := simp)]
theorem doubleBaseChangeComparison_projection (p : X ⟶ Y) (q : Z ⟶ X) (r : Z' ⟶ Y) (s : Z ⟶ Z')
    (e : q ≫ p = s ≫ r) (V : SpacesEtale B S hS Y) :
    doubleBaseChangeComparison p q r s e V ≫ (spacesBaseChange B S hS r).projection.app V =
      (spacesBaseChange B S hS q).projection.app _ ≫
        (spacesBaseChange B S hS p).projection.app V :=
  IsPullback.lift_fst _ _ _ _

/-- The comparison of an iterated base change lies over `s`. -/
@[reassoc (attr := simp)]
theorem doubleBaseChangeComparison_hom (p : X ⟶ Y) (q : Z ⟶ X) (r : Z' ⟶ Y) (s : Z ⟶ Z')
    (e : q ≫ p = s ≫ r) (V : SpacesEtale B S hS Y) :
    doubleBaseChangeComparison p q r s e V ≫ ((spacesBaseChange B S hS r).functor.obj V).obj.hom =
      ((spacesBaseChange B S hS q).functor.obj
        ((spacesBaseChange B S hS p).functor.obj V)).obj.hom ≫ s :=
  IsPullback.lift_snd _ _ _ _

/-- The comparison square of an iterated base change is cartesian, by the pasting lemma. -/
theorem isPullback_doubleBaseChangeComparison (p : X ⟶ Y) (q : Z ⟶ X) (r : Z' ⟶ Y)
    (s : Z ⟶ Z') (e : q ≫ p = s ≫ r) (V : SpacesEtale B S hS Y) :
    IsPullback (doubleBaseChangeComparison p q r s e V)
      ((spacesBaseChange B S hS q).functor.obj
        ((spacesBaseChange B S hS p).functor.obj V)).obj.hom
      ((spacesBaseChange B S hS r).functor.obj V).obj.hom s := by
  refine IsPullback.of_right ?_ (doubleBaseChangeComparison_hom p q r s e V)
    ((spacesBaseChange B S hS r).isPullback V)
  rw [doubleBaseChangeComparison_projection, ← e]
  exact ((spacesBaseChange B S hS q).isPullback _).paste_horiz
    ((spacesBaseChange B S hS p).isPullback V)

end DoubleBaseChange

/-! ### The functors between the components -/

variable {A A' : SimplicialObject.Augmented (AlgebraicSpaces B S hS)}

namespace EtaleComponent

/-- The square `A_n → A'_n → A'_{-1}` and `A_n → A_{-1} → A'_{-1}` of a morphism of augmented
simplicial algebraic spaces commutes. -/
theorem hom_app_comp_right (h : A ⟶ A') (n : SimplexCategory) :
    A.hom.app (op n) ≫ h.right = h.left.app (op n) ≫ A'.hom.app (op n) :=
  (NatTrans.congr_app h.w (op n)).symm

/-- Base change of formal base changes along a morphism `h : A ⟶ A'` of augmented simplicial
algebraic spaces: an object étale over `A'_{-1}` goes to its base change to `A_{-1}`, and an
object étale over `A'_m` to its base change to `A_m`. -/
@[reducible] def Index.map (h : A ⟶ A') {n : SimplexCategory} : Index A' n → Index A n
  | .inl V => .inl ((spacesBaseChange B S hS h.right).functor.obj V)
  | .inr ⟨m, φ, V⟩ => .inr ⟨m, φ, (spacesBaseChange B S hS (h.left.app (op m))).functor.obj V⟩

/-- Base change along `h` commutes with pushing a formal base change along `ψ`. -/
theorem Index.map_push (h : A ⟶ A') {n k : SimplexCategory} (ψ : n ⟶ k) (x : Index A' n) :
    (x.push ψ).map h = (x.map h).push ψ := by
  rcases x with V | ⟨m, φ, V⟩ <;> rfl

/-- The canonical morphism from the realization of `x.map h` to the realization of `x`, lying over
`h_n : A_n → A'_n`. -/
def mapComparison (h : A ⟶ A') {n : SimplexCategory} :
    (x : Index A' n) → (realize (x.map h)).obj.left ⟶ (realize x).obj.left
  | .inl V => doubleBaseChangeComparison h.right (A.hom.app (op n)) (A'.hom.app (op n))
      (h.left.app (op n)) (hom_app_comp_right h n) V
  | .inr ⟨m, φ, V⟩ => doubleBaseChangeComparison (h.left.app (op m))
      (A.left.map (simplexHom φ).op) (A'.left.map (simplexHom φ).op) (h.left.app (op n))
      (h.left.naturality _) V

/-- On an object étale over `A'_{-1}`, `mapComparison` is the comparison of the iterated base
change along `h_{-1}` and `A_n → A_{-1}`. -/
theorem mapComparison_inl (h : A ⟶ A') {n : SimplexCategory} (V : SpacesEtale B S hS A'.right) :
    mapComparison h (Sum.inl V : Index A' n) =
      doubleBaseChangeComparison h.right (A.hom.app (op n)) (A'.hom.app (op n))
        (h.left.app (op n)) (hom_app_comp_right h n) V :=
  rfl

/-- On a formal base change of an object étale over `A'_m`, `mapComparison` is the comparison of
the iterated base change along `h_m` and `A_n → A_m`. -/
theorem mapComparison_inr (h : A ⟶ A') {n m : SimplexCategory}
    (φ : Fin (m.len + 1) →o Fin (n.len + 1)) (V : SpacesEtale B S hS (A'.left.obj (op m))) :
    mapComparison h (Sum.inr ⟨m, φ, V⟩ : Index A' n) =
      doubleBaseChangeComparison (h.left.app (op m))
        (A.left.map (simplexHom φ).op) (A'.left.map (simplexHom φ).op) (h.left.app (op n))
        (h.left.naturality _) V :=
  rfl

/-- The realization of `x.map h` is the fibre product of the realization of `x` and `A_n` over
`A'_n`, with `mapComparison h x` as projection. -/
theorem isPullback_mapComparison (h : A ⟶ A') {n : SimplexCategory} (x : Index A' n) :
    IsPullback (mapComparison h x) (realize (x.map h)).obj.hom (realize x).obj.hom
      (h.left.app (op n)) := by
  rcases x with V | ⟨m, φ, V⟩
  · exact isPullback_doubleBaseChangeComparison _ _ _ _ (hom_app_comp_right h n) V
  · exact isPullback_doubleBaseChangeComparison _ _ _ _ (h.left.naturality _) V

/-- `mapComparison h x` lies over `h_n : A_n → A'_n`. -/
@[reassoc]
theorem mapComparison_hom (h : A ⟶ A') {n : SimplexCategory} (x : Index A' n) :
    mapComparison h x ≫ (realize x).obj.hom = (realize (x.map h)).obj.hom ≫ h.left.app (op n) :=
  (isPullback_mapComparison h x).w

/-- The comparison of iterated base changes commutes with the comparison of base changes along a
map of squares. -/
private theorem doubleBaseChangeComparison_comp_baseChangeComparison
    {X Y Z Z' T T' : AlgebraicSpaces B S hS} (p : X ⟶ Y) (a : Z ⟶ X) (b : Z' ⟶ Z) (a' : Z' ⟶ X)
    (g : T ⟶ Y) (h : T' ⟶ T) (g' : T' ⟶ Y) (s : Z ⟶ T) (s' : Z' ⟶ T') (ea : b ≫ a = a')
    (eg : h ≫ g = g') (e1 : a ≫ p = s ≫ g) (e2 : a' ≫ p = s' ≫ g') (e3 : b ≫ s = s' ≫ h)
    (V : SpacesEtale B S hS Y) :
    doubleBaseChangeComparison p a' g' s' e2 V ≫ baseChangeComparison g h g' eg V =
      baseChangeComparison a b a' ea ((spacesBaseChange B S hS p).functor.obj V) ≫
        doubleBaseChangeComparison p a g s e1 V := by
  apply ((spacesBaseChange B S hS g).isPullback V).hom_ext <;> simp [e3]

/-- The comparisons of base change along `h` and along the transitions commute, on objects
étale over `A'_{-1}`. -/
theorem mapComparison_push_comp_inl (h : A ⟶ A') {n k : SimplexCategory} (ψ : n ⟶ k)
    (V : SpacesEtale B S hS A'.right) :
    mapComparison h (Index.push ψ (Sum.inl V : Index A' n)) ≫
        comparison ψ (Sum.inl V : Index A' n) =
      comparison ψ (Index.map h (Sum.inl V : Index A' n)) ≫
        mapComparison h (Sum.inl V : Index A' n) :=
  doubleBaseChangeComparison_comp_baseChangeComparison _ _ _ _ _ _ _ _ _ (hom_app_comp ψ)
    (hom_app_comp ψ) (hom_app_comp_right h n) (hom_app_comp_right h k) (h.left.naturality ψ.op) V

/-- The comparisons of base change along `h` and along the transitions commute, on formal base
changes of objects étale over some `A'_m`. -/
theorem mapComparison_push_comp_inr (h : A ⟶ A') {n k m : SimplexCategory} (ψ : n ⟶ k)
    (φ : Fin (m.len + 1) →o Fin (n.len + 1)) (V : SpacesEtale B S hS (A'.left.obj (op m))) :
    mapComparison h (Index.push ψ (Sum.inr ⟨m, φ, V⟩ : Index A' n)) ≫
        comparison ψ (Sum.inr ⟨m, φ, V⟩ : Index A' n) =
      comparison ψ (Index.map h (Sum.inr ⟨m, φ, V⟩ : Index A' n)) ≫
        mapComparison h (Sum.inr ⟨m, φ, V⟩ : Index A' n) :=
  doubleBaseChangeComparison_comp_baseChangeComparison _ _ _ _ _ _ _ _ _
    (A.left.map_comp _ _).symm (A'.left.map_comp _ _).symm (h.left.naturality _)
    (h.left.naturality _) (h.left.naturality ψ.op) V

/-- **Base change along `h_n : A_n → A'_n` on the strict components.** A formal base change in
degree `n` for `A'` goes to its base change along `h`, and a morphism to the morphism transported
along the cartesian comparison squares. -/
def mapFunctor (h : A ⟶ A') (n : SimplexCategory) : EtaleComponent A' n ⥤ EtaleComponent A n where
  obj x := Index.map h x
  map {x y} f := InducedCategory.homMk (transportAlong (h.left.app (op n))
    (isPullback_mapComparison h x).toCommSq (isPullback_mapComparison h y) f.hom)
  map_id x := InducedCategory.hom_ext (transportAlong_id (isPullback_mapComparison h x))
  map_comp {x y z} f g := InducedCategory.hom_ext
    (transportAlong_comp (isPullback_mapComparison h x).toCommSq (isPullback_mapComparison h y)
      (isPullback_mapComparison h z) f.hom g.hom)

/-- The image of a morphism under `mapFunctor h n` is compatible with the comparison maps. -/
@[reassoc (attr := simp)]
theorem mapFunctor_map_hom_comp (h : A ⟶ A') {n : SimplexCategory} {x y : EtaleComponent A' n}
    (f : x ⟶ y) :
    ((mapFunctor h n).map f).hom.hom.left ≫ mapComparison h y =
      mapComparison h x ≫ f.hom.hom.left :=
  transportAlong_comp_q (isPullback_mapComparison h x).toCommSq (isPullback_mapComparison h y)
    f.hom

/-- Base change along `h` commutes strictly with the transitions. -/
theorem transition_comp_mapFunctor (h : A ⟶ A') {n k : SimplexCategory} (ψ : n ⟶ k) :
    transition ψ ⋙ mapFunctor h k = mapFunctor h n ⋙ transition ψ := by
  refine CategoryTheory.Functor.hext (fun x ↦ Index.map_push h ψ x) (fun x y f ↦ ?_)
  rcases x with V | ⟨m, φ, V⟩ <;> rcases y with W | ⟨m', φ', W⟩ <;>
  · refine heq_of_eq (InducedCategory.hom_ext ?_)
    refine (transportAlong_eq_iff (isPullback_mapComparison h _).toCommSq _ _ _).2 ?_
    first
    | have px := mapComparison_push_comp_inl h ψ V
    | have px := mapComparison_push_comp_inr h ψ φ V
    first
    | have py := mapComparison_push_comp_inl h ψ W
    | have py := mapComparison_push_comp_inr h ψ φ' W
    first
    | apply (isPullback_comparison ψ (Sum.inl W : Index A' n)).hom_ext
    | apply (isPullback_comparison ψ (Sum.inr ⟨m', φ', W⟩ : Index A' n)).hom_ext
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) py).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
          (transition_map_hom_comp ψ ((mapFunctor h n).map f))).trans
            ((Category.assoc _ _ _).trans
              (congrArg (_ ≫ ·) (mapFunctor_map_hom_comp h f)))))) |>.trans ?_
      exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (transition_map_hom_comp ψ f)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) px).trans
          (Category.assoc _ _ _))))).symm
    · refine (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (mapComparison_hom h _)).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (Over.w _)))) |>.trans ?_
      exact ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) (Over.w _)).trans
        (mapComparison_hom h _))).symm

/-- The component at `x` of `mapRealizeIso`: both objects are fibre products of the realization
of `x` along `h_n`. -/
def mapRealizeIsoApp (h : A ⟶ A') {n : SimplexCategory} (x : EtaleComponent A' n) :
    (realizeFunctor n).obj ((mapFunctor h n).obj x) ≅
      (spacesBaseChange B S hS (h.left.app (op n))).functor.obj ((realizeFunctor n).obj x) :=
  (IsEtaleOver B S hS _).isoMk (Over.isoMk
    ((isPullback_mapComparison h x).isoIsPullback _ _
      ((spacesBaseChange B S hS (h.left.app (op n))).isPullback (realize x)))
    (IsPullback.isoIsPullback_hom_snd _ _ _ _))

/-- The component `mapRealizeIsoApp h x`, followed by the projection of the base change, is
`mapComparison h x`. -/
theorem mapRealizeIsoApp_hom_fst (h : A ⟶ A') {n : SimplexCategory} (x : EtaleComponent A' n) :
    (mapRealizeIsoApp h x).hom.hom.left ≫
        (spacesBaseChange B S hS (h.left.app (op n))).projection.app (realize x) =
      mapComparison h x :=
  IsPullback.isoIsPullback_hom_fst _ _ _ _

/-- Base change along `h_n` on the strict components, followed by realization, is realization
followed by the base-change functor of Stacks 03G2 along `h_n : A_n → A'_n`. -/
def mapRealizeIso (h : A ⟶ A') (n : SimplexCategory) :
    mapFunctor h n ⋙ realizeFunctor n ≅
      realizeFunctor n ⋙ (spacesBaseChange B S hS (h.left.app (op n))).functor :=
  NatIso.ofComponents (mapRealizeIsoApp h) (fun {x y} f ↦ by
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
    apply ((spacesBaseChange B S hS (h.left.app (op n))).isPullback (realize y)).hom_ext
    · have hnat : ((spacesBaseChange B S hS (h.left.app (op n))).functor.map f.hom).hom.left ≫
          (spacesBaseChange B S hS (h.left.app (op n))).projection.app (realize y) =
          (spacesBaseChange B S hS (h.left.app (op n))).projection.app (realize x) ≫
            f.hom.hom.left :=
        (spacesBaseChange B S hS (h.left.app (op n))).projection.naturality f.hom
      change (((mapFunctor h n).map f).hom.hom.left ≫ (mapRealizeIsoApp h y).hom.hom.left) ≫
          _ = ((mapRealizeIsoApp h x).hom.hom.left ≫
            ((spacesBaseChange B S hS (h.left.app (op n))).functor.map f.hom).hom.left) ≫ _
      rw [Category.assoc, Category.assoc, mapRealizeIsoApp_hom_fst, hnat,
        ← Category.assoc, mapRealizeIsoApp_hom_fst]
      exact mapFunctor_map_hom_comp h f
    · exact ((Category.assoc _ _ _).trans ((congrArg (fun t ↦ _ ≫ t)
        (Over.w (mapRealizeIsoApp h y).hom.hom)).trans
          (Over.w ((mapFunctor h n).map f).hom.hom))).trans
        (((Over.w (mapRealizeIsoApp h x).hom.hom).symm.trans (congrArg (fun t ↦ _ ≫ t)
          (Over.w ((spacesBaseChange B S hS (h.left.app (op n))).functor.map
            f.hom).hom).symm)).trans (Category.assoc _ _ _).symm))

/-- Base change along `h_n` on the strict components preserves fibre products. -/
instance (h : A ⟶ A') (n : SimplexCategory) :
    PreservesLimitsOfShape WalkingCospan (mapFunctor h n) :=
  have : PreservesLimitsOfShape WalkingCospan (mapFunctor h n ⋙ realizeFunctor n) :=
    preservesLimitsOfShape_of_natIso (mapRealizeIso h n).symm
  preservesLimitsOfShape_of_reflects_of_preserves _ (realizeFunctor n)

/-- Base change along `h_n` on the strict components preserves the fibre product of `f` and
`g`. -/
theorem mapFunctor_preservesLimit (h : A ⟶ A') {n : SimplexCategory}
    {x y z : EtaleComponent A' n} (f : x ⟶ y) (g : z ⟶ y) :
    PreservesLimit (cospan f g) (mapFunctor h n) :=
  inferInstance

/-- The comparison squares of base change along `h_n` are cartesian along every arrow. -/
theorem isPullback_mapFunctor_map (h : A ⟶ A') {n : SimplexCategory} {x y : EtaleComponent A' n}
    (g : x ⟶ y) :
    IsPullback ((mapFunctor h n).map g).hom.hom.left (mapComparison h x) (mapComparison h y)
      g.hom.hom.left := by
  refine IsPullback.of_right ?_ (mapFunctor_map_hom_comp h g) (isPullback_mapComparison h y).flip
  have e₁ : ((mapFunctor h n).map g).hom.hom.left ≫ (realize (Index.map h y)).obj.hom =
      (realize (Index.map h x)).obj.hom := Over.w ((mapFunctor h n).map g).hom.hom
  rw [e₁, Over.w g.hom.hom]
  exact (isPullback_mapComparison h x).flip

/-- Base change along `h_n` on the strict components sends étale coverings to étale coverings. -/
theorem precoverage_le_comap_mapFunctor (h : A ⟶ A') (n : SimplexCategory) :
    precoverage (A := A') n ≤ (precoverage (A := A) n).comap (mapFunctor h n) :=
  fun _ _ hR ↦ map_mem_comap_precoverage_of_isPullback (realizeFunctor n) (mapFunctor h n)
    (realizeFunctor n) (mapComparison h) (fun g ↦ isPullback_mapFunctor_map h g) hR

/-- **Base change along `h_n` is a morphism of sites** (Stacks 03G2). -/
theorem mapFunctor_isMorphismOfSites (h : A ⟶ A') (n : SimplexCategory) :
    (mapFunctor h n).IsMorphismOfSites (precoverage (A := A') n).toGrothendieck
      (precoverage (A := A) n).toGrothendieck :=
  have : (mapFunctor h n).IsContinuous (precoverage (A := A') n).toGrothendieck
      (precoverage (A := A) n).toGrothendieck :=
    Stacks.Sites.isContinuous_toGrothendieck_of_le_comap _ _ _
      ((precoverage_le_comap_mapFunctor h n).trans
        (Precoverage.comap_monotone (Precoverage.le_toPrecoverage_toGrothendieck _)))
  have : IsIso ((spacesBaseChange B S hS (h.left.app (op n))).functor.obj
      (SpacesEtale.idObj B S hS (A'.left.obj (op n)))).obj.hom :=
    ((spacesBaseChange B S hS (h.left.app (op n))).isPullback _).isIso_snd_of_isIso
      (inferInstanceAs (IsIso (𝟙 _)))
  Functor.isMorphismOfSites_of_isTerminal _ _ _ (isTerminalFinal n)
    (IsTerminal.isTerminalOfObj (realizeFunctor n) _
      (SpacesEtale.isTerminal_of_isIso B S hS _
        (((spacesBaseChange B S hS _).isPullback _).isIso_snd_of_isIso)))

/-- The comparisons of base change along `h` and along the transitions commute, for every formal
base change, up to the identification of `(x.push ψ).map h` with `(x.map h).push ψ`. -/
theorem mapComparison_push_comp_eqToHom (h : A ⟶ A') {n k : SimplexCategory} (ψ : n ⟶ k)
    (x : EtaleComponent A' n)
    (e : (mapFunctor h k).obj ((transition ψ).obj x) =
      (transition ψ).obj ((mapFunctor h n).obj x)) :
    (realizeFunctor k ⋙ SpacesEtale.toSpaces B S hS (A.left.obj (op k))).map (eqToHom e) ≫
        comparison ψ (Index.map h x) ≫ mapComparison h x =
      mapComparison h (Index.push ψ x) ≫ comparison ψ x := by
  rcases x with V | ⟨m, φ, V⟩
  · exact (Category.id_comp _).trans (mapComparison_push_comp_inl h ψ V).symm
  · exact (Category.id_comp _).trans (mapComparison_push_comp_inr h ψ φ V).symm

end EtaleComponent

open EtaleComponent

/-- **Section 0DE7, the morphism of simplicial sites of `h`.** A morphism `h : X ⟶ Y` of augmented
simplicial algebraic spaces gives the morphisms of sites `(h_n)_{spaces, étale}` of Stacks 03G2,
base change along `h_n`, commuting strictly with the transitions: a morphism of simplicial sites
in case (A) of Stacks 09WE. -/
def etaleSimplicialSiteMorphism (h : A ⟶ A') :
    SimplicialSite.Morphism (etaleSimplicialSite A) (etaleSimplicialSite A') where
  hom :=
    { app := fun n => (mapFunctor h n).toCatHom
      naturality := fun _ _ ψ => Cat.Hom.ext (transition_comp_mapFunctor h ψ) }
  isMorphismOfSites n := mapFunctor_isMorphismOfSites h n
  coverPreserving n := precoverage_le_comap_mapFunctor h n
  preservesPullbacks _n _ _ _ _ _ _ _ f := mapFunctor_preservesLimit h f _

/-- **Section 0DE7, `h_étale`.** The morphism of small étale topoi
`h_étale : Sh(X_étale) ⟶ Sh(Y_étale)` of a morphism of augmented simplicial algebraic spaces,
obtained by Lemma 0D96 from the morphisms of sites `(h_n)_{spaces, étale}`. -/
abbrev etaleMorphismOfTopoi (h : A ⟶ A') :
    MorphismOfTopoi (Sheaf (etaleSimplicialSite A).totalTopology (Type (u + 1)))
      (Sheaf (etaleSimplicialSite A').totalTopology (Type (u + 1))) :=
  (etaleSimplicialSiteMorphism h).totalMorphism

/-- **The components of `h_étale` are base change.** Through the equivalences
`EtaleComponent.sheafEquiv`, the direct image along the morphism of topoi of `h_étale` in degree
`n` is the direct image along the morphism of topoi of base change by `h_n : X_n → Y_n`
(Stacks 03G2). -/
def etaleMorphismComponentPushforwardIso (h : A ⟶ A') (n : SimplexCategory) :
    (sheafEquiv (A := A) n (Type (u + 1))).inverse ⋙
        ((SimplicialSiteMorphism.ofMorphismOfSites
          (etaleSimplicialSiteMorphism h)).componentMorphism n).pushforward ≅
      (spacesBaseChange_isMorphismOfSites B S hS (h.left.app (op n))).morphismOfTopoi.pushforward ⋙
        (sheafEquiv (A := A') n (Type (u + 1))).inverse :=
  NatIso.ofComponents
    (fun G => ObjectProperty.isoMk _ (Functor.isoWhiskerRight (NatIso.op
      (mapRealizeIso h n)).symm G.obj))
    (fun {G G'} g => by
      refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun x => ?_))
      exact (g.hom.naturality _).symm)

/-- The comparison maps `V ×_{Y_n} X_n ⟶ V` between the realizations of an object of
`Y_étale` and of its image in `X_étale`, natural on `Y_étale`. -/
def etaleTotalMapComparison (h : A ⟶ A') :
    (etaleSimplicialSiteMorphism h).totalFunctor ⋙ etaleTotalToSpaces A ⟶
      etaleTotalToSpaces A' where
  app y := mapComparison h y.fiber
  naturality y y' f := by
    change ((realizeFunctor y.base.unop ⋙ SpacesEtale.toSpaces B S hS _).map
        ((mapFunctor h y.base.unop).map f.fiber ≫ eqToHom _) ≫
          comparison f.base.unop (Index.map h y'.fiber)) ≫ mapComparison h y'.fiber =
      mapComparison h y.fiber ≫ ((realizeFunctor y.base.unop ⋙ SpacesEtale.toSpaces B S hS _).map
        f.fiber ≫ comparison f.base.unop y'.fiber)
    rw [Functor.map_comp, Category.assoc, Category.assoc]
    exact (congrArg (_ ≫ ·) (mapComparison_push_comp_eqToHom h f.base.unop y'.fiber _)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _)
        (mapFunctor_map_hom_comp h f.fiber)).trans (Category.assoc _ _ _)))

/-- **Section 0DE7, `h_étale♯`.** The map `𝒪_Y ⟶ h_{étale,*}𝒪_X` of sheaves of rings on `Y_étale`,
given on `Y_n` by `h_n♯ : 𝒪_{Y_n} ⟶ h_{n,*}𝒪_{X_n}`: over an object `V` étale over `Y_n`, pullback
of global functions along the projection `V ×_{Y_n} X_n ⟶ V`. -/
def etaleMorphismStructureSharp (h : A ⟶ A') :
    etaleStructureSheaf A' ⟶
      ((etaleSimplicialSiteMorphism h).totalFunctor.sheafPushforwardContinuous CommRingCat.{u + 1}
        (etaleSimplicialSite A').totalTopology (etaleSimplicialSite A).totalTopology).obj
        (etaleStructureSheaf A) :=
  ObjectProperty.homMk
    (Functor.whiskerRight (NatTrans.op (etaleTotalMapComparison h))
      (globalFunctionsPresheaf B S hS))

/-- The sections of `h_étale♯` over an object `y` of `Y_étale` are the pullback of global functions
along the comparison `V ×_{Y_n} X_n ⟶ V` of realizations. -/
theorem etaleMorphismStructureSharp_app (h : A ⟶ A')
    (y : (Pseudofunctor.CoGrothendieck (etaleSimplicialSite A').totalPseudofunctor)ᵒᵖ) :
    (etaleMorphismStructureSharp h).hom.app y =
      (globalFunctionsPresheaf B S hS).map (mapComparison h y.unop.fiber).op :=
  rfl

/-- **Section 0DE7, the morphism of ringed topoi
`h_étale : (Sh(X_étale), 𝒪_X) ⟶ (Sh(Y_étale), 𝒪_Y)`.** Its underlying morphism of topoi is
`h_étale` and its structure map is `h_étale♯`, read in the direct image of sheaves of commutative
rings along `h_étale`, which is restriction along the functor of total sites. -/
def etaleMorphismRingedHom (h : A ⟶ A') :
    RingedToposHom ((etaleSituation A).totalRingedTopos (etaleStructureSheaf A))
      ((etaleSituation A').totalRingedTopos (etaleStructureSheaf A')) where
  toToposHom := etaleMorphismOfTopoi h
  fSharp :=
    haveI := (etaleSimplicialSiteMorphism h).totalFunctor_isContinuous
    etaleMorphismStructureSharp h ≫
      (Stacks.Sheaves.ToposPullback.restrictionCommRingIso (etaleSimplicialSite A').totalTopology
        (etaleSimplicialSite A).totalTopology (etaleSimplicialSiteMorphism h).totalFunctor
        (etaleStructureSheaf A)).inv

/-! ### Simplicial algebraic spaces without a given augmentation -/

variable (B S hS) in
/-- The final algebraic space over `S`: the representable presheaf of the final object `S` of
the big fppf site over `S`. -/
def finalSpace : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj (⊤_ (BigFppfOver B S hS)), isAlgebraicSpace_yoneda B S hS _⟩

variable (B S hS) in
/-- The final algebraic space is a final object of the category of algebraic spaces over `S`. -/
def isTerminalFinalSpace : IsTerminal (finalSpace B S hS) :=
  IsTerminal.isTerminalOfObj (ObjectProperty.ι _) _
    (IsTerminal.isTerminalObj yoneda _ terminalIsTerminal)

/-- A simplicial algebraic space with its augmentation towards the final algebraic space. Every
simplicial algebraic space carries it, so its small étale site is that of this augmented
simplicial algebraic space. -/
def augmentFinal (X : SimplicialObject (AlgebraicSpaces B S hS)) :
    SimplicialObject.Augmented (AlgebraicSpaces B S hS) where
  left := X
  right := finalSpace B S hS
  hom :=
    { app := fun _ => (isTerminalFinalSpace B S hS).from _
      naturality := fun _ _ _ => (isTerminalFinalSpace B S hS).hom_ext _ _ }

/-- A morphism of simplicial algebraic spaces, as a morphism of the simplicial algebraic spaces
augmented towards the final algebraic space. -/
def augmentFinalMap {X Y : SimplicialObject (AlgebraicSpaces B S hS)} (h : X ⟶ Y) :
    augmentFinal X ⟶ augmentFinal Y where
  left := h
  right := 𝟙 _
  w := NatTrans.ext (funext fun _ => (isTerminalFinalSpace B S hS).hom_ext _ _)

/-- **Section 0DE7, `h_étale` for a morphism of simplicial algebraic spaces.** The morphism of
small étale topoi `Sh(X_étale) ⟶ Sh(Y_étale)` of a morphism `h : X ⟶ Y` of simplicial algebraic
spaces, with `X_étale` and `Y_étale` the small étale sites of `X` and `Y` augmented towards the
final algebraic space. -/
abbrev simplicialEtaleMorphismOfTopoi {X Y : SimplicialObject (AlgebraicSpaces B S hS)}
    (h : X ⟶ Y) :
    MorphismOfTopoi (Sheaf (etaleSimplicialSite (augmentFinal X)).totalTopology (Type (u + 1)))
      (Sheaf (etaleSimplicialSite (augmentFinal Y)).totalTopology (Type (u + 1))) :=
  etaleMorphismOfTopoi (augmentFinalMap h)

/-- **Section 0DE7, the morphism of ringed topoi `h_étale` of a morphism of simplicial algebraic
spaces.** -/
abbrev simplicialEtaleRingedHom {X Y : SimplicialObject (AlgebraicSpaces B S hS)} (h : X ⟶ Y) :
    RingedToposHom ((etaleSituation (augmentFinal X)).totalRingedTopos
        (etaleStructureSheaf (augmentFinal X)))
      ((etaleSituation (augmentFinal Y)).totalRingedTopos
        (etaleStructureSheaf (augmentFinal Y))) :=
  etaleMorphismRingedHom (augmentFinalMap h)

end AlgebraicGeometry.Space

end
