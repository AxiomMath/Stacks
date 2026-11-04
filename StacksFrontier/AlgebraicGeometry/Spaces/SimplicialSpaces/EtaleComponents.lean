module

public import Mathlib.AlgebraicTopology.SimplicialObject.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleBaseChange

/-!
# The components of the small étale site of an augmented simplicial algebraic space

Let `a : U → X` be an augmented simplicial algebraic space over a scheme `S`. Section 0DE7 of
the Stacks project forms the simplicial object in sites `n ↦ U_{n, spaces, étale}` whose
transition along `φ : [m] → [n]` is the morphism of sites of Stacks 03G2 attached to
`U(φ) : U_n → U_m`, that is, base change `V ↦ V ×_{U_m} U_n`. Base change is functorial only
up to the canonical isomorphisms of iterated fibre products, whereas the total-site
construction of Stacks 09WC in this library consumes a strict functor
`SimplexCategory ⥤ Cat`. This file supplies a strict model.

The component in degree `n` is the category `EtaleComponent A n` whose objects are *formal
base changes*: an object étale over `X`, or an object étale over some `U_m` together with a
simplex map `φ : [m] → [n]`. Such an object is realized, by `EtaleComponent.realize`, as its
base change to `U_n`, and the morphisms are those of the realizations in the spaces-étale site
of `U_n`. Thus `EtaleComponent A n` is equivalent to `U_{n, spaces, étale}` through the fully
faithful and essentially surjective realization functor, and the transition along
`ψ : [n] → [k]` acts on formal base changes by composing with `ψ`, which is strictly
functorial; on morphisms it is base change, read off from the universal property of the
cartesian squares relating the realizations in degrees `n` and `k`.

## Main definitions

* `AlgebraicGeometry.Space.EtaleComponent.Index`: the formal base changes in degree `n`.
* `AlgebraicGeometry.Space.EtaleComponent`: the strict model of `U_{n, spaces, étale}`.
* `AlgebraicGeometry.Space.EtaleComponent.realizeFunctor`: the realization functor to
  `U_{n, spaces, étale}`, which is an equivalence.
* `AlgebraicGeometry.Space.EtaleComponent.transition`: base change along `U(ψ) : U_k → U_n`.
* `AlgebraicGeometry.Space.etaleComponentsFunctor`: the resulting strict cosimplicial diagram
  of categories.

## References

* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Transporting morphisms along cartesian squares -/

section Transport

variable {B S hS} {T T' : AlgebraicSpaces B S hS} (h : T' ⟶ T)

/-- A morphism `f : W₁ ⟶ W₂` of the spaces-étale site of `T`, transported along a commutative
square from `W₁'` and a cartesian square from `W₂'` lying over `h : T' ⟶ T`: the unique morphism
`W₁' ⟶ W₂'` over `T'` compatible with `f` through the two squares. -/
def transportAlong {W₁ W₂ : SpacesEtale B S hS T} {W₁' W₂' : SpacesEtale B S hS T'}
    {q₁ : W₁'.obj.left ⟶ W₁.obj.left} {q₂ : W₂'.obj.left ⟶ W₂.obj.left}
    (sq₁ : CommSq q₁ W₁'.obj.hom W₁.obj.hom h) (sq₂ : IsPullback q₂ W₂'.obj.hom W₂.obj.hom h)
    (f : W₁ ⟶ W₂) : W₁' ⟶ W₂' :=
  ObjectProperty.homMk (Over.homMk (sq₂.lift (q₁ ≫ f.hom.left) W₁'.obj.hom (by
    rw [Category.assoc, Over.w f.hom, sq₁.w])) (sq₂.lift_snd _ _ _))

variable {h}

/-- The transported morphism, followed by the projection `q₂`, equals `q₁` followed by `f`. -/
@[reassoc (attr := simp)]
theorem transportAlong_comp_q {W₁ W₂ : SpacesEtale B S hS T} {W₁' W₂' : SpacesEtale B S hS T'}
    {q₁ : W₁'.obj.left ⟶ W₁.obj.left} {q₂ : W₂'.obj.left ⟶ W₂.obj.left}
    (sq₁ : CommSq q₁ W₁'.obj.hom W₁.obj.hom h) (sq₂ : IsPullback q₂ W₂'.obj.hom W₂.obj.hom h)
    (f : W₁ ⟶ W₂) : (transportAlong h sq₁ sq₂ f).hom.left ≫ q₂ = q₁ ≫ f.hom.left :=
  sq₂.lift_fst _ _ _

/-- Transport is characterized by its compatibility with the two squares. -/
theorem transportAlong_eq_iff {W₁ W₂ : SpacesEtale B S hS T} {W₁' W₂' : SpacesEtale B S hS T'}
    {q₁ : W₁'.obj.left ⟶ W₁.obj.left} {q₂ : W₂'.obj.left ⟶ W₂.obj.left}
    (sq₁ : CommSq q₁ W₁'.obj.hom W₁.obj.hom h) (sq₂ : IsPullback q₂ W₂'.obj.hom W₂.obj.hom h)
    (f : W₁ ⟶ W₂) (g : W₁' ⟶ W₂') :
    transportAlong h sq₁ sq₂ f = g ↔ g.hom.left ≫ q₂ = q₁ ≫ f.hom.left := by
  constructor
  · rintro rfl
    exact transportAlong_comp_q sq₁ sq₂ f
  · intro hg
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext ?_)
    apply sq₂.hom_ext
    · rw [hg, transportAlong_comp_q]
    · rw [Over.w g.hom]
      exact sq₂.lift_snd _ _ _

/-- Transporting the identity along a cartesian square gives the identity. -/
theorem transportAlong_id {W : SpacesEtale B S hS T} {W' : SpacesEtale B S hS T'}
    {q : W'.obj.left ⟶ W.obj.left} (sq : IsPullback q W'.obj.hom W.obj.hom h) :
    transportAlong h sq.toCommSq sq (𝟙 W) = 𝟙 W' := by
  rw [transportAlong_eq_iff]
  simp

/-- Transport of a composite is the composite of the transports. -/
theorem transportAlong_comp {W₁ W₂ W₃ : SpacesEtale B S hS T}
    {W₁' W₂' W₃' : SpacesEtale B S hS T'}
    {q₁ : W₁'.obj.left ⟶ W₁.obj.left} {q₂ : W₂'.obj.left ⟶ W₂.obj.left}
    {q₃ : W₃'.obj.left ⟶ W₃.obj.left}
    (sq₁ : CommSq q₁ W₁'.obj.hom W₁.obj.hom h) (sq₂ : IsPullback q₂ W₂'.obj.hom W₂.obj.hom h)
    (sq₃ : IsPullback q₃ W₃'.obj.hom W₃.obj.hom h) (f : W₁ ⟶ W₂) (g : W₂ ⟶ W₃) :
    transportAlong h sq₁ sq₃ (f ≫ g) =
      transportAlong h sq₁ sq₂ f ≫ transportAlong h sq₂.toCommSq sq₃ g := by
  rw [transportAlong_eq_iff]
  simp

end Transport

/-! ### Base change along a factorization -/

section Comparison

variable {B S hS} {T T' Y : AlgebraicSpaces B S hS}

/-- For `g' = h ≫ g`, the canonical morphism from the base change of `V` along `g'` to its base
change along `g`, lying over `h`. -/
def baseChangeComparison (g : T ⟶ Y) (h : T' ⟶ T) (g' : T' ⟶ Y) (e : h ≫ g = g')
    (V : SpacesEtale B S hS Y) :
    ((spacesBaseChange B S hS g').functor.obj V).obj.left ⟶
      ((spacesBaseChange B S hS g).functor.obj V).obj.left :=
  ((spacesBaseChange B S hS g).isPullback V).lift ((spacesBaseChange B S hS g').projection.app V)
    (((spacesBaseChange B S hS g').functor.obj V).obj.hom ≫ h) (by
      rw [((spacesBaseChange B S hS g').isPullback V).w, Category.assoc, e])

/-- The comparison morphism, followed by the projection of the base change along `g` to `V`, is
the projection of the base change along `g'` to `V`. -/
@[reassoc (attr := simp)]
theorem baseChangeComparison_projection (g : T ⟶ Y) (h : T' ⟶ T) (g' : T' ⟶ Y)
    (e : h ≫ g = g') (V : SpacesEtale B S hS Y) :
    baseChangeComparison g h g' e V ≫ (spacesBaseChange B S hS g).projection.app V =
      (spacesBaseChange B S hS g').projection.app V :=
  IsPullback.lift_fst _ _ _ _

/-- The comparison morphism lies over `h`. -/
@[reassoc (attr := simp)]
theorem baseChangeComparison_hom (g : T ⟶ Y) (h : T' ⟶ T) (g' : T' ⟶ Y)
    (e : h ≫ g = g') (V : SpacesEtale B S hS Y) :
    baseChangeComparison g h g' e V ≫ ((spacesBaseChange B S hS g).functor.obj V).obj.hom =
      ((spacesBaseChange B S hS g').functor.obj V).obj.hom ≫ h :=
  IsPullback.lift_snd _ _ _ _

/-- The comparison square is cartesian, by the pasting lemma. -/
theorem isPullback_baseChangeComparison (g : T ⟶ Y) (h : T' ⟶ T) (g' : T' ⟶ Y)
    (e : h ≫ g = g') (V : SpacesEtale B S hS Y) :
    IsPullback (baseChangeComparison g h g' e V)
      ((spacesBaseChange B S hS g').functor.obj V).obj.hom
      ((spacesBaseChange B S hS g).functor.obj V).obj.hom h := by
  refine IsPullback.of_right ?_ (baseChangeComparison_hom g h g' e V)
    ((spacesBaseChange B S hS g).isPullback V)
  rw [baseChangeComparison_projection, e]
  exact (spacesBaseChange B S hS g').isPullback V

/-- The comparison morphism along an identity morphism is the identity. -/
private theorem baseChangeComparison_of_eq_id (g : T ⟶ Y) (h : T ⟶ T) (e : h ≫ g = g)
    (hh : h = 𝟙 T) (V : SpacesEtale B S hS Y) : baseChangeComparison g h g e V = 𝟙 _ := by
  apply ((spacesBaseChange B S hS g).isPullback V).hom_ext
  · simp
  · simp [hh]

/-- The comparison morphism along a composite is the composite of the comparison morphisms. -/
private theorem baseChangeComparison_of_eq_comp {T'' : AlgebraicSpaces B S hS} (g : T ⟶ Y)
    (h : T' ⟶ T) (g' : T' ⟶ Y) (e : h ≫ g = g') (h' : T'' ⟶ T') (g'' : T'' ⟶ Y)
    (e' : h' ≫ g' = g'') (h'' : T'' ⟶ T) (e'' : h'' ≫ g = g'') (hh : h'' = h' ≫ h)
    (V : SpacesEtale B S hS Y) :
    baseChangeComparison g h'' g'' e'' V =
      baseChangeComparison g' h' g'' e' V ≫ baseChangeComparison g h g' e V := by
  apply ((spacesBaseChange B S hS g).isPullback V).hom_ext
  · simp
  · simp [hh]

end Comparison

/-! ### The components -/

variable {B S hS} (A : SimplicialObject.Augmented (AlgebraicSpaces B S hS))

namespace EtaleComponent

/-- The formal base changes in simplicial degree `n`: an object étale over the base `X` of the
augmentation, or an order-preserving map `φ : [m] → [n]` together with an object étale over
`U_m`. The simplex map is recorded through its underlying order-preserving map, so that
composing with further simplex maps is strictly associative and unital. -/
def Index (n : SimplexCategory) : Type (u + 1) :=
  SpacesEtale B S hS A.right ⊕
    Σ m : SimplexCategory, (Fin (m.len + 1) →o Fin (n.len + 1)) ×
      SpacesEtale B S hS (A.left.obj (op m))

variable {A}

/-- The simplex map with a given underlying order-preserving map. -/
abbrev simplexHom {m n : SimplexCategory} (φ : Fin (m.len + 1) →o Fin (n.len + 1)) : m ⟶ n :=
  SimplexCategory.Hom.mk φ

/-- The realization of a formal base change in degree `n`, an object étale over `U_n`. -/
@[reducible] def realize {n : SimplexCategory} : Index A n → SpacesEtale B S hS (A.left.obj (op n))
  | .inl V => (spacesBaseChange B S hS (A.hom.app (op n))).functor.obj V
  | .inr ⟨_, φ, V⟩ => (spacesBaseChange B S hS (A.left.map (simplexHom φ).op)).functor.obj V

/-- The action of `ψ : [n] → [k]` on formal base changes: compose the simplex map with `ψ`. -/
@[reducible] def Index.push {n k : SimplexCategory} (ψ : n ⟶ k) : Index A n → Index A k
  | .inl V => .inl V
  | .inr ⟨m, φ, V⟩ => .inr ⟨m, ψ.toOrderHom.comp φ, V⟩

/-- Pushing along the identity is the identity. -/
@[simp]
theorem Index.push_id {n : SimplexCategory} (x : Index A n) : x.push (𝟙 n) = x := by
  rcases x with V | ⟨m, φ, V⟩ <;> rfl

/-- Pushing along a composite `ψ ≫ χ` is pushing along `ψ`, then along `χ`. -/
@[simp]
theorem Index.push_comp {n k l : SimplexCategory} (ψ : n ⟶ k) (χ : k ⟶ l) (x : Index A n) :
    x.push (ψ ≫ χ) = (x.push ψ).push χ := by
  rcases x with V | ⟨m, φ, V⟩ <;> rfl

/-- The augmentation is compatible with the face map `U(ψ) : U_k → U_n`. -/
theorem hom_app_comp {n k : SimplexCategory} (ψ : n ⟶ k) :
    A.left.map ψ.op ≫ A.hom.app (op n) = A.hom.app (op k) :=
  (A.hom.naturality ψ.op).trans (Category.comp_id _)

/-- The canonical morphism from the realization of `x.push ψ` to the realization of `x`, lying
over `U(ψ) : U_k → U_n`. -/
def comparison {n k : SimplexCategory} (ψ : n ⟶ k) :
    (x : Index A n) → (realize (x.push ψ)).obj.left ⟶ (realize x).obj.left
  | .inl V => baseChangeComparison (A.hom.app (op n)) (A.left.map ψ.op) (A.hom.app (op k))
      (hom_app_comp (A := A) ψ) V
  | .inr ⟨_, φ, V⟩ => baseChangeComparison (A.left.map (simplexHom φ).op)
      (A.left.map ψ.op) (A.left.map (simplexHom (ψ.toOrderHom.comp φ)).op)
      ((A.left.map_comp _ _).symm) V

/-- The comparison square between the realizations in degrees `k` and `n` is cartesian. -/
theorem isPullback_comparison {n k : SimplexCategory} (ψ : n ⟶ k) (x : Index A n) :
    IsPullback (comparison ψ x) (realize (x.push ψ)).obj.hom (realize x).obj.hom
      (A.left.map ψ.op) := by
  rcases x with V | ⟨m, φ, V⟩
  · exact isPullback_baseChangeComparison _ _ _ (hom_app_comp (A := A) ψ) V
  · exact isPullback_baseChangeComparison _ _ _ (A.left.map_comp _ _).symm V

/-- The comparison morphism lies over `U(ψ) : U_k → U_n`. -/
theorem comparison_hom {n k : SimplexCategory} (ψ : n ⟶ k) (x : Index A n) :
    comparison ψ x ≫ (realize x).obj.hom = (realize (x.push ψ)).obj.hom ≫ A.left.map ψ.op :=
  (isPullback_comparison ψ x).w

/-- For an object `V` étale over `X`, the comparison morphism is compatible with the projections
of the base changes of `V` to `U_n` and to `U_k`. -/
theorem comparison_inl_fst {n k : SimplexCategory} (ψ : n ⟶ k) (V : SpacesEtale B S hS A.right) :
    comparison ψ (Sum.inl V : Index A n) ≫
        (spacesBaseChange B S hS (A.hom.app (op n))).projection.app V =
      (spacesBaseChange B S hS (A.hom.app (op k))).projection.app V :=
  baseChangeComparison_projection (A.hom.app (op n)) (A.left.map ψ.op) (A.hom.app (op k))
    (hom_app_comp (A := A) ψ) V

/-- For an object `V` étale over `U_m` and `φ : [m] → [n]`, the comparison morphism is compatible
with the projections to `V` of its base changes along `U(φ)` and `U(ψ ∘ φ)`. -/
theorem comparison_inr_fst {n k m : SimplexCategory} (ψ : n ⟶ k)
    (φ : Fin (m.len + 1) →o Fin (n.len + 1)) (V : SpacesEtale B S hS (A.left.obj (op m))) :
    comparison ψ (Sum.inr ⟨m, φ, V⟩ : Index A n) ≫
        (spacesBaseChange B S hS (A.left.map (simplexHom φ).op)).projection.app V =
      (spacesBaseChange B S hS (A.left.map (simplexHom (ψ.toOrderHom.comp φ)).op)).projection.app
        V :=
  baseChangeComparison_projection (A.left.map (simplexHom φ).op) (A.left.map ψ.op)
    (A.left.map (simplexHom (ψ.toOrderHom.comp φ)).op) (A.left.map_comp _ _).symm V

/-- The comparison morphism along the identity is the identity, for an object étale over `X`. -/
theorem comparison_id_inl {n : SimplexCategory} (V : SpacesEtale B S hS A.right) :
    comparison (𝟙 n) (Sum.inl V : Index A n) = 𝟙 _ :=
  baseChangeComparison_of_eq_id _ _ (hom_app_comp _) (A.left.map_id (op n)) V

/-- The comparison morphism along the identity is the identity, for a formal base change of an
object étale over `U_m`. -/
theorem comparison_id_inr {n m : SimplexCategory} (φ : Fin (m.len + 1) →o Fin (n.len + 1))
    (V : SpacesEtale B S hS (A.left.obj (op m))) :
    comparison (𝟙 n) (Sum.inr ⟨m, φ, V⟩ : Index A n) = 𝟙 _ :=
  baseChangeComparison_of_eq_id _ _ (A.left.map_comp _ _).symm (A.left.map_id (op n)) V

/-- The comparison morphism along `ψ ≫ χ` is the composite of those along `χ` and `ψ`, for an
object étale over `X`. -/
theorem comparison_comp_inl {n k l : SimplexCategory} (ψ : n ⟶ k) (χ : k ⟶ l)
    (V : SpacesEtale B S hS A.right) :
    comparison (ψ ≫ χ) (Sum.inl V : Index A n) =
      comparison χ (Sum.inl V : Index A k) ≫ comparison ψ (Sum.inl V : Index A n) :=
  baseChangeComparison_of_eq_comp _ _ _ (hom_app_comp ψ) _ _ (hom_app_comp χ) _
    (hom_app_comp (ψ ≫ χ)) (A.left.map_comp _ _) V

/-- The comparison morphism along `ψ ≫ χ` is the composite of those along `χ` and `ψ`, for a
formal base change of an object étale over `U_m`. -/
theorem comparison_comp_inr {n k l m : SimplexCategory} (ψ : n ⟶ k) (χ : k ⟶ l)
    (φ : Fin (m.len + 1) →o Fin (n.len + 1)) (V : SpacesEtale B S hS (A.left.obj (op m))) :
    comparison (ψ ≫ χ) (Sum.inr ⟨m, φ, V⟩ : Index A n) =
      comparison χ (Sum.inr ⟨m, ψ.toOrderHom.comp φ, V⟩ : Index A k) ≫
        comparison ψ (Sum.inr ⟨m, φ, V⟩ : Index A n) :=
  baseChangeComparison_of_eq_comp _ _ _ (A.left.map_comp _ _).symm _ _
    (A.left.map_comp _ _).symm _ (A.left.map_comp _ _).symm (A.left.map_comp _ _) V

end EtaleComponent

/-- **Section 0DE7, the components.** The strict model of the spaces-étale site of `U_n`: the
formal base changes in degree `n`, with the morphisms of their realizations. -/
abbrev EtaleComponent (n : SimplexCategory) : Type (u + 1) :=
  InducedCategory (SpacesEtale B S hS (A.left.obj (op n))) (EtaleComponent.realize (A := A))

namespace EtaleComponent

variable {A}

/-- The realization functor `EtaleComponent A n ⥤ U_{n, spaces, étale}`. -/
abbrev realizeFunctor (n : SimplexCategory) :
    EtaleComponent A n ⥤ SpacesEtale B S hS (A.left.obj (op n)) :=
  inducedFunctor _

/-- The realization functor is fully faithful. -/
def realizeFullyFaithful (n : SimplexCategory) : (realizeFunctor (A := A) n).FullyFaithful :=
  fullyFaithfulInducedFunctor _

/-- An object of `U_{n, spaces, étale}`, regarded as the trivial formal base change. -/
def ofSpacesEtale {n : SimplexCategory} (V : SpacesEtale B S hS (A.left.obj (op n))) :
    EtaleComponent A n :=
  (Sum.inr ⟨n, OrderHom.id, V⟩ : Index A n)

/-- The realization of a trivial formal base change is isomorphic to the object itself. -/
def realizeOfSpacesEtaleIso {n : SimplexCategory} (V : SpacesEtale B S hS (A.left.obj (op n))) :
    (realizeFunctor n).obj (ofSpacesEtale (A := A) V) ≅ V := by
  have hid : A.left.map (simplexHom (OrderHom.id : Fin (n.len + 1) →o _)).op =
      𝟙 _ := A.left.map_id (op n)
  have sq := (spacesBaseChange B S hS
    (A.left.map (simplexHom (OrderHom.id : Fin (n.len + 1) →o _)).op)).isPullback V
  haveI : IsIso (A.left.map (simplexHom (OrderHom.id : Fin (n.len + 1) →o _)).op) :=
    hid ▸ inferInstance
  exact (IsEtaleOver B S hS _).isoMk (Over.isoMk (@asIso _ _ _ _ _ sq.isIso_fst_of_isIso)
    (sq.w.trans ((congrArg (fun t ↦ _ ≫ t) hid).trans (Category.comp_id _))))

/-- The realization functor is essentially surjective. -/
instance (n : SimplexCategory) : (realizeFunctor (A := A) n).EssSurj :=
  ⟨fun V ↦ ⟨ofSpacesEtale V, ⟨realizeOfSpacesEtaleIso V⟩⟩⟩

/-- The realization functor is an equivalence of categories. -/
instance (n : SimplexCategory) : (realizeFunctor (A := A) n).IsEquivalence where

/-- **Section 0DE7, the transitions.** The transition along `ψ : [n] → [k]`, base change along
`U(ψ) : U_k → U_n`: it composes formal base changes with `ψ` and transports morphisms along the
cartesian comparison squares. -/
def transition {n k : SimplexCategory} (ψ : n ⟶ k) : EtaleComponent A n ⥤ EtaleComponent A k where
  obj x := Index.push ψ x
  map {x y} f := InducedCategory.homMk (transportAlong (A.left.map ψ.op)
    (isPullback_comparison ψ x).toCommSq (isPullback_comparison ψ y) f.hom)
  map_id x := InducedCategory.hom_ext (transportAlong_id (isPullback_comparison ψ x))
  map_comp {x y z} f g := InducedCategory.hom_ext
    (transportAlong_comp (isPullback_comparison ψ x).toCommSq (isPullback_comparison ψ y)
      (isPullback_comparison ψ z) f.hom g.hom)

/-- The transition acts on a morphism by transport along the comparison squares. -/
theorem transition_map_hom {n k : SimplexCategory} (ψ : n ⟶ k) {x y : EtaleComponent A n}
    (f : x ⟶ y) :
    ((transition ψ).map f).hom = transportAlong (A.left.map ψ.op)
      (isPullback_comparison ψ x).toCommSq (isPullback_comparison ψ y) f.hom :=
  rfl

/-- The image of `f` under the transition is compatible with `f` through the comparison
morphisms. -/
@[reassoc (attr := simp)]
theorem transition_map_hom_comp {n k : SimplexCategory} (ψ : n ⟶ k) {x y : EtaleComponent A n}
    (f : x ⟶ y) :
    ((transition ψ).map f).hom.hom.left ≫ comparison ψ y = comparison ψ x ≫ f.hom.hom.left :=
  transportAlong_comp_q (isPullback_comparison ψ x).toCommSq (isPullback_comparison ψ y) f.hom

/-- The transition along the identity sends each morphism to itself, up to the identification of
its source and target. -/
theorem transition_map_id_heq {n : SimplexCategory} {x y : EtaleComponent A n} (f : x ⟶ y) :
    HEq ((transition (𝟙 n)).map f) f := by
  rcases x with V | ⟨m, φ, V⟩ <;> rcases y with W | ⟨m', φ', W⟩ <;>
  · refine heq_of_eq (InducedCategory.hom_ext ?_)
    refine (transportAlong_eq_iff (isPullback_comparison _ _).toCommSq _ _ _).2 ?_
    first
    | rw [comparison_id_inl, comparison_id_inl]
    | rw [comparison_id_inl, comparison_id_inr]
    | rw [comparison_id_inr, comparison_id_inl]
    | rw [comparison_id_inr, comparison_id_inr]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The transition along the identity is the identity functor. -/
theorem transition_id (n : SimplexCategory) : transition (A := A) (𝟙 n) = 𝟭 _ :=
  CategoryTheory.Functor.hext (fun x ↦ Index.push_id (A := A) x)
    (fun _ _ f ↦ transition_map_id_heq f)

/-- The transition along `ψ ≫ χ` agrees on morphisms with the transition along `ψ` followed by
that along `χ`, up to the identification of sources and targets. -/
theorem transition_map_comp_heq {n k l : SimplexCategory} (ψ : n ⟶ k) (χ : k ⟶ l)
    {x y : EtaleComponent A n} (f : x ⟶ y) :
    HEq ((transition (ψ ≫ χ)).map f) ((transition χ).map ((transition ψ).map f)) := by
  rcases x with V | ⟨m, φ, V⟩ <;> rcases y with W | ⟨m', φ', W⟩ <;>
  · refine heq_of_eq (InducedCategory.hom_ext ?_)
    refine (transportAlong_eq_iff (isPullback_comparison _ _).toCommSq _ _ _).2 ?_
    first
    | rw [comparison_comp_inl, comparison_comp_inl]
    | rw [comparison_comp_inl, comparison_comp_inr]
    | rw [comparison_comp_inr, comparison_comp_inl]
    | rw [comparison_comp_inr, comparison_comp_inr]
    exact ((Category.assoc _ _ _).symm.trans (congrArg (fun t ↦ t ≫ _)
      (transition_map_hom_comp χ ((transition ψ).map f)))).trans
        (((Category.assoc _ _ _).trans (congrArg (fun t ↦ _ ≫ t)
          (transition_map_hom_comp ψ f))).trans (Category.assoc _ _ _).symm)

/-- The transition along `ψ ≫ χ` is the transition along `ψ` followed by that along `χ`. -/
theorem transition_comp {n k l : SimplexCategory} (ψ : n ⟶ k) (χ : k ⟶ l) :
    transition (A := A) (ψ ≫ χ) = transition ψ ⋙ transition χ :=
  CategoryTheory.Functor.hext (fun x ↦ Index.push_comp (A := A) ψ χ x)
    (fun _ _ f ↦ transition_map_comp_heq ψ χ f)

end EtaleComponent

/-- **Section 0DE7.** The strict cosimplicial diagram of the components
`n ↦ U_{n, spaces, étale}`, with the base-change transitions. -/
def etaleComponentsFunctor : SimplexCategory ⥤ Cat.{u + 1, u + 1} where
  obj n := Cat.of (EtaleComponent A n)
  map ψ := (EtaleComponent.transition ψ).toCatHom
  map_id n := Cat.Hom.ext (EtaleComponent.transition_id n)
  map_comp ψ χ := Cat.Hom.ext (EtaleComponent.transition_comp ψ χ)

end AlgebraicGeometry.Space

end
