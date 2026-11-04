module

public import Mathlib.CategoryTheory.Sites.CoverLifting
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Sheaves.Sheaf
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Functors.FMap.Comp
public import StacksFrontier.Topology.Simplicial.ComponentInclusion

/-!
# Sheaves on the site of a simplicial space

For a simplicial topological space `X`, a sheaf on its total site is equivalently a system of
sheaves on the spaces `X n`, with restriction maps along every simplex map. The composition and
identity requirements on those restriction maps are encoded by the functor laws of the underlying
presheaf on the total category. The construction works for sheaves valued in any category.

## Main definitions

* `Stacks.Topology.Simplicial.SimplicialSheafSystem`: the category of families of sheaves with
  compatible normalized transition maps.
* `Stacks.Topology.Simplicial.SimplicialSheafSystem.Hom`: compatible families of component
  morphisms.
* `Stacks.Topology.Simplicial.SimplicialSheafSystem.componentFunctor`: evaluation of a system in
  one simplicial degree.
* `Stacks.Topology.Simplicial.SimplicialSheafSystem.transitionHom` and `transitionMap`: the
  canonical arrow over a simplex map, and the `f`-map it induces on a total presheaf.
* `Stacks.Topology.Simplicial.componentSheafFunctor`: restriction of a sheaf on the total site
  to the opens of one degree.
* `Stacks.Topology.Simplicial.sheafToSimplicialSheafSystem`: a sheaf on the total site, as the
  system of its degreewise restrictions and its restriction maps over simplex maps.
* `Stacks.Topology.Simplicial.SheafSystemEquivalence`: an equivalence together with its
  identification over the category of presheaves on all simplicial opens and its component
  identifications.
* `Stacks.Topology.Simplicial.sheafEquivalenceSimplicialSheafSystem`: the equivalence with
  forward functor `sheafToSimplicialSheafSystem`, with the reconstruction of total presheaves.

## Main results

* `Stacks.Topology.Simplicial.isEquivalence_sheafToSimplicialSheafSystem`: the functor
  `sheafToSimplicialSheafSystem` is an equivalence of categories (Stacks 09VM).

## Implementation notes

The systems are given directly by component sheaves and `StacksFMap` transition maps. Their
composition and identity laws are explicit fields. The equivalence includes reconstruction of
the total presheaf and its canonical identification with the original sheaf.

## References

* [Stacks Project, Tag 09VM](https://stacks.math.columbia.edu/tag/09VM)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open CategoryTheory.Limits

universe u v w

namespace Stacks.Topology.Simplicial

variable {X : SimplicialObject TopCat.{u}}
variable {A : Type w} [Category.{v} A]

/-- A normalized system of sheaves on the degrees of a simplicial space. The transition
maps are `X.map φ`-maps, and their composition and identity laws are stated on every open. -/
structure SimplicialSheafSystem (X : SimplicialObject TopCat.{u})
    (A : Type w) [Category.{v} A] where
  /-- The component sheaf in each simplicial degree. -/
  component : ∀ n : SimplexCategoryᵒᵖ, TopCat.Sheaf A (X.obj n)
  /-- The transition `f`-map attached to a map of simplicial degrees. -/
  transition : ∀ {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m),
    StacksFMap (X.map φ)
      ((TopCat.Sheaf.forget A (X.obj n)).obj (component n))
      ((TopCat.Sheaf.forget A (X.obj m)).obj (component m))
  /-- Transition along an identity is an identity. -/
  transition_id : ∀ (n : SimplexCategoryᵒᵖ) (V : (Opens (X.obj n))ᵒᵖ),
    HEq ((transition (𝟙 n)).app V)
      (𝟙 (((TopCat.Sheaf.forget A (X.obj n)).obj (component n)).obj V))
  /-- Transition along a composite is the composite of the transitions. -/
  transition_comp : ∀ {l m n : SimplexCategoryᵒᵖ} (φ : l ⟶ m) (ψ : m ⟶ n)
    (V : (Opens (X.obj n))ᵒᵖ),
    HEq (((transition φ).compPresheaf (transition ψ)).app V)
      ((transition (φ ≫ ψ)).app V)

namespace SimplicialSheafSystem

/-- A morphism of systems consists of compatible morphisms of all component sheaves. -/
structure Hom (S T : SimplicialSheafSystem X A) where
  /-- The morphism of component sheaves in each simplicial degree. -/
  componentHom : ∀ n : SimplexCategoryᵒᵖ, S.component n ⟶ T.component n
  /-- Compatibility of the component morphisms with the transition maps. -/
  naturality : ∀ {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    (V : (Opens (X.obj m))ᵒᵖ),
    (S.transition φ).app V ≫
      ((TopCat.Sheaf.forget A (X.obj n)).map (componentHom n)).app
        (op ((Opens.map (X.map φ)).obj V.unop)) =
      ((TopCat.Sheaf.forget A (X.obj m)).map (componentHom m)).app V ≫
        (T.transition φ).app V

/-- Two morphisms of systems with the same components are equal. -/
@[ext] theorem Hom.ext {S T : SimplicialSheafSystem X A} (f g : Hom S T)
    (h : ∀ n, f.componentHom n = g.componentHom n) : f = g := by
  cases f
  cases g
  obtain rfl : _ = _ := funext h
  rfl

/-- Simplicial sheaf systems form a category, with morphisms the compatible families of
component morphisms, composed componentwise. -/
noncomputable instance : Category (SimplicialSheafSystem X A) where
  Hom := Hom
  id S := by
    refine { componentHom := fun _ => 𝟙 _, naturality := ?_ }
    intro n m φ V
    change (S.transition φ).app V ≫ 𝟙 _ = 𝟙 _ ≫ (S.transition φ).app V
    simp
  comp f g :=
    { componentHom := fun n => f.componentHom n ≫ g.componentHom n
      naturality := by
        intro n m φ V
        simp only [Functor.map_comp]
        change _ ≫ (_ ≫ _) = (_ ≫ _) ≫ _
        rw [← Category.assoc, f.naturality φ V, Category.assoc,
          g.naturality φ V]
        simp only [Category.assoc] }
  id_comp f := by apply Hom.ext; intro n; simp
  comp_id f := by apply Hom.ext; intro n; simp
  assoc f g h := by
    dsimp
    apply Hom.ext
    intro n
    exact Category.assoc _ _ _

/-- Evaluation of a system at one simplicial degree. -/
def componentFunctor (X : SimplicialObject TopCat.{u}) (A : Type w) [Category.{v} A]
    (n : SimplexCategoryᵒᵖ) :
    SimplicialSheafSystem X A ⥤ TopCat.Sheaf A (X.obj n) where
  obj S := S.component n
  map f := f.componentHom n
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The morphism of simplicial opens over `φ` obtained by restricting the target open to its
inverse image. -/
def transitionHom {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m)
    (V : Opens (X.obj m)) :
    (⟨n, (Opens.map (X.map φ)).obj V⟩ : SimplicialOpen X) ⟶ ⟨m, V⟩ where
  base := φ
  le := le_rfl

/-- The `X.map φ`-map extracted from a total presheaf. Its naturality field is compatibility
with restriction inside a fixed degree. -/
def transitionMap (P : (SimplicialOpen X)ᵒᵖ ⥤ A) {n m : SimplexCategoryᵒᵖ}
    (φ : n ⟶ m) :
    StacksFMap (X.map φ) (componentPresheaf P n) (componentPresheaf P m) where
  app V := P.map (transitionHom φ V.unop).op
  naturality h := by
    dsimp [componentPresheaf, levelFunctor]
    rw [← P.map_comp, ← P.map_comp]
    congr 1

private lemma eqToHom_base_self {n : SimplexCategoryᵒᵖ} {W U : Opens (X.obj n)}
    (h : (⟨n, W⟩ : SimplicialOpen X) = ⟨n, U⟩) : (eqToHom h).base = 𝟙 n := by
  cases h
  rfl

/-- The transition map of a total presheaf along an identity simplex map is the identity on
every open. -/
lemma transitionMap_id_app (P : (SimplicialOpen X)ᵒᵖ ⥤ A)
    (n : SimplexCategoryᵒᵖ) (V : (Opens (X.obj n))ᵒᵖ) :
    HEq ((transitionMap P (𝟙 n)).app V) (𝟙 ((componentPresheaf P n).obj V)) := by
  show HEq
    (P.map (transitionHom (𝟙 n) V.unop).op) (𝟙 _)
  let U : Opens (X.obj n) := V.unop
  let W : Opens (X.obj n) := (Opens.map (X.map (𝟙 n))).obj U
  have e : W = U := by simp [W]
  let hobj : (⟨n, W⟩ : SimplicialOpen X) = ⟨n, U⟩ :=
    congrArg (fun T => (⟨n, T⟩ : SimplicialOpen X)) e
  have h : transitionHom (𝟙 n) U = eqToHom hobj :=
    SimplicialOpen.Hom.ext _ _ (eqToHom_base_self hobj).symm
  rw [h, eqToHom_op, eqToHom_map]
  exact eqToHom_heq_id_dom _ _ _

/-- The transition map of a total presheaf along a composite `φ ≫ ψ` is the composite of the
transition maps along `φ` and `ψ`, on every open. -/
lemma transitionMap_comp_app (P : (SimplicialOpen X)ᵒᵖ ⥤ A)
    {l m n : SimplexCategoryᵒᵖ} (φ : l ⟶ m) (ψ : m ⟶ n)
    (V : (Opens (X.obj n))ᵒᵖ) :
    HEq (((transitionMap P φ).compPresheaf (transitionMap P ψ)).app V)
      ((transitionMap P (φ ≫ ψ)).app V) := by
  show HEq
    (P.map (transitionHom ψ V.unop).op ≫
      P.map (transitionHom φ ((Opens.map (X.map ψ)).obj V.unop)).op)
    (P.map (transitionHom (φ ≫ ψ) V.unop).op)
  let U : Opens (X.obj n) := V.unop
  let W₁ : Opens (X.obj m) := (Opens.map (X.map ψ)).obj U
  let W₂ : Opens (X.obj l) := (Opens.map (X.map φ)).obj W₁
  let W : Opens (X.obj l) := (Opens.map (X.map (φ ≫ ψ))).obj U
  have e : W = W₂ := by simp [W, W₂, W₁, Functor.map_comp]
  let hobj : (⟨l, W⟩ : SimplicialOpen X) = ⟨l, W₂⟩ :=
    congrArg (fun T => (⟨l, T⟩ : SimplicialOpen X)) e
  let k : (⟨l, W₂⟩ : SimplicialOpen X) ⟶ ⟨n, U⟩ :=
    transitionHom φ W₁ ≫ transitionHom ψ U
  let c : (⟨l, W⟩ : SimplicialOpen X) ⟶ ⟨n, U⟩ := transitionHom (φ ≫ ψ) U
  have h : eqToHom hobj ≫ k = c := by
    apply SimplicialOpen.Hom.ext
    show ((eqToHom hobj).base ≫ φ) ≫ ψ = φ ≫ ψ
    rw [eqToHom_base_self hobj]
    simp
  have hmap := congrArg (fun f => P.map f.op) h
  have eP : P.obj (op (⟨l, W₂⟩ : SimplicialOpen X)) =
      P.obj (op (⟨l, W⟩ : SimplicialOpen X)) :=
    congrArg P.obj (congrArg op hobj.symm)
  have hmap' :
      (P.map k.op) ≫ eqToHom eP = P.map c.op := by
    simpa only [op_comp, Functor.map_comp, eqToHom_op, eqToHom_map] using hmap
  have htransition : HEq (P.map k.op) (P.map c.op) :=
    (comp_eqToHom_heq_iff _ _ eP).mp (heq_of_eq hmap')
  show HEq
    (P.map (transitionHom ψ U).op ≫ P.map (transitionHom φ W₁).op)
    (P.map (transitionHom (φ ≫ ψ) U).op)
  have hk : P.map k.op =
      P.map (transitionHom ψ U).op ≫ P.map (transitionHom φ W₁).op := by
    simp [k, ← P.map_comp, ← op_comp]
  rw [← hk]
  exact htransition

end SimplicialSheafSystem

/-- Restriction to a simplicial degree, as a functor on sheaf categories: the sheaf
`F ↦ F_n` on `X n`, pushed forward along the inclusion of the opens of `X n` into the site. -/
noncomputable def componentSheafFunctor (X : SimplicialObject TopCat.{u})
    (A : Type w) [Category.{v} A] (n : SimplexCategoryᵒᵖ) :
    Sheaf (SimplicialOpen.grothendieckTopology X) A ⥤ TopCat.Sheaf A (X.obj n) := by
  let := levelFunctor_isContinuous X n
  exact (levelFunctor X n).sheafPushforwardContinuous A
    (Opens.grothendieckTopology (X.obj n)) (SimplicialOpen.grothendieckTopology X)

/-- The functor of Stacks 09VM from sheaves on the site of `X` to systems of degreewise
sheaves. A sheaf `F` goes to the system whose degree-`n` component is the restriction
`componentSheafFunctor X A n` of `F` to the opens of `X n`, and whose transition map over a
simplex map `φ` is the `X.map φ`-map given by the restriction maps of `F` along
`transitionHom φ`. -/
noncomputable def sheafToSimplicialSheafSystem :
    Sheaf (SimplicialOpen.grothendieckTopology X) A ⥤ SimplicialSheafSystem X A where
  obj F := by
    let P := (sheafToPresheaf (SimplicialOpen.grothendieckTopology X) A).obj F
    refine
      { component := fun n => (componentSheafFunctor X A n).obj F
        transition := fun φ => SimplicialSheafSystem.transitionMap P φ
        transition_id := ?_
        transition_comp := ?_ }
    · intro n V
      exact SimplicialSheafSystem.transitionMap_id_app P n V
    · intro l m n φ ψ V
      exact SimplicialSheafSystem.transitionMap_comp_app P φ ψ V
  map {F G} f := by
    let P := (sheafToPresheaf (SimplicialOpen.grothendieckTopology X) A).obj F
    let Q := (sheafToPresheaf (SimplicialOpen.grothendieckTopology X) A).obj G
    refine
      { componentHom := fun n => (componentSheafFunctor X A n).map f
        naturality := ?_ }
    intro n m φ V
    dsimp [componentSheafFunctor, Functor.sheafPushforwardContinuous]
    change P.map (SimplicialSheafSystem.transitionHom φ V.unop).op ≫
        f.hom.app (op ((levelFunctor X n).obj
          ((Opens.map (X.map φ)).obj V.unop))) =
      f.hom.app (op ((levelFunctor X m).obj V.unop)) ≫
        Q.map (SimplicialSheafSystem.transitionHom φ V.unop).op
    exact f.hom.naturality (SimplicialSheafSystem.transitionHom φ V.unop).op
  map_id F := SimplicialSheafSystem.Hom.ext _ _ fun n => (componentSheafFunctor X A n).map_id F
  map_comp f g :=
    SimplicialSheafSystem.Hom.ext _ _ fun n => (componentSheafFunctor X A n).map_comp f g

/-- Restriction along a morphism in the simplicial-open category, constructed from the
transition map and the component restriction. -/
private def systemRestriction (S : SimplicialSheafSystem X A)
    {U V : SimplicialOpen X} (f : U ⟶ V) :
    (S.component V.degree).obj.obj (op V.toOpens) ⟶
      (S.component U.degree).obj.obj (op U.toOpens) := by
  exact (S.transition f.base).app (op V.toOpens) ≫
      ((TopCat.Sheaf.forget A (X.obj U.degree)).obj (S.component U.degree)).map
      (homOfLE (SimplicialOpen.Hom.le f)).op

/-- Restriction along the canonical arrow over a simplex map is the transition map itself. -/
private lemma systemRestriction_transitionHom (S : SimplicialSheafSystem X A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (V : Opens (X.obj m)) :
    systemRestriction S (SimplicialSheafSystem.transitionHom φ V) =
      (S.transition φ).app (op V) := by
  let F := (TopCat.Sheaf.forget A (X.obj n)).obj (S.component n)
  show (S.transition φ).app (op V) ≫ F.map (𝟙 _) = (S.transition φ).app (op V)
  rw [F.map_id, Category.comp_id]

private lemma systemRestriction_extracted (F : Sheaf (SimplicialOpen.grothendieckTopology X) A)
    {U V : SimplicialOpen X} (f : U ⟶ V) :
    systemRestriction (sheafToSimplicialSheafSystem.obj F) f =
      ((sheafToPresheaf (SimplicialOpen.grothendieckTopology X) A).obj F).map f.op := by
  let P := (sheafToPresheaf (SimplicialOpen.grothendieckTopology X) A).obj F
  let G := levelFunctor X U.degree
  let a : U.toOpens ⟶ (Opens.map (X.map f.base)).obj V.toOpens :=
    homOfLE (SimplicialOpen.Hom.le f)
  have hfactor : G.map a ≫ SimplicialSheafSystem.transitionHom f.base V.toOpens = f := by
    apply SimplicialOpen.Hom.ext
    show 𝟙 U.degree ≫ f.base = f.base
    simp
  show P.map (SimplicialSheafSystem.transitionHom f.base V.toOpens).op ≫
    P.map (G.map a).op = P.map f.op
  dsimp [G, levelFunctor, SimplicialSheafSystem.transitionHom] at hfactor ⊢
  rw [← P.map_comp, ← op_comp]
  exact congrArg (fun g => P.map g.op) hfactor

private def transportOpen (n m : SimplexCategoryᵒᵖ) (e : n = m)
    (U : Opens (X.obj n)) : Opens (X.obj m) := cast (congrArg (fun d => Opens (X.obj d)) e) U

private def transportPoint (n m : SimplexCategoryᵒᵖ) (e : n = m)
    (x : X.obj n) : X.obj m := cast (congrArg (fun d => (X.obj d : Type u)) e) x

private lemma transportPoint_mem_transportOpen {n m : SimplexCategoryᵒᵖ} (e : n = m)
    (U : Opens (X.obj n)) (x : X.obj n) :
    transportPoint n m e x ∈ transportOpen n m e U ↔ x ∈ U := by
  cases e
  rfl

private lemma levelwise_sourceOpen_le {U V : SimplicialOpen X} (f : V ⟶ U)
    (e : V.degree = U.degree) (he : f.base = eqToHom e) :
    transportOpen V.degree U.degree e V.toOpens ≤ U.toOpens := by
  cases U with
  | mk ud uo =>
  cases V with
  | mk vd vo =>
  cases e
  have hb : f.base = 𝟙 ud := by simpa using he
  have hf : vo ≤ (Opens.map (X.map f.base)).obj uo := SimplicialOpen.Hom.le f
  rw [hb, X.map_id] at hf
  simpa [transportOpen] using hf

private def levelwiseSourceIso {U V : SimplicialOpen X} (e : V.degree = U.degree) :
    (levelFunctor X U.degree).obj (transportOpen V.degree U.degree e V.toOpens) ≅ V := by
  cases U with
  | mk ud uo =>
    cases V with
    | mk vd vo =>
      cases e
      exact Iso.refl _

private lemma levelwise_factorization {U V : SimplicialOpen X} (f : V ⟶ U)
    (e : V.degree = U.degree) (he : f.base = eqToHom e) :
    (levelwiseSourceIso (X := X) e).hom ≫ f =
      (levelFunctor X U.degree).map
        (homOfLE (levelwise_sourceOpen_le (X := X) f e he)) := by
  cases U with
  | mk ud uo =>
    cases V with
    | mk vd vo =>
      cases e
      apply SimplicialOpen.Hom.ext
      have hb : f.base = 𝟙 ud := by simpa using he
      show 𝟙 ud ≫ f.base = 𝟙 ud
      rw [hb]
      simp

private lemma levelwise_map_apply {U V : SimplicialOpen X} (f : V ⟶ U)
    (e : V.degree = U.degree) (he : f.base = eqToHom e) (x : X.obj V.degree) :
    (X.map f.base).hom x = transportPoint V.degree U.degree e x := by
  cases U with
  | mk ud uo =>
    cases V with
    | mk vd vo =>
      cases e
      have hb : f.base = 𝟙 ud := by simpa using he
      simp [hb, transportPoint]

private lemma heq_comp_eqToHom {C : Type*} [Category C] {a b c : C}
    {f : a ⟶ b} {g : a ⟶ c} (e : b = c) (h : HEq f g) :
    f ≫ eqToHom e = g := by
  cases e
  simpa using eq_of_heq h

private lemma systemRestriction_id (S : SimplicialSheafSystem X A)
    (n : SimplexCategoryᵒᵖ) (V : Opens (X.obj n)) :
    systemRestriction S (SimplicialOpen.Hom.id ⟨n, V⟩) = 𝟙 _ := by
  dsimp [systemRestriction]
  let F := (TopCat.Sheaf.forget A (X.obj n)).obj (S.component n)
  let f : SimplicialOpen.Hom ⟨n, V⟩ ⟨n, V⟩ := SimplicialOpen.Hom.id ⟨n, V⟩
  let W := (Opens.map (X.map f.base)).obj V
  have e : W = V := by
    dsimp [W, f, SimplicialOpen.Hom.id]
    rw [X.map_id]
    exact Opens.map_id_obj V
  have htrans := S.transition_id n (op V)
  have hcast : (S.transition f.base).app (op V) ≫
      eqToHom (congrArg (fun U : Opens (X.obj n) => F.obj (op U)) e) = 𝟙 _ :=
    heq_comp_eqToHom _ htrans
  have hinc : homOfLE f.le = eqToHom e.symm := Subsingleton.elim _ _
  rw [hinc]
  have hmap : F.map (eqToHom e.symm).op =
      eqToHom (congrArg (fun U : Opens (X.obj n) => F.obj (op U)) e) := by
    simp only [eqToHom_op, eqToHom_map]
  show (S.transition (SimplicialOpen.Hom.id ⟨n, V⟩).base).app (op V) ≫
      F.map (eqToHom e.symm).op = 𝟙 (F.obj (op V))
  rw [hmap]
  exact hcast

private lemma systemRestriction_levelwise (S : SimplicialSheafSystem X A)
    (n : SimplexCategoryᵒᵖ) {V W : Opens (X.obj n)} (h : V ≤ W) :
    systemRestriction S ((levelFunctor X n).map (homOfLE h)) =
      ((TopCat.Sheaf.forget A (X.obj n)).obj (S.component n)).map (homOfLE h).op := by
  let F := (TopCat.Sheaf.forget A (X.obj n)).obj (S.component n)
  let D := (Opens.map (X.map (𝟙 n))).obj W
  let k : W ⟶ D := homOfLE (SimplicialOpen.Hom.le (SimplicialOpen.Hom.id ⟨n, W⟩))
  let i : V ⟶ D := homOfLE (SimplicialOpen.Hom.le ((levelFunctor X n).map (homOfLE h)))
  have hid : (S.transition (𝟙 n)).app (op W) ≫ F.map k.op = 𝟙 _ :=
    systemRestriction_id S n W
  change (S.transition (𝟙 n)).app (op W) ≫ F.map i.op = F.map (homOfLE h).op
  rw [show i = homOfLE h ≫ k from Subsingleton.elim _ _, op_comp, F.map_comp,
    ← Category.assoc, hid, Category.id_comp]

private lemma systemRestriction_comp (S : SimplicialSheafSystem X A)
    {U V W : SimplicialOpen X} (f : U ⟶ V) (g : V ⟶ W) :
    systemRestriction S g ≫ systemRestriction S f = systemRestriction S (f ≫ g) := by
  show ((S.transition g.base).app (op W.toOpens) ≫
      ((TopCat.Sheaf.forget A (X.obj V.degree)).obj (S.component V.degree)).map
        (homOfLE (SimplicialOpen.Hom.le g)).op) ≫
      ((S.transition f.base).app (op V.toOpens) ≫
        ((TopCat.Sheaf.forget A (X.obj U.degree)).obj (S.component U.degree)).map
          (homOfLE (SimplicialOpen.Hom.le f)).op) =
    (S.transition (f.base ≫ g.base)).app (op W.toOpens) ≫
      ((TopCat.Sheaf.forget A (X.obj U.degree)).obj (S.component U.degree)).map
        (homOfLE (SimplicialOpen.Hom.le (f ≫ g))).op
  simp only [Category.assoc]
  rw [reassoc_of% (S.transition f.base).naturality
    (homOfLE (SimplicialOpen.Hom.le g)).op]
  let F := (TopCat.Sheaf.forget A (X.obj U.degree)).obj (S.component U.degree)
  let D := (Opens.map (X.map (f.base ≫ g.base))).obj W.toOpens
  let E := (Opens.map (X.map f.base)).obj ((Opens.map (X.map g.base)).obj W.toOpens)
  have e : D = E := by simp [D, E, Functor.map_comp]
  let eF : F.obj (op D) = F.obj (op E) :=
    congrArg (fun T : Opens (X.obj U.degree) => F.obj (op T)) e
  have hcomp :
      HEq ((S.transition g.base).app (op W.toOpens) ≫
        (S.transition f.base).app (op ((Opens.map (X.map g.base)).obj W.toOpens)))
        ((S.transition (f.base ≫ g.base)).app (op W.toOpens)) := by
    simpa only [StacksFMap.compPresheaf_app, Functor.map_comp,
      Opens.map_comp_obj] using
      S.transition_comp f.base g.base (op W.toOpens)
  have htrans := heq_comp_eqToHom eF.symm hcomp
  have hinc :
      homOfLE (SimplicialOpen.Hom.le f) ≫
        (Opens.map (X.map f.base)).map (homOfLE (SimplicialOpen.Hom.le g)) ≫
        eqToHom e.symm = homOfLE (SimplicialOpen.Hom.le (f ≫ g)) := by
    apply Subsingleton.elim
  have hfull : F.map (eqToHom e.symm).op ≫
      F.map ((Opens.map (X.map f.base)).map (homOfLE (SimplicialOpen.Hom.le g))).op ≫
      F.map (homOfLE (SimplicialOpen.Hom.le f)).op =
      F.map (homOfLE (SimplicialOpen.Hom.le (f ≫ g))).op := by
    have h := congrArg F.map (congrArg (fun k => k.op) hinc)
    simpa only [← Functor.map_comp, ← op_comp, hinc]
  let p := F.map ((Opens.map (X.map f.base)).map
      (homOfLE (SimplicialOpen.Hom.le g))).op ≫
    F.map (homOfLE (SimplicialOpen.Hom.le f)).op
  let q := F.map (homOfLE (SimplicialOpen.Hom.le (f ≫ g))).op
  have hfull' : eqToHom eF ≫
      p = q := by simpa only [p, q, eqToHom_op, eqToHom_map] using hfull
  have hmaps : p = eqToHom eF.symm ≫ q := (eqToHom_comp_iff _ _ _).mp hfull'
  have hrestriction :
      F.map ((Opens.map (X.map f.base)).op.map
          (homOfLE (SimplicialOpen.Hom.le g)).op ≫
        (homOfLE (SimplicialOpen.Hom.le f)).op) =
      F.map ((homOfLE (SimplicialOpen.Hom.le f) ≫
        (Opens.map (X.map f.base)).map (homOfLE (SimplicialOpen.Hom.le g))).op) := by
    congr 1
  calc
    _ = ((S.transition g.base).app (op W.toOpens) ≫
        (S.transition f.base).app (op ((Opens.map (X.map g.base)).obj W.toOpens))) ≫ p := by
      simp only [p, ← Functor.map_comp, ← op_comp, Category.assoc]
      rw [hrestriction]
    _ = ((S.transition g.base).app (op W.toOpens) ≫
        (S.transition f.base).app (op ((Opens.map (X.map g.base)).obj W.toOpens))) ≫
        (eqToHom eF.symm ≫ q) := by rw [hmaps]
    _ = (((S.transition g.base).app (op W.toOpens) ≫
        (S.transition f.base).app (op ((Opens.map (X.map g.base)).obj W.toOpens))) ≫
        eqToHom eF.symm) ≫ q := (Category.assoc _ _ _).symm
    _ = _ := by rw [htrans]; rfl

/-- The presheaf reconstructed from a simplicial sheaf system. -/
private def systemPresheaf (S : SimplicialSheafSystem X A) : (SimplicialOpen X)ᵒᵖ ⥤ A where
  obj U := ((TopCat.Sheaf.forget A (X.obj U.unop.degree)).obj
    (S.component U.unop.degree)).obj (op U.unop.toOpens)
  map f := systemRestriction S f.unop
  map_id U := by
    change systemRestriction S (SimplicialOpen.Hom.id U.unop) = 𝟙 _
    exact systemRestriction_id S U.unop.degree U.unop.toOpens
  map_comp f g := (systemRestriction_comp S g.unop f.unop).symm

private noncomputable def systemPresheafFunctor :
    SimplicialSheafSystem X A ⥤ (SimplicialOpen X)ᵒᵖ ⥤ A where
  obj := systemPresheaf
  map {S T} f :=
    { app U := ((TopCat.Sheaf.forget A (X.obj U.unop.degree)).map
        (f.componentHom U.unop.degree)).app (op U.unop.toOpens)
      naturality := by
        intro U V g
        let h := g.unop
        let i := (homOfLE (SimplicialOpen.Hom.le h)).op
        let ηV := (TopCat.Sheaf.forget A (X.obj V.unop.degree)).map
          (f.componentHom V.unop.degree)
        let ηU := (TopCat.Sheaf.forget A (X.obj U.unop.degree)).map
          (f.componentHom U.unop.degree)
        let FV := (TopCat.Sheaf.forget A (X.obj V.unop.degree)).obj
          (S.component V.unop.degree)
        let GV := (TopCat.Sheaf.forget A (X.obj V.unop.degree)).obj
          (T.component V.unop.degree)
        change ((S.transition h.base).app (op U.unop.toOpens) ≫ FV.map i) ≫
            ηV.app (op V.unop.toOpens) =
          ηU.app (op U.unop.toOpens) ≫
            ((T.transition h.base).app (op U.unop.toOpens) ≫ GV.map i)
        rw [Category.assoc, ηV.naturality i, ← Category.assoc,
          f.naturality h.base (op U.unop.toOpens), Category.assoc] }
  map_id S := by
    ext U
    rfl
  map_comp f g := by
    ext U
    rfl

/-- The transition maps extracted from the reconstructed presheaf are the original ones. -/
private lemma systemPresheaf_transitionMap_app (S : SimplicialSheafSystem X A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (V : (Opens (X.obj m))ᵒᵖ) :
    (SimplicialSheafSystem.transitionMap (systemPresheaf S) φ).app V =
      (S.transition φ).app V :=
  systemRestriction_transitionHom S φ V.unop

private lemma systemPresheaf_map_level (S : SimplicialSheafSystem X A)
    (n : SimplexCategoryᵒᵖ) {V W : Opens (X.obj n)} (h : V ≤ W) :
    (systemPresheaf S).map ((levelFunctor X n).map (homOfLE h)).op =
      ((TopCat.Sheaf.forget A (X.obj n)).obj (S.component n)).map (homOfLE h).op :=
  systemRestriction_levelwise S n h

private lemma systemPresheaf_map_levelFunctor (S : SimplicialSheafSystem X A)
    (n : SimplexCategoryᵒᵖ) {V W : Opens (X.obj n)} (a : V ⟶ W) :
    (systemPresheaf S).map ((levelFunctor X n).map a).op =
      ((TopCat.Sheaf.forget A (X.obj n)).obj (S.component n)).map a.op := by
  have ha : homOfLE (leOfHom a) = a := Subsingleton.elim _ _
  simpa [ha] using systemPresheaf_map_level S n (leOfHom a)

private lemma systemPresheaf_map_levelwise (S : SimplicialSheafSystem X A)
    {U V : SimplicialOpen X} (f : V ⟶ U) (e : V.degree = U.degree) (he : f.base = eqToHom e) :
    ((TopCat.Sheaf.forget A (X.obj U.degree)).obj (S.component U.degree)).map
        (homOfLE (levelwise_sourceOpen_le f e he)).op =
      (systemPresheaf S).map f.op ≫ (systemPresheaf S).map (levelwiseSourceIso e).hom.op := by
  rw [← systemPresheaf_map_levelFunctor S U.degree, ← levelwise_factorization f e he]
  exact (systemPresheaf S).map_comp f.op (levelwiseSourceIso e).hom.op

private lemma systemPresheaf_levelwise_compatible (S : SimplicialSheafSystem X A)
    {U V₁ V₂ : SimplicialOpen X} {E : A} (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U)
    (e₁ : V₁.degree = U.degree) (e₂ : V₂.degree = U.degree)
    (he₁ : f₁.base = eqToHom e₁) (he₂ : f₂.base = eqToHom e₂)
    (x₁ : E ⟶ (systemPresheaf S).obj (op V₁)) (x₂ : E ⟶ (systemPresheaf S).obj (op V₂))
    (hx : ∀ (Z : SimplicialOpen X) (g₁ : Z ⟶ V₁) (g₂ : Z ⟶ V₂), g₁ ≫ f₁ = g₂ ≫ f₂ →
      x₁ ≫ (systemPresheaf S).map g₁.op = x₂ ≫ (systemPresheaf S).map g₂.op)
    {W : Opens (X.obj U.degree)} (a : W ⟶ transportOpen V₁.degree U.degree e₁ V₁.toOpens)
    (b : W ⟶ transportOpen V₂.degree U.degree e₂ V₂.toOpens)
    (hab : a ≫ homOfLE (levelwise_sourceOpen_le f₁ e₁ he₁) =
      b ≫ homOfLE (levelwise_sourceOpen_le f₂ e₂ he₂)) :
    (x₁ ≫ (systemPresheaf S).map (levelwiseSourceIso e₁).hom.op) ≫
        ((TopCat.Sheaf.forget A (X.obj U.degree)).obj (S.component U.degree)).map a.op =
      (x₂ ≫ (systemPresheaf S).map (levelwiseSourceIso e₂).hom.op) ≫
        ((TopCat.Sheaf.forget A (X.obj U.degree)).obj (S.component U.degree)).map b.op := by
  have hmap : (levelFunctor X U.degree).map a ≫
      (levelFunctor X U.degree).map (homOfLE (levelwise_sourceOpen_le f₁ e₁ he₁)) =
      (levelFunctor X U.degree).map b ≫
        (levelFunctor X U.degree).map (homOfLE (levelwise_sourceOpen_le f₂ e₂ he₂)) := by
    simpa [Functor.map_comp] using congrArg (levelFunctor X U.degree).map hab
  have h := hx _ ((levelFunctor X U.degree).map a ≫ (levelwiseSourceIso e₁).hom)
    ((levelFunctor X U.degree).map b ≫ (levelwiseSourceIso e₂).hom) (by
      rw [Category.assoc, levelwise_factorization f₁ e₁ he₁, Category.assoc,
        levelwise_factorization f₂ e₂ he₂]
      exact hmap)
  rw [op_comp, Functor.map_comp, op_comp, Functor.map_comp, systemPresheaf_map_levelFunctor,
    systemPresheaf_map_levelFunctor] at h
  exact (Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)

private lemma systemPresheaf_isSheafFor_levelwise (S : SimplicialSheafSystem X A)
    {U : SimplicialOpen X} {ι : Type*} {V : ι → SimplicialOpen X} (f : ∀ i, V i ⟶ U)
    (e : ∀ i, (V i).degree = U.degree) (he : ∀ i, (f i).base = eqToHom (e i))
    (hopen : Sieve.ofArrows (fun i => transportOpen (V i).degree U.degree (e i) (V i).toOpens)
      (fun i => homOfLE (levelwise_sourceOpen_le (f i) (e i) (he i))) ∈
        Opens.grothendieckTopology (X.obj U.degree) U.toOpens) (E : A) :
    (Presieve.ofArrows V f).IsSheafFor (systemPresheaf S ⋙ coyoneda.obj (op E)) := by
  let opens (i : ι) : Opens (X.obj U.degree) :=
    transportOpen (V i).degree U.degree (e i) (V i).toOpens
  let inc (i : ι) : opens i ⟶ U.toOpens :=
    homOfLE (levelwise_sourceOpen_le (f i) (e i) (he i))
  apply (Presieve.isSheafFor_arrows_iff
    (systemPresheaf S ⋙ coyoneda.obj (op E)) f).2
  intro x hx
  let P := systemPresheaf S
  let F := ((TopCat.Sheaf.forget A (X.obj U.degree)).obj (S.component U.degree))
  let L := levelFunctor X U.degree
  let iso (i : ι) := levelwiseSourceIso (e i)
  let y (i : ι) : E ⟶ F.obj (op (opens i)) := x i ≫ P.map (iso i).hom.op
  have hF : Presheaf.IsSheaf (Opens.grothendieckTopology (X.obj U.degree)) F :=
    (S.component U.degree).property
  obtain ⟨t, ht, htuniq⟩ := hF.existsUnique_amalgamation_ofArrows inc hopen y
    fun W i j a b hab => systemPresheaf_levelwise_compatible S (f i) (f j) (e i) (e j)
      (he i) (he j) (x i) (x j) (fun Z gi gj h => hx i j Z gi gj h) a b hab
  have hfactorMap (i : ι) :
      F.map (inc i).op = P.map (f i).op ≫ P.map (iso i).hom.op :=
    systemPresheaf_map_levelwise S (f i) (e i) (he i)
  have hobjU : P.obj (op U) = F.obj (op U.toOpens) := rfl
  cases hobjU
  refine ⟨t, ?_, ?_⟩
  · intro i
    have hobjI : P.obj (op (L.obj (opens i))) = F.obj (op (opens i)) := rfl
    cases hobjI
    show t ≫ P.map (f i).op = x i
    have : IsIso (P.map (iso i).hom.op) := Functor.map_isIso P (iso i).hom.op
    apply (cancel_mono (P.map (iso i).hom.op)).mp
    have h₁ :
        (t ≫ P.map (f i).op) ≫ P.map (iso i).hom.op =
          t ≫ F.map (inc i).op :=
      (Category.assoc _ _ _).trans (congrArg (fun g => t ≫ g) (hfactorMap i).symm)
    exact h₁.trans (ht i)
  · intro t' ht'
    apply htuniq t'
    intro i
    have hobjI : P.obj (op (L.obj (opens i))) = F.obj (op (opens i)) := rfl
    cases hobjI
    show t' ≫ F.map (inc i).op = y i
    have h₁ : t' ≫ F.map (inc i).op =
        t' ≫ (P.map (f i).op ≫ P.map (iso i).hom.op) :=
      congrArg (fun g => t' ≫ g) (hfactorMap i)
    have h₂ : t' ≫ (P.map (f i).op ≫ P.map (iso i).hom.op) =
        (t' ≫ P.map (f i).op) ≫ P.map (iso i).hom.op :=
      (Category.assoc _ _ _).symm
    have h₃ : (t' ≫ P.map (f i).op) ≫ P.map (iso i).hom.op =
        x i ≫ P.map (iso i).hom.op :=
      congrArg (fun g => g ≫ P.map (iso i).hom.op) (ht' i)
    exact h₁.trans (h₂.trans h₃)

private lemma systemPresheaf_isSheaf (S : SimplicialSheafSystem X A) :
    Presheaf.IsSheaf (SimplicialOpen.grothendieckTopology X) (systemPresheaf S) := by
  let := SimplicialOpen.precoverage_hasPullbacks X
  let := SimplicialOpen.precoverage_isStableUnderBaseChange X
  show ∀ E : A, Presieve.IsSheaf (SimplicialOpen.precoverage X).toGrothendieck
    (systemPresheaf S ⋙ coyoneda.obj (op E))
  intro E
  rw [Precoverage.isSheaf_toGrothendieck_iff_of_isStableUnderBaseChange]
  intro U R hR
  change SimplicialOpen.IsCovering U R at hR
  let I := {p : Σ V : SimplicialOpen X, V ⟶ U // R p.2}
  let dom (i : I) : SimplicialOpen X := i.val.1
  let arr (i : I) : dom i ⟶ U := i.val.2
  have hR_eq : R = Presieve.ofArrows dom arr := by
    funext V f
    apply propext
    constructor
    · intro hf
      exact Presieve.ofArrows.mk (⟨⟨V, f⟩, hf⟩ : I)
    · rintro ⟨i, hi⟩
      exact hi
  have hlevel (i : I) : SimplicialOpen.IsLevelwise (arr i) :=
    hR.1 (dom i) (arr i) i.property
  let e (i : I) : (dom i).degree = U.degree := Classical.choose (hlevel i)
  have he (i : I) : (arr i).base = eqToHom (e i) := Classical.choose_spec (hlevel i)
  let opens (i : I) : Opens (X.obj U.degree) :=
    transportOpen (dom i).degree U.degree (e i) (dom i).toOpens
  let inc (i : I) : opens i ⟶ U.toOpens :=
    homOfLE (levelwise_sourceOpen_le (arr i) (e i) (he i))
  have hopen : Sieve.ofArrows opens inc ∈
      Opens.grothendieckTopology (X.obj U.degree) U.toOpens := by
    rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨V, f, hf, y, hy, hxy⟩ := hR.2 x hx
    let i : I := ⟨⟨V, f⟩, hf⟩
    refine ⟨opens i, inc i, Sieve.ofArrows_mk opens inc i, ?_⟩
    have hpoint : transportPoint (dom i).degree U.degree (e i) y = x := by
      rw [← levelwise_map_apply (arr i) (e i) (he i)]
      exact hxy
    rw [← hpoint]
    exact (transportPoint_mem_transportOpen (e i) (dom i).toOpens y).2 hy
  rw [hR_eq]
  exact systemPresheaf_isSheafFor_levelwise S arr e he hopen E

private noncomputable def systemToSheafFunctor :
    SimplicialSheafSystem X A ⥤ Sheaf (SimplicialOpen.grothendieckTopology X) A where
  obj S := ⟨systemPresheaf S, systemPresheaf_isSheaf S⟩
  map f := ObjectProperty.homMk ((systemPresheafFunctor (X := X) (A := A)).map f)
  map_id S := by
    apply Sheaf.hom_ext
    rfl
  map_comp f g := by
    apply Sheaf.hom_ext
    rfl

/-- Naturality square whose components are identities. -/
private lemma comp_id_eq_id_comp {C : Type*} [Category C] {a b : C} (f : a ⟶ b) :
    f ≫ 𝟙 b = 𝟙 a ≫ f :=
  (Category.comp_id _).trans (Category.id_comp _).symm

/-- The transition maps of the reconstructed presheaf are the original ones, as a naturality
square with identity components. -/
private lemma systemPresheaf_transitionMap_naturality (S : SimplicialSheafSystem X A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (V : (Opens (X.obj m))ᵒᵖ) :
    (SimplicialSheafSystem.transitionMap (systemPresheaf S) φ).app V ≫ 𝟙 _ =
      𝟙 _ ≫ (S.transition φ).app V := by
  rw [systemPresheaf_transitionMap_app]
  exact comp_id_eq_id_comp _

private noncomputable def reconstructedComponentPresheafIso
    (S : SimplicialSheafSystem X A) (n : SimplexCategoryᵒᵖ) :
    componentPresheaf (systemPresheaf S) n ≅
      (TopCat.Sheaf.forget A (X.obj n)).obj (S.component n) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V f
    have h := systemPresheaf_map_level S n (leOfHom f.unop)
    have hf : homOfLE (leOfHom f.unop) = f.unop := Subsingleton.elim _ _
    change (systemPresheaf S).map ((levelFunctor X n).map f.unop).op ≫
        𝟙 _ = 𝟙 _ ≫ ((TopCat.Sheaf.forget A (X.obj n)).obj (S.component n)).map f
    simp only [Category.comp_id, Category.id_comp]
    simpa only [hf, Quiver.Hom.op_unop] using h)

private noncomputable def reconstructedComponentPresheafIsoFunctor
    (n : SimplexCategoryᵒᵖ) :
    systemPresheafFunctor (X := X) (A := A) ⋙ componentPresheafFunctor X A n ≅
      SimplicialSheafSystem.componentFunctor X A n ⋙
        TopCat.Sheaf.forget A (X.obj n) := by
  refine NatIso.ofComponents (fun S => reconstructedComponentPresheafIso S n) ?_
  intro S T f
  ext V
  exact comp_id_eq_id_comp _

private noncomputable def extractionReconstructionPresheafIso
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) A) :
    (sheafToPresheaf (SimplicialOpen.grothendieckTopology X) A).obj
        ((systemToSheafFunctor (X := X) (A := A)).obj
          ((sheafToSimplicialSheafSystem (X := X) (A := A)).obj F)) ≅
    (sheafToPresheaf (SimplicialOpen.grothendieckTopology X) A).obj F := by
  exact NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V f
    change _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id]
    exact (systemRestriction_extracted F f.unop).trans (Category.id_comp _).symm)

private noncomputable def extractedReconstructedSheafIso :
    sheafToSimplicialSheafSystem (X := X) (A := A) ⋙
        systemToSheafFunctor (X := X) (A := A) ≅
      𝟭 (Sheaf (SimplicialOpen.grothendieckTopology X) A) := by
  refine NatIso.ofComponents (fun F =>
    ObjectProperty.isoMk _ (extractionReconstructionPresheafIso F)) ?_
  intro F G f
  apply Sheaf.hom_ext
  ext U
  exact comp_id_eq_id_comp _

private noncomputable def reconstructedComponentSheafIso
    (S : SimplicialSheafSystem X A) (n : SimplexCategoryᵒᵖ) :
    ((sheafToSimplicialSheafSystem (X := X) (A := A)).obj
      ((systemToSheafFunctor (X := X) (A := A)).obj S)).component n ≅ S.component n := by
  exact ObjectProperty.isoMk _ (reconstructedComponentPresheafIso S n)

private noncomputable def reconstructedSystemHom (S : SimplicialSheafSystem X A) :
    (sheafToSimplicialSheafSystem (X := X) (A := A)).obj
      ((systemToSheafFunctor (X := X) (A := A)).obj S) ⟶ S := by
  refine
    { componentHom := fun n => (reconstructedComponentSheafIso S n).hom
      naturality := ?_ }
  intro n m φ V
  exact systemPresheaf_transitionMap_naturality S φ V

private noncomputable def reconstructedSystemInv (S : SimplicialSheafSystem X A) :
    S ⟶ (sheafToSimplicialSheafSystem (X := X) (A := A)).obj
      ((systemToSheafFunctor (X := X) (A := A)).obj S) := by
  refine
    { componentHom := fun n => (reconstructedComponentSheafIso S n).inv
      naturality := ?_ }
  intro n m φ V
  rw [← systemPresheaf_transitionMap_app S φ V]
  exact comp_id_eq_id_comp _

private noncomputable def reconstructedSystemIso (S : SimplicialSheafSystem X A) :
    (sheafToSimplicialSheafSystem (X := X) (A := A)).obj
      ((systemToSheafFunctor (X := X) (A := A)).obj S) ≅ S where
  hom := reconstructedSystemHom S
  inv := reconstructedSystemInv S
  hom_inv_id :=
    SimplicialSheafSystem.Hom.ext _ _ fun n => (reconstructedComponentSheafIso S n).hom_inv_id
  inv_hom_id :=
    SimplicialSheafSystem.Hom.ext _ _ fun n => (reconstructedComponentSheafIso S n).inv_hom_id

private noncomputable def reconstructedExtractedSystemIso :
    systemToSheafFunctor (X := X) (A := A) ⋙
      sheafToSimplicialSheafSystem ≅ 𝟭 (SimplicialSheafSystem X A) := by
  refine NatIso.ofComponents reconstructedSystemIso ?_
  intro S T f
  apply SimplicialSheafSystem.Hom.ext
  intro n
  apply Sheaf.hom_ext
  ext V
  exact comp_id_eq_id_comp _

private noncomputable def extractedReconstructedPresheafIso :
    sheafToSimplicialSheafSystem (X := X) (A := A) ⋙ systemPresheafFunctor ≅
      sheafToPresheaf (SimplicialOpen.grothendieckTopology X) A := by
  refine NatIso.ofComponents extractionReconstructionPresheafIso ?_
  intro F G f
  ext U
  exact comp_id_eq_id_comp _

/-- An equivalence between sheaves on the simplicial site and simplicial sheaf systems, together
with the natural identification asserting that its forward functor does not change the underlying
presheaf. In particular, this identification determines all component sheaves and transition
maps of the image. -/
structure SheafSystemEquivalence (X : SimplicialObject TopCat.{u})
    (A : Type w) [Category.{v} A] where
  /-- The equivalence of categories. -/
  toEquivalence :
    Sheaf (SimplicialOpen.grothendieckTopology X) A ≌ SimplicialSheafSystem X A
  /-- Reconstruct the total presheaf, including all cross-degree restriction maps, from an
  explicit system. -/
  toPresheaf : SimplicialSheafSystem X A ⥤ (SimplicialOpen X)ᵒᵖ ⥤ A
  /-- The forward functor, followed by reconstruction of its total presheaf, is naturally
  isomorphic to the usual forgetful functor from sheaves to presheaves. -/
  underlyingPresheafIso :
    toEquivalence.functor ⋙ toPresheaf ≅
      sheafToPresheaf (SimplicialOpen.grothendieckTopology X) A
  /-- Reconstruction recovers the component sheaves naturally in system morphisms. -/
  componentIso : ∀ n : SimplexCategoryᵒᵖ,
    toPresheaf ⋙ componentPresheafFunctor X A n ≅
      SimplicialSheafSystem.componentFunctor X A n ⋙ TopCat.Sheaf.forget A (X.obj n)
  /-- The reconstructed restriction maps are precisely the transition maps of the system. -/
  transition_compatibility : ∀ (S : SimplicialSheafSystem X A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (V : (Opens (X.obj m))ᵒᵖ),
    (SimplicialSheafSystem.transitionMap (toPresheaf.obj S) φ).app V ≫
        ((componentIso n).app S).hom.app (op ((Opens.map (X.map φ)).obj V.unop)) =
      ((componentIso m).app S).hom.app V ≫ (S.transition φ).app V

/-- The equivalence between sheaves on the simplicial site and systems of degreewise sheaves,
with forward functor `sheafToSimplicialSheafSystem`, together with the reconstruction of the
total presheaf of a system and its identifications. -/
@[no_expose]
noncomputable def sheafEquivalenceSimplicialSheafSystem
    (X : SimplicialObject TopCat.{u}) (A : Type w) [Category.{v} A] :
    SheafSystemEquivalence X A where
  toEquivalence := CategoryTheory.Equivalence.mk
    sheafToSimplicialSheafSystem systemToSheafFunctor
    extractedReconstructedSheafIso.symm reconstructedExtractedSystemIso
  toPresheaf := systemPresheafFunctor
  underlyingPresheafIso := extractedReconstructedPresheafIso
  componentIso := reconstructedComponentPresheafIsoFunctor
  transition_compatibility := by
    intro S n m φ V
    change (SimplicialSheafSystem.transitionMap (systemPresheaf S) φ).app V ≫ 𝟙 _ =
      𝟙 _ ≫ (S.transition φ).app V
    rw [systemPresheaf_transitionMap_app]
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- **Stacks 09VM.** Let `X` be a simplicial topological space. The functor
`sheafToSimplicialSheafSystem` from sheaves on the site `X_Zar` of `X`
(`SimplicialOpen.grothendieckTopology X`: opens of the spaces `X n`, morphisms over simplex
maps, coverings by open coverings inside one degree) to the category `SimplicialSheafSystem X A`
of systems `(F_n, F(φ))` of sheaves `F_n` on `X n` with `X.map φ`-maps `F(φ)` satisfying
`F(φ) ∘ F(ψ) = F(φ ∘ ψ)` and `F(id) = id`, which sends `F` to its restrictions to the degrees
and its restriction maps over simplex maps, is an equivalence of categories. The values are in
an arbitrary category `A`; sheaves of sets are the case `A = Type _`. -/
@[stacks 09VM]
instance isEquivalence_sheafToSimplicialSheafSystem
    (X : SimplicialObject TopCat.{u}) (A : Type w) [Category.{v} A] :
    (sheafToSimplicialSheafSystem (X := X) (A := A)).IsEquivalence :=
  (CategoryTheory.Equivalence.mk sheafToSimplicialSheafSystem systemToSheafFunctor
    extractedReconstructedSheafIso.symm reconstructedExtractedSystemIso).isEquivalence_functor

end Stacks.Topology.Simplicial

end
