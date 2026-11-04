module

public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.Topology.Category.TopCat.Limits.Products
public import StacksFrontier.Topology.Simplicial.DiagramSiteIsoCovering
public import StacksFrontier.Topology.Simplicial.SliceSite
public import StacksFrontier.Topology.Simplicial.Sheaves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Simplicial topological spaces

A *simplicial space* is a simplicial object `X : SimplicialObject TopCat` in the category of
topological spaces and continuous maps. It has spaces `X_n` and continuous face maps
`d^n_i : X_n → X_{n-1}` (`CategoryTheory.SimplicialObject.δ`) and degeneracy maps
`s^n_j : X_n → X_{n+1}` (`CategoryTheory.SimplicialObject.σ`); for instance there are two face
maps `d^1_0, d^1_1 : X_1 → X_0`, indexed by `Fin 2`, and a single degeneracy `s^0_0 : X_0 → X_1`.
The face map `d^n_i` is to be thought of as the projection forgetting the `i`-th coordinate and
`s^n_j` as the diagonal repeating the `j`-th coordinate. This is literally true for the simplicial
object `X_n = Y^{n+1}` of an object `Y` of a category with finite products
(`CategoryTheory.cechNerveTerminalFrom`), and in general it is reflected in the simplicial
identities `d_j ∘ s_j = d_{j+1} ∘ s_j = id`.

A simplicial space `X` has a site `X_Zar` (`Stacks.Topology.Simplicial.SimplicialOpen`):
1. an object is an open `U` of some `X_n`;
2. a morphism `U → V`, for `U ⊆ X_n` and `V ⊆ X_m`, is a `φ : [m] → [n]` with `X(φ)(U) ⊆ V`;
3. a covering `{U_i → U}` consists of opens `U, U_i ⊆ X_n` with maps given by `id : [n] → [n]`
   and `U = ⋃ U_i`.
A morphism `U → V` given by `φ` induces a continuous map `U → V` of topological spaces. The
construction is a special case of the one attaching a site to an arbitrary diagram of
topological spaces (`Stacks.Topology.Simplicial.DiagramOpen`).

For a sheaf `F` on `X_Zar`, the restriction of `F` to the opens of `X_n` is a sheaf `F_n` on the
space `X_n`, and for `φ : [m] → [n]` the restriction maps of `F` along the morphisms given by `φ`
form an `X(φ)`-map `F(φ) : F_m → F_n`, with `F(φ) ∘ F(ψ) = F(φ ∘ ψ)` and `F(id) = id`. Conversely
a system `(F_n, F(φ))` with these properties is a sheaf on `X_Zar`; this is the equivalence
`Stacks.Topology.Simplicial.sheafEquivalenceSimplicialSheafSystem`.

For a topological space `X`, the site `X_Zar` of open subsets with inclusions and open coverings
is `TopologicalSpace.Opens.pretopology`, and its category of sheaves is identified with the
category `TopCat.Sheaf` of sheaves on `X`.

## Main definitions

* `Stacks.Topology.Simplicial.SimplicialOpen.toTopCat`: an object of `X_Zar` as a topological
  space, and a morphism as the continuous map it induces.
* `Stacks.Topology.Simplicial.sheafSystem`: the system `(F_n, F(φ))` of a sheaf `F` on `X_Zar`.
* `Stacks.Topology.Simplicial.systemSheaf`: the sheaf on `X_Zar` of a system `(F_n, F(φ))`.

## Main results

* `Stacks.Topology.Simplicial.cechNerveTerminalFrom_δ_π` and `cechNerveTerminalFrom_σ_π`: on
  `X_n = Y^{n+1}` the face maps forget a coordinate and the degeneracies repeat one.
* `Stacks.Topology.Simplicial.SimplicialOpen.toTopCat_map_comp_inclusion`: the continuous map
  induced by a morphism `U → V` given by `φ` is the restriction of `X(φ)`.
* `Stacks.Topology.Simplicial.componentPresheaf_isSheaf`: the restriction `F_n` of a sheaf on
  `X_Zar` to the opens of `X_n` is a sheaf on `X_n`.
* `Stacks.Topology.Simplicial.SimplicialSheafSystem.transitionMap_id_app` and
  `transitionMap_comp`: the maps `F(φ)` preserve identities and compositions.
* `Stacks.Topology.Simplicial.sheafSystemIso`: `sheafSystem` is the forward functor of the
  equivalence of Lemma 09VM.
* `Stacks.Topology.Simplicial.systemSheafCompSheafSystemIso`: the system of the sheaf of a system
  is that system.

## Implementation notes

The identity `F(φ) ∘ F(ψ) = F(φ ∘ ψ)` compares an `(X(ψ) ∘ X(φ))`-map with an `X(φ ∘ ψ)`-map.
The two continuous maps are equal but not definitionally so, and the identity is stated as a
heterogeneous equality, as in the fields of `Stacks.Topology.Simplicial.SimplicialSheafSystem`.

## References

* [Stacks Project, Tag 09VK](https://stacks.math.columbia.edu/tag/09VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w v₁ u₁

/-! ### Simplicial spaces and their face and degeneracy maps -/

add_to_stacks 09VK "a simplicial space: a simplicial object of the category of topological spaces
  and continuous maps, `SimplicialObject TopCat`" CategoryTheory.SimplicialObject
add_to_sga "4 V 7.1.0" CategoryTheory.SimplicialObject
add_to_sga "4 Vbis 1.2.6" CategoryTheory.SimplicialObject
add_to_sga "4 Vbis 3.0.1" CategoryTheory.SimplicialObject
add_to_sga "4 Vbis 5.1.0" CategoryTheory.SimplicialObject
add_to_stacks 09VK "the face maps `d^n_i : X_n → X_{n-1}`; for `n = 1` the two maps `d^1_0, d^1_1`"
  CategoryTheory.SimplicialObject.δ
add_to_sga "4 V 1.10" CategoryTheory.SimplicialObject.δ
add_to_sga "4 Vbis 5.1.0" CategoryTheory.SimplicialObject.δ
add_to_stacks 09VK "the degeneracy maps `s^n_j : X_n → X_{n+1}`; for `n = 0` the single `s^0_0`"
  CategoryTheory.SimplicialObject.σ
add_to_sga "4 Vbis 5.1.0" CategoryTheory.SimplicialObject.σ
add_to_stacks 09VK "`d_j ∘ s_j = id`: the diagonal repeating the `j`-th coordinate followed by
  forgetting it" CategoryTheory.SimplicialObject.δ_comp_σ_self
add_to_stacks 09VK "`d_{j+1} ∘ s_j = id`: the diagonal repeating the `j`-th coordinate followed by
  forgetting the repeated copy" CategoryTheory.SimplicialObject.δ_comp_σ_succ
add_to_stacks 09VK "the model `X_n = Y^{n+1}` of the picture of a simplicial space"
  CategoryTheory.cechNerveTerminalFrom
add_to_sga "3 X 6.3" CategoryTheory.cechNerveTerminalFrom
add_to_sga "3 X 9.7.1" CategoryTheory.cechNerveTerminalFrom
add_to_sga "4 V 1.10" "special case" CategoryTheory.cechNerveTerminalFrom
add_to_sga "4 Vbis 1.2.7" "special case" CategoryTheory.cechNerveTerminalFrom

namespace Stacks.Topology.Simplicial

section Coordinates

variable {C : Type u₁} [Category.{v₁} C] [HasFiniteProducts C] (Y : C)

/-- **The face map `d^{n+1}_i` forgets the `i`-th coordinate.** On the simplicial object
`X_n = Y^{n+1}`, the `k`-th coordinate of `d_i` is the `(i.succAbove k)`-th coordinate, i.e. the
coordinates of `d_i(y_0, …, y_{n+1})` are those of `(y_0, …, y_{n+1})` with `y_i` left out. -/
@[stacks 09VK "the face map `d^n_i` is the projection forgetting the `i`-th coordinate"]
theorem cechNerveTerminalFrom_δ_π {n : ℕ} (i : Fin (n + 2)) (k : Fin (n + 1)) :
    (cechNerveTerminalFrom Y).δ i ≫ Pi.π (fun _ : Fin (n + 1) => Y) k =
      Pi.π (fun _ : Fin (n + 2) => Y) (i.succAbove k) := by
  simp [SimplicialObject.δ, cechNerveTerminalFrom, SimplexCategory.δ]

/-- **The degeneracy map `s^n_j` repeats the `j`-th coordinate.** On the simplicial object
`X_n = Y^{n+1}`, the `k`-th coordinate of `s_j` is the `(j.predAbove k)`-th coordinate, i.e.
`s_j(y_0, …, y_n) = (y_0, …, y_j, y_j, …, y_n)`. -/
@[stacks 09VK "the degeneracy map `s^n_j` is the diagonal repeating the `j`-th coordinate"]
theorem cechNerveTerminalFrom_σ_π {n : ℕ} (j : Fin (n + 1)) (k : Fin (n + 2)) :
    (cechNerveTerminalFrom Y).σ j ≫ Pi.π (fun _ : Fin (n + 2) => Y) k =
      Pi.π (fun _ : Fin (n + 1) => Y) (j.predAbove k) := by
  simp [SimplicialObject.σ, cechNerveTerminalFrom, SimplexCategory.σ]

end Coordinates

/-! ### The site of a simplicial space -/

add_to_stacks 09VK "(1) an object of `X_Zar` is an open `U` of `X_n` for some `n`" SimplicialOpen
add_to_stacks 09VK "(2) a morphism `U → V` of `X_Zar` is a `φ : [m] → [n]` with `X(φ)(U) ⊆ V`"
  SimplicialOpen.Hom
add_to_stacks 09VK "(3) a covering `{U_i → U}`: opens of one `X_n`, maps given by `id : [n] → [n]`,
  and `U = ⋃ U_i`" SimplicialOpen.IsCovering
add_to_stacks 09VK "the coverings of `X_Zar`" SimplicialOpen.precoverage
add_to_stacks 09VK "the topology of `X_Zar`" SimplicialOpen.grothendieckTopology

namespace SimplicialOpen

variable (X : SimplicialObject TopCat.{u})

/-- **A morphism of `X_Zar` induces a continuous map.** An object `U ⊆ X_n` of the site of a
simplicial space is a topological space, and a morphism `U → V` given by `φ` induces the
continuous map `U → V` restricting `X(φ) : X_n → X_m`. -/
@[stacks 09VK "a morphism `U → V` of `X_Zar` given by `φ` induces a continuous map `U → V`"]
def toTopCat : SimplicialOpen X ⥤ TopCat.{u} where
  obj U := TopCat.of U.toOpens
  map {U V} f := TopCat.ofHom
    ⟨fun x => ⟨X.map f.base x.1, SimplicialOpen.Hom.le f x.2⟩,
      ((X.map f.base).hom.continuous.comp continuous_subtype_val).subtype_mk _⟩
  map_id U := by
    ext x
    exact ConcreteCategory.congr_hom (X.map_id _) x.1
  map_comp f g := by
    ext x
    exact ConcreteCategory.congr_hom (X.map_comp f.base g.base) x.1

/-- The space attached to an open `U` of `X_n` is `U` with the subspace topology. -/
@[simp]
theorem toTopCat_obj (U : SimplicialOpen X) : (toTopCat X).obj U = TopCat.of U.toOpens := rfl

/-- The continuous map `U → V` induced by a morphism given by `φ` is the restriction of
`X(φ) : X_n → X_m`. -/
@[stacks 09VK "the induced continuous map `U → V` is the restriction of `X(φ)`"]
theorem toTopCat_map_comp_inclusion {U V : SimplicialOpen X} (f : U ⟶ V) :
    (toTopCat X).map f ≫ V.toOpens.inclusion' = U.toOpens.inclusion' ≫ X.map f.base :=
  rfl

end SimplicialOpen

/-! ### The site as a special case of the site of a diagram of spaces -/

add_to_stacks 09VK "the site attached to an arbitrary diagram of topological spaces: its objects"
  DiagramOpen
add_to_stacks 09VK "the site attached to an arbitrary diagram of topological spaces: its
  coverings" DiagramOpen.isoPrecoverage
add_to_stacks 09VK "the site attached to an arbitrary diagram of topological spaces: the
  identity-covering axiom" DiagramOpen.isoPrecoverage_hasIsos
add_to_stacks 09VK "the site attached to an arbitrary diagram of topological spaces: existence of
  pullbacks of coverings" DiagramOpen.isoPrecoverage_hasPullbacks
add_to_stacks 09VK "the site attached to an arbitrary diagram of topological spaces: the base-change
  axiom" DiagramOpen.isoPrecoverage_isStableUnderBaseChange
add_to_stacks 09VK "the site attached to an arbitrary diagram of topological spaces: the
  composition axiom" DiagramOpen.isoPrecoverage_isStableUnderComposition
add_to_stacks 09VK "for a simplicial space its coverings are the levelwise open coverings"
  DiagramOpen.isoPrecoverage_eq_precoverage
add_to_stacks 09VK "`X_Zar` is the site of the diagram `X` of spaces: the identification of
  categories" simplicialOpenEquiv
add_to_stacks 09VK "`X_Zar` is the site of the diagram `X` of spaces: the identification is one of
  sites" toDiagramOpen_isDenseSubsite

/-! ### Sheaves on the site of a simplicial space -/

/-- **The restriction `F_n` of a sheaf on `X_Zar` to the opens of `X_n` is a sheaf on `X_n`.**
This holds for sheaves with values in any category. -/
@[stacks 09VK "the restriction `F_n` of a sheaf `F` on `X_Zar` to the opens of `X_n` is a sheaf"]
theorem componentPresheaf_isSheaf {X : SimplicialObject TopCat.{u}} {A : Type w} [Category.{v} A]
    (F : Sheaf (SimplicialOpen.grothendieckTopology X) A) (n : SimplexCategoryᵒᵖ) :
    TopCat.Presheaf.IsSheaf (componentPresheaf F.obj n) :=
  have := levelFunctor_isContinuous X n
  (levelFunctor X n).op_comp_isSheaf _ _ F

add_to_stacks 09VK "the restriction `F_n` of a presheaf on `X_Zar` to the opens of `X_n`"
  componentPresheaf
add_to_stacks 09VK "the restriction maps of `F` for `X(φ)(U) ⊆ V` define an `X(φ)`-map
  `F(φ) : F_m → F_n`" SimplicialSheafSystem.transitionMap

namespace SimplicialSheafSystem

variable {X : SimplicialObject TopCat.{u}} {A : Type w} [Category.{v} A]

add_to_stacks 09VK "`F(id_{[n]}) = id_{F_n}`" transitionMap_id_app

/-- **`F(φ) ∘ F(ψ) = F(φ ∘ ψ)`.** The composite (Stacks 008L) of the `f`-maps `F(φ)` and `F(ψ)`
is the `f`-map of the composite. It is an `(X(φ) ≫ X(ψ))`-map while `F(φ ≫ ψ)` is an
`X(φ ≫ ψ)`-map, so the equality is heterogeneous. -/
@[stacks 09VK "`F(φ) ∘ F(ψ) = F(φ ∘ ψ)`, composition of `f`-maps as in Sheaves 008L"]
theorem transitionMap_comp (P : (SimplicialOpen X)ᵒᵖ ⥤ A) {l m n : SimplexCategoryᵒᵖ}
    (φ : l ⟶ m) (ψ : m ⟶ n) :
    HEq ((transitionMap P φ).compPresheaf (transitionMap P ψ)) (transitionMap P (φ ≫ ψ)) := by
  have ext : ∀ (s t : StacksFMap (X.map (φ ≫ ψ)) (componentPresheaf P l)
      (componentPresheaf P n)), (∀ V, s.app V = t.app V) → s = t := by
    rintro ⟨app, _⟩ ⟨app', _⟩ h
    obtain rfl : app = app' := funext h
    rfl
  have key : ∀ (f : X.obj l ⟶ X.obj n) (_ : f = X.map (φ ≫ ψ))
      (s : StacksFMap f (componentPresheaf P l) (componentPresheaf P n)),
      (∀ V, HEq (s.app V) ((transitionMap P (φ ≫ ψ)).app V)) →
        HEq s (transitionMap P (φ ≫ ψ)) := by
    rintro f rfl s hs
    exact heq_of_eq (ext _ _ fun V => eq_of_heq (hs V))
  exact key _ (X.map_comp φ ψ).symm _ (transitionMap_comp_app P φ ψ)

end SimplicialSheafSystem

add_to_stacks 09VK "a system `({F_n}, {F(φ)})`: sheaves on the `X_n` with `X(φ)`-maps satisfying
  `F(φ) ∘ F(ψ) = F(φ ∘ ψ)` and `F(id) = id`" SimplicialSheafSystem

section SheafSystem

variable (X : SimplicialObject TopCat.{u}) (A : Type w) [Category.{v} A]

/-- **The system `(F_n, F(φ))` of a sheaf on `X_Zar`.** A sheaf `F` on the site of a simplicial
space gives the sheaves `F_n` on the spaces `X_n`, obtained by restricting `F` to the opens of
`X_n`, together with the `X(φ)`-maps `F(φ) : F_m → F_n` formed by the restriction maps of `F`,
which satisfy `F(φ) ∘ F(ψ) = F(φ ∘ ψ)` and `F(id) = id`. -/
@[stacks 09VK "a sheaf `F` on `X_Zar` gives the system `(F_n, F(φ))`"]
def sheafSystem :
    Sheaf (SimplicialOpen.grothendieckTopology X) A ⥤ SimplicialSheafSystem X A where
  obj F :=
    { component n := ⟨componentPresheaf F.obj n, componentPresheaf_isSheaf F n⟩
      transition φ := SimplicialSheafSystem.transitionMap F.obj φ
      transition_id n V := SimplicialSheafSystem.transitionMap_id_app F.obj n V
      transition_comp φ ψ V := SimplicialSheafSystem.transitionMap_comp_app F.obj φ ψ V }
  map f :=
    { componentHom n := ObjectProperty.homMk (Functor.whiskerLeft (levelFunctor X n).op f.hom)
      naturality _ _ := f.hom.naturality _ }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The `n`-th component of the system of a sheaf `F` is the restriction `F_n` of `F` to the
opens of `X_n`. -/
@[simp]
theorem sheafSystem_obj_component_obj (F : Sheaf (SimplicialOpen.grothendieckTopology X) A)
    (n : SimplexCategoryᵒᵖ) :
    (((sheafSystem X A).obj F).component n).obj = componentPresheaf F.obj n :=
  rfl

/-- The transition map `F(φ)` of the system of a sheaf `F` is the `X(φ)`-map formed by the
restriction maps of `F`. -/
@[simp]
theorem sheafSystem_obj_transition (F : Sheaf (SimplicialOpen.grothendieckTopology X) A)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    ((sheafSystem X A).obj F).transition φ = SimplicialSheafSystem.transitionMap F.obj φ :=
  rfl

/-- An isomorphism of systems from isomorphisms of the components compatible with the
transition maps. -/
def SimplicialSheafSystem.isoMk {S T : SimplicialSheafSystem X A}
    (e : ∀ n, S.component n ≅ T.component n)
    (h : ∀ {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) (V : (Opens (X.obj m))ᵒᵖ),
      (S.transition φ).app V ≫ ((TopCat.Sheaf.forget A (X.obj n)).map (e n).hom).app
          (op ((Opens.map (X.map φ)).obj V.unop)) =
        ((TopCat.Sheaf.forget A (X.obj m)).map (e m).hom).app V ≫ (T.transition φ).app V) :
    S ≅ T where
  hom := { componentHom n := (e n).hom, naturality φ V := h φ V }
  inv :=
    { componentHom n := (e n).inv
      naturality {n m} φ V := by
        let i := fun k => (TopCat.Sheaf.forget A (X.obj k)).mapIso (e k)
        have h' : (S.transition φ).app V ≫ (i n).hom.app (op ((Opens.map (X.map φ)).obj V.unop)) =
            (i m).hom.app V ≫ (T.transition φ).app V := h φ V
        change (T.transition φ).app V ≫ (i n).inv.app _ = (i m).inv.app V ≫ (S.transition φ).app V
        rw [← cancel_epi ((i m).hom.app V), Iso.hom_inv_id_app_assoc, ← Category.assoc, ← h',
          Category.assoc, Iso.hom_inv_id_app, Category.comp_id] }
  hom_inv_id := SimplicialSheafSystem.Hom.ext _ _ fun n => (e n).hom_inv_id
  inv_hom_id := SimplicialSheafSystem.Hom.ext _ _ fun n => (e n).inv_hom_id

/-- The components of the system of `F` are the components of the image of `F` under the
equivalence of Lemma 09VM. -/
def sheafSystemComponentIso (F : Sheaf (SimplicialOpen.grothendieckTopology X) A)
    (n : SimplexCategoryᵒᵖ) :
    ((sheafSystem X A).obj F).component n ≅
      ((sheafEquivalenceSimplicialSheafSystem X A).toEquivalence.functor.obj F).component n :=
  ObjectProperty.isoMk _
    (Functor.isoWhiskerLeft (levelFunctor X n).op
        ((sheafEquivalenceSimplicialSheafSystem X A).underlyingPresheafIso.app F).symm ≪≫
      ((sheafEquivalenceSimplicialSheafSystem X A).componentIso n).app
        ((sheafEquivalenceSimplicialSheafSystem X A).toEquivalence.functor.obj F))

/-- The system of a sheaf is isomorphic to its image under the equivalence of Lemma 09VM. -/
def sheafSystemObjIso (F : Sheaf (SimplicialOpen.grothendieckTopology X) A) :
    (sheafSystem X A).obj F ≅
      (sheafEquivalenceSimplicialSheafSystem X A).toEquivalence.functor.obj F := by
  refine SimplicialSheafSystem.isoMk X A (sheafSystemComponentIso X A F) ?_
  intro n m φ V
  let E := sheafEquivalenceSimplicialSheafSystem X A
  let S := E.toEquivalence.functor.obj F
  let P := E.toPresheaf.obj S
  let α : F.obj ⟶ P := (E.underlyingPresheafIso.app F).inv
  let g := (SimplicialSheafSystem.transitionHom φ V.unop).op
  let cn : P.obj (op ⟨n, (Opens.map (X.map φ)).obj V.unop⟩) ⟶
      (S.component n).obj.obj (op ((Opens.map (X.map φ)).obj V.unop)) :=
    ((E.componentIso n).app S).hom.app _
  let cm : P.obj (op ⟨m, V.unop⟩) ⟶ (S.component m).obj.obj V :=
    ((E.componentIso m).app S).hom.app V
  have hα : F.obj.map g ≫ α.app _ = α.app _ ≫ P.map g := α.naturality g
  have hc : P.map g ≫ cn = cm ≫ (S.transition φ).app V := E.transition_compatibility S φ V
  change F.obj.map g ≫ (α.app _ ≫ cn) = (α.app _ ≫ cm) ≫ (S.transition φ).app V
  rw [← Category.assoc, hα, Category.assoc, hc]
  exact (Category.assoc _ _ _).symm

/-- **The system of a sheaf is the description of Lemma 09VM.** The functor `sheafSystem`, which
sends `F` to `(F_n, F(φ))`, is isomorphic to the forward functor of
`Stacks.Topology.Simplicial.sheafEquivalenceSimplicialSheafSystem`. -/
def sheafSystemIso :
    sheafSystem X A ≅ (sheafEquivalenceSimplicialSheafSystem X A).toEquivalence.functor := by
  refine NatIso.ofComponents (sheafSystemObjIso X A) ?_
  intro F G f
  let E := sheafEquivalenceSimplicialSheafSystem X A
  apply SimplicialSheafSystem.Hom.ext
  intro n
  apply Sheaf.hom_ext
  ext V
  let SF := E.toEquivalence.functor.obj F
  let SG := E.toEquivalence.functor.obj G
  let h : SF ⟶ SG := E.toEquivalence.functor.map f
  let αF : F.obj ⟶ E.toPresheaf.obj SF := (E.underlyingPresheafIso.app F).inv
  let αG : G.obj ⟶ E.toPresheaf.obj SG := (E.underlyingPresheafIso.app G).inv
  let cF : (E.toPresheaf.obj SF).obj (op ⟨n, V.unop⟩) ⟶ (SF.component n).obj.obj V :=
    ((E.componentIso n).app SF).hom.app V
  let cG : (E.toPresheaf.obj SG).obj (op ⟨n, V.unop⟩) ⟶ (SG.component n).obj.obj V :=
    ((E.componentIso n).app SG).hom.app V
  have h₁ : f.hom.app (op ⟨n, V.unop⟩) ≫ αG.app _ = αF.app _ ≫ (E.toPresheaf.map h).app _ :=
    congrArg (fun k => k.app (op (⟨n, V.unop⟩ : SimplicialOpen X)))
      (E.underlyingPresheafIso.inv.naturality f)
  have h₂ : (E.toPresheaf.map h).app (op ⟨n, V.unop⟩) ≫ cG =
      cF ≫ (h.componentHom n).hom.app V :=
    congrArg (fun k => k.app V) ((E.componentIso n).hom.naturality h)
  have e₁ : (((sheafSystem X A).map f ≫ (sheafSystemObjIso X A G).hom).componentHom n).hom.app V =
      f.hom.app _ ≫ (αG.app _ ≫ cG) := rfl
  have e₂ : (((sheafSystemObjIso X A F).hom ≫ h).componentHom n).hom.app V =
      (αF.app _ ≫ cF) ≫ (h.componentHom n).hom.app V := rfl
  rw [e₁, e₂, ← Category.assoc, h₁, Category.assoc, h₂, Category.assoc]

/-- **The sheaf on `X_Zar` of a system.** A system `(F_n, F(φ))` satisfying
`F(φ) ∘ F(ψ) = F(φ ∘ ψ)` and `F(id) = id` defines a sheaf on `X_Zar`: this is the inverse functor
of the equivalence of Lemma 09VM. -/
def systemSheaf : SimplicialSheafSystem X A ⥤ Sheaf (SimplicialOpen.grothendieckTopology X) A :=
  (sheafEquivalenceSimplicialSheafSystem X A).toEquivalence.inverse

/-- **A system is the system of its sheaf.** The sheaf on `X_Zar` defined by a system
`(F_n, F(φ))` has, as its restrictions to the opens of the `X_n` and as its restriction maps along
the morphisms given by the `φ`, the system `(F_n, F(φ))` again, naturally in the system. -/
@[stacks 09VK "conversely, a system `(F_n, F(φ))` with `F(φ) ∘ F(ψ) = F(φ ∘ ψ)` and
  `F(id) = id` gives a sheaf on `X_Zar` whose system it is"]
def systemSheafCompSheafSystemIso : systemSheaf X A ⋙ sheafSystem X A ≅ 𝟭 _ :=
  Functor.isoWhiskerLeft _ (sheafSystemIso X A) ≪≫
    (sheafEquivalenceSimplicialSheafSystem X A).toEquivalence.counitIso

end SheafSystem

/-! ### The site of a topological space -/

add_to_stacks 09VK "for a topological space `X`, the site `X_Zar` of opens of `X` with inclusions
  and open coverings (Sites, Example 00VJ)" _root_.Opens.pretopology
add_to_sga "4 III 1.9.1" Opens.pretopology
add_to_sga "4½ Arcata 1.6.4" "partial" Opens.pretopology
add_to_stacks 09VK "the topos `Sh(X_Zar)` is identified with the category of sheaves on `X`: the
  topology generated by the open coverings is the topology of sheaves on `X`"
  _root_.Opens.pretopology_toGrothendieck
add_to_stacks 09VK "the category of sheaves on a topological space `X`, that is, `Sh(X_Zar)`"
  TopCat.Sheaf

end Stacks.Topology.Simplicial

end
