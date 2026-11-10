module

public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Copower
public import StacksFrontier.AlgebraicTopology.SimplicialObject.Homotopy.Basic

/-!
# Multiplying a simplicial set by a simplicial object preserves homotopies

Let `V` be a simplicial object of a category `C` and let `U`, `U'` be simplicial sets. The
product `U × V = V.copower U` of [Stacks, Tag 017C] is functorial in `U`, and this file shows
that the functor `U ↦ U × V` carries a simplicial homotopy between two morphisms `U ⟶ U'` to a
simplicial homotopy between the induced morphisms, hence a homotopy equivalence of simplicial
sets to a homotopy equivalence of simplicial objects of `C`.

The homotopy transported to the product uses the degeneracies of `V`: the `i`-th component of
the transported homotopy carries the summand of `(U × V)_n` indexed by `u ∈ U_n` into the
summand of `(U' × V)_{n + 1}` indexed by `h_i(u)` by the degeneracy `σ_i` of `V`. On the `V`
factor the eight relations of a simplicial homotopy are then the relations satisfied by the
constant homotopy of the identity of `V`, and on the index factor they are the relations
satisfied by the given homotopy.

The product of a simplicial object with the constant simplicial set on a singleton is the
simplicial object itself, the comparison being the projection of [Stacks, Tag 017E] (2); so
together with the above, multiplying by a simplicial set homotopy equivalent to a singleton
changes nothing up to homotopy equivalence.

## Main definitions

* `CategoryTheory.Functor.copowerConstPUnitIso`: the copower of a functor by the constant
  functor with value a singleton is the functor itself, the comparison being the projection
  `CategoryTheory.Functor.copowerProj`.
* `CategoryTheory.SimplicialObject.Homotopy.copower`: the transported simplicial homotopy.

## Main results

* `CategoryTheory.SimplicialObject.homotopyEquivalences_copowerMap_id`: multiplying by a
  simplicial object carries a homotopy equivalence of simplicial sets to a homotopy
  equivalence of simplicial objects.
* `CategoryTheory.SimplicialObject.homotopyEquivalences_iso_comp_iso`: homotopy equivalences
  of simplicial objects are stable under composition with isomorphisms on either side, being
  homotopic a congruence ([Stacks, Tag 08RJ]).

## References

* [Stacks, Tag 017C](https://stacks.math.columbia.edu/tag/017C)
* [Stacks, Tag 017E](https://stacks.math.columbia.edu/tag/017E)
* [Stacks, Tag 019N](https://stacks.math.columbia.edu/tag/019N)
* [Stacks, Tag 08RJ](https://stacks.math.columbia.edu/tag/08RJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

universe w v u v' u'

namespace CategoryTheory.Functor

variable {J : Type u'} [Category.{v'} J] {C : Type u} [Category.{v} C] (V : J ⥤ C)
  [∀ j, HasCoproduct fun _ : ((Functor.const J).obj PUnit.{w + 1}).obj j => V.obj j]

/-- The projection from the copower of `V` by the constant functor with value a singleton to `V`
is an isomorphism. -/
instance isIso_copowerProj_const :
    IsIso (V.copowerProj ((Functor.const J).obj PUnit.{w + 1})) := by
  have happ (j : J) : IsIso ((V.copowerProj ((Functor.const J).obj PUnit.{w + 1})).app j) := by
    refine ⟨Sigma.ι (fun _ : PUnit.{w + 1} => V.obj j) PUnit.unit, ?_, ?_⟩
    · refine Sigma.hom_ext _ _ fun u => ?_
      obtain rfl : u = PUnit.unit := rfl
      simp [copowerProj]
    · exact Sigma.ι_comp_desc _ _
  exact NatIso.isIso_of_isIso_app _

/-- **The copower of `V` by the constant functor with value a singleton is `V`**, the
comparison being the projection of [Stacks, Tag 017E] (2). -/
noncomputable def copowerConstPUnitIso :
    V.copower ((Functor.const J).obj PUnit.{w + 1}) ≅ V :=
  asIso (V.copowerProj ((Functor.const J).obj PUnit.{w + 1}))

/-- The forward morphism of `copowerConstPUnitIso` is the projection `copowerProj`. -/
@[simp]
lemma copowerConstPUnitIso_hom :
    (copowerConstPUnitIso.{w} V).hom =
      V.copowerProj ((Functor.const J).obj PUnit.{w + 1}) :=
  rfl

end CategoryTheory.Functor

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C]

section

variable (V : SimplicialObject C) (U : SimplicialObject (Type w))
  [∀ j, HasCoproduct fun _ : U.obj j => V.obj j]

/-- The `i`-th face map of `U × V` carries the summand indexed by `u` into the summand indexed
by `U.δ i u` by the `i`-th face map of `V`. -/
@[reassoc]
lemma ι_copower_δ {n : ℕ} (i : Fin (n + 2)) (u : U.obj (op ⦋n + 1⦌)) :
    Sigma.ι (fun _ : U.obj (op ⦋n + 1⦌) => V.obj (op ⦋n + 1⦌)) u ≫
        SimplicialObject.δ (V.copower U) i =
      V.δ i ≫ Sigma.ι (fun _ : U.obj (op ⦋n⦌) => V.obj (op ⦋n⦌)) (U.δ i u) :=
  Sigma.ι_comp_map' _ _ u

/-- The `i`-th degeneracy of `U × V` carries the summand indexed by `u` into the summand
indexed by `U.σ i u` by the `i`-th degeneracy of `V`. -/
@[reassoc]
lemma ι_copower_σ {n : ℕ} (i : Fin (n + 1)) (u : U.obj (op ⦋n⦌)) :
    Sigma.ι (fun _ : U.obj (op ⦋n⦌) => V.obj (op ⦋n⦌)) u ≫
        SimplicialObject.σ (V.copower U) i =
      V.σ i ≫ Sigma.ι (fun _ : U.obj (op ⦋n + 1⦌) => V.obj (op ⦋n + 1⦌)) (U.σ i u) :=
  Sigma.ι_comp_map' _ _ u

end

section

variable {U U' : SimplicialObject (Type w)} (V : SimplicialObject C)
  [∀ j, HasCoproduct fun _ : U.obj j => V.obj j]
  [∀ j, HasCoproduct fun _ : U'.obj j => V.obj j]

/-- **A simplicial homotopy of morphisms of simplicial sets, multiplied by a simplicial
object.** Given a homotopy `h` from `f` to `g`, the family carrying the summand of `(U × V)_n`
indexed by `u` into the summand of `(U' × V)_{n + 1}` indexed by `h_i(u)` by the degeneracy
`σ_i` of `V` is a homotopy from `f × V` to `g × V`. -/
noncomputable def Homotopy.copower {f g : U ⟶ U'} (H : Homotopy f g) :
    Homotopy (Functor.copowerMap (𝟙 V) f) (Functor.copowerMap (𝟙 V) g) where
  h {n} i := Sigma.map' (H.h i) fun _ => V.σ i
  h_zero_comp_δ_zero n := by
    refine Sigma.hom_ext _ _ fun u => ?_
    have hidx := ConcreteCategory.congr_hom (H.h_zero_comp_δ_zero n) u
    simp only [CategoryTheory.comp_apply] at hidx
    rw [Sigma.ι_comp_map'_assoc, ι_copower_δ, V.δ_comp_σ_self'_assoc (by simp),
      Functor.ι_copowerMap_app]
    simp [hidx]
  h_last_comp_δ_last n := by
    refine Sigma.hom_ext _ _ fun u => ?_
    have hidx := ConcreteCategory.congr_hom (H.h_last_comp_δ_last n) u
    simp only [CategoryTheory.comp_apply] at hidx
    rw [Sigma.ι_comp_map'_assoc, ι_copower_δ, V.δ_comp_σ_succ'_assoc (by simp),
      Functor.ι_copowerMap_app]
    simp [hidx]
  h_succ_comp_δ_castSucc_of_lt i j hij := by
    refine Sigma.hom_ext _ _ fun u => ?_
    have hidx := ConcreteCategory.congr_hom (H.h_succ_comp_δ_castSucc_of_lt i j hij) u
    simp only [CategoryTheory.comp_apply] at hidx
    rw [Sigma.ι_comp_map'_assoc, ι_copower_δ, V.δ_comp_σ_of_le_assoc hij, ι_copower_δ_assoc,
      Sigma.ι_comp_map']
    simp [hidx]
  h_succ_comp_δ_castSucc_succ {n} j := by
    refine Sigma.hom_ext _ _ fun u => ?_
    have hidx := ConcreteCategory.congr_hom (H.h_succ_comp_δ_castSucc_succ j) u
    simp only [CategoryTheory.comp_apply] at hidx
    rw [Sigma.ι_comp_map'_assoc, ι_copower_δ, Sigma.ι_comp_map'_assoc, ι_copower_δ,
      V.δ_comp_σ_self'_assoc (by simp), V.δ_comp_σ_succ'_assoc (by simp)]
    simp [hidx]
  h_castSucc_comp_δ_succ_of_lt i j hji := by
    refine Sigma.hom_ext _ _ fun u => ?_
    have hidx := ConcreteCategory.congr_hom (H.h_castSucc_comp_δ_succ_of_lt i j hji) u
    simp only [CategoryTheory.comp_apply] at hidx
    rw [Sigma.ι_comp_map'_assoc, ι_copower_δ, V.δ_comp_σ_of_gt_assoc hji, ι_copower_δ_assoc,
      Sigma.ι_comp_map']
    simp [hidx]
  h_comp_σ_castSucc_of_le i j hij := by
    refine Sigma.hom_ext _ _ fun u => ?_
    have hidx := ConcreteCategory.congr_hom (H.h_comp_σ_castSucc_of_le i j hij) u
    simp only [CategoryTheory.comp_apply] at hidx
    rw [Sigma.ι_comp_map'_assoc, ι_copower_σ, V.σ_comp_σ_assoc hij, ι_copower_σ_assoc,
      Sigma.ι_comp_map']
    simp [hidx]
  h_comp_σ_succ_of_lt i j hji := by
    refine Sigma.hom_ext _ _ fun u => ?_
    have hidx := ConcreteCategory.congr_hom (H.h_comp_σ_succ_of_lt i j hji) u
    simp only [CategoryTheory.comp_apply] at hidx
    rw [Sigma.ι_comp_map'_assoc, ι_copower_σ, ← V.σ_comp_σ_assoc hji, ι_copower_σ_assoc,
      Sigma.ι_comp_map']
    simp [hidx]

end

section

variable (V : SimplicialObject C)

/-- An equivalence relation generated by one relation is carried into the one generated by
another by any map matching the two generating relations. -/
private lemma eqvGen_map {α β : Type*} {r : α → α → Prop} {s : β → β → Prop} (φ : α → β)
    (hφ : ∀ x y, r x y → s (φ x) (φ y)) {x y : α} (hxy : Relation.EqvGen r x y) :
    Relation.EqvGen s (φ x) (φ y) := by
  induction hxy with
  | rel _ _ h => exact .rel _ _ (hφ _ _ h)
  | refl _ => exact .refl _
  | symm _ _ _ ih => exact ih.symm _ _
  | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans _ _ _ ih₂

/-- Two homotopic endomorphisms of a simplicial set stay homotopic after multiplication by a
simplicial object. -/
lemma eqvGen_homotopy_copowerMap_id {U : SimplicialObject (Type w)}
    [∀ j, HasCoproduct fun _ : U.obj j => V.obj j] {x y : U ⟶ U}
    (hxy : Relation.EqvGen (fun a b : U ⟶ U => Nonempty (Homotopy a b)) x y) :
    Relation.EqvGen
      (fun a b : V.copower U ⟶ V.copower U => Nonempty (Homotopy a b))
      (Functor.copowerMap (𝟙 V) x) (Functor.copowerMap (𝟙 V) y) :=
  eqvGen_map _ (fun _ _ h => ⟨h.some.copower V⟩) hxy

/-- **Homotopy equivalences of simplicial objects are stable under composition with
isomorphisms on either side.** Being homotopic is a congruence ([Stacks, Tag 08RJ]), so a
homotopy inverse of `a` conjugates to one of `e ≫ a ≫ e'`. -/
lemma homotopyEquivalences_iso_comp_iso {X Y X' Y' : SimplicialObject C} (e : X' ≅ X)
    (a : X ⟶ Y) (e' : Y ≅ Y') (ha : homotopyEquivalences C a) :
    homotopyEquivalences C (e.hom ≫ a ≫ e'.hom) := by
  obtain ⟨b, hab, hba⟩ := ha
  refine ⟨e'.inv ≫ b ≫ e.inv, ?_, ?_⟩
  · have h := (congruence_homotopic (C := C)).comp_left e.hom
      ((congruence_homotopic (C := C)).comp_right e.inv hab)
    simpa using h
  · have h := (congruence_homotopic (C := C)).comp_left e'.inv
      ((congruence_homotopic (C := C)).comp_right e'.hom hba)
    simpa using h

/-- **Multiplying by a simplicial object preserves homotopy equivalences.** If `a : U ⟶ U'` is
a homotopy equivalence of simplicial sets, then `a × V : U × V ⟶ U' × V` is a homotopy
equivalence of simplicial objects of `C`. -/
lemma homotopyEquivalences_copowerMap_id {U U' : SimplicialObject (Type w)}
    [∀ j, HasCoproduct fun _ : U.obj j => V.obj j]
    [∀ j, HasCoproduct fun _ : U'.obj j => V.obj j] {a : U ⟶ U'}
    (ha : homotopyEquivalences (Type w) a) :
    homotopyEquivalences C (Functor.copowerMap (𝟙 V) a) := by
  obtain ⟨b, hab, hba⟩ := ha
  refine ⟨Functor.copowerMap (𝟙 V) b, ?_, ?_⟩
  · have h := eqvGen_homotopy_copowerMap_id V hab
    rw [Functor.copowerMap_id] at h
    rwa [Functor.copowerMap_comp, Category.comp_id]
  · have h := eqvGen_homotopy_copowerMap_id V hba
    rw [Functor.copowerMap_id] at h
    rwa [Functor.copowerMap_comp, Category.comp_id]

end

end CategoryTheory.SimplicialObject

end
