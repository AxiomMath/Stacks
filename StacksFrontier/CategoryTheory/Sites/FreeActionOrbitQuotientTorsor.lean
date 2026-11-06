module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.CategoryTheory.Sites.CharacterTwistTorsor

/-!
# A free action whose quotient is the final object makes its object a torsor

Let `C` be a site, let a group `G` act by automorphisms on an object `W` of `C` and let
`q : W ⟶ T` be a morphism invariant under the action. The *presheaf of orbits* of `W` is
`V ↦ (V ⟶ W)/G`, and `q` exhibits `T` as the quotient `W/G` when the induced morphism from the
presheaf of orbits to `Hom(-, T)` is locally bijective, that is when the sheafification of the
presheaf of orbits is the sheaf represented by `T`. This is
`CategoryTheory.IsOrbitQuotient`.

This file proves that for a free action whose quotient is the final object the object `W` is a
`G`-torsor over the final object in the sense of `CategoryTheory.IsTorsorObject`: that notion
asks that the morphisms into `W` cover every object, that any two morphisms into `W` become
translates of each other locally, and that the action on the morphisms into `W` is free, and
the first two of those are exactly local surjectivity and local injectivity of the comparison
morphism, the base being final. This is the first sentence of the proof of Stacks 0727 — *the
quotient morphism `q : W ⟶ U` is a `G`-torsor, namely `U' = W` works* — and it is what lets
the two halves of that tag be stated at the hypotheses of the source, a free action with
quotient the base, rather than at the torsor property itself.

The converse also holds, and is recorded: over a final object the torsor property says
precisely that the quotient of `W` by `G` is that final object. Freeness is not used for it,
and is not implied by it.

## Main definitions

* `CategoryTheory.ActsFreelyOnObject` is freeness of an action of `G` on an object of a site:
  a morphism into `W` fixed by a group element forces that element to be trivial, except over
  the objects covered by the empty sieve.
* `CategoryTheory.actOrbitPresheaf` is the presheaf of orbits `V ↦ (V ⟶ W)/G`, with
  `CategoryTheory.actOrbitClass` the orbit of a morphism and
  `CategoryTheory.actOrbitProjection` the projection of `Hom(-, W)` onto it.
* `CategoryTheory.actOrbitDesc` is the morphism from the presheaf of orbits to `Hom(-, T)`
  induced by an invariant morphism `q : W ⟶ T`.
* `CategoryTheory.IsOrbitQuotient` says that `q` exhibits `T` as the quotient `W/G`.

## Main results

* `CategoryTheory.isOrbitQuotient_of_isIso_presheafToSheaf_map` and
  `CategoryTheory.IsOrbitQuotient.isIso_presheafToSheaf_map`: that condition holds precisely
  when sheafification identifies the presheaf of orbits with the sheaf represented by `T`, that
  is precisely when the quotient sheaf `W/G` is `T`.
* `CategoryTheory.IsOrbitQuotient.splittingSieve_mem` and
  `CategoryTheory.IsOrbitQuotient.translationSieve_mem`: over a final object the quotient
  morphism is covering and its kernel pair is the orbit relation.
* `CategoryTheory.IsOrbitQuotient.isTorsorObject`: **a free action whose quotient is the final
  object makes `W` a `G`-torsor over the final object.**
* `CategoryTheory.IsTorsorObject.isOrbitQuotient`: conversely, a `G`-torsor over a final object
  has that final object as its quotient.
* `CategoryTheory.IsOrbitQuotient.exists_sieve_existsUnique_comp_act`: **the kernel pair of the
  quotient morphism is one copy of `W` for each group element**, locally on the base and with
  the group element unique away from the objects covered by the empty sieve. This is the
  source's `W ×_U W = ∐_{g ∈ G} W`.

## Implementation notes

Freeness carries the escape over the objects covered by the empty sieve, as it must: a sheaf
has exactly one section over such an object, so every group element fixes every morphism there,
and asking freeness without the escape would force `G` to be trivial. This is the same reading
of freeness as `CategoryTheory.IsTorsorObject.eq_one_of_comp_act`, as
`AlgebraicGeometry.Space.IsFreeOnNonemptyPoints` on the big fppf site, and as the freeness of
the symmetric group action of Stacks 0726 in
`AlgebraicGeometry.Space.SpacesEtale.eq_one_of_comp_diagonalComplementAut`.

Nothing here assumes `G` finite: finiteness is used in Stacks 0727 to know that the quotient
is an algebraic space with étale quotient morphism, not for the torsor property, which is a
statement about the site and the quotient alone.

## References

* [Stacks Project, Tag 0727](https://stacks.math.columbia.edu/tag/0727)
* [Stacks Project, Tag 071S](https://stacks.math.columbia.edu/tag/071S)
-/

@[expose] public section

universe w v u

namespace CategoryTheory

open Limits Opposite

variable {C : Type u} [Category.{v} C] {W : C} {G : Type w} [Group G]

/-! ### Free actions on an object of a site -/

/-- An action of a group `G` by automorphisms on an object `W` of a site is **free** when a
morphism into `W` fixed by a group element forces that element to be trivial, over every object
that the empty sieve does not cover.

The escape is necessary: a sheaf has exactly one section over an object covered by the empty
sieve, so over such an object every group element fixes every morphism into `W`, and freeness
without the escape would force `G` to be trivial. -/
def ActsFreelyOnObject (act : G →* Aut W) (J : GrothendieckTopology C) : Prop :=
  ∀ ⦃V : C⦄ (φ : V ⟶ W) (g : G), φ ≫ (act g).asIso.hom = φ → (⊥ : Sieve V) ∈ J V ∨ g = 1

/-! ### The presheaf of orbits -/

/-- Two morphisms into `W` lie in the same orbit when a group element carries the first to the
second. -/
def actOrbitSetoid (act : G →* Aut W) (V : C) : Setoid (V ⟶ W) where
  r φ ψ := ∃ g : G, φ ≫ (act g).asIso.hom = ψ
  iseqv :=
    { refl := fun φ => ⟨1, by rw [act_hom_one, Category.comp_id]⟩
      symm := by
        rintro φ ψ ⟨g, rfl⟩
        refine ⟨g⁻¹, ?_⟩
        rw [Category.assoc, ← act_hom_mul, inv_mul_cancel, act_hom_one, Category.comp_id]
      trans := by
        rintro φ ψ ρ ⟨g, rfl⟩ ⟨g', rfl⟩
        exact ⟨g' * g, by rw [act_hom_mul, Category.assoc]⟩ }

/-- The map on orbit sets induced by precomposition with a morphism of the site. -/
def actOrbitMap (act : G →* Aut W) {V V' : C} (f : V' ⟶ V) :
    _root_.Quotient (actOrbitSetoid act V) → _root_.Quotient (actOrbitSetoid act V') :=
  _root_.Quotient.map (fun φ => f ≫ φ) (by
    rintro φ ψ ⟨g, rfl⟩
    exact ⟨g, Category.assoc _ _ _⟩)

/-- **The presheaf of orbits of the morphisms into `W`**: its value at `V` is the set of
morphisms `V ⟶ W` modulo the action of `G`, and its sheafification is the quotient `W/G`. -/
def actOrbitPresheaf (W : C) (act : G →* Aut W) : Cᵒᵖ ⥤ Type v where
  obj V := _root_.Quotient (actOrbitSetoid act V.unop)
  map f := ↾(actOrbitMap act f.unop)
  map_id V := by
    apply ConcreteCategory.hom_ext
    intro x
    induction x using _root_.Quotient.inductionOn with
    | _ φ => exact congrArg (_root_.Quotient.mk _) (Category.id_comp φ)
  map_comp f g := by
    apply ConcreteCategory.hom_ext
    intro x
    induction x using _root_.Quotient.inductionOn with
    | _ φ => exact congrArg (_root_.Quotient.mk _) (Category.assoc _ _ _)

/-- The orbit of a morphism into `W`, as a section of the presheaf of orbits. -/
def actOrbitClass (act : G →* Aut W) {V : C} (φ : V ⟶ W) :
    (actOrbitPresheaf W act).obj (op V) :=
  _root_.Quotient.mk _ φ

/-- Two morphisms into `W` have the same orbit if and only if a group element carries the first to
the second. -/
theorem actOrbitClass_eq_iff (act : G →* Aut W) {V : C} (φ ψ : V ⟶ W) :
    actOrbitClass act φ = actOrbitClass act ψ ↔ ∃ g : G, φ ≫ (act g).asIso.hom = ψ :=
  ⟨fun h => _root_.Quotient.exact h, fun h => _root_.Quotient.sound h⟩

/-- Restricting the orbit of `φ` along `f` gives the orbit of `f ≫ φ`. -/
@[simp]
theorem actOrbitPresheaf_map_actOrbitClass (act : G →* Aut W) {V V' : C} (f : V' ⟶ V)
    (φ : V ⟶ W) :
    (actOrbitPresheaf W act).map f.op (actOrbitClass act φ) = actOrbitClass act (f ≫ φ) :=
  rfl

/-- Every section of the presheaf of orbits is the orbit of a morphism into `W`. -/
theorem exists_actOrbitClass_eq (act : G →* Aut W) {V : C}
    (x : (actOrbitPresheaf W act).obj (op V)) : ∃ φ : V ⟶ W, actOrbitClass act φ = x :=
  x.exists_rep

/-- The projection of `Hom(-, W)` onto the presheaf of orbits. -/
def actOrbitProjection (W : C) (act : G →* Aut W) : yoneda.obj W ⟶ actOrbitPresheaf W act where
  app _ := ↾(fun φ => _root_.Quotient.mk _ φ)
  naturality _ _ _ := rfl

/-- The projection onto the presheaf of orbits sends a morphism to its orbit. -/
@[simp]
theorem actOrbitProjection_app (act : G →* Aut W) {V : C} (φ : V ⟶ W) :
    (actOrbitProjection W act).app (op V) φ = actOrbitClass act φ :=
  rfl

/-- The morphism from the presheaf of orbits of `W` to `Hom(-, T)` induced by a morphism
`q : W ⟶ T` invariant under the action. -/
def actOrbitDesc (act : G →* Aut W) {T : C} (q : W ⟶ T)
    (hq : ∀ g : G, (act g).asIso.hom ≫ q = q) : actOrbitPresheaf W act ⟶ yoneda.obj T where
  app _ := ↾(_root_.Quotient.lift (fun φ => φ ≫ q) (by
    rintro φ ψ ⟨g, rfl⟩
    rw [Category.assoc, hq]))
  naturality _ _ f := by
    apply ConcreteCategory.hom_ext
    intro x
    induction x using _root_.Quotient.inductionOn with
    | _ φ => exact Category.assoc f.unop φ q

/-- The morphism induced by an invariant `q` sends the orbit of `φ` to `φ ≫ q`. -/
@[simp]
theorem actOrbitDesc_actOrbitClass (act : G →* Aut W) {T : C} (q : W ⟶ T)
    (hq : ∀ g : G, (act g).asIso.hom ≫ q = q) {V : C} (φ : V ⟶ W) :
    (actOrbitDesc act q hq).app (op V) (actOrbitClass act φ) = φ ≫ q :=
  rfl

/-! ### Quotients -/

/-- A morphism `q : W ⟶ T` **exhibits `T` as the quotient `W/G`** when it is invariant under
the action and the induced morphism from the presheaf of orbits of `W` to `Hom(-, T)` is
locally bijective, that is when the sheafification of `V ↦ (V ⟶ W)/G` is the sheaf represented
by `T`.

Local surjectivity says that `q` is surjective as a morphism of sheaves, and local injectivity
that its kernel pair is the orbit relation. -/
structure IsOrbitQuotient (act : G →* Aut W) (J : GrothendieckTopology C) {T : C} (q : W ⟶ T) :
    Prop where
  /-- The morphism is invariant under the action. -/
  comp_eq (g : G) : (act g).asIso.hom ≫ q = q
  /-- Every morphism into `T` lifts to `W`, locally on the source. -/
  isLocallySurjective : Presheaf.IsLocallySurjective J (actOrbitDesc act q comp_eq)
  /-- Two morphisms into `W` with the same composite to `T` are in the same orbit, locally on
  the source. -/
  isLocallyInjective : Presheaf.IsLocallyInjective J (actOrbitDesc act q comp_eq)

/-! ### The quotient condition as an identification of sheaves -/

section Sheafification

variable {act : G →* Aut W} {J : GrothendieckTopology C} [HasWeakSheafify J (Type v)]
  [J.WEqualsLocallyBijective (Type v)] {T : C} {q : W ⟶ T}

/-- **If the quotient sheaf `W/G` is the sheaf represented by `T` then `q` exhibits `T` as the
quotient `W/G`.** The hypothesis is that sheafification carries the comparison morphism from the
presheaf of orbits to an isomorphism, which is exactly the identification of `W/G` with `T`. -/
theorem isOrbitQuotient_of_isIso_presheafToSheaf_map (hq : ∀ g : G, (act g).asIso.hom ≫ q = q)
    (h : IsIso ((presheafToSheaf J (Type v)).map (actOrbitDesc act q hq))) :
    IsOrbitQuotient act J q where
  comp_eq := hq
  isLocallySurjective := ((J.W_iff _).mpr h).isLocallySurjective
  isLocallyInjective := ((J.W_iff _).mpr h).isLocallyInjective

/-- Conversely, if `q` exhibits `T` as the quotient `W/G` then sheafification carries the
comparison morphism from the presheaf of orbits to an isomorphism: the quotient sheaf `W/G` is
the sheaf represented by `T`. -/
theorem IsOrbitQuotient.isIso_presheafToSheaf_map (hq : IsOrbitQuotient act J q) :
    IsIso ((presheafToSheaf J (Type v)).map (actOrbitDesc act q hq.comp_eq)) :=
  (J.W_iff _).mp ((J.W_iff_isLocallyBijective _).mpr
    ⟨hq.isLocallyInjective, hq.isLocallySurjective⟩)

end Sheafification

namespace IsOrbitQuotient

variable {act : G →* Aut W} {J : GrothendieckTopology C} {T : C} {q : W ⟶ T}
  (hq : IsOrbitQuotient act J q) (hT : IsTerminal T)

include hq hT

/-- **The morphisms into `W` cover every object**, when the quotient of `W` by `G` is a final
object: every object maps to the final object, and that morphism lifts to `W` locally. -/
theorem splittingSieve_mem (V : C) : splittingSieve W V ∈ J V := by
  have := hq.isLocallySurjective
  refine J.superset_covering ?_
    (Presheaf.imageSieve_mem J (actOrbitDesc act q hq.comp_eq) (U := op V) (hT.from V))
  rintro V' f ⟨x, -⟩
  obtain ⟨φ, -⟩ := exists_actOrbitClass_eq act x
  exact ⟨φ⟩

/-- **Any two morphisms into `W` are translates of each other locally**, when the quotient of
`W` by `G` is a final object: the two morphisms have the same composite to the final object, so
their orbits agree locally. -/
theorem translationSieve_mem {V : C} (φ ψ : V ⟶ W) : translationSieve act φ ψ ∈ J V := by
  have := hq.isLocallyInjective
  refine J.superset_covering ?_ (Presheaf.equalizerSieve_mem J
    (actOrbitDesc act q hq.comp_eq) (actOrbitClass act φ) (actOrbitClass act ψ) (hT.hom_ext _ _))
  intro V' f hf
  obtain ⟨g, hg⟩ := (actOrbitClass_eq_iff act (f ≫ φ) (f ≫ ψ)).mp hf
  exact ⟨g, by rw [← hg, Category.assoc]⟩

/-- **A free action whose quotient is the final object makes its object a torsor over the final
object.** This is the first sentence of the proof of Stacks 0727: the quotient morphism of a
free action is a `G`-torsor, split by the total space itself. -/
theorem isTorsorObject (hfree : ActsFreelyOnObject act J) : IsTorsorObject act J where
  splittingSieve_mem := hq.splittingSieve_mem hT
  translationSieve_mem := hq.translationSieve_mem hT
  eq_one_of_comp_act φ g h := hfree φ g h

/-- **The kernel pair of the quotient morphism of a free action is one copy of `W` for each
group element.** Two morphisms into `W` are, locally on the source, translates of each other by
a group element which is unique over every object the empty sieve does not cover.

This is the source's description of the torsor: `W ×_U W = ∐_{g ∈ G} W` as objects with
`G`-action over `W`. It is a statement about covering sieves rather than about morphisms
because the presheaf of orbits is not separated: over an object with two disjoint pieces two
morphisms into `W` can be translates of each other by different group elements on the two
pieces. -/
theorem exists_sieve_existsUnique_comp_act (hfree : ActsFreelyOnObject act J) {V : C}
    (φ ψ : V ⟶ W) :
    ∃ S : Sieve V, S ∈ J V ∧ ∀ ⦃V' : C⦄ (f : V' ⟶ V), S f → (⊥ : Sieve V') ∉ J V' →
      ∃! g : G, f ≫ φ ≫ (act g).asIso.hom = f ≫ ψ := by
  refine ⟨translationSieve act φ ψ, hq.translationSieve_mem hT φ ψ, ?_⟩
  rintro V' f ⟨g, hg⟩ hV'
  refine ⟨g, hg.symm, fun g' hg' => ?_⟩
  refine (hq.isTorsorObject hT hfree).injective_comp_act (f ≫ φ) hV' ?_
  change (f ≫ φ) ≫ (act g').asIso.hom = (f ≫ φ) ≫ (act g).asIso.hom
  rw [Category.assoc, Category.assoc, hg', ← hg]

end IsOrbitQuotient

/-- **A torsor over a final object has that final object as its quotient.** The two local
conditions on the comparison morphism from the presheaf of orbits are the two covering clauses
of the torsor property; freeness is not used, and is not implied. -/
theorem IsTorsorObject.isOrbitQuotient {act : G →* Aut W} {J : GrothendieckTopology C}
    (h : IsTorsorObject act J) {T : C} (hT : IsTerminal T) :
    IsOrbitQuotient act J (hT.from W) where
  comp_eq _ := hT.hom_ext _ _
  isLocallySurjective := by
    constructor
    intro V x
    refine J.superset_covering ?_ (h.splittingSieve_mem V)
    rintro V' f ⟨φ⟩
    exact ⟨actOrbitClass act φ, hT.hom_ext _ _⟩
  isLocallyInjective := by
    constructor
    intro V x y _
    obtain ⟨φ, rfl⟩ := exists_actOrbitClass_eq act x
    obtain ⟨ψ, rfl⟩ := exists_actOrbitClass_eq act y
    refine J.superset_covering ?_ (h.translationSieve_mem φ ψ)
    rintro V' f ⟨g, hg⟩
    exact (actOrbitClass_eq_iff act (f ≫ φ) (f ≫ ψ)).mpr ⟨g, by rw [Category.assoc, ← hg]⟩

end CategoryTheory

end
