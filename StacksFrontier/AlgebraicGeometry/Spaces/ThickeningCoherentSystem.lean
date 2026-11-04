module

public import Mathlib.CategoryTheory.Functor.OfSequence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCoherentEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionIdealQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImageUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentCompletionFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp

/-!
# Coherent systems on a tower of thickenings

Let `X` be an algebraic space and let `Z 0 → Z 1 → Z 2 → ⋯` be a tower of closed subspaces
`ι n : Z n ⟶ X`, with transition morphisms `t n : Z n ⟶ Z (n + 1)` satisfying
`t n ≫ ι (n + 1) = ι n`.  A *coherent system* on the tower is a family of coherent
`𝒪_{Z n}`-modules `F_n` together with isomorphisms `φ_n : t n ^* F_{n + 1} ≅ F_n`. This file
sets up that category, the restriction functor `F ↦ (ι n ^* F)_n` from coherent `𝒪_X`-modules,
and the direct image `(F_n, φ_n) ↦ ((ι n)_* F_n)_n` to inverse systems of `𝒪_X`-modules.

The direct image is fully faithful: levelwise, direct image along a closed immersion is fully
faithful (equivalently the counit `ι^* ι_* ≅ 𝟭`), and a family of maps of terms is compatible
with the `φ_n` exactly when its direct images commute with the transition maps. The transition
map `(ι (n + 1))_* F_{n + 1} ⟶ (ι n)_* F_n` is the adjoint of the identification
`ι n ^* (ι (n + 1))_* F_{n + 1} ≅ t n ^* ι (n + 1) ^* (ι (n + 1))_* F_{n + 1} ≅
t n ^* F_{n + 1} ≅ F_n`. If the ideal of `ι n` acts on every `𝒪_X`-module `M` as `𝓘 ^ (n + 1)`,
then the terms of the direct image are coherent and annihilated by `𝓘 ^ (n + 1)`, and
`M / 𝓘 ^ (n + 1) M` is identified with `(ι n)_* ι n ^* M`, which is the quotient condition of a
coherent adic system for a transition map adjoint to an isomorphism. The same identification,
natural in `M`, gives `Ψ ∘ Φ ≅ (-)^∧`: the direct image of the restriction of a coherent module to
the thickenings is its completion. Hence `Φ` is fully faithful, resp. essentially surjective, as
soon as the completion functor is.

The category theory is carried out for an arbitrary tower of categories `C n` with functors
`T n : C (n + 1) ⥤ C n`, functors `L n : D ⥤ C n` with `T n ∘ L (n + 1) ≅ L n` and fully faithful
right adjoints `R n` of the `L n`; the algebraic spaces enter only through the instantiation
`C n = Mod(𝒪_{Z n})`, `T n = t n ^*`, `L n = ι n ^*`, `R n = (ι n)_*`.

## Main definitions

* `CategoryTheory.TowerSystem` — systems along a tower of categories, and their category.
* `CategoryTheory.TowerSystem.restriction` — restriction of objects of `D` to the tower.
* `CategoryTheory.TowerSystem.pushforward` — the direct image to inverse systems in `D`.
* `AlgebraicGeometry.Space.ThickeningCoherentSystem` — the category of coherent systems
  `(F_n, φ_n)` on a tower of closed subspaces of an algebraic space.
* `AlgebraicGeometry.Space.thickeningRestriction` — `Φ : F ↦ (ι n ^* F)_n`.
* `AlgebraicGeometry.Space.thickeningPushforwardSystems` — `(F_n, φ_n) ↦ ((ι n)_* F_n)_n`.
* `AlgebraicGeometry.Space.thickeningPushforward` — `Ψ`, the same with values in `Coh(X, 𝓘)`.

## Main results

* `CategoryTheory.TowerSystem.fullyFaithfulPushforward` and
  `AlgebraicGeometry.Space.thickeningPushforwardFullyFaithful` — the direct image of systems
  is fully faithful.
* `CategoryTheory.TowerSystem.restrictionCompPushforwardIsoOfUnit` — the direct image of the
  restriction is any functor of quotients identified with the `R n (L n M)` through the units.
* `AlgebraicGeometry.Space.thickeningPushforwardRestrictionIso` — levelwise,
  `((ι n)_* ι n ^* F)_n ≅ (F / 𝓘 ^ (n + 1) F)_n`.
* `AlgebraicGeometry.Space.thickeningRestrictionCompPushforwardIso` — `Ψ ∘ Φ ≅ (-)^∧`.
* `AlgebraicGeometry.Space.thickeningRestrictionFullyFaithful` and
  `AlgebraicGeometry.Space.essSurj_thickeningRestriction` — `Φ` is fully faithful, resp.
  essentially surjective, if the completion functor is.

## Implementation notes

The terms of a system are objects of the full subcategory of coherent modules, while morphisms of
systems are morphisms of the underlying modules; the full subcategory is full, so this is the same
category as the one with morphisms in the full subcategory. No condition on supports is imposed
on the terms.

The comparison with the completion takes its hypotheses packaged in the structures
`CategoryTheory.TowerSystem.IsUnitQuotient` and `CategoryTheory.TowerSystem.IsUnitQuotientFunctor`,
and the quotients are written as cokernels: the instantiation then type-checks by comparing
arguments, without unfolding the module categories.

## References

* [Stacks Project, Tag 08BF](https://stacks.math.columbia.edu/tag/08BF)
* [Stacks Project, Tag 08AM](https://stacks.math.columbia.edu/tag/08AM)
* [Stacks Project, Tag 04CJ](https://stacks.math.columbia.edu/tag/04CJ)
* [Stacks Project, Tag 08B4](https://stacks.math.columbia.edu/tag/08B4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ v₂ u₁ u₂ u

namespace CategoryTheory

variable {C : ℕ → Type u₁} [∀ n, Category.{v₁} (C n)]

/-- If a map `π : M ⟶ Q` followed by an isomorphism `q : Q ≅ R (L M)` is the unit of `L ⊣ R`,
then `π` followed by `q` and `R` of an isomorphism `e : L M ≅ N` is the adjoint of `e`. -/
theorem Adjunction.comp_trans_mapIso_hom_eq_homEquiv {D : Type u₂} [Category.{v₂} D]
    {E : Type*} [Category E] {L : D ⥤ E} {R : E ⥤ D} (adj : L ⊣ R) {M Q : D} {N : E}
    (π : M ⟶ Q) (q : Q ≅ R.obj (L.obj M)) (e : L.obj M ≅ N) (h : π ≫ q.hom = adj.unit.app M) :
    π ≫ (q ≪≫ R.mapIso e).hom = adj.homEquiv M N e.hom := by
  rw [Iso.trans_hom, ← Category.assoc, h, Functor.mapIso_hom, Adjunction.homEquiv_unit]

/-- An inverse system `G : ℕᵒᵖ ⥤ D` is isomorphic to the functor `ℕᵒᵖ ⥤ D` built from its
transition maps `G (n + 1) ⟶ G n`. -/
def Functor.ofOpSequenceMapIso {D : Type u₂} [Category.{v₂} D] (G : ℕᵒᵖ ⥤ D) :
    Functor.ofOpSequence (X := fun n => G.obj (op n))
      (fun n => G.map (homOfLE (Nat.le_succ n)).op) ≅ G where
  hom := NatTrans.ofOpSequence (fun n => 𝟙 (G.obj (op n))) fun n => by
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  inv := NatTrans.ofOpSequence (fun n => 𝟙 (G.obj (op n))) fun n => by
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  hom_inv_id := NatTrans.ext (funext fun _ => Category.id_comp _)
  inv_hom_id := NatTrans.ext (funext fun _ => Category.id_comp _)

/-- The components of `CategoryTheory.Functor.ofOpSequenceMapIso` are identities. -/
@[simp]
theorem Functor.ofOpSequenceMapIso_hom_app {D : Type u₂} [Category.{v₂} D] (G : ℕᵒᵖ ⥤ D)
    (n : ℕ) : (Functor.ofOpSequenceMapIso G).hom.app (op n) = 𝟙 (G.obj (op n)) :=
  rfl

/-- A system along a tower of categories: objects `F n` of `C n` satisfying `P n`, together with
isomorphisms `T n (F (n + 1)) ≅ F n`. -/
structure TowerSystem (P : ∀ n, ObjectProperty (C n)) (T : ∀ n, C (n + 1) ⥤ C n) where
  /-- The term in `C n`. -/
  term (n : ℕ) : (P n).FullSubcategory
  /-- The identification of the transport of the next term with the term. -/
  transitionIso (n : ℕ) : (T n).obj (term (n + 1)).obj ≅ (term n).obj

namespace TowerSystem

variable {P : ∀ n, ObjectProperty (C n)} {T : ∀ n, C (n + 1) ⥤ C n}

/-- A morphism of systems: maps of the terms compatible with the transition isomorphisms. -/
@[ext]
structure Hom (A A' : TowerSystem P T) where
  /-- The component in `C n`. -/
  app (n : ℕ) : (A.term n).obj ⟶ (A'.term n).obj
  /-- The components are compatible with the transition isomorphisms. -/
  comm (n : ℕ) : (T n).map (app (n + 1)) ≫ (A'.transitionIso n).hom =
    (A.transitionIso n).hom ≫ app n

attribute [reassoc] Hom.comm

/-- The identity morphism of a system. -/
def Hom.id (A : TowerSystem P T) : Hom A A where
  app n := 𝟙 _
  comm n := by simp

/-- The composite of two morphisms of systems. -/
def Hom.comp {A A' A'' : TowerSystem P T} (f : Hom A A') (g : Hom A' A'') : Hom A A'' where
  app n := f.app n ≫ g.app n
  comm n := by rw [Functor.map_comp, Category.assoc, g.comm, f.comm_assoc]

/-- The category of systems along a tower. -/
instance : Category (TowerSystem P T) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext (funext fun _ => Category.id_comp _)
  comp_id _ := Hom.ext (funext fun _ => Category.comp_id _)
  assoc _ _ _ := Hom.ext (funext fun _ => Category.assoc _ _ _)

/-- Morphisms of systems are determined by their components. -/
@[ext]
theorem hom_ext {A A' : TowerSystem P T} {f g : A ⟶ A'} (h : ∀ n, f.app n = g.app n) : f = g :=
  Hom.ext (funext h)

/-- The components of the identity are identities. -/
@[simp]
theorem id_app (A : TowerSystem P T) (n : ℕ) : (𝟙 A : A ⟶ A).app n = 𝟙 _ :=
  rfl

/-- The components of a composite are the composites of the components. -/
@[simp, reassoc]
theorem comp_app {A A' A'' : TowerSystem P T} (f : A ⟶ A') (g : A' ⟶ A'') (n : ℕ) :
    (f ≫ g).app n = f.app n ≫ g.app n :=
  rfl

/-! ### Restriction -/

section Restriction

variable {D : Type u₂} [Category.{v₂} D] (Q : ObjectProperty D) (L : ∀ n, D ⥤ C n)
  (ρ : ∀ n, L (n + 1) ⋙ T n ≅ L n) (hL : ∀ n M, Q M → P n ((L n).obj M))

/-- Restriction of an object of `D` to the tower along functors `L n : D ⥤ C n` with
`T n ∘ L (n + 1) ≅ L n`. -/
def restriction : Q.FullSubcategory ⥤ TowerSystem P T where
  obj M :=
    { term n := ⟨(L n).obj M.obj, hL n M.obj M.property⟩
      transitionIso n := (ρ n).app M.obj }
  map f :=
    { app n := (L n).map f.hom
      comm n := (ρ n).hom.naturality f.hom }
  map_id _ := hom_ext fun n => (L n).map_id _
  map_comp _ _ := hom_ext fun n => (L n).map_comp _ _

/-- The terms of a restricted object. -/
@[simp]
theorem restriction_obj_term_obj (M : Q.FullSubcategory) (n : ℕ) :
    (((restriction Q L ρ hL).obj M).term n).obj = (L n).obj M.obj :=
  rfl

/-- The transition isomorphisms of a restricted object. -/
@[simp]
theorem restriction_obj_transitionIso (M : Q.FullSubcategory) (n : ℕ) :
    ((restriction Q L ρ hL).obj M).transitionIso n = (ρ n).app M.obj :=
  rfl

/-- The components of a restricted morphism. -/
@[simp]
theorem restriction_map_app {M M' : Q.FullSubcategory} (f : M ⟶ M') (n : ℕ) :
    ((restriction Q L ρ hL).map f).app n = (L n).map f.hom :=
  rfl

end Restriction

/-! ### Direct image -/

section Pushforward

variable {D : Type u₂} [Category.{v₂} D] {L : ∀ n, D ⥤ C n} {R : ∀ n, C n ⥤ D}
  (adj : ∀ n, L n ⊣ R n) (hR : ∀ n, (R n).FullyFaithful) (ρ : ∀ n, L (n + 1) ⋙ T n ≅ L n)

/-- The identification `L n (R (n + 1) F_{n + 1}) ≅ F_n`: the comparison `L n ≅ T n ∘ L (n + 1)`,
then `T n` of the counit, invertible since `R (n + 1)` is fully faithful, then `φ_n`. -/
def pullbackPushforwardIso (A : TowerSystem P T) (n : ℕ) :
    (L n).obj ((R (n + 1)).obj (A.term (n + 1)).obj) ≅ (A.term n).obj :=
  haveI := (hR (n + 1)).full
  haveI := (hR (n + 1)).faithful
  ((ρ n).app _).symm ≪≫
    (T n).mapIso (asIso ((adj (n + 1)).counit.app (A.term (n + 1)).obj)) ≪≫ A.transitionIso n

/-- The forward map of `CategoryTheory.TowerSystem.pullbackPushforwardIso`. -/
theorem pullbackPushforwardIso_hom (A : TowerSystem P T) (n : ℕ) :
    (pullbackPushforwardIso adj hR ρ A n).hom =
      (ρ n).inv.app _ ≫ (T n).map ((adj (n + 1)).counit.app (A.term (n + 1)).obj) ≫
        (A.transitionIso n).hom :=
  rfl

/-- A family of maps of terms is compatible with the transition isomorphisms exactly when it is
compatible with the identifications `L n (R (n + 1) F_{n + 1}) ≅ F_n`. -/
theorem pullbackPushforwardIso_comm_iff {A A' : TowerSystem P T}
    (a : ∀ n, (A.term n).obj ⟶ (A'.term n).obj) (n : ℕ) :
    (T n).map (a (n + 1)) ≫ (A'.transitionIso n).hom = (A.transitionIso n).hom ≫ a n ↔
      (L n).map ((R (n + 1)).map (a (n + 1))) ≫ (pullbackPushforwardIso adj hR ρ A' n).hom =
        (pullbackPushforwardIso adj hR ρ A n).hom ≫ a n := by
  have := (hR (n + 1)).full
  have := (hR (n + 1)).faithful
  rw [pullbackPushforwardIso_hom, pullbackPushforwardIso_hom, NatTrans.naturality_assoc,
    Functor.comp_map, ← Functor.map_comp_assoc, ← Functor.comp_map (R (n + 1)) (L (n + 1)),
    (adj (n + 1)).counit.naturality, Functor.id_map, Functor.map_comp, Category.assoc,
    Category.assoc, Category.assoc, cancel_epi, cancel_epi]

/-- The transition map `R (n + 1) F_{n + 1} ⟶ R n F_n` of the direct image of a system, the
adjoint of `CategoryTheory.TowerSystem.pullbackPushforwardIso`. -/
def pushforwardTransition (A : TowerSystem P T) (n : ℕ) :
    (R (n + 1)).obj (A.term (n + 1)).obj ⟶ (R n).obj (A.term n).obj :=
  (adj n).homEquiv _ _ (pullbackPushforwardIso adj hR ρ A n).hom

/-- The transition map is the adjoint of `CategoryTheory.TowerSystem.pullbackPushforwardIso`. -/
theorem pushforwardTransition_eq (A : TowerSystem P T) (n : ℕ) :
    pushforwardTransition adj hR ρ A n =
      (adj n).homEquiv _ _ (pullbackPushforwardIso adj hR ρ A n).hom :=
  rfl

/-- A family of maps of terms is a morphism of systems exactly when its direct images commute with
the transition maps. -/
theorem pushforwardTransition_comp_iff {A A' : TowerSystem P T}
    (a : ∀ n, (A.term n).obj ⟶ (A'.term n).obj) (n : ℕ) :
    pushforwardTransition adj hR ρ A n ≫ (R n).map (a n) =
        (R (n + 1)).map (a (n + 1)) ≫ pushforwardTransition adj hR ρ A' n ↔
      (T n).map (a (n + 1)) ≫ (A'.transitionIso n).hom = (A.transitionIso n).hom ≫ a n := by
  rw [pullbackPushforwardIso_comm_iff adj hR ρ a n, pushforwardTransition_eq,
    pushforwardTransition_eq, ← Adjunction.homEquiv_naturality_right,
    ← Adjunction.homEquiv_naturality_left, Equiv.apply_eq_iff_eq, eq_comm]

/-- The direct image of a system, the inverse system `(R n F_n)_n`. -/
def pushforwardSystem (A : TowerSystem P T) : ℕᵒᵖ ⥤ D :=
  Functor.ofOpSequence (X := fun n => (R n).obj (A.term n).obj)
    (pushforwardTransition adj hR ρ A)

/-- The terms of the direct image of a system. -/
@[simp]
theorem pushforwardSystem_obj (A : TowerSystem P T) (n : ℕᵒᵖ) :
    (pushforwardSystem adj hR ρ A).obj n = (R n.unop).obj (A.term n.unop).obj :=
  rfl

/-- The transition maps of the direct image of a system. -/
@[simp]
theorem pushforwardSystem_map_succ (A : TowerSystem P T) (n : ℕ) :
    (pushforwardSystem adj hR ρ A).map (homOfLE (Nat.le_add_right n 1)).op =
      pushforwardTransition adj hR ρ A n :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- The morphism of inverse systems induced by a morphism of systems. -/
def pushforwardMap {A A' : TowerSystem P T} (f : A ⟶ A') :
    pushforwardSystem adj hR ρ A ⟶ pushforwardSystem adj hR ρ A' :=
  NatTrans.ofOpSequence (fun n => (R n).map (f.app n)) fun n => by
    rw [pushforwardSystem_map_succ, pushforwardSystem_map_succ]
    exact (pushforwardTransition_comp_iff adj hR ρ (fun n => f.app n) n).2 (f.comm n)

/-- The components of the morphism of inverse systems induced by a morphism of systems. -/
@[simp]
theorem pushforwardMap_app {A A' : TowerSystem P T} (f : A ⟶ A') (n : ℕᵒᵖ) :
    (pushforwardMap adj hR ρ f).app n = (R n.unop).map (f.app n.unop) :=
  rfl

variable (P) in
/-- **The direct image functor** from systems on the tower to inverse systems in `D`. -/
def pushforward : TowerSystem P T ⥤ (ℕᵒᵖ ⥤ D) where
  obj A := pushforwardSystem adj hR ρ A
  map f := pushforwardMap adj hR ρ f
  map_id A := by
    ext n
    simp
  map_comp f g := by
    ext n
    simp

/-- The direct image functor on objects. -/
@[simp]
theorem pushforward_obj (A : TowerSystem P T) :
    (pushforward P adj hR ρ).obj A = pushforwardSystem adj hR ρ A :=
  rfl

/-- The direct image functor on morphisms, componentwise. -/
@[simp]
theorem pushforward_map_app {A A' : TowerSystem P T} (f : A ⟶ A') (n : ℕᵒᵖ) :
    ((pushforward P adj hR ρ).map f).app n = (R n.unop).map (f.app n.unop) :=
  rfl

/-- The component at `n` of a morphism between direct images of systems, as a map between the
direct images of the terms. -/
def pushforwardHomApp {A A' : TowerSystem P T}
    (f : (pushforward P adj hR ρ).obj A ⟶ (pushforward P adj hR ρ).obj A') (n : ℕ) :
    (R n).obj (A.term n).obj ⟶ (R n).obj (A'.term n).obj :=
  f.app (op n)

/-- The components of a morphism between direct images of systems commute with the transition
maps. -/
theorem pushforwardTransition_comp_pushforwardHomApp {A A' : TowerSystem P T}
    (f : (pushforward P adj hR ρ).obj A ⟶ (pushforward P adj hR ρ).obj A') (n : ℕ) :
    pushforwardTransition adj hR ρ A n ≫ pushforwardHomApp adj hR ρ f n =
      pushforwardHomApp adj hR ρ f (n + 1) ≫ pushforwardTransition adj hR ρ A' n := by
  have := f.naturality (homOfLE (Nat.le_add_right n 1)).op
  dsimp only [pushforward_obj] at this
  rwa [pushforwardSystem_map_succ, pushforwardSystem_map_succ] at this

variable (P) in
/-- **The direct image functor is fully faithful**: levelwise this is full faithfulness of the
`R n`, and the compatibility with the transitions is recovered from
`CategoryTheory.TowerSystem.pushforwardTransition_comp_iff`. -/
def fullyFaithfulPushforward : (pushforward P adj hR ρ).FullyFaithful where
  preimage {A A'} f :=
    { app n := (hR n).preimage (pushforwardHomApp adj hR ρ f n)
      comm n := by
        refine (pushforwardTransition_comp_iff adj hR ρ
          (fun n => (hR n).preimage (pushforwardHomApp adj hR ρ f n)) n).1 ?_
        rw [(hR n).map_preimage, (hR (n + 1)).map_preimage]
        exact pushforwardTransition_comp_pushforwardHomApp adj hR ρ f n }
  map_preimage f := by
    ext n
    exact (hR n.unop).map_preimage _
  preimage_map f := hom_ext fun n => (hR n).preimage_map _

/-- The transition maps of the direct image, as the maps of the functor `ℕᵒᵖ ⥤ D`. -/
theorem pushforward_obj_map_le_succ (A : TowerSystem P T) (n : ℕ) :
    ((pushforward P adj hR ρ).obj A).map (homOfLE (Nat.le_succ n)).op =
      (adj n).homEquiv _ _ (pullbackPushforwardIso adj hR ρ A n).hom :=
  pushforwardSystem_map_succ adj hR ρ A n

/-- The terms of the direct image, as the values of the functor `ℕᵒᵖ ⥤ D`. -/
theorem pushforward_obj_obj (A : TowerSystem P T) (n : ℕ) :
    ((pushforward P adj hR ρ).obj A).obj (op n) = (R n).obj (A.term n).obj :=
  rfl

/-- The transition map of the direct image of a system is the unit followed by the direct image of
`CategoryTheory.TowerSystem.pullbackPushforwardIso`. -/
theorem pushforward_obj_map_le_succ_eq_unit_comp (A : TowerSystem P T) (n : ℕ) :
    ((pushforward P adj hR ρ).obj A).map (homOfLE (Nat.le_succ n)).op =
      @CategoryStruct.comp D _ ((R (n + 1)).obj (A.term (n + 1)).obj)
        ((R n).obj ((L n).obj ((R (n + 1)).obj (A.term (n + 1)).obj)))
        ((R n).obj (A.term n).obj) ((adj n).unit.app _)
        ((R n).map (pullbackPushforwardIso adj hR ρ A n).hom) := by
  rw [pushforward_obj_map_le_succ, Adjunction.homEquiv_unit]

/-- The quotient condition for the direct image of a system: if `p` followed by an isomorphism
`q` onto `R n (L n (R (n + 1) F_{n + 1}))` is the unit, then `p` is the transition map up to an
isomorphism of its target. -/
theorem exists_iso_comp_eq_pushforward_obj_map (A : TowerSystem P T) (n : ℕ) {K : D}
    (p : ((pushforward P adj hR ρ).obj A).obj (op (n + 1)) ⟶ K)
    (q : K ≅ (R n).obj ((L n).obj (((pushforward P adj hR ρ).obj A).obj (op (n + 1)))))
    (hpq : p ≫ q.hom = (adj n).unit.app (((pushforward P adj hR ρ).obj A).obj (op (n + 1)))) :
    ∃ e : K ≅ ((pushforward P adj hR ρ).obj A).obj (op n),
      p ≫ e.hom = ((pushforward P adj hR ρ).obj A).map (homOfLE (Nat.le_succ n)).op := by
  refine ⟨q ≪≫ (R n).mapIso (pullbackPushforwardIso adj hR ρ A n), ?_⟩
  refine ((Category.assoc p q.hom ((R n).map (pullbackPushforwardIso adj hR ρ A n).hom)).symm.trans
    ?_).trans (pushforward_obj_map_le_succ adj hR ρ A n).symm
  rw [hpq]
  exact ((adj n).homEquiv_unit _ _ _).symm

/-- The quotient condition for the direct image of a system, from a family of quotient maps: if
for every object `M` of `D` a map `p M : M ⟶ K M` followed by an isomorphism
`q M : K M ≅ R n (L n M)` is the unit, then `p` at the term `n + 1` is the transition map up to an
isomorphism of its target. -/
theorem exists_iso_comp_eq_pushforward_obj_map_of_forall (A : TowerSystem P T) (n : ℕ)
    (K : D → D) (p : ∀ M, M ⟶ K M) (q : ∀ M, K M ≅ (R n).obj ((L n).obj M))
    (hpq : ∀ M, p M ≫ (q M).hom = (adj n).unit.app M) :
    ∃ e : K (((pushforward P adj hR ρ).obj A).obj (op (n + 1))) ≅
        ((pushforward P adj hR ρ).obj A).obj (op n),
      p _ ≫ e.hom = ((pushforward P adj hR ρ).obj A).map (homOfLE (Nat.le_succ n)).op :=
  exists_iso_comp_eq_pushforward_obj_map adj hR ρ A n (p _) (q _) (hpq _)

/-- The identification `L n (R (n + 1) (L (n + 1) M)) ≅ L n M` of a restricted object inverts
`L n` of the unit. -/
theorem map_unit_comp_pullbackPushforwardIso_restriction_hom (Q : ObjectProperty D)
    (hL : ∀ n M, Q M → P n ((L n).obj M)) (M : Q.FullSubcategory) (n : ℕ) :
    (L n).map ((adj (n + 1)).unit.app M.obj) ≫
        (pullbackPushforwardIso adj hR ρ ((restriction Q L ρ hL).obj M) n).hom = 𝟙 _ := by
  rw [pullbackPushforwardIso_hom, restriction_obj_transitionIso, Iso.app_hom]
  dsimp only [restriction_obj_term_obj, Functor.comp_obj, Functor.id_obj]
  rw [NatTrans.naturality_assoc, Functor.comp_map, ← Functor.map_comp_assoc,
    Adjunction.left_triangle_components, Functor.map_id, Category.id_comp, Iso.inv_hom_id_app]

/-- The transition maps of the direct image of a restricted object are compatible with the units
of the adjunctions. -/
theorem unit_comp_pushforwardTransition_restriction (Q : ObjectProperty D)
    (hL : ∀ n M, Q M → P n ((L n).obj M)) (M : Q.FullSubcategory) (n : ℕ) :
    (adj (n + 1)).unit.app M.obj ≫
        pushforwardTransition adj hR ρ ((restriction Q L ρ hL).obj M) n =
      (adj n).unit.app M.obj := by
  rw [pushforwardTransition_eq]
  refine ((adj n).homEquiv_naturality_left _ _).symm.trans ?_
  rw [map_unit_comp_pullbackPushforwardIso_restriction_hom]
  exact (adj n).homEquiv_id _

/-- The transition maps of the direct image of a restricted object are compatible with the units
of the adjunctions, in terms of the inverse system. -/
theorem unit_comp_pushforward_obj_map_restriction (Q : ObjectProperty D)
    (hL : ∀ n M, Q M → P n ((L n).obj M)) (M : Q.FullSubcategory) (n : ℕ) :
    (adj (n + 1)).unit.app M.obj ≫
        ((pushforward P adj hR ρ).obj ((restriction Q L ρ hL).obj M)).map
          (homOfLE (Nat.le_succ n)).op =
      (adj n).unit.app M.obj := by
  rw [pushforward_obj_map_le_succ, ← pushforwardTransition_eq]
  exact unit_comp_pushforwardTransition_restriction adj hR ρ Q hL M n

/-- A tower of quotients `p n : M ⟶ K n` of an object `M` of `D`, with transition maps
`d n : K (n + 1) ⟶ K n`, identified with the `R n (L n M)` through the units of the
adjunctions: the `p n` are epimorphisms compatible with the `d n`, and the isomorphisms
`c n : K n ≅ R n (L n M)` carry them to the units. -/
structure IsUnitQuotient (M : D) {K : ℕ → D} (d : ∀ n, K (n + 1) ⟶ K n)
    (c : ∀ n, K n ≅ (R n).obj ((L n).obj M)) (p : ∀ n, M ⟶ K n) : Prop where
  /-- The quotient maps are epimorphisms. -/
  epi (n : ℕ) : Epi (p n)
  /-- The isomorphisms carry the quotient maps to the units. -/
  comp_hom (n : ℕ) : p n ≫ (c n).hom = (adj n).unit.app M
  /-- The quotient maps are compatible with the transition maps. -/
  comp_transition (n : ℕ) : p (n + 1) ≫ d n = p n

/-- The unit followed by the inverse of the identification is the quotient map. -/
private theorem IsUnitQuotient.unit_comp_inv {M : D} {K : ℕ → D} {d : ∀ n, K (n + 1) ⟶ K n}
    {c : ∀ n, K n ≅ (R n).obj ((L n).obj M)} {p : ∀ n, M ⟶ K n}
    (h : IsUnitQuotient adj M d c p) (n : ℕ) : (adj n).unit.app M ≫ (c n).inv = p n :=
  (Iso.comp_inv_eq (c n)).2 (h.comp_hom n).symm

/-- The units of a tower of quotients are epimorphisms. -/
private theorem IsUnitQuotient.epi_unit {M : D} {K : ℕ → D} {d : ∀ n, K (n + 1) ⟶ K n}
    {c : ∀ n, K n ≅ (R n).obj ((L n).obj M)} {p : ∀ n, M ⟶ K n}
    (h : IsUnitQuotient adj M d c p) (n : ℕ) : Epi ((adj n).unit.app M) := by
  have := h.epi n
  rw [← h.comp_hom n]
  infer_instance

/-- The direct image of a restricted object `M` is compared with an inverse system
`(K n, d n)` of quotients of `M` identified with the `R n (L n M)` through the units: the
inverses of the identifications commute with the transition maps. -/
theorem pushforward_restriction_map_comp_inv_of_unit (Q : ObjectProperty D)
    (hL : ∀ n M, Q M → P n ((L n).obj M)) (M : Q.FullSubcategory) {K : ℕ → D}
    {d : ∀ n, K (n + 1) ⟶ K n} {c : ∀ n, K n ≅ (R n).obj ((L n).obj M.obj)}
    {p : ∀ n, M.obj ⟶ K n} (h : IsUnitQuotient adj M.obj d c p) (n : ℕ) :
    ((pushforward P adj hR ρ).obj ((restriction Q L ρ hL).obj M)).map
        (homOfLE (n.le_add_right 1)).op ≫ (c n).inv =
      (c (n + 1)).inv ≫ d n := by
  have hu := IsUnitQuotient.unit_comp_inv adj h
  have := IsUnitQuotient.epi_unit adj h (n + 1)
  have h1 : (adj (n + 1)).unit.app M.obj ≫
      (((pushforward P adj hR ρ).obj ((restriction Q L ρ hL).obj M)).map
        (homOfLE (n.le_add_right 1)).op ≫ (c n).inv) = p n :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (c n).inv)
      (unit_comp_pushforward_obj_map_restriction adj hR ρ Q hL M n)).trans (hu n))
  have h2 : (adj (n + 1)).unit.app M.obj ≫ ((c (n + 1)).inv ≫ d n) = p n :=
    (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ d n) (hu (n + 1))).trans
      (h.comp_transition n))
  exact (cancel_epi ((adj (n + 1)).unit.app M.obj)).1 (h1.trans h2.symm)

/-- The comparison morphism of the direct image of a restricted object `M` with an inverse system
`(K n, d n)` of quotients of `M` identified with the `R n (L n M)` through the units. -/
def pushforwardRestrictionHomOfUnit (Q : ObjectProperty D)
    (hL : ∀ n M, Q M → P n ((L n).obj M)) (M : Q.FullSubcategory) {K : ℕ → D}
    {d : ∀ n, K (n + 1) ⟶ K n} {c : ∀ n, K n ≅ (R n).obj ((L n).obj M.obj)}
    {p : ∀ n, M.obj ⟶ K n} (h : IsUnitQuotient adj M.obj d c p) :
    (pushforward P adj hR ρ).obj ((restriction Q L ρ hL).obj M) ⟶ Functor.ofOpSequence d :=
  NatTrans.ofOpSequence (fun n => (c n).inv) fun n => by
    rw [Functor.ofOpSequence_map_homOfLE_succ]
    exact pushforward_restriction_map_comp_inv_of_unit adj hR ρ Q hL M h n

/-- The comparison morphism of `pushforwardRestrictionHomOfUnit` is an isomorphism. -/
theorem isIso_pushforwardRestrictionHomOfUnit (Q : ObjectProperty D)
    (hL : ∀ n M, Q M → P n ((L n).obj M)) (M : Q.FullSubcategory) {K : ℕ → D}
    {d : ∀ n, K (n + 1) ⟶ K n} {c : ∀ n, K n ≅ (R n).obj ((L n).obj M.obj)}
    {p : ∀ n, M.obj ⟶ K n} (h : IsUnitQuotient adj M.obj d c p) :
    IsIso (pushforwardRestrictionHomOfUnit adj hR ρ Q hL M h) := by
  have : ∀ X : ℕᵒᵖ, IsIso ((pushforwardRestrictionHomOfUnit adj hR ρ Q hL M h).app X) :=
    fun X => Iso.isIso_inv (c X.unop)
  exact NatIso.isIso_of_isIso_app _

/-- The isomorphism of the direct image of a restricted object `M` with an inverse system
`(K n, d n)` of quotients of `M` identified with the `R n (L n M)` through the units. -/
def pushforwardRestrictionIsoOfUnit (Q : ObjectProperty D)
    (hL : ∀ n M, Q M → P n ((L n).obj M)) (M : Q.FullSubcategory) {K : ℕ → D}
    {d : ∀ n, K (n + 1) ⟶ K n} {c : ∀ n, K n ≅ (R n).obj ((L n).obj M.obj)}
    {p : ∀ n, M.obj ⟶ K n} (h : IsUnitQuotient adj M.obj d c p) :
    (pushforward P adj hR ρ).obj ((restriction Q L ρ hL).obj M) ≅ Functor.ofOpSequence d :=
  have := isIso_pushforwardRestrictionHomOfUnit adj hR ρ Q hL M h
  asIso (pushforwardRestrictionHomOfUnit adj hR ρ Q hL M h)

/-- The components of `pushforwardRestrictionIsoOfUnit` are the inverses of the
identifications. -/
theorem pushforwardRestrictionIsoOfUnit_hom_app (Q : ObjectProperty D)
    (hL : ∀ n M, Q M → P n ((L n).obj M)) (M : Q.FullSubcategory) {K : ℕ → D}
    {d : ∀ n, K (n + 1) ⟶ K n} {c : ∀ n, K n ≅ (R n).obj ((L n).obj M.obj)}
    {p : ∀ n, M.obj ⟶ K n} (h : IsUnitQuotient adj M.obj d c p) (n : ℕ) :
    (pushforwardRestrictionIsoOfUnit adj hR ρ Q hL M h).hom.app (op n) = (c n).inv :=
  rfl

/-- A functor `G` to inverse systems in `D` whose terms are quotients `p M n : M ⟶ G M n`
identified with the `R n (L n M)` through the units, naturally in `M`. -/
structure IsUnitQuotientFunctor (Q : ObjectProperty D) (G : Q.FullSubcategory ⥤ (ℕᵒᵖ ⥤ D))
    (c : ∀ M n, (G.obj M).obj (op n) ≅ (R n).obj ((L n).obj M.obj))
    (p : ∀ M n, M.obj ⟶ (G.obj M).obj (op n)) : Prop where
  /-- Each `G M` is a tower of quotients of `M` identified with the `R n (L n M)`. -/
  isUnitQuotient (M : Q.FullSubcategory) :
    IsUnitQuotient adj M.obj (K := fun n => (G.obj M).obj (op n))
      (fun n => (G.obj M).map (homOfLE (Nat.le_succ n)).op) (c M) (p M)
  /-- The quotient maps are natural in `M`. -/
  naturality {M M' : Q.FullSubcategory} (f : M ⟶ M') (n : ℕ) :
    p M n ≫ (G.map f).app (op n) = f.hom ≫ p M' n

/-- The identifications of `pushforwardRestrictionIsoOfUnit` are natural in the object. -/
theorem map_map_comp_inv_of_isUnitQuotientFunctor (Q : ObjectProperty D)
    {G : Q.FullSubcategory ⥤ (ℕᵒᵖ ⥤ D)}
    {c : ∀ M n, (G.obj M).obj (op n) ≅ (R n).obj ((L n).obj M.obj)}
    {p : ∀ M n, M.obj ⟶ (G.obj M).obj (op n)} (h : IsUnitQuotientFunctor adj Q G c p)
    {M M' : Q.FullSubcategory} (f : M ⟶ M') (n : ℕ) :
    (R n).map ((L n).map f.hom) ≫ (c M' n).inv = (c M n).inv ≫ (G.map f).app (op n) := by
  have hu := fun N => IsUnitQuotient.unit_comp_inv adj (h.isUnitQuotient N) n
  have := IsUnitQuotient.epi_unit adj (h.isUnitQuotient M) n
  refine (cancel_epi ((adj n).unit.app M.obj)).1 ?_
  have hnat := (adj n).unit.naturality f.hom
  dsimp only [Functor.id_obj, Functor.id_map, Functor.comp_obj, Functor.comp_map] at hnat
  rw [← Category.assoc, ← hnat, Category.assoc, hu M', ← Category.assoc, hu M, h.naturality]

/-- **The direct image of the restriction of an object is a given functor `G`** to inverse
systems whose terms are quotients identified with the `R n (L n M)` through the units, naturally
in `M`. -/
def restrictionCompPushforwardIsoOfUnit (Q : ObjectProperty D)
    (hL : ∀ n M, Q M → P n ((L n).obj M)) {G : Q.FullSubcategory ⥤ (ℕᵒᵖ ⥤ D)}
    {c : ∀ M n, (G.obj M).obj (op n) ≅ (R n).obj ((L n).obj M.obj)}
    {p : ∀ M n, M.obj ⟶ (G.obj M).obj (op n)} (h : IsUnitQuotientFunctor adj Q G c p) :
    restriction Q L ρ hL ⋙ pushforward P adj hR ρ ≅ G :=
  NatIso.ofComponents (fun M => pushforwardRestrictionIsoOfUnit adj hR ρ Q hL M
      (h.isUnitQuotient M) ≪≫ Functor.ofOpSequenceMapIso (G.obj M)) fun f => by
    ext ⟨n⟩
    simp only [Functor.comp_map, NatTrans.comp_app, Iso.trans_hom,
      pushforwardRestrictionIsoOfUnit_hom_app, Functor.ofOpSequenceMapIso_hom_app,
      pushforward_map_app, restriction_map_app]
    exact (congrArg (_ ≫ ·) (Category.comp_id _)).trans
      ((map_map_comp_inv_of_isUnitQuotientFunctor adj Q h f n).trans
        (congrArg (· ≫ _) (Category.comp_id _)).symm)

end Pushforward

end TowerSystem

end CategoryTheory


namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison `f^* ∘ g^* ≅ h^*` of inverse images along a factorization `f ≫ g = h`. -/
def modulePullbackCompIsoOfEq {X Y W : AlgebraicSpaces B S hS} (f : X ⟶ Y) (g : Y ⟶ W)
    {h : X ⟶ W} (w : f ≫ g = h) :
    modulePullback B S hS g ⋙ modulePullback B S hS f ≅ modulePullback B S hS h :=
  modulePullbackCompIso B S hS f g ≪≫ eqToIso (by rw [w])

/-- The ideal cutting out a closed subspace kills every direct image from it: `𝓘 · i_* G = 0`. -/
theorem kerIdealSmul_modulePushforward_eq_bot {Y W : AlgebraicSpaces B S hS} (i : W ⟶ Y)
    (hi : IsClosedImmersion B S hS i.hom) (G : Modules.{u, u} B S hS W.1 W.2) :
    kerIdealSmul B S hS i ((modulePushforward B S hS i).obj G) =
      (⊥ : SheafOfModules.Submodule ((modulePushforward B S hS i).obj G)) := by
  have hiso : IsIso ((modulePullbackAdjunction B S hS i).unit.app
      ((modulePushforward B S hS i).obj G)) :=
    (essImage_modulePushforward_iff_isIso_modulePullbackAdjunction_unit B S hS i hi _).1
      ((modulePushforward B S hS i).obj_mem_essImage G)
  refine eq_bot_iff.2 fun U x hx => ?_
  have hk : ((modulePullbackAdjunction B S hS i).unit.app
      ((modulePushforward B S hS i).obj G)).val.app U x = 0 :=
    idealSmul_kerIdeal_le_ker_modulePullbackAdjunction_unit B S hS i _ U hx
  have h1 := congrArg (fun k => k.val.app U x)
    (IsIso.hom_inv_id ((modulePullbackAdjunction B S hS i).unit.app
      ((modulePushforward B S hS i).obj G)))
  have hx0 : (inv ((modulePullbackAdjunction B S hS i).unit.app
      ((modulePushforward B S hS i).obj G))).val.app U
        (((modulePullbackAdjunction B S hS i).unit.app
          ((modulePushforward B S hS i).obj G)).val.app U x) = x := h1
  rw [hk, map_zero] at hx0
  rw [← hx0]
  exact zero_mem _

/-- The isomorphism `M / P ≅ M / Q` of quotients by equal submodules. -/
def submoduleCokernelIsoOfEq {Y : AlgebraicSpaces B S hS} {M : Modules.{u, u} B S hS Y.1 Y.2}
    {P Q : M.Submodule} (h : P = Q) : cokernel P.ι ≅ cokernel Q.ι :=
  eqToIso (by rw [h])

/-- The isomorphism of quotients by equal submodules is compatible with the projections. -/
@[reassoc]
theorem cokernel_π_comp_submoduleCokernelIsoOfEq_hom {Y : AlgebraicSpaces B S hS}
    {M : Modules.{u, u} B S hS Y.1 Y.2} {P Q : M.Submodule} (h : P = Q) :
    cokernel.π P.ι ≫ (submoduleCokernelIsoOfEq B S hS h).hom = cokernel.π Q.ι := by
  subst h
  simp [submoduleCokernelIsoOfEq]

/-- **The category of coherent systems on a tower of spaces** `Z 0 → Z 1 → ⋯` with transition
morphisms `t n : Z n ⟶ Z (n + 1)`: systems `(F_n, φ_n)` of coherent `𝒪_{Z n}`-modules `F_n`
with isomorphisms `φ_n : t n ^* F_{n + 1} ≅ F_n`. -/
abbrev ThickeningCoherentSystem (Z : ℕ → AlgebraicSpaces B S hS) (t : ∀ n, Z n ⟶ Z (n + 1)) :=
  TowerSystem (C := fun n => Modules.{u, u} B S hS (Z n).1 (Z n).2)
    (fun n => isCoherent.{u, u} B S hS (Z n).1 (Z n).2) (fun n => modulePullback B S hS (t n))

section Thickening

variable {X : AlgebraicSpaces B S hS} {Z : ℕ → AlgebraicSpaces B S hS} (ι : ∀ n, Z n ⟶ X)
  (t : ∀ n, Z n ⟶ Z (n + 1)) (hι : ∀ n, t n ≫ ι (n + 1) = ι n)

/-- **Restriction to the thickenings**, `F ↦ (ι n ^* F)_n`. -/
abbrev thickeningRestriction
    (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :
    CoherentModules.{u, u} B S hS X.1 X.2 ⥤ ThickeningCoherentSystem B S hS Z t :=
  TowerSystem.restriction (isCoherent.{u, u} B S hS X.1 X.2) (fun n => modulePullback B S hS (ι n))
    (fun n => modulePullbackCompIsoOfEq B S hS (t n) (ι (n + 1)) (hι n))
    (fun n M hM => haveI : Fact _ := ⟨hZ n⟩
      isCoherent_modulePullback B S hS (ι n) M hM)

/-- Restriction to the thickenings is the restriction of objects to the tower along the
`ι n ^*`. -/
theorem thickeningRestriction_eq
    (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :
    thickeningRestriction B S hS ι t hι hZ =
      TowerSystem.restriction (isCoherent.{u, u} B S hS X.1 X.2)
        (fun n => modulePullback B S hS (ι n))
        (fun n => modulePullbackCompIsoOfEq B S hS (t n) (ι (n + 1)) (hι n))
        (fun n M hM => haveI : Fact _ := ⟨hZ n⟩
          isCoherent_modulePullback B S hS (ι n) M hM) :=
  rfl

variable (hi : ∀ n, IsClosedImmersion B S hS (ι n).hom)

variable {𝓘 : (SheafOfModules.unit
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))).Submodule}

/-- The isomorphism `M / ker(ι n ♯) · M ≅ (ι n)_* ι n ^* M` of the closed immersion `ι n`,
transported along `ker(ι n ♯) · M = 𝓘 ^ (n + 1) M`, is induced by the unit. -/
theorem cokernel_π_comp_kerIdealSmulQuotientUnitIso_of_eq
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (n : ℕ) (M : Modules.{u, u} B S hS X.1 X.2) :
    cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι ≫
        (submoduleCokernelIsoOfEq B S hS (hker n M).symm ≪≫
        kerIdealSmulQuotientUnitIso B S hS (ι n) (hi n) M).hom =
      (modulePullbackAdjunction B S hS (ι n)).unit.app M := by
  rw [Iso.trans_hom, cokernel_π_comp_submoduleCokernelIsoOfEq_hom_assoc,
    cokernel_π_comp_kerIdealSmulQuotientUnitIso_hom]

include hi in
/-- The isomorphism `M / 𝓘 ^ (n + 1) M ≅ (ι n)_* N` built from
`AlgebraicGeometry.Space.kerIdealSmulQuotientUnitIso` and an isomorphism `e : ι n ^* M ≅ N` turns
the quotient projection into the adjoint of `e`. -/
theorem cokernel_π_comp_kerIdealSmulQuotientUnitIso_trans_mapIso_hom
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (n : ℕ) (M : Modules.{u, u} B S hS X.1 X.2) (N : Modules.{u, u} B S hS (Z n).1 (Z n).2)
    (e : (modulePullback B S hS (ι n)).obj M ≅ N) :
      cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι ≫
        ((submoduleCokernelIsoOfEq B S hS (hker n M).symm ≪≫
        kerIdealSmulQuotientUnitIso B S hS (ι n) (hi n) M) ≪≫
      (modulePushforward B S hS (ι n)).mapIso e).hom =
        @CategoryStruct.comp (Modules.{u, u} B S hS X.1 X.2) _ M
          ((modulePushforward B S hS (ι n)).obj ((modulePullback B S hS (ι n)).obj M))
          ((modulePushforward B S hS (ι n)).obj N)
          ((modulePullbackAdjunction B S hS (ι n)).unit.app M)
          ((modulePushforward B S hS (ι n)).map e.hom) := by
    rw [Iso.trans_hom, ← Category.assoc,
      cokernel_π_comp_kerIdealSmulQuotientUnitIso_of_eq B S hS ι hi hker, Functor.mapIso_hom]

include hi in
/-- The quotient condition of a coherent adic system for a transition map adjoint to an
isomorphism `ι n ^* M ≅ N`, with the quotient written as a cokernel. -/
theorem exists_cokernel_iso_comp_eq_unit_comp
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (n : ℕ) (M : Modules.{u, u} B S hS X.1 X.2) (N : Modules.{u, u} B S hS (Z n).1 (Z n).2)
    (e : (modulePullback B S hS (ι n)).obj M ≅ N) :
    ∃ e' : cokernel (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι ≅
        (modulePushforward B S hS (ι n)).obj N,
      cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι ≫ e'.hom =
        @CategoryStruct.comp (Modules.{u, u} B S hS X.1 X.2) _ M
          ((modulePushforward B S hS (ι n)).obj ((modulePullback B S hS (ι n)).obj M))
          ((modulePushforward B S hS (ι n)).obj N)
          ((modulePullbackAdjunction B S hS (ι n)).unit.app M)
          ((modulePushforward B S hS (ι n)).map e.hom) :=
  ⟨_, cokernel_π_comp_kerIdealSmulQuotientUnitIso_trans_mapIso_hom B S hS ι hi hker n M N e⟩

include hi in
/-- The quotient condition of a coherent adic system for a transition map adjoint to an
isomorphism `ι n ^* M ≅ N`. -/
theorem exists_idealPowerQuotient_iso_comp_eq_unit_comp
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (n : ℕ) (M : Modules.{u, u} B S hS X.1 X.2) (N : Modules.{u, u} B S hS (Z n).1 (Z n).2)
    (e : (modulePullback B S hS (ι n)).obj M ≅ N) :
    ∃ e' : idealPowerQuotient B S hS X.1 X.2 𝓘 (n + 1) M ≅ (modulePushforward B S hS (ι n)).obj N,
      cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι ≫ e'.hom =
        @CategoryStruct.comp (Modules.{u, u} B S hS X.1 X.2) _ M
          ((modulePushforward B S hS (ι n)).obj ((modulePullback B S hS (ι n)).obj M))
          ((modulePushforward B S hS (ι n)).obj N)
          ((modulePullbackAdjunction B S hS (ι n)).unit.app M)
          ((modulePushforward B S hS (ι n)).map e.hom) :=
  exists_cokernel_iso_comp_eq_unit_comp B S hS ι hi hker n M N e

/-- **The direct image of a system on the thickenings**, `(F_n, φ_n) ↦ ((ι n)_* F_n)_n`, as an
inverse system of `𝒪_X`-modules: the transition map `(ι (n + 1))_* F_{n + 1} ⟶ (ι n)_* F_n` is the
adjoint of the identification `ι n ^* (ι (n + 1))_* F_{n + 1} ≅ F_n`. -/
abbrev thickeningPushforwardSystems :
    ThickeningCoherentSystem B S hS Z t ⥤ (ℕᵒᵖ ⥤ Modules.{u, u} B S hS X.1 X.2) :=
  (TowerSystem.pushforward (C := fun n => Modules.{u, u} B S hS (Z n).1 (Z n).2)
      (T := fun n => modulePullback B S hS (t n))
      (fun n => isCoherent.{u, u} B S hS (Z n).1 (Z n).2)
      (fun n => modulePullbackAdjunction B S hS (ι n))
      (fun n => fullyFaithfulModulePushforward B S hS (ι n) (hi n))
      (fun n => modulePullbackCompIsoOfEq B S hS (t n) (ι (n + 1)) (hι n)))

/-- **The direct image functor from systems on the thickenings to inverse systems of
`𝒪_X`-modules is fully faithful.** -/
def thickeningPushforwardSystemsFullyFaithful :
    (thickeningPushforwardSystems B S hS ι t hι hi).FullyFaithful :=
  TowerSystem.fullyFaithfulPushforward _ _ _ _

/-- The terms of the direct image of a coherent system on the thickenings are coherent. -/
theorem isCoherent_thickeningPushforwardSystems_obj_obj
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (A : ThickeningCoherentSystem B S hS Z t) (n : ℕ) :
    IsCoherent B S hS X.1 X.2
      (((thickeningPushforwardSystems B S hS ι t hι hi).obj A).obj (op n)) :=
  isCoherent_modulePushforward_of_isClosedImmersion B S hS hX (ι n) (hi n) _ (A.term n).property

/-- The term at `n` of the direct image of a system on the thickenings is annihilated by
`𝓘 ^ (n + 1)`. -/
theorem idealPowerMultiple_thickeningPushforwardSystems_obj_obj_eq_bot
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (A : ThickeningCoherentSystem B S hS Z t) (n : ℕ) :
    idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1)
      (((thickeningPushforwardSystems B S hS ι t hι hi).obj A).obj (op n)) = ⊥ := by
  rw [← hker n]
  exact kerIdealSmul_modulePushforward_eq_bot B S hS (ι n) (hi n) _

include hi in
/-- The quotient condition of a coherent adic system for the direct image of a system on the
thickenings: the transition map at `n` is the projection onto the quotient by `𝓘 ^ (n + 1)`, up to
an isomorphism of its target. -/
theorem exists_idealPowerQuotient_iso_thickeningPushforwardSystems
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (A : ThickeningCoherentSystem B S hS Z t) (n : ℕ) :
    ∃ e : idealPowerQuotient B S hS X.1 X.2 𝓘 (n + 1)
        (((thickeningPushforwardSystems B S hS ι t hι hi).obj A).obj (op (n + 1))) ≅
        ((thickeningPushforwardSystems B S hS ι t hι hi).obj A).obj (op n),
      cokernel.π ((idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1)
        (((thickeningPushforwardSystems B S hS ι t hι hi).obj A).obj (op (n + 1)))).ι) ≫ e.hom =
        ((thickeningPushforwardSystems B S hS ι t hι hi).obj A).map (homOfLE (Nat.le_succ n)).op :=
  TowerSystem.exists_iso_comp_eq_pushforward_obj_map _ _ _ A n _ _
    (cokernel_π_comp_kerIdealSmulQuotientUnitIso_of_eq B S hS ι hi hker n _)

include hi in
/-- **The direct image of a coherent system on the thickenings is a coherent `𝓘`-adic system.** -/
theorem isCoherentAdicSystem_thickeningPushforwardSystems
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (A : ThickeningCoherentSystem B S hS Z t) :
    IsCoherentAdicSystem B S hS X.1 X.2 𝓘 ((thickeningPushforwardSystems B S hS ι t hι hi).obj A) :=
  ⟨isCoherent_thickeningPushforwardSystems_obj_obj B S hS ι t hι hi hX A,
    idealPowerMultiple_thickeningPushforwardSystems_obj_obj_eq_bot B S hS ι t hι hi hker A,
    exists_idealPowerQuotient_iso_thickeningPushforwardSystems B S hS ι t hι hi hker A⟩

/-- **The direct image functor `Ψ` from coherent systems on the thickenings to `Coh(X, 𝓘)`**,
`(F_n, φ_n) ↦ ((ι n)_* F_n)_n`, for a tower of closed immersions `ι n` whose ideals are the powers
`𝓘 ^ (n + 1)`. -/
def thickeningPushforward
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M) :
    ThickeningCoherentSystem B S hS Z t ⥤ CoherentAdicSystems B S hS X.1 X.2 𝓘 :=
  ObjectProperty.lift _ (thickeningPushforwardSystems B S hS ι t hι hi)
    (isCoherentAdicSystem_thickeningPushforwardSystems B S hS ι t hι hi hX hker)

/-- **The direct image functor `Ψ` to `Coh(X, 𝓘)` is fully faithful.** -/
def thickeningPushforwardFullyFaithful
    (hX : HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M) :
    (thickeningPushforward B S hS ι t hι hi hX hker).FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := ObjectProperty.ι _)
    ((thickeningPushforwardSystemsFullyFaithful B S hS ι t hι hi).ofIso
      (ObjectProperty.liftCompιIso _ _ _).symm)


/-- The inverse of the identification `M / 𝓘 ^ (n + 1) M ≅ (ι n)_* ι n ^* M` carries the unit to
the quotient projection. -/
@[reassoc]
theorem unit_comp_kerIdealSmulQuotientUnitIso_inv_of_eq
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (n : ℕ) (M : Modules.{u, u} B S hS X.1 X.2) :
    (modulePullbackAdjunction B S hS (ι n)).unit.app M ≫
        (submoduleCokernelIsoOfEq B S hS (hker n M).symm ≪≫
          kerIdealSmulQuotientUnitIso B S hS (ι n) (hi n) M).inv =
      cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι := by
  rw [Iso.comp_inv_eq, cokernel_π_comp_kerIdealSmulQuotientUnitIso_of_eq B S hS ι hi hker n M]


/-- The units of the closed immersions `ι n` are compatible with the transition maps of the
direct image of the restriction of a coherent module to the thickenings. -/
theorem unit_comp_thickeningPushforwardSystems_obj_map
    (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (F : CoherentModules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    (modulePullbackAdjunction B S hS (ι (n + 1))).unit.app F.obj ≫
        ((thickeningPushforwardSystems B S hS ι t hι hi).obj
          ((thickeningRestriction B S hS ι t hι hZ).obj F)).map (homOfLE (Nat.le_succ n)).op =
      (modulePullbackAdjunction B S hS (ι n)).unit.app F.obj :=
  TowerSystem.unit_comp_pushforward_obj_map_restriction _ _ _ _ _ F n

include hi in
/-- The identifications `(ι n)_* ι n ^* F ≅ F / 𝓘 ^ (n + 1) F` are natural in `F`. -/
theorem modulePushforward_map_modulePullback_map_comp_inv
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    {M N : Modules.{u, u} B S hS X.1 X.2} (f : M ⟶ N) (n : ℕ) :
    (modulePushforward B S hS (ι n)).map ((modulePullback B S hS (ι n)).map f) ≫
        (submoduleCokernelIsoOfEq B S hS (hker n N).symm ≪≫
          kerIdealSmulQuotientUnitIso B S hS (ι n) (hi n) N).inv =
      (submoduleCokernelIsoOfEq B S hS (hker n M).symm ≪≫
          kerIdealSmulQuotientUnitIso B S hS (ι n) (hi n) M).inv ≫
        idealPowerQuotientMapOfHom B S hS X.1 X.2 𝓘 (n + 1) f := by
  have hnat := (modulePullbackAdjunction B S hS (ι n)).unit.naturality f
  simp only [Functor.id_map, Functor.comp_map] at hnat
  refine (Iso.eq_inv_comp _).2 ?_
  refine (cancel_epi (cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι)).1 ?_
  rw [π_comp_idealPowerQuotientMapOfHom, ← Category.assoc,
    cokernel_π_comp_kerIdealSmulQuotientUnitIso_of_eq B S hS ι hi hker n M,
    ← Category.assoc, ← hnat, Category.assoc,
    unit_comp_kerIdealSmulQuotientUnitIso_inv_of_eq B S hS ι hi hker n N]


include hi in
/-- The isomorphism `M / 𝓘 ^ (n + 1) M ≅ (ι n)_* ι n ^* M` for the closed immersion `ι n`, when
`ker(ι n ♯) · M = 𝓘 ^ (n + 1) M`. -/
def idealPowerQuotientPushforwardPullbackIso
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (M : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    cokernel (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι ≅
      (modulePushforward B S hS (ι n)).obj ((modulePullback B S hS (ι n)).obj M) :=
  submoduleCokernelIsoOfEq B S hS (hker n M).symm ≪≫
    kerIdealSmulQuotientUnitIso B S hS (ι n) (hi n) M

/-- The isomorphism `M / 𝓘 ^ (n + 1) M ≅ (ι n)_* ι n ^* M` is the composite of the identification
of the quotients by equal submodules with `AlgebraicGeometry.Space.kerIdealSmulQuotientUnitIso`.
-/
theorem idealPowerQuotientPushforwardPullbackIso_eq
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (M : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    idealPowerQuotientPushforwardPullbackIso B S hS ι hi hker M n =
      submoduleCokernelIsoOfEq B S hS (hker n M).symm ≪≫
        kerIdealSmulQuotientUnitIso B S hS (ι n) (hi n) M :=
  rfl

/-- The isomorphism `M / 𝓘 ^ (n + 1) M ≅ (ι n)_* ι n ^* M` carries the quotient projection to the
unit. -/
@[reassoc]
theorem cokernel_π_comp_idealPowerQuotientPushforwardPullbackIso_hom
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (M : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι ≫
        (idealPowerQuotientPushforwardPullbackIso B S hS ι hi hker M n).hom =
      (modulePullbackAdjunction B S hS (ι n)).unit.app M := by
  rw [idealPowerQuotientPushforwardPullbackIso_eq]
  exact cokernel_π_comp_kerIdealSmulQuotientUnitIso_of_eq B S hS ι hi hker n M

/-- The quotient projections are compatible with the transition maps of the inverse system
`(M / 𝓘 ^ (n + 1) M)_n`. -/
theorem cokernel_π_comp_adicQuotientSystem_map (M : Modules.{u, u} B S hS X.1 X.2) (n : ℕ) :
    @CategoryStruct.comp _ _ M (cokernel (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1 + 1) M).ι)
        (cokernel (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι)
        (cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1 + 1) M).ι)
        ((adicQuotientSystem B S hS X.1 X.2 𝓘 M).map (homOfLE (Nat.le_succ n)).op) =
      cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι :=
  π_comp_idealPowerQuotientMapOfLE B S hS X.1 X.2 𝓘 (Nat.add_le_add_right (Nat.le_succ n) 1) M

/-- The quotients `M / 𝓘 ^ (n + 1) M` are identified with the `(ι n)_* ι n ^* M` through the
units. -/
theorem isUnitQuotient_idealPowerQuotient
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (M : Modules.{u, u} B S hS X.1 X.2) :
    TowerSystem.IsUnitQuotient (fun n => modulePullbackAdjunction B S hS (ι n)) M
      (K := fun n => cokernel (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι)
      (fun n => (adicQuotientSystem B S hS X.1 X.2 𝓘 M).map (homOfLE (Nat.le_succ n)).op)
      (idealPowerQuotientPushforwardPullbackIso B S hS ι hi hker M)
      (fun n => cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M).ι) where
  epi _ := inferInstance
  comp_hom := cokernel_π_comp_idealPowerQuotientPushforwardPullbackIso_hom B S hS ι hi hker M
  comp_transition := cokernel_π_comp_adicQuotientSystem_map B S hS M

/-- The quotients `F / 𝓘 ^ (n + 1) F` of a coherent module are identified with the
`(ι n)_* ι n ^* F` through the units. -/
theorem isUnitQuotient_idealPowerQuotient_obj
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (F : CoherentModules.{u, u} B S hS X.1 X.2) :
    TowerSystem.IsUnitQuotient (fun n => modulePullbackAdjunction B S hS (ι n)) F.obj
      (K := fun n => cokernel (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) F.obj).ι)
      (fun n => (adicQuotientSystem B S hS X.1 X.2 𝓘 F.obj).map (homOfLE (Nat.le_succ n)).op)
      (idealPowerQuotientPushforwardPullbackIso B S hS ι hi hker F.obj)
      (fun n => cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) F.obj).ι) :=
  isUnitQuotient_idealPowerQuotient B S hS ι hi hker F.obj

/-- The restriction of a coherent module to a thickening is coherent. -/
theorem isCoherent_modulePullback_thickening
    (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (n : ℕ) (M : Modules.{u, u} B S hS X.1 X.2) (hM : isCoherent.{u, u} B S hS X.1 X.2 M) :
    isCoherent.{u, u} B S hS (Z n).1 (Z n).2 ((modulePullback B S hS (ι n)).obj M) :=
  have : Fact _ := ⟨hZ n⟩
  isCoherent_modulePullback B S hS (ι n) M hM

/-- **The direct image of the restriction of a coherent module `F` to the thickenings is its
completion**: `((ι n)_* ι n ^* F)_n ≅ (F / 𝓘 ^ (n + 1) F)_n` as inverse systems. -/
def thickeningPushforwardRestrictionIso
    (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (F : CoherentModules.{u, u} B S hS X.1 X.2) :
    (thickeningPushforwardSystems B S hS ι t hι hi).obj
        ((thickeningRestriction B S hS ι t hι hZ).obj F) ≅
      adicQuotientSystem B S hS X.1 X.2 𝓘 F.obj :=
  TowerSystem.pushforwardRestrictionIsoOfUnit
    (fun n => modulePullbackAdjunction B S hS (ι n))
    (fun n => fullyFaithfulModulePushforward B S hS (ι n) (hi n))
    (fun n => modulePullbackCompIsoOfEq B S hS (t n) (ι (n + 1)) (hι n))
    (P := fun n => isCoherent.{u, u} B S hS (Z n).1 (Z n).2)
    (isCoherent.{u, u} B S hS X.1 X.2)
    (isCoherent_modulePullback_thickening B S hS ι hZ) F
    (isUnitQuotient_idealPowerQuotient_obj B S hS ι hi hker F) ≪≫
  Functor.ofOpSequenceMapIso (adicQuotientSystem B S hS X.1 X.2 𝓘 F.obj)

/-- The completion `F ↦ (F / 𝓘 ^ (n + 1) F)_n` of coherent modules is a functor of quotients
identified with the `(ι n)_* ι n ^* F` through the units, naturally in `F`. -/
theorem isUnitQuotientFunctor_adicQuotientFunctor
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M) :
    TowerSystem.IsUnitQuotientFunctor (fun n => modulePullbackAdjunction B S hS (ι n))
      (isCoherent.{u, u} B S hS X.1 X.2)
      (ObjectProperty.ι (isCoherent.{u, u} B S hS X.1 X.2) ⋙ adicQuotientFunctor B S hS X.1 X.2 𝓘)
      (fun F => idealPowerQuotientPushforwardPullbackIso B S hS ι hi hker F.obj)
      (fun F n => cokernel.π (idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) F.obj).ι) where
  isUnitQuotient F := isUnitQuotient_idealPowerQuotient B S hS ι hi hker F.obj
  naturality f n := π_comp_idealPowerQuotientMapOfHom B S hS X.1 X.2 𝓘 (n + 1) f.hom

/-- **The direct image of the restriction to the thickenings is the completion**, as functors from
coherent modules to inverse systems of modules: `((ι n)_* ι n ^* F)_n ≅ (F / 𝓘 ^ (n + 1) F)_n`,
naturally in `F`. -/
def thickeningRestrictionCompPushforwardSystemsIso
    (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M) :
    thickeningRestriction B S hS ι t hι hZ ⋙ thickeningPushforwardSystems B S hS ι t hι hi ≅
      ObjectProperty.ι (isCoherent.{u, u} B S hS X.1 X.2) ⋙ adicQuotientFunctor B S hS X.1 X.2 𝓘 :=
  TowerSystem.restrictionCompPushforwardIsoOfUnit
    (fun n => modulePullbackAdjunction B S hS (ι n))
    (fun n => fullyFaithfulModulePushforward B S hS (ι n) (hi n))
    (fun n => modulePullbackCompIsoOfEq B S hS (t n) (ι (n + 1)) (hι n))
    (P := fun n => isCoherent.{u, u} B S hS (Z n).1 (Z n).2)
    (isCoherent.{u, u} B S hS X.1 X.2)
    (isCoherent_modulePullback_thickening B S hS ι hZ)
    (isUnitQuotientFunctor_adicQuotientFunctor B S hS ι hi hker)

/-- **`Ψ ∘ Φ ≅ (-)^∧`**: the restriction of coherent `𝒪_X`-modules to the thickenings followed by
the direct image to `Coh(X, 𝓘)` is the completion functor
`AlgebraicGeometry.Space.completionFunctor`. -/
def thickeningRestrictionCompPushforwardIso
    [hX : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite) :
    thickeningRestriction B S hS ι t hι hZ ⋙ thickeningPushforward B S hS ι t hι hi hX.out hker ≅
      completionFunctor B S hS X.1 X.2 𝓘 hI :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (ObjectProperty.liftCompιIso _ _ _) ≪≫
      thickeningRestrictionCompPushforwardSystemsIso B S hS ι t hι hi hZ hker ≪≫
      (ObjectProperty.liftCompιIso _ _ _).symm)

/-- **The restriction `Φ` to the thickenings is fully faithful if the completion functor is.** -/
def thickeningRestrictionFullyFaithful
    [hX : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    (hC : (completionFunctor B S hS X.1 X.2 𝓘 hI).FullyFaithful) :
    (thickeningRestriction B S hS ι t hι hZ).FullyFaithful :=
  have := (thickeningPushforwardFullyFaithful B S hS ι t hι hi hX.out hker).faithful
  Functor.FullyFaithful.ofCompFaithful (G := thickeningPushforward B S hS ι t hι hi hX.out hker)
    (hC.ofIso (thickeningRestrictionCompPushforwardIso B S hS ι t hι hi hZ hker hI).symm)

include hi in
/-- **The restriction `Φ` to the thickenings is essentially surjective if the completion functor
is.** -/
theorem essSurj_thickeningRestriction
    [hX : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))]
    (hZ : ∀ n, HasEtaleLocalProperty B S hS (Z n).1 (fun V : Scheme.{u} => IsLocallyNoetherian V))
    (hker : ∀ n (M : Modules.{u, u} B S hS X.1 X.2),
      kerIdealSmul B S hS (ι n) M = idealPowerMultiple B S hS X.1 X.2 𝓘 (n + 1) M)
    (hI : 𝓘.toSheafOfModules.IsQuasicoherentOnSite)
    [(completionFunctor B S hS X.1 X.2 𝓘 hI).EssSurj] :
    (thickeningRestriction B S hS ι t hι hZ).EssSurj where
  mem_essImage A :=
    ⟨(completionFunctor B S hS X.1 X.2 𝓘 hI).objPreimage
        ((thickeningPushforward B S hS ι t hι hi hX.out hker).obj A),
      ⟨(thickeningPushforwardFullyFaithful B S hS ι t hι hi hX.out hker).preimageIso
        ((thickeningRestrictionCompPushforwardIso B S hS ι t hι hi hZ hker hI).app _ ≪≫
          (completionFunctor B S hS X.1 X.2 𝓘 hI).objObjPreimageIso _)⟩⟩


end Thickening

end AlgebraicGeometry.Space

end
