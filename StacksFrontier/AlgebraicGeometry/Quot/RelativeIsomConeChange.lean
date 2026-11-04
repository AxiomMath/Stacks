module

public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackIsomFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Changing the family of test objects of a relative Hom or Isom functor

Let `P` be a coherent pullback pseudofunctor datum on a category `A` with fibres `D`, and let
`κ : π ⟶ a₀` be a family of test objects over `a₀ : A` indexed by a category `I`.  The relative
Hom functor `i ↦ ((π i)^*M ⟶ (π i)^*N)` and the relative Isom functor of `M, N : D a₀`,
`CategoryTheory.PullbackData.relHomFunctor` and `CategoryTheory.PullbackData.relIsoFunctor`,
depend on the family only up to isomorphism: if `κ' : π' ⟶ a₀` is a second family and
`e : π ≅ π'` is an isomorphism of the index functors compatible with the structure morphisms,
the two relative Hom functors, and the two relative Isom functors, are isomorphic.  The
comparison conjugates a morphism `(π' i)^*M ⟶ (π' i)^*N` by the composition comparison of the
factorisation `π i ≅ π' i ⟶ a₀`; the inverse image along the isomorphism `π i ≅ π' i` is an
equivalence, so conjugation is a bijection, and the associativity of the datum makes it natural.

## Main definitions

* `CategoryTheory.PullbackData.pullFullyFaithfulOfIso`: the inverse image along an isomorphism
  is fully faithful.
* `CategoryTheory.PullbackData.ConeTo.precomp`: restricting a family of test objects along a
  functor of index categories.
* `CategoryTheory.PullbackData.relHomConeChange`: the bijection between the relative Hom sets of
  two isomorphic families.
* `CategoryTheory.PullbackData.relHomFunctorConeChangeIso` and
  `CategoryTheory.PullbackData.relIsoFunctorConeChangeIso`: **the relative Hom and Isom functors
  of two isomorphic families are isomorphic**.
* `CategoryTheory.PullbackData.relIsoFunctorPrecompIso`: the relative Isom functor of a restricted
  family is the restriction of the relative Isom functor.
* `CategoryTheory.PullbackData.relIsoFunctorSymmIso`: `Isom(M, N) ≅ Isom(N, M)`, `φ ↦ φ⁻¹`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.PullbackData

universe v₁ u₁ v₂ u₂

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  (P : PullbackData A D)

/-- **The inverse image along an isomorphism is fully faithful**: it is an equivalence, with the
inverse image along the inverse isomorphism as quasi-inverse. -/
def pullFullyFaithfulOfIso {a b : A} (e : a ≅ b) : (P.pull e.hom).FullyFaithful :=
  (Equivalence.mk (P.pull e.hom) (P.pull e.inv)
    ((P.idIso b).symm ≪≫ eqToIso (congrArg (fun m : b ⟶ b => P.pull m) e.inv_hom_id.symm) ≪≫
      P.compIso e.inv e.hom)
    ((P.compIso e.hom e.inv).symm ≪≫
      eqToIso (congrArg (fun m : a ⟶ a => P.pull m) e.hom_inv_id) ≪≫
      P.idIso a)).fullyFaithfulFunctor

namespace ConeTo

variable {I : Type*} [Category* I] {J : Type*} [Category* J] {π : I ⥤ A} {a₀ : A}

/-- The restriction of a family of test objects along a functor of index categories. -/
def precomp (κ : ConeTo π a₀) (G : J ⥤ I) : ConeTo (G ⋙ π) a₀ where
  leg j := κ.leg (G.obj j)
  w g := κ.w (G.map g)

end ConeTo

variable {I : Type*} [Category* I] {π π' : I ⥤ A} {a₀ : A}
  (κ : ConeTo π a₀) (κ' : ConeTo π' a₀) (e : π ≅ π')
  (he : ∀ i, e.hom.app i ≫ κ'.leg i = κ.leg i)

/-- Conjugation by the comparison of the factorisation `π i ≅ π' i ⟶ a₀` is a bijection from
the relative Hom set of the family `κ'` at `i` to that of the family `κ`. -/
theorem bijective_relHomConeChange (M N : D a₀) (i : I) :
    Function.Bijective (Functor.conjHom (P.triangle (he i)) (M := M) (N := N)) := by
  let c := P.triangle (he i)
  let hL := P.pullFullyFaithfulOfIso (e.app i)
  let φ : ((P.pull (e.hom.app i)).obj ((P.pull (κ'.leg i)).obj M) ⟶
      (P.pull (e.hom.app i)).obj ((P.pull (κ'.leg i)).obj N)) ≃
      ((P.pull (κ.leg i)).obj M ⟶ (P.pull (κ.leg i)).obj N) :=
    { toFun := fun β => c.hom.app M ≫ β ≫ c.inv.app N
      invFun := fun γ => c.inv.app M ≫ γ ≫ c.hom.app N
      left_inv := fun β => by simp
      right_inv := fun γ => by simp }
  have hcomp : Functor.conjHom c (M := M) (N := N) =
      (fun β => φ β) ∘ fun α => (P.pull (e.hom.app i)).map α := rfl
  rw [hcomp]
  exact φ.bijective.comp (hL.map_bijective _ _)

/-- **The bijection between the relative Hom sets of two isomorphic families**: conjugation by the
composition comparison of the factorisation `π i ≅ π' i ⟶ a₀`. -/
def relHomConeChange (M N : D a₀) (i : I) : P.relHomObj κ' M N i ≃ P.relHomObj κ M N i :=
  Equiv.ofBijective _ (P.bijective_relHomConeChange κ κ' e he M N i)

/-- The bijection `relHomConeChange` sends a relative morphism `α` to its conjugate by the
comparison of the factorisation `π i ≅ π' i ⟶ a₀`. -/
theorem relHomConeChange_apply (M N : D a₀) (i : I) (α : P.relHomObj κ' M N i) :
    P.relHomConeChange κ κ' e he M N i α = Functor.conjHom (P.triangle (he i)) α :=
  rfl

variable {P} (hP : P.IsCoherent)

include hP in
/-- **The bijection between the relative Hom sets of two isomorphic families is natural**: it
commutes with the inverse image along a transition morphism `g : j ⟶ i`. -/
theorem relHomConeChange_relHomMap (M N : D a₀) {j i : I} (g : j ⟶ i)
    (α : P.relHomObj κ' M N i) :
    P.relHomConeChange κ κ' e he M N j (P.relHomMap κ' M N g α) =
      P.relHomMap κ M N g (P.relHomConeChange κ κ' e he M N i α) := by
  have hkr : (e.hom.app j ≫ π'.map g) ≫ κ'.leg i = κ.leg j := by
    rw [Category.assoc, κ'.w g, he j]
  have hk : π.map g ≫ e.hom.app i = e.hom.app j ≫ π'.map g := e.hom.naturality g
  simp only [relHomConeChange_apply, relHomMap]
  rw [← Functor.conjHom_comp _ _ _ _
      (hP.triangle_comp' (f := e.hom.app j) (g := π'.map g) (p := κ'.leg i) rfl (κ'.w g)
        (he j) hkr) α,
    ← Functor.conjHom_comp _ _ _ _
      (hP.triangle_comp' (f := π.map g) (g := e.hom.app i) (p := κ'.leg i) hk (he i)
        (κ.w g) hkr) α]

/-- **The relative Hom functors of two isomorphic families are isomorphic.** -/
def relHomFunctorConeChangeIso (M N : D a₀) :
    P.relHomFunctor hP κ' M N ≅ P.relHomFunctor hP κ M N :=
  NatIso.ofComponents
    (fun i => Equiv.toIso (P.relHomConeChange κ κ' e he M N i.unop))
    (fun g => congrArg TypeCat.ofHom
      (funext fun α => relHomConeChange_relHomMap κ κ' e he hP M N g.unop α))

omit hP in
/-- Conjugation by the comparison of the factorisation `π i ≅ π' i ⟶ a₀` preserves and reflects
isomorphisms. -/
theorem isIso_relHomConeChange_iff (M N : D a₀) (i : I) (α : P.relHomObj κ' M N i) :
    IsIso (P.relHomConeChange κ κ' e he M N i α) ↔ IsIso α := by
  rw [relHomConeChange_apply]
  show IsIso ((P.triangle (he i)).hom.app M ≫ (P.pull (e.hom.app i)).map α ≫
    (P.triangle (he i)).inv.app N) ↔ _
  rw [isIso_comp_left_iff, isIso_comp_right_iff]
  refine ⟨fun h => ?_, fun _ => Functor.map_isIso _ _⟩
  have : IsIso ((P.pull (e.app i).hom).map α) := h
  exact (P.pullFullyFaithfulOfIso (e.app i)).isIso_of_isIso_map α

/-- **The relative Isom functors of two isomorphic families are isomorphic.** -/
def relIsoFunctorConeChangeIso (M N : D a₀) :
    P.relIsoFunctor κ' hP M N ≅ P.relIsoFunctor κ hP M N :=
  NatIso.ofComponents
    (fun i => Equiv.toIso
      { toFun := fun α => ⟨P.relHomConeChange κ κ' e he M N i.unop α.1,
          (isIso_relHomConeChange_iff κ κ' e he M N i.unop α.1).2 α.2⟩
        invFun := fun β => ⟨(P.relHomConeChange κ κ' e he M N i.unop).symm β.1,
          (isIso_relHomConeChange_iff κ κ' e he M N i.unop _).1 (by
            rw [Equiv.apply_symm_apply]
            exact β.2)⟩
        left_inv := fun α => Subtype.ext (Equiv.symm_apply_apply _ _)
        right_inv := fun β => Subtype.ext (Equiv.apply_symm_apply _ _) })
    (fun {i j} g => congrArg TypeCat.ofHom (funext fun α => Subtype.ext
      (relHomConeChange_relHomMap κ κ' e he hP M N g.unop α.1)))

omit κ' e he in
/-- The relative Isom functor acts on a transition morphism by inverse image of morphisms. -/
theorem relIsoFunctor_map_val (M N : D a₀) {i j : I} (g : j ⟶ i)
    (α : (P.relIsoFunctor κ hP M N).obj (Opposite.op i)) :
    ((P.relIsoFunctor κ hP M N).map g.op α).1 = P.relHomMap κ M N g α.1 :=
  rfl

omit hP κ' e he in
/-- The inverse image of a morphism of inverse images along a transition morphism is its
conjugate by the composition comparison. -/
theorem relHomMap_eq_conjHom (M N : D a₀) {i j : I} (g : j ⟶ i)
    (α : P.relHomObj κ M N i) :
    P.relHomMap κ M N g α = Functor.conjHom (P.triangle (κ.w g)) α :=
  rfl

omit κ' e he in
/-- **The relative Isom functor of a restricted family is the restriction of the relative Isom
functor.** -/
def relIsoFunctorPrecompIso {J : Type*} [Category* J] (G : J ⥤ I) (M N : D a₀) :
    P.relIsoFunctor (κ.precomp G) hP M N ≅ G.op ⋙ P.relIsoFunctor κ hP M N :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

omit κ' e he in
/-- **`Isom(M, N) ≅ Isom(N, M)`**, an isomorphism being sent to its inverse. -/
@[sga "3 I 1.7.2" "more general"]
def relIsoFunctorSymmIso (M N : D a₀) :
    P.relIsoFunctor κ hP M N ≅ P.relIsoFunctor κ hP N M :=
  NatIso.ofComponents
    (fun i => Equiv.toIso
      { toFun := fun α => ⟨@inv _ _ _ _ α.1 α.2, by have := α.2; infer_instance⟩
        invFun := fun β => ⟨@inv _ _ _ _ β.1 β.2, by have := β.2; infer_instance⟩
        left_inv := fun α => Subtype.ext (by have := α.2; exact IsIso.inv_inv (f := α.1))
        right_inv := fun β => Subtype.ext (by have := β.2; exact IsIso.inv_inv (f := β.1)) })
    (fun {i j} g => congrArg TypeCat.ofHom (funext fun α => Subtype.ext (by
      have := α.2
      exact (P.relHomMap_inv κ g.unop α.1).symm)))

end CategoryTheory.PullbackData

end
