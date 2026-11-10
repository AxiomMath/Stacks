module

public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesFibreExtBaseChange

/-!
# Comparing relative Hom functors along isomorphic cones

Let `P` be a coherent pullback pseudofunctor datum on a category `A` and `M`, `N` objects over
`a₀ : A`.  For a cone `κ` from a functor `π : I ⥤ A` to `a₀` the relative Hom functor
`i ↦ Hom((π i)^* M, (π i)^* N)` of `CategoryTheory.PullbackData.relHomFunctor` depends on the cone
only up to isomorphism: if `κ'` is a second cone from `π' : I' ⥤ A`, `Ψ : I ⥤ I'` is a functor and
`σ : π ≅ Ψ ⋙ π'` is a natural isomorphism compatible with the legs, then the relative Hom functor
of `κ` is the restriction along `Ψ` of that of `κ'`.

The comparison at `i` is conjugation by the comparison `(κ i)^* ≅ (κ' (Ψ i))^* ⋙ (σ i)^*` of the
datum, which is bijective because the inverse image along an isomorphism is an equivalence.  Its
naturality is the associativity law of the datum.

This is what identifies the functor `V ↦ Hom(K_V, E_V)` computed with two different, but
isomorphic, models of the base changes `X_V`.

## Main definitions

* `CategoryTheory.PullbackData.relHomConeEquiv`: the comparison at one index.
* `CategoryTheory.PullbackData.relHomFunctorConeIso`: the isomorphism of relative Hom functors.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.PullbackData

universe v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] {D : A → Type u₂} [∀ a, Category.{v₂} (D a)]
  (P : PullbackData A D) (hP : P.IsCoherent)
  {I I' : Type*} [Category* I] [Category* I'] {π : I ⥤ A} {π' : I' ⥤ A} {a₀ : A}

/-- **The comparison of the relative Hom sets of two cones at one index.**  For an isomorphism
`σ : π i ≅ π' i'` compatible with the legs, conjugation by the comparison
`(κ i)^* ≅ (κ' i')^* ⋙ σ^*` is a bijection from the morphisms between the inverse images along
`κ' i'` to those between the inverse images along `κ i`. -/
def relHomConeEquiv (κ : ConeTo π a₀) (κ' : ConeTo π' a₀) {i : I} {i' : I'}
    (σ : π.obj i ≅ π'.obj i') (hσ : σ.hom ≫ κ'.leg i' = κ.leg i) (M N : D a₀) :
    P.relHomObj κ' M N i' ≃ P.relHomObj κ M N i where
  toFun α := Functor.conjHom (P.triangle hσ) α
  invFun β := ((P.pullEquivalence σ).fullyFaithfulFunctor).preimage
    ((P.triangle hσ).inv.app M ≫ β ≫ (P.triangle hσ).hom.app N)
  left_inv α := by
    apply ((P.pullEquivalence σ).fullyFaithfulFunctor).map_injective
    rw [Functor.FullyFaithful.map_preimage]
    simp [Functor.conjHom, pullEquivalence_functor]
  right_inv β := by
    have h : (P.pull σ.hom).map (((P.pullEquivalence σ).fullyFaithfulFunctor).preimage
        ((P.triangle hσ).inv.app M ≫ β ≫ (P.triangle hσ).hom.app N)) =
        (P.triangle hσ).inv.app M ≫ β ≫ (P.triangle hσ).hom.app N :=
      ((P.pullEquivalence σ).fullyFaithfulFunctor).map_preimage _
    simp only [Functor.conjHom, h]
    simp

/-- **Relative Hom functors along isomorphic cones are isomorphic.**  For cones `κ` from `π` and
`κ'` from `π'` to `a₀`, a functor `Ψ : I ⥤ I'` and a natural isomorphism `σ : π ≅ Ψ ⋙ π'`
compatible with the legs, the relative Hom functor of `κ` is the restriction along `Ψ` of that of
`κ'`. -/
def relHomFunctorConeIso (κ : ConeTo π a₀) (κ' : ConeTo π' a₀) (Ψ : I ⥤ I')
    (σ : π ≅ Ψ ⋙ π') (hσ : ∀ i, σ.hom.app i ≫ κ'.leg (Ψ.obj i) = κ.leg i) (M N : D a₀) :
    Ψ.op ⋙ P.relHomFunctor hP κ' M N ≅ P.relHomFunctor hP κ M N :=
  NatIso.ofComponents
    (fun i => (P.relHomConeEquiv κ κ' (σ.app i.unop) (hσ i.unop) M N).toIso) <| by
    rintro ⟨j⟩ ⟨i⟩ ⟨g⟩
    have hnat : π.map g ≫ σ.hom.app j = σ.hom.app i ≫ π'.map (Ψ.map g) :=
      σ.hom.naturality g
    have hr : (π.map g ≫ σ.hom.app j) ≫ κ'.leg (Ψ.obj j) = κ.leg i := by
      rw [Category.assoc, hσ, κ.w]
    have key : ∀ α : (P.pull (κ'.leg (Ψ.obj j))).obj M ⟶ (P.pull (κ'.leg (Ψ.obj j))).obj N,
        Functor.conjHom (P.triangle (hσ i))
            (Functor.conjHom (P.triangle (κ'.w (Ψ.map g))) α) =
          Functor.conjHom (P.triangle (κ.w g)) (Functor.conjHom (P.triangle (hσ j)) α) := by
      intro α
      rw [← Functor.conjHom_comp (P.triangle (hσ j)) (P.triangle (κ.w g)) (P.triangle hr)
          (P.triangle (f := π.map g) (g := σ.hom.app j) rfl)
          (hP.triangle_comp' rfl (hσ j) (κ.w g) hr),
        ← Functor.conjHom_comp (P.triangle (κ'.w (Ψ.map g))) (P.triangle (hσ i)) (P.triangle hr)
          (P.triangle (f := σ.hom.app i) (g := π'.map (Ψ.map g)) hnat.symm)
          (hP.triangle_comp' hnat.symm (κ'.w (Ψ.map g)) (hσ i) hr)]
    ext α : 3
    exact key α

/-- Conjugation by a comparison carries isomorphisms to isomorphisms. -/
instance _root_.CategoryTheory.Functor.isIso_conjHom {C D₁ D₂ : Type*} [Category* C]
    [Category* D₁] [Category* D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}
    (e : P₂ ≅ P₁ ⋙ L) {M N : C} (α : P₁.obj M ⟶ P₁.obj N) [IsIso α] :
    IsIso (Functor.conjHom e α) := by
  dsimp only [Functor.conjHom]
  infer_instance

/-- Conjugation by a comparison is compatible with composition. -/
theorem _root_.CategoryTheory.Functor.conjHom_comp_conjHom {C D₁ D₂ : Type*} [Category* C]
    [Category* D₁] [Category* D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}
    (e : P₂ ≅ P₁ ⋙ L) {M N K : C} (α : P₁.obj M ⟶ P₁.obj N) (β : P₁.obj N ⟶ P₁.obj K) :
    Functor.conjHom e α ≫ Functor.conjHom e β = Functor.conjHom e (α ≫ β) := by
  simp [Functor.conjHom]

/-- **The subfunctor of isomorphisms of the relative Hom functor.** -/
def relIsoSubfunctor (κ : ConeTo π a₀) (M N : D a₀) : Subfunctor (P.relHomFunctor hP κ M N) where
  obj _ := {α | IsIso α}
  map g α hα :=
    @Functor.isIso_conjHom _ _ _ _ _ _ _ _ _ (P.triangle (κ.w g.unop)) M N α hα

/-- **The relative Isom functor**: `i ↦ Isom((π i)^* M, (π i)^* N)`. -/
abbrev relHomIsoFunctor (κ : ConeTo π a₀) (M N : D a₀) : Iᵒᵖ ⥤ Type v₂ :=
  (P.relIsoSubfunctor hP κ M N).toFunctor

/-- The comparison of `CategoryTheory.PullbackData.relHomConeEquiv` preserves and reflects
isomorphisms. -/
theorem isIso_relHomConeEquiv_iff (κ : ConeTo π a₀) (κ' : ConeTo π' a₀) {i : I} {i' : I'}
    (σ : π.obj i ≅ π'.obj i') (hσ : σ.hom ≫ κ'.leg i' = κ.leg i) (M N : D a₀)
    (α : P.relHomObj κ' M N i') :
    IsIso (P.relHomConeEquiv κ κ' σ hσ M N α) ↔ IsIso α := by
  refine ⟨fun h => ?_, fun _ => Functor.isIso_conjHom (P.triangle hσ) α⟩
  change IsIso (Functor.conjHom (P.triangle hσ) α) at h
  have : IsIso ((P.pullEquivalence σ).functor.map α) := by
    change IsIso ((P.pull σ.hom).map α)
    rw [show (P.pull σ.hom).map α = (P.triangle hσ).inv.app M ≫
        Functor.conjHom (P.triangle hσ) α ≫ (P.triangle hσ).hom.app N by simp [Functor.conjHom]]
    infer_instance
  exact (P.pullEquivalence σ).fullyFaithfulFunctor.isIso_of_isIso_map α

/-- **Relative Isom functors along isomorphic cones are isomorphic.** -/
def relHomIsoFunctorConeIso (κ : ConeTo π a₀) (κ' : ConeTo π' a₀) (Ψ : I ⥤ I')
    (σ : π ≅ Ψ ⋙ π') (hσ : ∀ i, σ.hom.app i ≫ κ'.leg (Ψ.obj i) = κ.leg i) (M N : D a₀) :
    Ψ.op ⋙ P.relHomIsoFunctor hP κ' M N ≅ P.relHomIsoFunctor hP κ M N :=
  NatIso.ofComponents
    (fun i => Equiv.toIso
      ((P.relHomConeEquiv κ κ' (σ.app i.unop) (hσ i.unop) M N).subtypeEquiv
        (fun α => (P.isIso_relHomConeEquiv_iff κ κ' (σ.app i.unop) (hσ i.unop) M N α).symm)))
    (fun {i j} g => by
      ext α : 3
      exact Subtype.ext (congrArg (fun t => t α.1)
        (congrArg (fun m => (ConcreteCategory.hom m : _ → _))
          ((P.relHomFunctorConeIso hP κ κ' Ψ σ hσ M N).hom.naturality g))))

/-- **Conjugation by a comparison along a composite, against composition of fibre morphisms.**
For a morphism `k₀` equal both to a composite `f ≫ g` and to `k`, conjugating `α` by the
comparison of `k^*` with `g^* ⋙ f^*`, read at `k₀`, is composing `α` after the identification of
`k₀^*` with `k^*`, through the comparison of `k₀^*` with `g^* ⋙ f^*`. -/
theorem eqToHom_comp_conjHom_triangle {a b c : A} (f : a ⟶ b) (g : b ⟶ c) {k k₀ : a ⟶ c}
    (e₀ : k₀ = f ≫ g) (e₁ : k₀ = k) (w : f ≫ g = k) {M N : D c}
    (α : (P.pull g).obj M ⟶ (P.pull g).obj N) :
    eqToHom (congrArg (fun m => (P.pull m).obj M) e₁) ≫ Functor.conjHom (P.triangle w) α =
      Functor.fibreComp (P.triangle e₀.symm)
        ((P.triangle e₀.symm).symm.app N ≪≫ (eqToIso (congrArg (fun m => P.pull m) e₁)).app N).hom
        α := by
  subst e₁
  subst e₀
  simp [Functor.conjHom, Functor.fibreComp]

/-- The restriction maps of the relative Isom functor are those of the relative Hom functor. -/
theorem relHomIsoFunctor_map_coe (κ : ConeTo π a₀) (M N : D a₀) {i j : I} (h : i ⟶ j)
    (α : (P.relHomIsoFunctor hP κ M N).obj (Opposite.op j)) :
    ((P.relHomIsoFunctor hP κ M N).map h.op α).1 = P.relHomMap κ M N h α.1 := rfl

/-- The restriction of a cone along a functor of index categories. -/
def ConeTo.restrict (κ : ConeTo π' a₀) (Ψ : I ⥤ I') : ConeTo (Ψ ⋙ π') a₀ where
  leg i := κ.leg (Ψ.obj i)
  w g := κ.w (Ψ.map g)

/-- The relative Hom functor of a restricted cone is the restriction of the relative Hom
functor. -/
def relHomFunctorRestrictIso (κ : ConeTo π' a₀) (Ψ : I ⥤ I') (M N : D a₀) :
    P.relHomFunctor hP (κ.restrict Ψ) M N ≅ Ψ.op ⋙ P.relHomFunctor hP κ M N :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

section Pairs

variable {J : Type*} [Category* J]

/-- The pointwise product of two presheaves of sets. -/
@[simps]
def pairPresheaf (F G : J ⥤ Type v₂) : J ⥤ Type v₂ where
  obj i := F.obj i × G.obj i
  map f := ↾fun x => (F.map f x.1, G.map f x.2)

/-- The first projection of the pointwise product. -/
def pairFst (F G : J ⥤ Type v₂) : pairPresheaf F G ⟶ F where
  app _ := ↾fun x => x.1

/-- The second projection of the pointwise product. -/
def pairSnd (F G : J ⥤ Type v₂) : pairPresheaf F G ⟶ G where
  app _ := ↾fun x => x.2

/-- The terminal presheaf of sets. -/
abbrev unitPresheaf (J : Type*) [Category* J] : J ⥤ Type v₂ := (Functor.const J).obj PUnit

/-- The morphism to the terminal presheaf. -/
def toUnitPresheaf (F : J ⥤ Type v₂) : F ⟶ unitPresheaf J where
  app _ := ↾fun _ => PUnit.unit

/-- The constant presheaf `PUnit` is terminal. -/
theorem isTerminal_unitPresheaf : Nonempty (Limits.IsTerminal (unitPresheaf.{v₂} J)) :=
  ⟨Limits.IsTerminal.ofUniqueHom (fun F => toUnitPresheaf F) (fun F m => by ext; rfl)⟩

/-- The pointwise product is a fibre product over the terminal presheaf. -/
theorem isPullback_pairPresheaf (F G : J ⥤ Type v₂) :
    IsPullback (pairFst F G) (pairSnd F G) (toUnitPresheaf F) (toUnitPresheaf G) :=
  IsPullback.of_forall_isPullback_app fun i => by
    rw [CategoryTheory.Limits.Types.isPullback_iff]
    exact ⟨rfl, fun x y h => Prod.ext h.1 h.2, fun a b _ => ⟨(a, b), rfl, rfl⟩⟩

/-- Restricting a fibre-product square of presheaves of sets along a functor gives a
fibre-product square. -/
theorem isPullback_whiskerLeft {J' : Type*} [Category* J'] (Φ : J' ⥤ J)
    {F₁ F₂ F₃ F₄ : J ⥤ Type v₂} {t : F₁ ⟶ F₂} {l : F₁ ⟶ F₃} {r : F₂ ⟶ F₄} {b : F₃ ⟶ F₄}
    (h : IsPullback t l r b) :
    IsPullback (Functor.whiskerLeft Φ t) (Functor.whiskerLeft Φ l) (Functor.whiskerLeft Φ r)
      (Functor.whiskerLeft Φ b) :=
  IsPullback.of_forall_isPullback_app fun j => h.app (Φ.obj j)

/-- The restriction of the terminal presheaf is terminal. -/
theorem isTerminal_comp_unitPresheaf {J' : Type*} [Category* J'] (Φ : J' ⥤ J) :
    Nonempty (Limits.IsTerminal (Φ ⋙ unitPresheaf.{v₂} J)) :=
  ⟨Limits.IsTerminal.ofUniqueHom (fun _ => { app := fun _ => ↾fun _ => PUnit.unit })
    (fun _ _ => by ext; rfl)⟩

end Pairs

section IsomAsFibreProduct

variable (κ : ConeTo π a₀) (M N : D a₀)

/-- The composition maps `(α, β) ↦ (α ≫ β, β ≫ α)` of the relative Hom functors. -/
def relHomCompPair :
    pairPresheaf (P.relHomFunctor hP κ M N) (P.relHomFunctor hP κ N M) ⟶
      pairPresheaf (P.relHomFunctor hP κ M M) (P.relHomFunctor hP κ N N) where
  app _ := ↾fun x => (x.1 ≫ x.2, x.2 ≫ x.1)
  naturality {i j} g := by
    ext x : 3
    exact Prod.ext (Functor.conjHom_comp_conjHom (P.triangle (κ.w g.unop)) x.1 x.2)
      (Functor.conjHom_comp_conjHom (P.triangle (κ.w g.unop)) x.2 x.1)

/-- The pair of identities. -/
def relHomIdPair :
    unitPresheaf Iᵒᵖ ⟶ pairPresheaf (P.relHomFunctor hP κ M M) (P.relHomFunctor hP κ N N) where
  app _ := ↾fun _ => (𝟙 _, 𝟙 _)
  naturality {i j} g := by
    ext x : 3
    have hid : ∀ {P₁ : D a₀ ⥤ D (π.obj i.unop)} {P₂ : D a₀ ⥤ D (π.obj j.unop)}
        {L : D (π.obj i.unop) ⥤ D (π.obj j.unop)} (e : P₂ ≅ P₁ ⋙ L) (K : D a₀),
        Functor.conjHom e (𝟙 (P₁.obj K)) = 𝟙 (P₂.obj K) := fun e K => by
      simp [Functor.conjHom]
    exact Prod.ext (hid (P.triangle (κ.w g.unop)) M).symm (hid (P.triangle (κ.w g.unop)) N).symm

/-- The inverse of the conjugate is the conjugate of the inverse. -/
theorem inv_conjHom {C D₁ D₂ : Type*} [Category* C] [Category* D₁] [Category* D₂] {P₁ : C ⥤ D₁}
    {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂} (e : P₂ ≅ P₁ ⋙ L) {M N : C} (α : P₁.obj M ⟶ P₁.obj N) [IsIso α] :
    Functor.conjHom e (inv α) = inv (Functor.conjHom e α) := by
  refine IsIso.eq_inv_of_hom_inv_id (f := Functor.conjHom e α) ?_
  rw [Functor.conjHom_comp_conjHom, IsIso.hom_inv_id]
  simp [Functor.conjHom]

/-- An isomorphism `α` with its inverse. -/
def relIsoToPair :
    P.relHomIsoFunctor hP κ M N ⟶
      pairPresheaf (P.relHomFunctor hP κ M N) (P.relHomFunctor hP κ N M) where
  app _ := ↾fun α => (α.1, haveI : IsIso α.1 := α.2; inv α.1)
  naturality {i j} g := by
    ext ⟨α, hα⟩ : 3
    have : IsIso α := hα
    exact Prod.ext rfl (inv_conjHom (P.triangle (κ.w g.unop)) α).symm

/-- **The relative Isom functor is the fibre product of the relative Hom functors** along the
composition maps and the identities, as in the proof of Stacks 08K9. -/
theorem isPullback_relHomIsoFunctor :
    IsPullback (P.relIsoToPair hP κ M N) (toUnitPresheaf _) (P.relHomCompPair hP κ M N)
      (P.relHomIdPair hP κ M N) :=
  IsPullback.of_forall_isPullback_app fun i => by
    rw [CategoryTheory.Limits.Types.isPullback_iff]
    refine ⟨?_, ?_, ?_⟩
    · ext ⟨α, hα⟩
      have : IsIso α := hα
      exact Prod.ext (IsIso.hom_inv_id α) (IsIso.inv_hom_id α)
    · rintro ⟨α, hα⟩ ⟨β, hβ⟩ ⟨h, -⟩
      exact Subtype.ext (congrArg (fun p => p.1) h :)
    · rintro ⟨α, β⟩ _ h
      have h1 : α ≫ β = 𝟙 _ := (congrArg (fun p => p.1) h :)
      have h2 : β ≫ α = 𝟙 _ := (congrArg (fun p => p.2) h :)
      have hα : IsIso α := ⟨β, h1, h2⟩
      refine ⟨⟨α, hα⟩, Prod.ext rfl ?_, rfl⟩
      exact IsIso.inv_eq_of_hom_inv_id h1

end IsomAsFibreProduct

end CategoryTheory.PullbackData

end
