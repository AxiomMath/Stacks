module

public import StacksFrontier.Deformation.Artin.Obstruction.DualNotion
public import StacksFrontier.Homology.Tor.DerivedTensorFunctorSmul

/-!
# A dual deformation situation from identifications with given groups

Let `x` be an object over `Spec A` of a category fibred in groupoids satisfying (RS*), and let
`K` be an object of `D(A)`. Suppose the groups `Hⁿ(K ⊗ᴸ M)`, `n = 1, 2`, are identified with
groups `V M n`, naturally in the `A`-module `M` and compatibly with the connecting maps of short
exact sequences, and suppose that

* the tangent functor `T_x(M)` is identified with `V M 1`, naturally in `M`;
* every deformation situation `(x, A' → A)` with kernel `I` carries an element of `V I 2`,
  carried to each other by morphisms of deformation situations, vanishing exactly when `x`
  lifts to `Spec A'`;
* for a short exact sequence of deformation situations, the element of the smallest one is the
  image of a tangent class under the connecting map of `V`.

Then `K` is the complex of a dual deformation situation (Stacks 07YX) satisfying clause (iv)
of Stacks 07YY. This separates the homological algebra of the first proof of Stacks 08WA, which
produces `K` and the identifications with Ext groups, from the deformation theory, which
produces the tangent classes and the obstructions in those Ext groups.

## Main definitions

* `Deformation.Artin.DualNotion.GroupsBoundaryCondition`: the third condition above.

## Main results

* `Deformation.Artin.derivedCohomology_map_smul_id`: `Hⁿ(K ⊗ᴸ -)` carries multiplication by a
  scalar to multiplication by the scalar.
* `Deformation.Artin.DualNotion.exists_dualDeformationSituation_of_groups`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

attribute [local instance] HasDerivedCategory.standard

/-- `Hⁿ(K ⊗ᴸ -)` carries `a • 𝟙` to `a • 𝟙`. -/
theorem derivedCohomology_map_smul_id {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (M : ModuleCat.{u} A) (a : A) :
    (derivedCohomology A K n).map (a • 𝟙 M) = a • 𝟙 _ := by
  show (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
    ((CochainComplex.DerivedTensor.derivedTensorProduct K).map
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map (a • 𝟙 M))) = _
  rw [Functor.map_smul, CategoryTheory.Functor.map_id,
    CochainComplex.DerivedTensor.derivedTensorProduct_map_smul_id, Functor.map_smul,
    CategoryTheory.Functor.map_id]
  rfl

/-- An additive map out of `Hⁿ(K ⊗ᴸ M)` which is natural in `M` is `A`-linear. -/
theorem derivedCohomology_smul_apply {A : Type u} [CommRing A]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ) (M : ModuleCat.{u} A) (a : A)
    (c : (derivedCohomology A K n).obj M) :
    (derivedCohomology A K n).map (a • 𝟙 M) c = a • c := by
  rw [derivedCohomology_map_smul_id]
  rfl

end Deformation.Artin

namespace Deformation.Artin.DualNotion

attribute [local instance] HasDerivedCategory.standard

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) [IsLocallyNoetherian S]
variable (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
variable (X : Type v) [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
variable {Λ A B S hS toS hA X p}
variable (x : X) (hx : p.obj x = algebraOver A B S hS toS hA) (hp : p.IsFiberedInGroupoids)
  (hRS : SatisfiesRSStar B S hS p hp)

/-- The inverse of an additive equivalence intertwines maps intertwined by the equivalence. -/
private theorem symm_apply_of_natural {α β γ δ : Type*} [Add α] [Add β] [Add γ] [Add δ]
    (e : α ≃+ γ) (e' : β ≃+ δ) {f : α → β} {g : γ → δ} (h : ∀ c, e' (f c) = g (e c)) (v : γ) :
    e'.symm (g v) = f (e.symm v) := by
  rw [AddEquiv.symm_apply_eq, h, AddEquiv.apply_symm_apply]

/-- **The boundary condition read in given groups.** For a short exact sequence of deformation
situations and a lift of `x` over the middle one, the element `ob` of the smallest one is the
image under the connecting map `Vδ` of the tangent class `τ` of the restriction of that lift
along the canonical identification `A₁' = A[I₁]`. This is clause (iv) of Stacks 07YY with the
cohomology groups of `K ⊗ᴸ -` replaced by the groups `V`. -/
public def GroupsBoundaryCondition (V : ModuleCat.{u} A → ℤ → Type*)
    (Vδ : ∀ {Sq : ShortComplex (ModuleCat.{u} A)} (_ : Sq.ShortExact), V Sq.X₃ 1 → V Sq.X₁ 2)
    (τ : ∀ M : SiteModule A B,
      ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M : Type _) → V M.obj 1)
    (ob : ∀ (A' : Type u) [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A'),
      V D.kernel 2) : Prop :=
  ∀ (A₁ A₂ A₃ : Type u) [CommRing A₁] [CommRing A₂] [CommRing A₃]
    (D₁ : SquareZeroThickening A B S hS toS hA A₁)
    (D₂ : SquareZeroThickening A B S hS toS hA A₂)
    (D₃ : SquareZeroThickening A B S hS toS hA A₃)
    (g₂₁ : SquareZeroThickening.Hom D₂ D₁) (g₃₂ : SquareZeroThickening.Hom D₃ D₂),
    IsShortExactSequence D₁.q D₂.q D₃.q g₂₁.ringHom g₃₂.ringHom →
    ∀ lift₂ : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ D₂.arrow)),
    ∃ (hzero : g₃₂.kernelMap ≫ g₂₁.kernelMap = 0)
      (hSq : (ShortComplex.mk g₃₂.kernelMap g₂₁.kernelMap hzero).ShortExact)
      (hmem : B.Contains (Spec (squareZeroRing A D₁.kernel)))
      (s : A →+* A₁) (ψ : A₂ →+* (squareZeroRing A D₁.kernel : Type u))
      (_hs : g₂₁.ringHom.comp g₃₂.ringHom = s.comp D₃.q)
      (_hψfst : ∀ y : A₂, (ψ y).fst = D₂.q y)
      (_hψsnd : ∀ y : A₂, ((ψ y).snd).1 = g₂₁.ringHom y - s (D₂.q y)),
      letI M₁ : SiteModule A B := ⟨D₁.kernel, hmem⟩
      ∃ (dMap : squareZeroOver A B S hS toS M₁ ⟶ (Over.mk D₂.toS' : BigFppfOver B S hS))
        (lift₁ : (Under.post p).Fiber
          (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M₁)))
        (φ : lift₁.1.right ⟶ lift₂.1.right),
        B.inclusion.map dMap.left = Spec.map (CommRingCat.ofHom ψ) ∧
        squareZeroArrow A B S hS toS hA M₁ ≫ dMap = D₂.arrow ∧
        p.IsStronglyCartesian dMap φ ∧ lift₁.1.hom ≫ φ = lift₂.1.hom ∧
          ob A₃ D₃ = Vδ hSq (τ M₁
            (((tangentFunctor A B S hS toS hA p x hx hp hRS).liftEquiv M₁).symm
              (Quotient.mk _ lift₁)))

/-- **A dual deformation situation from identifications with given groups.** Let `K` be an
object of `D(A)` whose groups `H¹(K ⊗ᴸ M)`, `H²(K ⊗ᴸ M)` are identified with groups `V M 1`,
`V M 2`, naturally in `M` and compatibly with the connecting maps. Suppose the tangent functor of
`x` is identified with `V (-) 1` naturally, and that deformation situations carry obstruction
elements in `V I 2`, functorial, vanishing exactly when `x` lifts, and satisfying the boundary
condition `Deformation.Artin.DualNotion.GroupsBoundaryCondition`. Then there is a dual
deformation situation (Stacks 07YX) with object `x` and complex `K` satisfying clause (iv) of
Stacks 07YY. -/
theorem exists_dualDeformationSituation_of_groups
    (hft : Algebra.FiniteType Λ A) (iΛ : Spec (.of Λ) ⟶ S) [IsOpenImmersion iΛ]
    (hfac : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ iΛ = toS)
    (K : DerivedCategory (ModuleCat.{u} A))
    (V : ModuleCat.{u} A → ℤ → Type*) [∀ M n, AddCommGroup (V M n)]
    (Vmap : ∀ {M N : ModuleCat.{u} A} (_ : M ⟶ N) (n : ℤ), V M n →+ V N n)
    (Vδ : ∀ {Sq : ShortComplex (ModuleCat.{u} A)} (_ : Sq.ShortExact), V Sq.X₃ 1 → V Sq.X₁ 2)
    (Ψ₁ : ∀ M : ModuleCat.{u} A, ((derivedCohomology A K 1).obj M : Type u) ≃+ V M 1)
    (Ψ₂ : ∀ M : ModuleCat.{u} A, ((derivedCohomology A K 2).obj M : Type u) ≃+ V M 2)
    (hΨ₁ : ∀ {M N : ModuleCat.{u} A} (f : M ⟶ N) (c : (derivedCohomology A K 1).obj M),
      Ψ₁ N ((derivedCohomology A K 1).map f c) = Vmap f 1 (Ψ₁ M c))
    (hΨ₂ : ∀ {M N : ModuleCat.{u} A} (f : M ⟶ N) (c : (derivedCohomology A K 2).obj M),
      Ψ₂ N ((derivedCohomology A K 2).map f c) = Vmap f 2 (Ψ₂ M c))
    (hΨδ : ∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact)
      (c : (derivedCohomology A K 1).obj Sq.X₃),
      Ψ₂ Sq.X₁ (boundaryMap A K hSq c) = Vδ hSq (Ψ₁ Sq.X₃ c))
    (τ : ∀ M : SiteModule A B,
      ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M : Type _) ≃+ V M.obj 1)
    (hτ : ∀ {M N : SiteModule A B} (f : M ⟶ N)
      (t : (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M),
      τ N ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map f t) =
        Vmap f.hom 1 (τ M t))
    (ob : ∀ (A' : Type u) [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A'),
      V D.kernel 2)
    (hob₁ : ∀ (A' : Type u) [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A'),
      Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))) ↔ ob A' D = 0)
    (hob₂ : ∀ (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂]
      (D₁ : SquareZeroThickening A B S hS toS hA A₁)
      (D₂ : SquareZeroThickening A B S hS toS hA A₂) (f : SquareZeroThickening.Hom D₁ D₂),
      Vmap f.kernelMap 2 (ob A₁ D₁) = ob A₂ D₂)
    (hV : GroupsBoundaryCondition x hx hp hRS V Vδ (fun M t => τ M t) ob) :
    ∃ sit : DualDeformationSituation A Λ B S hS toS hA X p,
      sit.x = x ∧ sit.K = K ∧ ObstructionBoundaryCondition Λ A B S hS toS hA X p sit := by
  let T := tangentFunctor A B S hS toS hA p x hx hp hRS
  let tangentMap : ∀ M : SiteModule A B,
      (T.functor.obj M : Type _) →ₗ[A] ((derivedCohomology A K 1).obj M.obj : Type u) :=
    fun M =>
      { toFun := fun t => (Ψ₁ M.obj).symm (τ M t)
        map_add' := fun t t' => by simp only [map_add]
        map_smul' := fun a t => by
          have h1 : a • t = T.functor.map (a • 𝟙 M) t := by
            rw [Functor.map_smul, CategoryTheory.Functor.map_id]
            rfl
          rw [h1, hτ, RingHom.id_apply]
          have h2 : (a • 𝟙 M : M ⟶ M).hom = a • 𝟙 M.obj := rfl
          rw [h2, symm_apply_of_natural _ _ (hΨ₁ _), derivedCohomology_smul_apply] }
  let sit : DualDeformationSituation A Λ B S hS toS hA X p :=
    { finiteType := hft
      affineOpen := iΛ
      openImmersion := inferInstance
      factorization := hfac
      x := x
      hx := hx
      fibered := hp
      rsStar := hRS
      K := K
      tangentMap := tangentMap
      tangentBijective := fun M => (Ψ₁ M.obj).symm.bijective.comp (τ M).bijective
      tangentNatural := by
        intro M N f t
        show (Ψ₁ N.obj).symm (τ N (T.functor.map f t)) = _
        rw [hτ, symm_apply_of_natural _ _ (hΨ₁ _)]
        rfl
      obstruction := fun A' _ D => (Ψ₂ D.kernel).symm (ob A' D)
      obstructionNatural := by
        intro A₁ A₂ _ _ D₁ D₂ f
        rw [← symm_apply_of_natural _ _ (hΨ₂ _), hob₂]
      obstruction_iff_lift := by
        intro A' _ D
        rw [hob₁, AddEquiv.map_eq_zero_iff] }
  refine ⟨sit, rfl, rfl, ?_⟩
  intro A₁ A₂ A₃ _ _ _ D₁ D₂ D₃ g₂₁ g₃₂ hexact lift₂
  obtain ⟨hzero, hSq, hmem, s, ψ, hs, hψfst, hψsnd, dMap, lift₁, φ, h₁, h₂, h₃, h₄, h₅⟩ :=
    hV A₁ A₂ A₃ D₁ D₂ D₃ g₂₁ g₃₂ hexact lift₂
  refine ⟨hzero, hSq, hmem, s, ψ, hs, hψfst, hψsnd, dMap, lift₁, φ, h₁, h₂, h₃, h₄, ?_⟩
  show (Ψ₂ D₃.kernel).symm (ob A₃ D₃) = boundaryMap A K hSq ((Ψ₁ D₁.kernel).symm _)
  rw [AddEquiv.symm_apply_eq]
  exact h₅.trans ((hΨδ hSq _).trans (congrArg (Vδ hSq) ((Ψ₁ _).apply_symm_apply _))).symm

end Deformation.Artin.DualNotion
