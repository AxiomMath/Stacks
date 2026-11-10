module

public import StacksFrontier.Deformation.Artin.Obstruction.DualNotion

/-!
# Dual deformation situations from a deformation theory valued in a pair of functors

Situation 07YX of [Stacks] presents the deformation theory of an object `x` by one complex `K`
of `A`-modules: the tangent functor is `H¹(K ⊗ᴸ_A −)`, the obstructions live in
`H²(K ⊗ᴸ_A I)`. In practice the deformation theory is first computed in other terms — in the
first proof of [Stacks, Tag 08WA] and in [Stacks, Remark 0D1P] as `Ext`-groups
`Ext^i_{𝒪_X}(E, 𝒢 ⊗ f^*M)` for `i = 1, 2` — and a perfect `K` is produced afterwards by
[Stacks, Tag 08JR], together with functorial isomorphisms
`H^i(K ⊗ᴸ_A M) ≅ Ext^i_{𝒪_X}(E, 𝒢 ⊗ f^*M)` for `i ≤ 2` compatible with boundary maps. The source
then says: "This object `K`, together with the displayed identifications above gives us a datum
as in Situation 07YX", and checks condition (iv) of [Stacks, Tag 07YY] on the `Ext` side.

This file makes that sentence a construction. A *functor deformation theory* of `x` is the data
of Situation 07YX with the two functors `H¹(K ⊗ᴸ_A −)`, `H²(K ⊗ᴸ_A −)` and their connecting map
replaced by an arbitrary pair of functors `T¹, T²` of `A`-modules with a connecting map `δ`
attached to every short exact sequence, including condition (iv) phrased with `δ`. Given a
complex `K` and natural isomorphisms `H^i(K ⊗ᴸ_A −) ≅ T^i` for `i = 1, 2` carrying the
connecting map of `K` to `δ`, the theory transports to a dual deformation situation with complex
`K`, and condition (iv) transports with it.

## Main definitions

* `FunctorDeformationTheory`: a deformation theory of `x` valued in a pair of functors.
* `FunctorDeformationTheory.toDualDeformationSituation`: its transport to a dual deformation
  situation with complex `K`.

## Main results

* `FunctorDeformationTheory.obstructionBoundaryCondition_toDualDeformationSituation`: condition
  (iv) of [Stacks, Tag 07YY] holds for the transported situation.

## References

* [Stacks Project, Tag 07YX](https://stacks.math.columbia.edu/tag/07YX)
* [Stacks Project, Tag 07YY](https://stacks.math.columbia.edu/tag/07YY)
* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

universe u v w

attribute [local instance 10000] HasDerivedCategory.standard

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
  (X : Type v) [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA) (fibered : p.IsFiberedInGroupoids)
  (rsStar : SatisfiesRSStar B S hS p fibered)

/-- **A deformation theory of `x` valued in a pair of functors.** The data of Situation 07YX
together with condition (iv) of [Stacks, Tag 07YY], with `H¹(K ⊗ᴸ_A −)`, `H²(K ⊗ᴸ_A −)` and
their connecting map replaced by functors `T¹`, `T²` of `A`-modules and a connecting map
`δ : T¹(M₃) ⟶ T²(M₁)` for every short exact sequence `0 → M₁ → M₂ → M₃ → 0`: an isomorphism of
the tangent functor with `T¹`, obstruction elements in `T²(I)` functorial in the deformation
situation and vanishing exactly when `x` lifts, and the obstruction of the smallest member of a
short exact sequence of deformation situations computed by `δ` from a lift over the middle
one. -/
public structure FunctorDeformationTheory where
  /-- The functor carrying the tangent spaces, `Ext¹_{𝒪_X}(E, 𝒢 ⊗ f^*−)` in the source. -/
  T₁ : ModuleCat.{u} A ⥤ ModuleCat.{u} A
  /-- The functor carrying the obstructions, `Ext²_{𝒪_X}(E, 𝒢 ⊗ f^*−)` in the source. -/
  T₂ : ModuleCat.{u} A ⥤ ModuleCat.{u} A
  /-- The connecting map of a short exact sequence. -/
  δ : ∀ {Sq : ShortComplex (ModuleCat.{u} A)}, Sq.ShortExact → (T₁.obj Sq.X₃ ⟶ T₂.obj Sq.X₁)
  /-- The transformation `T_x(−) → T¹(−)`. -/
  tangentMap : ∀ M : SiteModule A B,
    ((tangentFunctor A B S hS toS hA p x hx fibered rsStar).functor.obj M : Type _) →ₗ[A]
      (T₁.obj M.obj : Type _)
  /-- It is an isomorphism. -/
  tangentBijective : ∀ M, Function.Bijective (tangentMap M)
  /-- It is a transformation of functors. -/
  tangentNatural : ∀ {M N : SiteModule A B} (f : M ⟶ N)
    (z : (tangentFunctor A B S hS toS hA p x hx fibered rsStar).functor.obj M),
    tangentMap N ((tangentFunctor A B S hS toS hA p x hx fibered rsStar).functor.map f z) =
      T₁.map f.hom (tangentMap M z)
  /-- The obstruction element of a deformation situation. -/
  obstruction : ∀ (A' : Type u) [CommRing A'] (D : SquareZeroThickening A B S hS toS hA A'),
    T₂.obj D.kernel
  /-- Obstruction elements are carried to obstruction elements. -/
  obstructionNatural : ∀ (A₁ A₂ : Type u) [CommRing A₁] [CommRing A₂]
    (D₁ : SquareZeroThickening A B S hS toS hA A₁)
    (D₂ : SquareZeroThickening A B S hS toS hA A₂) (f : SquareZeroThickening.Hom D₁ D₂),
    (T₂.map f.kernelMap) (obstruction A₁ D₁) = obstruction A₂ D₂
  /-- The obstruction vanishes exactly when a lift exists. -/
  obstruction_iff_lift : ∀ (A' : Type u) [CommRing A']
    (D : SquareZeroThickening A B S hS toS hA A'),
    Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))) ↔ obstruction A' D = 0
  /-- Condition (iv) of [Stacks, Tag 07YY], phrased with `δ`: for a short exact sequence of
  deformation situations and a lift of `x` over the middle one, the obstruction element of the
  smallest one is `δ` of the tangent class of the restriction of that lift along the canonical
  identification `A₁' = A[I₁]`. -/
  boundary : ∀ (A₁ A₂ A₃ : Type u) [CommRing A₁] [CommRing A₂] [CommRing A₃]
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
          obstruction A₃ D₃ =
            δ hSq (tangentMap M₁
              (((tangentFunctor A B S hS toS hA p x hx fibered rsStar).liftEquiv M₁).symm
                (Quotient.mk _ lift₁)))

namespace FunctorDeformationTheory

variable {A B S hS toS hA X p x hx fibered rsStar}
variable (Λ : Type u) [CommRing Λ] [Algebra Λ A] [IsLocallyNoetherian S]
  (T : FunctorDeformationTheory A B S hS toS hA X p x hx fibered rsStar)
  (K : DerivedCategory (ModuleCat.{u} A))
  (e₁ : derivedCohomology A K 1 ≅ T.T₁) (e₂ : derivedCohomology A K 2 ≅ T.T₂)

omit [IsLocallyNoetherian S] in
/-- The inverse comparison carries `δ` to the connecting map of `K`, once the forward one does. -/
theorem boundaryMap_inv_apply
    (he : ∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact),
      boundaryMap A K hSq ≫ e₂.hom.app Sq.X₁ = e₁.hom.app Sq.X₃ ≫ T.δ hSq)
    {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact) (y : T.T₁.obj Sq.X₃) :
    boundaryMap A K hSq (e₁.inv.app Sq.X₃ y) = e₂.inv.app Sq.X₁ (T.δ hSq y) := by
  have h : boundaryMap A K hSq = e₁.hom.app Sq.X₃ ≫ T.δ hSq ≫ e₂.inv.app Sq.X₁ := by
    rw [← reassoc_of% (he hSq)]
    simp
  rw [h]
  change e₂.inv.app Sq.X₁ (T.δ hSq ((e₁.inv.app Sq.X₃ ≫ e₁.hom.app Sq.X₃) y)) = _
  rw [Iso.inv_hom_id_app]
  rfl

/-- **The dual deformation situation of a functor deformation theory.** A complex `K` with
natural isomorphisms `H^i(K ⊗ᴸ_A −) ≅ T^i` for `i = 1, 2` turns a deformation theory of `x`
valued in `(T¹, T²)` into a dual deformation situation (Situation 07YX) with complex `K`: the
tangent isomorphism and the obstruction elements are carried across the inverse isomorphisms. -/
public def toDualDeformationSituation (finiteType : Algebra.FiniteType Λ A)
    (affineOpen : Spec (.of Λ) ⟶ S) (openImmersion : IsOpenImmersion affineOpen)
    (factorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS) :
    DualDeformationSituation A Λ B S hS toS hA X p where
  finiteType := finiteType
  affineOpen := affineOpen
  openImmersion := openImmersion
  factorization := factorization
  x := x
  hx := hx
  fibered := fibered
  rsStar := rsStar
  K := K
  tangentMap M := (e₁.inv.app M.obj).hom ∘ₗ T.tangentMap M
  tangentBijective M :=
    (e₁.app M.obj).symm.toLinearEquiv.bijective.comp (T.tangentBijective M)
  tangentNatural {M N} f z := by
    change e₁.inv.app N.obj (T.tangentMap N _) = _
    rw [T.tangentNatural f z]
    change (T.T₁.map f.hom ≫ e₁.inv.app N.obj) (T.tangentMap M z) = _
    rw [e₁.inv.naturality]
    rfl
  obstruction A' _ D := e₂.inv.app D.kernel (T.obstruction A' D)
  obstructionNatural A₁ A₂ _ _ D₁ D₂ f := by
    change (e₂.inv.app D₁.kernel ≫ (derivedCohomology A K 2).map f.kernelMap)
      (T.obstruction A₁ D₁) = _
    rw [← e₂.inv.naturality]
    change e₂.inv.app D₂.kernel ((T.T₂.map f.kernelMap) (T.obstruction A₁ D₁)) = _
    rw [T.obstructionNatural]
  obstruction_iff_lift A' _ D := by
    rw [T.obstruction_iff_lift]
    refine ⟨fun h => by rw [h, map_zero], fun h => ?_⟩
    have hinj : Function.Injective (e₂.inv.app D.kernel) :=
      (e₂.app D.kernel).symm.toLinearEquiv.injective
    exact hinj (h.trans (map_zero _).symm)

/-- **Condition (iv) transports.** If the comparison isomorphisms carry the connecting map of
`K` to `δ`, then the dual deformation situation of a functor deformation theory satisfies
condition (iv) of [Stacks, Tag 07YY]. -/
public theorem obstructionBoundaryCondition_toDualDeformationSituation
    (finiteType : Algebra.FiniteType Λ A)
    (affineOpen : Spec (.of Λ) ⟶ S) (openImmersion : IsOpenImmersion affineOpen)
    (factorization : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ affineOpen = toS)
    (he : ∀ {Sq : ShortComplex (ModuleCat.{u} A)} (hSq : Sq.ShortExact),
      boundaryMap A K hSq ≫ e₂.hom.app Sq.X₁ = e₁.hom.app Sq.X₃ ≫ T.δ hSq) :
    DualNotion.ObstructionBoundaryCondition Λ A B S hS toS hA X p
      (T.toDualDeformationSituation Λ K e₁ e₂ finiteType affineOpen openImmersion
        factorization) := by
  intro A₁ A₂ A₃ _ _ _ D₁ D₂ D₃ g₂₁ g₃₂ hses lift₂
  obtain ⟨hzero, hSq, hmem, s, ψ, hs, hψfst, hψsnd, dMap, lift₁, φ, h₁, h₂, h₃, h₄, h₅⟩ :=
    T.boundary A₁ A₂ A₃ D₁ D₂ D₃ g₂₁ g₃₂ hses lift₂
  refine ⟨hzero, hSq, hmem, s, ψ, hs, hψfst, hψsnd, dMap, lift₁, φ, h₁, h₂, h₃, h₄, ?_⟩
  change e₂.inv.app D₃.kernel (T.obstruction A₃ D₃) = _
  rw [h₅]
  exact (T.boundaryMap_inv_apply K e₁ e₂ he hSq _).symm

end FunctorDeformationTheory

end Deformation.Artin

end
