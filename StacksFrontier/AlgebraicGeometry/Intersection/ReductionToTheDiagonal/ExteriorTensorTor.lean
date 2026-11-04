module

public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
public import Mathlib.Data.Finsupp.SMulWithZero
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import
  StacksFrontier.AlgebraicGeometry.Intersection.ReductionToTheDiagonal.ExteriorTensorBaseChange
public import StacksFrontier.RingTheory.Tor.LongExactSequence

/-!
# Reduction to the diagonal for the higher Tor modules

Let `k` be a field, `A` a commutative `k`-algebra and `M`, `N` two `A`-modules. The exterior
tensor product `M ⊗[k] N` is a module over `A ⊗[k] A`, and `A` is an `A ⊗[k] A`-algebra through
the multiplication map; the reduction to the diagonal identifies

`Tor_i^{A ⊗[k] A}(A, M ⊗[k] N) = Tor_i^A(M, N)` for every `i`.

## Main definitions

* `Stacks.Tor.TorδSecond`: the connecting morphism of the long exact sequence of `Tor` in its
  derived (second) variable, and `Stacks.Tor.TorδSecondIso` the dimension shift it gives.
* `Stacks.Tor.torOneIsoKernel`: `Tor₁(M, X₃)` as the kernel of `M ⊗ X₁ → M ⊗ X₂` when
  `Tor₁(M, X₂)` vanishes.
* `Stacks.Intersection.Diagonal.diagonalTensorModuleIso`: the degree-zero reduction to the
  diagonal in `ModuleCat (A ⊗[k] A)`.
* `Stacks.Intersection.Diagonal.extObj`: `M ⊗[k] N` as an object of `ModuleCat (A ⊗[k] A)`.
* `Stacks.Intersection.Diagonal.extLeftSC`, `Stacks.Intersection.Diagonal.extRightSC`: the
  exterior tensor product of a short complex of `A`-modules with a fixed `A`-module, in either
  variable.
* `Stacks.Intersection.Diagonal.freeπ`: the canonical surjection onto an `A`-module from the free
  module on its underlying set, with kernel `Stacks.Intersection.Diagonal.syzygy`.
* `Stacks.Intersection.Diagonal.extLeftFreeSC`, `Stacks.Intersection.Diagonal.extRightFreeSC`:
  the exterior tensor products of the free-cover sequence with a fixed `A`-module.
* `Stacks.Intersection.Diagonal.freeExteriorEquiv`: the `A ⊗[k] A`-linear isomorphism
  `(ι →₀ A) ⊗[k] (κ →₀ A) ≃ (ι × κ) →₀ (A ⊗[k] A)`.
* `Stacks.Intersection.Diagonal.diagonalTorIso`: a choice of isomorphism
  `Tor_i^{A ⊗[k] A}(A, M ⊗[k] N) ≅ Tor_i^A(M, N)`.

## Main results

* `Stacks.Tor.Tor_composableArrows_exact_second`: the long exact sequence of `Tor` in the
  derived variable, and `Stacks.Tor.Tor_composableArrows_exact_second_zero` its bottom.
* `Stacks.Tor.isZero_torOne`: `Tor₁(M, X₃)` vanishes when `Tor₁(M, X₂)` vanishes and
  `M ⊗ X₁ → M ⊗ X₂` is a monomorphism.
* `Stacks.Intersection.Diagonal.diagonalTensorModuleIso_naturality`: naturality of the
  degree-zero reduction to the diagonal.
* `Stacks.Intersection.Diagonal.isZero_diagonalTor_free`: an exterior tensor product with a free
  `A`-module is acyclic for `A ⊗_{A ⊗[k] A} -`.
* `Stacks.Intersection.Diagonal.nonempty_diagonalTorIso`: the reduction to the diagonal in every
  degree.

## References

* [Stacks Project, Tag 0B0T](https://stacks.math.columbia.edu/tag/0B0T)
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits

universe u

namespace Stacks.Tor

variable {R : Type u} [CommRing R] {S : ShortComplex (ModuleCat.{u} R)}

/-- The connecting morphism `Tor_{n+1}(M, X₃) ⟶ Tor_n(M, X₁)` of the long exact sequence of
`Tor_•(M, -)` in its derived variable, attached to a short exact sequence
`S : 0 → X₁ → X₂ → X₃ → 0`. -/
noncomputable def TorδSecond (hS : S.ShortExact) (M : ModuleCat.{u} R) (n : ℕ) :
    ((Tor (ModuleCat.{u} R) (n + 1)).obj M).obj S.X₃ ⟶
      ((Tor (ModuleCat.{u} R) n).obj M).obj S.X₁ :=
  ((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedδ hS n

open ComposableArrows in
/-- The long exact sequence of `Tor_•(M, -)` in the derived variable: for a short exact sequence
`S : 0 → X₁ → X₂ → X₃ → 0` and every `n`, the sequence
`Tor_{n+1}(M, X₁) → Tor_{n+1}(M, X₂) → Tor_{n+1}(M, X₃) → Tor_n(M, X₁) → Tor_n(M, X₂) →
Tor_n(M, X₃)` is exact. -/
theorem Tor_composableArrows_exact_second (hS : S.ShortExact) (M : ModuleCat.{u} R) (n : ℕ) :
    (mk₅ (((Tor (ModuleCat.{u} R) (n + 1)).obj M).map S.f)
      (((Tor (ModuleCat.{u} R) (n + 1)).obj M).map S.g) (TorδSecond hS M n)
      (((Tor (ModuleCat.{u} R) n).obj M).map S.f)
      (((Tor (ModuleCat.{u} R) n).obj M).map S.g)).Exact :=
  exact_of_δ₀
    ((((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerived_exact hS
      (n + 1)).exact_toComposableArrows)
    (exact_of_δ₀
      ((((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerived_exact_δ₁ hS
        n).exact_toComposableArrows)
      (exact_of_δ₀
        ((((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerived_exact_δ₂ hS
          n).exact_toComposableArrows)
        ((((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerived_exact hS
          n).exact_toComposableArrows)))

/-- The connecting morphism is an isomorphism as soon as both middle terms flanking it vanish. -/
theorem isIso_TorδSecond (hS : S.ShortExact) (M : ModuleCat.{u} R) (n : ℕ)
    (h : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj M).obj S.X₂))
    (h' : IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj S.X₂)) :
    IsIso (TorδSecond hS M n) := by
  have hex := Tor_composableArrows_exact_second hS M n
  have hmono : Mono (TorδSecond hS M n) := (hex.exact' 1 2 3).mono_g (h.eq_of_src _ _)
  have hepi : Epi (TorδSecond hS M n) := (hex.exact' 2 3 4).epi_f (h'.eq_of_tgt _ _)
  exact isIso_of_mono_of_epi _

/-- The dimension shift `Tor_{n+1}(M, X₃) ≅ Tor_n(M, X₁)` in the derived variable, given by the
connecting morphism when both middle terms flanking it vanish. -/
noncomputable def TorδSecondIso (hS : S.ShortExact) (M : ModuleCat.{u} R) (n : ℕ)
    (h : IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj M).obj S.X₂))
    (h' : IsZero (((Tor (ModuleCat.{u} R) n).obj M).obj S.X₂)) :
    ((Tor (ModuleCat.{u} R) (n + 1)).obj M).obj S.X₃ ≅
      ((Tor (ModuleCat.{u} R) n).obj M).obj S.X₁ :=
  haveI := isIso_TorδSecond hS M n h h'
  asIso (TorδSecond hS M n)

/-- The connecting morphism `Tor₁(M, X₃) ⟶ M ⊗ X₁` at the bottom of the long exact sequence of
`Tor_•(M, -)`, with the zeroth derived functor identified with the tensor product. -/
noncomputable def TorδSecondZero (hS : S.ShortExact) (M : ModuleCat.{u} R) :
    ((Tor (ModuleCat.{u} R) 1).obj M).obj S.X₃ ⟶ M ⊗ S.X₁ :=
  TorδSecond hS M 0 ≫
    (((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedZeroIsoSelf.app S.X₁).hom

open ComposableArrows in
/-- The bottom of the long exact sequence of `Tor_•(M, -)`: for a short exact sequence
`S : 0 → X₁ → X₂ → X₃ → 0` the sequence
`Tor₁(M, X₁) → Tor₁(M, X₂) → Tor₁(M, X₃) → M ⊗ X₁ → M ⊗ X₂ → M ⊗ X₃` is exact. -/
theorem Tor_composableArrows_exact_second_zero (hS : S.ShortExact) (M : ModuleCat.{u} R) :
    (mk₅ (((Tor (ModuleCat.{u} R) 1).obj M).map S.f) (((Tor (ModuleCat.{u} R) 1).obj M).map S.g)
      (TorδSecondZero hS M) (M ◁ S.f) (M ◁ S.g)).Exact := by
  refine ComposableArrows.exact_of_iso ?_ (Tor_composableArrows_exact_second hS M 0)
  exact isoMk₅ (Iso.refl _) (Iso.refl _) (Iso.refl _)
    (((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedZeroIsoSelf.app S.X₁)
    (((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedZeroIsoSelf.app S.X₂)
    (((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedZeroIsoSelf.app S.X₃)
    (by cat_disch) (by cat_disch) (Category.id_comp _).symm
    (((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedZeroIsoSelf.hom.naturality S.f)
    (((tensoringLeft (ModuleCat.{u} R)).obj M).leftDerivedZeroIsoSelf.hom.naturality S.g)

/-- The composite `Tor₁(M, X₃) ⟶ M ⊗ X₁ ⟶ M ⊗ X₂` at the bottom of the long exact sequence
vanishes. -/
theorem TorδSecondZero_comp_whiskerLeft (hS : S.ShortExact) (M : ModuleCat.{u} R) :
    TorδSecondZero hS M ≫ M ◁ S.f = 0 :=
  (Tor_composableArrows_exact_second_zero hS M).toIsComplex.zero 2 (by omega)

/-- `Tor₁(M, X₃)` is the kernel of `M ⊗ X₁ → M ⊗ X₂` as soon as `Tor₁(M, X₂)` vanishes. -/
noncomputable def torOneIsoKernel (hS : S.ShortExact) (M : ModuleCat.{u} R)
    (h : IsZero (((Tor (ModuleCat.{u} R) 1).obj M).obj S.X₂)) :
    ((Tor (ModuleCat.{u} R) 1).obj M).obj S.X₃ ≅ kernel (M ◁ S.f) := by
  have hex := Tor_composableArrows_exact_second_zero hS M
  let T : ShortComplex (ModuleCat.{u} R) :=
    ShortComplex.mk (TorδSecondZero hS M) (M ◁ S.f) (TorδSecondZero_comp_whiskerLeft hS M)
  haveI : Mono T.f := (hex.exact' 1 2 3).mono_g (h.eq_of_src _ _)
  have hT : T.Exact := hex.exact' 2 3 4
  exact IsLimit.conePointUniqueUpToIso hT.fIsKernel
    (limit.isLimit (parallelPair (M ◁ S.f) 0))

/-- **`Tor₁(M, X₃)` vanishes** as soon as `Tor₁(M, X₂)` vanishes and `M ⊗ X₁ → M ⊗ X₂` is a
monomorphism. -/
theorem isZero_torOne (hS : S.ShortExact) (M : ModuleCat.{u} R)
    (h : IsZero (((Tor (ModuleCat.{u} R) 1).obj M).obj S.X₂)) (hm : Mono (M ◁ S.f)) :
    IsZero (((Tor (ModuleCat.{u} R) 1).obj M).obj S.X₃) := by
  have : Mono (TorδSecondZero hS M) :=
    ((Tor_composableArrows_exact_second_zero hS M).exact' 1 2 3).mono_g (h.eq_of_src _ _)
  exact IsZero.of_mono_eq_zero (TorδSecondZero hS M) (by
    rw [← cancel_mono (M ◁ S.f), TorδSecondZero_comp_whiskerLeft, zero_comp])

/-- The higher `Tor` modules against a projective module in the derived variable vanish. -/
theorem isZero_Tor_succ_obj_of_projective (M P : ModuleCat.{u} R) [Projective P] (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} R) (n + 1)).obj M).obj P) :=
  Functor.isZero_leftDerived_obj_projective_succ ((tensoringLeft (ModuleCat.{u} R)).obj M) n P

end Stacks.Tor

namespace Stacks.Intersection.Diagonal

open TensorProduct

variable {k A : Type u} [Field k] [CommRing A] [Algebra k A]

attribute [local instance] exteriorModule

attribute [local instance 1100] Module.Free.of_divisionRing

section Comparison

attribute [local instance] diagonalAlgebra diagonalModule diagonalIsScalarTower

variable (M N : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
  [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- Scalars of `A ⊗[k] A` act on `A ⊗[A ⊗[k] A] (M ⊗[k] N)` through the multiplication map. -/
theorem smul_base_tmul (r : A ⊗[k] A) (z : A ⊗[A ⊗[k] A] (M ⊗[k] N)) :
    r • z = (Algebra.TensorProduct.lmul' k r) • z := by
  induction z with
  | zero => simp
  | add x y hx hy => simp only [smul_add, hx, hy]
  | tmul a x =>
      rw [TensorProduct.smul_tmul', TensorProduct.smul_tmul', diagonalAlgebra_smul, smul_eq_mul]

/-- **The degree-zero reduction to the diagonal, as an isomorphism of `A ⊗[k] A`-modules**
`A ⊗[A ⊗[k] A] (M ⊗[k] N) ≃ M ⊗[A] N`, the right-hand side carrying the action of `A ⊗[k] A`
through the multiplication map `A ⊗[k] A → A`. -/
noncomputable def diagonalTensorEquivTensor :
    (A ⊗[A ⊗[k] A] (M ⊗[k] N)) ≃ₗ[A ⊗[k] A] (M ⊗[A] N) where
  toFun := diagonalTensorEquiv M N
  map_add' := (diagonalTensorEquiv M N).map_add
  map_smul' r z := by
    rw [RingHom.id_apply, smul_base_tmul, map_smul, diagonalModule_smul]
  invFun := (diagonalTensorEquiv M N).symm
  left_inv := (diagonalTensorEquiv M N).left_inv
  right_inv := (diagonalTensorEquiv M N).right_inv

/-- The degree-zero reduction to the diagonal as an isomorphism in `ModuleCat (A ⊗[k] A)`:
tensoring the exterior product with the structure module `A` of the diagonal returns the tensor
product over `A`. -/
noncomputable def diagonalTensorModuleIso :
    MonoidalCategory.tensorObj (ModuleCat.of (A ⊗[k] A) A)
        (ModuleCat.of (A ⊗[k] A) (M ⊗[k] N)) ≅
      ModuleCat.of (A ⊗[k] A) (M ⊗[A] N) :=
  (diagonalTensorEquivTensor M N).toModuleIso

variable {M N}
variable {M' N' : Type u} [AddCommGroup M'] [Module k M'] [Module A M'] [IsScalarTower k A M']
  [AddCommGroup N'] [Module k N'] [Module A N'] [IsScalarTower k A N']

/-- A pair of `A`-linear maps induces an `A ⊗[k] A`-linear map of the tensor products over `A`,
both sides carrying the action through the multiplication map. -/
noncomputable def diagonalMap (f : M →ₗ[A] M') (g : N →ₗ[A] N') :
    (M ⊗[A] N) →ₗ[A ⊗[k] A] (M' ⊗[A] N') where
  toFun := TensorProduct.map f g
  map_add' := (TensorProduct.map f g).map_add
  map_smul' r x := by
    rw [RingHom.id_apply, diagonalModule_smul, diagonalModule_smul, map_smul]

/-- **Naturality of the degree-zero reduction to the diagonal**, in `ModuleCat (A ⊗[k] A)`. -/
theorem diagonalTensorModuleIso_naturality (f : M →ₗ[A] M') (g : N →ₗ[A] N') :
    MonoidalCategory.whiskerLeft (ModuleCat.of (A ⊗[k] A) A)
          (ModuleCat.ofHom (exteriorMap (k := k) f g)) ≫ (diagonalTensorModuleIso M' N').hom =
      (diagonalTensorModuleIso M N).hom ≫ ModuleCat.ofHom (diagonalMap (k := k) f g) := by
  ext x
  exact diagonalTensorEquiv_naturality f g x

end Comparison

section ShortExact

variable (W : Type u) [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
variable {X Y Z : Type u} [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X]
  [AddCommGroup Y] [Module k Y] [Module A Y] [IsScalarTower k A Y]
  [AddCommGroup Z] [Module k Z] [Module A Z] [IsScalarTower k A Z]

/-- The exterior tensor product `W ⊗[k] X` of two `A`-modules, as an object of
`ModuleCat (A ⊗[k] A)` carrying the exterior action. -/
noncomputable abbrev extObj (W X : Type u) [AddCommGroup W] [Module k W] [Module A W]
    [IsScalarTower k A W] [AddCommGroup X] [Module k X] [Module A X] [IsScalarTower k A X] :
    ModuleCat.{u} (A ⊗[k] A) :=
  ModuleCat.of (A ⊗[k] A) (W ⊗[k] X)

/-- The exterior tensor product of a short complex of `A`-modules with a fixed `A`-module `W`
in the second variable: `W ⊗[k] X → W ⊗[k] Y → W ⊗[k] Z`, a short complex of
`A ⊗[k] A`-modules. -/
noncomputable def extLeftSC (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (hfg : g ∘ₗ f = 0) :
    ShortComplex (ModuleCat.{u} (A ⊗[k] A)) :=
  ShortComplex.mk (ModuleCat.ofHom (exteriorMap (k := k) (LinearMap.id (R := A) (M := W)) f))
    (ModuleCat.ofHom (exteriorMap (k := k) (LinearMap.id (R := A) (M := W)) g))
    (by
      ext z
      refine TensorProduct.induction_on z ?_ (fun w x ↦ ?_) (fun x y hx hy ↦ ?_)
      · simp
      · have h : g (f x) = 0 := by rw [← LinearMap.comp_apply, hfg, LinearMap.zero_apply]
        simp [h]
      · simp only [map_add, hx, hy])

/-- The exterior tensor product of a short complex of `A`-modules with a fixed `A`-module `W`
in the first variable: `X ⊗[k] W → Y ⊗[k] W → Z ⊗[k] W`. -/
noncomputable def extRightSC (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (hfg : g ∘ₗ f = 0) :
    ShortComplex (ModuleCat.{u} (A ⊗[k] A)) :=
  ShortComplex.mk (ModuleCat.ofHom (exteriorMap (k := k) f (LinearMap.id (R := A) (M := W))))
    (ModuleCat.ofHom (exteriorMap (k := k) g (LinearMap.id (R := A) (M := W))))
    (by
      ext z
      refine TensorProduct.induction_on z ?_ (fun x w ↦ ?_) (fun x y hx hy ↦ ?_)
      · simp
      · have h : g (f x) = 0 := by rw [← LinearMap.comp_apply, hfg, LinearMap.zero_apply]
        simp [h]
      · simp only [map_add, hx, hy])

/-- The first map of `extLeftSC` is `id_W ⊗ f`. -/
@[simp] theorem extLeftSC_f (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (hfg : g ∘ₗ f = 0) :
    (extLeftSC (k := k) W f g hfg).f =
      ModuleCat.ofHom (exteriorMap (k := k) (LinearMap.id (R := A) (M := W)) f) := rfl

/-- The first map of `extRightSC` is `f ⊗ id_W`. -/
@[simp] theorem extRightSC_f (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (hfg : g ∘ₗ f = 0) :
    (extRightSC (k := k) W f g hfg).f =
      ModuleCat.ofHom (exteriorMap (k := k) f (LinearMap.id (R := A) (M := W))) := rfl

/-- The first object of `extLeftSC` is `W ⊗[k] X`. -/
@[simp] theorem extLeftSC_X₁ (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (hfg : g ∘ₗ f = 0) :
    (extLeftSC (k := k) W f g hfg).X₁ = extObj (k := k) W X := rfl

/-- The first object of `extRightSC` is `X ⊗[k] W`. -/
@[simp] theorem extRightSC_X₁ (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (hfg : g ∘ₗ f = 0) :
    (extRightSC (k := k) W f g hfg).X₁ = extObj (k := k) X W := rfl

/-- The middle object of `extLeftSC` is `W ⊗[k] Y`. -/
@[simp] theorem extLeftSC_X₂ (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (hfg : g ∘ₗ f = 0) :
    (extLeftSC (k := k) W f g hfg).X₂ = extObj (k := k) W Y := rfl

/-- The middle object of `extRightSC` is `Y ⊗[k] W`. -/
@[simp] theorem extRightSC_X₂ (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (hfg : g ∘ₗ f = 0) :
    (extRightSC (k := k) W f g hfg).X₂ = extObj (k := k) Y W := rfl

/-- The last object of `extLeftSC` is `W ⊗[k] Z`. -/
@[simp] theorem extLeftSC_X₃ (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (hfg : g ∘ₗ f = 0) :
    (extLeftSC (k := k) W f g hfg).X₃ = extObj (k := k) W Z := rfl

/-- The last object of `extRightSC` is `Z ⊗[k] W`. -/
@[simp] theorem extRightSC_X₃ (f : X →ₗ[A] Y) (g : Y →ₗ[A] Z) (hfg : g ∘ₗ f = 0) :
    (extRightSC (k := k) W f g hfg).X₃ = extObj (k := k) Z W := rfl

/-- The exterior tensor product of a short exact sequence of `A`-modules with a fixed `A`-module,
in the second variable, is short exact. -/
theorem extLeftSC_shortExact {f : X →ₗ[A] Y} {g : Y →ₗ[A] Z} (hfg : g ∘ₗ f = 0)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g) (hex : Function.Exact f g) :
    (extLeftSC (k := k) W f g hfg).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · exact Module.Flat.lTensor_exact (R := k) W (f := f.restrictScalars k)
      (g := g.restrictScalars k) hex
  · exact Module.Flat.lTensor_preserves_injective_linearMap (R := k) (M := W)
      (f.restrictScalars k) hinj
  · exact LinearMap.lTensor_surjective (R := k) W (g := g.restrictScalars k) hsurj

/-- The exterior tensor product of a short exact sequence of `A`-modules with a fixed `A`-module,
in the first variable, is short exact. -/
theorem extRightSC_shortExact {f : X →ₗ[A] Y} {g : Y →ₗ[A] Z} (hfg : g ∘ₗ f = 0)
    (hinj : Function.Injective f) (hsurj : Function.Surjective g) (hex : Function.Exact f g) :
    (extRightSC (k := k) W f g hfg).ShortExact := by
  refine ModuleCat.shortComplex_shortExact _ ?_ ?_ ?_
  · exact Module.Flat.rTensor_exact (R := k) W (f := f.restrictScalars k)
      (g := g.restrictScalars k) hex
  · exact Module.Flat.rTensor_preserves_injective_linearMap (R := k) (M := W)
      (f.restrictScalars k) hinj
  · exact LinearMap.rTensor_surjective (R := k) W (g := g.restrictScalars k) hsurj

end ShortExact

section FreeCover

variable (M : Type u) [AddCommGroup M] [Module A M]

/-- The canonical surjection onto an `A`-module from the free `A`-module on its underlying
set. -/
noncomputable def freeπ : (M →₀ A) →ₗ[A] M := Finsupp.linearCombination A id

/-- The canonical map `freeπ M : (M →₀ A) → M` is surjective. -/
theorem freeπ_surjective : Function.Surjective (freeπ (A := A) M) :=
  fun m ↦ ⟨Finsupp.single m 1, by simp [freeπ]⟩

/-- The syzygy module of an `A`-module: the kernel of the canonical surjection from the free
module on its underlying set. -/
noncomputable abbrev syzygy : Submodule A (M →₀ A) := LinearMap.ker (freeπ (A := A) M)

/-- The composite of the inclusion of `syzygy M` with `freeπ M` is zero. -/
theorem freeπ_comp_syzygy_subtype : freeπ (A := A) M ∘ₗ (syzygy M).subtype = 0 := by
  ext x
  exact LinearMap.mem_ker.mp x.2

/-- The sequence `syzygy M → (M →₀ A) → M` is exact. -/
theorem exact_syzygy_subtype_freeπ :
    Function.Exact (syzygy M).subtype (freeπ (A := A) M) :=
  LinearMap.exact_subtype_ker_map _

end FreeCover

section FreeSES

variable (W M : Type u) [AddCommGroup W] [Module k W] [Module A W] [IsScalarTower k A W]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- The free-cover short exact sequence of `M`, tensored over the ground field with a fixed
`A`-module `W` in the first variable:
`0 → syzygy M ⊗[k] W → (M →₀ A) ⊗[k] W → M ⊗[k] W → 0`. -/
noncomputable def extRightFreeSC : ShortComplex (ModuleCat.{u} (A ⊗[k] A)) :=
  extRightSC (k := k) (A := A) (W := W) (X := ↥(syzygy (A := A) M)) (Y := (M →₀ A)) (Z := M)
    ((syzygy M).subtype) (freeπ M) (freeπ_comp_syzygy_subtype M)

/-- The free-cover short exact sequence of `M`, tensored over the ground field with a fixed
`A`-module `W` in the second variable:
`0 → W ⊗[k] syzygy M → W ⊗[k] (M →₀ A) → W ⊗[k] M → 0`. -/
noncomputable def extLeftFreeSC : ShortComplex (ModuleCat.{u} (A ⊗[k] A)) :=
  extLeftSC (k := k) (A := A) (W := W) (X := ↥(syzygy (A := A) M)) (Y := (M →₀ A)) (Z := M)
    ((syzygy M).subtype) (freeπ M) (freeπ_comp_syzygy_subtype M)

/-- The short complex `extRightFreeSC W M` is short exact. -/
theorem extRightFreeSC_shortExact : (extRightFreeSC (k := k) (A := A) W M).ShortExact :=
  extRightSC_shortExact (k := k) (A := A) (W := W) (X := ↥(syzygy (A := A) M))
    (Y := (M →₀ A)) (Z := M) (freeπ_comp_syzygy_subtype M) (Submodule.injective_subtype _)
    (freeπ_surjective M) (exact_syzygy_subtype_freeπ M)

/-- The short complex `extLeftFreeSC W M` is short exact. -/
theorem extLeftFreeSC_shortExact : (extLeftFreeSC (k := k) (A := A) W M).ShortExact :=
  extLeftSC_shortExact (k := k) (A := A) (W := W) (X := ↥(syzygy (A := A) M))
    (Y := (M →₀ A)) (Z := M) (freeπ_comp_syzygy_subtype M) (Submodule.injective_subtype _)
    (freeπ_surjective M) (exact_syzygy_subtype_freeπ M)

/-- The first object of `extRightFreeSC W M` is `syzygy M ⊗[k] W`. -/
@[simp] theorem extRightFreeSC_X₁ :
    (extRightFreeSC (k := k) (A := A) W M).X₁ = extObj (k := k) ↥(syzygy (A := A) M) W := rfl

/-- The middle object of `extRightFreeSC W M` is `(M →₀ A) ⊗[k] W`. -/
@[simp] theorem extRightFreeSC_X₂ :
    (extRightFreeSC (k := k) (A := A) W M).X₂ = extObj (k := k) (M →₀ A) W := rfl

/-- The last object of `extRightFreeSC W M` is `M ⊗[k] W`. -/
@[simp] theorem extRightFreeSC_X₃ :
    (extRightFreeSC (k := k) (A := A) W M).X₃ = extObj (k := k) M W := rfl

/-- The first map of `extRightFreeSC W M` is the inclusion of `syzygy M` tensored with `id_W`. -/
@[simp] theorem extRightFreeSC_f : (extRightFreeSC (k := k) (A := A) W M).f =
    ModuleCat.ofHom (exteriorMap (k := k) ((syzygy M).subtype)
      (LinearMap.id (R := A) (M := W))) := rfl

/-- The first object of `extLeftFreeSC W M` is `W ⊗[k] syzygy M`. -/
@[simp] theorem extLeftFreeSC_X₁ :
    (extLeftFreeSC (k := k) (A := A) W M).X₁ = extObj (k := k) W ↥(syzygy (A := A) M) := rfl

/-- The middle object of `extLeftFreeSC W M` is `W ⊗[k] (M →₀ A)`. -/
@[simp] theorem extLeftFreeSC_X₂ :
    (extLeftFreeSC (k := k) (A := A) W M).X₂ = extObj (k := k) W (M →₀ A) := rfl

/-- The last object of `extLeftFreeSC W M` is `W ⊗[k] M`. -/
@[simp] theorem extLeftFreeSC_X₃ :
    (extLeftFreeSC (k := k) (A := A) W M).X₃ = extObj (k := k) W M := rfl

/-- The first map of `extLeftFreeSC W M` is `id_W` tensored with the inclusion of `syzygy M`. -/
@[simp] theorem extLeftFreeSC_f : (extLeftFreeSC (k := k) (A := A) W M).f =
    ModuleCat.ofHom (exteriorMap (k := k) (LinearMap.id (R := A) (M := W))
      ((syzygy M).subtype)) := rfl

end FreeSES

section FreeExterior

variable (ι κ : Type u)

/-- **The exterior tensor product of two free `A`-modules is a free `A ⊗[k] A`-module.**
It matches `single i a ⊗ single j b` with `single (i, j) (a ⊗ b)`. -/
noncomputable def freeExteriorEquiv :
    ((ι →₀ A) ⊗[k] (κ →₀ A)) ≃ₗ[A ⊗[k] A] ((ι × κ) →₀ (A ⊗[k] A)) where
  toFun := finsuppTensorFinsupp k A A A ι κ
  map_add' := map_add _
  map_smul' r z := by
    rw [RingHom.id_apply]
    induction r with
    | zero =>
        have h : (0 : A ⊗[k] A) • z = 0 := zero_smul _ _
        rw [h, map_zero, zero_smul]
    | add r r' hr hr' =>
        have h : (r + r') • z = r • z + r' • z := add_smul _ _ _
        rw [h, map_add, hr, hr', add_smul]
    | tmul x y =>
        induction z with
        | zero =>
            have h : (x ⊗ₜ[k] y) • (0 : (ι →₀ A) ⊗[k] (κ →₀ A)) = 0 := smul_zero _
            rw [h, map_zero, smul_zero]
        | add z z' hz hz' =>
            have h : (x ⊗ₜ[k] y) • (z + z') = (x ⊗ₜ[k] y) • z + (x ⊗ₜ[k] y) • z' :=
              smul_add _ _ _
            rw [h, map_add, map_add, hz, hz', smul_add]
        | tmul f g =>
            rw [exteriorModule_smul_tmul]
            refine Finsupp.ext fun ⟨i, j⟩ ↦ ?_
            simp [Finsupp.smul_apply, Algebra.TensorProduct.tmul_mul_tmul]
  invFun := (finsuppTensorFinsupp k A A A ι κ).symm
  left_inv := (finsuppTensorFinsupp k A A A ι κ).left_inv
  right_inv := (finsuppTensorFinsupp k A A A ι κ).right_inv

/-- The exterior tensor product of two free `A`-modules is projective over `A ⊗[k] A`. -/
theorem projective_freeExterior :
    Module.Projective (A ⊗[k] A) ((ι →₀ A) ⊗[k] (κ →₀ A)) :=
  Module.Projective.of_equiv (freeExteriorEquiv (k := k) ι κ).symm

end FreeExterior

section Acyclic

attribute [local instance] diagonalAlgebra diagonalModule diagonalIsScalarTower

/-- The middle term of `extRightFreeSC (ι →₀ A) M` has vanishing positive-degree `Tor`. -/
private theorem isZero_tor_extRightFreeSC_X₂ (ι M : Type u) [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] (n : ℕ) :
    IsZero (((Tor (ModuleCat.{u} (A ⊗[k] A)) (n + 1)).obj (ModuleCat.of (A ⊗[k] A) A)).obj
      (extRightFreeSC (k := k) (A := A) (ι →₀ A) M).X₂) := by
  have := projective_freeExterior (k := k) (A := A) M ι
  rw [extRightFreeSC_X₂]
  exact Stacks.Tor.isZero_Tor_succ_obj_of_projective _ _ n

/-- **The exterior tensor product with a free `A`-module is acyclic for `A ⊗_{A ⊗_k A} -`.**
For every `A`-module `M`, every index type `ι` and every `j`, the module
`Tor_{j+1}^{A ⊗_k A}(A, M ⊗_k (ι →₀ A))` vanishes. -/
theorem isZero_diagonalTor_free (ι : Type u) (j : ℕ) :
    ∀ (M : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M],
      IsZero (((Tor (ModuleCat.{u} (A ⊗[k] A)) (j + 1)).obj (ModuleCat.of (A ⊗[k] A) A)).obj
        (extObj (k := k) M (ι →₀ A))) := by
  induction j with
  | zero =>
      intro M _ _ _ _
      rw [← extRightFreeSC_X₃ (k := k) (A := A) (ι →₀ A) M]
      refine Stacks.Tor.isZero_torOne (extRightFreeSC_shortExact (k := k) (A := A) (ι →₀ A) M)
        (ModuleCat.of (A ⊗[k] A) A) (isZero_tor_extRightFreeSC_X₂ ι M 0) ?_
      have : Mono (ModuleCat.ofHom (diagonalMap (k := k) ((syzygy M).subtype)
          (LinearMap.id (R := A) (M := (ι →₀ A))))) := by
        rw [ModuleCat.mono_iff_injective]
        exact Module.Flat.rTensor_preserves_injective_linearMap (R := A) (M := (ι →₀ A))
          _ (Submodule.injective_subtype _)
      change Mono (MonoidalCategory.whiskerLeft (ModuleCat.of (A ⊗[k] A) A)
        (ModuleCat.ofHom (exteriorMap (k := k) ((syzygy M).subtype)
          (LinearMap.id (R := A) (M := (ι →₀ A))))))
      rw [(Iso.eq_comp_inv _).2 (diagonalTensorModuleIso_naturality (k := k)
        ((syzygy M).subtype) (LinearMap.id (R := A) (M := (ι →₀ A))))]
      infer_instance
  | succ j ih =>
      intro M _ _ _ _
      rw [← extRightFreeSC_X₃ (k := k) (A := A) (ι →₀ A) M]
      refine IsZero.of_iso ?_ (Stacks.Tor.TorδSecondIso
        (extRightFreeSC_shortExact (k := k) (A := A) (ι →₀ A) M) (ModuleCat.of (A ⊗[k] A) A) (j + 1)
        (isZero_tor_extRightFreeSC_X₂ ι M (j + 1)) (isZero_tor_extRightFreeSC_X₂ ι M j))
      rw [extRightFreeSC_X₁]
      exact ih ↥(syzygy M)

end Acyclic

section Main

attribute [local instance] diagonalAlgebra diagonalModule diagonalIsScalarTower

/-- An `A`-module read as an `A ⊗[k] A`-module through the multiplication map, the restriction of
scalars along `Algebra.TensorProduct.lmul'`. -/
noncomputable abbrev diagonalRestrict : ModuleCat.{u} A ⥤ ModuleCat.{u} (A ⊗[k] A) :=
  ModuleCat.restrictScalars (Algebra.TensorProduct.lmul' k (S := A)).toRingHom

/-- **Reduction to the diagonal in all degrees, in affine form.**
For a field `k`, a commutative `k`-algebra `A` and `A`-modules `M`, `N` there is, in every
degree `i`, an isomorphism

`Tor_i^{A ⊗[k] A}(A, M ⊗[k] N) ≅ Tor_i^A(M, N)`

of `A ⊗[k] A`-modules, the right-hand side carrying the action through the multiplication map
`A ⊗[k] A → A`. On `Spec A × Spec A` the left-hand side is
`Tor_i^{𝒪_{X × X}}(𝒪_Δ, pr_1^*M ⊗ pr_2^*N)` and the right-hand side the pushforward of
`Tor_i^{𝒪_X}(M, N)` along the diagonal. -/
theorem nonempty_diagonalTorIso (i : ℕ) :
    ∀ (M N : Type u) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
      [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N],
      Nonempty (((Tor (ModuleCat.{u} (A ⊗[k] A)) i).obj (ModuleCat.of (A ⊗[k] A) A)).obj
          (extObj (k := k) M N) ≅
        (diagonalRestrict (k := k) (A := A)).obj
          (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).obj (ModuleCat.of A N))) := by
  induction i with
  | zero =>
      intro M N _ _ _ _ _ _ _ _
      exact ⟨(((tensoringLeft (ModuleCat.{u} (A ⊗[k] A))).obj
            (ModuleCat.of (A ⊗[k] A) A)).leftDerivedZeroIsoSelf.app (extObj (k := k) M N)) ≪≫
          diagonalTensorModuleIso M N ≪≫
          ((diagonalRestrict (k := k) (A := A)).mapIso
            (((tensoringLeft (ModuleCat.{u} A)).obj
              (ModuleCat.of A M)).leftDerivedZeroIsoSelf.app (ModuleCat.of A N))).symm⟩
  | succ i ih =>
      intro M N _ _ _ _ _ _ _ _
      have hS := extLeftFreeSC_shortExact (k := k) (A := A) M N
      have hS' := LinearMap.shortExact_shortComplexKer (freeπ_surjective (A := A) N)
      rw [← extLeftFreeSC_X₃ (k := k) (A := A) M N]
      cases i with
      | zero =>
          exact ⟨Stacks.Tor.torOneIsoKernel hS (ModuleCat.of (A ⊗[k] A) A)
              (by rw [extLeftFreeSC_X₂]; exact isZero_diagonalTor_free N 0 M) ≪≫
            Limits.kernel.mapIso _
              ((diagonalRestrict (k := k) (A := A)).map
                (MonoidalCategory.whiskerLeft (ModuleCat.of A M)
                  ((freeπ (A := A) N).shortComplexKer.f)))
              (diagonalTensorModuleIso M ↥(syzygy (A := A) N)) (diagonalTensorModuleIso M (N →₀ A))
              (diagonalTensorModuleIso_naturality (k := k) (LinearMap.id (R := A) (M := M))
                ((syzygy N).subtype)) ≪≫
            (Limits.PreservesKernel.iso (diagonalRestrict (k := k) (A := A))
              (MonoidalCategory.whiskerLeft (ModuleCat.of A M)
                ((freeπ (A := A) N).shortComplexKer.f))).symm ≪≫
            (diagonalRestrict (k := k) (A := A)).mapIso
              (Stacks.Tor.torOneIsoKernel hS' (ModuleCat.of A M)
                (Stacks.Tor.isZero_Tor_succ_obj_of_projective _ _ 0)).symm⟩
      | succ j =>
          obtain ⟨e⟩ := ih M ↥(syzygy (A := A) N)
          refine ⟨Stacks.Tor.TorδSecondIso hS (ModuleCat.of (A ⊗[k] A) A) (j + 1)
              (by rw [extLeftFreeSC_X₂]; exact isZero_diagonalTor_free N (j + 1) M)
              (by rw [extLeftFreeSC_X₂]; exact isZero_diagonalTor_free N j M) ≪≫ ?_⟩
          rw [extLeftFreeSC_X₁]
          exact e ≪≫ ((diagonalRestrict (k := k) (A := A)).mapIso
            (Stacks.Tor.TorδSecondIso hS' (ModuleCat.of A M) (j + 1)
              (Stacks.Tor.isZero_Tor_succ_obj_of_projective _ _ (j + 1))
              (Stacks.Tor.isZero_Tor_succ_obj_of_projective _ _ j))).symm

/-- A choice of isomorphism `Tor_i^{A ⊗[k] A}(A, M ⊗[k] N) ≅ Tor_i^A(M, N)` of
`A ⊗[k] A`-modules. -/
noncomputable def diagonalTorIso (i : ℕ) (M N : Type u) [AddCommGroup M] [Module k M]
    [Module A M] [IsScalarTower k A M] [AddCommGroup N] [Module k N] [Module A N]
    [IsScalarTower k A N] :
    ((Tor (ModuleCat.{u} (A ⊗[k] A)) i).obj (ModuleCat.of (A ⊗[k] A) A)).obj
        (extObj (k := k) M N) ≅
      (diagonalRestrict (k := k) (A := A)).obj
        (((Tor (ModuleCat.{u} A) i).obj (ModuleCat.of A M)).obj (ModuleCat.of A N)) :=
  (nonempty_diagonalTorIso i M N).some

end Main

end Stacks.Intersection.Diagonal

end
