module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.ExternalTensor.Basic
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafUnitSections
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.ProductIdealGenerators
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.SubmoduleFactorAffine

/-!
# The product of two ideal sheaves is a quotient of the tensor product

Let `X` be a scheme and let `K`, `K'` be quasi-coherent sheaves of ideals on `X`. Multiplication
of sections is a morphism of `𝒪_X`-modules

`Kⁿ ⊗_{𝒪_X} K'ⁿ ⟶ 𝒪_X`

whose image is the subsheaf `(K K')ⁿ`, so it factors through an epimorphism

`Kⁿ ⊗_{𝒪_X} K'ⁿ ⟶ (K K')ⁿ`.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealProduct.tensorModules`: the tensor product of Tag 01CA, typed
  as an object of `AlgebraicGeometry.Scheme.Modules`.
* `Stacks.AlgebraicGeometry.IdealProduct.mulToStructure`: multiplication of sections, as a
  morphism `A ⊗_{𝒪_X} B ⟶ 𝒪_X` attached to a pair of morphisms `A ⟶ 𝒪_X`, `B ⟶ 𝒪_X`.
* `Stacks.AlgebraicGeometry.IdealProduct.idealPowMul`: the resulting morphism
  `Kⁿ ⊗_{𝒪_X} K'ⁿ ⟶ (K K')ⁿ`, and
  `Stacks.AlgebraicGeometry.IdealProduct.idealPowMulOfHom` its composition with a pair of
  morphisms onto the two factors.

## Main results

* `Stacks.AlgebraicGeometry.IdealProduct.mulToStructure_app_toTensorSheafSection`:
  multiplication of sections on a local pure tensor, `a ⊗ b ↦ φ(a) ψ(b)`.
* `Stacks.AlgebraicGeometry.IdealProduct.idealPowMul_ι`: the factorization composed with the
  inclusion of `(K K')ⁿ` into `𝒪_X` is multiplication of sections.
* `Stacks.AlgebraicGeometry.IdealProduct.epi_idealPowMul`: **the morphism
  `Kⁿ ⊗_{𝒪_X} K'ⁿ ⟶ (K K')ⁿ` is an epimorphism.**
* `Stacks.AlgebraicGeometry.IdealProduct.epi_idealPowMulOfHom`: a quotient of `Kⁿ` and a
  quotient of `K'ⁿ` give a quotient of `(K K')ⁿ`.
* `Stacks.AlgebraicGeometry.IdealProduct.epi_idealPowMul_externalProduct`: the same for the
  product ideal sheaf `pr₁^*𝓘 · pr₂^*𝓘'` on a fibre product, which is the shape in which
  [Stacks, Tag 0FZ0] uses it.

## Implementation notes

Multiplication of sections is the tensor product of the two given morphisms followed by the left
unitor of the tensor product sheaf,
`AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso`, whose action on local pure tensors is
`r ⊗ s ↦ r • s`. The unitors of a monoidal structure on sheaves of modules obtained by
localizing along sheafification have no such description, which is why that one is used.

Both halves of the argument are affine-local, and both use that a local section of a tensor
product sheaf is, on a covering sieve, a finite sum of pure tensors
(`Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_toTensorSheafSection`); the sieve is
refined to an affine open because the only available description of the sections of a power of
an ideal sheaf, `Stacks.AlgebraicGeometry.IdealPower.obj_idealPow_affineOpen`, is on the affine
opens. For the factorization that refinement is what
`AlgebraicGeometry.factorThruOfLocalMem` is designed to accept; for the epimorphism it feeds
`Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections`, with the finite sum of products
coming from `Submodule.mul_induction_on`.

`AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules X.ringCatSheaf`, and
`Stacks.SheafOfModules.Tensor.sheafTensor` is stated for the latter; the two agree
definitionally but not under
the reduced transparency at which `rw` and instance search operate, so `tensorModules` ascribes
the tensor product to `AlgebraicGeometry.Scheme.Modules` once and for all, the section
computations are assembled as terms rather than by rewriting, and the epimorphism is transported
from `SheafOfModules` by the cancellation property.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 0FZ0](https://stacks.math.columbia.edu/tag/0FZ0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerColimit
open Stacks.SheafOfModules.TensorUnit
open AlgebraicGeometry.SheafOfModules
  (tensorSheafUnitLeftIso tensorSheafUnitLeftIso_hom_toTensorSheafSection)

universe u

noncomputable section

/-- **An element of a product of two ideals is a finite sum of products.** -/
theorem Ideal.exists_sum_mul_of_mem_mul {R : Type*} [CommRing R] {I J : Ideal R} {x : R}
    (hx : x ∈ I * J) :
    ∃ (m : ℕ) (a b : Fin m → R), (∀ j, a j ∈ I) ∧ (∀ j, b j ∈ J) ∧ x = ∑ j, a j * b j := by
  refine Submodule.mul_induction_on hx (fun u hu v hv ↦ ⟨1, fun _ ↦ u, fun _ ↦ v,
    fun _ ↦ hu, fun _ ↦ hv, by simp⟩) ?_
  rintro u v ⟨m₁, a₁, b₁, ha₁, hb₁, hu⟩ ⟨m₂, a₂, b₂, ha₂, hb₂, hv⟩
  refine ⟨m₁ + m₂, Fin.append a₁ a₂, Fin.append b₁ b₂, fun j ↦ ?_, fun j ↦ ?_, ?_⟩
  · exact Fin.addCases (fun i ↦ by simpa using ha₁ i) (fun i ↦ by simpa using ha₂ i) j
  · exact Fin.addCases (fun i ↦ by simpa using hb₁ i) (fun i ↦ by simpa using hb₂ i) j
  · rw [Fin.sum_univ_add]
    simp [hu, hv]

namespace Stacks.AlgebraicGeometry.IdealProduct

variable {X : Scheme.{u}}

/-- The tensor product `A ⊗_{𝒪_X} B` of two `𝒪_X`-modules on a scheme, typed as an object of
`AlgebraicGeometry.Scheme.Modules`. This is the tensor product of [Stacks, Tag 01CA] in the
spelling `AlgebraicGeometry.externalTensorProduct` also uses. -/
abbrev tensorModules (A B : X.Modules) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj A).obj B

/-- **Multiplication of sections.** Two morphisms `φ : A ⟶ 𝒪_X` and `ψ : B ⟶ 𝒪_X` of
`𝒪_X`-modules induce `A ⊗_{𝒪_X} B ⟶ 𝒪_X`, sending a local pure tensor `a ⊗ b` to the product
`φ(a) ψ(b)`. -/
def mulToStructure {A B : X.Modules} (φ : A ⟶ structureModule X)
    (ψ : B ⟶ structureModule X) : tensorModules A B ⟶ structureModule X :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    X.sheaf)).map (X := (A, B)) (Y := (structureModule X, structureModule X)) (φ, ψ)) ≫
    (tensorSheafUnitLeftIso X.toRingedSpace (structureModule X)).hom

/-- **Multiplication of sections, on a local pure tensor**: the morphism `mulToStructure φ ψ`
sends the image of `a ⊗ b` in `A ⊗_{𝒪_X} B` to `φ(a) ψ(b)`.

The two factors of the product are passed as sections `r`, `s` of the structure sheaf together
with the equations identifying them, because the values of `φ` and `ψ` are sections of
`𝒪_X` viewed as an `𝒪_X`-module and multiplication is not available at that spelling. -/
theorem mulToStructure_app_toTensorSheafSection {A B : X.Modules} (φ : A ⟶ structureModule X)
    (ψ : B ⟶ structureModule X) (U : X.Opens) (a : Γ(A, U)) (b : Γ(B, U))
    (r s : Γ(X, U)) (hr : φ.app U a = r) (hs : ψ.app U b = s) :
    (mulToStructure φ ψ).app U
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace A B (op
        U)
          (a ⊗ₜ[X.presheaf.obj (op U)] b)) = r * s := by
  subst hr; subst hs
  exact (congrArg (ConcreteCategory.hom
        ((tensorSheafUnitLeftIso X.toRingedSpace (structureModule X)).hom.val.app (op U)))
      (Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap_app_toTensorSheafSection
      X.toRingedSpace A B
        (structureModule X) (structureModule X) φ ψ U a b)).trans
    (tensorSheafUnitLeftIso_hom_toTensorSheafSection X.toRingedSpace (structureModule X)
      (op U) (φ.app U a) (ψ.app U b))

/-- **A local section of a tensor product sheaf is a finite sum of pure tensors on an affine
neighbourhood of each of its points.** This refines
`Stacks.SheafOfModules.TensorUnit.exists_sieve_sum_toTensorSheafSection` from a covering sieve
to the affine opens, on which the sections of a power of an ideal sheaf are computable. -/
theorem exists_affineOpen_sum_toTensorSheafSection (A B : X.Modules) (W : X.Opens)
    (t : Γ(tensorModules A B, W)) (p : X) (hp : p ∈ W) :
    ∃ (V : X.affineOpens) (hV : V.1 ≤ W), p ∈ V.1 ∧
      ∃ (m : ℕ) (a : Fin m → Γ(A, V.1)) (b : Fin m → Γ(B, V.1)),
        (tensorModules A B).presheaf.map (homOfLE hV).op t =
          ∑ j, Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace A B
          (op V.1)
            (a j ⊗ₜ[X.presheaf.obj (op V.1)] b j) := by
  obtain ⟨S, hS, hsum⟩ := exists_sieve_sum_toTensorSheafSection X.toRingedSpace A B W t
  obtain ⟨V₀, k₀, hk₀, hpV₀⟩ := (Opens.mem_grothendieckTopology _).1 hS p hp
  obtain ⟨-, ⟨V, hVaff, rfl⟩, hpV, hVV₀⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show p ∈ (V₀ : Set X) from hpV₀) V₀.isOpen
  have hVW : V ≤ W := hVV₀.trans (leOfHom k₀)
  obtain ⟨m, a, b, heq⟩ := hsum (homOfLE hVW) (S.downward_closed hk₀ (homOfLE hVV₀))
  exact ⟨⟨V, hVaff⟩, hVW, hpV, m, a, b, heq⟩

/-- A morphism of `𝒪_X`-modules is an epimorphism in `X.Modules` iff it is one in
`SheafOfModules X.ringCatSheaf`. -/
private theorem epi_modules_iff {M N : X.Modules} (f : M ⟶ N) :
    Epi f ↔ @Epi (SheafOfModules X.ringCatSheaf) _ _ _ f :=
  ⟨fun h ↦ ⟨fun g₁ g₂ hg ↦ h.left_cancellation g₁ g₂ hg⟩,
    fun h ↦ ⟨fun g₁ g₂ hg ↦ h.left_cancellation g₁ g₂ hg⟩⟩

/-! ### The sections of a power of a product of ideal sheaves -/

/-- The sections of `(K K')ⁿ` over an affine open are the product of the `n`-th powers of the
ideals of `K` and of `K'`. -/
theorem obj_idealPow_mul_affineOpen (K K' : X.IdealSheafData) (n : ℕ) (V : X.affineOpens) :
    (idealPowerMultiple (K * K') n (structureModule X)).toSubmodule.obj (op V.1) =
      K.ideal V ^ n * K'.ideal V ^ n := by
  refine (obj_idealPow_affineOpen (K * K') n V).trans ?_
  show (K.ideal V * K'.ideal V) ^ n = _
  exact mul_pow _ _ n

/-! ### Multiplication of sections of two powers of ideal sheaves -/

variable (K K' : X.IdealSheafData) (n : ℕ)

/-- Multiplication of sections of `Kⁿ` and of `K'ⁿ`, as a morphism `Kⁿ ⊗_{𝒪_X} K'ⁿ ⟶ 𝒪_X`. -/
abbrev idealPowMulToStructure :
    tensorModules (idealPow K n) (idealPow K' n) ⟶ structureModule X :=
  mulToStructure (idealPowerMultiple K n (structureModule X)).ι
    (idealPowerMultiple K' n (structureModule X)).ι

/-- **Multiplication of sections of `Kⁿ` and of `K'ⁿ` takes values in `(K K')ⁿ`.** The
containment is checked on an affine open neighbourhood of each point, where a section of the
tensor product is a finite sum of pure tensors and the sections of the three ideal sheaves are
the corresponding powers of their ideals. -/
theorem exists_mem_idealPow_mul (W : X.Opens)
    (t : Γ(tensorModules (idealPow K n) (idealPow K' n), W)) (p : X) (hp : p ∈ W) :
    ∃ (V : X.Opens) (hV : V ≤ W), p ∈ V ∧
      (idealPowMulToStructure K K' n).app V
          ((tensorModules (idealPow K n) (idealPow K' n)).presheaf.map (homOfLE hV).op t) ∈
        (idealPowerMultiple (K * K') n (structureModule X)).toSubmodule.obj (op V) := by
  obtain ⟨V, hV, hpV, m, a, b, heq⟩ :=
    exists_affineOpen_sum_toTensorSheafSection (idealPow K n) (idealPow K' n) W t p hp
  refine ⟨V.1, hV, hpV, ?_⟩
  have hterm : ∀ j : Fin m, (idealPowMulToStructure K K' n).app V.1
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X.toRingedSpace (idealPow
        K n)
          (idealPow K' n) (op V.1) (a j ⊗ₜ[X.presheaf.obj (op V.1)] b j)) ∈
      (idealPowerMultiple (K * K') n (structureModule X)).toSubmodule.obj (op V.1) := by
    intro j
    refine (obj_idealPow_mul_affineOpen K K' n V).ge <|
      Eq.subst (motive := fun z ↦ z ∈ K.ideal V ^ n * K'.ideal V ^ n)
        (mulToStructure_app_toTensorSheafSection _ _ V.1 (a j) (b j)
          ((a j).1 : Γ(X, V.1)) ((b j).1 : Γ(X, V.1)) rfl rfl).symm ?_
    exact Ideal.mul_mem_mul ((obj_idealPow_affineOpen K n V).le (a j).2)
      ((obj_idealPow_affineOpen K' n V).le (b j).2)
  refine Eq.subst (motive := fun z ↦ z ∈
      (idealPowerMultiple (K * K') n (structureModule X)).toSubmodule.obj (op V.1))
    (Eq.trans (congrArg (ConcreteCategory.hom
        ((idealPowMulToStructure K K' n).app V.1)) heq) (map_sum _ _ _)).symm ?_
  exact Submodule.sum_mem _ fun j _ ↦ hterm j

/-- **The multiplication morphism `Kⁿ ⊗_{𝒪_X} K'ⁿ ⟶ (K K')ⁿ`.** -/
def idealPowMul :
    tensorModules (idealPow K n) (idealPow K' n) ⟶ idealPow (K * K') n :=
  factorThruOfLocalMem (idealPowerMultiple (K * K') n (structureModule X))
    (idealPowMulToStructure K K' n) (exists_mem_idealPow_mul K K' n)

/-- The multiplication morphism followed by the inclusion of `(K K')ⁿ` into the structure sheaf
is multiplication of sections. -/
@[reassoc (attr := simp)]
theorem idealPowMul_ι :
    idealPowMul K K' n ≫ (idealPowerMultiple (K * K') n (structureModule X)).ι =
      idealPowMulToStructure K K' n :=
  factorThruOfLocalMem_ι _ _ _

/-- The multiplication morphism does not change the value of a section: as a section of the
structure sheaf it is the product of the two factors. -/
theorem val_idealPowMul_app (V : X.Opens)
    (z : Γ(tensorModules (idealPow K n) (idealPow K' n), V)) :
    (((idealPowMul K K' n).app V z).1 : Γ(X, V)) =
      (idealPowMulToStructure K K' n).app V z := rfl

/-- **The multiplication morphism `Kⁿ ⊗_{𝒪_X} K'ⁿ ⟶ (K K')ⁿ` is an epimorphism.** Every
section of `(K K')ⁿ` over an affine open is a finite sum of products of a section of `Kⁿ` and a
section of `K'ⁿ`, hence the image of a finite sum of pure tensors. -/
theorem epi_idealPowMul : Epi (idealPowMul K K' n) := by
  refine (epi_modules_iff _).2 ?_
  refine Stacks.SheafOfModules.StalkEpiMono.epi_of_exists_sections _ fun W t p hp ↦ ?_
  obtain ⟨-, ⟨V, hVaff, rfl⟩, hpV, hVW⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show p ∈ (W : Set X) from hp) W.isOpen
  obtain ⟨m, a, b, ha, hb, hsum⟩ :=
    Ideal.exists_sum_mul_of_mem_mul (I := K.ideal ⟨V, hVaff⟩ ^ n)
      (J := K'.ideal ⟨V, hVaff⟩ ^ n)
      ((obj_idealPow_mul_affineOpen K K' n ⟨V, hVaff⟩).le
        ((idealPow (K * K') n).val.map (homOfLE hVW).op t).2)
  refine ⟨V, hVW, hpV, ∑ j, Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
  X.toRingedSpace
    (idealPow K n) (idealPow K' n) (op V)
    (⟨a j, (obj_idealPow_affineOpen K n ⟨V, hVaff⟩).ge (ha j)⟩ ⊗ₜ[X.presheaf.obj (op V)]
      ⟨b j, (obj_idealPow_affineOpen K' n ⟨V, hVaff⟩).ge (hb j)⟩), Subtype.ext ?_⟩
  refine (val_idealPowMul_app K K' n V _).trans (Eq.trans (Eq.trans (map_sum _ _ _) ?_)
    hsum.symm)
  exact Finset.sum_congr rfl fun j _ ↦
    mulToStructure_app_toTensorSheafSection _ _ V _ _ (a j) (b j) rfl rfl

/-! ### Quotients of the two factors give a quotient of the product -/

/-- **Multiplication along a pair of quotient maps.** Morphisms `A ⟶ Kⁿ` and `B ⟶ K'ⁿ` compose
with multiplication to give `A ⊗_{𝒪_X} B ⟶ (K K')ⁿ`. -/
def idealPowMulOfHom {A B : X.Modules} (e : A ⟶ idealPow K n) (e' : B ⟶ idealPow K' n) :
    tensorModules A B ⟶ idealPow (K * K') n :=
  ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    X.sheaf)).map (X := (A, B)) (Y := (idealPow K n, idealPow K' n)) (e, e')) ≫
    idealPowMul K K' n

/-- **A quotient of `Kⁿ` and a quotient of `K'ⁿ` give a quotient of `(K K')ⁿ`.** The tensor
product of two epimorphisms is an epimorphism (right exactness of the tensor product of modules
on a ringed space, [Stacks, Tag 01CC]), and multiplication is an epimorphism by
`epi_idealPowMul`. -/
theorem epi_idealPowMulOfHom {A B : X.Modules} (e : A ⟶ idealPow K n) (e' : B ⟶ idealPow K' n)
    (he : Epi e) (he' : Epi e') : Epi (idealPowMulOfHom K K' n e e') := by
  have h : @Epi (SheafOfModules (structureSheafRing X.toRingedSpace)) _ _ _
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        X.sheaf)).map ((e, e') : (A, B) ⟶ (idealPow K n, idealPow K' n))) :=
    @Stacks.SheafOfModules.TensorPresentations.tensorSheafMap_epi_of_epi_of_epi
      X.toRingedSpace _ _ _ _ e e'
      ((epi_modules_iff _).1 he) ((epi_modules_iff _).1 he')
  have := epi_idealPowMul K K' n
  exact @epi_comp X.Modules _ _ _ _ _ ((epi_modules_iff _).2 h) _ this

end Stacks.AlgebraicGeometry.IdealProduct

namespace Stacks.AlgebraicGeometry.IdealProduct

/-! ### The product ideal sheaf of a fibre product -/

/-- **The multiplication morphism onto a power of the product ideal sheaf `𝓙 = pr₁^*𝓘 · pr₂^*𝓘'`
of a fibre product is an epimorphism.** This is
`AlgebraicGeometry.Scheme.IdealSheafData.externalProduct` read through `epi_idealPowMul`: the
product ideal sheaf of [Stacks, Tag 0FZ0] is by definition the product of the two inverse image
ideal sheaves. -/
theorem epi_idealPowMul_externalProduct {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (I : X.IdealSheafData) (I' : Y.IdealSheafData) (n : ℕ) :
    Epi (idealPowMul (I.comap (Limits.pullback.fst f g)) (I'.comap (Limits.pullback.snd f g)) n :
      tensorModules (idealPow (I.comap (Limits.pullback.fst f g)) n)
          (idealPow (I'.comap (Limits.pullback.snd f g)) n) ⟶
        idealPow (Scheme.IdealSheafData.externalProduct f g I I') n) :=
  epi_idealPowMul _ _ n

end Stacks.AlgebraicGeometry.IdealProduct

end

end
