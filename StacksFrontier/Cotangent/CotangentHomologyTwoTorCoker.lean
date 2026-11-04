module

public import StacksFrontier.Cotangent.ConormalTorDifferentialLinear
public import StacksFrontier.Cotangent.StandardResolutionIsResolution
public import StacksFrontier.Cotangent.TorTwoExplicitResolution
public import StacksFrontier.Cotangent.TorTwoResolutionIndependence

/-!
# `H₂(L_{B/A}) = Coker(Tor₂^{P₁}(B, B) → Tor₂^{P₀}(B, B))` (Stacks Remark 09D6)

Let `A → B` be a ring map and `P_•` a resolution of `B` over `A`, `J_n = Ker(P_n → B)`. Stacks
Remark 09D6 observes `Tor₂^{P_n}(B, B) = Tor₁^{P_n}(J_n, B) = Ker(J_n ⊗_{P_n} J_n → J_n²)` and
concludes from Remark 09D5 that `H₂(L_{B/A})` is canonically the cokernel of
`d₀ - d₁ : Tor₂^{P₁}(B, B) → Tor₂^{P₀}(B, B)`.

Remark 09D5 is `Stacks.Cotangent.cotangentComplexHomologyTwoLinearIsoTorOne`:
`H₂(L_{B/A}) = H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))`, the latter computed by the standard resolution. This
file reads `H₀` of a simplicial module as the cokernel of `d₀ - d₁`
(`mooreHomologyZeroIso`), identifies the standard resolution's `Tor₁^𝒪(𝒥, B̲)` term by term with
the tensor-kernel model of `Tor₂`, and transports the result to an arbitrary resolution with
`Stacks.Cotangent.TorTwo.Resolution.torTwoCokerIso`.

For the resolution of Example 09D4 this gives the remark's concluding exact sequence

`∧²_B(J₀/J₀²) → Tor₂^{P₀}(B, B) → H^{-2}(L_{B/A}) → 0`,

the image of `d₀ - d₁` being that of `∧²_B(J₀/J₀²)`
(`Stacks.Cotangent.TorTwo.Explicit.range_face`).

## Main definitions

* `Stacks.Cotangent.TorTwo.toHomologyTwo`: `Tor₂^{P₀}(B, B) → H^{-2}(L_{B/A})` for the resolution
  of 09D4.

## Main results

* `Stacks.Cotangent.TorTwo.mooreHomologyZeroIso`: `H₀` of the Moore complex is
  `X₀ / Im(d₀ - d₁)`.
* `Stacks.Cotangent.TorTwo.cotangentHomologyTwoIsoTorTwoCoker`: **`H₂(L_{B/A}) = Coker(d₀ - d₁)`**
  for an arbitrary resolution.
* `Stacks.Cotangent.TorTwo.exact_wedgeAntisymm_toHomologyTwo` and
  `Stacks.Cotangent.TorTwo.toHomologyTwo_surjective`: **the exact sequence**.

## Implementation notes

All the isomorphisms are `B`-linear: Remark 09D5 is used in its `B`-linear form, `H₀` of the
Moore complex is computed in `B`-modules, and the comparison of the cokernels of two resolutions is
`B`-linear.

## References

* [Stacks Project, Tag 09D6](https://stacks.math.columbia.edu/tag/09D6)
* [Stacks Project, Tag 09D5](https://stacks.math.columbia.edu/tag/09D5)
-/


@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology
open scoped Simplicial TensorProduct

universe u v w

namespace Stacks.Cotangent.TorTwo

/-! ### `H₀` of a simplicial module -/

section MooreZero

variable {A : Type u} [CommRing A] (X : SimplicialObject (ModuleCat.{w} A))

/-- The differential `X₁ → X₀` of the Moore complex of a simplicial module is `d₀ - d₁`. -/
theorem mooreComplex_d_one_zero :
    (((alternatingFaceMapComplex (ModuleCat.{w} A)).obj X).d 1 0).hom =
      (X.δ (0 : Fin 2)).hom - (X.δ (1 : Fin 2)).hom := by
  change ((AlternatingFaceMapComplex.obj X).d (0 + 1) 0).hom = _
  rw [AlternatingFaceMapComplex.obj_d_eq, Fin.sum_univ_two]
  ext x
  simp [sub_eq_add_neg]

/-- **`H₀` of the Moore complex of a simplicial module is `X₀ / Im(d₀ - d₁)`.** -/
def mooreHomologyZeroIso :
    ((alternatingFaceMapComplex (ModuleCat.{w} A)).obj X).homology 0 ≅
      ModuleCat.of A (X.obj (op ⦋0⦌) ⧸
        LinearMap.range ((X.δ (0 : Fin 2)).hom - (X.δ (1 : Fin 2)).hom)) :=
  ((alternatingFaceMapComplex (ModuleCat.{w} A)).obj X).isoHomologyι₀ ≪≫
    (((alternatingFaceMapComplex (ModuleCat.{w} A)).obj X).opcyclesIsCokernel 1 0
      (by simp)).coconePointUniqueUpToIso (cokernelIsCokernel _) ≪≫
    ModuleCat.cokernelIsoRangeQuotient _ ≪≫
    (Submodule.quotEquivOfEq _ _ (by rw [mooreComplex_d_one_zero X])).toModuleIso

end MooreZero

/-! ### The standard resolution -/

section Standard

open CommAlgCat Stacks.Cotangent.TorTwo.Resolution

variable (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)

/-- The standard resolution is a resolution. -/
abbrev stdIsResolution :
    CommAlgCat.IsResolution A B (standardResolution A B).left (standardResolution A B).hom :=
  standardResolution_isResolution A B

/-- The term `Tor₁^{P_n}(J_n, B)` of `Tor₁^𝒪(𝒥, B̲)` on the standard resolution is the model of
`Tor₂^{P_n}(B, B)`, as `B`-modules; on elements it is the identity of `Ker(J_n ⊗ J_n → J_n²)`. -/
def stdTorOneEquiv (n : ℕ) :
    (torOneSimplicialB.{u, v} A B).obj (op ⦋n⦌) ≃ₗ[(B : Type (max u v))]
      torTwo (stdIsResolution A B) n where
  toFun t := ⟨(torOneTermEquiv.{u, v} A B (op ⦋n⦌) t).1, (torOneTermEquiv.{u, v} A B (op ⦋n⦌) t).2⟩
  invFun k := (torOneTermEquiv.{u, v} A B (op ⦋n⦌)).symm ⟨k.1, k.2⟩
  map_add' _ _ := rfl
  map_smul' b t := by
    have : Fact (Function.Surjective (aug (standardResolution A B).hom n)) :=
      ⟨aug_surjective (stdIsResolution A B) n⟩
    have hp : standardResolutionAugmentationHom.{u, v} A B (op ⦋n⦌)
        (Function.surjInv (aug_surjective (stdIsResolution A B) n) b) = b :=
      Function.surjInv_eq (aug_surjective (stdIsResolution A B) n) b
    exact Subtype.ext (congrArg Subtype.val (torOneTermEquiv_smul.{u, v} A B (op ⦋n⦌) b _ hp t))
  left_inv _ := rfl
  right_inv _ := rfl

/-- On the standard resolution, `stdTorOneEquiv` carries `d₀ - d₁` of `Tor₁^𝒪(𝒥, B̲)` to the map
`d₀ - d₁ : Tor₂^{P₁}(B, B) → Tor₂^{P₀}(B, B)` of the model of `Tor₂`. -/
theorem stdTorOneEquiv_face (y : (torOneSimplicialB.{u, v} A B).obj (op ⦋1⦌)) :
    stdTorOneEquiv A B 0 (((torOneSimplicialB.{u, v} A B).δ (0 : Fin 2)).hom y -
        ((torOneSimplicialB.{u, v} A B).δ (1 : Fin 2)).hom y) =
      (torTwoFace (stdIsResolution A B)).hom (stdTorOneEquiv A B 1 y) := by
  apply Subtype.ext
  have key : ∀ (i : Fin 2),
      (torOneTermEquiv.{u, v} A B (op ⦋0⦌) (((torOneSimplicialB.{u, v} A B).δ i).hom y)).1 =
        tensorMap (face i) (aug_comp_face _ i) (torOneTermEquiv.{u, v} A B (op ⦋1⦌) y).1 := by
    intro i
    change (idealTensorIdeal.{u, v} A B).map (SimplexCategory.δ i).op
      (torOneTermEquiv.{u, v} A B (op ⦋1⦌) y).1 = _
    induction ((torOneTermEquiv.{u, v} A B (op ⦋1⦌) y).1 :
        augmentationIdeal A B (op ⦋1⦌) ⊗[(standardResolution A B).left.obj (op ⦋1⦌)]
          augmentationIdeal A B (op ⦋1⦌)) using TensorProduct.induction_on with
    | zero => exact (map_zero _).symm
    | tmul a b => rfl
    | add s t hs ht => exact (map_add _ s t).trans ((congrArg₂ (· + ·) hs ht).trans
        (map_add _ s t).symm)
  change (torOneTermEquiv.{u, v} A B (op ⦋0⦌)
        (((torOneSimplicialB.{u, v} A B).δ (0 : Fin 2)).hom y)).1 -
      (torOneTermEquiv.{u, v} A B (op ⦋0⦌)
        (((torOneSimplicialB.{u, v} A B).δ (1 : Fin 2)).hom y)).1 =
    tensorMap (face 0) (aug_comp_face _ 0) (torOneTermEquiv.{u, v} A B (op ⦋1⦌) y).1 -
      tensorMap (face 1) (aug_comp_face _ 1) (torOneTermEquiv.{u, v} A B (op ⦋1⦌) y).1
  rw [key, key]
  rfl

/-- The class map `Tor₁^{P₀}(J₀, B) → Coker(d₀ - d₁)` on the standard resolution. -/
def stdClassMap :
    (torOneSimplicialB.{u, v} A B).obj (op ⦋0⦌) →ₗ[(B : Type (max u v))]
      torTwoCoker (stdIsResolution A B) :=
  (LinearMap.range (torTwoFace (stdIsResolution A B)).hom).mkQ ∘ₗ
    (stdTorOneEquiv A B 0).toLinearMap

/-- An element lies in the kernel of `stdClassMap` if and only if its image under
`stdTorOneEquiv` lies in the image of `d₀ - d₁`. -/
theorem stdClassMap_eq_zero_iff (x : (torOneSimplicialB.{u, v} A B).obj (op ⦋0⦌)) :
    stdClassMap A B x = 0 ↔
      stdTorOneEquiv A B 0 x ∈ LinearMap.range (torTwoFace (stdIsResolution A B)).hom :=
  Submodule.Quotient.mk_eq_zero _

/-- The image of `d₀ - d₁` on `Tor₁^𝒪(𝒥, B̲)` lies in the kernel of `stdClassMap`. -/
theorem range_le_ker_stdClassMap :
    LinearMap.range (((torOneSimplicialB.{u, v} A B).δ (0 : Fin 2)).hom -
        ((torOneSimplicialB.{u, v} A B).δ (1 : Fin 2)).hom) ≤ LinearMap.ker (stdClassMap A B) := by
  rintro _ ⟨y, rfl⟩
  rw [LinearMap.mem_ker, stdClassMap_eq_zero_iff]
  exact ⟨stdTorOneEquiv A B 1 y, (stdTorOneEquiv_face A B y).symm⟩

/-- The class map `stdClassMap` is surjective. -/
theorem stdClassMap_surjective : Function.Surjective (stdClassMap A B) := by
  intro c
  obtain ⟨k, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  exact ⟨(stdTorOneEquiv A B 0).symm k,
    congrArg Submodule.Quotient.mk ((stdTorOneEquiv A B 0).apply_symm_apply k)⟩

/-- `X₀ / Im(d₀ - d₁)` for `Tor₁^𝒪(𝒥, B̲)` on the standard resolution is the cokernel of
`d₀ - d₁` on the model of `Tor₂`. -/
def stdCokerEquiv :
    ((torOneSimplicialB.{u, v} A B).obj (op ⦋0⦌) ⧸ LinearMap.range
        (((torOneSimplicialB.{u, v} A B).δ (0 : Fin 2)).hom -
          ((torOneSimplicialB.{u, v} A B).δ (1 : Fin 2)).hom)) ≃ₗ[(B : Type (max u v))]
      torTwoCoker (stdIsResolution A B) :=
  LinearEquiv.ofBijective (Submodule.liftQ _ (stdClassMap A B) (range_le_ker_stdClassMap A B)) (by
    refine ⟨(injective_iff_map_eq_zero _).2 fun q hq => ?_, fun c => ?_⟩
    · induction q using Submodule.Quotient.induction_on with
      | H x =>
        rw [Submodule.liftQ_apply, stdClassMap_eq_zero_iff] at hq
        obtain ⟨w, hw⟩ := hq
        rw [Submodule.Quotient.mk_eq_zero]
        refine ⟨(stdTorOneEquiv A B 1).symm w, (stdTorOneEquiv A B 0).injective ?_⟩
        rw [LinearMap.sub_apply, stdTorOneEquiv_face, LinearEquiv.apply_symm_apply]
        exact hw
    · obtain ⟨x, rfl⟩ := stdClassMap_surjective A B c
      exact ⟨Submodule.Quotient.mk x, Submodule.liftQ_apply _ _ _⟩)

end Standard

/-! ### `H₂(L_{B/A})` -/

section Main

open CommAlgCat Stacks.Cotangent.TorTwo.Resolution

variable {A : Type u} [CommRing A] {B : CommAlgCat.{max u v} A}
  {P : SimplicialObject (CommAlgCat.{max u v} A)}
  {ε : P ⟶ (SimplicialObject.const _).obj (CommAlgCat.of A B)}

/-- `H₂(L_{B/A}) = Coker(Tor₂^{P₁}(B, B) → Tor₂^{P₀}(B, B))` for an arbitrary resolution `P_•`
of `B` over `A`, as `B`-modules, where `Tor₂^{P_n}(B, B) = Ker(J_n ⊗_{P_n} J_n → J_n²)` and the
map is `d₀ - d₁`. The isomorphism is Remark 09D5's `H₂(L_{B/A}) = H₀(C_{B/A}, Tor₁^𝒪(𝒥, B̲))`,
followed by `H₀ = Coker(d₀ - d₁)` on the standard resolution and the canonical comparison of the
cokernels of two resolutions. -/
@[stacks 09D6 "H₂(L_{B/A}) is canonically Coker(Tor₂^{P₁}(B, B) → Tor₂^{P₀}(B, B)), the map being \
  d₀ - d₁, for an arbitrary resolution P_• of B over A (Remark 08QI), as B-modules, with \
  Tor₂^{P_n}(B, B) read as Ker(J_n ⊗_{P_n} J_n → J_n²); obtained from Remark 09D5, \
  Stacks.Cotangent.cotangentComplexHomologyTwoLinearIsoTorOne, as the source obtains it"]
def cotangentHomologyTwoIsoTorTwoCoker (hP : CommAlgCat.IsResolution A B P ε) :
    (cotangentComplex A B).homology (-2) ≅ torTwoCoker hP :=
  cotangentComplexHomologyTwoLinearIsoTorOne.{u, v} A B ≪≫ mooreHomologyZeroIso _ ≪≫
    (stdCokerEquiv.{u, v} A B).toModuleIso ≪≫ torTwoCokerIso (stdIsResolution A B) hP

end Main

/-! ### The exact sequence for the resolution of 09D4 -/

section Explicit

open CommAlgCat Stacks.Cotangent.TorTwo.Resolution Stacks.Cotangent.TorTwo.Explicit

universe x

variable (p : Algebra.PolynomialPresentationWithKernelGenerators.{u, v, w, x})

/-- `H₂(L_{B/A}) = Coker(d₀ - d₁)` for the resolution of 09D4. -/
abbrev explicitIso :=
  cotangentHomologyTwoIsoTorTwoCoker.{u, max v w x}
    (B := Algebra.PolynomialPresentationWithKernelGenerators.Degeneracies.commAlgB p)
    (res p).isResolution

/-- The map `Tor₂^{P₀}(B, B) → H^{-2}(L_{B/A})` for the resolution of 09D4: the class in
`Coker(d₀ - d₁)`, read in `H₂(L_{B/A})` through `cotangentHomologyTwoIsoTorTwoCoker`. -/
def toHomologyTwo :
    mulKernel (aug p 0) →ₗ[target p]
      ((cotangentComplex.{u, max v w x} p.A
        (Algebra.PolynomialPresentationWithKernelGenerators.Degeneracies.commAlgB p)).homology
          (-2)) :=
  (explicitIso p).inv.hom ∘ₗ (LinearMap.range (face p)).mkQ

/-- `toHomologyTwo` sends `k` to the image of its class in `Coker(d₀ - d₁)` under the inverse of
`explicitIso`. -/
theorem toHomologyTwo_apply (k : mulKernel (aug p 0)) :
    toHomologyTwo p k = (explicitIso p).inv.hom (Submodule.Quotient.mk k) := rfl

/-- The map `Tor₂^{P₀}(B, B) → H^{-2}(L_{B/A})` is surjective. -/
@[stacks 09D6 "the exact sequence ∧²_B(J₀/J₀²) → Tor₂^{P₀}(B, B) → H^{-2}(L_{B/A}) → 0 for the \
  resolution of Example 09D4: the last map is surjective"]
theorem toHomologyTwo_surjective : Function.Surjective (toHomologyTwo p) :=
  (ConcreteCategory.bijective_of_isIso (explicitIso p).inv).2.comp
    (Submodule.mkQ_surjective _)

/-- The exact sequence `∧²_B(J₀/J₀²) → Tor₂^{P₀}(B, B) → H^{-2}(L_{B/A}) → 0` for the resolution
of Example 09D4: exactness at `Tor₂^{P₀}(B, B)`, the first map being `ā ∧ b̄ ↦ a ⊗ b - b ⊗ a`; the
second map is surjective by `toHomologyTwo_surjective`. Both maps are `B`-linear. -/
@[stacks 09D6 "the exact sequence ∧²_B(J₀/J₀²) → Tor₂^{P₀}(B, B) → H^{-2}(L_{B/A}) → 0 for the \
  resolution of Example 09D4: exactness at Tor₂^{P₀}(B, B), the first map being \
  ā ∧ b̄ ↦ a ⊗ b - b ⊗ a"]
theorem exact_wedgeAntisymm_toHomologyTwo :
    Function.Exact (wedgeAntisymm (φ := aug p 0)) (toHomologyTwo p) := by
  intro k
  have hinj : Function.Injective (explicitIso p).inv.hom :=
    (ModuleCat.mono_iff_injective _).1 inferInstance
  rw [toHomologyTwo_apply]
  change _ ↔ k ∈ LinearMap.range (wedgeAntisymm (φ := aug p 0))
  rw [← range_face p, ← Submodule.Quotient.mk_eq_zero]
  exact map_eq_zero_iff _ hinj

end Explicit

end Stacks.Cotangent.TorTwo

end
