module

public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.Inf
public import StacksFrontier.AlgebraicGeometry.Stacks.GroupoidLift.ModBaseChange
public import Mathlib.LinearAlgebra.TensorProduct.Prod

/-!
# Flat base change of the derivations killed by the source and the target

Along a flat base change `e₂ = e ⊗ F` of thickenings, the derivations of `Q` killed by `sV` and
`tV` base change: `F ⊗ K₂(v) ≅ K₂(v ⊗ F)` (`K2BC`, `K2BC_bijective`). They are the kernel of
`E ↦ (E ∘ sV, E ∘ tV)` from the derivations of `Q` to two copies of the derivations of `P`, and
both of those base change (`AlgebraicGeometry.Stack.GroupoidLift.derBC_bijective`) compatibly
with precomposition (`AlgebraicGeometry.Stack.GroupoidLift.derBC_precomp`), so flatness of `F`
carries the kernel along.
-/

@[expose] public section

open scoped TensorProduct
open CategoryTheory
open AlgebraicGeometry.Space.ChartDescent

namespace AlgebraicGeometry.Stack.GroupoidLift

universe u

variable {A' : Type u} [CommRing A'] {κ : Cardinal.{u}}
  {X' X Y : SmallAlg A' κ} {e : SqZero X' X} {F : Type u} [CommRing F] [Algebra A' F]
  {hY : Cardinal.mk (X'.obj ⊗[A'] F) < κ} {e₂ : SqZero (SmallAlg.mk (X'.obj ⊗[A'] F) hY) Y}
  {φ : SqZero.Hom e e₂} (hB : IsBaseChange e F e₂ φ)
  {P : Type u} [CommRing P] [Algebra A' P] {Q : Type u} [CommRing Q] [Algebra A' Q]
  (sV tV : P →ₐ[A'] Q) {v : Q →ₐ[A'] X.obj} {w : P →ₐ[A'] X.obj} (hs : v.comp sV = w)
  (ht : v.comp tV = w) (m : Q →ₐ[A'] X'.obj) (hm : e.q.hom.hom.comp m = v)
  {v₂ : Q →ₐ[A'] Y.obj} (hv : φ.bot.hom.hom.comp v = v₂)

/-- The inclusion of `K₂` in the derivations. -/
def K2ι : K2 e v sV tV →ₗ[A'] Der e v where
  toFun E := ⟨E.1, E.2.1.1⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The pair of precompositions. -/
def K2Ψ : Der e v →ₗ[A'] Der e w × Der e w :=
  ((precompDer e sV hs).restrictScalars A').prod ((precompDer e tV ht).restrictScalars A')

/-- The sequence `K₂(v) → Der(v) → Der(w) × Der(w)` formed by `K2ι` and `K2Ψ` is exact: a
derivation of `Q` lies in `K₂(v)` exactly when its precompositions with `sV` and `tV` both
vanish. -/
theorem K2_exact : Function.Exact (K2ι (e := e) sV tV (v := v)) (K2Ψ sV tV hs ht) := by
  refine fun D ↦
    ⟨fun hD ↦ ⟨⟨D.1, ⟨D.2, LinearMap.mem_ker.mpr ?_⟩, LinearMap.mem_ker.mpr ?_⟩, rfl⟩, ?_⟩
  · exact congrArg (fun p ↦ (p.1 : P →ₗ[A'] X'.obj)) hD
  · exact congrArg (fun p ↦ (p.2 : P →ₗ[A'] X'.obj)) hD
  · rintro ⟨E, rfl⟩
    exact Prod.ext (Subtype.ext (LinearMap.mem_ker.mp E.2.1.2))
      (Subtype.ext (LinearMap.mem_ker.mp E.2.2))

include hB hm in
/-- The base change `derBC` of the image of an element of `F ⊗ K₂(v)` in `F ⊗ Der(v)` lies in
`K₂(v₂)`. -/
theorem derBC_mem_K2 (x : F ⊗[A'] K2 e v sV tV) :
    ((derBC hB m hm hv ((K2ι sV tV).lTensor F x) : Der e₂ v₂) : Q →ₗ[A'] (X'.obj ⊗[A'] F)) ∈
      K2 e₂ v₂ sV tV := by
  induction x using TensorProduct.inductionOn with
  | add x y hx hy =>
    rw [map_add, map_add, Submodule.coe_add]
    exact add_mem hx hy
  | tmul f E =>
    rw [LinearMap.lTensor_tmul, derBC_tmul]
    exact Submodule.smul_mem _ _ (postcomp_mem_K2 sV tV φ hv E.2)

/-- **The flat base change of `K₂`.** -/
noncomputable def K2BC : F ⊗[A'] K2 e v sV tV →ₗ[A'] K2 e₂ v₂ sV tV :=
  LinearMap.codRestrict ((K2 e₂ v₂ sV tV).restrictScalars A')
    (((Der e₂ v₂).subtype.restrictScalars A') ∘ₗ derBC hB m hm hv ∘ₗ (K2ι sV tV).lTensor F)
    (derBC_mem_K2 hB sV tV m hm hv)

/-- `K2BC` sends `f ⊗ E` to `(1 ⊗ f) • postcomp φ E`. -/
theorem K2BC_tmul (f : F) (E : K2 e v sV tV) :
    ((K2BC hB sV tV m hm hv (f ⊗ₜ E) : K2 e₂ v₂ sV tV) : Q →ₗ[A'] (X'.obj ⊗[A'] F)) =
      ((1 : X'.obj) ⊗ₜ[A'] f : X'.obj ⊗[A'] F) • postcomp φ E.1 := by
  change ((derBC hB m hm hv ((K2ι sV tV).lTensor F (f ⊗ₜ E)) : Der e₂ v₂) :
    Q →ₗ[A'] (X'.obj ⊗[A'] F)) = _
  rw [LinearMap.lTensor_tmul, derBC_tmul]
  rfl

variable [Module.Flat A' F]

/-- For `F` flat over `A'`, tensoring the exact sequence `K2ι`, `K2Ψ` with `F` keeps it exact. -/
theorem K2_lTensor_exact :
    Function.Exact ((K2ι (e := e) sV tV (v := v)).lTensor F) ((K2Ψ sV tV hs ht).lTensor F) :=
  Module.Flat.lTensor_exact F (K2_exact sV tV hs ht)

variable [Module.FinitePresentation P Ω[P⁄A']] [Module.FinitePresentation Q Ω[Q⁄A']]

include hs ht in
/-- For `F` flat over `A'`, the base change map `K2BC : F ⊗ K₂(v) → K₂(v₂)` is bijective. -/
theorem K2BC_bijective {w₂ : P →ₐ[A'] Y.obj} (hw : φ.bot.hom.hom.comp w = w₂)
    (hs₂ : v₂.comp sV = w₂) (ht₂ : v₂.comp tV = w₂) :
    Function.Bijective (K2BC hB sV tV m hm hv) := by
  have hD := derBC_bijective hB m hm hv
  have hιinj : Function.Injective ((K2ι (e := e) sV tV (v := v)).lTensor F) :=
    Module.Flat.lTensor_preserves_injective_linearMap _ fun a b h ↦
      Subtype.ext (congrArg (fun D : Der e v ↦ (D : Q →ₗ[A'] X'.obj)) h)
  refine ⟨fun x y h ↦ hιinj (hD.1 (Subtype.ext
    (congrArg (fun E : K2 e₂ v₂ sV tV ↦ (E : Q →ₗ[A'] (X'.obj ⊗[A'] F))) h))), fun y ↦ ?_⟩
  obtain ⟨z, hz⟩ := hD.2 ⟨y.1, y.2.1.1⟩
  have hzero : ∀ (σ : P →ₐ[A'] Q) (hσ : v.comp σ = w) (hσ₂ : v₂.comp σ = w₂)
      (hy : precomp _ σ y.1 = 0),
      ((precompDer e σ hσ).restrictScalars A').lTensor F z = 0 := by
    intro σ hσ hσ₂ hy
    apply (derBC_bijective hB (m.comp σ) (by rw [← AlgHom.comp_assoc, hm, hσ]) hw).1
    rw [map_zero, derBC_precomp hB σ hσ m hm hv hw hσ₂, hz]
    exact Subtype.ext hy
  have hΨ : (K2Ψ sV tV hs ht).lTensor F z = 0 := by
    apply (TensorProduct.prodRight A' A' F (Der e w) (Der e w)).injective
    rw [map_zero]
    have key : ∀ t : F ⊗[A'] Der e v,
        TensorProduct.prodRight A' A' F (Der e w) (Der e w) ((K2Ψ sV tV hs ht).lTensor F t) =
          (((precompDer e sV hs).restrictScalars A').lTensor F t,
            ((precompDer e tV ht).restrictScalars A').lTensor F t) := by
      intro t
      induction t using TensorProduct.inductionOn with
      | add a c ha hc => rw [map_add, map_add, ha, hc, map_add, map_add, Prod.mk_add_mk]
      | tmul f D => rfl
    rw [key, hzero sV hs hs₂ (LinearMap.mem_ker.mp y.2.1.2),
      hzero tV ht ht₂ (LinearMap.mem_ker.mp y.2.2)]
    rfl
  obtain ⟨x, hx⟩ := (K2_lTensor_exact sV tV hs ht z).mp hΨ
  refine ⟨x, Subtype.ext ?_⟩
  change (derBC hB m hm hv ((K2ι sV tV).lTensor F x) : Q →ₗ[A'] (X'.obj ⊗[A'] F)) = y.1
  rw [show ((K2ι (e := e) sV tV (v := v)).lTensor F) x = z from hx, hz]

end AlgebraicGeometry.Stack.GroupoidLift

end
