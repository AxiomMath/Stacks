module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.PullbackTensor.StalkFormula
public import Mathlib.Geometry.RingedSpace.LocallyRingedSpace
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksCore.Tactic.StacksAttribute

/-!
# Tag 0H78: the nonvanishing locus of a pulled-back global section

Let `f : Y ⟶ X` be a morphism of locally ringed spaces and `L` a sheaf of `𝒪_X`-modules. A
global section `s` of `L` has a pullback, the global section of `f^*L` obtained by applying the
unit of `f^* ⊣ f_*` to `s` and restricting. [Stacks, Tag 0H78] says that the nonvanishing locus
of the pullback is the preimage of the nonvanishing locus of `s`:

  `f⁻¹(X_s) = Y_{f^*s}`.

## Main definitions

* `Stacks.SheafOfModules.modulePullbackSection`: the pullback of a global section along a
  morphism of locally ringed spaces.

## Main results

* `Stacks.SheafOfModules.preimage_nonvanishingLocus`: **Tag 0H78**, the two loci agree.

## Implementation notes

Nonvanishing at `y` means that the germ of the section does not lie in `𝔪_y · (f^*L)_y`. The
stalk of the pullback is `𝒪_{Y,y} ⊗_{𝒪_{X,f y}} L_{f y}` by [Stacks, Tag 0098], which is
available as `Stacks.RingedSpace.pullbackStalkFormula` in exactly the spelling of the module
structure on a stalk that `Stacks.SheafOfModules.nonvanishingLocus` uses, and that equivalence
carries the germ of the pulled-back section to `1 ⊗ (germ of s)`. So the statement reduces to the
algebraic fact that for a local homomorphism `A → B` of local rings and an `A`-module `M` one has
`m ∈ 𝔪_A · M` if and only if `1 ⊗ m ∈ 𝔪_B · (B ⊗_A M)`, which is faithful flatness of the
residue field extension: both sides say that the image of `m` in `κ(B) ⊗_A M` vanishes, read
through `κ(B) ⊗_{κ(A)} (κ(A) ⊗_A M)`.

`Stacks.SheafOfModules.mem_ideal_smul_top_iff_of_linearEquiv` is the transport of `I · ⊤` along a
linear equivalence, which is what lets the stalk formula be used as a black box.

## References

* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.SheafOfModules.TensorStalkRingedSpace RingedSpaceModuleAdjunction
open Stacks.RingedSpace (structureRingSheaf pullbackUnit pullbackStalkFormula)
open scoped TensorProduct

universe u

namespace Stacks.SheafOfModules

/-- For a local homomorphism of local rings `A → B` and an `A`-module `M`, an element of `M`
lies in `𝔪_A · M` if and only if `1 ⊗ m` lies in `𝔪_B · (B ⊗_A M)`. Both conditions say that
the image of `m` in the residue-field base change vanishes, and the two residue fields are
compared by faithful flatness of `κ(A) → κ(B)`. -/
theorem mem_maximalIdeal_smul_iff_tmul
    {A B M : Type u} [CommRing A] [IsLocalRing A] [CommRing B] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)] [AddCommGroup M] [Module A M] (m : M) :
    m ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ↔
      (1 : B) ⊗ₜ[A] m ∈ IsLocalRing.maximalIdeal B •
        (⊤ : Submodule B (B ⊗[A] M)) := by
  let K := IsLocalRing.ResidueField A
  let L := IsLocalRing.ResidueField B
  let eA := TensorProduct.quotTensorEquivQuotSMul M (IsLocalRing.maximalIdeal A)
  let eAK := TensorProduct.AlgebraTensorModule.cancelBaseChange A K L L M
  let eB := TensorProduct.quotTensorEquivQuotSMul (B ⊗[A] M) (IsLocalRing.maximalIdeal B)
  let eBA := TensorProduct.AlgebraTensorModule.cancelBaseChange A B L L M
  have hA : eA (1 ⊗ₜ[A] m) = Submodule.Quotient.mk m :=
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ _
  have hB : eB ((1 : L) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] m)) =
      Submodule.Quotient.mk (1 ⊗ₜ[A] m) :=
    TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul _ _
  have hBA : eBA.symm ((1 : L) ⊗ₜ[A] m) =
      (1 : L) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] m) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul A B L 1 m).symm
  have hAK : eAK.symm ((1 : L) ⊗ₜ[A] m) =
      (1 : L) ⊗ₜ[K] ((1 : K) ⊗ₜ[A] m) :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul A K L 1 m).symm
  have hsrc : m ∈ IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) ↔
      (1 : K) ⊗ₜ[A] m = 0 := by
    rw [← Submodule.Quotient.mk_eq_zero, ← hA, eA.map_eq_zero_iff]
    exact Iff.rfl
  have htarget : (1 : B) ⊗ₜ[A] m ∈ IsLocalRing.maximalIdeal B •
      (⊤ : Submodule B (B ⊗[A] M)) ↔
      (1 : L) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] m) = 0 := by
    rw [← Submodule.Quotient.mk_eq_zero, ← hB, eB.map_eq_zero_iff]
    exact Iff.rfl
  have hfaith : (1 : L) ⊗ₜ[K] ((1 : K) ⊗ₜ[A] m) = 0 ↔
      (1 : K) ⊗ₜ[A] m = 0 := by
    rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff]
  have hchange : (1 : L) ⊗ₜ[B] ((1 : B) ⊗ₜ[A] m) = 0 ↔
      (1 : L) ⊗ₜ[A] m = 0 := by
    rw [← hBA, eBA.symm.map_eq_zero_iff]
  have hchange' : (1 : L) ⊗ₜ[A] m = 0 ↔
      (1 : L) ⊗ₜ[K] ((1 : K) ⊗ₜ[A] m) = 0 := by
    rw [← hAK, eAK.symm.map_eq_zero_iff]
  rw [hsrc, htarget, hchange, hchange', hfaith]

/-- A linear equivalence carries `I · ⊤` to `I · ⊤`. -/
theorem mem_ideal_smul_top_iff_of_linearEquiv
    {R M N : Type u} [CommSemiring R] [AddCommMonoid M] [Module R M]
    [AddCommMonoid N] [Module R N] (I : Ideal R) (e : M ≃ₗ[R] N) (x : M) :
    x ∈ I • (⊤ : Submodule R M) ↔ e x ∈ I • (⊤ : Submodule R N) := by
  have h₁ : I • (⊤ : Submodule R M) ≤ Submodule.comap e.toLinearMap
      (I • (⊤ : Submodule R N)) := by
    rw [Submodule.smul_le]
    intro r hr m _
    change e (r • m) ∈ I • (⊤ : Submodule R N)
    rw [e.map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  have h₂ : I • (⊤ : Submodule R N) ≤ Submodule.comap e.symm.toLinearMap
      (I • (⊤ : Submodule R M)) := by
    rw [Submodule.smul_le]
    intro r hr n _
    change e.symm (r • n) ∈ I • (⊤ : Submodule R M)
    rw [e.symm.map_smul]
    exact Submodule.smul_mem_smul hr Submodule.mem_top
  exact ⟨fun hx => by simpa using h₁ hx, fun h => by simpa using h₂ h⟩

variable {X Y : LocallyRingedSpace.{u}} (f : Y ⟶ X)
  (L : SheafOfModules.{u} (structureRingSheaf X.toRingedSpace))

/-- **The pullback of a global section.** The unit of `f^* ⊣ f_*` sends a global section of `L`
to a section of `f^*L` over `f⁻¹X = Y`, hence to a global section; restricting it to every open
gives the compatible family. -/
public noncomputable def modulePullbackSection (s : L.sections) :
    ((modulePullback f.toShHom).obj L).sections :=
  ((modulePullback f.toShHom).obj L).val.sectionsMk
    (fun U => ((modulePullback f.toShHom).obj L).val.map
      (homOfLE (le_top : U.unop ≤ ⊤)).op
      (pullbackUnit f.toShHom L (op ⊤) (s.eval (op ⊤))))
    (by
      intro U V g
      rw (transparency := .default)
        [← ((modulePullback f.toShHom).obj L).val.map_comp_apply]
      congr 2)

/-- The pullback of a global section evaluates over `⊤` to the image of the section under the
unit of `f^* ⊣ f_*`. -/
theorem modulePullbackSection_eval_top (s : L.sections) :
    (modulePullbackSection f L s).eval (op ⊤) =
      pullbackUnit f.toShHom L (op ⊤) (s.eval (op ⊤)) := by
  change ((modulePullback f.toShHom).obj L).val.map
      (homOfLE (le_top : (⊤ : Opens Y.carrier) ≤ ⊤)).op
      (pullbackUnit f.toShHom L (op ⊤) (s.eval (op ⊤))) = _
  rw [show (homOfLE (le_top : (⊤ : Opens Y.carrier) ≤ ⊤)).op =
      𝟙 (op (⊤ : Opens Y.carrier)) from Subsingleton.elim _ _,
    ((modulePullback f.toShHom).obj L).val.map_id]
  rfl

/-- **Stacks Project, Tag 0H78.** For a morphism `f : Y ⟶ X` of locally ringed spaces and a
global section `s` of a sheaf of `𝒪_X`-modules `L`, the nonvanishing locus of the pullback of
`s` is the preimage of the nonvanishing locus of `s`. -/
@[stacks 0H78]
public theorem preimage_nonvanishingLocus (s : L.sections) :
    f.base ⁻¹' nonvanishingLocus (X := X.toRingedSpace) L s =
      nonvanishingLocus (X := Y.toRingedSpace)
        ((modulePullback f.toShHom).obj L) (modulePullbackSection f L s) := by
  ext y
  let _ : Algebra (ringStalk X.toRingedSpace (f.base y)) (ringStalk Y.toRingedSpace y) :=
    (f.stalkMap y).hom.toAlgebra
  have : IsLocalHom (algebraMap (ringStalk X.toRingedSpace (f.base y))
      (ringStalk Y.toRingedSpace y)) := f.prop y
  obtain ⟨e, he⟩ := pullbackStalkFormula f.toShHom L y
  have hunit : e (grpGerm Y.toRingedSpace ((modulePullback f.toShHom).obj L).val y ⊤
        (Opens.mem_top y) ((modulePullbackSection f L s).eval (op ⊤))) =
      (1 : ringStalk Y.toRingedSpace y) ⊗ₜ[ringStalk X.toRingedSpace (f.base y)]
        grpGerm X.toRingedSpace L.val (f.base y) ⊤ (Opens.mem_top _) (s.eval (op ⊤)) := by
    rw [modulePullbackSection_eval_top]
    exact he ⊤ (Opens.mem_top _) (s.eval (op ⊤))
  simp only [Set.mem_preimage, nonvanishingLocus, Set.mem_ofPred_eq]
  refine not_congr (Iff.trans (mem_maximalIdeal_smul_iff_tmul
    (A := ringStalk X.toRingedSpace (f.base y)) (B := ringStalk Y.toRingedSpace y)
    (M := grpStalk X.toRingedSpace L.val (f.base y)) _) ?_)
  rw [← hunit]
  exact (mem_ideal_smul_top_iff_of_linearEquiv
    (IsLocalRing.maximalIdeal (ringStalk Y.toRingedSpace y)) e _).symm

end Stacks.SheafOfModules

end
