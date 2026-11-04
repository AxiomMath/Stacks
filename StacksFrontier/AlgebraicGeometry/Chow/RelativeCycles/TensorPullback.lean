module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Multiplicity
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Reflexive.Basic
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.TensorCoherence.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The tensor product of a module with a pullback

Let `f : X ⟶ Y` be a morphism of schemes, `F` an `𝒪_X`-module and `G` an `𝒪_Y`-module. This file
introduces the `𝒪_X`-module `F ⊗_{𝒪_X} f^* G`, computes its stalks and bounds its support, and
shows it coherent when `X` is locally Noetherian and `F` and `G` are coherent.

## Main definitions

* `AlgebraicGeometry.tensorPullback` — the `𝒪_X`-module `F ⊗_{𝒪_X} f^* G`.
* `AlgebraicGeometry.tensorPullbackStalkEquiv` — its stalk at `x` is `F_x ⊗_{𝒪_{X,x}} (f^* G)_x`.
* `AlgebraicGeometry.pullbackStalkEquivOfEq` — the stalk of a module pullback at a point, as a
  base change of the stalk at the image point.

## Main results

* `AlgebraicGeometry.tensorPullback_isCoherent` — on a locally Noetherian scheme the tensor
  product of a coherent module with the pullback of a coherent module is coherent.
* `AlgebraicGeometry.supp_tensorPullback_subset` — the support of `F ⊗_{𝒪_X} f^* G` is contained
  in `Supp(F) ∩ f^{-1} Supp(G)`.
* `AlgebraicGeometry.sheafMultiplicity_mul_sheafMultiplicity_pullback_fiberι` — when `F` is flat
  over `Y` at `x`, the multiplicity of `F ⊗_{𝒪_X} f^* G` at `x` is the product of the
  multiplicity of `G` at `f x` with the fibrewise multiplicity of `F` at `x`.
* `IsLocalRing.length_tensorProduct_of_flat` — the length identity that computes it, a
  generalisation of `IsLocalRing.length_baseChange` from a flat algebra to a flat module.

## Implementation notes

Nothing is constructed here: the tensor product is
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, the sheafification of the objectwise
tensor product of Stacks 01CA, the pullback is Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullback`, the module pullback of Stacks 03D6, and
`tensorPullback` abbreviates the composite.

Stacks 01CB identifies the stalk of a tensor product with the tensor product of the stalks, and
states it at the ringed-space spelling `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`
of the module structure on a stalk rather than at the instance search finds on the stalk of an
`AlgebraicGeometry.Scheme.Modules`. Both are Mathlib's instance; the `rfl`
`Stacks.SheafOfModules.stalkModule_eq` is restated here as
`AlgebraicGeometry.stalkModule_toRingedSpace_eq`, and `tensorPullbackStalkEquiv` is that
comparison read at the scheme spelling — so every statement below is read with the module
structures instance search finds, and no local `Module` instance has to be supplied by hand.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01Y2](https://stacks.math.columbia.edu/tag/01Y2)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 056J](https://stacks.math.columbia.edu/tag/056J)
* [Stacks Project, Tag 0EBF](https://stacks.math.columbia.edu/tag/0EBF)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.SheafOfModules.TensorStalkRingedSpace (tensorStalkIso)
open scoped TensorProduct

universe u

namespace TensorProduct

/-- A tensor product over a commutative ring is nontrivial only if both of its factors are: a
tensor product with a subsingleton factor is a subsingleton. -/
theorem nontrivial_and_nontrivial_of_nontrivial {R M N : Type*} [CommSemiring R]
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    (h : Nontrivial (M ⊗[R] N)) : Nontrivial M ∧ Nontrivial N := by
  constructor <;> by_contra hc <;> rw [not_nontrivial_iff_subsingleton] at hc <;>
    exact not_nontrivial_iff_subsingleton.mpr inferInstance h

end TensorProduct

namespace IsLocalRing

/-- Let `A` be a local ring with residue field `κ`, let `B` be an `A`-algebra and let `N` be a
`B`-module which is flat as an `A`-module. For every `A`-module `M` of finite length,
`ℓ_B(N ⊗_A M) = ℓ_A(M) · ℓ_B(N ⊗_A κ)`, the residue field being spelled `A ⧸ 𝔪_A`.

This is `IsLocalRing.length_baseChange` with the flat algebra `B` in the left factor replaced by
an arbitrary `A`-flat `B`-module `N`, and with no hypothesis on `B` beyond being an `A`-algebra.
The proof is the same induction along a composition series of `M`: flatness makes each step of
the series tensor to a short exact sequence, whose quotient term is `N ⊗_A κ` because the
quotient of the step is `κ`. -/
@[ega "IV 2.5.5.3" "special case", ega "IV 4.7.1" "more general"]
theorem length_tensorProduct_of_flat {A B N M : Type*} [CommRing A] [IsLocalRing A] [CommRing B]
    [Algebra A B] [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N]
    [SMulCommClass A B N] [Module.Flat A N] [AddCommGroup M] [Module A M]
    (hM : IsFiniteLength A M) :
    Module.length B (N ⊗[A] M) =
      Module.length A M * Module.length B (N ⊗[A] (A ⧸ maximalIdeal A)) := by
  classical
  obtain ⟨s, hs₀, hs₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hM
  have hstep (p q : Submodule A M) (hc : p ⋖ q) :
      Module.length B (N ⊗[A] q) =
        Module.length B (N ⊗[A] p) + Module.length B (N ⊗[A] (A ⧸ maximalIdeal A)) := by
    let f : p →ₗ[A] q := Submodule.inclusion hc.le
    let g : q →ₗ[A] q ⧸ LinearMap.range f := f.range.mkQ
    have hexact : Function.Exact f g :=
      LinearMap.exact_iff.mpr (by simp [f, g, Submodule.range_inclusion])
    have htensorInj : Function.Injective (f.lTensor N) :=
      Module.Flat.lTensor_preserves_injective_linearMap f (Submodule.inclusion_injective _)
    have htensorSurj : Function.Surjective (g.lTensor N) :=
      LinearMap.lTensor_surjective N f.range.mkQ_surjective
    have htensorExact : Function.Exact (f.lTensor N) (g.lTensor N) :=
      Module.Flat.lTensor_exact N hexact
    have hlen := Module.length_eq_add_of_exact
      (TensorProduct.AlgebraTensorModule.lTensor B N f)
      (TensorProduct.AlgebraTensorModule.lTensor B N g)
      htensorInj htensorSurj htensorExact
    have hsimple : IsSimpleModule A (q ⧸ LinearMap.range f) := by
      rwa [Submodule.range_inclusion, ← covBy_iff_quot_is_simple hc.le]
    obtain ⟨I, hI, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp hsimple
    rw [eq_maximalIdeal hI] at e
    rw [hlen, (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B N) e).length_eq]
  suffices h : ∀ k,
      Module.length B (N ⊗[A] s k) = k * Module.length B (N ⊗[A] (A ⧸ maximalIdeal A)) by
    rw [← Module.length_compositionSeries s hs₀ hs₁, ← Fin.val_last s.length, ← h,
      ← RelSeries.last, hs₁]
    exact (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl B N)
      (Submodule.topEquiv : (⊤ : Submodule A M) ≃ₗ[A] M)).length_eq.symm
  intro k
  induction k using Fin.induction with
  | zero => rw [← RelSeries.head, hs₀]; simp
  | succ i hi => simpa [hi, add_one_mul] using hstep (s i.castSucc) (s i.succ) (s.step i)

end IsLocalRing

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The module structure on the stalk of a module on a ringed space used in Stacks 01CB is the
one instance search finds on the stalk of a module on a scheme. This is
`Stacks.SheafOfModules.stalkModule_eq` with its right-hand side spelled as that instance. -/
theorem stalkModule_toRingedSpace_eq (F : X.Modules) (x : X) :
    Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule X.toRingedSpace F.val x =
      AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf F x :=
  Stacks.SheafOfModules.stalkModule_eq X.toRingedSpace F.val x

/-- The `𝒪_X`-module `F ⊗_{𝒪_X} f^* G`, for `f : X ⟶ Y`, an `𝒪_X`-module `F` and an
`𝒪_Y`-module `G`. -/
abbrev tensorPullback (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) : X.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj
    ((Scheme.Modules.pullback f).obj G)

/-- If `X` is locally Noetherian and `F`, `G` are coherent, then `F ⊗_{𝒪_X} f^* G` is coherent:
the pullback `f^* G` is coherent by Stacks 0EBF, and the tensor product of two coherent modules
is coherent by Stacks 01Y2. -/
instance tensorPullback_isCoherent [IsLocallyNoetherian X] (f : X ⟶ Y) (F : X.Modules)
    [F.IsCoherent] (G : Y.Modules) [G.IsCoherent] : (tensorPullback f F G).IsCoherent :=
  @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace F ((Scheme.Modules.pullback f).obj G)
    ‹F.IsCoherent› (isCoherent_pullback f G)

/-- **Stacks 01CB.** The stalk of `F ⊗_{𝒪_X} f^* G` at `x` is the tensor product of the stalk of
`F` with the stalk of `f^* G`, over the local ring of `X` at `x`. -/
def tensorPullbackStalkEquiv (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) (x : X) :
    (tensorPullback f F G).presheaf.stalk x ≃ₗ[X.presheaf.stalk x]
      F.presheaf.stalk x ⊗[X.presheaf.stalk x]
        ((Scheme.Modules.pullback f).obj G).presheaf.stalk x := by
  rw [← stalkModule_toRingedSpace_eq (tensorPullback f F G) x,
    ← stalkModule_toRingedSpace_eq F x,
    ← stalkModule_toRingedSpace_eq ((Scheme.Modules.pullback f).obj G) x]
  exact tensorStalkIso X.toRingedSpace x F ((Scheme.Modules.pullback f).obj G)

/-- The support of `F ⊗_{𝒪_X} f^* G` is contained in the intersection of the support of `F` with
the support of `f^* G`: the stalk of the tensor product is the tensor product of the stalks, and
that vanishes as soon as one of them does. -/
theorem supp_tensorPullback_subset_inter (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) :
    SheafOfModules.supp (tensorPullback f F G) ⊆
      SheafOfModules.supp F ∩ SheafOfModules.supp ((Scheme.Modules.pullback f).obj G) := by
  intro x hx
  have hT := TensorProduct.nontrivial_and_nontrivial_of_nontrivial
    ((tensorPullbackStalkEquiv f F G x).toEquiv.nontrivial_congr.mp
      ((SheafOfModules.mem_supp_iff_nontrivial_stalk (tensorPullback f F G) x).mp hx))
  exact ⟨(SheafOfModules.mem_supp_iff_nontrivial_stalk F x).mpr hT.1,
    (SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mpr hT.2⟩

/-- **Stacks 056J.** The support of `F ⊗_{𝒪_X} f^* G` is contained in the intersection of the
support of `F` with the inverse image of the support of `G`. -/
theorem supp_tensorPullback_subset (f : X ⟶ Y) (F : X.Modules) (G : Y.Modules) [G.IsFiniteType] :
    SheafOfModules.supp (tensorPullback f F G) ⊆
      SheafOfModules.supp F ∩ f ⁻¹' SheafOfModules.supp G := by
  rw [← Stacks.Modules.supp_pullback f G]
  exact supp_tensorPullback_subset_inter f F G

/-! ### The multiplicity of a tensor pullback -/

/-- **Stacks 0098.** For `i : Z ⟶ X` and a point `z` of `Z` lying over `x`, the stalk at `z` of
the pullback of an `𝒪_X`-module `F` is the base change along the induced map of local rings of
the stalk of `F` at `x`. -/
def pullbackStalkEquivOfEq {Z : Scheme.{u}} (i : Z ⟶ X) (F : X.Modules) (z : Z) (x : X)
    (hx : i z = x) :
    letI : Algebra (X.presheaf.stalk x) (Z.presheaf.stalk z) :=
      ((i.stalkMap z).hom.comp
        (X.presheaf.stalkCongr (.of_eq hx.symm)).hom.hom).toAlgebra
    ((Scheme.Modules.pullback i).obj F).presheaf.stalk z ≃ₗ[Z.presheaf.stalk z]
      Z.presheaf.stalk z ⊗[X.presheaf.stalk x] F.presheaf.stalk x := by
  subst hx
  dsimp only
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
  exact (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    i.toLRSHom.toShHom F z).choose

/-- **The multiplicity of a tensor pullback.** If `F` is flat over `Y` at `x` and the stalk of
`G` at `f x` has finite length, then the multiplicity of `F ⊗_{𝒪_X} f^* G` at `x` is the product
of the multiplicity of `G` at `f x` with the multiplicity, read on the fibre of `f` through `x`,
of the restriction of `F` to that fibre.

Over the local ring `A` of `Y` at `f x` with residue field `κ`, the stalk of the tensor product
is `F_x ⊗_A G_{f x}`, which by flatness of `F_x` over `A` has length `ℓ_A(G_{f x})` copies of
`F_x ⊗_A κ`; and `F_x ⊗_A κ` is the stalk on the fibre of the restriction of `F`, because the
local ring of the fibre is `𝒪_{X,x} ⊗_A κ`. -/
theorem sheafMultiplicity_mul_sheafMultiplicity_pullback_fiberι (f : X ⟶ Y) (F : X.Modules)
    (G : Y.Modules) (x : X) (hflat : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hGlen : IsFiniteLength (Y.presheaf.stalk (f x)) (G.presheaf.stalk (f x))) :
    Stacks.Chow.sheafMultiplicity G (f x) *
        Stacks.Chow.sheafMultiplicity
          ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) (f.asFiber x) =
      Stacks.Chow.sheafMultiplicity (tensorPullback f F G) x := by
  classical
  let y : Y := f x
  let z : f.fiber y := f.asFiber x
  let i : f.fiber y ⟶ X := f.fiberι y
  let T : X.Modules := tensorPullback f F G
  let Gx : X.Modules := (Scheme.Modules.pullback f).obj G
  let A := Y.presheaf.stalk y
  let B := X.presheaf.stalk x
  let D := (f.fiber y).presheaf.stalk z
  let M := G.presheaf.stalk y
  let N := F.presheaf.stalk x
  let Mx := Gx.presheaf.stalk x
  let TX := T.presheaf.stalk x
  let FN := ((Scheme.Modules.pullback i).obj F).presheaf.stalk z
  let φ : A →+* B := (f.stalkMap x).hom
  let θ : B →+* D :=
    (i.stalkMap z).hom.comp (X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).hom.hom
  let Q := Ideal.map φ (IsLocalRing.maximalIdeal A)
  let K := A ⧸ IsLocalRing.maximalIdeal A
  let : Algebra A B := φ.toAlgebra
  let : Algebra B D := θ.toAlgebra
  let eQAlg : (B ⧸ Q) ≃ₐ[B] D :=
    { __ := quotientStalkEquivFiberStalk f x
      commutes' := quotientStalkEquivFiberStalk_mk f x }
  have hθsurj : Function.Surjective θ := by
    intro d
    obtain ⟨q, hq⟩ := eQAlg.surjective d
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    exact ⟨b, (eQAlg.commutes b).symm.trans hq⟩
  let : Module A N := Module.compHom N φ
  let : IsScalarTower A B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : Module.Flat A N := hflat
  let : Module B FN := Module.compHom FN θ
  let : IsScalarTower B D FN := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let eD : (B ⊗[A] K) ≃ₗ[B] D :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot B
      (IsLocalRing.maximalIdeal A)).toLinearEquiv.symm.trans eQAlg.toLinearEquiv
  let eFN : FN ≃ₗ[D] D ⊗[B] N := pullbackStalkEquivOfEq i F z x (f.fiberι_asFiber x)
  let ePN : N ⊗[A] K ≃ₗ[B] FN :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B N K).symm.trans
      ((TensorProduct.comm B N (B ⊗[A] K)).trans
        ((eD.rTensor N).trans (eFN.restrictScalars B).symm))
  let ePull : Mx ≃ₗ[B] B ⊗[A] M :=
    (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      f.toLRSHom.toShHom G x).choose
  have hTlen : Module.length B TX = Module.length A M * Module.length B (N ⊗[A] K) :=
    ((tensorPullbackStalkEquiv f F G x).trans ((ePull.lTensor N).trans
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A B B N M))).length_eq.trans
      (IsLocalRing.length_tensorProduct_of_flat (A := A) (B := B) (N := N) (M := M) hGlen)
  have hnat : (Module.length B TX).toNat =
      (Module.length A M).toNat * (Module.length D FN).toNat := by
    rw [hTlen, ENat.toNat_mul, ePN.length_eq, Module.length_eq_of_surjective hθsurj]
  change ((Module.length A M).toNat : ℤ) * ((Module.length D FN).toNat : ℤ) =
    ((Module.length B TX).toNat : ℤ)
  exact_mod_cast hnat.symm

end AlgebraicGeometry
