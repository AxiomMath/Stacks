module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.FirstDisplay
public import StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.SheafSubmodule
public import StacksFrontier.AlgebraicGeometry.Duality.IdealPowerSubmoduleArtinRees
public import StacksFrontier.AlgebraicGeometry.IdealPowerMultipleComparison.Basic

/-!
# The comparison `𝓘^{n+m} 𝓖 ⟶ 𝓘^m (𝓘^n 𝓖)`

Let `X` be a scheme, `𝓘` a quasi-coherent sheaf of ideals and `𝓖` a quasi-coherent
`𝒪_X`-module. The ideal-power filtration of `𝓖` and the ideal-power filtration of its member
`𝓘^n 𝓖` are related by the inclusion

`𝓘^{n + m} 𝓖 ⊆ 𝓘^m (𝓘^n 𝓖)`

of subsheaves of `𝓘^n 𝓖`. It is what the step *"after replacing `𝓕` by `𝓘^n 𝓕` we may assume
`n = 0`"* of the proof of [Stacks, Tag 0G2H] needs: a statement proved for the filtration of an
arbitrary coherent module, applied to `𝓘^n 𝓖`, concludes about `𝓘^m (𝓘^n 𝓖)`, and this inclusion
converts that into a conclusion about `𝓘^{n + m} 𝓖`, which is the member of the filtration of
`𝓖` that the statement for `𝓖` at stage `n` asks about.

## Main definitions

* `AlgebraicGeometry.sheafSubmoduleLift`: a morphism whose image lies in a subsheaf of its
  target, factored through that subsheaf.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulIterate`: **the inclusion
  `𝓘^{n + m} 𝓖 ⟶ 𝓘^m (𝓘^n 𝓖)`.**

## Main results

* `AlgebraicGeometry.sheafSubmoduleLift_comp_ι`: the factorisation recovers the morphism.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.idealPowSmulIterate_comp_ι`: **the inclusion
  `𝓘^{n + m} 𝓖 ⟶ 𝓘^m (𝓘^n 𝓖)`, followed by the inclusion of `𝓘^m (𝓘^n 𝓖)` into `𝓘^n 𝓖`, is the
  inclusion `𝓘^{n + m} 𝓖 ⟶ 𝓘^n 𝓖` of the filtration of `𝓖`.** This is what makes the comparison
  usable on `Ext`-groups, where only its composites with the filtration inclusions appear.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.mk₀_idealPowSmulMap_comp_eq_zero`: **the reduction
  itself, on `Ext`-groups.** A class on `𝓘^n 𝓖` killed by the inclusion of `𝓘^m (𝓘^n 𝓖)` — the
  conclusion of the injectivity half of the core case of [Stacks, Tag 0G2H] applied to the
  module `𝓘^n 𝓖` — is killed by the inclusion `𝓘^{n + m} 𝓖 ⟶ 𝓘^n 𝓖` of the filtration of
  `𝓖`, which is the form the hypothesis `hinj` of
  `AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem` is stated in. It holds in
  every degree.

## Implementation notes

Only the inclusion is constructed, not the equality of the two subsheaves: the two do agree, but
the reverse inclusion is a computation with affine-local images, while this one is the defining
affine-local lower bound of `𝓘^m (𝓘^n 𝓖)` applied to a submodule whose affine sections are known.

`Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule`'s `SheafOfModules.Submodule` has no
pushforward along a morphism, so the inclusion is built from the preimage
`AlgebraicGeometry.sheafSubmoduleComap`: the preimage of `𝓘^m (𝓘^n 𝓖)` under the filtration
inclusion `𝓘^{n + m} 𝓖 ⟶ 𝓘^n 𝓖` is shown to be everything, and `sheafSubmoduleLift` turns that
into the morphism.

Two spellings of the scalars on `Γ(𝓖, U)` meet here: the module structure is declared over
`X.ringCatSheaf.obj.obj (op U)`, which instance search does not recognise as `Γ(X, U)` across
the `TopCat.Sheaf` definition, while the `Submodule` arithmetic and
`Stacks.AlgebraicGeometry.IdealPower.le_idealPowerMultiple_obj` are phrased at `Γ(X, U)`.
`AlgebraicGeometry.secs` is the first spelling ascribed at the second, and it is used throughout
for that reason. The bridge between the two is made **once, with the submodules kept as
variables**, in `AlgebraicGeometry.mem_idealPowerMultiple_of_subInclusion`: specialised to
`idealPowerMultiple`, which is an infimum, the same conversion asks the kernel to unfold the
defining infimum and does not terminate. The implementation note of
`StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/Injectivity.lean` records the same obstruction
for `Stacks.AlgebraicGeometry.IdealPowerColimit.val_subInclusion_app`.

## References

* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.IdealPowerComparison
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe w u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Factoring a morphism through a subsheaf of its target -/

/-- Membership in the preimage subsheaf `AlgebraicGeometry.sheafSubmoduleComap f Q` is
membership of the image in `Q`. -/
public lemma mem_sheafSubmoduleComap {M N : X.Modules} (f : M ⟶ N) (Q : N.Submodule)
    (V : (Opens X)ᵒᵖ) {x : M.val.obj V}
    (hx : (f.val.app V).hom x ∈ Q.toSubmodule.obj V) :
    x ∈ (sheafSubmoduleComap f Q).toSubmodule.obj V := hx

/-- **A morphism whose image lies in a subsheaf `Q` of its target factors through `Q`.** The
hypothesis is that the preimage of `Q` is everything, and the factorisation is the induced
morphism of subsheaves out of the top subsheaf of the source. -/
public def sheafSubmoduleLift {M N : X.Modules} (f : M ⟶ N) (Q : N.Submodule)
    (h : (⊤ : M.Submodule) ≤ sheafSubmoduleComap f Q) : M ⟶ Q.toSheafOfModules :=
  (sheafTopIso M).inv ≫ sheafSubmoduleMap f ⊤ Q h

/-- The factorisation of `AlgebraicGeometry.sheafSubmoduleLift` recovers the morphism: composed
with the inclusion of the subsheaf into the ambient sheaf it is the original morphism. -/
public lemma sheafSubmoduleLift_comp_ι {M N : X.Modules} (f : M ⟶ N) (Q : N.Submodule)
    (h : (⊤ : M.Submodule) ≤ sheafSubmoduleComap f Q) :
    sheafSubmoduleLift f Q h ≫ Q.ι = f := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.Hom.ext
  funext U
  apply ModuleCat.Hom.ext
  ext x
  rfl

/-! ### A section of a subsheaf, read inside a larger subsheaf -/

/-- A section of `A'` which is given as a section of the ambient module and lies in `J ^ m A'`
there, lies in `J ^ m` times the whole of `A'` when read inside `A'`. The inclusion
`A' ⟶ M` carries `J ^ m • ⊤` onto `J ^ m • secs A' V` and is injective. -/
public lemma mem_smul_top_secs {R : Type*} [CommSemiring R] {M : Type*}
    [AddCommMonoid M] [Module R M] (N : Submodule R M) (J : Ideal R) (m : ℕ) (y : N)
    (hy : (y : M) ∈ J ^ m • N) : y ∈ J ^ m • (⊤ : Submodule R N) := by
  have hmap : (J ^ m • (⊤ : Submodule R N)).map N.subtype = J ^ m • N := by
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_subtype]
  rw [← hmap] at hy
  obtain ⟨w, hw, hwy⟩ := Submodule.mem_map.mp hy
  exact (Subtype.ext hwy : w = y) ▸ hw

/-- **The affine-local step of the comparison, with the two submodules kept variable.** A
section of a subsheaf `A` of `M`, whose value in `M` lies in `𝓘(U) ^ m` times the sections of a
larger subsheaf `A'`, lies in the preimage of `𝓘^m A'` under the inclusion `A ⟶ A'`.

Both the conversion from a section of `M` to a section of `A'` and the defining lower bound of
`𝓘^m A'` are applied here, once and for all: at a concrete `A'` the first conversion asks the
kernel to unfold the infimum defining
`Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple` and does not terminate. -/
public lemma mem_idealPowerMultiple_of_subInclusion (I : X.IdealSheafData) (m : ℕ)
    {M : X.Modules} {A A' : M.Submodule} (hle : A ≤ A') (U : X.affineOpens)
    (z : Γ(subMod A, U.1)) (hz : (z.1 : Γ(M, U.1)) ∈ I.ideal U ^ m • secs A' U.1) :
    z ∈ (sheafSubmoduleComap (subInclusion hle)
      (idealPowerMultiple I m (subMod A'))).toSubmodule.obj (op U.1) :=
  mem_sheafSubmoduleComap _ _ _
    (le_idealPowerMultiple_obj I m (subMod A') U
      (mem_smul_top_secs (secs A' U.1) (I.ideal U) m _ hz))

end AlgebraicGeometry

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}} (I : X.IdealSheafData) (n m : ℕ) (G : X.Modules) [G.IsQuasicoherent]

/-! ### The inclusion `𝓘^{n + m} 𝓖 ⊆ 𝓘^m (𝓘^n 𝓖)` -/

/-- The sections of `𝓘^{n + m} 𝓖` over an affine open lie in `𝓘(U) ^ m` times the sections of
`𝓘^n 𝓖`, because `𝓘(U) ^ {n + m} = 𝓘(U) ^ m 𝓘(U) ^ n` and the sections of a member of the
ideal-power filtration over an affine open are the corresponding product
(`Stacks.AlgebraicGeometry.IdealPowerComparison.obj_idealPowerMultiple`). -/
public lemma val_mem_smul_secs_idealPowerMultiple (U : X.affineOpens)
    (z : Γ(idealPowSmul I (n + m) G, U.1)) :
    (z.1 : Γ(G, U.1)) ∈ I.ideal U ^ m • secs (idealPowerMultiple I n G) U.1 := by
  have hsecs : secs (idealPowerMultiple I n G) U.1 =
      I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1)) := obj_idealPowerMultiple I n G U
  have hpow : I.ideal U ^ m • (I.ideal U ^ n • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1))) =
      I.ideal U ^ (n + m) • (⊤ : Submodule Γ(X, U.1) Γ(G, U.1)) := by
    rw [← mul_smul, ← pow_add, Nat.add_comm m n]
  rw [hsecs, hpow]
  exact (obj_idealPowerMultiple I (n + m) G U).le z.2

/-- **`𝓘^{n + m} 𝓖` lands in `𝓘^m (𝓘^n 𝓖)`**: the preimage, under the inclusion
`𝓘^{n + m} 𝓖 ⟶ 𝓘^n 𝓖` of the filtration of `𝓖`, of the subsheaf `𝓘^m (𝓘^n 𝓖)` of `𝓘^n 𝓖` is
everything.

Membership in a subsheaf is affine-local
(`AlgebraicGeometry.sheafSubmodule_eq_top_of_affine`), and over an affine open the containment
is `AlgebraicGeometry.mem_idealPowerMultiple_of_subInclusion` applied to
`val_mem_smul_secs_idealPowerMultiple`. -/
public lemma top_le_sheafSubmoduleComap_idealPowerMultiple :
    (⊤ : (idealPowSmul I (n + m) G).Submodule) ≤
      sheafSubmoduleComap (idealPowSmulMap I G (Nat.le_add_right n m))
        (idealPowerMultiple I m (idealPowSmul I n G)) :=
  le_of_eq (sheafSubmodule_eq_top_of_affine _ fun U _ _hz ↦
    mem_idealPowerMultiple_of_subInclusion I m
      (IdealPower.idealPowerMultiple_antitone I G (Nat.le_add_right n m)) U _
      (val_mem_smul_secs_idealPowerMultiple I n m G U _)).symm

/-- **The inclusion `𝓘^{n + m} 𝓖 ⟶ 𝓘^m (𝓘^n 𝓖)`.** -/
public def idealPowSmulIterate :
    idealPowSmul I (n + m) G ⟶ idealPowSmul I m (idealPowSmul I n G) :=
  sheafSubmoduleLift (idealPowSmulMap I G (Nat.le_add_right n m))
    (idealPowerMultiple I m (idealPowSmul I n G))
    (top_le_sheafSubmoduleComap_idealPowerMultiple I n m G)

/-- **The inclusion `𝓘^{n + m} 𝓖 ⟶ 𝓘^m (𝓘^n 𝓖)` is compatible with the inclusions into
`𝓘^n 𝓖`**: followed by the inclusion of `𝓘^m (𝓘^n 𝓖)` into `𝓘^n 𝓖` it is the inclusion
`𝓘^{n + m} 𝓖 ⟶ 𝓘^n 𝓖` of the ideal-power filtration of `𝓖`.

This is the only property of `idealPowSmulIterate` its consumers use: on `Ext`-groups the
comparison appears only through `CategoryTheory.Abelian.Ext.mk₀` of this composite. -/
@[simp] public lemma idealPowSmulIterate_comp_ι :
    idealPowSmulIterate I n m G ≫ submoduleι (idealPowerMultiple I m (idealPowSmul I n G)) =
      idealPowSmulMap I G (Nat.le_add_right n m) :=
  sheafSubmoduleLift_comp_ι _ _ _

/-! ### The reduction "replace `𝓖` by `𝓘^n 𝓖`" on `Ext`-groups -/

/-- **The reduction *"after replacing `𝓕` by `𝓘^n 𝓕` we may assume `n = 0`"* of the proof of
[Stacks, Tag 0G2H], on `Ext`-groups.** A class on `𝓘^n 𝓖` which already dies under the
inclusion of the subsheaf `𝓘^N (𝓘^n 𝓖)` of `𝓘^n 𝓖` — that is, which the statement applied to
the module `𝓘^n 𝓖` at stage `N` kills — also dies under the inclusion `𝓘^{n + N} 𝓖 ⟶ 𝓘^n 𝓖`
of the filtration of `𝓖`, which is the form the identification of
`AlgebraicGeometry.restrictionLifting_singleFunctor_idealPowerSystem` asks for.

This is what `idealPowSmulIterate` is for: the injectivity half of the core case of the tag is
proved for a class on an arbitrary coherent module, hence for `𝓘^n 𝓖`, and this converts the
conclusion back to a statement about the filtration of `𝓖` itself. It holds in every degree
`i`. -/
public theorem mk₀_idealPowSmulMap_comp_eq_zero [HasExt.{w} X.Modules] {F : X.Modules} {i : ℕ}
    (ζ : Ext.{w} (idealPowSmul I n G) F i)
    (h : (Ext.mk₀ (submoduleι (idealPowerMultiple I m (idealPowSmul I n G)))).comp ζ
      (zero_add i) = 0) :
    (Ext.mk₀ (idealPowSmulMap I G (Nat.le_add_right n m))).comp ζ (zero_add i) = 0 := by
  rw [← idealPowSmulIterate_comp_ι I n m G, ← Ext.mk₀_comp_mk₀,
    Ext.comp_assoc_of_second_deg_zero, h, Ext.comp_zero]

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
