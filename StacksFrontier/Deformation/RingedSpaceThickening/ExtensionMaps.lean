module

public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.Topology.Sheaves.RingedSpace.Thickening
import StacksCore.Tactic.StacksAttribute

/-!
# Maps between extensions across a first order thickening of ringed spaces (Stacks 08L5)

Let `i : (X, 𝒪_X) ⟶ (X', 𝒪_{X'})` be a first order thickening of ringed spaces and let

    0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0    and    0 ⟶ i_* ℒ ⟶ 𝒢' ⟶ i_* 𝒢 ⟶ 0

be two extensions of `𝒪_{X'}`-modules as in Tag 08L4, together with maps `φ : ℱ ⟶ 𝒢` and
`ψ : 𝒦 ⟶ ℒ`. This file proves the second clause of Tag 08L5: the set of `𝒪_{X'}`-module maps
`φ' : ℱ' ⟶ 𝒢'` compatible with `φ` and `ψ` is, when nonempty, a principal homogeneous space
under `Hom_{𝒪_X}(ℱ, ℒ)`.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.ExtensionPair`: the standing data — the thickening,
  the two extensions, and the maps on their quotient and kernel modules.
* `ExtensionPair.CompatibleMap`: a map of the middle terms inducing the prescribed maps on
  kernels and quotients.

## Main results

* `ExtensionPair.exists_compatibleMap_translate`: **Stacks 08L5**, translating a compatible map
  by `α : ℱ ⟶ ℒ` again gives a compatible map; this is the action of `Hom_{𝒪_X}(ℱ, ℒ)`.
* `ExtensionPair.existsUnique_translate`: **Stacks 08L5**, any two compatible maps differ by a
  unique such `α`, so the action is free and transitive.
* `CategoryTheory.Abelian.YonedaExtension.comp_eq_zero`,
  `CategoryTheory.Abelian.YonedaExtension.exact_shortComplex` and
  `CategoryTheory.Abelian.YonedaExtension.shortExact`: a degree-zero Yoneda extension read as a
  short exact sequence, which is the form in which an extension as in Tag 08L4 is used.

## Implementation notes

The principal homogeneous space is recorded by its translation law rather than through an
abstract torsor structure: `α : ℱ ⟶ ℒ` acts on `φ'` by adding the composite
`ℱ' ⟶ i_* ℱ ⟶ i_* ℒ ⟶ 𝒢'`. The two results above are exactly closure of the set of
compatible maps under that action, and freeness together with transitivity of it.

The extensions are `CategoryTheory.Abelian.YonedaExtension` in degree zero, as in Tag 08L4,
with their outer terms pushed forward along `i`; the uniqueness of `α` is where Tag 08KS
enters, through full faithfulness of `i_*` for the closed quotient morphism
`AlgebraicGeometry.RingedSpaceThickening.closedQuotientOfIsThickening` of the thickening.

## References

* [Stacks Project, Tag 08L5](https://stacks.math.columbia.edu/tag/08L5)
* [Stacks Project, Tag 08L4](https://stacks.math.columbia.edu/tag/08L4)
* [Stacks Project, Tag 08KS](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open RingedSpaceModuleAdjunction

universe u

namespace CategoryTheory.Abelian.YonedaExtension

variable {C : Type*} [Category C] [Abelian C] {B A : C}

/-- The two maps of a degree-zero Yoneda extension compose to zero. -/
theorem comp_eq_zero (E : YonedaExtension B A 0) : E.f ≫ E.g = 0 := by
  exact E.exact_g.toIsComplex.zero 0

/-- The short complex `0 ⟶ A ⟶ E ⟶ B ⟶ 0` of a degree-zero Yoneda extension is exact. -/
theorem exact_shortComplex (E : YonedaExtension B A 0) :
    (ShortComplex.mk E.f E.g (comp_eq_zero E)).Exact := by
  exact E.exact_g.exact 0

/-- A degree-zero Yoneda extension is a short exact sequence. -/
theorem shortExact (E : YonedaExtension B A 0) :
    (ShortComplex.mk E.f E.g (comp_eq_zero E)).ShortExact := by
  have := E.mono_f
  have := E.epi_g
  exact { exact := exact_shortComplex E }

end CategoryTheory.Abelian.YonedaExtension

namespace AlgebraicGeometry.RingedSpaceThickening

/-- The standing data for maps between two extensions across a first order thickening: the
thickening `i`, the quotient and kernel modules of the two extensions, the extensions
themselves, and the prescribed maps `φ : ℱ ⟶ 𝒢` and `ψ : 𝒦 ⟶ ℒ`. -/
structure ExtensionPair where
  /-- The ringed space being thickened. -/
  X : RingedSpace.{u, u}
  /-- The thickened ringed space. -/
  X' : RingedSpace.{u, u}
  /-- The thickening. -/
  i : X ⟶ X'
  /-- The thickening is first order. -/
  firstOrder : IsFirstOrderThickening i
  /-- The quotient module of the first extension. -/
  F : SheafOfModules.{u} (structureSheafRing X)
  /-- The kernel module of the first extension. -/
  K : SheafOfModules.{u} (structureSheafRing X)
  /-- The quotient module of the second extension. -/
  G : SheafOfModules.{u} (structureSheafRing X)
  /-- The kernel module of the second extension. -/
  L : SheafOfModules.{u} (structureSheafRing X)
  /-- The first extension `0 ⟶ i_* 𝒦 ⟶ ℱ' ⟶ i_* ℱ ⟶ 0`. -/
  firstExtension : CategoryTheory.Abelian.YonedaExtension
    ((modulePushforward i).obj F) ((modulePushforward i).obj K) 0
  /-- The second extension `0 ⟶ i_* ℒ ⟶ 𝒢' ⟶ i_* 𝒢 ⟶ 0`. -/
  secondExtension : CategoryTheory.Abelian.YonedaExtension
    ((modulePushforward i).obj G) ((modulePushforward i).obj L) 0
  /-- The prescribed map on quotient modules. -/
  quotientMap : F ⟶ G
  /-- The prescribed map on kernel modules. -/
  kernelMap : K ⟶ L

namespace ExtensionPair

open CategoryTheory.Abelian.YonedaExtension (comp_eq_zero exact_shortComplex)

/-- A map of the middle terms of the two extensions which induces the prescribed maps on their
kernel and quotient modules. -/
structure CompatibleMap (S : ExtensionPair.{u}) where
  /-- The map `ℱ' ⟶ 𝒢'` of `𝒪_{X'}`-modules. -/
  hom : S.firstExtension.Z.left ⟶ S.secondExtension.Z.left
  /-- It restricts to the prescribed map on the kernel modules. -/
  kernel_commutes :
    S.firstExtension.f ≫ hom =
      (modulePushforward S.i).map S.kernelMap ≫ S.secondExtension.f
  /-- It induces the prescribed map on the quotient modules. -/
  quotient_commutes :
    hom ≫ S.secondExtension.g =
      S.firstExtension.g ≫ (modulePushforward S.i).map S.quotientMap

variable (S : ExtensionPair.{u})

/-- **Stacks Project, Tag 08L5.** Translating a compatible map `φ'` by a map `α : ℱ ⟶ ℒ`, that
is adding the composite `ℱ' ⟶ i_* ℱ ⟶ i_* ℒ ⟶ 𝒢'`, again gives a compatible map. This is the
action of `Hom_{𝒪_X}(ℱ, ℒ)` on the set of compatible maps. -/
@[stacks 08L5 "the action on compatible maps"]
theorem exists_compatibleMap_translate (c : CompatibleMap S) (α : S.F ⟶ S.L) :
    ∃ d : CompatibleMap S,
      d.hom = c.hom +
        S.firstExtension.g ≫ (modulePushforward S.i).map α ≫ S.secondExtension.f := by
  set z := S.firstExtension.g ≫ (modulePushforward S.i).map α ≫ S.secondExtension.f with hz
  have hz₁ : S.firstExtension.f ≫ z = 0 := by
    simp [hz, ← Category.assoc, comp_eq_zero]
  have hz₂ : z ≫ S.secondExtension.g = 0 := by
    simp [hz, Category.assoc, comp_eq_zero]
  refine ⟨⟨c.hom + z, ?_, ?_⟩, rfl⟩
  · simp [Preadditive.comp_add, c.kernel_commutes, hz₁]
  · simp [Preadditive.add_comp, c.quotient_commutes, hz₂]

private theorem exists_translate (c d : CompatibleMap S) :
    ∃ α : S.F ⟶ S.L,
      d.hom = c.hom +
        S.firstExtension.g ≫ (modulePushforward S.i).map α ≫ S.secondExtension.f := by
  let E₁ := S.firstExtension
  let E₂ := S.secondExtension
  let P := modulePushforward S.i
  let h := d.hom - c.hom
  have hleft : E₁.f ≫ h = 0 := by
    dsimp [h]
    rw [Preadditive.comp_sub, d.kernel_commutes, c.kernel_commutes, sub_self]
  have hright : h ≫ E₂.g = 0 := by
    dsimp [h]
    rw [Preadditive.sub_comp, d.quotient_commutes, c.quotient_commutes, sub_self]
  let s₁ := exact_shortComplex E₁
  let t := s₁.desc h hleft
  have ht : E₁.g ≫ t = h := s₁.g_desc h hleft
  have htg : t ≫ E₂.g = 0 := by
    apply (cancel_epi E₁.g).1
    simpa [← Category.assoc, ht] using hright
  let s₂ := exact_shortComplex E₂
  let β := s₂.lift t htg
  have hβ : β ≫ E₂.f = t := s₂.lift_f t htg
  have : P.Full := (closedQuotientOfIsThickening S.i S.firstOrder.1).full_modulePushforward
  obtain ⟨α, hα⟩ := (Functor.Full.map_surjective (F := P)) β
  have hdiff : h = E₁.g ≫ P.map α ≫ E₂.f := by
    simp [← hα, ← hβ, ← ht]
  exact ⟨α, by simpa [h, add_comm] using sub_eq_iff_eq_add.mp hdiff⟩

/-- **Stacks Project, Tag 08L5.** Any two compatible maps differ by a unique
`α : ℱ ⟶ ℒ`. Together with `exists_compatibleMap_translate` this says that the set of
compatible maps is, when nonempty, a principal homogeneous space under
`Hom_{𝒪_X}(ℱ, ℒ)`. -/
@[stacks 08L5 "freeness and transitivity of the action"]
theorem existsUnique_translate (c d : CompatibleMap S) :
    ∃! α : S.F ⟶ S.L,
      d.hom = c.hom +
        S.firstExtension.g ≫ (modulePushforward S.i).map α ≫ S.secondExtension.f := by
  obtain ⟨α, hα⟩ := exists_translate S c d
  refine ⟨α, hα, fun β hβ => ?_⟩
  have : (modulePushforward S.i).Faithful :=
    (closedQuotientOfIsThickening S.i S.firstOrder.1).faithful_modulePushforward
  exact (modulePushforward S.i).map_injective <| (cancel_epi S.firstExtension.g).1 <|
    (cancel_mono S.secondExtension.f).1 (add_left_cancel (hα.symm.trans hβ)).symm

end ExtensionPair

end AlgebraicGeometry.RingedSpaceThickening

end
