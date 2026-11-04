module

public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.CoheratorMonoidal
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.MixedTensorFinitePresentation

/-!
# The symmetric monoidal category of coherent modules on an algebraic stack

Let `𝒳` be an algebraic stack. The category `Coh(𝒪_𝒳)` of coherent `𝒪_𝒳`-modules (Stacks 0GR6,
`AlgebraicGeometry.Stack.Coh`) is a symmetric monoidal subcategory of `Mod(𝒪_𝒳)` for the tensor
product of `𝒪_𝒳`-modules of Tag 01CA, the structure
`AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal` whose tensor product is the tensor
product sheaf on the nose: the tensor product of two coherent modules is coherent
(`AlgebraicGeometry.Stack.isCoherent_tensorSheaf`) and so is `𝒪_𝒳`. The inclusion
`Coh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` is then a functor of symmetric monoidal categories.

These are the monoidal structures in which Stacks 0GRJ and 0GRR speak of right exact tensor
functors out of `Coh(𝒪_𝒳)`.

## Main definitions

* `AlgebraicGeometry.Stack.coherentAmbientMonoidal`, `coherentAmbientBraided` and
  `coherentAmbientSymmetric`: the symmetric monoidal structure
  `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal` on `Mod(𝒪_𝒳)`, read on the
  ambient category of `AlgebraicGeometry.Stack.coherentModules`, whose structure sheaf of rings
  is written through `AlgebraicGeometry.Stack.ringStructureSheafCore`.
* `AlgebraicGeometry.Stack.coherentQuasicoherentInclusion`: the inclusion
  `Coh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)`, with its structure of braided monoidal functor
  `AlgebraicGeometry.Stack.coherentQuasicoherentInclusionBraided`.

## Main results

* `AlgebraicGeometry.Stack.isCoherent_sheafOfModules_unit`: `𝒪_𝒳` is coherent, with no
  hypothesis on `𝒳`.
* `AlgebraicGeometry.Stack.isMonoidal_coherentModules`: coherence is a monoidal property of
  `𝒪_𝒳`-modules, so `Coh(𝒪_𝒳)` is a symmetric monoidal category
  (`CategoryTheory.ObjectProperty.fullSymmetricSubcategory`).

## Implementation notes

The base writes the ring sheaf of `Coh(𝒪_𝒳)` as
`AlgebraicGeometry.Stack.ringStructureSheafCore B S hS p hp B.topology le_rfl` and the one of
`Mod(𝒪_𝒳)` as `AlgebraicGeometry.FibredSite.ringStructureSheafCore B S hS p hp .fppf`; the two
are definitionally equal but not reducibly so, so instance search does not carry the monoidal
structure across. `AlgebraicGeometry.Stack.coherentAmbientMonoidal` and its companions are that
same structure, named at the first spelling, and are made local instances only where used, as
`AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal` is.

## References

* [Stacks Project, Tag 0GR6](https://stacks.math.columbia.edu/tag/0GR6)
* [Stacks Project, Tag 0GQM](https://stacks.math.columbia.edu/tag/0GQM)
* [Stacks Project, Tag 0GRJ](https://stacks.math.columbia.edu/tag/0GRJ)
* [Stacks Project, Tag 0GRR](https://stacks.math.columbia.edu/tag/0GRR)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, w} B S hS)

/-- **The structure sheaf of an algebraic stack is coherent**, with no hypothesis on the stack:
it is of finite presentation, being finite locally free, and a module of finite presentation is
quasi-coherent and of finite type. -/
theorem isCoherent_sheafOfModules_unit :
    IsCoherent B S hS 𝒳 (SheafOfModules.unit _) :=
  have h := SheafOfModules.isFinitePresentationOnSite_unit (R := ringStructureSheafCore B S hS
    𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl)
  ⟨⟨@SheafOfModules.isQuasicoherentOnSite_of_isFinitePresentationOnSite _ _ _ _ _ h,
    @SheafOfModules.isFiniteTypeOnSite_of_isFinitePresentationOnSite _ _ _ _ _ h⟩, h⟩

/-- A coherent module on an algebraic stack is quasi-coherent. -/
theorem coherentModules_le_isQuasicoherentOnSite :
    coherentModules.{u, u, w} B S hS 𝒳 ≤
      SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl) :=
  fun _ hM ↦ hM.1.1

/-- The monoidal structure `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesMonoidal` of
Tag 01CA on `Mod(𝒪_𝒳)`, on the ambient category of `AlgebraicGeometry.Stack.coherentModules`. -/
@[instance_reducible]
def coherentAmbientMonoidal :
    MonoidalCategory (SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) :=
  AlgebraicStacks.fppfModulesMonoidal B S hS 𝒳

/-- The braiding `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesBraided`, on the ambient
category of `AlgebraicGeometry.Stack.coherentModules`. -/
@[instance_reducible]
def coherentAmbientBraided :
    letI := coherentAmbientMonoidal B S hS 𝒳
    BraidedCategory (SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) :=
  AlgebraicStacks.fppfModulesBraided B S hS 𝒳

/-- The symmetry `AlgebraicGeometry.Stack.AlgebraicStacks.fppfModulesSymmetric`, on the ambient
category of `AlgebraicGeometry.Stack.coherentModules`. -/
@[instance_reducible]
def coherentAmbientSymmetric :
    letI := coherentAmbientMonoidal B S hS 𝒳
    letI := coherentAmbientBraided B S hS 𝒳
    SymmetricCategory (SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl)) :=
  AlgebraicStacks.fppfModulesSymmetric B S hS 𝒳

section Monoidal

attribute [local instance] coherentAmbientMonoidal coherentAmbientBraided
  coherentAmbientSymmetric

/-- **Coherence is a monoidal property of `𝒪_𝒳`-modules** on an algebraic stack: the tensor
product sheaf of two coherent modules is coherent
(`AlgebraicGeometry.Stack.isCoherent_tensorSheaf`), and `𝒪_𝒳` is coherent. Together with
`CategoryTheory.ObjectProperty.fullMonoidalSubcategory`,
`CategoryTheory.ObjectProperty.fullBraidedSubcategory` and
`CategoryTheory.ObjectProperty.fullSymmetricSubcategory` this makes `Coh(𝒪_𝒳)` a symmetric
monoidal category. -/
instance isMonoidal_coherentModules : (coherentModules.{u, u, w} B S hS 𝒳).IsMonoidal where
  prop_tensor F G hF hG := isCoherent_tensorSheaf B S hS 𝒳 F G hF hG
  prop_unit := isCoherent_sheafOfModules_unit B S hS 𝒳

/-- The inclusion `Coh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` of coherent modules into quasi-coherent modules on an
algebraic stack. -/
abbrev coherentQuasicoherentInclusion :
    Coh.{u, u, w} B S hS 𝒳 ⥤ AlgebraicStacks.quasicoherentModules B S hS 𝒳 :=
  ObjectProperty.ιOfLE (coherentModules_le_isQuasicoherentOnSite B S hS 𝒳)

attribute [local instance] AlgebraicStacks.fppfModulesMonoidal AlgebraicStacks.fppfModulesBraided
  AlgebraicStacks.fppfModulesSymmetric

/-- **The inclusion `Coh(𝒪_𝒳) ⥤ QCoh(𝒪_𝒳)` is a functor of symmetric monoidal categories**, for
the structures of `AlgebraicGeometry.Stack.isMonoidal_coherentModules` and
`AlgebraicGeometry.Stack.AlgebraicStacks.isMonoidal_isQuasicoherentOnSite`: both are full
monoidal subcategories of `Mod(𝒪_𝒳)` for the tensor product sheaf. -/
@[instance_reducible]
def coherentQuasicoherentInclusionBraided :
    (coherentQuasicoherentInclusion B S hS 𝒳).Braided :=
  letI : (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        B.topology le_rfl)).IsMonoidal :=
    AlgebraicStacks.isMonoidal_isQuasicoherentOnSite B S hS 𝒳
  inferInstanceAs (ObjectProperty.ιOfLE (coherentModules_le_isQuasicoherentOnSite B S hS 𝒳)).Braided

end Monoidal

end AlgebraicGeometry.Stack
