module

public import StacksFrontier.AlgebraicGeometry.Modules.TildeExteriorPower

/-!
# Exterior powers of the sheaf associated to a module, on an arbitrary ringed space

Let `(X, 𝒪_X)` be a ringed space, `α : R → Γ(X, 𝒪_X)` a ring homomorphism and `M` an
`R`-module. Construction (3) of Stacks 01BH attaches to these the sheaf of `𝒪_X`-modules
`ℱ_M = ` `Stacks.AssociatedSheaf.associatedSheaf X α M`, the sheafification of
`U ↦ 𝒪_X(U) ⊗_R M`. This file proves that **taking exterior powers commutes with that
construction**:

```
ℱ_{⋀ⁿ_R M} ≅ ⋀ⁿ(ℱ_M)
```

for an arbitrary ringed space, an arbitrary bundle of algebras on `ℱ_M` in the sense of
Section 17.21, and every `n`.

## Main definitions

* `Stacks.AssociatedSheaf.exteriorPowerIso`: **the comparison `ℱ_{⋀ⁿ_R M} ≅ ⋀ⁿ(ℱ_M)`** for an
  arbitrary bundle of tensor, exterior and symmetric algebras on `ℱ_M`.
* `Stacks.AssociatedSheaf.ringedSpaceExteriorPowerIso`: the same comparison for the bundle
  `SheafOfModules.ringedSpaceAlgebras` that the repository attaches to a sheaf of modules on a
  ringed space.
* `Stacks.AssociatedSheaf.model` and `Stacks.AssociatedSheaf.modelAssociatedSheaf`: `ℱ_N`
  written as `SheafOfModules.sheafifyModulePresheaf` of its presheaf model, and the identity
  comparing the two spellings.
* `Stacks.AssociatedSheaf.modelExteriorPowerIsoFull`: the comparison with its source in that
  spelling.

## Implementation notes

`AlgebraicGeometry.tildeExteriorPowerIso`
(`StacksFrontier/AlgebraicGeometry/Modules/TildeExteriorPower.lean`) is this statement on
`Spec R`, and both of its two legs are already general:

* the presheaf-level base-change comparison
  `AlgebraicGeometry.specTildeExteriorPowerPresheafIso` is stated for an arbitrary
  `X : RingedSpace.{u, u}` and an arbitrary `α : R →+* Γ(X, 𝒪_X)`, despite its name — it says
  that `U ↦ 𝒪_X(U) ⊗_R ⋀ⁿ_R M` is the sectionwise degree-`n` exterior power of
  `U ↦ 𝒪_X(U) ⊗_R M`, which is `ExteriorAlgebra.exteriorPowerBaseChange` read over each open;
* `SheafOfModules.presheafModelExteriorPowerIso` is stated for an arbitrary site and an
  arbitrary presheaf model, and says that `⋀ⁿ F` is the sheafification of the sectionwise
  exterior power of any presheaf whose sheafification is `F`.

What the affine statement adds, and what this file does not need, is the comparison of Tag 01I7
between `M~` and the sheafification of `U ↦ 𝒪(U) ⊗_R M`: here the associated sheaf **is** that
sheafification, by definition of construction (3), so the model isomorphism is `Iso.refl`. The
two legs therefore compose directly, and the generality costs nothing beyond rewriting the
affine proof's third leg away.

**Why the junction of the two legs carries no type ascription.** Construction (3) indexes its
presheaves by `Stacks.PresheafOfModules.ChangeOfRings.ringPresheaf X.presheaf` and the
presheaf-model form of Tag 01CG indexes them by
`(CategoryTheory.Sheaf.toRingCat _ X.sheaf).obj`. The two agree, but only after `X.sheaf.obj`
is reduced to `X.presheaf`, which the unifier will not do at `implicit` transparency; faced
with two `PresheafOfModules.exteriorAlgebraPiece` terms whose ring-presheaf arguments are
spelled differently it unfolds the pieces instead, down through `TensorAlgebra` and
`CliffordAlgebra` to `TensorProduct` — a quarter of a million unfoldings of
`SheafedSpace.sheaf` alone, and a `whnf` timeout. So the sheafification functor of the first
leg is written `_` in `modelExteriorPowerIsoFull` and solved from the second leg's source, and
that definition is left with its inferred type: ascribing either spelling to it reinstates the
mismatch and the timeout.

Deliberately UNTAGGED. The exterior-power clause of Tag 01I8 is about `Spec R`, and is already
carried — as part of that tag's fifteen-site covering set — by the affine statement; this is
the ringed-space generalisation, which Tag 01I8 does not state. Tag 01BH's own clauses are
about construction (3) itself, not about its interaction with exterior powers.

## References

* [Stacks Project, Tag 01BH](https://stacks.math.columbia.edu/tag/01BH)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
* [Stacks Project, Tag 01I8](https://stacks.math.columbia.edu/tag/01I8)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry

namespace Stacks.AssociatedSheaf

universe u

attribute [local instance] hasModuleSheafify moduleSheafifyWEqualsLocallyBijective

variable (R : CommRingCat.{u}) (X : RingedSpace.{u, u}) (α : ↥R →+* X.presheaf.obj (op ⊤))
  (M : ModuleCat.{u} ↥R) (n : ℕ)

/-- The sheaf `ℱ_N` of construction (3) in the spelling
`SheafOfModules.sheafifyModulePresheaf`, which is the one the presheaf-model form of Tag 01CG is
stated at.

It is `Stacks.AssociatedSheaf.associatedSheaf X α N` on the nose — that is `modelAssociatedSheaf`
below — but the two differ in how the sheaf of rings is written, `ringSheaf X` against
`CategoryTheory.Sheaf.toRingCat _ X.sheaf`, and the unifier does not identify the two inside a
larger expression within the heartbeat budget. Every intermediate object below is therefore
written in the `toRingCat` spelling, and the change of spelling happens exactly once, in
`modelAssociatedSheaf`. -/
abbrev model (N : ModuleCat.{u} ↥R) : SheafOfModules.{u}
    (CategoryTheory.Sheaf.toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf) :=
  SheafOfModules.sheafifyModulePresheaf (Opens.grothendieckTopology X.carrier)
    (Osharp := X.sheaf) (associatedPresheaf X α N)

/-- `ℱ_N` is the sheafification of its presheaf model, by definition of construction (3). -/
def modelAssociatedSheaf (N : ModuleCat.{u} ↥R) : associatedSheaf X α N ≅ model R X α N :=
  Iso.refl _

/-- **The sheaf associated to `⋀ⁿ_R M` is the `n`-th exterior power of the sheaf associated to
`M`**, with the source in the `SheafOfModules.sheafifyModulePresheaf` spelling.

The composite of the sheafified presheaf-level base-change comparison with the presheaf-model
form of Tag 01CG. The sheafification functor of the first leg is written `_`: solving it against
the second leg's source is what keeps the two legs' indexing sheaves of rings syntactically
equal, and hence keeps the junction out of the two `exteriorAlgebraPiece` terms. -/
def modelExteriorPowerIsoFull
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) (model R X α M)) :=
  (Functor.mapIso _ (specTildeExteriorPowerPresheafIso R X α M n)).trans
    (SheafOfModules.presheafModelExteriorPowerIso (Opens.grothendieckTopology X.carrier)
      (associatedPresheaf X α M) A (Iso.refl _) (n : ℤ))

/-- **The sheaf associated to `⋀ⁿ_R M` is the `n`-th exterior power of the sheaf associated to
`M`.**

The left-hand side is construction (3) of Stacks 01BH applied to the exterior power of the
module; the right-hand side is the degree-`n` exterior power, in the sense of Section 17.21, of
construction (3) applied to the module. -/
def exteriorPowerIso
    (A : SheafOfModules.TensorExteriorSymmetricAlgebras
      (Opens.grothendieckTopology X.carrier) (associatedSheaf X α M)) :
    associatedSheaf X α (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) ≅ A.exteriorPower n :=
  (modelAssociatedSheaf R X α (exteriorPowerSource R M n)).trans
    (modelExteriorPowerIsoFull R X α M n A)

/-- `Stacks.AssociatedSheaf.exteriorPowerIso` for the bundle of algebras the repository attaches
to a sheaf of modules on a ringed space, `SheafOfModules.ringedSpaceAlgebras`. -/
def ringedSpaceExteriorPowerIso :
    associatedSheaf X α (ModuleCat.of ↥R ↥(⋀[↥R]^n ↥M)) ≅
      (SheafOfModules.ringedSpaceAlgebras X (associatedSheaf X α M)).exteriorPower n :=
  exteriorPowerIso R X α M n (SheafOfModules.ringedSpaceAlgebras X (associatedSheaf X α M))

end Stacks.AssociatedSheaf

end
