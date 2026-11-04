module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalizationStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleStructureSheaf

/-!
# Locally quasi-coherent modules on a category fibred in groupoids (Stacks 06WJ)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` be a presheaf of
modules over the structure sheaf of Stacks 06TV. Stacks 06WJ calls `F` *locally
quasi-coherent* when `F` is a sheaf for the étale topology and, for every object `x` of `𝒳`
lying over a scheme `U`, the restriction `x^*F|_{U_ét}` to the small étale site of `U` is a
quasi-coherent sheaf of modules.

The restriction of the underlying abelian presheaf is the one of Stacks 06W1; what this file
adds is its module structure. The scalars have to be moved: the restriction of a module over
the structure sheaf of `𝒳` is naturally a module over the restriction of that structure sheaf,
and quasi-coherence is a statement about modules over the structure sheaf of the small étale
site of `U` (Stacks 03DU). The two presheaves of rings are identified by
`AlgebraicGeometry.Stack.localStructurePresheafIso`, built from the counit of the localization
equivalence of Stacks 06W0 together with the identification of structure sheaves of
Stacks 06W9, and restriction of scalars along it supplies the module structure.

## Main definitions

* `AlgebraicGeometry.Stack.localStructurePresheafIso`: the canonical identification of the
  structure sheaf of the small étale site of `U` with the restriction at `x` of the structure
  sheaf of `𝒳`.
* `AlgebraicGeometry.Stack.restrictModuleToSmallEtale`: **Stacks 06WJ**, the restriction at `x`
  of a presheaf of modules on `𝒳`, as a presheaf of modules on the small étale site of `U`.
* `AlgebraicGeometry.Stack.IsLocallyQuasicoherent`: **Stacks 06WJ**, local quasi-coherence.

## Main results

* `AlgebraicGeometry.Stack.restrictModuleToSmallEtale_presheaf`: the underlying abelian presheaf
  of the restricted module is the restriction of Stacks 06W1, so no sheafification intervenes.

## Implementation notes

The identification of the two presheaves of rings, and therefore the restriction of modules,
is given for an arbitrary topology `τ` on the underlying category of schemes which is coarser
than the fppf one, as elsewhere in this area: the underlying presheaf of
`AlgebraicGeometry.Stack.ringStructureSheafCore` does not depend on `τ` at all, only its sheaf
condition does. Local quasi-coherence itself names the étale topology, because that is the
topology its sheaf condition is for.

The small étale and big fppf sites are assumed to have the same size cutoff, as in
Stacks 06W1, so that they have the same bounded category of schemes. The sections of the
module have an independent universe `m`, which the restriction retains; it is not tied to the
universe of the schemes.

## References

* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 06W9](https://stacks.math.columbia.edu/tag/06W9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- The structure sheaf of the small étale site of the scheme `U` below an object `x` is the
restriction, along the small étale inclusion of Stacks 06W1, of the structure sheaf of the big
fppf site of `U`. Both are the presheaf of global functions on the underlying schemes. -/
theorem smallEtale_structureSheaf_obj_eq {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (x : 𝒳)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj =
      (smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)).op ⋙
        (baseRingStructureSheaf B (p.obj x).left.1 (p.obj x).left.2 τ hτ).obj :=
  rfl

/-- The canonical identification of the structure sheaf of the small étale site of the scheme
`U` below an object `x` with the restriction at `x` of the structure sheaf of `𝒳`.

The restriction at `x` transports along the localization equivalence of Stacks 06W0, and
Stacks 06W9 says that equivalence matches the structure sheaf of `𝒳` with the structure sheaf
of the schemes over `U`; the identification is the resulting composite. -/
noncomputable def localStructurePresheafIso {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj ≅
      restrictToSmallEtale B E h S hS p hp x (ringStructureSheafCore B S hS p hp τ hτ).obj := by
  letI _ := isEquivalence_overPost B S hS p hp x
  let b := Over.post (X := x) (p ⋙ Over.forget (B.obj hS))
  let i := smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x)
  let R := (baseRingStructureSheaf B (p.obj x).left.1 (p.obj x).left.2 τ hτ).obj
  have hlast : i.op ⋙ b.inv.op ⋙ b.op ⋙ R =
      restrictToSmallEtale B E h S hS p hp x (ringStructureSheafCore B S hS p hp τ hτ).obj :=
    congrArg (fun T => i.op ⋙ b.inv.op ⋙ T)
      (ringStructureSheafCore_overPost B S hS p hp τ hτ x).symm
  exact eqToIso (smallEtale_structureSheaf_obj_eq B E h S hS p x τ hτ) ≪≫
    Functor.isoWhiskerLeft i.op (b.asEquivalence.op.invFunIdAssoc R).symm ≪≫ eqToIso hlast

/-- **Stacks 06WJ.** The restriction `x^*F|_{U_ét}` at an object `x` of a presheaf of modules on
`𝒳` to the small étale site of the scheme `U` below `x`: restrict the underlying abelian
presheaf as in Stacks 06W1, then transport the scalars through
`AlgebraicGeometry.Stack.localStructurePresheafIso`. -/
@[stacks 06WJ "the restriction to the small étale site"]
noncomputable def restrictModuleToSmallEtale {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    PresheafOfModules.{m}
      (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj :=
  letI _ := isEquivalence_overPost B S hS p hp x
  let q : SmallEtale E (p.obj x).left.1 (contains_base B E h S hS p x) ⥤ 𝒳 :=
    smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
      (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x
  (PresheafOfModules.pushforward₀ q (ringStructureSheafCore B S hS p hp τ hτ).obj ⋙
    PresheafOfModules.restrictScalars
      (localStructurePresheafIso B E h S hS p hp x τ hτ).hom).obj F

/-- The underlying abelian presheaf of the restricted module is the restriction of Stacks 06W1:
moving the scalars does not change the sections. -/
@[simp]
theorem restrictModuleToSmallEtale_presheaf {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (x : 𝒳)
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    (restrictModuleToSmallEtale B E h S hS p hp x τ hτ F).presheaf =
      restrictToSmallEtale B E h S hS p hp x F.presheaf :=
  rfl

/-- **Stacks 06WJ.** A presheaf of modules over the structure sheaf of a category fibred in
groupoids is *locally quasi-coherent* when it is a sheaf for the étale topology and, at every
object `x` of `𝒳`, its restriction to the small étale site of the scheme below `x` is a
quasi-coherent sheaf of modules.

The source calls the notation nonstandard; it is the condition under which the module is
determined by quasi-coherent modules on the small étale sites of the objects. -/
@[stacks 06WJ "local quasi-coherence"]
noncomputable abbrev IsLocallyQuasicoherent {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    (F : PresheafOfModules.{m}
      (ringStructureSheafCore B S hS p hp (etaleTopology B) (etaleTopology_le_topology B)).obj) :
    Prop :=
  Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf ∧
    ∀ x : 𝒳,
      ∃ hM : Presheaf.IsSheaf
          (SmallEtale.topology E (p.obj x).left.1 (contains_base B E h S hS p x))
          (restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
            (etaleTopology_le_topology B) F).presheaf,
        (⟨restrictModuleToSmallEtale B E h S hS p hp x (etaleTopology B)
            (etaleTopology_le_topology B) F, hM⟩ :
          SheafOfModules
            (SmallEtale.structureSheaf E (p.obj x).left.1
              (contains_base B E h S hS p x))).IsQuasicoherentOnSite

end AlgebraicGeometry.Stack

end
