module

public import StacksFrontier.AlgebraicGeometry.DeRham.FirstChernClass.HodgeClassShifted
public import StacksFrontier.AlgebraicGeometry.DeRham.HodgeCohomology.CanonicalCupProductBridge
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.Situation

/-!
# The Hodge first Chern class in the module realization of Hodge cohomology

Let `f : X ⟶ S` be a morphism of schemes. The Hodge first Chern class
`c₁^{Hodge} : Pic(X) ⟶ H¹(X, Ω_{X/S})` of [Stacks, Section 0FLE] is the identification
`Pic(X) = H¹(X, 𝒪_X^*)` followed by the map induced by `d log : 𝒪_X^* ⟶ Ω_{X/S}`. Since `d log`
is only additive, it is formed in the cohomology of the sheaf of abelian groups underlying
`Ω_{X/S}`. The cup product on Hodge cohomology `H^*_{Hodge}(X/S)`, on the other hand, is formed on
the groups `H^q(X, Ω^p_{X/S})` computed as the cohomology of the derived global sections of
`Ω^p_{X/S}` as a sheaf of `f⁻¹𝒪_S`-modules. This file reads `c₁^{Hodge}` in the latter groups:
the degree-one generator `Ω_{X/S} ⟶ ⋀¹Ω_{X/S}` is an isomorphism, and the cohomology of the
abelian sheaf underlying `⋀¹Ω_{X/S}` is its cohomology as a sheaf of modules
([Stacks, Tag 01F1]), so `H¹(X, Ω_{X/S})` is the summand `H¹(X, Ω¹_{X/S})` of
`H²_{Hodge}(X/S)`, and `c₁^{Hodge}` becomes a homomorphism
`Pic(X) ⟶ H¹(X, Ω¹_{X/S}) ⊂ H²_{Hodge}(X/S)`. This is the datum (D2') of a Weil cohomology
theory for Hodge cohomology ([Stacks, Remark 0FWE]).

## Main definitions

* `Stacks.HodgeWeil.hodgeCohomologyOneIsoComponent`: the identification of `H¹(X, Ω_{X/S})`,
  computed in abelian sheaves, with `H¹(X, Ω¹_{X/S})`, computed in sheaves of modules.
* `Stacks.HodgeWeil.hodgeFirstChernClassModule`: **the Hodge first Chern class**
  `c₁^{Hodge} : Pic(X) ⟶ H¹(X, Ω¹_{X/S})` in the module realization.

## Main results

* `Stacks.HodgeWeil.hodgeFirstChernClassModule_apply` and
  `Stacks.HodgeWeil.hodgeCohomologyOneIsoComponent_inv_hodgeFirstChernClassModule`: the class is
  `AlgebraicGeometry.Scheme.Hom.hodgeFirstChernClass` read through the identification.
* `Stacks.HodgeWeil.hodgeFirstChernClassModule_picardClassOf`: its value on the class of an
  invertible module, in the spelling of `Stacks.WeilCohomology.picardClassOf`.
* `Stacks.HodgeWeil.hodgeFirstChernClassModule_schemePullbackClassHom`: compatibility with
  pullback along a commutative square of schemes, for the pullback on `H¹(X, Ω_{X/S})` of the
  abelian realization read through the identification.

## Implementation notes

The identification is `AlgebraicGeometry.SheafOfModules.hodgeComponentAbelianIso`, the one along
which the cup product `AlgebraicGeometry.SheafOfModules.hodgeComponentCup` of the module
realization is shown to be the cup product of the abelian realization
(`AlgebraicGeometry.SheafOfModules.hodgeComponentCup_exteriorProductComponent`), preceded by the
degree-one generator `Ω_{X/S} ⟶ ⋀¹Ω_{X/S}`. The de Rham differential entering
`hodgeComponentAbelianIso` is the canonical one; the groups compared do not depend on it.

The Picard group `Stacks.Picard.ofScheme X` on which
`AlgebraicGeometry.Scheme.Hom.hodgeFirstChernClass` is defined and the Picard group
`AlgebraicGeometry.Scheme.picardGroup X` of the data of a Weil cohomology theory are the same
group by definition: both are the group of isomorphism classes of invertible modules over the
structure sheaf of `X` read as a sheaf of rings, the two sheaf conditions differing only as
proofs. So `hodgeFirstChernClassModule` is also a homomorphism on `X.picardGroup`.

## References

* [Stacks Project, Remark 0FWE](https://stacks.math.columbia.edu/tag/0FWE)
* [Stacks Project, Section 0FLE](https://stacks.math.columbia.edu/tag/0FLE)
* [Stacks Project, Tag 0FMD](https://stacks.math.columbia.edu/tag/0FMD)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.Leray (sectionsFunctor)

universe u

namespace Stacks.HodgeWeil

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **`H¹(X, Ω_{X/S})` computed in abelian sheaves is `H¹(X, Ω¹_{X/S})` computed in sheaves of
modules**: the degree-one generator `Ω_{X/S} ⟶ ⋀¹Ω_{X/S}`, an isomorphism, followed by the
comparison `AlgebraicGeometry.SheafOfModules.hodgeComponentAbelianIso` of [Stacks, Tag 01F1]. -/
def hodgeCohomologyOneIsoComponent :
    Scheme.Hom.hodgeCohomologyOne f ≅
      (forget₂ (ModuleCat.{u} _) AddCommGrpCat.{u}).obj
        (SheafOfModules.hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) 1 1) :=
  ((sectionsFunctor X.carrier ⊤).rightDerived 1).mapIso
      ((_root_.SheafOfModules.toSheaf X.ringCatSheaf).mapIso
        (@asIso _ _ _ _ (Scheme.Modules.exteriorGenerator (Scheme.Hom.relativeDifferentials f))
          (Scheme.Hom.isIso_exteriorGenerator_relativeDifferentials f))) ≪≫
    SheafOfModules.hodgeComponentAbelianIso (Scheme.Hom.deRhamAlgebras f)
      (SheafOfModules.deRhamDifferential (Scheme.Hom.deRhamAlgebras f)) 1 1 1 rfl

/-- **The Hodge first Chern class in the module realization**
`c₁^{Hodge} : Pic(X) ⟶ H¹(X, Ω¹_{X/S}) ⊂ H²_{Hodge}(X/S)`: the Hodge first Chern class
`AlgebraicGeometry.Scheme.Hom.hodgeFirstChernClass` of [Stacks, Section 0FLE] followed by the
identification `hodgeCohomologyOneIsoComponent`. -/
def hodgeFirstChernClassModule :
    Stacks.Picard.ofScheme X →+
      SheafOfModules.hodgeCohomologyComponent (Scheme.Hom.deRhamAlgebras f) 1 1 :=
  (hodgeCohomologyOneIsoComponent f).hom.hom.comp (Scheme.Hom.hodgeFirstChernClass f)

/-- **The module-realization class is the Hodge first Chern class read through the
identification** `H¹(X, Ω_{X/S}) ≅ H¹(X, Ω¹_{X/S})`. -/
theorem hodgeFirstChernClassModule_apply (c : Stacks.Picard.ofScheme X) :
    hodgeFirstChernClassModule f c =
      (hodgeCohomologyOneIsoComponent f).hom.hom (Scheme.Hom.hodgeFirstChernClass f c) :=
  rfl

/-- **The identification carries the module-realization class back to the Hodge first Chern
class** of the abelian realization. -/
theorem hodgeCohomologyOneIsoComponent_inv_hodgeFirstChernClassModule
    (c : Stacks.Picard.ofScheme X) :
    (hodgeCohomologyOneIsoComponent f).inv.hom (hodgeFirstChernClassModule f c) =
      Scheme.Hom.hodgeFirstChernClass f c :=
  ConcreteCategory.congr_hom (hodgeCohomologyOneIsoComponent f).hom_inv_id _

/-- The module-realization class on the class of an invertible `𝒪_X`-module, in the spelling of
`Stacks.WeilCohomology.picardClassOf` used by the data of a Weil cohomology theory: it is the Hodge
first Chern class of the class of the module in `Stacks.Picard.ofScheme X`, read through the
identification. -/
theorem hodgeFirstChernClassModule_picardClassOf (L : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L) :
    hodgeFirstChernClassModule f (Stacks.WeilCohomology.picardClassOf X L hL) =
      (hodgeCohomologyOneIsoComponent f).hom.hom (Scheme.Hom.hodgeFirstChernClass f
        (Stacks.SheafOfModules.picardClass X.toRingedSpace.presheaf
          (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L
          ((Stacks.InvertiblePullback.stacksIsInvertible_iff_algebraicGeometryIsInvertible
            X.presheaf X.ringCatIsSheaf L).mpr hL))) :=
  rfl

/-- **The module-realization Hodge first Chern class commutes with pullback** along a
commutative square of schemes with horizontal arrows `g : X' ⟶ X` and `h : S' ⟶ S`, for the
pullback `H¹(X, Ω_{X/S}) ⟶ H¹(X', Ω_{X'/S'})` of
`AlgebraicGeometry.Scheme.Hom.hodgeCohomologyOnePullback` read through the identifications
`hodgeCohomologyOneIsoComponent` ([Stacks, Tag 0FMD]). -/
theorem hodgeFirstChernClassModule_schemePullbackClassHom {X' S' : Scheme.{u}} (g : X' ⟶ X)
    (f' : X' ⟶ S') (h : S' ⟶ S) (hcomm : g ≫ f = f' ≫ h) (c : Stacks.Picard.ofScheme X) :
    hodgeFirstChernClassModule f' (Stacks.Picard.schemePullbackClassHom g c) =
      (hodgeCohomologyOneIsoComponent f').hom.hom
        ((Scheme.Hom.hodgeCohomologyOnePullback g f f' h hcomm).hom
          ((hodgeCohomologyOneIsoComponent f).inv.hom (hodgeFirstChernClassModule f c))) := by
  rw [hodgeCohomologyOneIsoComponent_inv_hodgeFirstChernClassModule,
    hodgeFirstChernClassModule_apply,
    Scheme.Hom.hodgeFirstChernClass_schemePullbackClassHom g f f' h hcomm]

end Stacks.HodgeWeil

end
