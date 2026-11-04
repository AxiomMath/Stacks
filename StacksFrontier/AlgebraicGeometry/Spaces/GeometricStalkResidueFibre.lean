module

public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.LocalRing.ResidueField.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality

/-!
# The fibre of a module at a geometric point over the residue field

Let `X` be an algebraic space over a scheme `S`, let `F` be a quasi-coherent `𝒪_X`-module of
finite type and let `x̄` be a geometric point of `X`.  The *fibre* of `F` at `x̄` is the base
change

`F_{x̄} ⊗_{𝒪_{X, x̄}} κ(x̄)`

of the geometric stalk of Stacks 05VQ along the residue map of the étale local ring
`𝒪_{X, x̄}` of Stacks 04KG.  The second equivalence of Stacks 07TZ part (2) says that the stalk
is nonzero exactly when the fibre is: this is Nakayama's lemma, and it needs the stalk to be a
finite `𝒪_{X, x̄}`-module.

That finiteness is
`AlgebraicGeometry.Space.module_finite_geometricModuleStalk`, and with it both directions are
already present in this development at the categorical extension of scalars that the fibre is
formed by: the residue map is a local homomorphism onto a field, so
`AlgebraicGeometry.Space.nontrivial_extendScalars_of_isLocalHom` gives one direction from the
finiteness, and `AlgebraicGeometry.Space.nontrivial_of_nontrivial_extendScalars` gives the
other with no hypotheses at all.  Nothing further is needed, so the equivalence carries exactly
the hypotheses of the tag: quasi-coherence and finite type.

The same file records the quasi-coherent case of the containment of supports that
`StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveLocusOpenSubspace` carries as a hypothesis.

## Main definitions

* `AlgebraicGeometry.Space.geometricModuleResidueFibre` is the fibre `F_{x̄} ⊗_{𝒪_{X, x̄}} κ(x̄)`.

## Main results

* `AlgebraicGeometry.Space.nontrivial_geometricModuleStalk_iff_nontrivial_residueFibre` is the
  **second equivalence of Stacks 07TZ part (2)**.
* `AlgebraicGeometry.Space.preimage_supportOfSheaf_subset_supportOfSheaf_modulePullback` is the
  containment `|g|^{-1}(Supp F) ⊆ Supp(g^* F)` for a quasi-coherent module of finite type.

## Implementation notes

The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.SupportGeometricStalkCriterion` declare this equivalence
unavailable for want of the finiteness of the geometric stalk.  That note predates
`AlgebraicGeometry.Space.module_finite_geometricModuleStalk` and is stale.

The equivalence is stated at module universe `m = u`, that is for
`AlgebraicGeometry.Space.Modules.{u, u}`, because the finiteness of the geometric stalk is
available only there.  The fibre itself is defined at every module universe.

## References

* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 04KG](https://stacks.math.columbia.edu/tag/04KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The fibre at a geometric point -/

/-- **The fibre of an `𝒪_X`-module at a geometric point `x̄`**: the base change

`F_{x̄} ⊗_{𝒪_{X, x̄}} κ(x̄)`

of the geometric stalk of Stacks 05VQ along the residue map of the étale local ring
`𝒪_{X, x̄}` of Stacks 04KG, which is a local ring by Stacks 08AH. -/
def geometricModuleResidueFibre (X : AlgebraicSpaces B S hS)
    (x : GeometricPoint B S hS X.1) (F : Modules.{u, m} B S hS X.1 X.2) :
    letI := isLocalRing_etaleLocalRing B S hS X.1 X.2 x
    ModuleCat (IsLocalRing.ResidueField ↥(etaleLocalRing B S hS X.1 x)) :=
  letI := isLocalRing_etaleLocalRing B S hS X.1 X.2 x
  (ModuleCat.extendScalars (IsLocalRing.residue ↥(etaleLocalRing B S hS X.1 x))).obj
    (geometricModuleStalk B S hS X x F)

/-! ### The second equivalence of Stacks 07TZ part (2) -/

/-- **Stacks 07TZ, part (2), second equivalence.** Let `F` be a quasi-coherent `𝒪_X`-module of
finite type on an algebraic space `X` over `S` and let `x̄` be a geometric point of `X`.  Then

`F_{x̄} ≠ 0 ↔ F_{x̄} ⊗_{𝒪_{X, x̄}} κ(x̄) ≠ 0`.

This is Nakayama's lemma.  The stalk is a finite module over the étale local ring by
`AlgebraicGeometry.Space.module_finite_geometricModuleStalk`, and the residue map is a local
homomorphism of local rings, so base change along it keeps a nonzero finite module nonzero
(`AlgebraicGeometry.Space.nontrivial_extendScalars_of_isLocalHom`); the converse direction
needs no hypotheses at all
(`AlgebraicGeometry.Space.nontrivial_of_nontrivial_extendScalars`). -/
@[stacks 07TZ "part (2), second equivalence: the stalk at a geometric point is nonzero iff the \
fibre over the residue field is nonzero"]
theorem nontrivial_geometricModuleStalk_iff_nontrivial_residueFibre (X : AlgebraicSpaces B S hS)
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F) (x : GeometricPoint B S hS X.1) :
    Nontrivial ↥(geometricModuleStalk B S hS X x F) ↔
      letI := isLocalRing_etaleLocalRing B S hS X.1 X.2 x
      Nontrivial ↥(geometricModuleResidueFibre B S hS X x F) := by
  have := isLocalRing_etaleLocalRing B S hS X.1 X.2 x
  have := module_finite_geometricModuleStalk B S hS X F hqc hft x
  refine ⟨fun h => ?_, fun h => nontrivial_of_nontrivial_extendScalars _ _ h⟩
  have := h
  exact nontrivial_extendScalars_of_isLocalHom
    (IsLocalRing.residue ↥(etaleLocalRing B S hS X.1 x)) (geometricModuleStalk B S hS X x F)

/-! ### The containment of supports for a quasi-coherent module -/

variable {X' X : AlgebraicSpaces B S hS}

/-- **The inverse image of the support is contained in the support of the pullback**, for a
quasi-coherent `𝒪_X`-module of finite type: `|g|^{-1}(Supp F) ⊆ Supp(g^* F)`.

This is the half of `AlgebraicGeometry.Space.supportOfSheaf_modulePullback_eq` that needs the
quasi-coherence of `F`; the other half,
`AlgebraicGeometry.Space.supportOfSheaf_modulePullback_subset`, holds for any module of finite
type.  `StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveLocusOpenSubspace` does not carry this
containment as a hypothesis (for an arbitrary module of finite type it would be strictly stronger
than Stacks 07TZ part (3)); that file applies the equality to the cokernel of its map directly,
the cokernel of a map of quasi-coherent modules being quasi-coherent unconditionally. -/
theorem preimage_supportOfSheaf_subset_supportOfSheaf_modulePullback (g : X' ⟶ X)
    (F : Modules.{u, u} B S hS X.1 X.2) (hqc : F.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite F) :
    pointsMap B S hS X'.1 g.hom ⁻¹'
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj F) ⊆
      supportOfSheaf B S hS X'.1
        ((SheafOfModules.toSheaf _).obj ((modulePullback B S hS g).obj F)) :=
  (supportOfSheaf_modulePullback_eq B S hS g F hqc hft).ge

end AlgebraicGeometry.Space

end
