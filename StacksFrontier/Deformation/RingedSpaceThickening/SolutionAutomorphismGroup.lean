module

public import StacksFrontier.Deformation.RingedSpaceThickening.SolutionAutomorphisms
import StacksCore.Tactic.StacksAttribute

/-!
# The automorphism group of a solution of a deformation problem of ringed spaces (Stacks 08UZ (3))

Fix a first order thickening `t : (S, 𝒪_S) ⟶ (S', 𝒪_{S'})` of ringed spaces, a morphism
`f : (X, 𝒪_X) ⟶ (S, 𝒪_S)`, an `𝒪_X`-module `𝒢` and an `f`-map `c : 𝒥 ⟶ 𝒢`, and let `Q` be a
solution `X'` of the deformation problem (08UY). The endomorphisms of `X'` fitting into (08UY)
are the `AlgebraicGeometry.RingedSpaceThickening.SolutionHom Q Q`; every one is invertible
(`SolutionHom.isIso_hom`), so they are the automorphisms of `X'` in the diagram, and under
composition they form a group. This file builds that group and identifies it, as a group, with
the additive group `Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)`: clause (3) of **Stacks 08UZ**.

## Main definitions

* `...SolutionHom.instGroup`: the automorphisms of a solution form a group under composition,
  with `(e₁ * e₂).hom = e₂.hom ≫ e₁.hom` (that is, `e₁ ∘ e₂`), unit the identity, and inverse
  the inverse morphism of ringed spaces.
* `...DeformationSolution.solutionAutMulEquivCotangentExt`: **Stacks 08UZ, clause (3).** The
  group of automorphisms of `X'` fitting into (08UY) is isomorphic to the additive group
  `Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)`. Its underlying bijection is
  `...DeformationSolution.solutionHomEquivCotangentExt`.

## Implementation notes

An automorphism of a solution is `x ↦ x + δ(x)` for a unique relative derivation `δ`
(`solutionHomEquivSDerivation`). Composition corresponds to addition:
`(id + δ₁) ∘ (id + δ₂) = id + δ₁ + δ₂`, because `δ₁` vanishes on the ideal `𝒢` into which
`δ₂` lands (`dval_incl`; the ideal has square zero). This is `derivationHom_comp`. The
identifications of the derivations with `Hom_{𝒪_X}(Ω_{X/S}, 𝒢)` (corepresentability,
`SheafOfModules.derivationsAddCommGrpCorepresentation`) and of the latter with
`Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)` (`extZeroCotangentAddEquiv`) are additive.

That the composite and the inverse of automorphisms of a solution are again the identity on the
prescribed ideal is obtained from the same formula: each of them is the endomorphism attached to
a derivation, which is the identity on the ideal by `derivationHom_kernel_comm`.

## References

* [Stacks Project, Tag 08UZ](https://stacks.math.columbia.edu/tag/08UZ)
* [Stacks Project, Tag 08UY](https://stacks.math.columbia.edu/tag/08UY), the deformation problem
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Sheaves.RingedSpaceDifferentials

/-- The relative derivations of `𝒪_X` over `f⁻¹𝒪_S` with values in an `𝒪_X`-module `F` form an
additive group under termwise addition. -/
noncomputable instance instAddCommGroupSDerivation {X S : RingedSpace.{u, u}} (f : X ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X)) : AddCommGroup (SDerivation f F) :=
  AlgebraicGeometry.SheafOfModules.derivationAddCommGroup (inverseImageStructureMap f).hom F.val

end Stacks.Sheaves.RingedSpaceDifferentials

namespace AlgebraicGeometry.RingedSpaceThickening

variable {X S S' : RingedSpace.{u, u}} {t : S ⟶ S'}
  {ht : IsFirstOrderThickening t} {f : X ⟶ S}
  {G : SheafOfModules.{u} (structureSheafRing X)}
  {c : (modulePullback f).obj
    ((modulePullback t).obj (AlgebraicGeometry.SheafOfModules.idealSheaf t)) ⟶ G}

namespace DeformationSolution

variable (Q : DeformationSolution t ht f G c)

/-! ### Composition of automorphisms is addition of derivations -/

/-- The value on reductions of a sum of derivations is the sum of the values. -/
theorem dval_add_derivation
    (D₁ D₂ : Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G)
    {W : (Opens Q.X'.carrier)ᵒᵖ} (x : Q.X'.presheaf.obj W) :
    Q.dval (D₁ + D₂) x = Q.dval D₁ x + Q.dval D₂ x :=
  rfl

/-- **Composition is addition, on the structure sheaf.** Following `x ↦ x + δ₂(x)` by
`x ↦ x + δ₁(x)` gives `x ↦ x + δ₁(x) + δ₂(x)`: `δ₁` vanishes on the value `δ₂(x)`, a section of
the square-zero ideal `𝒢`. -/
theorem derivationComorphism_comp
    (D₁ D₂ : Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G) :
    Q.derivationComorphism D₂ ≫ Q.derivationComorphism D₁ =
      Q.derivationComorphism (D₁ + D₂) := by
  refine NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun x => ?_))
  change ((Q.derivationComorphism D₁).app W).hom (((Q.derivationComorphism D₂).app W).hom x) =
    ((Q.derivationComorphism (D₁ + D₂)).app W).hom x
  rw [Q.derivationComorphism_app, Q.derivationComorphism_app, Q.derivationComorphism_app,
    Q.dval_add, Q.dval_incl, add_zero, Q.dval_add_derivation, Q.incl_add]
  abel

/-- The endomorphism of the deformed space with comorphism `k` is the one attached to `D` if `k`
is the comorphism of `D`. -/
private theorem derivationHom_eq_mk {D : Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G}
    {k : Q.X'.presheaf ⟶ Q.X'.presheaf} (hk : k = Q.derivationComorphism D) :
    (⟨⟨𝟙 Q.X'.carrier, k⟩⟩ : Q.X' ⟶ Q.X') = Q.derivationHom D :=
  congrArg (fun k => (⟨⟨𝟙 Q.X'.carrier, k⟩⟩ : Q.X' ⟶ Q.X')) hk

/-- **Composition is addition.** The composite of the endomorphisms of the deformed space
attached to two derivations is the endomorphism attached to their sum. -/
theorem derivationHom_comp
    (D₁ D₂ : Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G) :
    Q.derivationHom D₁ ≫ Q.derivationHom D₂ = Q.derivationHom (D₁ + D₂) := by
  exact Q.derivationHom_eq_mk (Q.derivationComorphism_comp D₁ D₂)

/-- The endomorphism attached to the zero derivation is the identity. -/
theorem derivationHom_zero : Q.derivationHom 0 = 𝟙 Q.X' := by
  have hc : 𝟙 Q.X'.presheaf = Q.derivationComorphism 0 := by
    refine NatTrans.ext (funext fun W => CommRingCat.hom_ext (RingHom.ext fun x => ?_))
    change x = x + Q.incl (Q.dval 0 x)
    rw [show Q.dval 0 x = 0 from rfl, Q.incl_zero, add_zero]
  exact (Q.derivationHom_eq_mk hc).symm

/-- An automorphism of a solution is the endomorphism attached to its derivation. -/
theorem hom_eq_derivationHom (e : SolutionHom Q Q) :
    e.hom = Q.derivationHom e.toDerivation :=
  (congrArg SolutionHom.hom (Q.derivationSolutionHom_toDerivation e)).symm

/-- An endomorphism of the deformed space under `X` which is the endomorphism attached to a
derivation is the identity on the prescribed ideal. -/
theorem kernel_comm_of_eq_derivationHom
    (D : Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G) {h : Q.X' ⟶ Q.X'}
    (hh : h = Q.derivationHom D) (hi : Q.i ≫ h = Q.i) :
    Q.idealInclusion ≫ SheafOfModules.unitToPushforwardObjUnit (structureSheafHom h) =
      (pushforwardIsoOfComp Q.i h Q.i hi).hom.app G ≫
        (modulePushforward h).map Q.idealInclusion := by
  subst hh
  exact Q.derivationHom_kernel_comm D

end DeformationSolution

/-! ### The group of automorphisms of a solution -/

namespace SolutionHom

variable {Q : DeformationSolution t ht f G c}

/-- The composite `e₁ ∘ e₂` of two automorphisms of a solution, as an automorphism of the
solution. -/
noncomputable def selfComp (e₁ e₂ : SolutionHom Q Q) : SolutionHom Q Q where
  hom := e₂.hom ≫ e₁.hom
  thickening_comm := by rw [← Category.assoc, e₂.thickening_comm, e₁.thickening_comm]
  base_comm := by rw [Category.assoc, e₁.base_comm, e₂.base_comm]
  kernel_comm := Q.kernel_comm_of_eq_derivationHom (e₁.toDerivation + e₂.toDerivation)
    ((congrArg₂ (· ≫ ·) (Q.hom_eq_derivationHom e₂) (Q.hom_eq_derivationHom e₁)).trans
      ((Q.derivationHom_comp _ _).trans (congrArg Q.derivationHom (add_comm _ _)))) _

/-- The inverse of an automorphism of a solution, as an automorphism of the solution: the
inverse morphism of ringed spaces, which exists by `SolutionHom.isIso_hom`. -/
noncomputable def selfInv (e : SolutionHom Q Q) : SolutionHom Q Q :=
  haveI := e.isIso_hom
  { hom := inv e.hom
    thickening_comm := by rw [IsIso.comp_inv_eq, e.thickening_comm]
    base_comm := by rw [IsIso.inv_comp_eq, e.base_comm]
    kernel_comm := Q.kernel_comm_of_eq_derivationHom (-e.toDerivation)
      (IsIso.inv_eq_of_hom_inv_id
        ((congrArg (· ≫ Q.derivationHom (-e.toDerivation)) (Q.hom_eq_derivationHom e)).trans
          ((Q.derivationHom_comp _ _).trans
            ((congrArg Q.derivationHom (add_neg_cancel _)).trans Q.derivationHom_zero)))) _ }

/-- **The automorphisms of a solution form a group under composition**: the product `e₁ * e₂`
is the composite `e₁ ∘ e₂`, the unit is the identity, and the inverse is the inverse morphism
of ringed spaces. -/
noncomputable instance instGroup : Group (SolutionHom Q Q) where
  mul := selfComp
  one := SolutionHom.id Q
  inv := selfInv
  mul_assoc _ _ _ := ext' (Category.assoc _ _ _).symm
  one_mul _ := ext' (Category.comp_id _)
  mul_one _ := ext' (Category.id_comp _)
  inv_mul_cancel e :=
    haveI := e.isIso_hom
    ext' (IsIso.hom_inv_id e.hom)

/-- The product of two automorphisms of a solution is their composite. -/
theorem mul_hom (e₁ e₂ : SolutionHom Q Q) : (e₁ * e₂).hom = e₂.hom ≫ e₁.hom :=
  rfl

/-- The unit automorphism of a solution is the identity. -/
theorem one_hom : (1 : SolutionHom Q Q).hom = 𝟙 Q.X' :=
  rfl

/-- The inverse of an automorphism of a solution is the inverse morphism of ringed spaces. -/
theorem inv_hom (e : SolutionHom Q Q) :
    haveI := e.isIso_hom
    e⁻¹.hom = inv e.hom :=
  rfl

end SolutionHom

namespace DeformationSolution

variable (Q : DeformationSolution t ht f G c)

/-- The derivation of a composite of automorphisms of a solution is the sum of their
derivations. -/
theorem toDerivation_mul (e₁ e₂ : SolutionHom Q Q) :
    (e₁ * e₂).toDerivation = e₁.toDerivation + e₂.toDerivation := by
  have h : e₁ * e₂ = Q.derivationSolutionHom (e₁.toDerivation + e₂.toDerivation) :=
    SolutionHom.ext'
      ((congrArg₂ (· ≫ ·) (Q.hom_eq_derivationHom e₂) (Q.hom_eq_derivationHom e₁)).trans
        ((Q.derivationHom_comp _ _).trans (congrArg Q.derivationHom (add_comm _ _))))
  rw [h, Q.toDerivation_derivationSolutionHom]

section CotangentExt

attribute [local instance] HasDerivedCategory.standard

open Stacks.Sheaves.RingedSpaceCotangent in
/-- **Stacks Project, Tag 08UZ, clause (3).** Given a solution `X'` of the deformation problem
of (08UY), the group of automorphisms of `X'` fitting into that diagram is canonically
isomorphic to `Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)`.

The automorphisms in question are the `SolutionHom Q Q`: morphisms of the deformed space under
`X`, over `S'`, and the identity on the prescribed ideal `𝒢`. Every one is invertible by
`SolutionHom.isIso_hom`, so these are the automorphisms of `X'` in the diagram; they form a
group under composition (`SolutionHom.instGroup`, with `SolutionHom.mul_hom`,
`SolutionHom.one_hom`, `SolutionHom.inv_hom`). The isomorphism is a group isomorphism onto the
additive group `Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)`, written multiplicatively. Its underlying bijection is
`solutionHomEquivCotangentExt`: an automorphism is `x ↦ x + δ(x)` for a unique relative
derivation `δ` of `𝒪_X` over `f⁻¹𝒪_S` with values in `𝒢`, and these derivations are
`Hom_{𝒪_X}(Ω_{X/S}, 𝒢) = Ext⁰_{𝒪_X}(L_{X/S}, 𝒢)`. Composition goes to addition because
`(id + δ₁) ∘ (id + δ₂) = id + δ₁ + δ₂`, the ideal having square zero (`toDerivation_mul`). -/
@[stacks 08UZ "clause (3): the group of automorphisms of a solution X' fitting into (08UY), \
under composition, is isomorphic to the additive group Ext^0(L_{X/S}, G)"]
noncomputable def solutionAutMulEquivCotangentExt :
    SolutionHom Q Q ≃* Multiplicative (cotangentExt f G 0) where
  toEquiv := Q.solutionHomEquivCotangentExt.trans Multiplicative.ofAdd
  map_mul' e₁ e₂ := by
    let A : Stacks.Sheaves.RingedSpaceDifferentials.SDerivation f G ≃+ cotangentExt f G 0 :=
      ((AlgebraicGeometry.SheafOfModules.derivationsAddCommGrpCorepresentation.{u, u, u, u}
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageSheaf f) X.sheaf
          (Stacks.Sheaves.RingedSpaceDifferentials.inverseImageStructureMap f)
          (moduleOfDifferentials_corepresentableBy f)).app G).addCommGroupIsoToAddEquiv.symm.trans
        (extZeroCotangentAddEquiv f G).symm
    change Multiplicative.ofAdd (A (e₁ * e₂).toDerivation) =
      Multiplicative.ofAdd (A e₁.toDerivation) * Multiplicative.ofAdd (A e₂.toDerivation)
    rw [Q.toDerivation_mul]
    exact congrArg Multiplicative.ofAdd (A.map_add _ _)

/-- The underlying bijection of `solutionAutMulEquivCotangentExt` is
`solutionHomEquivCotangentExt`. -/
theorem solutionAutMulEquivCotangentExt_apply (e : SolutionHom Q Q) :
    Q.solutionAutMulEquivCotangentExt e =
      Multiplicative.ofAdd (Q.solutionHomEquivCotangentExt e) :=
  rfl

end CotangentExt

end DeformationSolution

end AlgebraicGeometry.RingedSpaceThickening

end
