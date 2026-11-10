module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsScaling
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphisms
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0E41, first display: `Inf(𝓓_X) = Der_k(𝒪_X, 𝒪_X)` as `k`-vector spaces

Let `X` be an algebraic space over the field `k` (Example 0E3Z).  `Inf(𝓓_X)` carries the
`k`-vector-space structure of [Stacks Project, Tag 06JV]: addition is composition of
infinitesimal automorphisms and a scalar `c` acts by pushing an automorphism forward along the
rescaling `ε ↦ c ε` of the dual numbers.  The group isomorphism
`Deformation.Examples.spaceInfinitesimalAutomorphismGroupMulEquivDerivations` of the first display
of [Stacks Project, Tag 0E41] carries this action to the action of `k` on `Der_k(𝒪_X, 𝒪_X)`
through the structure morphism `X ⟶ Spec k`:

* `Deformation.Examples.spaceInfinitesimalAutomorphismGroupMulEquivDerivations_pushforward`:
  **the scaling clause.**  For an endomorphism `s` of the dual-number object which is `ε ↦ c ε`
  in a dual-number coordinate, and any arrow `j : xε ⟶ xε` over `s` fixing the pushforward
  `x₀ ⟶ xε`, the pushforward of an infinitesimal automorphism `a` along `j` is an infinitesimal
  automorphism whose derivation is `c` times the derivation of `a`.

  The proof: on total spaces the pushforward `b` satisfies `J ≫ a = b ≫ J` and `J ≫ π = π`, so
  `b ≫ π = J ≫ (θ_a · π)`; the conormal map of `J` on the special fibre is multiplication by `c`
  (`Deformation.Examples.conormalMap_spaceSpecialSubspace_eq_comp_globalSmul`, a sectionwise
  computation on the multiplication by `ε`), so by the precomposition law of the torsor of lifts
  `θ_b = θ_a ≫ c·` (`Deformation.Examples.spaceAutToHom_pushforwardAutomorphism`), and `c·` on the
  conormal module is `c·` on `Hom(Ω_{X/k}, 𝒪_X)`
  (`Deformation.Examples.spaceLiftHomAddEquiv_comp_familySpecialConormalSmul`).
* `Deformation.Examples.spaceInfinitesimalAutomorphismModule` and
  `Deformation.Examples.spaceInfinitesimalAutomorphismLinearEquivDerivations`: the `k`-module
  structure on `Inf(𝓓_X)` and the `k`-linear identification with `Der_k(𝒪_X, 𝒪_X)`, with
  `Deformation.Examples.spaceInfinitesimalAutomorphismModule_smul_eq` identifying `c • a` with the
  pushforward of `a` along `ε ↦ c ε`.
* `Deformation.Examples.spaceInfinitesimalAutomorphismGroup_linearEquivDerivations`:
  **[Stacks Project, Tag 0E41], first display, `k`-linear form.**

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.Space Stacks.Cohomology.SiteModules
open scoped IsMulCommutative

universe u

namespace Deformation.Examples

attribute [local irreducible] modulePullback

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))
variable (X : (BigFppfOver B (Spec (.of Λ)) hΛ)ᵒᵖ ⥤ Type u)
  (hX : IsAlgebraicSpace B (Spec (.of Λ)) hΛ X)
  (toK : X ⟶ yoneda.obj (spaceBaseOver B hΛ hSpec (residueFieldBase Λ k)))

variable {Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
  {x₀ : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber
    (residueFieldObject.{u, u, u} Λ k)}
  {xε : (spaceDeformationProjection B hΛ hSpec X hX toK).Fiber Aε}
  {g : residueFieldObject.{u, u, u} Λ k ⟶ Aε} {e : Aε ⟶ residueFieldObject.{u, u, u} Λ k}
  (hpair : IsCanonicalDualNumberPair g e)
  (i : x₀.1 ⟶ xε.1)

/-- The first identification of the first display, unfolded. -/
theorem spaceInfinitesimalAutomorphismGroupMulEquivDerivations_apply
    (hp : IsPredeformationCategory (spaceDeformationProjection B hΛ hSpec X hX toK))
    (hi : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift g i)
    (a : infinitesimalAutomorphismGroup hp g e hpair i hi) :
    spaceInfinitesimalAutomorphismGroupMulEquivDerivations B hΛ hSpec X hX toK hpair i hp hi a =
      Multiplicative.ofAdd (differentialsHomAddEquiv B (Spec (.of Λ)) hΛ
        (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
        (spaceLiftHomAddEquiv B hΛ hSpec X hX toK hpair i
          (spaceAutToHom B hΛ hSpec X hX toK hpair i a.1))) := by
  rw [spaceInfinitesimalAutomorphismGroupMulEquivDerivations, MulEquiv.trans_apply,
    spaceInfinitesimalAutomorphismGroupMulEquivDifferentialsHom, MulEquiv.trans_apply,
    MulEquiv.trans_apply]
  rfl

/-- **Multiplication by the function `c` after a map out of `Ω_{X/k}` is `c` times its
derivation.** -/
theorem differentialsHomAddEquiv_comp_globalSmul
    (f : sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK) ⟶
      spaceStructureModule B hΛ (spaceOf B hΛ X hX)) (c : k) :
    letI : Module k (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
      derivationModuleOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
        (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
        (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
    @id (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK))
      (differentialsHomAddEquiv B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK)
        (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
        (f ≫ globalSmul (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))
          (spaceResidueFieldRingHom B hΛ hSpec X hX toK c)
          (spaceStructureModule B hΛ (spaceOf B hΛ X hX)))) =
      c • @id (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK))
        (differentialsHomAddEquiv B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK)
        (spaceStructureModule B hΛ (spaceOf B hΛ X hX)) f) := by
  let := derivationAddCommGroupModules B (Spec (.of Λ)) hΛ
    (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
  have h := (differentialsHomGlobalSectionLinearEquiv B (Spec (.of Λ)) hΛ
    (spaceStructureMap B hΛ hSpec X hX toK)
    (spaceStructureModule B hΛ (spaceOf B hΛ X hX))).map_smul
    (spaceResidueFieldRingHom B hΛ hSpec X hX toK c) f
  exact (congrArg (differentialsHomAddEquiv B (Spec (.of Λ)) hΛ _ _)
    (comp_globalSmul (structureRingSheaf B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX))
      (spaceResidueFieldRingHom B hΛ hSpec X hX toK c) f)).trans h

/-- **The scaling clause of the first display of [Stacks Project, Tag 0E41].**  Let `s` be an
endomorphism of the base `Aε` of `xε` which is `ε ↦ c ε` in a dual-number coordinate of `Aε`, and
let `j : xε ⟶ xε` lie over `s` and fix the pushforward `i : x₀ ⟶ xε`.  Then pushing an
infinitesimal automorphism `a` forward along `j` gives an infinitesimal automorphism `b`, and the
derivation of `b` is `c` times the derivation of `a`, `k` acting on `Der_k(𝒪_X, 𝒪_X)` through
the structure morphism `X ⟶ Spec k`. -/
theorem spaceInfinitesimalAutomorphismGroupMulEquivDerivations_pushforward
    (hp : IsPredeformationCategory (spaceDeformationProjection B hΛ hSpec X hX toK))
    (hi : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift g i)
    (c : k) (s : Aε ⟶ Aε)
    (hs : ∃ φ : Aε ≃ₐ[Λ] DualNumber k,
      (∀ t : Aε, (φ t).1 = Aε.residueEquiv (IsLocalRing.residue Aε t)) ∧
      (∀ t : k, φ (s.hom (φ.symm (TrivSqZeroExt.inl t))) = TrivSqZeroExt.inl t) ∧
      φ (s.hom (φ.symm DualNumber.eps)) = c • DualNumber.eps)
    (j : xε.1 ⟶ xε.1) (hj : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift s j)
    (hj0 : i ≫ j = i) (a : infinitesimalAutomorphismGroup hp g e hpair i hi) :
    letI : Module k (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
      derivationModuleOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
        (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
        (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
    ∃ b : infinitesimalAutomorphismGroup hp g e hpair i hi,
      b.val = pushforwardAutomorphismHom hp.cofibered s j hj a.val ∧
        Multiplicative.toAdd
            (spaceInfinitesimalAutomorphismGroupMulEquivDerivations B hΛ hSpec X hX toK hpair i hp
              hi b) =
          c • Multiplicative.toAdd
            (spaceInfinitesimalAutomorphismGroupMulEquivDerivations B hΛ hSpec X hX toK hpair i hp
              hi a) := by
  obtain ⟨c₁, hres₁, hmul₁⟩ := exists_mul_of_dualNumberScaling c s hs
  obtain ⟨c'', hres', hmul'⟩ := exists_mul_of_eq
    (IsHomLift.domain_eq (spaceDeformationProjection B hΛ hSpec X hX toK) s j) s c hres₁ hmul₁
  let c' : xε.1.left.base := c''
  have hker := ker_eq_maximalIdeal_of_hom_residueFieldBase
    (spacePointResidue B hΛ hSpec X hX toK xε.1)
  have hσ : ∀ x ∈ RingHom.ker xε.1.hom.base.hom.toRingHom, j.left.base.hom x = c' * x := by
    intro x hx
    rw [show j.left.base = _ from
      IsHomLift.fac' (spaceDeformationProjection B hΛ hSpec X hX toK) s j]
    exact hmul' x ((congrArg (x ∈ ·) hker).mp hx)
  have hc : xε.1.hom.base.hom c' = c :=
    (residueFieldBase_residueEquiv_residue Λ k (xε.1.hom.base.hom c')).symm.trans
      (((spacePointResidue B hΛ hSpec X hX toK xε.1).residue_comm c').trans hres')
  refine ⟨⟨pushforwardAutomorphismHom hp.cofibered s j hj a.val, by
    have htop := infinitesimalAutomorphisms_spaceDeformation_eq_top B hΛ hSpec X hX toK
      hp.cofibered g e hpair i hi
    exact (SetLike.ext_iff.mp htop _).mpr (Subgroup.mem_top _)⟩, rfl, ?_⟩
  rw [spaceInfinitesimalAutomorphismGroupMulEquivDerivations_apply,
    spaceInfinitesimalAutomorphismGroupMulEquivDerivations_apply]
  change differentialsHomAddEquiv B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK)
      (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
      (spaceLiftHomAddEquiv B hΛ hSpec X hX toK hpair i
        (spaceAutToHom B hΛ hSpec X hX toK hpair i
          (pushforwardAutomorphism hp.cofibered s j hj a.val))) = _
  rw [spaceAutToHom_pushforwardAutomorphism B hΛ hSpec X hX toK hpair i hp.cofibered s j hj hj0
    c' hσ, spaceLiftHomAddEquiv_comp_familySpecialConormalSmul, hc]
  exact differentialsHomAddEquiv_comp_globalSmul B hΛ hSpec X hX toK _ c

section Linear

-- Lean 4.35: the search for `AddCommMonoid (Additive Inf)` through `CommMonoid Inf` times out
-- before reaching the `letI` structure below.
attribute [-instance] Additive.addCommMonoid Additive.addCommGroup

variable (hp : IsPredeformationCategory (spaceDeformationProjection B hΛ hSpec X hX toK))
  (hi : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift g i)

/-- The first identification of the first display, `Inf(𝓓_X) ≅ Der_k(𝒪_X, 𝒪_X)`, as an additive
equivalence out of `Inf(𝓓_X)` written additively. -/
abbrev spaceInfinitesimalAutomorphismAddEquivDerivations :
    Additive (infinitesimalAutomorphismGroup hp g e hpair i hi) ≃+
      SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK) :=
  MulEquiv.toAdditiveLeft
    (spaceInfinitesimalAutomorphismGroupMulEquivDerivations B hΛ hSpec X hX toK hpair i hp hi)

/-- `Inf(𝓓_X)` is commutative ([Stacks Project, Tag 06JV]): it is isomorphic to the additive group
of derivations. -/
@[instance_reducible]
def spaceInfinitesimalAutomorphismAddCommGroup :
    AddCommGroup (Additive (infinitesimalAutomorphismGroup hp g e hpair i hi)) :=
  { (inferInstance : AddGroup (Additive (infinitesimalAutomorphismGroup hp g e hpair i hi))) with
    add_comm := fun a b =>
      (spaceInfinitesimalAutomorphismAddEquivDerivations B hΛ hSpec X hX toK hpair i hp
        hi).injective (by rw [AddEquiv.map_add, AddEquiv.map_add, add_comm]) }

/-- **The `k`-vector-space structure on `Inf(𝓓_X)`** ([Stacks Project, Tag 06JV]): addition is
composition, and by `Deformation.Examples.spaceInfinitesimalAutomorphismModule_smul_eq` a scalar
`c` acts by pushing an infinitesimal automorphism forward along `ε ↦ c ε`.  It is constructed
along the first identification of the first display, which by
`Deformation.Examples.spaceInfinitesimalAutomorphismGroupMulEquivDerivations_pushforward` turns
that pushforward into multiplication by `c`. -/
@[instance_reducible]
def spaceInfinitesimalAutomorphismModule :
    letI := spaceInfinitesimalAutomorphismAddCommGroup B hΛ hSpec X hX toK hpair i hp hi
    Module k (Additive (infinitesimalAutomorphismGroup hp g e hpair i hi)) :=
  letI := spaceInfinitesimalAutomorphismAddCommGroup B hΛ hSpec X hX toK hpair i hp hi
  letI : Module k (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
    derivationModuleOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
      (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
      (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
  letI : SMul k (Additive (infinitesimalAutomorphismGroup hp g e hpair i hi)) :=
    ⟨fun c a => (spaceInfinitesimalAutomorphismAddEquivDerivations B hΛ hSpec X hX toK hpair i
      hp hi).symm (c • spaceInfinitesimalAutomorphismAddEquivDerivations B hΛ hSpec X hX toK
        hpair i hp hi a)⟩
  Function.Injective.module k
    (spaceInfinitesimalAutomorphismAddEquivDerivations B hΛ hSpec X hX toK hpair i hp
      hi).toAddMonoidHom
    (spaceInfinitesimalAutomorphismAddEquivDerivations B hΛ hSpec X hX toK hpair i hp hi).injective
    (fun c a => AddEquiv.apply_symm_apply
      (spaceInfinitesimalAutomorphismAddEquivDerivations B hΛ hSpec X hX toK hpair i hp hi)
      (c • spaceInfinitesimalAutomorphismAddEquivDerivations B hΛ hSpec X hX toK hpair i hp hi a))

/-- **`Inf(𝓓_X) ≅ Der_k(𝒪_X, 𝒪_X)`, `k`-linearly**: the first identification of the first
display of [Stacks Project, Tag 0E41] is `k`-linear for the vector-space structure of
[Stacks Project, Tag 06JV] on `Inf(𝓓_X)` and the action of `k` on derivations through the
structure morphism `X ⟶ Spec k`. -/
def spaceInfinitesimalAutomorphismLinearEquivDerivations :
    letI := spaceInfinitesimalAutomorphismAddCommGroup B hΛ hSpec X hX toK hpair i hp hi
    letI := spaceInfinitesimalAutomorphismModule B hΛ hSpec X hX toK hpair i hp hi
    letI : Module k (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
      derivationModuleOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
        (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
        (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
    Additive (infinitesimalAutomorphismGroup hp g e hpair i hi) ≃ₗ[k]
      SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK) :=
  letI := spaceInfinitesimalAutomorphismAddCommGroup B hΛ hSpec X hX toK hpair i hp hi
  letI := spaceInfinitesimalAutomorphismModule B hΛ hSpec X hX toK hpair i hp hi
  letI : Module k (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
    derivationModuleOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
      (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
      (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
  (spaceInfinitesimalAutomorphismAddEquivDerivations B hΛ hSpec X hX toK hpair i hp
    hi).toLinearEquiv fun _ _ => AddEquiv.apply_symm_apply _ _

/-- The `k`-linear identification is the first identification of the first display. -/
theorem spaceInfinitesimalAutomorphismLinearEquivDerivations_apply
    (a : infinitesimalAutomorphismGroup hp g e hpair i hi) :
    letI := spaceInfinitesimalAutomorphismAddCommGroup B hΛ hSpec X hX toK hpair i hp hi
    letI := spaceInfinitesimalAutomorphismModule B hΛ hSpec X hX toK hpair i hp hi
    letI : Module k (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
      derivationModuleOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
        (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
        (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
    DFunLike.coe
      (F := Additive (infinitesimalAutomorphismGroup hp g e hpair i hi) ≃ₗ[k]
        SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK))
      (spaceInfinitesimalAutomorphismLinearEquivDerivations B hΛ hSpec X hX toK hpair i hp hi)
        (Additive.ofMul a) =
      Multiplicative.toAdd
        (spaceInfinitesimalAutomorphismGroupMulEquivDerivations B hΛ hSpec X hX toK hpair i hp
          hi a) :=
  rfl

/-- **The scalar action on `Inf(𝓓_X)` is pushforward along `ε ↦ c ε`** ([Stacks Project,
Tag 06JV]): for an endomorphism `s` of `Aε` which is `ε ↦ c ε` in a dual-number coordinate and an
arrow `j : xε ⟶ xε` over `s` fixing `i`, `c • a` is the pushforward of `a` along `j`. -/
theorem spaceInfinitesimalAutomorphismModule_smul_eq (c : k) (s : Aε ⟶ Aε)
    (hs : ∃ φ : Aε ≃ₐ[Λ] DualNumber k,
      (∀ t : Aε, (φ t).1 = Aε.residueEquiv (IsLocalRing.residue Aε t)) ∧
      (∀ t : k, φ (s.hom (φ.symm (TrivSqZeroExt.inl t))) = TrivSqZeroExt.inl t) ∧
      φ (s.hom (φ.symm DualNumber.eps)) = c • DualNumber.eps)
    (j : xε.1 ⟶ xε.1) (hj : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift s j)
    (hj0 : i ≫ j = i) (a : infinitesimalAutomorphismGroup hp g e hpair i hi) :
    letI := spaceInfinitesimalAutomorphismAddCommGroup B hΛ hSpec X hX toK hpair i hp hi
    letI := spaceInfinitesimalAutomorphismModule B hΛ hSpec X hX toK hpair i hp hi
    ∃ b : infinitesimalAutomorphismGroup hp g e hpair i hi,
      b.val = pushforwardAutomorphismHom hp.cofibered s j hj a.val ∧
        c • Additive.ofMul a = Additive.ofMul b := by
  obtain ⟨b, hb, hΦ⟩ := spaceInfinitesimalAutomorphismGroupMulEquivDerivations_pushforward B hΛ
    hSpec X hX toK hpair i hp hi c s hs j hj hj0 a
  exact ⟨b, hb, (spaceInfinitesimalAutomorphismAddEquivDerivations B hΛ hSpec X hX toK hpair i hp
    hi).injective ((AddEquiv.apply_symm_apply _ _).trans hΦ.symm)⟩

/-- **The first display of [Stacks Project, Tag 0E41], `k`-linearly: `Inf(𝓓_X) = Der_k(𝒪_X, 𝒪_X)`
as `k`-vector spaces.**  In Example 0E3Z, let `X` be an algebraic space over the field `k`.  At
every point `x₀` of the deformation category of `X` over `k`, every pushforward `i : x₀ ⟶ xε` of
it along a dual-number pair `k → k[ε] → k` and every predeformation-category structure, the
infinitesimal automorphism group `Inf(𝓓_X)` of [Stacks Project, Tag 06JS] carries the
`k`-vector-space structure of [Stacks Project, Tag 06JV]:

* addition is composition of infinitesimal automorphisms;
* a scalar `c` acts by pushforward along `ε ↦ c ε`: for every endomorphism `s` of the base which is
  `ε ↦ c ε` in a dual-number coordinate and every arrow `j : xε ⟶ xε` over `s` fixing `i`, `c • a`
  is the pushforward of `a` along `j`;

and the first identification of the first display,
`Deformation.Examples.spaceInfinitesimalAutomorphismGroupMulEquivDerivations`, is a `k`-linear
isomorphism onto `Der_k(𝒪_X, 𝒪_X)`, `k` acting on derivations through the structure morphism
`X ⟶ Spec k`.  The remaining identifications of the display,
`Ext⁰_{𝒪_X}(NL_{X/k}, 𝒪_X) = Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X) = Der_k(𝒪_X, 𝒪_X)`, are `k`-linear by
`Deformation.Examples.spaceInfinitesimalAutomorphismGroupChain`. -/
@[stacks 0E41 "first display, k-linear form: for an algebraic space X over the field k, \
Inf(Def_X) with the vector space structure of 06JV (addition is composition; c acts by pushforward \
along eps -> c eps, along every arrow over such a rescaling fixing the pushforward x0 -> x_eps) is \
k-linearly isomorphic to Der_k(O_X, O_X), k acting through the structure morphism X -> Spec k, by \
the first identification of the first display, at every point x0 over k and every pushforward \
along a dual-number pair", sga "3 II 3.14" "special case"]
theorem spaceInfinitesimalAutomorphismGroup_linearEquivDerivations :
    letI : Module k (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
      derivationModuleOfRingHom B (Spec (.of Λ)) hΛ (X := spaceOf B hΛ X hX)
        (spaceResidueFieldRingHom B hΛ hSpec X hX toK)
        (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))
    ∃ A : AddCommGroup (Additive (infinitesimalAutomorphismGroup hp g e hpair i hi)),
      letI := A
      ∃ M : Module k (Additive (infinitesimalAutomorphismGroup hp g e hpair i hi)),
        letI := M
        (∀ a b : infinitesimalAutomorphismGroup hp g e hpair i hi,
          Additive.ofMul a + Additive.ofMul b = Additive.ofMul (a * b)) ∧
        (∀ (c : k) (s : Aε ⟶ Aε),
          (∃ φ : Aε ≃ₐ[Λ] DualNumber k,
            (∀ t : Aε, (φ t).1 = Aε.residueEquiv (IsLocalRing.residue Aε t)) ∧
            (∀ t : k, φ (s.hom (φ.symm (TrivSqZeroExt.inl t))) = TrivSqZeroExt.inl t) ∧
            φ (s.hom (φ.symm DualNumber.eps)) = c • DualNumber.eps) →
          ∀ (j : xε.1 ⟶ xε.1) (hj : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift s j),
            i ≫ j = i → ∀ a : infinitesimalAutomorphismGroup hp g e hpair i hi,
              ∃ b : infinitesimalAutomorphismGroup hp g e hpair i hi,
                b.val = pushforwardAutomorphismHom hp.cofibered s j hj a.val ∧
                  c • Additive.ofMul a = Additive.ofMul b) ∧
        ∃ E : Additive (infinitesimalAutomorphismGroup hp g e hpair i hi) ≃ₗ[k]
            SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK),
          ∀ a : infinitesimalAutomorphismGroup hp g e hpair i hi,
            DFunLike.coe
              (F := Additive (infinitesimalAutomorphismGroup hp g e hpair i hi) ≃ₗ[k]
                SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) E
              (Additive.ofMul a) =
            Multiplicative.toAdd
              (spaceInfinitesimalAutomorphismGroupMulEquivDerivations B hΛ hSpec X hX toK hpair i
                hp hi a) :=
  ⟨spaceInfinitesimalAutomorphismAddCommGroup B hΛ hSpec X hX toK hpair i hp hi,
    spaceInfinitesimalAutomorphismModule B hΛ hSpec X hX toK hpair i hp hi,
    fun _ _ => rfl,
    fun c s hs j hj hj0 a => spaceInfinitesimalAutomorphismModule_smul_eq B hΛ hSpec X hX toK
      hpair i hp hi c s hs j hj hj0 a,
    spaceInfinitesimalAutomorphismLinearEquivDerivations B hΛ hSpec X hX toK hpair i hp hi,
    spaceInfinitesimalAutomorphismLinearEquivDerivations_apply B hΛ hSpec X hX toK hpair i hp hi⟩

end Linear

end Deformation.Examples

end
