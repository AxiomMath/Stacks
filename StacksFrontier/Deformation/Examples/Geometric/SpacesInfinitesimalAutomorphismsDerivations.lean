module

public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsTransport
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsConormalSpecialFibre
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsDualNumberIdeal
public import StacksFrontier.Deformation.Examples.Geometric.SpacesInfinitesimalAutomorphismsExtZero
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMapEtale
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackId
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The infinitesimal automorphisms of an algebraic space are its derivations

Let `k` be a field and `X` an algebraic space over `k`, with deformation category `𝓓_X`
([Stacks Project, Tag 0E3Z]).  This file proves that the infinitesimal automorphism group
`Inf(𝓓_X)` of [Stacks Project, Tag 06JS], at any point `x₀` over `k` and any pushforward
`x₀ ⟶ xε` to an object of `𝒞_Λ` with a dual-number coordinate, is isomorphic **as a group** to
the additive group of `k`-derivations of `𝒪_X`,

`Inf(𝓓_X) ≅ Der_k(𝒪_X, 𝒪_X)`.

The automorphisms are the self-maps of the total space `X'` of `xε` over `Spec Aε` fixing `X`
(`Deformation.Examples.spaceInfinitesimalAutomorphismGroupMulEquivAut`), and composing with the
retraction `π : X' ⟶ X` identifies them, as a group, with
`Hom_{𝒪_G}(π|_G^*Ω_{X/k}, 𝒞_{G/X'})` for the special fibre `G ⊆ X'`
(`Deformation.Examples.spaceAutMulEquivHom`).  The special fibre is `X` (`π|_G` is an
isomorphism, `Deformation.Examples.spaceSpecialIso`), the conormal module `𝒞_{G/X'}` is free of
rank one because `X'` is flat over the dual numbers
(`Deformation.Examples.spaceSpecialConormalIsoUnit`), and so this group is
`Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`, which is `Der_k(𝒪_X, 𝒪_X)` by the universal property of
[Stacks Project, Tag 04CT].

## Main definitions

* `Deformation.Examples.spaceLiftHomAddEquiv`: `Hom(π|_G^*Ω, 𝒞_{G/X'}) ≃+ Hom(Ω_{X/k}, 𝒪_X)`.
* `Deformation.Examples.spaceInfinitesimalAutomorphismGroupMulEquivDifferentialsHom` and
  `Deformation.Examples.spaceInfinitesimalAutomorphismGroupMulEquivDerivations`.

## References

* [Stacks Project, Tag 0E41](https://stacks.math.columbia.edu/tag/0E41)
* [Stacks Project, Tag 06JS](https://stacks.math.columbia.edu/tag/06JS)
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.Space

universe u


namespace Deformation.Examples

variable {Λ : Type u} {k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]
variable (B : BigFppfSite.{u}) (hΛ : B.Contains (Spec (.of Λ)))
variable (hSpec : ∀ A : ArtinianLocalAlgCat.{u, u, u} Λ k, B.Contains (Spec (.of A)))

/-! ### The dual-number element of the base -/

/-- An object of `𝒞_Λ` with a dual-number coordinate has an element `ε` generating the kernel
of every morphism to the residue field and equal to its own annihilator. -/
theorem exists_epsilon_of_isCanonicalDualNumberPair
    {A₀ Aε : ArtinianLocalAlgCat.{u, u, u} Λ k}
    {g : A₀ ⟶ Aε} {e : Aε ⟶ A₀} (hpair : IsCanonicalDualNumberPair g e)
    (f : Aε ⟶ residueFieldBase Λ k) :
    ∃ εA : Aε, RingHom.ker f.hom.toRingHom = Ideal.span {εA} ∧
      ∀ a : Aε, εA * a = 0 ↔ a ∈ Ideal.span {εA} := by
  obtain ⟨-, iε, -, -, -⟩ := hpair
  refine ⟨iε.symm DualNumber.eps, ?_, mul_eq_zero_iff_mem_span_of_algEquiv_dualNumber iε⟩
  rw [ker_eq_maximalIdeal_of_hom_residueFieldBase]
  exact IsLocalRing.maximalIdeal_eq_span_of_algEquiv_dualNumber iε

/-! ### Inverse image along an isomorphism -/

/-- The inverse image of modules along an isomorphism of algebraic spaces is an equivalence. -/
def modulePullbackEquivalenceOfIso {X Y : AlgebraicSpaces B (Spec (.of Λ)) hΛ} (e : X ≅ Y) :
    Space.Modules.{u, u} B (Spec (.of Λ)) hΛ Y.1 Y.2 ≌
      Space.Modules.{u, u} B (Spec (.of Λ)) hΛ X.1 X.2 :=
  CategoryTheory.Equivalence.mk (modulePullback B (Spec (.of Λ)) hΛ e.hom)
    (modulePullback B (Spec (.of Λ)) hΛ e.inv)
    ((modulePullbackIdIso B (Spec (.of Λ)) hΛ Y).symm ≪≫
      eqToIso (congrArg (modulePullback B (Spec (.of Λ)) hΛ) e.inv_hom_id.symm) ≪≫
      (modulePullbackCompIso B (Spec (.of Λ)) hΛ e.inv e.hom).symm)
    (modulePullbackCompIso B (Spec (.of Λ)) hΛ e.hom e.inv ≪≫
      eqToIso (congrArg (modulePullback B (Spec (.of Λ)) hΛ) e.hom_inv_id) ≪≫
      modulePullbackIdIso B (Spec (.of Λ)) hΛ X)

/-- Hom groups out of and into inverse images along an isomorphism, additively. -/
def modulePullbackHomAddEquivOfIso {X Y : AlgebraicSpaces B (Spec (.of Λ)) hΛ} (e : X ≅ Y)
    (M N : Space.Modules.{u, u} B (Spec (.of Λ)) hΛ Y.1 Y.2) :
    (M ⟶ N) ≃+ ((modulePullback B (Spec (.of Λ)) hΛ e.hom).obj M ⟶
      (modulePullback B (Spec (.of Λ)) hΛ e.hom).obj N) :=
  haveI := modulePullback_additive (B := B) (S := Spec (.of Λ)) (hS := hΛ) e.hom
  { (modulePullbackEquivalenceOfIso B hΛ e).fullyFaithfulFunctor.homEquiv with
    map_add' := fun f g => by
      change (modulePullbackEquivalenceOfIso B hΛ e).functor.map (f + g) = _
      exact (modulePullback B (Spec (.of Λ)) hΛ e.hom).map_add }

/-- Conjugating hom groups by isomorphisms, additively. -/
def homAddEquivOfIso {C : Type*} [Category C] [Preadditive C] {M M' N N' : C} (a : M ≅ M')
    (b : N ≅ N') : (M ⟶ N) ≃+ (M' ⟶ N') :=
  { a.homCongr b with
    map_add' := fun f g => by
      change a.homCongr b (f + g) = a.homCongr b f + a.homCongr b g
      rw [Iso.homCongr_apply, Iso.homCongr_apply, Iso.homCongr_apply, Preadditive.add_comp,
        Preadditive.comp_add] }

/-! ### The group of linear maps is `Hom(Ω_{X/k}, 𝒪_X)` -/

/-- The structure sheaf `𝒪_Y` of an algebraic space, as an `𝒪_Y`-module. -/
def spaceStructureModule (Y : AlgebraicSpaces B (Spec (.of Λ)) hΛ) :
    Space.Modules.{u, u} B (Spec (.of Λ)) hΛ Y.1 Y.2 :=
  SheafOfModules.unit (structureRingSheaf B (Spec (.of Λ)) hΛ Y)

/-- **`Der_k(𝒪_X, 𝒪_X)`**: the derivations of `𝒪_Y` over `f⁻¹𝒪_Z` with values in `𝒪_Y`, for a
morphism `f : Y ⟶ Z` of algebraic spaces. -/
def SpaceDerivations {Y Z : AlgebraicSpaces B (Spec (.of Λ)) hΛ} (f : Y ⟶ Z) : Type _ :=
  PresheafOfModulesOfCommRing.Derivation' (spaceStructureModule B hΛ Y).val
    (structureSharpInverseImage B (Spec (.of Λ)) hΛ f).hom

/-- The derivations of `𝒪_Y` over `f⁻¹𝒪_Z` form an additive commutative group. -/
instance {Y Z : AlgebraicSpaces B (Spec (.of Λ)) hΛ} (f : Y ⟶ Z) :
    AddCommGroup (SpaceDerivations B hΛ f) :=
  derivationAddCommGroupModules B _ hΛ f _

section Lifts

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

include hpair in
/-- The base of `xε` has an element `ε` generating the kernel of the residue map and equal to
its own annihilator. -/
theorem exists_epsilon_spacePoint :
    ∃ εA : xε.1.left.base, RingHom.ker xε.1.hom.base.hom.toRingHom = Ideal.span {εA} ∧
      ∀ a : xε.1.left.base, εA * a = 0 ↔ a ∈ Ideal.span {εA} := by
  have hQ : ∀ (A : ArtinianLocalAlgCat.{u, u, u} Λ k), A = Aε →
      ∀ f : A ⟶ residueFieldBase Λ k, ∃ εA : A, RingHom.ker f.hom.toRingHom = Ideal.span {εA} ∧
        ∀ a : A, εA * a = 0 ↔ a ∈ Ideal.span {εA} := by
    rintro A rfl f
    exact exists_epsilon_of_isCanonicalDualNumberPair hpair f
  exact hQ _ xε.2 _

/-- The equality `π|_G = e₀ ≫ (X ⊂ X)`. -/
theorem spaceSpecialIso_hom_eq :
    (spaceSpecialIso B hΛ hSpec X hX toK i).hom =
      spaceRetractionSpecial B hΛ hSpec X hX toK i ≫
        subspaceInclusion B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)) :=
  spaceRetractionSpecial_spec B hΛ hSpec X hX toK i

/-- The comparison `ι^*Ω_{X/k} ⟶ Ω_{⊤/k}` along the inclusion `ι` of the top closed subspace of
`X`, which is an isomorphism ([Stacks Project, Tag 04CU]). -/
def topDifferentialsMap :
    (modulePullback B (Spec (.of Λ)) hΛ (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)))).obj
        (sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK)) ⟶
      sheafOfDifferentials B (Spec (.of Λ)) hΛ
        (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
          (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)) ≫
          spaceStructureMap B hΛ hSpec X hX toK) :=
  sheafOfDifferentialsMap B (Spec (.of Λ)) hΛ _ _ _ (𝟙 _) (Category.comp_id _).symm

/-- The comparison map `ι^*Ω_{X/k} ⟶ Ω_{⊤/k}` is an isomorphism. -/
theorem isIso_topDifferentialsMap : IsIso (topDifferentialsMap B hΛ hSpec X hX toK) :=
  isIso_sheafOfDifferentialsMap_of_isEtale B (Spec (.of Λ)) hΛ _ _ _ (𝟙 _)
    (@isEtale_of_isIso B (Spec (.of Λ)) hΛ _ _ (Subfunctor.ι (⊤ : Subfunctor X))
      (show IsIso (Subfunctor.ι (⊤ : Subfunctor X)) from inferInstance))
    (isEtale_of_isIso B (Spec (.of Λ)) hΛ _)
    (Category.comp_id _).symm

/-- **The group acting on the lifts is `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`**: transport along the
isomorphism `π|_G : G ≅ X` of the special fibre, the identification `ι^*Ω_{X/k} ≅ Ω_{⊤/k}` along
the inclusion of the top closed subspace, and `𝒞_{G/X'} ≅ 𝒪_G`. -/
def spaceLiftHomAddEquiv :
    SpaceLiftHom B hΛ hSpec X hX toK i ≃+
      (sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK) ⟶
        spaceStructureModule B hΛ (spaceOf B hΛ X hX)) :=
  haveI := isIso_topDifferentialsMap B hΛ hSpec X hX toK
  let α := spaceSpecialIso B hΛ hSpec X hX toK i
  let εA := (exists_epsilon_spacePoint B hΛ hSpec X hX toK hpair (xε := xε)).choose
  let hε := (exists_epsilon_spacePoint B hΛ hSpec X hX toK hpair (xε := xε)).choose_spec
  let src : (modulePullback B (Spec (.of Λ)) hΛ α.hom).obj
      (sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK)) ≅
      (modulePullback B (Spec (.of Λ)) hΛ (spaceRetractionSpecial B hΛ hSpec X hX toK i)).obj
        (sheafOfDifferentials B (Spec (.of Λ)) hΛ
          (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
            (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)) ≫
            spaceStructureMap B hΛ hSpec X hX toK)) :=
    eqToIso (congrArg (fun h => (modulePullback B (Spec (.of Λ)) hΛ h).obj
      (sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK)))
      (spaceSpecialIso_hom_eq B hΛ hSpec X hX toK i)) ≪≫
    ((modulePullbackCompIso B (Spec (.of Λ)) hΛ (spaceRetractionSpecial B hΛ hSpec X hX toK i)
      (subspaceInclusion B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)
        (topSubspace B (Spec (.of Λ)) hΛ (spaceOf B hΛ X hX)))).app
      (sheafOfDifferentials B (Spec (.of Λ)) hΛ (spaceStructureMap B hΛ hSpec X hX toK))).symm ≪≫
    (modulePullback B (Spec (.of Λ)) hΛ (spaceRetractionSpecial B hΛ hSpec X hX toK i)).mapIso
      (asIso (topDifferentialsMap B hΛ hSpec X hX toK))
  let tgt : conormalModule B (Spec (.of Λ)) hΛ (spaceTotalSpace B hΛ hSpec xε.1.left)
      (spacePointSpecial B hΛ hSpec X hX toK xε.1) ≅
      (modulePullback B (Spec (.of Λ)) hΛ α.hom).obj
        (spaceStructureModule B hΛ (spaceOf B hΛ X hX)) :=
    spaceSpecialConormalIsoUnit B hΛ hSpec xε.1.left xε.1.hom.base εA hε.1 hε.2
      (isFirstOrderThickening_spacePointSpecial B hΛ hSpec X hX toK hpair) ≪≫
    (modulePullbackUnitIso B (Spec (.of Λ)) hΛ α.hom).symm
  (homAddEquivOfIso src.symm tgt).trans
    (modulePullbackHomAddEquivOfIso B hΛ α _ _).symm

/-- **`Inf(𝓓_X)` is `Hom_{𝒪_X}(Ω_{X/k}, 𝒪_X)`, as a group**: composition of infinitesimal
automorphisms is addition of maps. -/
def spaceInfinitesimalAutomorphismGroupMulEquivDifferentialsHom
    (hp : IsPredeformationCategory (spaceDeformationProjection B hΛ hSpec X hX toK))
    (hi : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift g i) :
    infinitesimalAutomorphismGroup hp g e hpair i hi ≃*
      Multiplicative (sheafOfDifferentials B (Spec (.of Λ)) hΛ
        (spaceStructureMap B hΛ hSpec X hX toK) ⟶ spaceStructureModule B hΛ (spaceOf B hΛ X hX)) :=
  (spaceInfinitesimalAutomorphismGroupMulEquivAut B hΛ hSpec X hX toK hp g e hpair i hi).trans
    ((spaceAutMulEquivHom B hΛ hSpec X hX toK hpair i).trans
      (AddEquiv.toMultiplicative (spaceLiftHomAddEquiv B hΛ hSpec X hX toK hpair i)))

/-- **`Inf(𝓓_X)` is the group of `k`-derivations of `𝒪_X`**: for an algebraic space `X` over the
field `k`, the infinitesimal automorphism group of its deformation category, at any point over
`k` and any pushforward of it to an object of `𝒞_Λ` with a dual-number coordinate, is isomorphic
as a group to `Der_k(𝒪_X, 𝒪_X)` under addition. -/
@[sga "1 III 6.1" "partial"]
def spaceInfinitesimalAutomorphismGroupMulEquivDerivations
    (hp : IsPredeformationCategory (spaceDeformationProjection B hΛ hSpec X hX toK))
    (hi : (spaceDeformationProjection B hΛ hSpec X hX toK).IsHomLift g i) :
    infinitesimalAutomorphismGroup hp g e hpair i hi ≃*
      Multiplicative (SpaceDerivations B hΛ (spaceStructureMap B hΛ hSpec X hX toK)) :=
  (spaceInfinitesimalAutomorphismGroupMulEquivDifferentialsHom B hΛ hSpec X hX toK hpair i hp
      hi).trans
    (AddEquiv.toMultiplicative (differentialsHomAddEquiv B (Spec (.of Λ)) hΛ
      (spaceStructureMap B hΛ hSpec X hX toK) (spaceStructureModule B hΛ (spaceOf B hΛ X hX))))

end Lifts

end Deformation.Examples

end
