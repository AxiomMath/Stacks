module

public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentStalkJacobiZariski
public import StacksFrontier.RingTheory.NaiveCotangent.SelfPresentationCotangentSpace

/-!
# The canonical map `g : NL_{C/A} ⟶ NL_{C/B}` is invertible in degree `0`

Let `A ⟶ B ⟶ C` be morphisms of sheaves of commutative rings on a topological space.  The
degree `0` term of the naive cotangent complex of `D` over `D'` is built from the *canonical*
polynomial presentation `D'[D] ⟶ D` of Stacks 07BL, whose variables are indexed by `D` alone;
so the degree `0` terms of `NL_{C/A}` and of `NL_{C/B}` have the same variables, and the
canonical map `g` identifies them.

This file proves exactly that: `g` is an isomorphism in degree `0`.  Invertibility of a morphism
of sheaves of modules is a stalkwise condition, and at a stalk the degree `0` component of `g`
is the comparison `Algebra.Extension.CotangentSpace.map` of the canonical presentations of the
stalk rings, which carries the canonical basis `1 ⊗ D X_t` to the canonical basis
(`NaiveCotangent.bijective_cotangentSpaceMap_self`).

## Main results

* `Stacks.SheafOfModules.isIso_spaceRelativeNaiveCotangentComplexMap_zero`: **the canonical map
  `g : NL_{C/A} ⟶ NL_{C/B}` of Stacks 0E1Y is an isomorphism in degree `0`**, for sheaves of
  rings on a topological space.  The canonical map `NL_{X/Z} ⟶ NL_{X/Y}` of Stacks 0E1Z is this
  map for the tower `(g ∘ f)⁻¹O_Z ⟶ f⁻¹O_Y ⟶ O_X`, so it is covered as it stands.
* `Stacks.NaiveCotangentStalkJacobiZariski.bijective_stalk_spaceRelativeMap_zero`: the stalkwise
  statement it is proved from.
* `Stacks.NaiveCotangentStalkJacobiZariski.toRingHom_stalkTowerHomRel_X`: the morphism of
  canonical presentations of the stalk rings attached to `g` fixes the variables.

## Implementation notes

The three lemmas before the main result are bookkeeping around the `Algebra Cₓ Cₓ` structure
read off the stalk of `𝟙 C`, which is not the identity structure definitionally — the stalk
functor is a colimit, so it does not preserve identities on the nose.  The morphism of
presentations is stated over the identity structure, as
`Stacks.NaiveCotangentTowerStalk.stalkTowerHomRel`, so the underlying ring map has to be read
through the transport `Stacks.NaiveCotangentTowerStalk.homCongrEq`; the transport does not touch
the underlying ring homomorphism, which is
`Stacks.NaiveCotangentAffineComparison.squareRingHom` and carries `X_t` to `X_{𝟙 t}`.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y), the two canonical maps.
* [Stacks Project, Tag 07BL](https://stacks.math.columbia.edu/tag/07BL), the canonical
  presentation.
* [Stacks Project, Tag 0D09](https://stacks.math.columbia.edu/tag/0D09), the stalk of the naive
  cotangent complex.
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG), invertibility is
  stalkwise.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.SheafOfModules
open Stacks.NaiveCotangentAffineStalkLegs
open Stacks.NaiveCotangentTowerStalk
open Stacks.RelativeDifferentialStalk (algebraStalk)
open AlgebraicGeometry.SheafOfModules (stalkFunctor)
open Stacks.Sites.Conormal (stalkIsScalarTowerSquareTarget)

universe u

noncomputable section

namespace Stacks.NaiveCotangentStalkJacobiZariski

/-- A map conjugate to a bijection by two bijections is a bijection. -/
theorem bijective_of_bijective_conj {α β γ δ : Type*} (e₁ : α ≃ γ) (e₂ : β ≃ δ) (f : α → β)
    (φ : γ → δ) (hcomm : ∀ x, e₂ (f x) = φ (e₁ x)) (hφ : Function.Bijective φ) :
    Function.Bijective f := by
  have hf : f = fun x => e₂.symm (φ (e₁ x)) :=
    funext fun x => by rw [← hcomm x, Equiv.symm_apply_apply]
  rw [hf]
  exact e₂.symm.bijective.comp (hφ.comp e₁.bijective)

/-- Transporting a morphism of extensions along equalities of the two comparison algebra
structures does not change its underlying ring homomorphism. -/
theorem toRingHom_homCongrEq {R S R' S' : Type u} [CommRing R] [CommRing S] [CommRing R']
    [CommRing S'] [Algebra R S] [Algebra R' S'] {P : Algebra.Extension R S}
    {P' : Algebra.Extension R' S'} (i₁ i₂ : Algebra R R') (j₁ j₂ : Algebra S S') (hi : i₁ = i₂)
    (hj : j₁ = j₂) (h : @Algebra.Extension.Hom R S _ _ _ P R' S' _ _ _ P' i₁ j₁) :
    @Algebra.Extension.Hom.toRingHom R S _ _ _ P R' S' _ _ _ P' i₂ j₂
          (homCongrEq i₁ i₂ j₁ j₂ hi hj h) =
      @Algebra.Extension.Hom.toRingHom R S _ _ _ P R' S' _ _ _ P' i₁ j₁ h := by
  subst hi
  subst hj
  rfl

attribute [local instance 1]
  Sheaf.hasWeakSheafifyCommRingCat
  Sheaf.hasSheafifyAddCommGrpCat
  Sheaf.wEqualsLocallyBijectiveAddCommGrpCat

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C) (z : T)

/-- **The morphism `Aₓ[Cₓ] ⟶ Bₓ[Cₓ]` of canonical presentations of the stalks attached to the
canonical map `g` of Stacks 0E1Y fixes the variables.** -/
theorem toRingHom_stalkTowerHomRel_X (t : ToType (TopCat.Presheaf.stalk C.obj z)) :
    letI := algebraStalk (a ≫ b).hom z
    letI := algebraStalk a.hom z
    letI := algebraStalk b.hom z
    (stalkTowerHomRel A B B C a b a b z rfl).toRingHom (MvPolynomial.X t) =
      MvPolynomial.X t := by
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk a.hom z
  let := algebraStalk b.hom z
  have h0 : stalkTowerHomRel A B B C a b a b z rfl =
      homCongrEq (algebraStalk a.hom z) (algebraStalk a.hom z)
        (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 C)) z) (Algebra.id _) rfl
        (algebraStalk_id C z)
        (generatorsSelfStalkHomOfSquare A B C C (a ≫ b) b a (𝟙 C) z
          (comp_id_eq_of_tower A B B C a b a b rfl)) := rfl
  have hid : @algebraMap (ToType (TopCat.Presheaf.stalk C.obj z))
      (ToType (TopCat.Presheaf.stalk C.obj z)) _ _
      (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 C)) z) t = t := by
    rw [algebraStalk_id C z]
    rfl
  rw [h0, toRingHom_homCongrEq, generatorsSelfStalkHomOfSquare_toRingHom]
  exact (@squareRingHom_X (ToType (TopCat.Presheaf.stalk A.obj z))
    (ToType (TopCat.Presheaf.stalk B.obj z)) (ToType (TopCat.Presheaf.stalk C.obj z))
    (ToType (TopCat.Presheaf.stalk C.obj z)) _ _ _ _ (algebraStalk a.hom z)
    (algebraStalk (CategoryTheory.InducedCategory.Hom.hom (𝟙 C)) z) t).trans
      (congrArg MvPolynomial.X hid)

/-- **The stalk of the degree `0` component of the canonical map `g` of Stacks 0E1Y is
bijective.**  Read through the two legs of Stacks 0D09 it is
`Algebra.Extension.CotangentSpace.map` of the morphism of canonical presentations of the stalk
rings, which fixes the variables and therefore carries the canonical basis of the cotangent
space to the canonical basis. -/
theorem bijective_stalk_spaceRelativeMap_zero :
    Function.Bijective ((stalkFunctor (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} C) z).map
      ((spaceRelativeNaiveCotangentComplexMap A B C a b).f 0)).hom := by
  let := algebraStalk a.hom z
  let := algebraStalk (a ≫ b).hom z
  let := algebraStalk b.hom z
  let := stalkIsScalarTowerSquareTarget A B C a (a ≫ b) b z rfl
  refine bijective_of_bijective_conj (stalkLegZeroLinear A C (a ≫ b) z).toEquiv
    (stalkLegZeroLinear B C b z).toEquiv _
    (NaiveCotangent.nlExtensionOverMap (stalkTowerHomRel A B B C a b a b z rfl)).f₀
    (stalkLegZeroLinear_spaceRelativeMap A B C a b z) ?_
  exact NaiveCotangent.bijective_cotangentSpaceMap_self
    (stalkTowerHomRel A B B C a b a b z rfl) (toRingHom_stalkTowerHomRel_X A B C a b z)

end Stacks.NaiveCotangentStalkJacobiZariski

namespace Stacks.SheafOfModules

variable {T : TopCat.{u}}
  (A B C : CategoryTheory.Sheaf (Opens.grothendieckTopology T) CommRingCat.{u})
  (a : A ⟶ B) (b : B ⟶ C)

/-- **Stacks 0E1Y: the canonical map `g : NL_{C/A} ⟶ NL_{C/B}` is an isomorphism in degree
`0`.**  Both degree `0` terms are built from the canonical polynomial presentation of Stacks
07BL, whose variables are indexed by `C` in both cases, and `g` fixes those variables.

Invertibility of a morphism of sheaves of modules is stalkwise
(`AlgebraicGeometry.SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map`), and at a stalk
this is
`Stacks.NaiveCotangentStalkJacobiZariski.bijective_stalk_spaceRelativeMap_zero`. -/
instance isIso_spaceRelativeNaiveCotangentComplexMap_zero :
    IsIso ((spaceRelativeNaiveCotangentComplexMap A B C a b).f 0) := by
  rw [AlgebraicGeometry.SheafOfModules.isIso_iff_forall_isIso_stalkFunctor_map]
  intro z
  rw [ConcreteCategory.isIso_iff_bijective]
  exact Stacks.NaiveCotangentStalkJacobiZariski.bijective_stalk_spaceRelativeMap_zero
    A B C a b z

end Stacks.SheafOfModules

end

end
