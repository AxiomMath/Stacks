module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalencePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposSquare

/-!
# Sheaves of modules along a change of coefficient rings

Fix a site `(C, J)` and a map `α : O ⟶ O'` of sheaves of commutative rings on it, and let
`k : (Sh(J), O') ⟶ (Sh(J), O)` be the morphism of ringed topoi it induces
(`AlgebraicGeometry.RingedToposHom.coefficientMorphism`), whose underlying geometric morphism is
the identity. The direct image of sheaves of modules along `k` is restriction of scalars along
`α`, and so the pullback along `k` is left adjoint to restriction of scalars along `α`.

## Main definitions

* `AlgebraicGeometry.RingedToposHom.coefficientMorphismPushforwardIso`: the direct image of
  sheaves of modules along `k` is restriction of scalars along `α`; the comparison is the
  identity on underlying sheaves of sets.
* `AlgebraicGeometry.RingedToposHom.coefficientMorphismPullbackAdjunction`: the pullback of
  sheaves of modules along `k` is left adjoint to restriction of scalars along `α`.

## Main results

* `AlgebraicGeometry.RingedToposHom.forgetRing_map_coefficientMorphism_fSharp`: on underlying
  sheaves of sets the structure map of `k` is `α`.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPushforward Stacks.Sheaves.ToposPullback
open Stacks.Sheaves.RingedToposModules

namespace AlgebraicGeometry.RingedToposHom

universe w v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget RingCat.{w})]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O O' : Sheaf J CommRingCat.{w}} (α : O ⟶ O')

/-- On underlying sheaves of sets the structure map of a change of coefficient rings is the map
of coefficient sheaves itself. -/
theorem forgetRing_map_coefficientMorphism_fSharp :
    (⟨C, J, O⟩ : RingedTopos.{v, u, w}).forgetRing.map (coefficientMorphism J α).fSharp =
      (sheafCompose J (forget CommRingCat.{w})).map α :=
  (coefficientMorphism_fSharpInverseImageForget J α :)

variable [J.HasSheafCompose (forget AddCommGrpCat.{w})]

/-- The underlying sheaf of sets of the direct image along a change of coefficient rings is the
underlying sheaf of sets of the module. -/
def coefficientMorphismPushforwardSheafIso (M : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf O')) :
    Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)
        ((SheafOfModules.restrictScalars
          ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α)).obj M) ≅
      Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)
        ((pushforwardModules (coefficientMorphism J α)).obj M) :=
  (Iso.refl (𝟭 (Sheaf J (Type w)))).app
    (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O') M)

variable (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O'))

/-- The identification of underlying sheaves of sets is additive. -/
lemma moduleAddHom_comp_coefficientMorphismPushforwardSheafIso_hom :
    Sheaf.moduleAddHom (Stacks.SheafOfModules.Tensor.ringSheaf O)
          ((SheafOfModules.restrictScalars
            ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α)).obj M) ≫
        (coefficientMorphismPushforwardSheafIso J α M).hom =
      prod.map (coefficientMorphismPushforwardSheafIso J α M).hom
          (coefficientMorphismPushforwardSheafIso J α M).hom ≫
        Sheaf.moduleAddHom (Stacks.SheafOfModules.Tensor.ringSheaf O)
          ((pushforwardModules (coefficientMorphism J α)).obj M) :=
  Stacks.CategoryTheory.binaryOp_comp_hom_app (Iso.refl (𝟭 (Sheaf J (Type w)))) _ _
    (moduleAdd_map_aux' J (𝟭 (Sheaf J (Type w))) (Stacks.SheafOfModules.Tensor.ringSheaf O') M)

/-- The inverse identification of underlying sheaves of sets is compatible with the two scalar
multiplications: the direct image restricts its scalars along the structure map of the change of
coefficients, which is `α` on underlying sheaves of sets. -/
lemma moduleSMulHom_comp_coefficientMorphismPushforwardSheafIso_inv :
    Sheaf.moduleSMulHom (Stacks.SheafOfModules.Tensor.ringSheaf O)
          ((pushforwardModules (coefficientMorphism J α)).obj M) ≫
        (coefficientMorphismPushforwardSheafIso J α M).inv =
      prod.map (𝟙 (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)))
          (coefficientMorphismPushforwardSheafIso J α M).inv ≫
        Sheaf.moduleSMulHom (Stacks.SheafOfModules.Tensor.ringSheaf O)
          ((SheafOfModules.restrictScalars
            ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α)).obj M) := by
  refine (moduleSMulHom_comp_iff _).2 fun X r x ↦ ?_
  have h₅ : (ConcreteCategory.hom ((Sheaf.sectionsFunctor J X).map
        ((sheafCompose J (forget RingCat.{w})).map (coefficientMorphism J α).fSharpRing))) r =
      (ConcreteCategory.hom ((Sheaf.sectionsFunctor J X).map
        ((sheafCompose J (forget CommRingCat.{w})).map α))) r :=
    congrArg (fun m ↦ (Sheaf.sectionsFunctor J X).map m r)
      (forgetRing_map_coefficientMorphism_fSharp J α)
  exact (congrArg
      ((Sheaf.sectionsFunctor J X).map (coefficientMorphismPushforwardSheafIso J α M).inv)
      (pushforwardModules_smul (coefficientMorphism J α) M X r x)).trans
    ((Sheaf.sectionsFunctor_map_moduleSMulHom (Stacks.SheafOfModules.Tensor.ringSheaf O') M X _
      x).trans (congrArg (fun a : (Sheaf.sectionsFunctor J X).obj
          (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O')) ↦
        a • (show (Sheaf.sectionsFunctor J X).obj
          (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O') M) from x)) h₅))

/-- The identification of underlying sheaves of sets is compatible with the two scalar
multiplications. -/
lemma moduleSMulHom_comp_coefficientMorphismPushforwardSheafIso_hom :
    Sheaf.moduleSMulHom (Stacks.SheafOfModules.Tensor.ringSheaf O)
          ((SheafOfModules.restrictScalars
            ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α)).obj M) ≫
        (coefficientMorphismPushforwardSheafIso J α M).hom =
      prod.map (𝟙 (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)))
          (coefficientMorphismPushforwardSheafIso J α M).hom ≫
        Sheaf.moduleSMulHom (Stacks.SheafOfModules.Tensor.ringSheaf O)
          ((pushforwardModules (coefficientMorphism J α)).obj M) :=
  moduleSMulHom_inv_comm (coefficientMorphismPushforwardSheafIso J α M).symm
    (moduleSMulHom_comp_coefficientMorphismPushforwardSheafIso_inv J α M)

/-- The direct image of a sheaf of modules along a change of coefficient rings is its restriction
of scalars. -/
def coefficientMorphismPushforwardIsoApp :
    (SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α)).obj M ≅
      (pushforwardModules (coefficientMorphism J α)).obj M :=
  isoOfSheafIso (coefficientMorphismPushforwardSheafIso J α M)
    (moduleAddHom_comp_coefficientMorphismPushforwardSheafIso_hom J α M)
    (moduleSMulHom_comp_coefficientMorphismPushforwardSheafIso_hom J α M)

variable {J} in
/-- **The direct image of sheaves of modules along a change of coefficient rings is restriction
of scalars.** Each component is `coefficientMorphismPushforwardIsoApp`, the identity on
underlying sheaves of sets. -/
def coefficientMorphismPushforwardIso :
    SheafOfModules.restrictScalars ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α) ≅
      pushforwardModules (coefficientMorphism J α) :=
  NatIso.ofComponents (fun M ↦ coefficientMorphismPushforwardIsoApp J α M) fun _ ↦
    hom_ext_moduleSheafFunctor (Sheaf.hom_ext_sections fun _ _ ↦ rfl)

variable [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

variable {J} in
/-- **The pullback of sheaves of modules along a change of coefficient rings is left adjoint to
restriction of scalars**: it is left adjoint to the direct image (Stacks 03D7), which is
restriction of scalars by `coefficientMorphismPushforwardIso`. -/
def coefficientMorphismPullbackAdjunction :
    (coefficientMorphism J α).toModulesHom.pullbackModules ⊣
      SheafOfModules.restrictScalars
        ((sheafCompose J (forget₂ CommRingCat.{w} RingCat.{w})).map α) :=
  (pullbackAdjPushforwardModules (coefficientMorphism J α)).ofNatIsoRight
    (coefficientMorphismPushforwardIso α).symm

end AlgebraicGeometry.RingedToposHom

end
