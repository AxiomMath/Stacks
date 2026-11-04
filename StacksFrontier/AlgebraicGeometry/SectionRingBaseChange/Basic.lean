module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPullbackMultiplication
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TwistSectionRing
public import StacksFrontier.AlgebraicGeometry.InvertiblePullback.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Affine
public import StacksFrontier.AlgebraicGeometry.RelativeAmple.DirectImageAlgebra
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr

/-!
# Pulling back sections of the tensor powers of an invertible module, multiplicatively

Let `q : Y' ⟶ Y` be a morphism of schemes, `ℳ` an invertible `𝒪_Y`-module and `ℳ'` an invertible
`𝒪_{Y'}`-module with an isomorphism `ε : q^*ℳ ≅ ℳ'`.  For every integer `n`, an open `V` of `Y`
and an open `V' ≤ q⁻¹V` of `Y'`, a section of `ℳ^{⊗ n}` over `V` pulls back to a section of
`(ℳ')^{⊗ n}` over `V'`: pull back along `q` (the unit of `q^* ⊣ q_*`), compare
`q^*(ℳ^{⊗ n}) ≅ (q^*ℳ)^{⊗ n}` ([Stacks, Tag 01CU] with [Stacks, Tag 01CD]), restrict to `V'`, and
transport along `ε`.  This file proves that this is **multiplicative**: it carries the product
of the Laurent algebra `⨁_{n ∈ ℤ} ℳ^{⊗ n}` over `V` to the product of the Laurent algebra of `ℳ'`
over `V'`, and it is semilinear along `q`.

This is the input that makes the pullback of sections a homomorphism of graded rings of
sections, which the proof of [Stacks, Tag 0D4F] (3) uses to identify the section algebra of a
deformation with the base change of the section algebra of a Noetherian model.

## Main definitions

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.pullPow`: the pullback of a section of a
  tensor power along a morphism of ringed spaces, read in the tensor power of the pullback.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull`: the pullback of a section of
  `ℳ^{⊗ n}` over `V` to a section of `(ℳ')^{⊗ n}` over `V'`, for a morphism of schemes.

## Main results

* `Stacks.AlgebraicGeometry.SectionRingBaseChange.pullPow_mul`: the pullback of a product of
  sections of tensor powers is the product of their pullbacks.
* `Stacks.AlgebraicGeometry.SectionRingBaseChange.sectionPull_mul`,
  `sectionPull_smul`: the same for `sectionPull`, and its semilinearity.

## References

* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.RingedSpace Stacks.PullbackTensorCoherence Stacks.SheafOfModules.TensorPower
open Stacks.TensorPowerPullback RingedSpaceModuleAdjunction

universe u

namespace Stacks.AlgebraicGeometry.SectionRingBaseChange

attribute [local instance] Stacks.PullbackGradedAlgebra.monoidalCategory

/-! ### The ringed-space statement -/

section RingedSpace

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  (L : _root_.SheafOfModules.{u} (structureRingSheaf Y))
  [Stacks.SheafOfModules.IsInvertible Y.presheaf (isSheafStructure Y) L]

/-- The pullback of a local section of `L^{⊗ n}` along `f`, read in `(f^*L)^{⊗ n}` through the
comparison `f^*(L^{⊗ n}) ≅ (f^*L)^{⊗ n}` of [Stacks, Tag 01CU]. -/
def pullPow (n : ℤ) (U : (Opens Y.carrier)ᵒᵖ)
    (s : (tensorPower Y.presheaf (isSheafStructure Y) L n).val.obj U) :
    (tensorPower X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L) n).val.obj
      ((opensMap f).op.obj U) :=
  (pullbackIntPowIso f L n).hom.val.app _ (pullbackUnit f _ U s)

/-- **The pullback of a product of sections of tensor powers is the product of their
pullbacks**: the comparison of [Stacks, Tag 01CU] carries the multiplication of the Laurent
algebra of `L` to that of `f^*L` (`pullbackIntPowIso_coherentMulIso`), and the comparison of
[Stacks, Tag 01CD] carries a pullback of a pure tensor to the pure tensor of the pullbacks
(`pullbackTensorComparison_pullbackUnit`). -/
theorem pullPow_mul (n m : ℤ) (U : (Opens Y.carrier)ᵒᵖ)
    (s : (tensorPower Y.presheaf (isSheafStructure Y) L n).val.obj U)
    (t : (tensorPower Y.presheaf (isSheafStructure Y) L m).val.obj U) :
    pullPow f L (n + m) U ((mulBilinear Y.presheaf (isSheafStructure Y) L n m).app U s t) =
      (mulBilinear X.presheaf (isSheafStructure X) ((pullbackFunctor f).obj L) n m).app _
        (pullPow f L n U s) (pullPow f L m U t) := by
  have h1 := congrArg (fun φ => φ.val.app ((opensMap f).op.obj U)
    (pullbackUnit f _ U (tmul Y _ _ U s t))) (pullbackIntPowIso_coherentMulIso f L n m)
  have h2 := pullbackTensorComparison_pullbackUnit f
    (tensorPower Y.presheaf (isSheafStructure Y) L n)
    (tensorPower Y.presheaf (isSheafStructure Y) L m) U s t
  have h3 := pullbackUnit_naturality f (coherentMulIso Y.presheaf (isSheafStructure Y) L n m).hom
    U (tmul Y _ _ U s t)
  refine (congrArg ((pullbackIntPowIso f L (n + m)).hom.val.app ((opensMap f).op.obj U))
    h3.symm).trans ?_
  refine h1.trans ?_
  refine congrArg ((coherentMulIso X.presheaf (isSheafStructure X)
    ((pullbackFunctor f).obj L) n m).hom.val.app ((opensMap f).op.obj U)) ?_
  refine (congrArg ((tensorSheafMapIso X.presheaf (isSheafStructure X) (pullbackIntPowIso f L n)
    (pullbackIntPowIso f L m)).hom.val.app ((opensMap f).op.obj U)) h2).trans ?_
  exact Stacks.SheafOfModules.tensorSections_tensorMapAt _ _ _ _ _ _ _ _ _ _ _

end RingedSpace

/-! ### Schemes -/

section Scheme

variable {Y' Y : Scheme.{u}} (q : Y' ⟶ Y) (M : Y.Modules) [Stacks.Ample.IsInvertibleModule Y M]
  (M' : Y'.Modules) [Stacks.Ample.IsInvertibleModule Y' M']
  (ε : (Scheme.Modules.pullback q).obj M ≅ M')

/-- Invertibility of an `𝒪_Y`-module, in the spelling of the integral tensor powers. -/
theorem isInvertible_tensorPower_of_isInvertibleModule (Z : Scheme.{u}) (N : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z N] :
    Stacks.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (isSheafStructure Z.toRingedSpace) N :=
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ N).2 ‹_›

/-- Local instance form of `isInvertible_tensorPower_of_isInvertibleModule`. -/
private instance isInvertible_of_isInvertibleModule (Z : Scheme.{u}) (N : Z.Modules)
    [Stacks.Ample.IsInvertibleModule Z N] :
    Stacks.SheafOfModules.IsInvertible Z.toRingedSpace.presheaf
      (isSheafStructure Z.toRingedSpace) N :=
  isInvertible_tensorPower_of_isInvertibleModule Z N

/-- **The pullback of a section of `ℳ^{⊗ n}` over `V` to a section of `(ℳ')^{⊗ n}` over
`V' ≤ q⁻¹V`**: pull back along `q`, compare the tensor powers, restrict, and transport along
`ε : q^*ℳ ≅ ℳ'`. -/
def sectionPull (n : ℤ) (V : Y.Opens) (V' : Y'.Opens) (h : V' ≤ q ⁻¹ᵁ V) :
    ((Stacks.RelativeAmple.laurentPowers M).piece n).val.obj (op V) →+
      ((Stacks.RelativeAmple.laurentPowers M').piece n).val.obj (op V') :=
  haveI := isInvertible_tensorPower_of_isInvertibleModule Y M
  haveI := isInvertible_tensorPower_of_isInvertibleModule Y' M'
  haveI := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj M)
  haveI := isEquivalence_tensorRightFunctor Y.toRingedSpace.presheaf
    (isSheafStructure Y.toRingedSpace) M
  ((ConcreteCategory.hom
      ((Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n).hom.val.app
        (op V'))).toAddMonoidHom.comp
    (ConcreteCategory.hom ((tensorPower Y'.toRingedSpace.presheaf
      (isSheafStructure Y'.toRingedSpace)
        ((pullbackFunctor q.toLRSHom.toShHom).obj M) n).val.map
          (homOfLE h).op)).toAddMonoidHom).comp
    ((ConcreteCategory.hom ((pullbackIntPowIso q.toLRSHom.toShHom M n).hom.val.app
        ((opensMap q.toLRSHom.toShHom).op.obj (op V)))).toAddMonoidHom.comp
      (ConcreteCategory.hom (((pullbackAdjunction q.toLRSHom.toShHom).unit.app
        (tensorPower Y.toRingedSpace.presheaf (isSheafStructure Y.toRingedSpace) M n)).val.app
          (op V))).toAddMonoidHom)

/-- `sectionPull` sends a section `s` to the transport along `ε` of the restriction to `V'` of
the pullback `pullPow` of `s` along `q`. -/
theorem sectionPull_apply (n : ℤ) (V : Y.Opens) (V' : Y'.Opens) (h : V' ≤ q ⁻¹ᵁ V)
    (s : ((Stacks.RelativeAmple.laurentPowers M).piece n).val.obj (op V)) :
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y M
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y' M'
    haveI := isInvertible_tensorPower_of_isInvertibleModule Y' ((Scheme.Modules.pullback q).obj M)
    sectionPull q M M' ε n V V' h s =
      (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso ε n).hom.val.app
        (op V') ((tensorPower Y'.toRingedSpace.presheaf (isSheafStructure Y'.toRingedSpace)
          ((pullbackFunctor q.toLRSHom.toShHom).obj M) n).val.map (homOfLE h).op
            (pullPow q.toLRSHom.toShHom M n (op V) s)) :=
  rfl

/-- **`sectionPull` is multiplicative**: it carries the product of the Laurent algebra of `ℳ`
over `V` to the product of the Laurent algebra of `ℳ'` over `V'`. -/
theorem sectionPull_mul (n m : ℤ) (V : Y.Opens) (V' : Y'.Opens) (h : V' ≤ q ⁻¹ᵁ V)
    (s : ((Stacks.RelativeAmple.laurentPowers M).piece n).val.obj (op V))
    (t : ((Stacks.RelativeAmple.laurentPowers M).piece m).val.obj (op V)) :
    sectionPull q M M' ε (n + m) V V' h
        (((Stacks.RelativeAmple.laurentPowers M).mul n m).app (op V) s t) =
      ((Stacks.RelativeAmple.laurentPowers M').mul n m).app (op V')
        (sectionPull q M M' ε n V V' h s) (sectionPull q M M' ε m V V' h t) := by
  rw [sectionPull_apply, sectionPull_apply, sectionPull_apply]
  have h1 := pullPow_mul q.toLRSHom.toShHom M n m (op V) s t
  have h2 := (mulBilinear Y'.toRingedSpace.presheaf (isSheafStructure Y'.toRingedSpace)
    ((pullbackFunctor q.toLRSHom.toShHom).obj M) n m).naturality (homOfLE h).op
      (pullPow q.toLRSHom.toShHom M n (op V) s) (pullPow q.toLRSHom.toShHom M m (op V) t)
  have h3 := (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentAlgebraCongr.laurentCongrHom
    ε).map_mul n m (op V')
      ((tensorPower Y'.toRingedSpace.presheaf (isSheafStructure Y'.toRingedSpace)
          ((pullbackFunctor q.toLRSHom.toShHom).obj M) n).val.map (homOfLE h).op
            (pullPow q.toLRSHom.toShHom M n (op V) s))
      ((tensorPower Y'.toRingedSpace.presheaf (isSheafStructure Y'.toRingedSpace)
          ((pullbackFunctor q.toLRSHom.toShHom).obj M) m).val.map (homOfLE h).op
            (pullPow q.toLRSHom.toShHom M m (op V) t))
  refine Eq.trans ?_ h3
  refine congrArg _ (Eq.trans ?_ h2)
  exact congrArg _ h1

/-- **`sectionPull` is semilinear along `q`.** -/
theorem sectionPull_smul (n : ℤ) (V : Y.Opens) (V' : Y'.Opens) (h : V' ≤ q ⁻¹ᵁ V)
    (r : Y.ringCatSheaf.obj.obj (op V))
    (s : ((Stacks.RelativeAmple.laurentPowers M).piece n).val.obj (op V)) :
    sectionPull q M M' ε n V V' h (r • s) =
      (show Y'.ringCatSheaf.obj.obj (op V') from q.appLE V V' h r) •
        sectionPull q M M' ε n V V' h s := by
  have := isEquivalence_tensorRightFunctor Y.toRingedSpace.presheaf
    (isSheafStructure Y.toRingedSpace) M
  rw [sectionPull_apply, sectionPull_apply]
  have h1 := pullbackUnit_smul q.toLRSHom.toShHom
    (tensorPower Y.toRingedSpace.presheaf (isSheafStructure Y.toRingedSpace) M n) (op V) r s
  have e1 :=
    (congrArg ((pullbackIntPowIso q.toLRSHom.toShHom M n).hom.val.app
      ((opensMap q.toLRSHom.toShHom).op.obj (op V))) h1).trans (map_smul _ _ _)
  refine (congrArg (fun z => (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso
    ε n).hom.val.app (op V') ((tensorPower Y'.toRingedSpace.presheaf
      (isSheafStructure Y'.toRingedSpace) ((pullbackFunctor q.toLRSHom.toShHom).obj M) n).val.map
        (homOfLE h).op z)) e1).trans ?_
  refine (congrArg ((Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso
    ε n).hom.val.app (op V')) (PresheafOfModules.map_smul (tensorPower Y'.toRingedSpace.presheaf
      (isSheafStructure Y'.toRingedSpace) ((pullbackFunctor q.toLRSHom.toShHom).obj M) n).val
        (homOfLE h).op _ _)).trans ?_
  exact ((Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso
    ε n).hom.val.app (op V')).hom.map_smul _ _

/-! ### Bijectivity along an open immersion -/

/-- An isomorphism of sheaves of modules is bijective on sections. -/
theorem bijective_iso_hom_app {Z : Scheme.{u}} {N N' : _root_.SheafOfModules.{u} Z.ringCatSheaf}
    (φ : N ≅ N') (W : (Z.Opens)ᵒᵖ) : Function.Bijective (φ.hom.val.app W) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨φ.inv.val.app W, fun x => ?_, fun y => ?_⟩
  · exact congrArg (fun ψ : N ⟶ N => ψ.val.app W x) φ.hom_inv_id
  · exact congrArg (fun ψ : N' ⟶ N' => ψ.val.app W y) φ.inv_hom_id

/-- Restriction between two equal opens is bijective. -/
theorem bijective_map_homOfLE_of_eq {Z : Scheme.{u}} (N : _root_.SheafOfModules.{u} Z.ringCatSheaf)
    {W W' : Z.Opens} (h : W' ≤ W) (h' : W ≤ W') :
    Function.Bijective (N.val.map (homOfLE h).op) := by
  obtain rfl : W' = W := le_antisymm h h'
  have e : (homOfLE h).op = 𝟙 (op W') := Subsingleton.elim _ _
  rw [e, N.val.map_id]
  exact Function.bijective_id

/-- **Along an open immersion `ι : Y' ⟶ Y`, pulling back the sections over an open `W` contained
in the image is bijective.** Composed with the comparison of the restriction with the pullback it
is restriction to `ι(ι⁻¹W) = W`. -/
theorem bijective_pullbackUnit_of_isOpenImmersion (ι : Y' ⟶ Y) [IsOpenImmersion ι]
    (N : Y.Modules) (W : Y.Opens) (hW : ι ''ᵁ (ι ⁻¹ᵁ W) = W) :
    Function.Bijective (((pullbackAdjunction ι.toLRSHom.toShHom).unit.app N).val.app (op W)) := by
  have hcomp : ∀ a : N.val.obj (op W),
      ((Scheme.Modules.restrictFunctorIsoPullback ι).inv.app N).val.app (op (ι ⁻¹ᵁ W))
        (((pullbackAdjunction ι.toLRSHom.toShHom).unit.app N).val.app (op W) a) =
      N.val.map (homOfLE (ι.image_preimage_le W)).op a :=
    Scheme.Modules.restrictFunctorIsoPullback_inv_unit ι N W
  have hb := bijective_map_homOfLE_of_eq N (ι.image_preimage_le W) hW.symm.le
  have hi := bijective_iso_hom_app ((Scheme.Modules.restrictFunctorIsoPullback ι).app N).symm
    (op (ι ⁻¹ᵁ W))
  refine ⟨fun a b hab => hb.1 ?_, fun y => ?_⟩
  · rw [← hcomp, ← hcomp, hab]
  · obtain ⟨a, ha⟩ := hb.2 (((Scheme.Modules.restrictFunctorIsoPullback ι).inv.app N).val.app
      (op (ι ⁻¹ᵁ W)) y)
    refine ⟨a, hi.1 ?_⟩
    exact (hcomp a).trans ha

/-- **Along an open immersion, `sectionPull` is bijective** on the sections over an open `W`
contained in the image, read over its inverse image. -/
theorem bijective_sectionPull_of_isOpenImmersion (ι : Y' ⟶ Y) [IsOpenImmersion ι] (n : ℤ)
    (W : Y.Opens) (hW : ι ''ᵁ (ι ⁻¹ᵁ W) = W) (V' : Y'.Opens) (h : V' ≤ ι ⁻¹ᵁ W)
    (h' : ι ⁻¹ᵁ W ≤ V') :
    Function.Bijective (sectionPull ι M ((Scheme.Modules.pullback ι).obj M) (Iso.refl _) n W V'
      h) := by
  have := isEquivalence_tensorRightFunctor Y.toRingedSpace.presheaf
    (isSheafStructure Y.toRingedSpace) M
  have h1 := bijective_pullbackUnit_of_isOpenImmersion ι
    (tensorPower Y.toRingedSpace.presheaf (isSheafStructure Y.toRingedSpace) M n) W hW
  have h2 := bijective_iso_hom_app (pullbackIntPowIso ι.toLRSHom.toShHom M n)
    ((opensMap ι.toLRSHom.toShHom).op.obj (op W))
  have h3 := bijective_map_homOfLE_of_eq (tensorPower Y'.toRingedSpace.presheaf
    (isSheafStructure Y'.toRingedSpace) ((pullbackFunctor ι.toLRSHom.toShHom).obj M) n) h h'
  have h4 := bijective_iso_hom_app
    (Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.LaurentCongr.congrIso
      (Iso.refl ((Scheme.Modules.pullback ι).obj M)) n) (op V')
  exact h4.comp (h3.comp (h2.comp h1))

end Scheme

end Stacks.AlgebraicGeometry.SectionRingBaseChange

end
