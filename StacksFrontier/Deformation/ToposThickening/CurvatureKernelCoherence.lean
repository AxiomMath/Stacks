module

public import StacksFrontier.Deformation.ToposThickening.CurvatureLiftExistence
public import StacksFrontier.Deformation.ToposThickening.IdealKernelNaturality
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.BaseChangeLocallySurjective
import StacksCore.Tactic.StacksAttribute

/-!
# The kernel identifications of two flat lifts agree along a morphism of lifts

The curvature class of Tag 0DIU is read in the ideal part `F₀ ⊗_{O₀} I` of a flat lift, through
an identification `Deformation.ComplexLift.IdealKernel` of that ideal part with the kernel of the
reduction, normalized on local pure tensors by `x̄ ⊗ a ↦ a · x`. The naturality and independence
statements of
`StacksFrontier.Deformation.ToposThickening.CurvatureClass` and
`StacksFrontier.Deformation.ToposThickening.CurvatureLiftExistence` carry a hypothesis `hemb`
saying that a morphism of flat lifts carries one identification to the other. This file proves
that hypothesis: it is a consequence of the normalization alone, so it never has to be assumed.

The proof is the only possible one: both sides of `hemb` are morphisms out of `F₀ ⊗_{O₀} I`, so
they agree as soon as they agree on local pure tensors, and every local pure tensor is locally of
the form `x̄ ⊗ a` with `x` a section of the lift, because the reduction of a lifted term is
locally surjective. On such a tensor both sides are `a · x` read in the target, by the two
normalizations and the `O`-linearity of the morphism of lifts.

## Main results

* `Deformation.ComplexLift.restrictTensor_hom_ext`: a morphism out of `F ⊗_{O₀} I`, restricted
  along `f`, is determined by its values on local pure tensors.
* `Deformation.ComplexLift.restrictTensor_hom_ext_of_unit`: the same, with the first factor of
  the pure tensors restricted to the image of a locally surjective morphism.
* `Deformation.ComplexLift.emb_coherence`: **Tag 0DIU**, the hypothesis `hemb`.
* `Deformation.ComplexLift.obstructionMap_eq_of_hom'`,
  `Deformation.ComplexLift.obstructionMap_eq_of_lift`: **Tag 0DIU**, the independence
  statements with `hemb` discharged.

## Implementation notes

The two facts the discharge rests on are proved here for the first time in the tree. Local
surjectivity of the sheafification unit defining the tensor product is read off the instance for
`CategoryTheory.toSheafify`, which `tensorUnitTypes` exposes in the shape instance search wants;
local surjectivity of an abstract extension of scalars is
`Stacks.SheafOfModules.ComplexLifting.IsExtensionOfScalars.isLocallySurjective`, proved in
`StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.BaseChange` by transporting the model's
one along the comparison isomorphism. Only `Epi` was available before, which is too weak: a
section of the reduction has to be *written* as the image of a section of the lift on a covering,
not merely be in the image of an epimorphism.

## References

* [Stacks Project, Tag 0DIU](https://stacks.math.columbia.edu/tag/0DIU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Sheaves.ChangeOfRings (ringSheafMap)
open Stacks.SheafOfModules.ComplexLifting (GradedDifferential BaseChangeTo
  IsExtensionOfScalars)

universe v u w d

namespace Deformation.ComplexLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}

section Generic

variable [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify J AddCommGrpCat.{w}]

section HomExt

variable {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀)

/-- The sheafification unit defining `F ⊗_{O₀} I`, read as a map of type-valued presheaves of
sections. It is the same map as `tensorSheafificationUnit`; this spelling is the one whose
local surjectivity instance search finds. -/
abbrev tensorUnitTypes {O₀ : Sheaf J CommRingCat.{w}} (G I : SheafMod O₀) :=
  Functor.whiskerRight (CategoryTheory.toSheafify J
    (MonoidalCategoryStruct.tensorObj G.val I.val).presheaf) (forget AddCommGrpCat.{w})

/-- The sheafification unit at `U`, sending a section of the presheaf tensor product to the
corresponding section of `G ⊗_{O₀} I`. -/
private abbrev tensorUnitApp {O₀ : Sheaf J CommRingCat.{w}} (G I : SheafMod O₀) (U : Cᵒᵖ) :=
  ((PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
    (PresheafOfModules.tensorObj G.val I.val)).app U

/-- **A morphism out of `F ⊗_{O₀} I` is determined by its values on local pure tensors**, even
after restriction of scalars along `f`: the sheafification unit defining the tensor product is
locally surjective and the target is a sheaf. -/
theorem restrictTensor_hom_ext {I G : SheafMod O₀} {N : SheafMod O}
    (k l : (restrict f).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I)).obj G) ⟶ N)
    (h : ∀ (U : Cᵒᵖ) (x : G.val.obj U) (a : I.val.obj U),
      k.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj G.val I.val)).app U (x ⊗ₜ[O₀.obj.obj U] a)) =
      l.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj G.val I.val)).app U (x ⊗ₜ[O₀.obj.obj U] a))) : k = l := by
  ext U s
  refine N.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J (tensorUnitTypes G I) s) _ _ ?_
  rintro V g ⟨t, ht⟩
  have key : ∀ m : (restrict f).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I)).obj G) ⟶ N,
      N.val.map g.op (m.val.app U s) = m.val.app (Opposite.op V) (tensorUnitApp G I _ t) :=
    fun m => (PresheafOfModules.naturality_apply m.val g.op s).symm.trans (congrArg _ ht.symm)
  change N.val.map g.op (k.val.app U s) = N.val.map g.op (l.val.app U s)
  rw [key k, key l]
  clear key ht
  induction t using TensorProduct.inductionOn with
  | tmul x a => exact h (Opposite.op V) x a
  | add x y hx hy =>
      erw [map_add, map_add, map_add]
      rw [hx, hy]

/-- **A morphism out of `F ⊗_{O₀} I` is determined by its values on the pure tensors coming
from a locally surjective map into `F`.** -/
theorem restrictTensor_hom_ext_of_unit {I G : SheafMod O₀} {X N : SheafMod O}
    (u : X ⟶ (restrict f).obj G)
    (hu : Sheaf.IsLocallySurjective
      ((_root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)).map u))
    (k l : (restrict f).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I)).obj G) ⟶ N)
    (h : ∀ (U : Cᵒᵖ) (x : X.val.obj U) (a : I.val.obj U),
      k.val.app U
        (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj G.val I.val)).app U (u.val.app U x ⊗ₜ[O₀.obj.obj U] a)) =
      l.val.app U
        (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj G.val I.val)).app U
          (u.val.app U x ⊗ₜ[O₀.obj.obj U] a))) : k = l := by
  refine restrictTensor_hom_ext f k l fun U y a => ?_
  have := hu
  refine N.isSheaf.isSeparated _ _
    (Presheaf.imageSieve_mem J
      ((_root_.SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf O)).map u).hom y) _ _ ?_
  rintro V g ⟨m, hm⟩
  have key : ∀ n : (restrict f).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I)).obj G) ⟶ N,
      N.val.map g.op (n.val.app U (tensorUnitApp G I U (y ⊗ₜ[O₀.obj.obj U] a))) =
        n.val.app (Opposite.op V)
          (tensorUnitApp G I _ (u.val.app (Opposite.op V) m ⊗ₜ[O₀.obj.obj _] I.val.map g.op a)) :=
    fun n => by
      rw [show u.val.app (Opposite.op V) m = G.val.map g.op y from hm]
      exact (PresheafOfModules.naturality_apply n.val g.op _).symm.trans (congrArg _
        (PresheafOfModules.naturality_apply ((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
          (PresheafOfModules.tensorObj G.val I.val)) g.op _).symm)
  change N.val.map g.op (k.val.app U (tensorUnitApp G I U (y ⊗ₜ[O₀.obj.obj U] a))) =
    N.val.map g.op (l.val.app U (tensorUnitApp G I U (y ⊗ₜ[O₀.obj.obj U] a)))
  rw [key k, key l]
  exact h (Opposite.op V) m (I.val.map g.op a)

end HomExt

section Coherence

variable {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} {I : SheafMod O₀}
  [(((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I)).Additive] {S : SquareZeroIdeal f I}
  {K₀ L₀ : CochainComplex (SheafMod O₀) ℤ}

/-- **Stacks 0DIU, coherence of the kernel identifications.** A morphism of flat lifts carries
the identification of the ideal part of the source to that of the target. This is the hypothesis
`hemb` of `Deformation.ComplexLift.obstructionMap_natural` and of
`Deformation.ComplexLift.obstructionMap_eq_of_hom`, and it holds for *every* pair of
identifications, because both are normalized by the same pure-tensor formula
`Deformation.ComplexLift.IdealKernel.emb_tmul`. -/
@[stacks 0DIU "variant: a morphism of flat lifts carries the kernel identification to the kernel
identification, a step of the proof; the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem emb_coherence (hf : Sheaf.IsLocallySurjective f)
    {L : FlatLift f K₀} {M : FlatLift f L₀} {φ : K₀ ⟶ L₀} (h : FlatLiftHom L M φ)
    (TL : IdealKernel S L) (TM : IdealKernel S M) (n : ℤ) :
    (restrict f).map (((idealTensorFunctor O₀ I).map h.red).f n) ≫ TM.emb n =
      TL.emb n ≫ h.hom n := by
  have hu : Sheaf.IsLocallySurjective
      ((_root_.SheafOfModules.toSheaf (Stacks.SheafOfModules.Tensor.ringSheaf O)).map
        (L.baseChange.unit n)) :=
    Stacks.SheafOfModules.ComplexLifting.IsExtensionOfScalars.isLocallySurjective f hf
      (L.baseChange.isExtension n)
  refine restrictTensor_hom_ext_of_unit f (L.baseChange.unit n) hu _ _ fun U x a => ?_
  have hmap := Deformation.ToposThickening.tensorSheaf_map_unit_tmul O₀ (h.red.f n) U
    ((L.baseChange.unit n).val.app U x) a
  have hunit := congrArg (fun k : L.F.X n ⟶ (restrict f).obj (M.baseChange.complex.X n) =>
    k.val.app U x) (h.unit_red n)
  have hy : (h.red.f n).val.app U ((L.baseChange.unit n).val.app U x) =
      (M.baseChange.unit n).val.app U ((h.hom n).val.app U x) := hunit.symm
  calc (((restrict f).map (((idealTensorFunctor O₀ I).map h.red).f n) ≫ TM.emb n).val.app U)
        (tensorUnitApp (L.baseChange.complex.X n) I U
          ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a))
      = (TM.emb n).val.app U
          (tensorUnitApp (M.baseChange.complex.X n) I U
            ((M.baseChange.unit n).val.app U ((h.hom n).val.app U x) ⊗ₜ[O₀.obj.obj U] a)) := by
        rw [← hy]
        exact congrArg (fun t => (TM.emb n).val.app U t) hmap
    _ = (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from S.incl U a) •
          (h.hom n).val.app U x := TM.emb_tmul n U _ a
    _ = (h.hom n).val.app U
          ((show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from S.incl U a) • x) :=
        (((h.hom n).val.app U).hom.map_smul _ _).symm
    _ = ((TL.emb n ≫ h.hom n).val.app U)
          (tensorUnitApp (L.baseChange.complex.X n) I U
            ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a)) := by
        rw [← TL.emb_tmul n U x a]
        rfl

end Coherence

section Derived

variable {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} {I : SheafMod O₀}
  [(((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I)).Additive]
  [HasDerivedCategory.{d} (SheafMod O₀)]
  {S : SquareZeroIdeal f I} (D : DerivedIdealTensor I)
  {K₀ L₀ : CochainComplex (SheafMod O₀) ℤ}

/-! Naturality of `ω` along a morphism of flat lifts and the independence of `ω` of the flat
lift are
`Deformation.ComplexLift.obstructionMap_natural` in
`StacksFrontier/Deformation/ToposThickening/CurvatureClass.lean` and
`Deformation.ComplexLift.obstructionMap_eq_of_hom'` in
`StacksFrontier/Deformation/ToposThickening/IdealKernelNaturality.lean`; the hypothesis `hemb` the
first of them takes is discharged by `Deformation.ComplexLift.emb_natural`. -/

end Derived

end Generic

section Canonical

variable [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  {O O₀ : Sheaf J CommRingCat.{max u v w}} {f : O ⟶ O₀} {I : SheafMod O₀}
  [(((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I)).Additive]
  [HasDerivedCategory.{d} (SheafMod O₀)]
  {S : SquareZeroIdeal f I} (D : DerivedIdealTensor I)
  {K₀ : CochainComplex (SheafMod O₀) ℤ}

/-- **Stacks 0DIU, `ω(K₀)` does not depend on the flat lift.** Given a kernel identification on
every bounded above flat lift of `K₀` -- no compatibility between them assumed, since
`Deformation.ComplexLift.emb_coherence` supplies it -- the map `ω(K₀)` computed from any two
flat lifts is the same. The comparison that forces the agreement is
`Deformation.ComplexLift.exists_flatLiftHom_pair`, Stacks 0DIT applied to the direct sum of the
two lifted families. -/
@[stacks 0DIU "variant: ω depends on the complex alone at a supplied derived ideal tensor datum D;
the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem obstructionMap_eq_of_lift (hf : Sheaf.IsLocallySurjective f)
    (hK : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (K₀.homology n))
    (kern : ∀ M : FlatLift f K₀, IdealKernel S M) (L L' : FlatLift f K₀) :
    obstructionMap D (kern L) = obstructionMap D (kern L') :=
  obstructionMap_eq_of_coherentKernels D hf hK kern
    (fun h n => emb_coherence hf h _ _ n) L L'

end Canonical

end Deformation.ComplexLift

end
