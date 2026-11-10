module

public import StacksFrontier.Deformation.ToposThickening.CurvatureClass
public import StacksFrontier.Deformation.ToposThickening.ModulesOnThickening.TensorSheafSections

/-!
# The ideal part of a flat lift is natural, and the canonical class is independent of the lift

Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings on a site whose kernel is an
ideal sheaf `I` of square zero. The identification of the kernel of the reduction of a flat
lift with `F₀ ⊗_{O₀} I`, recorded by `Deformation.ComplexLift.IdealKernel`, is normalized on
local pure tensors by `x̄ ⊗ a ↦ a · x`. That normalization determines the identification, and
hence makes it natural: a morphism of flat lifts carries one ideal part to the other with no
further hypothesis.

Naturality of the ideal part is exactly the hypothesis `hemb` of the naturality statements of
Tag 0DIU in `StacksFrontier/Deformation/ToposThickening/CurvatureClass.lean`. This file proves it,
so those statements hold outright: supplying `Deformation.ComplexLift.emb_natural` for `hemb`
makes the curvature, the curvature class and the canonical class `ω` natural in the flat lift,
and makes two flat lifts of the same complex joined by a morphism of lifts give the same `ω`.

## Main results

* `Deformation.ToposThickening.tensorSheaf_restrict_hom_ext_of_locallySurjective_left`: two
  morphisms out of a restricted tensor product sheaf agree once they agree on the pure tensors
  whose *first* factor comes from a locally surjective family of sections.
* `Deformation.ComplexLift.emb_natural`: **the ideal part of a flat lift is natural** along a
  morphism of flat lifts.
* `Deformation.ComplexLift.obstructionMap_eq_of_hom'`: **Tag 0DIU**, two flat lifts of one
  complex joined by a morphism of lifts give the same `ω`, with no compatibility hypothesis.

## Implementation notes

The reduction of a flat lift is an epimorphism, because `f` is locally surjective, hence
locally surjective on sections; so a local section of the reduction of a term of the lift is,
after restriction along the arrows of a covering sieve, the reduction of a section of that
term. Combined with the fact that the tensor product sheaf is the sheafification of the
objectwise tensor product, this reduces an identity between two morphisms out of
`F₀ⁿ ⊗_{O₀} I` to an identity on pure tensors `x̄ ⊗ a` with `x` a section of `Fⁿ`; and there
both sides are `a · (the image of x)`, by the two normalizations and the fact that a morphism
of flat lifts is a morphism of sheaves of `O`-modules.

The first-factor extensionality principle is the mirror of
`Deformation.ToposThickening.tensorSheaf_restrict_hom_ext_of_locallySurjective`, which tests
the second factor; the ideal sheaf is the second factor here, so it is the first that has to be
covered.

## References

* [Stacks Project, Tag 0DIU](https://stacks.math.columbia.edu/tag/0DIU)
* [Stacks Project, Tag 0DIT](https://stacks.math.columbia.edu/tag/0DIT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct
open Stacks.Sheaves.ChangeOfRings (ringSheafMap)
open Stacks.SheafOfModules.ComplexLifting (IsExtensionOfScalars)

universe v u w d

namespace Deformation.ToposThickening

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- Two morphisms from a tensor product sheaf restricted along a morphism of sheaves of rings
agree as soon as they agree on the images of pure tensors whose *first* factor comes from a
locally surjective family of sections. -/
lemma tensorSheaf_restrict_hom_ext_of_locallySurjective_left {R : Sheaf J RingCat.{w}}
    (O : Sheaf J CommRingCat.{w}) (α : R ⟶ Stacks.SheafOfModules.Tensor.ringSheaf O)
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)} {P : SheafOfModules.{w} R}
    {Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (p : Q ⟶ M.val.presheaf)
    (hp : Presheaf.IsLocallySurjective J p)
    {f g : (SheafOfModules.restrictScalars α).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj N)).obj M) ⟶ P}
    (h : ∀ (U : Cᵒᵖ) (x : Q.obj U) (y : N.val.obj U),
      f.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj M.val N.val)).app U
        (p.app U x ⊗ₜ[O.obj.obj U] y)) =
      g.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj M.val N.val)).app U
        (p.app U x ⊗ₜ[O.obj.obj U] y))) :
    f = g := by
  have := hp
  apply tensorSheaf_restrict_hom_ext O α
  intro U x y
  apply P.isSheaf.isSeparated _ _ (Presheaf.imageSieve_mem J p x)
  rintro V a ⟨z, hz⟩
  have key (k : (SheafOfModules.restrictScalars α).obj
      ((((Stacks.SheafOfModules.Tensor.sheafTensor O).flip.obj N)).obj M) ⟶ P) :
      P.val.map a.op (k.val.app U (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj M.val N.val)).app U
          (x ⊗ₜ[O.obj.obj U] y))) =
        k.val.app (op V) (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app
        (PresheafOfModules.tensorObj M.val N.val)).app (op V)
          (M.val.map a.op x ⊗ₜ[O.obj.obj (op V)] N.val.map a.op y)) :=
    (PresheafOfModules.naturality_apply k.val a.op _).symm.trans
      (congrArg (fun t => k.val.app (op V) t)
        (tensorSheafificationUnit_naturality M N a.op x y))
  change P.val.map a.op _ = P.val.map a.op _
  refine (key f).trans (Eq.trans ?_ (key g).symm)
  change p.app _ z = M.val.map a.op x at hz
  rw [← hz]
  exact h _ _ _

end Deformation.ToposThickening

namespace Deformation.ComplexLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} {I : SheafMod O₀}
  [(((Stacks.SheafOfModules.Tensor.sheafTensor O₀).flip.obj I)).Additive] {S : SquareZeroIdeal f I}
  {K₀ L₀ : CochainComplex (SheafMod O₀) ℤ}
  {L : FlatLift f K₀} {M : FlatLift f L₀} {φ : K₀ ⟶ L₀}

/-- **The ideal part of a flat lift is natural.** A morphism of flat lifts carries the ideal
part of the source to the ideal part of the target, compatibly with the map induced on the
tensor products with the ideal sheaf. This is the hypothesis `hemb` of the naturality
statements of Tag 0DIU, and it holds outright: both sides send a local pure tensor `x̄ ⊗ a` to
`a` times the image of `x`, by the normalization of the two ideal parts. -/
theorem emb_natural (hf : Sheaf.IsLocallySurjective f) (h : FlatLiftHom L M φ)
    (TL : IdealKernel S L) (TM : IdealKernel S M) (n : ℤ) :
    (restrict f).map (((idealTensorFunctor O₀ I).map h.red).f n) ≫ TM.emb n =
      TL.emb n ≫ h.hom n := by
  have : Epi (L.baseChange.unit n) :=
    IsExtensionOfScalars.epi_unit.{v, u, w, w} f hf (L.baseChange.isExtension n)
  refine Deformation.ToposThickening.tensorSheaf_restrict_hom_ext_of_locallySurjective_left
    O₀ (ringSheafMap f)
    ((PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O).obj).map
      (L.baseChange.unit n).val)
    (Deformation.ToposThickening.sheafModule_epi_locallySurjective
      (L.baseChange.unit n)) ?_
  intro U x a
  have hred : (h.red.f n).val.app U ((L.baseChange.unit n).val.app U x) =
      (M.baseChange.unit n).val.app U ((h.hom n).val.app U x) :=
    (congrArg (fun k : L.F.X n ⟶ _ => k.val.app U x) (h.unit_red n)).symm
  change (TM.emb n).val.app U
      (((restrict f).map (((idealTensorFunctor O₀ I).map h.red).f n)).val.app U
        (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (L.baseChange.complex.X n).val I.val)).app U
          ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a))) =
    (h.hom n).val.app U ((TL.emb n).val.app U
      (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (L.baseChange.complex.X n).val I.val)).app U
        ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a)))
  have hmap : ((restrict f).map (((idealTensorFunctor O₀ I).map h.red).f n)).val.app U
        (((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (L.baseChange.complex.X n).val I.val)).app U
          ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a)) =
      ((PresheafOfModules.sheafificationAdjunction
        (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
        (PresheafOfModules.tensorObj (M.baseChange.complex.X n).val I.val)).app U
        ((M.baseChange.unit n).val.app U ((h.hom n).val.app U x) ⊗ₜ[O₀.obj.obj U] a) := by
    rw [← hred]
    exact Deformation.ToposThickening.tensorSheaf_map_unit_tmul O₀ (h.red.f n) U _ a
  rw [hmap, TM.emb_tmul n U ((h.hom n).val.app U x) a, TL.emb_tmul n U x a]
  exact (((h.hom n).val.app U).hom.map_smul
    (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from S.incl U a) x).symm

/-- **Stacks 0DIU.** Two flat lifts of the same complex joined by a morphism of flat lifts over
the identity give the same canonical class `ω(K₀)`. No compatibility of the ideal parts is
assumed: it is automatic. -/
@[stacks 0DIU "variant: independence of the flat lift at a supplied derived ideal tensor datum D;
the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem obstructionMap_eq_of_hom' [HasDerivedCategory.{d} (SheafMod O₀)]
    (D : DerivedIdealTensor I) (hf : Sheaf.IsLocallySurjective f) {L M : FlatLift f K₀}
    (h : FlatLiftHom L M (𝟙 K₀)) (TL : IdealKernel S L) (TM : IdealKernel S M) :
    obstructionMap D TL = obstructionMap D TM :=
  obstructionMap_eq_of_hom D h TL TM (emb_natural hf h TL TM)

end Deformation.ComplexLift

end
