module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FlatDeformation.Surjectivity
public import StacksFrontier.AlgebraicGeometry.PairDeformation.PolarizedThickening
public import StacksFrontier.Deformation.PairDeformation.PairSolution

/-!
# The pair extension problem of a polarized family over a thickening of its base

Let `x = (X, L)` be a polarized family over `Spec A`, with structure morphism `f : X ⟶ Spec A`,
and let `A' → A` be a deformation situation with kernel `I`, so that `Spec A ⊂ Spec A'` is a first
order thickening (`AlgebraicGeometry.PairDeformation.specThickening`). On the Zariski site of `X`
this file writes down the pair extension problem
(`Deformation.PairDeformation.PairExtensionProblem`) whose solutions are the lifts of `x` to
`A'`:

* the ring part is the deformation problem of `f` over `Spec A ⊂ Spec A'` of Stacks 0D14,
  `Stacks.Thickenings.FlatDeformation.problem`: the lower row is
  `f⁻¹𝒪_{Spec A'} ⟶ f⁻¹𝒪_{Spec A}`, the prescribed kernel is `G = f^*𝒞_{Spec A/Spec A'}`, the
  module `O_X ⊗_A I`;
* the module is `L`, its prescribed kernel is `GL = G ⊗_{O_X} L`, the module `L ⊗_A I`, and the
  pairing `G ⊗ L ⟶ GL` is the canonical map of the sectionwise tensor product to its
  sheafification.

## Main definitions

* `AlgebraicGeometry.PairDeformation.IsCanonicalIdealMap`: the condition on the map `c` of the
  ring part from the ideal of the thickened base to `G` that it sends the class of a section `j`
  of the ideal of `Spec A ⊂ Spec A'` to the pullback of the conormal class of `j`. It is the
  condition under which a solution of the ring part is realized by a flat deformation
  (`Stacks.Thickenings.FlatDeformation.deformationOf`), and it determines `c`
  (`Stacks.Thickenings.FlatDeformation.ideal_hom_ext`).
* `AlgebraicGeometry.PairDeformation.polarizedPairProblem`: the pair extension problem.
* `AlgebraicGeometry.PairDeformation.ringSolutionOfIsHomLift`: the solution of the ring part
  given by a polarized lift.
* `AlgebraicGeometry.PairDeformation.flatDeformationOfSolution`: the flat deformation of
  `X ⟶ Spec A` over `Spec A'` realizing the ring part of a solution, with
  `AlgebraicGeometry.PairDeformation.ringIsoOfSolution` identifying its solution with that ring
  part.

## Main results

* `AlgebraicGeometry.PairDeformation.idealMap_eq_of_isCanonicalIdealMap`: the map `c` read off from
  any flat deformation is the canonical one.

## Implementation notes

The map `c` is a parameter of the problem, constrained by `IsCanonicalIdealMap`; that property
determines it, and it is what the realization of solutions by flat deformations consumes.

## References

* [Stacks Project, Tag 0D14](https://stacks.math.columbia.edu/tag/0D14)
* [Stacks Project, Tag 0D4W](https://stacks.math.columbia.edu/tag/0D4W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Deformation.Artin Stacks.Thickenings Stacks.Thickenings.FlatDeformation

universe u

namespace AlgebraicGeometry.PairDeformation

/-! ### The canonical map `c` of the ring part -/

section Canonical

variable {X S' S'' : Scheme.{u}} (t : S' ⟶ S'') [IsClosedImmersion t] (hst : t.ker ^ 2 = ⊥)
  (f : X ⟶ S')

/-- The maps `c` of the deformation problem of `f` over `S' ⊂ S''`: from the ideal of the
thickened base to `f^*𝒞_{S'/S''}`, linear over `f⁻¹𝒪_{S'}`. -/
public abbrev IdealMap :=
  ideal t f hst ⟶ (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat.{u} RingCat.{u})).map
        (structureHom f).fSharpInverseImage)).obj (conormalModule t f)

/-- The map `c` is the canonical one: it sends the class of a section `j` of the ideal of
`S' ⊂ S''` to the pullback of the conormal class of `j`. -/
public def IsCanonicalIdealMap (c : IdealMap t hst f) : Prop :=
  ∀ (W : S''.Opens) (j : Γ(S'', W)) (hj : (t.app W).hom j = 0),
    (c.val.app (op ((Opens.map (f.base ≫ t.base)).obj W))).hom
        (idealSection (t := t) (f := f) hst W j hj) =
      canonicalSection (t := t) (f := f) W j hj

variable {t hst f} in
/-- The map `c` read off from any flat deformation is the canonical one. -/
public theorem idealMap_eq_of_isCanonicalIdealMap {c : IdealMap t hst f}
    (hc : IsCanonicalIdealMap t hst f c) (D : FlatDeformation t f) [IsIso D.i.base] :
    c = idealMap hst D :=
  ideal_hom_ext hst _ _ fun W j hj => (hc W j hj).trans (idealMap_idealSection hst D W j hj).symm

end Canonical

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} (hT : IsTerminal (B.obj hS))
  (P : AffineObject B S hS (polarizedSliceProjection B hS hT))
  (t : DeformationSituation B S hS P.alg)

/-- The prescribed kernel of the ring part, `G = f^*𝒞_{Spec A/Spec A'}`. -/
public abbrev ringKernel : P.obj.1.total.Modules :=
  conormalModule (specThickening t) (fiberStructure hT P.obj)

/-- The prescribed kernel of the module part, `GL = G ⊗_{O_X} L`. -/
public abbrev lineBundleKernel : P.obj.1.total.Modules :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor P.obj.1.total.sheaf).obj
    (ringKernel hT P t)).obj P.obj.1.lineBundle

/-- The pairing `G ⊗ L ⟶ G ⊗_{O_X} L`, the map of the sectionwise tensor product to its
sheafification. -/
public abbrev lineBundlePairing :
    PresheafOfModules.tensorObj (O := P.obj.1.total.sheaf.val) (ringKernel hT P t).val
        P.obj.1.lineBundle.val ⟶
      ((lineBundleKernel hT P t).val :
        PresheafOfModules.{u} (P.obj.1.total.sheaf.val ⋙ forget₂ CommRingCat.{u} RingCat.{u})) :=
  (PresheafOfModules.sheafificationAdjunction
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf P.obj.1.total.sheaf).obj)).unit.app
      (PresheafOfModules.tensorObj (O := P.obj.1.total.sheaf.val) (ringKernel hT P t).val
        P.obj.1.lineBundle.val) ≫
    PresheafOfModules.homMk (𝟙 _) (fun _ _ _ => rfl)

/-- **The pair extension problem of a polarized family over a thickening of its base.** For a
polarized family `x = (X, L)` over `Spec A` with structure morphism `f` and a deformation situation
`A' → A` with kernel `I`: the ring part is the deformation problem of `f` over `Spec A ⊂ Spec A'`
for the map `c`, with kernel `G = f^*𝒞_{Spec A/Spec A'} = O_X ⊗_A I`, the module is `L`, its
prescribed kernel is `G ⊗_{O_X} L = L ⊗_A I`, and the pairing is the canonical map
`G ⊗ L ⟶ G ⊗_{O_X} L`. -/
public def polarizedPairProblem
    (c : IdealMap (specThickening t) (specThickening_ker_sq t) (fiberStructure hT P.obj)) :
    Deformation.PairDeformation.PairExtensionProblem (sourceTopos P.obj.1.total)
      (reducedBase (fiberStructure hT P.obj)) where
  S := problem (specThickening t) (fiberStructure hT P.obj) (specThickening_ker_sq t) c
  L := P.obj.1.lineBundle
  moduleKernel := lineBundleKernel hT P t
  μ := lineBundlePairing hT P t

/-! ### The ring part of a lift, and the flat deformation of a solution -/

/-- The structure morphism of a polarized family in a fibre is flat. -/
public instance flat_fiberStructure {V : BigFppfOver B S hS}
    (x : (polarizedSliceProjection B hS hT).Fiber V) : Flat (fiberStructure hT x) := by
  have := x.1.flat
  infer_instance

variable {hT P t}

/-- **The ring part of a polarized lift.** A morphism `x ⟶ x'` of polarized families over
`Spec A ⟶ Spec A'` gives a solution of the ring part of the pair problem, for the canonical
map `c`: the structure sheaf of the total space of `x'`, read on `X`. -/
public def ringSolutionOfIsHomLift
    {c : IdealMap (specThickening t) (specThickening_ker_sq t) (fiberStructure hT P.obj)}
    (hc : IsCanonicalIdealMap (specThickening t) (specThickening_ker_sq t)
      (fiberStructure hT P.obj) c)
    (x' : (polarizedSliceProjection B hS hT).Fiber t.top.over) (φ : P.obj.1 ⟶ x'.1)
    (hφ : (polarizedSliceProjection B hS hT).IsHomLift t.hom.specMap φ) :
    (polarizedPairProblem hT P t c).S.CompatibleFirstOrderThickening :=
  have := (flatDeformationOfIsHomLift hT P t x' φ hφ).isIso_base (specThickening_ker_sq t)
  toSolution (specThickening_ker_sq t) (flatDeformationOfIsHomLift hT P t x' φ hφ) c
    (idealMap_eq_of_isCanonicalIdealMap hc _)

/-- **The flat deformation of a solution.** The ring part of a solution of the pair problem, for
the canonical map `c`, is realized by a flat deformation of `X ⟶ Spec A` over `Spec A'`
(Stacks 05YV and 063Y, through `Stacks.Thickenings.FlatDeformation.deformationOf`). -/
public abbrev flatDeformationOfSolution
    {c : IdealMap (specThickening t) (specThickening_ker_sq t) (fiberStructure hT P.obj)}
    (hc : IsCanonicalIdealMap (specThickening t) (specThickening_ker_sq t)
      (fiberStructure hT P.obj) c)
    (Q : (polarizedPairProblem hT P t c).Solution) :
    FlatDeformation (specThickening t) (fiberStructure hT P.obj) :=
  deformationOf Q.ring hc

/-- The deformation realizing a solution is a first order thickening of `X`, homeomorphic to it. -/
public instance isIso_flatDeformationOfSolution_i_base
    {c : IdealMap (specThickening t) (specThickening_ker_sq t) (fiberStructure hT P.obj)}
    (hc : IsCanonicalIdealMap (specThickening t) (specThickening_ker_sq t)
      (fiberStructure hT P.obj) c)
    (Q : (polarizedPairProblem hT P t c).Solution) :
    IsIso (flatDeformationOfSolution hc Q).i.base :=
  isIso_base_of_firstOrder _ (real_ker_sq (P := Q.ring))

/-- The ring part of a solution is isomorphic to the solution of the flat deformation it
realizes. -/
public def ringIsoOfSolution
    {c : IdealMap (specThickening t) (specThickening_ker_sq t) (fiberStructure hT P.obj)}
    (hc : IsCanonicalIdealMap (specThickening t) (specThickening_ker_sq t)
      (fiberStructure hT P.obj) c)
    (Q : (polarizedPairProblem hT P t c).Solution) :
    Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening.Iso.{u,
        u, u, u, u, u} (S := (polarizedPairProblem hT P t c).S)
      (toSolution (specThickening_ker_sq t) (flatDeformationOfSolution hc Q) c
        (idealMap_deformationOf Q.ring hc)) Q.ring :=
  solutionIsoDeformationOf Q.ring hc

end AlgebraicGeometry.PairDeformation

end
