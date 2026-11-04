module

public import StacksFrontier.AlgebraicGeometry.TwistMultTransport.Structural
public import StacksFrontier.AlgebraicGeometry.ProjInclusionTwist.Basic

/-!
# Transporting Tag 01MY's multiplication identity along the factors of Tag 01NO's comparison

Tag 01NO's fourth assertion is that the canonical isomorphisms on the twists of an inclusion of
affine opens commute with the multiplication maps `𝒪(n) ⊗ 𝒪(m) ⟶ 𝒪(n + m)`. The mathematics is
Tag 01MY's `Stacks.AlgebraicGeometry.ProjMapCard.projMapData_preserves_products`, which carries
a live project tag; what stands between the two is a *transport*, because Tag 01NO's comparison
`Stacks.AlgebraicGeometry.ProjInclusionTwist.projInclusionTwistIso` wraps Tag 01MY's twist map
in five structural isomorphisms of the inverse image. This file supplies the transport
machinery and the restatement of Tag 01MY the machinery consumes.

## Main results

* `Stacks.AlgebraicGeometry.TwistMultTransport.transport_tstep`: **one factor of the transport,
  with the tensor product split.** A factor of Tag 01NO's comparison is used at three modules at
  once -- at the two twists, where it contributes to the tensor product of the comparisons, and
  at the tensor product of the twists, where it mediates between the two multiplications -- and
  this lemma keeps those three uses in step from the factor's naturality square and its monoidal
  coherence.
* `Stacks.AlgebraicGeometry.TwistMultTransport.transport_last`, `transport_head`,
  `transport_middle`, `transport_functor_coh`, `comp_eq_of_id`: the remaining steps, each stated
  at the level of variables.
* `Stacks.AlgebraicGeometry.TwistMultTransport.bundle_mult_twistMap`: **Tag 01MY's
  multiplication identity with its leading Tag 01CD comparison cancelled**, which is the shape
  in which it is the naturality square of the third factor.
* `Stacks.AlgebraicGeometry.TwistMultTransport.pullbackTwistMultiplication_eq`: the pulled-back
  multiplication of Tag 01MY unfolded, so that its leading comparison can be cancelled without a
  conversion.

## Not done here

No `stacks` attribute is attached to any declaration in this file. The six factors are assembled
in `Stacks.AlgebraicGeometry.TwistMultCompat.transport_six`, and Tag 01NO's fourth assertion is
`Stacks.AlgebraicGeometry.TwistMultCompat.projInclusionTwistIso_preserves_products`.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjInvertibleLocus Stacks.AlgebraicGeometry.ProjMapCard
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjTwistTheta
open Stacks.AlgebraicGeometry.TwistTensor
open Stacks.AlgebraicGeometry.RelativeProj Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.ProjInclusionTwist
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.TwistMultTransport

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  TopCat.Presheaf.IsSheaf

universe u

/-! ### The transport, at the level of variables -/

section Steps

variable {C : Type*} [Category C]

/-- **The last factor of the transport**, where the factor's target at the tensor product is the
multiplication's own source and no further factor follows. -/
public theorem transport_last {A A' B B₂ E : C} {M : A ⟶ A'} {D : A ⟶ B} {a : A ⟶ B₂}
    {a' : A' ⟶ E} {T : B ⟶ B₂} {mult : B₂ ⟶ E} (hnat : M ≫ a' = a ≫ mult)
    (hcoh : D ≫ T = a) : M ≫ a' = D ≫ T ≫ mult := by
  rw [hnat, ← hcoh, Category.assoc]

/-- A composite with an inverse pair on the left. -/
public theorem comp_eq_of_id {A B E : C} {i : A ⟶ B} {d : B ⟶ A} {r : A ⟶ E}
    (hi : i ≫ d = 𝟙 A) : (i ≫ d) ≫ r = r := by
  rw [hi, Category.id_comp]

/-- The leading Tag 01CD comparison cancels against its inverse, which is the first factor of
the pulled-back multiplication. -/
public theorem transport_head {A A' B E : C} {i : A ⟶ A'} {d : A' ⟶ A} {M : A' ⟶ B}
    {th : B ⟶ E} {r : A ⟶ E} (hi : i ≫ d = 𝟙 A) (hM : M ≫ th = d ≫ r) :
    (i ≫ M) ≫ th = r := by
  rw [Category.assoc, hM, ← Category.assoc, comp_eq_of_id hi]

/-- **Tag 01MY's identity with its leading comparison cancelled**, at the level of variables. -/
public theorem transport_middle {A A' B B' E F : C} (c : A ⟶ A') (ci : A' ⟶ A)
    (MD : A ⟶ B) (th : B ⟶ B') (t : A' ⟶ E) (ei : E ⟶ F) (MI : F ⟶ B')
    (hc : c ≫ ci = 𝟙 A) (h01 : (ci ≫ MD) ≫ th = t ≫ ei ≫ MI) :
    MD ≫ th = (c ≫ t ≫ ei) ≫ MI := by
  rw [Category.assoc, Category.assoc, ← h01, Category.assoc, ← Category.assoc c ci,
    hc, Category.id_comp]

/-- **The coherence for a factor that is a functor image**, at the level of variables: the third
factor of Tag 01NO's comparison is the inverse image under the leading morphism of Tag 01MY's
twist map, and its coherence is naturality of the Tag 01CD comparison for that morphism. -/
public theorem transport_functor_coh {C' D' : Type*} [Category C'] [Category D'] (Fk : C' ⥤ D')
    {A A' E F : C'} {B B' : D'} (c : A ⟶ A') (t : A' ⟶ E) (ei : E ⟶ F) (eh : F ⟶ E)
    (pA : Fk.obj A' ⟶ B) (pE : Fk.obj E ⟶ B') (T : B ⟶ B')
    (hei : ei ≫ eh = 𝟙 E) (hnat : Fk.map t ≫ pE = pA ≫ T) :
    (Fk.map c ≫ pA) ≫ T = Fk.map (c ≫ t ≫ ei) ≫ Fk.map eh ≫ pE := by
  rw [← Category.assoc (Fk.map (c ≫ t ≫ ei)) (Fk.map eh) pE, ← Fk.map_comp,
    Category.assoc c, Category.assoc t, hei, Category.comp_id, Fk.map_comp,
    Category.assoc (Fk.map c), ← hnat, ← Category.assoc]

end Steps

section TensorSteps

variable {W : Scheme.{u}}

/-- **One factor of the transport, with the tensor product split.** A factor of Tag 01NO's
comparison is applied at three modules at once -- the two twists, where it contributes to the
tensor product of the comparisons, and the tensor product of the twists, where it mediates
between the two multiplications -- and this is the lemma that keeps those three uses in step.

The hypotheses are the factor's naturality square at the multiplication map, the factor's
monoidal coherence against the Tag 01CD comparisons, and the statement for the remaining
factors. -/
public theorem transport_tstep
    {P P' Pf Q Q' Qf R R' Rs Rs' E : W.Modules}
    {M : R ⟶ Rs} {D : R ⟶
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P).obj Q)} {a : R ⟶ R'}
    {a' : Rs ⟶ Rs'} {aP : P ⟶ P'} {aQ : Q ⟶ Q'} {M₂ : R' ⟶ Rs'}
    {D₂ : R' ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P').obj Q')} {r' :
      Rs' ⟶ E}
    {rP : P' ⟶ Pf} {rQ : Q' ⟶ Qf}
    {mult : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj Pf).obj Qf) ⟶ E}
    (hnat : M ≫ a' = a ≫ M₂)
    (hcoh : D ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map (X := (P, Q)) (Y := (P', Q'))
      ((aP, aQ) : (P, Q) ⟶ (P', Q'))) =
      a ≫ D₂)
    (ih : M₂ ≫ r' = D₂ ≫
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map (X := (P', Q')) (Y := (Pf, Qf))
      ((rP, rQ) : (P', Q') ⟶ (Pf, Qf))) ≫ mult) :
    M ≫ a' ≫ r' =
      D ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map (X := (P, Q)) (Y := (Pf, Qf))
        ((aP ≫ rP, aQ ≫ rQ) : (P, Q) ⟶ (Pf, Qf))) ≫ mult := by
  refine Eq.trans ?_ (congrArg (fun z => D ≫ z ≫ mult)
    (tensorSheafMap_comp W.toRingedSpace aP rP aQ rQ)).symm
  rw [← Category.assoc M, hnat, Category.assoc, ih]
  erw [← Category.assoc a, ← hcoh, Category.assoc, Category.assoc]

end TensorSteps

section Unfold

universe w

variable {R : Type u} {σ : Type w} [CommRing R] [SetLike σ R] [AddSubgroupClass σ R]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- The pulled-back multiplication of Tag 01MY, unfolded: the inverse Tag 01CD comparison
followed by the inverse image of the multiplication map of Tag 01MU. -/
public theorem pullbackTwistMultiplication_eq {W : Scheme.{u}}
    (p : W ⟶ AlgebraicGeometry.Proj 𝒮) (n m : ℤ) :
    pullbackTwistMultiplication 𝒮 p n m =
      (Stacks.PullbackTensorIso.pullbackTensorIso p.toLRSHom.toShHom).inv.app
          (twistingSheaf 𝒮 n, twistingSheaf 𝒮 m) ≫
        (Scheme.Modules.pullback p).map (twistMultiplicationMap 𝒮 n m) := rfl

end Unfold

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S) (U V : S.Opens) (h : U ≤ V)
  (hU : IsAffineOpen U) (hV : IsAffineOpen V)

/-! ### Tag 01MY's multiplication identity, read forwards -/

/-- **Tag 01MY's multiplication identity with the leading comparison cancelled.** The inverse
image of the multiplication map of Tag 01MU followed by the comparison on the `(n + m)`-th twist
is the tensor product of the comparisons on the two twists, conjugated by the Tag 01CD
comparisons for the two morphisms. This is
`Stacks.AlgebraicGeometry.ProjMapCard.projMapData_preserves_products` with its leading inverse
Tag 01CD comparison cancelled against the `hom`. -/
public theorem bundle_mult_twistMap (n m : ℤ) :
    (Scheme.Modules.pullback
          (projMapData (A.grading V) (A.grading U) (A.res h)).hom).map
          (twistMultiplicationMap (A.grading V) n m) ≫
        (projMapData (A.grading V) (A.grading U) (A.res h)).twistMap (n + m) =
      ((Stacks.PullbackTensorIso.pullbackTensorIso
              (projMapData (A.grading V) (A.grading U)
                (A.res h)).hom.toLRSHom.toShHom).hom.app
            (twistingSheaf (A.grading V) n, twistingSheaf (A.grading V) m) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨(((mapDomain (A.grading V) (A.grading U) (A.res h)).toScheme.toRingedSpace)).presheaf,
            (((mapDomain (A.grading V) (A.grading U)
            (A.res h)).toScheme.toRingedSpace)).IsSheaf⟩)).map
            ((((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap n),
            ((projMapData (A.grading V) (A.grading U) (A.res h)).twistMap m)) : (_, _) ⟶ (_, _))) ≫
            (Stacks.PullbackTensorIso.pullbackTensorIso
                (mapDomain (A.grading V) (A.grading U)
                  (A.res h)).ι.toLRSHom.toShHom).inv.app
              (twistingSheaf (A.grading U) n, twistingSheaf (A.grading U) m)) ≫
        (Scheme.Modules.pullback
          (mapDomain (A.grading V) (A.grading U) (A.res h)).ι).map
            (twistMultiplicationMap (A.grading U) n m) :=
  transport_middle _ _ _ _ _ _ _
    (Iso.hom_inv_id_app (Stacks.PullbackTensorIso.pullbackTensorIso
        (projMapData (A.grading V) (A.grading U) (A.res h)).hom.toLRSHom.toShHom)
      (twistingSheaf (A.grading V) n, twistingSheaf (A.grading V) m))
    (projMapData_preserves_products (A.grading V) (A.grading U) (A.res h) n m)

end Stacks.AlgebraicGeometry.TwistMultTransport

end
