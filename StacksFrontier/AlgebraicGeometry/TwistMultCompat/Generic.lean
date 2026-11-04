module

public import StacksFrontier.AlgebraicGeometry.TwistMultTransport.Basic

/-!
# The six-factor transport of a multiplication identity, one factor per declaration

Tag 01NO's comparison on the `n`-th twist is a composite of six factors. This file transports a
multiplication identity along those six factors at the level of variables: no `Proj`, no twisting
sheaf and no graded ring occurs, so the concrete statement is obtained by instantiation rather
than by conversion.

## Main results

* `Stacks.AlgebraicGeometry.TwistMultCompat.transport_step₁`: given a factorisation `k ≫ g = q`
  of a morphism of schemes, a retraction `k ≫ j = 𝟙` of a second morphism out of the middle
  scheme, and three comparison morphisms satisfying the multiplication identity for `g` and `j`,
  the composite of the six factors satisfies the multiplication identity for `q`.
* `Stacks.AlgebraicGeometry.TwistMultCompat.transport_six`: the same with the leading inverse
  Tag 01CD comparison in place, which is the shape of
  `Stacks.AlgebraicGeometry.ProjTwistTheta.pullbackTwistMultiplication`.
* `Stacks.AlgebraicGeometry.TwistMultCompat.transport_step₆` through `transport_step₂`: the
  factor-by-factor steps, each one factor longer than the last.
* `Stacks.AlgebraicGeometry.TwistMultCompat.comparison_tensorSheafMap_nat`: the Tag 01CD
  comparison is natural in its two module arguments.

## Implementation notes

* Every intermediate composite is written out in its own theorem, so that each step applies a
  lemma of `Stacks.AlgebraicGeometry.TwistMultTransport` and the kernel only compares two
  written-out composites of the same length.
* The congruence factors are taken whole, by `subst`
  (`Stacks.AlgebraicGeometry.TwistMultTransport.transport_congr_step` and
  `transport_congr_hom_step`): a component of `AlgebraicGeometry.Scheme.Modules.pullbackCongr` is
  an `eqToIso`, and reaching one by unification is an `isDefEq` timeout.
* The tensor maps are generalized before the abstract lemmas are applied in
  `transport_step₃_nat` and `transport_step₃_coh`, which keeps their implementations out of
  definitional unfolding.
* In `transport_step₂_nat` the module argument of the component of
  `AlgebraicGeometry.Scheme.Modules.pullbackComp` is spelled as the bifunctor's value on the pair,
  the same term as in `Stacks.AlgebraicGeometry.TwistMultTransport.comparison_pullbackComp`;
  converting between the two spellings is a `whnf` timeout.
* Step two is the two halves `transport_step₂_left` and `transport_step₂_right` glued by
  `Eq.trans`, with the middle term written out in both: a single application of
  `Stacks.AlgebraicGeometry.TwistMultTransport.transport_tstep` exceeds the heartbeat limit.
* In `transport_six` the three six-factor composites are type-ascribed. Without the ascription the
  target of each composite is `(𝟭 _).obj P'` rather than `P'`, which is definitionally equal but
  too expensive to convert at the concrete types of Tag 01NO.

## References

* [Stacks Project, Tag 01NO](https://stacks.math.columbia.edu/tag/01NO)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open Stacks.RingedSpace PresheafOfModules RingedSpaceModuleAdjunction
open Stacks.AlgebraicGeometry.TwistMultTransport
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.TwistMultCompat

attribute [local implicit_reducible] TopCat.Presheaf.IsSheaf

universe u

private theorem map_comp_eq_of_comp_eq {SourceCategory TargetCategory : Type*}
    [Category SourceCategory] [Category TargetCategory] (functor : SourceCategory ⥤ TargetCategory)
    {source leftMiddle rightMiddle target : SourceCategory}
    (leftFirst : source ⟶ leftMiddle) (leftSecond : leftMiddle ⟶ target)
    (rightFirst : source ⟶ rightMiddle) (rightSecond : rightMiddle ⟶ target)
    (hypothesis : leftFirst ≫ leftSecond = rightFirst ≫ rightSecond) :
    functor.map leftFirst ≫ functor.map leftSecond =
      functor.map rightFirst ≫ functor.map rightSecond := by
  rw [← functor.map_comp, hypothesis, functor.map_comp]

/-! ### The Tag 01CD comparison is natural in both module arguments -/

section Nat

variable {X Y : Scheme.{u}}

/-- **The Tag 01CD comparison is natural in its two module arguments.** This is
`Stacks.PullbackTensorIso.pullbackTensorIso` read as an isomorphism of bifunctors, with the
component of its `hom` at a pair of morphisms spelled as
`CategoryTheory.Functor.uncurry.obj.map`. -/
public theorem comparison_tensorSheafMap_nat (f : X ⟶ Y) {P P' Q Q' : Y.Modules}
    (a : P ⟶ P') (b : Q ⟶ Q') :
    (Scheme.Modules.pullback f).map
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).map (X := (P, Q)) (Y := (P', Q'))
      ((a, b) : (_, _) ⟶ (_, _)))) ≫
        (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (P', Q') =
      (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback f).obj P, (Scheme.Modules.pullback f).obj Q))
          (Y := ((Scheme.Modules.pullback f).obj P', (Scheme.Modules.pullback f).obj Q'))
          ((((Scheme.Modules.pullback f).map a), ((Scheme.Modules.pullback f).map b)) : (_, _) ⟶
          (_, _))) :=
  (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.naturality
    ((a, b) : ((P, Q) : _ × _) ⟶ (P', Q'))

/-- **The congruence factor of the transport, in the `hom` direction.** For `hf : f = g`, the
multiplication identity for `g` gives the one for `f` with the components of
`AlgebraicGeometry.Scheme.Modules.pullbackCongr hf` inserted. The `inv`-direction counterpart is
`Stacks.AlgebraicGeometry.TwistMultTransport.transport_congr_step`. -/
public theorem transport_congr_hom_step {f g : X ⟶ Y} (hf : f = g)
    {P Q R : Y.Modules} {Pf Qf E : X.Modules}
    (mult : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj P).obj Q) ⟶ R)
    (r' : (Scheme.Modules.pullback g).obj R ⟶ E)
    (rP : (Scheme.Modules.pullback g).obj P ⟶ Pf)
    (rQ : (Scheme.Modules.pullback g).obj Q ⟶ Qf)
    (multF : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj Pf).obj Qf) ⟶ E)
    (ih : (Scheme.Modules.pullback g).map mult ≫ r' =
      (Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
          (Y := (Pf, Qf)) ((rP, rQ) : (_, _) ⟶ (_, _))) ≫ multF) :
    (Scheme.Modules.pullback f).map mult ≫
        ((Scheme.Modules.pullbackCongr hf).hom.app R ≫ r') =
      (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback f).obj P, (Scheme.Modules.pullback f).obj Q))
          (Y := (Pf, Qf)) ((((Scheme.Modules.pullbackCongr hf).hom.app P ≫ rP),
          ((Scheme.Modules.pullbackCongr hf).hom.app Q ≫ rQ)) : (_, _) ⟶ (_, _))) ≫ multF := by
  subst hf
  refine Eq.trans (congrArg (fun z => (Scheme.Modules.pullback f).map mult ≫ z ≫ r')
    (pullbackCongr_rfl_hom_app f R)) ?_
  refine Eq.trans (congrArg (fun z => (Scheme.Modules.pullback f).map mult ≫ z)
    (Category.id_comp r')) ?_
  refine Eq.trans ih ?_
  refine congrArg (fun z =>
    (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app (P, Q) ≫
      z ≫ multF) ?_
  refine congrArg ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
    (X := ((Scheme.Modules.pullback f).obj P, (Scheme.Modules.pullback f).obj Q))
    (Y := (Pf, Qf))) (Prod.ext ?_ ?_)
  all_goals exact (Category.id_comp _).symm

end Nat

/-! ### The six steps

Each step adds one factor on the left of the comparison and the corresponding factor inside the
tensor product on the right. Nothing below mentions `Proj`. -/

section Steps

variable {W X Y : Scheme.{u}} (k : W ⟶ X) (g : X ⟶ Y) (j : X ⟶ W)

/-- **Step six: the pullback along the identity.** -/
public theorem transport_step₆ {P' Q' R' : W.Modules}
    (multW : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P').obj Q') ⟶ R') :
    (Scheme.Modules.pullback (𝟙 W)).map multW ≫
        (Scheme.Modules.pullbackId W).hom.app R' =
      (Stacks.PullbackTensorIso.pullbackTensorIso
          (𝟙 W : W ⟶ W).toLRSHom.toShHom).hom.app (P', Q') ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback (𝟙 W)).obj P', (Scheme.Modules.pullback (𝟙 W)).obj Q'))
          (Y := (P', Q')) ((((Scheme.Modules.pullbackId W).hom.app P'),
          ((Scheme.Modules.pullbackId W).hom.app Q')) : (_, _) ⟶ (_, _))) ≫ multW :=
  transport_last ((Scheme.Modules.pullbackId W).hom.naturality multW)
    (comparison_pullbackId W P' Q')

/-- **Step five: the congruence isomorphism for the retraction.** -/
public theorem transport_step₅ (hk : k ≫ j = 𝟙 W) {P' Q' R' : W.Modules}
    (multW : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P').obj Q') ⟶ R') :
    (Scheme.Modules.pullback (k ≫ j)).map multW ≫
        ((Scheme.Modules.pullbackCongr hk).hom.app R' ≫
          (Scheme.Modules.pullbackId W).hom.app R') =
      (Stacks.PullbackTensorIso.pullbackTensorIso (k ≫ j).toLRSHom.toShHom).hom.app (P', Q') ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback (k ≫ j)).obj P', (Scheme.Modules.pullback (k ≫ j)).obj
          Q')) (Y := (P', Q')) ((((Scheme.Modules.pullbackCongr hk).hom.app P' ≫
              (Scheme.Modules.pullbackId W).hom.app P'), ((Scheme.Modules.pullbackCongr hk).hom.app
                Q' ≫
              (Scheme.Modules.pullbackId W).hom.app Q')) : (_, _) ⟶ (_, _))) ≫ multW :=
  transport_congr_hom_step hk multW _ _ _ multW (transport_step₆ multW)

/-- **Step four: the pseudofunctoriality isomorphism for the retraction's factorisation.** -/
public theorem transport_step₄ (hk : k ≫ j = 𝟙 W) {P' Q' R' : W.Modules}
    (multW : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P').obj Q') ⟶ R') :
    (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback j).map multW) ≫
        ((Scheme.Modules.pullbackComp k j).hom.app R' ≫
          (Scheme.Modules.pullbackCongr hk).hom.app R' ≫
          (Scheme.Modules.pullbackId W).hom.app R') =
      ((Scheme.Modules.pullback k).map
            ((Stacks.PullbackTensorIso.pullbackTensorIso
              j.toLRSHom.toShHom).hom.app (P', Q')) ≫
          (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app
            ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q')) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback j).obj P'),
          (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback j).obj Q'))) (Y := (P', Q'))
          ((((Scheme.Modules.pullbackComp k j).hom.app P' ≫
              (Scheme.Modules.pullbackCongr hk).hom.app P' ≫
              (Scheme.Modules.pullbackId W).hom.app P'), ((Scheme.Modules.pullbackComp k j).hom.app
                Q' ≫
              (Scheme.Modules.pullbackCongr hk).hom.app Q' ≫
              (Scheme.Modules.pullbackId W).hom.app Q')) : (_, _) ⟶ (_, _))) ≫ multW :=
  transport_tstep ((Scheme.Modules.pullbackComp k j).hom.naturality multW)
    (comparison_pullbackComp_hom k j P' Q') (transport_step₅ k j hk multW)

/-- **The naturality square of the third factor**: the multiplication identity for `g` and `j`,
carried under the inverse image along `k`. -/
public theorem transport_step₃_nat {P Q R : Y.Modules} {P' Q' R' : W.Modules}
    (multY : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj P).obj Q) ⟶ R)
    (multW : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P').obj Q') ⟶ R')
    (θP : (Scheme.Modules.pullback g).obj P ⟶ (Scheme.Modules.pullback j).obj P')
    (θQ : (Scheme.Modules.pullback g).obj Q ⟶ (Scheme.Modules.pullback j).obj Q')
    (θR : (Scheme.Modules.pullback g).obj R ⟶ (Scheme.Modules.pullback j).obj R')
    (hb : (Scheme.Modules.pullback g).map multY ≫ θR =
      ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
            (Y := ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q'))
            ((θP, θQ) : (_, _) ⟶ (_, _))) ≫
            (Stacks.PullbackTensorIso.pullbackTensorIso
              j.toLRSHom.toShHom).inv.app (P', Q')) ≫
        (Scheme.Modules.pullback j).map multW) :
    (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback g).map multY) ≫
        (Scheme.Modules.pullback k).map θR =
      (Scheme.Modules.pullback k).map
        (X := (Scheme.Modules.pullback g).obj
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj (P, Q)))
        (Y := (Scheme.Modules.pullback j).obj
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).obj (P', Q')))
          ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
              (X := ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
              (Y := ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q'))
              ((θP, θQ) : (_, _) ⟶ (_, _))) ≫
              (Stacks.PullbackTensorIso.pullbackTensorIso
                j.toLRSHom.toShHom).inv.app (P', Q')) ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback j).map multW) := by
  generalize (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
    (X := ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
    (Y := ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q'))
    ((θP, θQ) : (_, _) ⟶ (_, _)))) = comparisonMap at hb ⊢
  exact map_comp_eq_of_comp_eq (Scheme.Modules.pullback k)
    ((Scheme.Modules.pullback g).map multY) θR
    ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
      comparisonMap ≫
        (Stacks.PullbackTensorIso.pullbackTensorIso j.toLRSHom.toShHom).inv.app (P', Q'))
    ((Scheme.Modules.pullback j).map multW) hb

private theorem transport_step₃_coh_aux {P Q : Y.Modules} {P' Q' : W.Modules}
    (comparisonMap : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj
        ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)) ⟶
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).obj
        ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q')))
    (mappedComparison : ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).obj
        ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj P),
        (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj Q))) ⟶
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).obj
        ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback j).obj P'),
        (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback j).obj Q'))))
    (naturality : (Scheme.Modules.pullback k).map comparisonMap ≫
        (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app
          ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q') =
      (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app
        ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q) ≫ mappedComparison) :
    ((Scheme.Modules.pullback k).map
      ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q)) ≫
        (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app
          ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)) ≫
          mappedComparison =
      (Scheme.Modules.pullback k).map
          ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
            comparisonMap ≫ (Stacks.PullbackTensorIso.pullbackTensorIso j.toLRSHom.toShHom).inv.app
            (P', Q')) ≫
        (Scheme.Modules.pullback k).map
          ((Stacks.PullbackTensorIso.pullbackTensorIso j.toLRSHom.toShHom).hom.app (P', Q')) ≫
          (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app
            ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q') :=
  transport_functor_coh (Scheme.Modules.pullback k)
    ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q)) comparisonMap
      ((Stacks.PullbackTensorIso.pullbackTensorIso j.toLRSHom.toShHom).inv.app (P', Q'))
      ((Stacks.PullbackTensorIso.pullbackTensorIso j.toLRSHom.toShHom).hom.app (P', Q'))
    ((Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app
      ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
      ((Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app
      ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q')) mappedComparison
    (Iso.inv_hom_id_app (Stacks.PullbackTensorIso.pullbackTensorIso j.toLRSHom.toShHom)
      (P', Q')) naturality

/-- **The monoidal coherence of the third factor**: the inverse image along `k` of the tensor
product of `θP` and `θQ`, against the Tag 01CD comparisons for `g`, `k` and `j`. -/
public theorem transport_step₃_coh {P Q : Y.Modules} {P' Q' : W.Modules}
    (θP : (Scheme.Modules.pullback g).obj P ⟶ (Scheme.Modules.pullback j).obj P')
    (θQ : (Scheme.Modules.pullback g).obj Q ⟶ (Scheme.Modules.pullback j).obj Q') :
    ((Scheme.Modules.pullback k).map
            ((Stacks.PullbackTensorIso.pullbackTensorIso
              g.toLRSHom.toShHom).hom.app (P, Q)) ≫
          (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app
            ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj P),
          (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj Q)))
          (Y := ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback j).obj P'),
          (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback j).obj Q')))
          ((((Scheme.Modules.pullback k).map θP), ((Scheme.Modules.pullback k).map θQ)) : (_, _) ⟶
          (_, _))) =
      (Scheme.Modules.pullback k).map
        (X := (Scheme.Modules.pullback g).obj
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩)).obj (P, Q)))
        (Y := (Scheme.Modules.pullback j).obj
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).obj (P', Q')))
          ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
              (X := ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
              (Y := ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q'))
              ((θP, θQ) : (_, _) ⟶ (_, _))) ≫
              (Stacks.PullbackTensorIso.pullbackTensorIso
                j.toLRSHom.toShHom).inv.app (P', Q')) ≫
        (Scheme.Modules.pullback k).map
            ((Stacks.PullbackTensorIso.pullbackTensorIso
              j.toLRSHom.toShHom).hom.app (P', Q')) ≫
          (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app
            ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q') := by
  have naturality := comparison_tensorSheafMap_nat k θP θQ
  generalize (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
    (X := ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
    (Y := ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q'))
    ((θP, θQ) : (_, _) ⟶ (_, _)))) = comparisonMap at naturality ⊢
  generalize (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
    (X := ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj P),
    (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj Q)))
    (Y := ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback j).obj P'),
    (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback j).obj Q')))
    ((((Scheme.Modules.pullback k).map θP), ((Scheme.Modules.pullback k).map θQ)) : (_, _) ⟶
    (_, _)))) = mappedComparison at naturality ⊢
  exact transport_step₃_coh_aux k g j (P := P) (Q := Q) (P' := P') (Q' := Q')
    comparisonMap mappedComparison naturality

/-- **Step three: the functor image of the comparison family.** -/
public theorem transport_step₃ (hk : k ≫ j = 𝟙 W) {P Q R : Y.Modules} {P' Q' R' : W.Modules}
    (multY : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj P).obj Q) ⟶ R)
    (multW : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P').obj Q') ⟶ R')
    (θP : (Scheme.Modules.pullback g).obj P ⟶ (Scheme.Modules.pullback j).obj P')
    (θQ : (Scheme.Modules.pullback g).obj Q ⟶ (Scheme.Modules.pullback j).obj Q')
    (θR : (Scheme.Modules.pullback g).obj R ⟶ (Scheme.Modules.pullback j).obj R')
    (hb : (Scheme.Modules.pullback g).map multY ≫ θR =
      ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
            (Y := ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q'))
            ((θP, θQ) : (_, _) ⟶ (_, _))) ≫
            (Stacks.PullbackTensorIso.pullbackTensorIso
              j.toLRSHom.toShHom).inv.app (P', Q')) ≫
        (Scheme.Modules.pullback j).map multW) :
    (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback g).map multY) ≫
        ((Scheme.Modules.pullback k).map θR ≫
          (Scheme.Modules.pullbackComp k j).hom.app R' ≫
          (Scheme.Modules.pullbackCongr hk).hom.app R' ≫
          (Scheme.Modules.pullbackId W).hom.app R') =
      ((Scheme.Modules.pullback k).map
            ((Stacks.PullbackTensorIso.pullbackTensorIso
              g.toLRSHom.toShHom).hom.app (P, Q)) ≫
          (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app
            ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj P),
          (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj Q))) (Y := (P', Q'))
          ((((Scheme.Modules.pullback k).map θP ≫
              (Scheme.Modules.pullbackComp k j).hom.app P' ≫
              (Scheme.Modules.pullbackCongr hk).hom.app P' ≫
              (Scheme.Modules.pullbackId W).hom.app P'), ((Scheme.Modules.pullback k).map θQ ≫
              (Scheme.Modules.pullbackComp k j).hom.app Q' ≫
              (Scheme.Modules.pullbackCongr hk).hom.app Q' ≫
              (Scheme.Modules.pullbackId W).hom.app Q')) : (_, _) ⟶ (_, _))) ≫ multW :=
  transport_tstep
    (transport_step₃_nat k g j multY multW θP θQ θR hb)
    (transport_step₃_coh k g j θP θQ)
    (transport_step₄ k j hk multW)

/-- **The naturality square of the second factor**: naturality of the inverse of the
pseudofunctoriality isomorphism for `k ≫ g` at the multiplication map on `Y`, with the module
argument of the component spelled as the bifunctor's value on the pair. -/
public theorem transport_step₂_nat {P Q R : Y.Modules}
    (multY : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj P).obj Q) ⟶ R) :
    (Scheme.Modules.pullback (k ≫ g)).map multY ≫
        (Scheme.Modules.pullbackComp k g).inv.app R =
      (Scheme.Modules.pullbackComp k g).inv.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩))).obj (P, Q)) ≫
        (Scheme.Modules.pullback k).map ((Scheme.Modules.pullback g).map multY) :=
  (Scheme.Modules.pullbackComp k g).inv.naturality multY

/-- **The left half of one transport factor**, at the level of variables: the naturality square
followed by the statement for the remaining factors, the latter's right-hand side left as a
single morphism `u`. -/
private theorem transport_tstep_left {C : Type*} [Category C] {R R' Rs Rs' E : C}
    {M : R ⟶ Rs} {a : R ⟶ R'} {a' : Rs ⟶ Rs'} {M₂ : R' ⟶ Rs'} {r' : Rs' ⟶ E} {u : R' ⟶ E}
    (hnat : M ≫ a' = a ≫ M₂) (ih : M₂ ≫ r' = u) :
    M ≫ a' ≫ r' = a ≫ u :=
  ((Category.assoc M a' r').symm.trans (congrArg (fun z => z ≫ r') hnat)).trans
    ((Category.assoc a M₂ r').trans (congrArg (fun z => a ≫ z) ih))

/-- **The right half of one transport factor**, at the level of variables: the factor's monoidal
coherence against the Tag 01CD comparisons, absorbed into the tensor product of the
comparisons. -/
private theorem transport_tstep_right {P P' Pf Q Q' Qf R R' E : W.Modules}
    {D : R ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P).obj Q)}
    {a : R ⟶ R'} {aP : P ⟶ P'} {aQ : Q ⟶ Q'}
    {D₂ : R' ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P').obj Q')}
    {rP : P' ⟶ Pf} {rQ : Q' ⟶ Qf}
    {mult : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj Pf).obj Qf) ⟶ E}
    (hcoh :
      D ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map (X := (P, Q)) (Y := (P', Q'))
        ((aP, aQ) : (P, Q) ⟶ (P', Q'))) =
        a ≫ D₂) :
    a ≫ D₂ ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map (X := (P', Q')) (Y := (Pf, Qf))
          ((rP, rQ) : (P', Q') ⟶ (Pf, Qf))) ≫
          mult =
      D ≫ ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map (X := (P, Q)) (Y := (Pf, Qf))
        ((aP ≫ rP, aQ ≫ rQ) : (P, Q) ⟶ (Pf, Qf))) ≫ mult :=
  Eq.symm
    ((congrArg (fun z => D ≫ z ≫ mult)
          (tensorSheafMap_comp W.toRingedSpace aP rP aQ rQ)).trans
      ((congrArg (fun z => D ≫ z) (Category.assoc _ _ _)).trans
        ((Category.assoc D
              (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map (X := (P, Q))
                (Y := (P', Q')) ((aP, aQ) : (P, Q) ⟶ (P', Q'))))
              _).symm.trans
          ((congrArg (fun z => z ≫
                ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
                  ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map (X := (P', Q'))
                  (Y := (Pf, Qf)) ((rP, rQ) : (P', Q') ⟶ (Pf, Qf))) ≫ mult) hcoh).trans
            (Category.assoc a D₂ _)))))

/-- **Step two, left half**: the naturality square of the pseudofunctoriality isomorphism,
followed by step three. Its right-hand side is the inverse pseudofunctoriality component at the
bifunctor's value on the pair, followed by the right-hand side of step three. -/
private theorem transport_step₂_left (hk : k ≫ j = 𝟙 W) {P Q R : Y.Modules}
    {P' Q' R' : W.Modules}
    (multY : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj P).obj Q) ⟶ R)
    (multW : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P').obj Q') ⟶ R')
    (θP : (Scheme.Modules.pullback g).obj P ⟶ (Scheme.Modules.pullback j).obj P')
    (θQ : (Scheme.Modules.pullback g).obj Q ⟶ (Scheme.Modules.pullback j).obj Q')
    (θR : (Scheme.Modules.pullback g).obj R ⟶ (Scheme.Modules.pullback j).obj R')
    (hb : (Scheme.Modules.pullback g).map multY ≫ θR =
      ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
            (Y := ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q'))
            ((θP, θQ) : (_, _) ⟶ (_, _))) ≫
            (Stacks.PullbackTensorIso.pullbackTensorIso
              j.toLRSHom.toShHom).inv.app (P', Q')) ≫
        (Scheme.Modules.pullback j).map multW) :
    (Scheme.Modules.pullback (k ≫ g)).map multY ≫
        ((Scheme.Modules.pullbackComp k g).inv.app R ≫
          (Scheme.Modules.pullback k).map θR ≫
          (Scheme.Modules.pullbackComp k j).hom.app R' ≫
          (Scheme.Modules.pullbackCongr hk).hom.app R' ≫
          (Scheme.Modules.pullbackId W).hom.app R') =
      (Scheme.Modules.pullbackComp k g).inv.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩))).obj (P, Q)) ≫
        ((Scheme.Modules.pullback k).map
              ((Stacks.PullbackTensorIso.pullbackTensorIso
                g.toLRSHom.toShHom).hom.app (P, Q)) ≫
            (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app
              ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj P),
            (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj Q))) (Y := (P', Q'))
            ((((Scheme.Modules.pullback k).map θP ≫
                (Scheme.Modules.pullbackComp k j).hom.app P' ≫
                (Scheme.Modules.pullbackCongr hk).hom.app P' ≫
                (Scheme.Modules.pullbackId W).hom.app P'), ((Scheme.Modules.pullback k).map θQ ≫
                (Scheme.Modules.pullbackComp k j).hom.app Q' ≫
                (Scheme.Modules.pullbackCongr hk).hom.app Q' ≫
                (Scheme.Modules.pullbackId W).hom.app Q')) : (_, _) ⟶ (_, _))) ≫ multW :=
  transport_tstep_left (transport_step₂_nat k g multY)
    (transport_step₃ k g j hk multY multW θP θQ θR hb)

/-- **Step two, right half**: the monoidal coherence of the pseudofunctoriality isomorphism for a
composite, absorbed into the tensor product of the comparisons. Its left-hand side is the
right-hand side of `transport_step₂_left`. -/
private theorem transport_step₂_right (hk : k ≫ j = 𝟙 W) {P Q : Y.Modules}
    {P' Q' R' : W.Modules}
    (multW : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P').obj Q') ⟶ R')
    (θP : (Scheme.Modules.pullback g).obj P ⟶ (Scheme.Modules.pullback j).obj P')
    (θQ : (Scheme.Modules.pullback g).obj Q ⟶ (Scheme.Modules.pullback j).obj Q') :
    (Scheme.Modules.pullbackComp k g).inv.app
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩))).obj (P, Q)) ≫
        ((Scheme.Modules.pullback k).map
              ((Stacks.PullbackTensorIso.pullbackTensorIso
                g.toLRSHom.toShHom).hom.app (P, Q)) ≫
            (Stacks.PullbackTensorIso.pullbackTensorIso k.toLRSHom.toShHom).hom.app
              ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q)) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj P),
            (Scheme.Modules.pullback k).obj ((Scheme.Modules.pullback g).obj Q))) (Y := (P', Q'))
            ((((Scheme.Modules.pullback k).map θP ≫
                (Scheme.Modules.pullbackComp k j).hom.app P' ≫
                (Scheme.Modules.pullbackCongr hk).hom.app P' ≫
                (Scheme.Modules.pullbackId W).hom.app P'), ((Scheme.Modules.pullback k).map θQ ≫
                (Scheme.Modules.pullbackComp k j).hom.app Q' ≫
                (Scheme.Modules.pullbackCongr hk).hom.app Q' ≫
                (Scheme.Modules.pullbackId W).hom.app Q')) : (_, _) ⟶ (_, _))) ≫ multW =
      (Stacks.PullbackTensorIso.pullbackTensorIso (k ≫ g).toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback (k ≫ g)).obj P, (Scheme.Modules.pullback (k ≫ g)).obj Q))
          (Y := (P', Q')) ((((Scheme.Modules.pullbackComp k g).inv.app P ≫
              (Scheme.Modules.pullback k).map θP ≫
              (Scheme.Modules.pullbackComp k j).hom.app P' ≫
              (Scheme.Modules.pullbackCongr hk).hom.app P' ≫
              (Scheme.Modules.pullbackId W).hom.app P'), ((Scheme.Modules.pullbackComp k g).inv.app
                Q ≫
              (Scheme.Modules.pullback k).map θQ ≫
              (Scheme.Modules.pullbackComp k j).hom.app Q' ≫
              (Scheme.Modules.pullbackCongr hk).hom.app Q' ≫
              (Scheme.Modules.pullbackId W).hom.app Q')) : (_, _) ⟶ (_, _))) ≫ multW :=
  transport_tstep_right (comparison_pullbackComp k g P Q)

/-- **Step two: the pseudofunctoriality isomorphism for the factorisation of the morphism.** -/
public theorem transport_step₂ (hk : k ≫ j = 𝟙 W) {P Q R : Y.Modules} {P' Q' R' : W.Modules}
    (multY : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj P).obj Q) ⟶ R)
    (multW : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P').obj Q') ⟶ R')
    (θP : (Scheme.Modules.pullback g).obj P ⟶ (Scheme.Modules.pullback j).obj P')
    (θQ : (Scheme.Modules.pullback g).obj Q ⟶ (Scheme.Modules.pullback j).obj Q')
    (θR : (Scheme.Modules.pullback g).obj R ⟶ (Scheme.Modules.pullback j).obj R')
    (hb : (Scheme.Modules.pullback g).map multY ≫ θR =
      ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
            (Y := ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q'))
            ((θP, θQ) : (_, _) ⟶ (_, _))) ≫
            (Stacks.PullbackTensorIso.pullbackTensorIso
              j.toLRSHom.toShHom).inv.app (P', Q')) ≫
        (Scheme.Modules.pullback j).map multW) :
    (Scheme.Modules.pullback (k ≫ g)).map multY ≫
        ((Scheme.Modules.pullbackComp k g).inv.app R ≫
          (Scheme.Modules.pullback k).map θR ≫
          (Scheme.Modules.pullbackComp k j).hom.app R' ≫
          (Scheme.Modules.pullbackCongr hk).hom.app R' ≫
          (Scheme.Modules.pullbackId W).hom.app R') =
      (Stacks.PullbackTensorIso.pullbackTensorIso (k ≫ g).toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback (k ≫ g)).obj P, (Scheme.Modules.pullback (k ≫ g)).obj Q))
          (Y := (P', Q')) ((((Scheme.Modules.pullbackComp k g).inv.app P ≫
              (Scheme.Modules.pullback k).map θP ≫
              (Scheme.Modules.pullbackComp k j).hom.app P' ≫
              (Scheme.Modules.pullbackCongr hk).hom.app P' ≫
              (Scheme.Modules.pullbackId W).hom.app P'), ((Scheme.Modules.pullbackComp k g).inv.app
                Q ≫
              (Scheme.Modules.pullback k).map θQ ≫
              (Scheme.Modules.pullbackComp k j).hom.app Q' ≫
              (Scheme.Modules.pullbackCongr hk).hom.app Q' ≫
              (Scheme.Modules.pullbackId W).hom.app Q')) : (_, _) ⟶ (_, _))) ≫ multW :=
  (transport_step₂_left k g j hk multY multW θP θQ θR hb).trans
    (transport_step₂_right k g j hk multW θP θQ)

/-- **Step one: the reassociation of the morphism, as a congruence isomorphism.** -/
public theorem transport_step₁ {q : W ⟶ Y} (hk : k ≫ j = 𝟙 W) (e : k ≫ g = q)
    {P Q R : Y.Modules} {P' Q' R' : W.Modules}
    (multY : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj P).obj Q) ⟶ R)
    (multW : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P').obj Q') ⟶ R')
    (θP : (Scheme.Modules.pullback g).obj P ⟶ (Scheme.Modules.pullback j).obj P')
    (θQ : (Scheme.Modules.pullback g).obj Q ⟶ (Scheme.Modules.pullback j).obj Q')
    (θR : (Scheme.Modules.pullback g).obj R ⟶ (Scheme.Modules.pullback j).obj R')
    (hb : (Scheme.Modules.pullback g).map multY ≫ θR =
      ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
            (Y := ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q'))
            ((θP, θQ) : (_, _) ⟶ (_, _))) ≫
            (Stacks.PullbackTensorIso.pullbackTensorIso
              j.toLRSHom.toShHom).inv.app (P', Q')) ≫
        (Scheme.Modules.pullback j).map multW) :
    (Scheme.Modules.pullback q).map multY ≫
        ((Scheme.Modules.pullbackCongr e).inv.app R ≫
          (Scheme.Modules.pullbackComp k g).inv.app R ≫
          (Scheme.Modules.pullback k).map θR ≫
          (Scheme.Modules.pullbackComp k j).hom.app R' ≫
          (Scheme.Modules.pullbackCongr hk).hom.app R' ≫
          (Scheme.Modules.pullbackId W).hom.app R') =
      (Stacks.PullbackTensorIso.pullbackTensorIso q.toLRSHom.toShHom).hom.app (P, Q) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback q).obj P, (Scheme.Modules.pullback q).obj Q))
          (Y := (P', Q')) ((((Scheme.Modules.pullbackCongr e).inv.app P ≫
              (Scheme.Modules.pullbackComp k g).inv.app P ≫
              (Scheme.Modules.pullback k).map θP ≫
              (Scheme.Modules.pullbackComp k j).hom.app P' ≫
              (Scheme.Modules.pullbackCongr hk).hom.app P' ≫
              (Scheme.Modules.pullbackId W).hom.app P'), ((Scheme.Modules.pullbackCongr e).inv.app
                Q ≫
              (Scheme.Modules.pullbackComp k g).inv.app Q ≫
              (Scheme.Modules.pullback k).map θQ ≫
              (Scheme.Modules.pullbackComp k j).hom.app Q' ≫
              (Scheme.Modules.pullbackCongr hk).hom.app Q' ≫
              (Scheme.Modules.pullbackId W).hom.app Q')) : (_, _) ⟶ (_, _))) ≫ multW :=
  transport_congr_step e multY _ _ _ multW
    (transport_step₂ k g j hk multY multW θP θQ θR hb)

/-- **The transport, with the leading inverse Tag 01CD comparison in place.** The pulled-back
multiplication along `q` — the inverse Tag 01CD comparison followed by the inverse image of
`multY` — followed by the six-factor composite at `R` equals the tensor product of the
six-factor composites at `P` and `Q` followed by `multW`. -/
public theorem transport_six {q : W ⟶ Y} (hk : k ≫ j = 𝟙 W) (e : k ≫ g = q)
    {P Q R : Y.Modules} {P' Q' R' : W.Modules}
    (multY : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj P).obj Q) ⟶ R)
    (multW : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj P').obj Q') ⟶ R')
    (θP : (Scheme.Modules.pullback g).obj P ⟶ (Scheme.Modules.pullback j).obj P')
    (θQ : (Scheme.Modules.pullback g).obj Q ⟶ (Scheme.Modules.pullback j).obj Q')
    (θR : (Scheme.Modules.pullback g).obj R ⟶ (Scheme.Modules.pullback j).obj R')
    (hb : (Scheme.Modules.pullback g).map multY ≫ θR =
      ((Stacks.PullbackTensorIso.pullbackTensorIso g.toLRSHom.toShHom).hom.app (P, Q) ≫
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
            (Y := ((Scheme.Modules.pullback j).obj P', (Scheme.Modules.pullback j).obj Q'))
            ((θP, θQ) : (_, _) ⟶ (_, _))) ≫
            (Stacks.PullbackTensorIso.pullbackTensorIso
              j.toLRSHom.toShHom).inv.app (P', Q')) ≫
        (Scheme.Modules.pullback j).map multW) :
    ((Stacks.PullbackTensorIso.pullbackTensorIso q.toLRSHom.toShHom).inv.app (P, Q) ≫
          (Scheme.Modules.pullback q).map multY) ≫
        (((Scheme.Modules.pullbackCongr e).inv.app R ≫
          (Scheme.Modules.pullbackComp k g).inv.app R ≫
          (Scheme.Modules.pullback k).map θR ≫
          (Scheme.Modules.pullbackComp k j).hom.app R' ≫
          (Scheme.Modules.pullbackCongr hk).hom.app R' ≫
          (Scheme.Modules.pullbackId W).hom.app R' :
            (Scheme.Modules.pullback q).obj R ⟶ R')) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        (X := ((Scheme.Modules.pullback q).obj P, (Scheme.Modules.pullback q).obj Q))
        (Y := (P', Q')) (((((Scheme.Modules.pullbackCongr e).inv.app P ≫
            (Scheme.Modules.pullbackComp k g).inv.app P ≫
            (Scheme.Modules.pullback k).map θP ≫
            (Scheme.Modules.pullbackComp k j).hom.app P' ≫
            (Scheme.Modules.pullbackCongr hk).hom.app P' ≫
            (Scheme.Modules.pullbackId W).hom.app P' :
              (Scheme.Modules.pullback q).obj P ⟶ P')),
                (((Scheme.Modules.pullbackCongr e).inv.app Q ≫
            (Scheme.Modules.pullbackComp k g).inv.app Q ≫
            (Scheme.Modules.pullback k).map θQ ≫
            (Scheme.Modules.pullbackComp k j).hom.app Q' ≫
            (Scheme.Modules.pullbackCongr hk).hom.app Q' ≫
            (Scheme.Modules.pullbackId W).hom.app Q' :
              (Scheme.Modules.pullback q).obj Q ⟶ Q'))) : (_, _) ⟶ (_, _))) ≫ multW :=
  transport_head
    (Iso.inv_hom_id_app
      (Stacks.PullbackTensorIso.pullbackTensorIso q.toLRSHom.toShHom) (P, Q))
    (transport_step₁ k g j hk e multY multW θP θQ θR hb)

end Steps

end Stacks.AlgebraicGeometry.TwistMultCompat

end
