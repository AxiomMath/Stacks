module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamentalGroup

/-!
# Functoriality of the étale fundamental group

Let `f : X ⟶ Y` be a morphism of connected schemes and let `x` be a geometric point of `X`,
with image `x.map f` in `Y`. Base change along `f` is a functor `FÉt_Y ⥤ FÉt_X`, and for a
finite étale cover `V ⟶ Y` a lift of `x` to `V ×_Y X` projects to a lift of `x.map f` to `V`.
These projections are bijections, natural in `V`, so they assemble into an isomorphism of fibre
functors `(- ×_Y X) ⋙ F_x ≅ F_{f ∘ x}`. Conjugating the action of `π₁(X, x)` on the left-hand
functor through that isomorphism produces the induced map `π₁(X, x) ⟶ π₁(Y, f ∘ x)`, which is
continuous because the topology on either side is induced by evaluation on covers.

## Main definitions

* `Stacks.FundamentalGroup.continuous_componentEmbedding_apply` and
  `Stacks.FundamentalGroup.continuous_of_continuous_component` — the two halves of the universal
  property of the topology on `Aut F`: evaluating a natural automorphism at a point of a value
  of `F` is continuous, and a map into `Aut G` is continuous as soon as every such evaluation of
  it is.
* `AlgebraicGeometry.finiteEtaleFiberProjection` — the projection from the fibre of a
  base-changed finite étale cover to the fibre of the original cover.
* `AlgebraicGeometry.finiteEtaleFiberProjectionEquiv` — that projection as a bijection.
* `AlgebraicGeometry.finiteEtaleFiberProjectionIso` — the resulting isomorphism of fibre
  functors.
* `AlgebraicGeometry.etaleFundamentalGroupMap` — the continuous homomorphism of étale
  fundamental groups induced by a morphism of connected schemes.

## Main results

* `AlgebraicGeometry.etaleFundamentalGroupMap_finiteEtaleFiberProjection` — the induced
  homomorphism commutes with the fibre projections; since the projections are bijective this
  equation determines it.

## Implementation notes

The fundamental group is `AlgebraicGeometry.EtaleFundamentalGroup`, so the induced map is
`etaleFundamentalGroupMap`; the shorter `fundamentalGroupMap` is avoided for the same reason
that `EtaleFundamentalGroup` is not called `FundamentalGroup`, namely Mathlib's
root-namespace topological fundamental group.

Base change is `AlgebraicGeometry.finiteEtaleBaseChange`, which uses the *chosen* pullback, so
the fibre at `x` of the base change of `V ⟶ Y` is literally the set of morphisms
`x.source ⟶ V ×_Y X` over `X`, and the inverse of the projection is `pullback.lift`. The chosen
pullback of a finite étale cover is only definitionally the pullback, not syntactically, so the
proofs here are written in term mode (`congrArg` and `calc`) where a rewrite would have to see
through that.

The topologies on `Aut F` of `Stacks.FundamentalGroup.functorAutomorphismTopology` are
definitions rather than instances, so the two continuity lemmas are stated `@`-applied, with the
discrete topology on the values of `F` written out as `⊥`.

## References

* [Stacks Project, Tag 0BND](https://stacks.math.columbia.edu/tag/0BND)
* [Stacks Project, Tag 0BQA](https://stacks.math.columbia.edu/tag/0BQA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w u' v'

namespace Stacks.FundamentalGroup

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-- Evaluating a natural automorphism of a set-valued functor at a fixed element of a fixed
value is continuous for the topology of `Stacks.FundamentalGroup.functorAutomorphismTopology`,
the value carrying the discrete topology. -/
theorem continuous_componentEmbedding_apply (F : C ⥤ Type w) (Z : C) (a : F.obj Z) :
    @Continuous (Aut F) (F.obj Z) (functorAutomorphismTopology F) ⊥
      (fun σ ↦ (σ.app Z).hom a) := by
  let _tF (W : C) : TopologicalSpace (F.obj W) := ⊥
  let _dF (W : C) : DiscreteTopology (F.obj W) := ⟨rfl⟩
  let _tP (W : C) : TopologicalSpace (Equiv.Perm (F.obj W)) := autTopology
  let _tA : TopologicalSpace (Aut F) :=
    TopologicalSpace.induced (componentEmbedding F) inferInstance
  have hcomp : Continuous (componentEmbedding F) := continuous_induced_dom
  have heval : Continuous (fun σ : Aut F ↦ (σ.app Z).toEquiv) :=
    (continuous_apply Z).comp hcomp
  have hfun : Continuous (fun e : Equiv.Perm (F.obj Z) ↦ (e : F.obj Z → F.obj Z)) :=
    continuous_induced_dom
  have hat : Continuous (fun g : F.obj Z → F.obj Z ↦ g a) := continuous_apply a
  exact hat.comp (hfun.comp heval)

/-- A map into the automorphism group of a set-valued functor is continuous as soon as each of
its componentwise evaluations is. Together with
`Stacks.FundamentalGroup.continuous_componentEmbedding_apply` this is the universal property of
the topology of `Stacks.FundamentalGroup.functorAutomorphismTopology`. -/
theorem continuous_of_continuous_component (F : C ⥤ Type w) (G : D ⥤ Type w)
    (φ : Aut F → Aut G)
    (h : ∀ (Z : D) (b : G.obj Z), @Continuous (Aut F) (G.obj Z)
      (functorAutomorphismTopology F) ⊥ (fun σ ↦ ((φ σ).app Z).hom b)) :
    @Continuous (Aut F) (Aut G) (functorAutomorphismTopology F)
      (functorAutomorphismTopology G) φ := by
  let _tA : TopologicalSpace (Aut F) := functorAutomorphismTopology F
  let _tG (W : D) : TopologicalSpace (G.obj W) := ⊥
  let _dG (W : D) : DiscreteTopology (G.obj W) := ⟨rfl⟩
  let _tP (W : D) : TopologicalSpace (Equiv.Perm (G.obj W)) := autTopology
  show @Continuous (Aut F) (Aut G) _
    (TopologicalSpace.induced (componentEmbedding G) inferInstance) φ
  refine continuous_induced_rng.mpr (continuous_pi fun Z ↦ ?_)
  exact continuous_induced_rng.mpr (continuous_pi fun b ↦ h Z b)

end Stacks.FundamentalGroup

namespace AlgebraicGeometry

/-- The canonical projection from the fibre at `x` of a finite étale cover base-changed along
`f : X ⟶ Y` to the fibre at `x.map f` of the original cover. -/
def finiteEtaleFiberProjection {X Y : Scheme.{u}} (f : X ⟶ Y) (x : GeometricPoint X)
    (V : FiniteEtaleOver Y) :
    finiteEtaleFiber x ((finiteEtaleBaseChange f).obj V) → finiteEtaleFiber (x.map f) V :=
  fun p ↦ ⟨p.1 ≫ pullback.fst V.hom f, by
    have hp : p.1 ≫ pullback.snd V.hom f = x.hom := p.2
    calc (p.1 ≫ pullback.fst V.hom f) ≫ V.hom
        = p.1 ≫ pullback.fst V.hom f ≫ V.hom := Category.assoc _ _ _
      _ = p.1 ≫ pullback.snd V.hom f ≫ f :=
          congrArg (p.1 ≫ ·) (pullback.condition (f := V.hom) (g := f))
      _ = (p.1 ≫ pullback.snd V.hom f) ≫ f := (Category.assoc _ _ _).symm
      _ = x.hom ≫ f := congrArg (· ≫ f) hp⟩

/-- The fibre projection of a base-changed finite étale cover is a bijection: a lift of `x.map f`
to `V` and the point `x` itself determine a unique lift of `x` to `V ×_Y X`. -/
def finiteEtaleFiberProjectionEquiv {X Y : Scheme.{u}} (f : X ⟶ Y) (x : GeometricPoint X)
    (V : FiniteEtaleOver Y) :
    finiteEtaleFiber x ((finiteEtaleBaseChange f).obj V) ≃ finiteEtaleFiber (x.map f) V where
  toFun := finiteEtaleFiberProjection f x V
  invFun q := ⟨pullback.lift q.1 x.hom q.2, pullback.lift_snd _ _ _⟩
  left_inv p := by
    refine Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _) ?_)
    have hp : p.1 ≫ pullback.snd V.hom f = x.hom := p.2
    exact (pullback.lift_snd _ _ _).trans hp.symm
  right_inv q := Subtype.ext (pullback.lift_fst _ _ _)

/-- The fibre projections assemble into an isomorphism between the fibre functor at `x`
precomposed with base change along `f` and the fibre functor at `x.map f`. -/
def finiteEtaleFiberProjectionIso {X Y : Scheme.{u}} (f : X ⟶ Y) (x : GeometricPoint X) :
    finiteEtaleBaseChange f ⋙ finiteEtaleFiberFunctor x ≅ finiteEtaleFiberFunctor (x.map f) :=
  NatIso.ofComponents (fun V ↦ Equiv.toIso (finiteEtaleFiberProjectionEquiv f x V))
    (fun {V W} g ↦ by
      ext p
      refine Subtype.ext ?_
      change (p.1 ≫ ((finiteEtaleBaseChange f).map g).left) ≫ pullback.fst W.hom f
          = (p.1 ≫ pullback.fst V.hom f) ≫ g.left
      calc (p.1 ≫ ((finiteEtaleBaseChange f).map g).left) ≫ pullback.fst W.hom f
          = p.1 ≫ ((finiteEtaleBaseChange f).map g).left ≫ pullback.fst W.hom f :=
            Category.assoc _ _ _
        _ = p.1 ≫ pullback.fst V.hom f ≫ g.left :=
            congrArg (p.1 ≫ ·) (finiteEtaleBaseChange_map_left_fst f g)
        _ = (p.1 ≫ pullback.fst V.hom f) ≫ g.left := (Category.assoc _ _ _).symm)

/-- The forward component of the fibre-functor isomorphism is the fibre projection. -/
theorem finiteEtaleFiberProjectionIso_hom_app_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    (x : GeometricPoint X) (V : FiniteEtaleOver Y)
    (p : finiteEtaleFiber x ((finiteEtaleBaseChange f).obj V)) :
    (finiteEtaleFiberProjectionIso f x).hom.app V p = finiteEtaleFiberProjection f x V p :=
  rfl

/-- The monoid homomorphism underlying `AlgebraicGeometry.etaleFundamentalGroupMap`: restrict a
natural automorphism of the fibre functor at `x` along base change, then transport it through
the fibre projections. -/
def etaleFundamentalGroupMonoidHom {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) (x : GeometricPoint X) :
    EtaleFundamentalGroup X x →* EtaleFundamentalGroup Y (x.map f) :=
  (finiteEtaleFiberProjectionIso f x).conjAut.toMonoidHom.comp
    (((Functor.whiskeringLeft (FiniteEtaleOver Y) (FiniteEtaleOver X) (Type u)).obj
      (finiteEtaleBaseChange f)).mapAut (finiteEtaleFiberFunctor x))

/-- The component of the transported automorphism at a cover `V` of `Y` is the component at
`V ×_Y X` conjugated by the fibre projection. -/
theorem etaleFundamentalGroupMonoidHom_app_apply {X Y : Scheme.{u}} [ConnectedSpace X]
    [ConnectedSpace Y] (f : X ⟶ Y) (x : GeometricPoint X) (V : FiniteEtaleOver Y)
    (σ : EtaleFundamentalGroup X x) (q : finiteEtaleFiber (x.map f) V) :
    ((etaleFundamentalGroupMonoidHom f x σ).app V).hom q =
      finiteEtaleFiberProjection f x V
        ((σ.app ((finiteEtaleBaseChange f).obj V)).hom
          ((finiteEtaleFiberProjectionEquiv f x V).symm q)) :=
  rfl

/-- **Stacks Project, Tag 0BND (3).** The continuous homomorphism of étale fundamental groups
induced by a morphism of connected schemes and a geometric point of its source. -/
@[stacks 0BND "(3) the induced continuous homomorphism; the equation determining it and the \
commuting square are separate, and (1) and (2) are not covered here"]
def etaleFundamentalGroupMap {X Y : Scheme.{u}} [ConnectedSpace X] [ConnectedSpace Y]
    (f : X ⟶ Y) (x : GeometricPoint X) :
    EtaleFundamentalGroup X x →ₜ* EtaleFundamentalGroup Y (x.map f) where
  toMonoidHom := etaleFundamentalGroupMonoidHom f x
  continuous_toFun := by
    refine Stacks.FundamentalGroup.continuous_of_continuous_component
      (finiteEtaleFiberFunctor x) (finiteEtaleFiberFunctor (x.map f))
      (etaleFundamentalGroupMonoidHom f x) fun V q ↦ ?_
    let _tA : TopologicalSpace (Aut (finiteEtaleFiberFunctor x)) :=
      Stacks.FundamentalGroup.functorAutomorphismTopology (finiteEtaleFiberFunctor x)
    let _tY : TopologicalSpace ((finiteEtaleFiberFunctor (x.map f)).obj V) := ⊥
    let _tX : TopologicalSpace
      ((finiteEtaleFiberFunctor x).obj ((finiteEtaleBaseChange f).obj V)) := ⊥
    let _dX : DiscreteTopology
      ((finiteEtaleFiberFunctor x).obj ((finiteEtaleBaseChange f).obj V)) := ⟨rfl⟩
    have hinner := Stacks.FundamentalGroup.continuous_componentEmbedding_apply
      (finiteEtaleFiberFunctor x) ((finiteEtaleBaseChange f).obj V)
      ((finiteEtaleFiberProjectionEquiv f x V).symm q)
    have houter : @Continuous
        ((finiteEtaleFiberFunctor x).obj ((finiteEtaleBaseChange f).obj V))
        ((finiteEtaleFiberFunctor (x.map f)).obj V) _tX _tY
        (finiteEtaleFiberProjection f x V) :=
      continuous_of_discreteTopology
    exact houter.comp hinner

/-- **Stacks Project, Tag 0BND (3).** The induced homomorphism commutes with the canonical
projection from the geometric fibre of a base-changed finite étale cover to the original
geometric fibre. Since the projections are bijective, this equation determines
`AlgebraicGeometry.etaleFundamentalGroupMap`. -/
@[stacks 0BND "(3) the equation determining the induced continuous homomorphism; the \
homomorphism itself and the commuting square are separate, and (1) and (2) are not covered here"]
theorem etaleFundamentalGroupMap_finiteEtaleFiberProjection {X Y : Scheme.{u}}
    [ConnectedSpace X] [ConnectedSpace Y] (f : X ⟶ Y) (x : GeometricPoint X)
    (V : FiniteEtaleOver Y) (σ : EtaleFundamentalGroup X x)
    (p : finiteEtaleFiber x ((finiteEtaleBaseChange f).obj V)) :
    finiteEtaleFiberProjection f x V ((σ.app _).hom p) =
      ((etaleFundamentalGroupMap f x σ).app V).hom
        (finiteEtaleFiberProjection f x V p) :=
  congrArg
    (fun r ↦ finiteEtaleFiberProjection f x V
      ((σ.app ((finiteEtaleBaseChange f).obj V)).hom r))
    ((finiteEtaleFiberProjectionEquiv f x V).symm_apply_apply p).symm

end AlgebraicGeometry

end
