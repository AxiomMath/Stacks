module

public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceChartScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.PointTwistNatural
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjInvertibleSpaceClauseOneSite

/-!
# The morphism of schemes underlying a morphism of the big fppf site over `S`, in one spelling

A morphism `c : V ⟶ U` of the big fppf site over `S` has two spellings of its underlying morphism
of schemes in the library: `(BigFppfOver.toScheme B S hS).map c`, through the functor to schemes,
and `AlgebraicGeometry.SmallEtale.schemeHom (associatedBigEtaleSite B) c.left`, through the
inclusion of the big étale site with the same underlying category.  The quasi-coherent pullbacks
of the site (`AlgebraicGeometry.Space.quasicoherentPullbackObj`) are typed in the first spelling,
while the contraction `AlgebraicGeometry.Space.quasicoherentPullbackCompIso` and the pullback of
morphisms `AlgebraicGeometry.Space.quasicoherentPullbackMap` are written in the second.  The two
are the same morphism by definition — they differ only in reading the size cutoff of the category
through `associatedBigEtaleSite B` or directly from `B`, and in `Over.forget` — but not
syntactically, so a statement mixing them makes the kernel unfold both sides.

This file states the bridge once and restates, in the `BigFppfOver.toScheme` spelling only, the
interface of the comparison `σ` of the source squares of the chart maps of Stacks 0D2Z and of
clause (1) of the tag at a scheme point.

## Main results

* `AlgebraicGeometry.Space.smallEtaleSchemeHom_left_eq_toScheme_map`: **the bridge**,
  `SmallEtale.schemeHom (associatedBigEtaleSite B) c.left = (BigFppfOver.toScheme B S hS).map c`.
* `AlgebraicGeometry.Space.quasicoherentPullbackMap_hom_eq`,
  `AlgebraicGeometry.Space.quasicoherentPullbackCompIso_hom_hom_eq`,
  `AlgebraicGeometry.Space.quasicoherentPullbackCompIso_inv_hom_eq`: the underlying morphisms of
  the pullback of a morphism and of the contraction, in the `BigFppfOver.toScheme` spelling.
* `AlgebraicGeometry.Space.toScheme_map_comp_eq_of_comp_eq`: a commutative square of the site,
  read on schemes through `BigFppfOver.toScheme`.
* `AlgebraicGeometry.Space.hom_eq_of_eq_quasicoherentPullbackCompIso`: **the comparison `σ` from
  its value `hσ`, on the underlying modules**, in the `BigFppfOver.toScheme` spelling.
* `…InvertibleTwistingRestriction.quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartTheta`:
  **clause (1) of Stacks 0D2Z at a scheme point `w`, on `W`**, with the inverse image of `ψ` along
  the section `c_w` written as the pullback of the morphism of quasi-coherent modules
  `…RelativeProjSituation.fibrePsiQcohHom`, every morphism of schemes spelled
  `(BigFppfOver.toScheme …).map _` (with
  `…InvertibleTwistingRestriction.quasicoherentPullbackMap_chartSection_fibrePsiQcohHom_hom`).

## References

* [Stacks Project, Tag 0D2Z](https://stacks.math.columbia.edu/tag/0D2Z)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The bridge between the two spellings of the morphism of schemes underlying a morphism of the
site**: `SmallEtale.schemeHom` over the associated big étale site, applied to the underlying
morphism of the slice, is the image under `BigFppfOver.toScheme`. -/
@[simp]
theorem smallEtaleSchemeHom_left_eq_toScheme_map {V U : BigFppfOver B S hS} (c : V ⟶ U) :
    SmallEtale.schemeHom (associatedBigEtaleSite B) c.left =
      (BigFppfOver.toScheme B S hS).map c :=
  rfl

/-- The pullback of a morphism of quasi-coherent modules along a morphism `g` of the site is, on
the underlying modules, the pullback along `(BigFppfOver.toScheme B S hS).map g`. -/
@[simp]
theorem quasicoherentPullbackMap_hom_eq {V U : BigFppfOver B S hS} (g : V ⟶ U)
    {M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory} (φ : M ⟶ N) :
    (quasicoherentPullbackMap B S hS g φ).hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).map φ.hom :=
  rfl

/-- The contraction `h^*(g^*M) ≅ (h ≫ g)^*M` is, on the underlying modules, the contraction of
pullbacks along `(BigFppfOver.toScheme B S hS).map h` and `(BigFppfOver.toScheme B S hS).map g`. -/
@[simp]
theorem quasicoherentPullbackCompIso_hom_hom_eq {W V U : BigFppfOver B S hS} (h : W ⟶ V)
    (g : V ⟶ U) (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (quasicoherentPullbackCompIso B S hS h g M).hom.hom =
      (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map h)
        ((BigFppfOver.toScheme B S hS).map g)).hom.app M.obj :=
  rfl

/-- The inverse of the contraction `h^*(g^*M) ≅ (h ≫ g)^*M` on the underlying modules, in the
`BigFppfOver.toScheme` spelling. -/
@[simp]
theorem quasicoherentPullbackCompIso_inv_hom_eq {W V U : BigFppfOver B S hS} (h : W ⟶ V)
    (g : V ⟶ U) (M : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    (quasicoherentPullbackCompIso B S hS h g M).inv.hom =
      (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map h)
        ((BigFppfOver.toScheme B S hS).map g)).inv.app M.obj :=
  rfl

/-- A commutative square of the site, read on the schemes through `BigFppfOver.toScheme`. -/
theorem toScheme_map_comp_eq_of_comp_eq {W V V' U : BigFppfOver B S hS} {τ : W ⟶ V}
    {c : V ⟶ U} {c' : W ⟶ V'} {y : V' ⟶ U} (e : τ ≫ c = c' ≫ y) :
    (BigFppfOver.toScheme B S hS).map τ ≫ (BigFppfOver.toScheme B S hS).map c =
      (BigFppfOver.toScheme B S hS).map c' ≫ (BigFppfOver.toScheme B S hS).map y :=
  (((BigFppfOver.toScheme B S hS).map_comp τ c).symm.trans
    (congrArg (BigFppfOver.toScheme B S hS).map e)).trans
    ((BigFppfOver.toScheme B S hS).map_comp c' y)

/-- **The comparison `σ` of two pullbacks from its value, on the underlying modules, in the
`BigFppfOver.toScheme` spelling.**  For `τ ≫ c = c' ≫ y` in the site and `t : y^*N ⟶ N'`, a
morphism `σ : τ^*(c^*N) ⟶ c'^*N'` equal to the contraction `τ^*(c^*N) ≅ (τ ≫ c)^*N`, the transport
along `τ ≫ c = c' ≫ y`, the inverse contraction and the pullback of `t` along `c'` is, on the
underlying modules, the corresponding composite of `Scheme.Modules.pullbackComp`, `eqToHom` and
`Scheme.Modules.pullback` along the images of `τ, c, c', y` under `BigFppfOver.toScheme`.  This is
`AlgebraicGeometry.Space.quasicoherentPullbackCompIso_hom_comp_eqToHom_comp_inv_comp_map_hom` with
`SmallEtale.schemeHom … _.left` replaced by `(BigFppfOver.toScheme …).map _`, consuming the
hypothesis `hσ` of the source squares directly. -/
theorem hom_eq_of_eq_quasicoherentPullbackCompIso {W V V' U : BigFppfOver B S hS}
    (τ : W ⟶ V) (c : V ⟶ U) (c' : W ⟶ V') (y : V' ⟶ U) (e : τ ≫ c = c' ≫ y)
    (N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory)
    {N' : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj V').ringCatSheaf).FullSubcategory}
    (t : quasicoherentPullbackObj B S hS y N ⟶ N')
    (σ : quasicoherentPullbackObj B S hS τ (quasicoherentPullbackObj B S hS c N) ⟶
      quasicoherentPullbackObj B S hS c' N')
    (hσ : σ = (quasicoherentPullbackCompIso B S hS τ c N).hom ≫
      quasicoherentPullbackEqToHom B S hS e N ≫
        (quasicoherentPullbackCompIso B S hS c' y N).inv ≫
          quasicoherentPullbackMap B S hS c' t) :
    σ.hom =
      (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map τ)
          ((BigFppfOver.toScheme B S hS).map c)).hom.app N.obj ≫
        eqToHom (congrArg (fun k => (Scheme.Modules.pullback k).obj N.obj)
          (toScheme_map_comp_eq_of_comp_eq e)) ≫
        (Scheme.Modules.pullbackComp ((BigFppfOver.toScheme B S hS).map c')
          ((BigFppfOver.toScheme B S hS).map y)).inv.app N.obj ≫
        (Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map c')).map t.hom := by
  subst hσ
  exact quasicoherentPullbackCompIso_hom_comp_eqToHom_comp_inv_comp_map_hom τ c c' y e N t

end AlgebraicGeometry.Space


namespace AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism
open Stacks.Sheaves.GradedAlgebraEssentiallySmall (gradedPull)

attribute [local instance 5000] AlgebraicGeometry.Space.SmallEtale.instHasSheafify
  AlgebraicGeometry.Space.SmallEtale.instWEqualsLocallyBijective

universe m

variable (s : RelativeProjSituation.{u, m})
  {X : AlgebraicSpaces s.shrink.site s.shrink.base s.shrink.containsBase} (f : X ⟶ s.shrink.space)
  (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O))
  [hL : Stacks.SheafOfModules.IsInvertible
    (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
    (Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L]
  (ψ : SheafOfModules.GradedAlgebra.UnitalHom
    ((gradedPull (X := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X)
      (Y := smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase s.shrink.space)
      (smallEtaleRingedToposHom s.shrink.site s.shrink.base s.shrink.containsBase f)).obj
        s.shrink.algebra)
    (Stacks.SheafOfModules.TensorPower.laurentAlgebra
      (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedTopos s.shrink.site s.shrink.base s.shrink.containsBase X).O).property L))
  {W : BigFppfOver s.site s.base s.containsBase} (x : yoneda.obj W ⟶ X.1)
  (hx : (ofUnitalHom s f L ψ).locusOpen W x = ⊤) (d : ℕ)


/-- **The inverse image of `ψ` of Tag 01NR along the section `c_w`, in the
`BigFppfOver.toScheme` spelling**: the pullback along `c_w` of the morphism of quasi-coherent
modules `…RelativeProjSituation.fibrePsiQcohHom` is, on the underlying modules, the pullback of
`ψ` in adjoint form (`…RelativeProjSituation.psiChartSchemeHomOfAdjoint`) along
`(BigFppfOver.toScheme …).map c_w`. -/
theorem quasicoherentPullbackMap_chartSection_fibrePsiQcohHom_hom :
    (quasicoherentPullbackMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x hx) (s.fibrePsiQcohHom W (x ≫ f.hom) d)).hom =
      (Scheme.Modules.pullback ((BigFppfOver.toScheme s.site s.base s.containsBase).map
          ((ofUnitalHom s f L ψ).chartSection x hx))).map
        (s.psiChartSchemeHomOfAdjoint W (x ≫ f.hom) d) :=
  rfl

/-- `…RelativeProjSituation.psiChartSchemeHomOfAdjoint` is
`AlgebraicGeometry.Space.pullbackAdjointPsi` at the graded algebra
`s.relativeProjPoints.algebra W v` of the points of the relative Proj, the spelling of
`…InvertibleTwistingRestriction.pullback_map_pullbackAdjointPsi_comp_chartTheta`. -/
theorem psiChartSchemeHomOfAdjoint_eq_pullbackAdjointPsi :
    s.psiChartSchemeHomOfAdjoint W (x ≫ f.hom) d =
      AlgebraicGeometry.Space.pullbackAdjointPsi
        (s.relativeProjPoints.algebra W (x ≫ f.hom)) (s.toRelativeProj W (x ≫ f.hom))
        (s.fibreToBase W (x ≫ f.hom)) (s.fibreToBase_eq W (x ≫ f.hom)) d :=
  rfl

/-- **Clause (1) of [Stacks, Tag 0D2Z] at a scheme point `w` of `U(ψ)`, on the scheme `W`, with
the inverse image of `ψ` along `c_w` read through the quasi-coherent pullback of the site.**  The
pullback along the section `c_w` of `…RelativeProjSituation.fibrePsiQcohHom` (`ψ` of Tag 01NR in
adjoint form, as a morphism of quasi-coherent modules), followed by the contraction
`c_w^*((W ×_Y P ⟶ P)^*𝒪(d)) ≅ r_w^*𝒪(d)` and `θ_w` of Tag 01O9, is the contraction
`c_w^*(π_W^*((f ∘ w)^*𝒜)_d) ≅ ((f ∘ w)^*𝒜)_d` followed by the adjoint transpose of the
restriction `w^*ψ`.  Every morphism of schemes is spelled `(BigFppfOver.toScheme …).map _`: this is
`…InvertibleTwistingRestriction.pullback_map_pullbackAdjointPsi_comp_chartTheta` at
`c = (BigFppfOver.toScheme …).map c_w`, with its first factor replaced along
`…quasicoherentPullbackMap_chartSection_fibrePsiQcohHom_hom`. -/
theorem quasicoherentPullbackMap_fibrePsiQcohHom_hom_comp_chartTheta :
    (quasicoherentPullbackMap s.site s.base s.containsBase
        ((ofUnitalHom s f L ψ).chartSection x hx) (s.fibrePsiQcohHom W (x ≫ f.hom) d)).hom ≫
        Stacks.AlgebraicGeometry.ModuleLimits.canHom
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map
            ((ofUnitalHom s f L ψ).chartSection x hx)) (s.toRelativeProj W (x ≫ f.hom))
          ((ofUnitalHom s f L ψ).chartLift x hx ≫
            (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x)).globalMorphism
              (relativeProj (s.relativeProjPoints.algebra W (x ≫ f.hom))))
          (toScheme_map_chartSection_toRelativeProj s f L ψ x hx)
          ((GradedPowerMap.twD (s.relativeProjPoints.algebra W (x ≫ f.hom))).algebra.piece
            (d : ℤ)) ≫
        (toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x)).thetaOnSection
          ((ofUnitalHom s f L ψ).chartLift x hx)
          ((ofUnitalHom s f L ψ).chartLift_ι x hx) (d : ℤ) =
      Stacks.AlgebraicGeometry.ModuleLimits.canHom
          ((BigFppfOver.toScheme s.site s.base s.containsBase).map
            ((ofUnitalHom s f L ψ).chartSection x hx))
          (s.fibreToBase W (x ≫ f.hom))
          (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W))
          (toScheme_map_chartSection_comp_fibreToBase s f L ψ x hx)
          ((s.relativeProjPoints.algebra W (x ≫ f.hom)).piece (d : ℤ)) ≫
        ((Scheme.Modules.pullbackPushforwardAdjunction
            (𝟙 ((BigFppfOver.toScheme s.site s.base s.containsBase).obj W))).homEquiv _ _).symm
          ((toGradedPowerMap ((ofUnitalHom s f L ψ).twisting W x)).ψ d) ≫
        (Stacks.AlgebraicGeometry.CoherentMulSections.powCompare
          ((ofUnitalHom s f L ψ).line W x) d).hom := by
  rw [quasicoherentPullbackMap_chartSection_fibrePsiQcohHom_hom,
    psiChartSchemeHomOfAdjoint_eq_pullbackAdjointPsi]
  exact pullback_map_pullbackAdjointPsi_comp_chartTheta s f L ψ x hx d _
    (toScheme_map_chartSection_toRelativeProj s f L ψ x hx)
    (toScheme_map_chartSection_comp_fibreToBase s f L ψ x hx)

end AlgebraicGeometry.Space.RelativeProjSituation.InvertibleTwistingRestriction

end
