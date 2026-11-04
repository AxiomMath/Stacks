module

public import Mathlib.AlgebraicGeometry.Restrict
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.BaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport

/-!
# Standard shrinkings of a complete dévissage

A standard shrinking of a complete dévissage at a point chooses standard opens in the base,
in the source, and in the closed subscheme and the smooth scheme of every stage, containing
the base point, the source point and the distinguished points of the stages, in such a way
that the restricted system is again a complete dévissage at the same point.

## Main definitions

* `AlgebraicGeometry.StageIsStandardRestriction`: a stage of a complete dévissage is the
  restriction of another one to standard opens.
* `AlgebraicGeometry.PointedStageIsStandardRestriction`: the compatibility of the
  distinguished points of two such stages.
* `AlgebraicGeometry.PointedChainIsStandardRestriction`: the same at every stage of a chain.
* `AlgebraicGeometry.NonemptyCompleteDevissageAt.StandardShrinking`: a standard shrinking of a
  complete dévissage at a point.

## Implementation notes

The source says that the shrunk system is a *one-step* dévissage of `𝓕'/X'/S'` at `x`; since
that system is the whole system `(Z'ₖ, Y'ₖ, i'ₖ, π'ₖ, 𝓖'ₖ, α'ₖ, zₖ, yₖ)` indexed by
`k = 1, …, n` and carries the maps `α'ₖ`, this is read as *complete* dévissage, which is also
how Stacks 05HM uses the definition.

A stage of the shrunk dévissage is related to the original stage by open immersions `j_Z`,
`j_Y` of its closed subscheme and its smooth scheme, rather than by a heterogeneous equality
with the scheme of an open subset: the restricted stage is then only determined up to a
unique isomorphism, which is what makes the comparison of the free-module maps expressible.
Standardness of the two opens is the statement that the range of the open immersion is a
basic open; the two schemes are affine, so this is the source's condition.

The maps `i'ₖ`, `π'ₖ`, `g'ₖ` are pinned down as the restrictions of `iₖ`, `πₖ`, `gₖ` by the
commuting squares, and `𝓖'ₖ` as the restriction of `𝓖ₖ`. The restriction of `αₖ` is the
composite of the canonical comparison of a restricted direct image with the direct image of
the restriction — which is
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans`, the base-change morphism of
the commuting square, needing no cartesianness — with the canonical identification
`AlgebraicGeometry.Scheme.Modules.pullbackFreeIso` of the inverse image of a free module with
a free module of the same rank; no isomorphism is existentially quantified, so `α'ₖ` is not
allowed an arbitrary change of basis. The square relating `πₖ` and `π'ₖ` is *not* required to
be cartesian: the source only asks for standard opens whose restricted maps again form a
complete dévissage, and `Z'ₖ` need not be all of `πₖ⁻¹(Y'ₖ)`.

The distinguished points are required to be the original ones, as in the source: the points
of the shrunk system map to `zₖ`, `yₖ` and `x` under the open immersions.

## References

* [Stacks Project, Tag 05HL](https://stacks.math.columbia.edu/tag/05HL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A stage of a complete dévissage which is the restriction of another stage to standard
opens of its closed subscheme and of its smooth scheme. -/
structure StageIsStandardRestriction {X S X' S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'}
    {F : X.Modules} {F' : X'.Modules} {s : S} {s' : S'}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    [LocallyOfFiniteType f'] [F'.IsQuasicoherent] [F'.IsFiniteType]
    (jS : S' ⟶ S) (jX : X' ⟶ X)
    (D : DevissageStage f F s) (D' : DevissageStage f' F' s') where
  /-- The shrunk closed subscheme inside the original one. -/
  jZ : D'.oneStep.Z ⟶ D.oneStep.Z
  /-- The shrunk smooth scheme inside the original one. -/
  jY : D'.oneStep.Y ⟶ D.oneStep.Y
  openImmersion_jZ : IsOpenImmersion jZ
  openImmersion_jY : IsOpenImmersion jY
  /-- A global function cutting out the shrunk closed subscheme. -/
  closed_section : Γ(D.oneStep.Z, ⊤)
  /-- A global function cutting out the shrunk smooth scheme. -/
  smooth_section : Γ(D.oneStep.Y, ⊤)
  /-- The shrunk closed subscheme is a standard open of the original one. -/
  closed_standard :
    haveI := openImmersion_jZ
    jZ.opensRange = D.oneStep.Z.basicOpen closed_section
  /-- The shrunk smooth scheme is a standard open of the original one. -/
  smooth_standard :
    haveI := openImmersion_jY
    jY.opensRange = D.oneStep.Y.basicOpen smooth_section
  /-- The closed immersion of the stage is the restriction of the original one. -/
  closed_comm : jZ ≫ D.oneStep.i = D'.oneStep.i ≫ jX
  /-- The finite morphism of the stage is the restriction of the original one. -/
  finite_comm : jZ ≫ D.oneStep.π = D'.oneStep.π ≫ jY
  /-- The structure morphism of the stage is the restriction of the original one. -/
  smooth_comm : jY ≫ D.oneStep.g = D'.oneStep.g ≫ jS
  /-- The module of the stage is the restriction of the original one. -/
  G_eq : D'.oneStep.G = (Scheme.Modules.pullback jZ).obj D.oneStep.G
  /-- The restriction has the same rank. -/
  rank_eq : D'.rank = D.rank
  /-- The free-module map of the stage is the restriction of the original one, under the
  canonical comparison of the restricted direct image with the direct image of the
  restriction, and the canonical identification of the restriction of a free module. -/
  alpha_restrict :
    (Scheme.Modules.pullback jY).map D.alpha ≫
        (AffinePushforward.baseChangeNatTrans finite_comm).app D.oneStep.G ≫
        (Scheme.Modules.pushforward D'.oneStep.π).map (eqToHom G_eq.symm) =
      (Scheme.Modules.pullbackFreeIso jY (ULift.{u} (Fin D.rank))).hom ≫
      SheafOfModules.freeMap (R := D'.oneStep.Y.ringCatSheaf)
        (fun i : ULift.{u} (Fin D.rank) => ULift.up (Fin.cast rank_eq.symm i.down)) ≫
        D'.alpha

/-- The distinguished points of a stage and of its standard restriction are the same points:
those of the restriction map to those of the original stage. -/
structure PointedStageIsStandardRestriction {X S X' S' : Scheme.{u}} {f : X ⟶ S}
    {f' : X' ⟶ S'} {F : X.Modules} {F' : X'.Modules} {s : S} {s' : S'}
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    [LocallyOfFiniteType f'] [F'.IsQuasicoherent] [F'.IsFiniteType]
    {x : X} {x' : X'} {D : DevissageStage f F s} {D' : DevissageStage f' F' s'}
    (jS : S' ⟶ S) (jX : X' ⟶ X) (pointed : PointedDevissageStage f F s x D)
    (pointed' : PointedDevissageStage f' F' s' x' D')
    (hstage : StageIsStandardRestriction jS jX D D') where
  x_eq : jX x' = x
  y_eq : hstage.jY pointed'.y = pointed.y
  /-- The distinguished point of the closed subscheme of the stage. -/
  z : D.oneStep.Z
  /-- The distinguished point of the closed subscheme of the restricted stage. -/
  z' : D'.oneStep.Z
  z_eq : hstage.jZ z' = z
  /-- `z` is the distinguished point of the closed subscheme recorded by `pointed`. -/
  z_is_pointed : HEq pointed.atPoint.z z
  /-- `z'` is the distinguished point of the closed subscheme recorded by `pointed'`. -/
  z'_is_pointed : HEq pointed'.atPoint.z z'

/-- Every stage of a pointed complete dévissage is the standard restriction, with the same
distinguished points, of the corresponding stage of another one. -/
inductive PointedChainIsStandardRestriction {S S' : Scheme.{u}} {s : S} {s' : S'}
    (jS : S' ⟶ S) :
    {X : Scheme.{u}} → {f : X ⟶ S} → {F : X.Modules} → {hl : LocallyOfFiniteType f} →
      {hq : F.IsQuasicoherent} → {ht : F.IsFiniteType} →
      {X' : Scheme.{u}} → {f' : X' ⟶ S'} → {F' : X'.Modules} →
      {hl' : LocallyOfFiniteType f'} → {hq' : F'.IsQuasicoherent} →
      {ht' : F'.IsFiniteType} → (jX : X' ⟶ X) → {x : X} → {x' : X'} →
      {chain : DevissageChain s X f F hl hq ht} →
      {chain' : DevissageChain s' X' f' F' hl' hq' ht'} →
      PointedDevissageChain s X f F hl hq ht x chain →
      PointedDevissageChain s' X' f' F' hl' hq' ht' x' chain' → Prop where
  /-- The final stages correspond. -/
  | last {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {X' : Scheme.{u}} {f' : X' ⟶ S'}
      {F' : X'.Modules} [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent]
      [ht : F.IsFiniteType] [hl' : LocallyOfFiniteType f'] [hq' : F'.IsQuasicoherent]
      [ht' : F'.IsFiniteType] {jX : X' ⟶ X} {x : X} {x' : X'}
      {D : @DevissageStage X S f F s hl hq ht}
      {D' : @DevissageStage X' S' f' F' s' hl' hq' ht'}
      {hz : IsZero D.coker} {hz' : IsZero D'.coker}
      {P : @PointedDevissageStage X S f F s x hl hq ht D}
      {P' : @PointedDevissageStage X' S' f' F' s' x' hl' hq' ht' D'}
      (hstage : StageIsStandardRestriction jS jX D D')
      (hpoint : PointedStageIsStandardRestriction jS jX P P' hstage) :
      PointedChainIsStandardRestriction jS jX (.last x D hz P) (.last x' D' hz' P')
  /-- A nonfinal stage corresponds, and so does the dévissage of its cokernel. -/
  | more {X : Scheme.{u}} {f : X ⟶ S} {F : X.Modules} {X' : Scheme.{u}} {f' : X' ⟶ S'}
      {F' : X'.Modules} [hl : LocallyOfFiniteType f] [hq : F.IsQuasicoherent]
      [ht : F.IsFiniteType] [hl' : LocallyOfFiniteType f'] [hq' : F'.IsQuasicoherent]
      [ht' : F'.IsFiniteType] {jX : X' ⟶ X} {x : X} {x' : X'}
      {D : @DevissageStage X S f F s hl hq ht}
      {D' : @DevissageStage X' S' f' F' s' hl' hq' ht'}
      {hqC : D.coker.IsQuasicoherent} {htC : D.coker.IsFiniteType}
      {hlY : LocallyOfFiniteType D.oneStep.g} {hqC' : D'.coker.IsQuasicoherent}
      {htC' : D'.coker.IsFiniteType} {hlY' : LocallyOfFiniteType D'.oneStep.g}
      {tail : DevissageChain s D.oneStep.Y D.oneStep.g D.coker hlY hqC htC}
      {tail' : DevissageChain s' D'.oneStep.Y D'.oneStep.g D'.coker hlY' hqC' htC'}
      {P : @PointedDevissageStage X S f F s x hl hq ht D}
      {P' : @PointedDevissageStage X' S' f' F' s' x' hl' hq' ht' D'}
      {Pt : PointedDevissageChain s D.oneStep.Y D.oneStep.g D.coker hlY hqC htC P.y tail}
      {Pt' : PointedDevissageChain s' D'.oneStep.Y D'.oneStep.g D'.coker hlY' hqC' htC'
        P'.y tail'}
      (hstage : StageIsStandardRestriction jS jX D D')
      (hpoint : PointedStageIsStandardRestriction jS jX P P' hstage)
      (htail : PointedChainIsStandardRestriction jS hstage.jY Pt Pt') :
      PointedChainIsStandardRestriction jS jX (.more x D hqC htC hlY tail P Pt)
        (.more x' D' hqC' htC' hlY' tail' P' Pt')

namespace NonemptyCompleteDevissageAt

/-- A standard shrinking of a complete dévissage of `F/X/S` at `x`: standard opens of the
base and of the source, and standard opens in every stage, containing the distinguished
points, whose restricted system is again a complete dévissage at `x`. -/
@[stacks 05HL]
structure StandardShrinking {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (x : X)
    [LocallyOfFiniteType f] [F.IsQuasicoherent] [F.IsFiniteType]
    (D : NonemptyCompleteDevissageAt f F x) where
  /-- The shrunk base. -/
  S' : S.Opens
  /-- The shrunk source. -/
  X' : X.Opens
  /-- A global function cutting out the shrunk base. -/
  base_section : Γ(S, ⊤)
  /-- A global function cutting out the shrunk source. -/
  source_section : Γ(X, ⊤)
  base_standard : S' = S.basicOpen base_section
  source_standard : X' = X.basicOpen source_section
  mem_base : f x ∈ S'
  mem_source : x ∈ X'
  source_over_base : X' ≤ f ⁻¹ᵁ S'
  /-- The restricted structure morphism. -/
  restricted_morphism : X'.toScheme ⟶ S'.toScheme
  restricted_morphism_eq : restricted_morphism = f.resLE S' X' source_over_base
  /-- The restricted structure morphism is locally of finite type. -/
  locally_finite_type : LocallyOfFiniteType restricted_morphism
  /-- The restriction of `F` to the shrunk source is quasi-coherent. -/
  quasi_coherent : (F.restrict X'.ι).IsQuasicoherent
  /-- The restriction of `F` to the shrunk source is of finite type. -/
  finite_type : (F.restrict X'.ι).IsFiniteType
  /-- The restricted system is a complete dévissage of `F|_{X'}/X'/S'` at `x`. -/
  restricted_devissage :
    @NonemptyCompleteDevissageAt _ _ restricted_morphism (F.restrict X'.ι) ⟨x, mem_source⟩
      locally_finite_type quasi_coherent finite_type
  /-- Every stage of the restricted dévissage is the restriction of the corresponding stage
  to standard opens, with the same distinguished points. -/
  restricted_stages : PointedChainIsStandardRestriction S'.ι X'.ι D.pointed
    restricted_devissage.pointed

end NonemptyCompleteDevissageAt

end AlgebraicGeometry

end
