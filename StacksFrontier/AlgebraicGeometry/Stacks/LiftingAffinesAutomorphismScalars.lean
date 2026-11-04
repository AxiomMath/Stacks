module

public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesAutomorphismRestriction
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCartesianLifts
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftActionSmul
public import StacksFrontier.AlgebraicGeometry.Spaces.DeformationLiftSheaf

/-!
# Scalars on the parameters of endomorphisms of a smooth lift (Stacks 0CKG (2))

Let `ξ = (U, U', a, i, x', α)` be a smooth lift of an étale open `U` of `W`
(`AlgebraicGeometry.Stack.EtaleSmoothLift`, Stacks 0CJP). The parameters of the endomorphisms
of `ξ` over the identity are the `𝒪`-linear maps `Δ^*Ω_{I/U'} ⟶ 𝒞_{U/U'}` of Stacks 061C, on the
closed subspace `i(U) ⊂ U'`, which `i` identifies with `U`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.zProjection`). A global regular function `f` on `U`
acts on them by multiplication on `𝒞_{U/U'}`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.liftsSmul`); this is the `Γ(U, 𝒪_U)`-module structure
of `SheafHom_{𝒪_U}(Δ^*Ω, 𝒞_{U/U'})(U)` of equation 0CKH of the source.

For a morphism `m = (f, f', γ) : η ⟶ ξ` of smooth lifts, the restriction of parameters along `m`
(`AlgebraicGeometry.Stack.EtaleSmoothLift.IsRestrictParam`) is semilinear over the pullback
`f^*` of functions (`AlgebraicGeometry.Stack.EtaleSmoothLift.IsRestrictParam.smul`), because
the restriction `V ⟶ U` of `f'` to the closed subspaces is étale
(`AlgebraicGeometry.Stack.EtaleSmoothLift.isEtale_liftsZRestriction`); and the datum of
Stacks 0CK6 along `Φ_m` is linear (`AlgebraicGeometry.Stack.EtaleSmoothLift.postcompParam_comp`).

## References

* [Stacks Project, Tag 0CKG](https://stacks.math.columbia.edu/tag/0CKG)
* [Stacks Project, Tag 061C](https://stacks.math.columbia.edu/tag/061C)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Subfunctor

universe v u

variable {C : Type u} [Category.{v} C] {V U : Cᵒᵖ ⥤ Type v}

/-- A morphism of subfunctors over `f` whose source is the inverse image of its target along `f`
is a base change of `f`. -/
theorem isPullback_of_eq_preimage (f : V ⟶ U) {G' : Subfunctor V} {G : Subfunctor U}
    (hG : G' = G.preimage f) (r : G'.toFunctor ⟶ G.toFunctor) (hr : r ≫ G.ι = G'.ι ≫ f) :
    IsPullback r G'.ι G.ι f := by
  subst hG
  have : r = G.fromPreimage f := (cancel_mono G.ι).1 (hr.trans (fromPreimage_ι G f).symm)
  subst this
  exact isPullback_preimage f G

/-- The inverse of the isomorphism onto the range, followed by the morphism, is the inclusion of
the range. -/
theorem inv_toRange_comp (f : V ⟶ U) [IsIso (toRange f)] : inv (toRange f) ≫ f = (range f).ι :=
  (cancel_epi (toRange f)).1 (by rw [IsIso.hom_inv_id_assoc]; exact (toRange_ι f).symm)

end CategoryTheory.Subfunctor

namespace AlgebraicGeometry.Stack.EtaleSmoothLift

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 𝒳' : AlgebraicStacks.{u, w} B S hS} {ι : 𝒳 ⟶ 𝒳'} {hι : IsThickening ι}
  {W : AlgebraicSpaces B S hS}
  {x : (algebraicSpaceStackFunctor B S hS).obj W ⟶ 𝒳}
  {hx : AlgebraicStacks.IsSmooth B S hS x}

attribute [local irreducible] Space.modulePullback Space.smallEtaleRingedSite Space.structureSheaf
  Space.smallEtaleRingedToposHom Space.chartFunctor Space.comparisonFunctor
  Space.modulePullbackCompIso

variable (hι₁ : AlgebraicStacks.IsFirstOrderThickening B S hS ι)

section Projection

variable (ξ : EtaleSmoothLift B S hS ι hι W x hx)

/-- The closed subspace `i(U) ⊂ U'` read on the final object, as an algebraic space. -/
abbrev liftsZSpace : AlgebraicSpaces B S hS :=
  ⟨(liftsZ hι₁ ξ).1.toFunctor, (liftsZ hι₁ ξ).2.1⟩

/-- The closed subspace `i(U) ⊂ U'` lies in the range of the monomorphism `i : U ⟶ U'`. -/
theorem range_ι_le_range_inclusion :
    Subfunctor.range (liftsZ hι₁ ξ).1.ι ≤ Subfunctor.range ξ.inclusion.hom := by
  rintro V _ ⟨z, rfl⟩
  exact z.2

/-- **The identification `i(U) ≅ U`**, in the direction `i(U) ⟶ U`: the inverse of the
isomorphism of `U` onto the range of the monomorphism `i`. -/
def zProjection : liftsZSpace hι₁ ξ ⟶ ξ.base.obj.left :=
  ObjectProperty.homMk (Subfunctor.lift (liftsZ hι₁ ξ).1.ι (range_ι_le_range_inclusion hι₁ ξ) ≫
    @inv _ _ _ _ (Subfunctor.toRange ξ.inclusion.hom) ξ.isThickeningHom_inclusion.1)

/-- The projection `i(U) ⟶ U` followed by `i : U ⟶ U'` is the inclusion of the closed subspace
`i(U) ⊂ U'`. -/
theorem zProjection_comp_inclusion :
    zProjection hι₁ ξ ≫ ξ.inclusion = Space.subspaceInclusion B S hS ξ.ambient (liftsZ hι₁ ξ) :=
  ObjectProperty.hom_ext _ ((Category.assoc _ _ _).trans ((congrArg
    (Subfunctor.lift (liftsZ hι₁ ξ).1.ι (range_ι_le_range_inclusion hι₁ ξ) ≫ ·)
    (@Subfunctor.inv_toRange_comp _ _ _ _ ξ.inclusion.hom ξ.isThickeningHom_inclusion.1)).trans
      (Subfunctor.lift_ι _ _)))

end Projection

variable {η ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)

/-- `f'` restricted to `V ⟶ U` is `f` read through the identifications `V ≅ j(V)`, `U ≅ i(U)`. -/
theorem liftsZRestriction_comp_zProjection :
    liftsZRestriction hι₁ m ≫ zProjection hι₁ ξ = zProjection hι₁ η ≫ m.base.hom.left := by
  have := ξ.mono_inclusion
  rw [← cancel_mono ξ.inclusion, Category.assoc, Category.assoc, zProjection_comp_inclusion,
    ← m.inclusion_comp, ← Category.assoc, zProjection_comp_inclusion]
  exact (liftsZRestriction_square hι₁ m).symm

/-- **The restriction `V ⟶ U` of `f'` to the closed subspaces is étale**: `j(V)` is the inverse
image of `i(U)` along the étale `f'` (Stacks 0CJT), and étale morphisms are stable under base
change. -/
theorem isEtale_liftsZRestriction : Space.IsEtale B S hS (liftsZRestriction hι₁ m).hom := by
  have hG : (liftsZ hι₁ η).1 = (liftsZ hι₁ ξ).1.preimage m.ambient.hom :=
    congrArg Subtype.val (liftsZ_eq_preimageSubspace hι₁ m)
  have hpb := Subfunctor.isPullback_of_eq_preimage m.ambient.hom hG
    (liftsZRestriction hι₁ m).hom (congrArg (fun g => g.hom) (liftsZRestriction_square hι₁ m)).symm
  have hpb' : IsPullback (liftsZRestriction hι₁ m)
      (Space.subspaceInclusion B S hS η.ambient (liftsZ hι₁ η))
      (Space.subspaceInclusion B S hS ξ.ambient (liftsZ hι₁ ξ)) m.ambient :=
    IsPullback.of_map_of_faithful
      (F := ObjectProperty.ι fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
        IsAlgebraicSpace B S hS F) hpb
  exact Space.isEtale_of_isPullback B S hS _ _ _ _ hpb'.flip (Hom.isEtale_ambient η ξ m)

section Scalars

/-- **The scalars on the parameters of `ξ`**: a global regular function on `U`, read on
`i(U) ⊂ U'` through `AlgebraicGeometry.Stack.EtaleSmoothLift.zProjection`. -/
def liftsScalar (ξ : EtaleSmoothLift B S hS ι hι W x hx)
    (f : Space.globalFunctions' B S hS ξ.base.obj.left.1) :
    Space.globalFunctions' B S hS (liftsZSpace hι₁ ξ).1 :=
  Space.globalFunctionsMap B S hS (zProjection hι₁ ξ) f

variable {η ξ : EtaleSmoothLift B S hS ι hι W x hx} (m : Hom η ξ)

/-- Pulling back the scalar of `ξ` given by `f` along the restriction `V ⟶ U` of `f'` gives the
scalar of `η` given by the pullback of `f` along `f : V ⟶ U`. -/
theorem globalFunctionsMap_liftsZRestriction_liftsScalar
    (f : Space.globalFunctions' B S hS ξ.base.obj.left.1) :
    Space.globalFunctionsMap B S hS (liftsZRestriction hι₁ m) (liftsScalar hι₁ ξ f) =
      liftsScalar hι₁ η (Space.globalFunctionsMap B S hS m.base.hom.left f) := by
  unfold liftsScalar
  rw [← RingHom.comp_apply, ← Space.globalFunctionsMap_comp, liftsZRestriction_comp_zProjection,
    Space.globalFunctionsMap_comp, RingHom.comp_apply]

/-- **The restriction of parameters along `m` is semilinear** over the pullback of functions along
`f : V ⟶ U`: if `θ₂` restricts `θ`, then `θ₂ (f^*s)` restricts `θ s`. -/
theorem IsRestrictParam.smul {θ : LiftsActingGroup hι₁ ξ} {θ₂ : RestrictedParam hι₁ m}
    (h : IsRestrictParam hι₁ m θ θ₂) (f : Space.globalFunctions' B S hS ξ.base.obj.left.1) :
    IsRestrictParam hι₁ m
      (θ ≫ Space.globalFunctionsSmul B S hS (X := liftsZSpace hι₁ ξ) (liftsScalar hι₁ ξ f) _)
      (θ₂ ≫ Space.globalFunctionsSmul B S hS (X := liftsZSpace hι₁ η)
        (liftsScalar hι₁ η (Space.globalFunctionsMap B S hS m.base.hom.left f)) _) := by
  have key := Space.comp_derivationMove_smul_of_comp_derivationMove B S hS (baseSubspace hι₁ ξ)
    (liftsW₀ hι₁ ξ) (liftsZ hι₁ ξ) (liftsZ hι₁ η) m.ambient
    ((Space.SpacesEtale.inclusion B S hS ξ.ambient).obj
      (Space.SpacesEtale.final B S hS ξ.ambient)).hom
    m.ambient (Category.comp_id _) (liftsProjection hι₁ ξ) (liftsZMap hι₁ m)
    (Space.conormalEtaleRestrictionSquare B S hS _ _) (liftsZMap_square hι₁ m)
    (diagonalRestriction hι₁ ξ) ξ.selfIntersection.fst (𝟙 ξ.ambient)
    (isFirstOrderThickening_liftsZ hι₁ ξ) (isFirstOrderThickening_liftsZ hι₁ η)
    (isFirstOrderThickening_preimage_fst hι₁ ξ) (liftsZRestriction hι₁ m)
    (liftsZRestriction_square hι₁ m) (liftsZRestriction_comp hι₁ m)
    (conormalRestrictionFinal hι₁ ξ) rfl (conormalRestrictionAlong hι₁ m) rfl ξ.diagonal
    (liftsBase hι₁ ξ).2.2.square (liftsBase hι₁ ξ).2.1.1
    (inclusion_comp_ambient_comp_diagonal hι₁ m) (ambient_comp_diagonal_fst m)
    (isEtale_liftsZRestriction hι₁ m) θ θ₂ (liftsScalar hι₁ ξ f) h
  rw [globalFunctionsMap_liftsZRestriction_liftsScalar] at key
  exact key

/-- **The datum of Stacks 0CK6 along `Φ_m` is linear**: it is precomposition with a fixed map. -/
theorem postcompParam_comp_globalFunctionsSmul (θ : LiftsActingGroup hι₁ η)
    (t : Space.globalFunctions' B S hS (liftsZSpace hι₁ η).1) :
    postcompParam hι₁ m
        (θ ≫ Space.globalFunctionsSmul B S hS (X := liftsZSpace hι₁ η) t
          (Space.conormalModule B S hS η.ambient (liftsZ hι₁ η))) =
      postcompParam hι₁ m θ ≫ Space.globalFunctionsSmul B S hS (X := liftsZSpace hι₁ η) t
        (Space.conormalModule B S hS η.ambient (liftsZ hι₁ η)) := by
  unfold postcompParam Space.postcompDerivationDatum
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))).symm

end Scalars

end AlgebraicGeometry.Stack.EtaleSmoothLift
