module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackPushforwardQuasiFinite
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackObstructionVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedVariants
public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningCoherentSystem

/-!
# The inputs of the vanishing of the obstruction groups of the Picard stack

The projection `q : X_{T'} ⟶ T'` of a base change of a flat, proper, finitely presented morphism
of relative dimension `≤ 1` has the same four properties, and the module `f^*𝒞_{T/T'}` on the
inverse image `q⁻¹(T)` whose cohomology computes the obstruction group of Stacks 0DPJ is the
pullback, along the projection `q⁻¹(T) ⟶ T`, of a quasi-coherent module on the algebraic space of
`T`.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- The projection `X_T ⟶ T` of a base change has relative dimension `≤ d` when `f` has
(Stacks 04NS). -/
theorem hasRelativeDimensionLE_projection {d : ℕ}
    (hd : HasRelativeDimensionLE d B S hS D.f.hom) (T : SchemesOver D.Y) :
    HasRelativeDimensionLE d B S hS (D.projection T).hom := by
  intro x
  obtain ⟨e, he, hrel⟩ := hd (pointsMap B S hS _
    (Limits.pullback.fst D.f.hom T.hom.hom) x)
  exact ⟨e, he, (hasRelativeDimensionAt_iff_of_isPullback B S hS
    (AlgebraicSpaces.isPullback_hom B S hS
      (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom))
    D.X.property ((schemeSpaceFunctor B S hS).obj T.left).property D.Y.property
    (isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS D.finitePresentation.1)
    x (e : ℕ∞)).1 hrel⟩

end CoherentSituation

/-- The conormal module of `T ⊂ T'`, transported to the algebraic space represented by `T`. -/
abbrev squareZeroConormalModule {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) :
    Modules.{u, u} B S hS (yoneda.obj T) (isAlgebraicSpace_yoneda B S hS T) :=
  (modulePullback B S hS (rangeSpaceIso B S hS i hi.1).hom).obj
    (conormalModule B S hS ((schemeSpaceFunctor B S hS).obj T') (squareZeroSubspace B S hS i hi))

/-- The conormal module of `T ⊂ T'`, transported to the algebraic space represented by `T`, is
quasi-coherent. -/
theorem isQuasicoherentOnSite_squareZeroConormalModule {T T' : BigFppfOver B S hS} (i : T ⟶ T')
    (hi : IsSquareZeroClosedImmersion B S hS i) :
    (squareZeroConormalModule i hi).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS _ _
    (isQuasicoherentOnSite_conormalModule B S hS _ _)

/-- For `g : W ⟶ T'`, the module computing the obstruction group is a pullback from `T`: the
inverse image of `squareZeroConormalModule i hi` along the projection `g⁻¹(T) ⟶ T` is the inverse
image of the conormal module of `T ⊂ T'` along `preimageProjection`. -/
def modulePullbackConormalIsoSquareZeroPreimageProjection {T T' : BigFppfOver B S hS}
    (i : T ⟶ T') (hi : IsSquareZeroClosedImmersion B S hS i)
    {W : AlgebraicSpaces B S hS} (g : W ⟶ (schemeSpaceFunctor B S hS).obj T') :
    (modulePullback B S hS (squareZeroPreimageProjection B S hS i hi g)).obj
        (squareZeroConormalModule i hi) ≅
      (modulePullback B S hS (preimageProjection B S hS g (squareZeroSubspace B S hS i hi))).obj
        (conormalModule B S hS ((schemeSpaceFunctor B S hS).obj T')
          (squareZeroSubspace B S hS i hi)) :=
  (modulePullbackCompIsoOfEq B S hS
      (squareZeroPreimageProjection B S hS i hi g) (rangeSpaceIso B S hS i hi.1).hom
      ((Category.assoc _ _ _).trans ((congrArg (fun k => _ ≫ k) (Iso.inv_hom_id _)).trans
        (Category.comp_id _)))).app _

end AlgebraicGeometry.Space

end
