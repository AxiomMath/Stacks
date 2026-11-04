module

public import StacksFrontier.AlgebraicGeometry.Spaces.AmpleSchemeFibreTwistFromFormalFunctions
public import StacksFrontier.AlgebraicGeometry.Spaces.FormalFunctionsStalkClauses
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmpleNeighbourhoodOfFibre

/-!
# Twists of a proper space with an ample scheme fibre, and ampleness near that fibre

Let `Y` be a Noetherian scheme of the site, `f : X ⟶ h_Y` a proper morphism from an algebraic
space, `ℒ` an invertible `𝒪_X`-module and `y ∈ Y` a point whose fibre `X_y` is a scheme on which
`ℒ_y` is ample.

* Stacks 0D39: for a coherent `ℱ` there is a `d₀` such that for all `d ≥ d₀` the higher direct
  images `R^p f_*(ℱ ⊗ ℒ^{⊗ d})` vanish at `y` for `p > 0` and
  `f_*(ℱ ⊗ ℒ^{⊗ d})_y ⟶ H^0(X_y, ℱ_y ⊗ ℒ_y^{⊗ d})` is surjective.
* Stacks 0D3A: there is an open neighbourhood `V` of `y` such that `ℒ|_{f⁻¹(V)}` is ample on
  `f⁻¹(V)/V`.

Both follow from the reductions
`AlgebraicGeometry.Space.ampleSchemeFibreTwistStatement_of_formalFunctions` and
`AlgebraicGeometry.Space.exists_mem_isRelativelyAmple_openSub_of_fibreSquare`, together with
clauses (1) and (3) of the theorem on formal functions over `Spec 𝒪_{Y,y}`
(`AlgebraicGeometry.Space.formalFunctionsKernelClause`,
`AlgebraicGeometry.Space.formalFunctionsImageClause`).

## Main results

* `AlgebraicGeometry.Space.exists_ampleSchemeFibreTwistConclusion_tensorPow`: Stacks 0D39.
* `AlgebraicGeometry.Space.exists_mem_isRelativelyAmple_openSub_of_isAmple_baseChangeModule`:
  Stacks 0D3A, the fibre given as a scheme by a cartesian square.
* `exists_mem_isRelativelyAmple_openSub_of_forall_isRelativelyAmple_residueField`:
  Stacks 0D3A with the hypothesis on the fibre read through Stacks 0D31 on every base change of
  `f` to `Spec κ(y)`.

## References

* [Stacks Project, Tag 0D39](https://stacks.math.columbia.edu/tag/0D39)
* [Stacks Project, Tag 0D3A](https://stacks.math.columbia.edu/tag/0D3A)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Stacks 0D39.**  Let `Y` be a Noetherian scheme of the site, `f : X ⟶ h_Y` a proper morphism
from an algebraic space, `ℒ` an invertible and `ℱ` a coherent `𝒪_X`-module, and `y ∈ Y` a point
such that the fibre `X_y` is a scheme (the cartesian square `hsq` of `f` along `Spec κ(y) ⟶ Y`)
on which the restriction of `ℒ` is ample.  Then there is a `d₀` such that for every `d ≥ d₀`,
`R^p f_*(ℱ ⊗ ℒ^{⊗ d})_y = 0` for `p > 0` and every section of `ℱ ⊗ ℒ^{⊗ d}` over `X_y` comes
from `f_*(ℱ ⊗ ℒ^{⊗ d})_y` (`AlgebraicGeometry.Space.AmpleSchemeFibreTwistConclusion`). -/
@[stacks 0D39]
theorem exists_ampleSchemeFibreTwistConclusion_tensorPow (Y : BigFppfOver B S hS)
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS Y)
    (hf : IsProper B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : IsCoherent B S hS X.1 X.2 F)
    (y : (BigFppfOver.toScheme B S hS).obj Y) (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1)
    (q : U ⟶ residuePointObject Y y)
    (hsq : IsPullback p (yoneda.map q) f.hom (yoneda.map (residuePointHom Y y)))
    (hL : ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U p), @Stacks.Ample.IsAmple _ _ hL) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d →
      AmpleSchemeFibreTwistConclusion f y U p (F ⊗ tensorPow B S hS L d) :=
  ampleSchemeFibreTwistStatement_of_formalFunctions formalFunctionsKernelClause
    formalFunctionsImageClause Y X f hf L F hF y U p q hsq hL

/-- **Stacks 0D3A.**  Let `Y` be a Noetherian scheme of the site, `f : X ⟶ h_Y` a proper morphism
from an algebraic space, `ℒ` an invertible `𝒪_X`-module, and `y ∈ Y` a point such that the fibre
`X_y` is a scheme (the cartesian square `hsq` of `f` along `Spec κ(y) ⟶ Y`) on which the
restriction of `ℒ` is ample.  Then there is an open neighbourhood `V` of `y` such that the
pullback of `ℒ` to `f⁻¹(V)` is ample on `f⁻¹(V)/V` (Stacks 0D31), for every base change of `f`
along `V ⟶ Y`. -/
@[stacks 0D3A]
theorem exists_mem_isRelativelyAmple_openSub_of_isAmple_baseChangeModule
    {Y : BigFppfOver B S hS}
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS Y)
    (hf : IsProper B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    [Stacks.SheafOfModules.IsInvertible (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L]
    (y : (BigFppfOver.toScheme B S hS).obj Y) (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X.1)
    (q : U ⟶ residuePointObject Y y)
    (hsq : IsPullback p (yoneda.map q) f.hom (yoneda.map (residuePointHom Y y)))
    (hamp : ∃ hL : Stacks.Ample.IsInvertibleModule ((BigFppfOver.toScheme B S hS).obj U)
      (baseChangeModule B S hS L U p), @Stacks.Ample.IsAmple _ _ hL) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj Y).Opens, y ∈ V ∧
      ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X)
        (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS (openSub Y V)),
        IsPullback p₁ f₁ f (ObjectProperty.homMk (yoneda.map (openSubHom Y V))) →
        IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L) :=
  exists_mem_isRelativelyAmple_openSub_of_fibreSquare
    (ampleSchemeFibreTwistStatement_of_formalFunctions formalFunctionsKernelClause
      formalFunctionsImageClause) f hf L y U p q hsq hamp

/-- **Stacks 0D3A, the fibre read through Stacks 0D31.**  Let `Y` be a Noetherian scheme of the
site, `f : X ⟶ h_Y` a proper morphism from an algebraic space, `ℒ` an invertible `𝒪_X`-module, and
`y ∈ Y` a point such that the pullback of `ℒ` is ample on every base change of `f` along
`Spec κ(y) ⟶ Y` (so `X_y` is a scheme on which `ℒ_y` is ample).  Then there is an open
neighbourhood `V` of `y` such that the pullback of `ℒ` is ample on every base change of `f` along
`V ⟶ Y`. -/
@[stacks 0D3A]
theorem exists_mem_isRelativelyAmple_openSub_of_forall_isRelativelyAmple_residueField
    {Y : BigFppfOver B S hS}
    [_root_.AlgebraicGeometry.IsNoetherian ((BigFppfOver.toScheme B S hS).obj Y)]
    {X : AlgebraicSpaces B S hS} (f : X ⟶ representedAlgebraicSpace B S hS Y)
    (hf : IsProper B S hS f.hom) (L : Modules.{u, u} B S hS X.1 X.2)
    (hL : Stacks.SheafOfModules.IsInvertible (structurePresheaf B S hS X.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)).property
        L)
    (y : (BigFppfOver.toScheme B S hS).obj Y)
    (hy : ∀ ⦃X₀ : AlgebraicSpaces B S hS⦄ (p₀ : X₀ ⟶ X)
      (f₀ : X₀ ⟶ representedAlgebraicSpace B S hS
        (residueFieldObject B S hS Y y (B.residueField_spec_contains Y.left.property y))),
      IsPullback p₀ f₀ f (ObjectProperty.homMk (yoneda.map
        (residueFieldMap B S hS Y y (B.residueField_spec_contains Y.left.property y)))) →
      IsRelativelyAmple B S hS f₀ ((modulePullback B S hS p₀).obj L)) :
    ∃ V : ((BigFppfOver.toScheme B S hS).obj Y).Opens, y ∈ V ∧
      ∀ ⦃X₁ : AlgebraicSpaces B S hS⦄ (p₁ : X₁ ⟶ X)
        (f₁ : X₁ ⟶ representedAlgebraicSpace B S hS (openSub Y V)),
        IsPullback p₁ f₁ f (ObjectProperty.homMk (yoneda.map (openSubHom Y V))) →
        IsRelativelyAmple B S hS f₁ ((modulePullback B S hS p₁).obj L) :=
  exists_mem_isRelativelyAmple_openSub_of_isRelativelyAmple_residueField
    (ampleSchemeFibreTwistStatement_of_formalFunctions formalFunctionsKernelClause
      formalFunctionsImageClause) f hf L hL y hy

end AlgebraicGeometry.Space

end
