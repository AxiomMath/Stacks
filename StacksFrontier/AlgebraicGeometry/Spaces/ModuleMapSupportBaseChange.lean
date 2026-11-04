module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleMapBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupportEquality
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback

/-!
# Base change of a module of finite type supported in the image of a morphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, let
`g : X' ⟶ X` be a morphism of algebraic spaces, and let `M` be a quasi-coherent `𝒪_X`-module of
finite type whose support is contained in the image of `|X'| ⟶ |X|`.  Both hypotheses are
inherited by the base change of `M` to `X ×_Y T` for a test scheme `T` over `Y`: finite type is
stable under inverse image, and the support of the inverse image is the inverse image of the
support, which the cartesian square `X' ×_Y T = X' ×_X (X ×_Y T)` turns into the image of
`|X' ×_Y T| ⟶ |X ×_Y T|`.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.ModuleMapSituation.isFiniteTypeOnSite_baseChange`: the base change
  of a module of finite type is of finite type.
* `AlgebraicGeometry.Space.ModuleMapSituation.supportOfSheaf_baseChange_subset_range`: the
  support of the base change is contained in the image of the comparison `X' ×_Y T ⟶ X ×_Y T`.

## Implementation notes

The surjectivity input is Stacks 03H4,
`AlgebraicGeometry.Space.exists_point_of_isPullback`, applied to the cartesian square
`AlgebraicGeometry.Space.ModuleMapSituation.isPullback_pullbackBaseChangeMap`: a point of `X'`
and a point of `X ×_Y T` with the same image in `X` come from a point of `X' ×_Y T`.

## References

* [Stacks Project, Tag 083F](https://stacks.math.columbia.edu/tag/083F)
* [Stacks Project, Tag 07TZ](https://stacks.math.columbia.edu/tag/07TZ)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ModuleMapSituation

variable (D : ModuleMapSituation.{u, u} B S hS)

/-- The base change to `X ×_Y T` of an `𝒪_X`-module of finite type is again of finite type, the
inverse image of Stacks 03LU preserving finite type by Stacks 03DO. -/
theorem isFiniteTypeOnSite_baseChange (M : Modules.{u, u} B S hS D.X.1 D.X.2)
    (hft : SheafOfModules.IsFiniteTypeOnSite M) (T : D.SchemesOver) :
    SheafOfModules.IsFiniteTypeOnSite
      ((modulePullback B S hS (D.baseChangeProjection T)).obj M) :=
  isFiniteTypeOnSite_modulePullback B S hS (D.baseChangeProjection T) M hft

/-- If the support of a quasi-coherent `𝒪_X`-module `M` of finite type is contained in the image
of `|X'| ⟶ |X|`, then the support of its base change to `X ×_Y T` is contained in the image of
the comparison `|X' ×_Y T| ⟶ |X ×_Y T|`.

The support of the base change is the inverse image of the support of `M` by Stacks 07TZ(3), and
a point of `X ×_Y T` whose image in `X` comes from `X'` comes from `X' ×_Y T` by Stacks 03H4
applied to the cartesian square `X' ×_Y T = X' ×_X (X ×_Y T)`. -/
theorem supportOfSheaf_baseChange_subset_range {X' : AlgebraicSpaces B S hS} (g : X' ⟶ D.X)
    (hF : ((modulePullback B S hS g).obj D.F).IsQuasicoherentOnSite)
    (hG : ((modulePullback B S hS g).obj D.G).IsQuasicoherentOnSite)
    (M : Modules.{u, u} B S hS D.X.1 D.X.2) (hqc : M.IsQuasicoherentOnSite)
    (hft : SheafOfModules.IsFiniteTypeOnSite M)
    (hsupp : supportOfSheaf B S hS D.X.1 ((SheafOfModules.toSheaf _).obj M) ⊆
      Set.range (pointsMap B S hS X'.1 g.hom))
    (T : D.SchemesOver) :
    supportOfSheaf B S hS (D.baseChangeSpace T).1
        ((SheafOfModules.toSheaf _).obj
          ((modulePullback B S hS (D.baseChangeProjection T)).obj M)) ⊆
      Set.range (pointsMap B S hS ((D.pullbackSituation g hF hG).baseChangeSpace T).1
        (D.pullbackBaseChangeMap g hF hG T).hom) := by
  intro x hx
  obtain ⟨x', hx'⟩ := hsupp
    ((supportOfSheaf_modulePullback_eq B S hS (D.baseChangeProjection T) M hqc hft).le hx)
  obtain ⟨w, -, hw⟩ :=
    exists_point_of_isPullback B S hS (D.isPullback_pullbackBaseChangeMap g hF hG T) x' x hx'
  exact ⟨w, hw⟩

end ModuleMapSituation

end AlgebraicGeometry.Space

end
