module

public import StacksFrontier.AlgebraicGeometry.Spaces.DualityRightAdjointBaseChangeAffine
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.SmallEtaleDerivedPullbackSheafHomMap
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleDerivedSheafHomDinaturality
public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomSquare
public import StacksFrontier.CategoryTheory.Adjunction.TransportAdjunctionDinaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomDinaturality
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The map of Stacks 08JF on algebraic spaces around a commutative square

For a commutative square `g₀ ≫ a = a' ≫ g'` of algebraic spaces, the maps
`Lh^*R𝓗om(E, K) ⟶ R𝓗om(Lh^*E, Lh^*K)` of Stacks 08JF along the two sides of the square agree,
up to the identification `ε : L(a')^* L(g')^* ≅ L(g₀)^* La^*` of the two iterated derived
pullbacks, in both variables of `R𝓗om`; and this survives postcomposition with a map
`φ : L(g')^*K ⟶ K'`.

## Main results

* `AlgebraicGeometry.Space.smallEtaleDerivedPullbackSheafHomMap_square`.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
-/

/- Instances that come into scope here only through the base versions of imported modules,
and that would change the elaboration below (universe joins, the small model of `D(R)`). -/
attribute [-instance] SheafOfModules.hasBinBiprod

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X X' Z Z' : AlgebraicSpaces B S hS} (g' : X' ⟶ X) (a : Z ⟶ X) (a' : Z' ⟶ X') (g₀ : Z' ⟶ Z)
  (ha' : g₀ ≫ a = a' ≫ g')

/-- **The map of Stacks 08JF around a commutative square.** For `g₀ ≫ a = a' ≫ g'`, `E`, `K` on
`X`, and `φ : L(g')^*K ⟶ K'`, with `ε⁻¹ : L(g₀)^*La^* ≅ L(a')^*L(g')^*` the comparison of the two
iterated pullbacks: `L(g₀)^*` of the map along `a`, followed by the map along `g₀` and
`ε⁻¹ ≫ L(a')^*φ`, is `ε⁻¹` followed by `L(a')^*` of the map along `g'` and `φ`, the map along `a'`
and `R𝓗om(ε⁻¹, -)`. -/
theorem smallEtaleDerivedPullbackSheafHomMap_square
    (E K : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)))
    (K' : DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X')))
    (φ : (smallEtaleDerivedModulePullback B S hS g').obj K ⟶ K') :
    (smallEtaleDerivedModulePullback B S hS g₀).map (smallEtaleDerivedPullbackSheafHomMap a E K) ≫
        smallEtaleDerivedPullbackSheafHomMap g₀ ((smallEtaleDerivedModulePullback B S hS a).obj E)
          ((smallEtaleDerivedModulePullback B S hS a).obj K) ≫
        ((smallEtaleDerivedSheafHom B S hS Z').obj
          (op ((smallEtaleDerivedModulePullback B S hS g₀).obj
            ((smallEtaleDerivedModulePullback B S hS a).obj E)))).map
          ((smallEtaleDerivedModulePullbackCompIso B S hS g₀ a).hom.app K ≫
            (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app K ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app K ≫
            (smallEtaleDerivedModulePullback B S hS a').map φ) =
      ((smallEtaleDerivedModulePullbackCompIso B S hS g₀ a).hom.app
            (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K) ≫
          (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app
            (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K) ≫
          (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app
            (((smallEtaleDerivedSheafHom B S hS X).obj (op E)).obj K) ≫
          (smallEtaleDerivedModulePullback B S hS a').map
            (smallEtaleDerivedPullbackSheafHomMap g' E K ≫
              ((smallEtaleDerivedSheafHom B S hS X').obj
                (op ((smallEtaleDerivedModulePullback B S hS g').obj E))).map φ)) ≫
        smallEtaleDerivedPullbackSheafHomMap a' ((smallEtaleDerivedModulePullback B S hS g').obj E)
          K' ≫
        ((smallEtaleDerivedSheafHom B S hS Z').map
          ((smallEtaleDerivedModulePullbackCompIso B S hS g₀ a).hom.app E ≫
            (smallEtaleDerivedModulePullbackCongr B S hS ha').hom.app E ≫
            (smallEtaleDerivedModulePullbackCompIso B S hS a' g').inv.app E).op).app
          ((smallEtaleDerivedModulePullback B S hS a').obj K') := by
  simp only [smallEtaleDerivedPullbackSheafHomMap_eq]
  exact CategoryTheory.PullbackInternalHom.pullbackHomMap_chart_square
    (smallEtaleDerivedModulePullbackCompIso B S hS a' g')
    (smallEtaleDerivedModulePullbackSquareIso B S hS a g' a' g₀ ha')
    (smallEtaleDerivedTensor B S hS X) (smallEtaleDerivedTensor B S hS X')
    (smallEtaleDerivedTensor B S hS Z) (smallEtaleDerivedTensor B S hS Z')
    (smallEtaleDerivedPullbackTensorIso a) (smallEtaleDerivedPullbackTensorIso a')
    (smallEtaleDerivedPullbackTensorIso g') (smallEtaleDerivedPullbackTensorIso g₀)
    (smallEtaleDerivedSheafHom B S hS X) (smallEtaleDerivedSheafHom B S hS X')
    (smallEtaleDerivedSheafHom B S hS Z) (smallEtaleDerivedSheafHom B S hS Z')
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS X')
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS Z)
    (smallEtaleDerivedTensorSheafHomAdjunction B S hS Z')
    (smallEtaleDerivedModulePullbackCompIso B S hS g₀ a)
    (smallEtaleDerivedModulePullbackCongr B S hS ha') rfl E K φ
    (tensorComparisonCompatible_smallEtaleDerivedPullbackTensorIso a g' a' g₀ ha' _ E)
    (fun v _ _ θ =>
      smallEtaleDerivedTensorSheafHomAdjunction_homEquiv_symm_dinatural B S hS Z' _ _ v θ)

end AlgebraicGeometry.Space

end
