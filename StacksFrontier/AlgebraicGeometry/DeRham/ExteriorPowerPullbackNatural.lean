module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFunctorial
public import StacksFrontier.AlgebraicGeometry.DeRham.Complex.DifferentialFormsComp
public import StacksFrontier.AlgebraicGeometry.DeRham.ExteriorPowerPullback

/-!
# Naturality in the module of the pullback comparison for exterior algebras

The comparison `f^*(⋀ⁿ M) ⟶ ⋀ⁿ(f^*M)` of [Stacks, Tag 01CI] is natural in `M`: for a morphism
`φ : M ⟶ N` of sheaves of modules on `Y`, the square

```
f^*(⋀ⁿ M) --------> ⋀ⁿ(f^*M)
   |                    |
f^*(⋀ⁿ φ)            ⋀ⁿ(f^*φ)
   v                    v
f^*(⋀ⁿ N) --------> ⋀ⁿ(f^*N)
```

commutes.  Both vertical edges are taken to be degree-`n` components of arbitrary unital
homomorphisms of sheaves of graded algebras extending `φ`, respectively `f^*φ`, on the
degree-one generators; the universal property makes such a homomorphism unique, so this is no
weaker than the square for the canonical ones, and it lets a consumer holding a homomorphism
obtained some other way apply it without first identifying it with the canonical one.

## Main results

* `SheafOfModules.GradedAlgebra.pullbackComparison_map_unitalHom`: **a unital homomorphism on
  the source is absorbed by the comparison**: pulling back `u : A ⟶ A'` and following with the
  comparison attached to `κ'` gives the comparison attached to `f^*φ ≫ κ'`.  This is the
  source-side counterpart of
  `SheafOfModules.GradedAlgebra.pullbackComparison_comp_unitalHom`.
* `SheafOfModules.GradedAlgebra.pullbackComparison_natural`: **the naturality square**, for
  arbitrary unital homomorphisms extending `φ` and `f^*φ`.
* `AlgebraicGeometry.Scheme.Modules.exteriorPowerPullbackIso_natural` and
  `AlgebraicGeometry.Scheme.Modules.exteriorPowerPullbackIso_inv_natural`: the square for
  `AlgebraicGeometry.Scheme.Modules.exteriorPowerPullbackIso` and
  `AlgebraicGeometry.Scheme.Modules.exteriorPowerMap` on a scheme, and its inverse form.

## Implementation notes

The source-side absorption is proved exactly like the target-side one: by
`SheafOfModules.GradedAlgebra.pullbackComparison_unique`, whose three hypotheses — multiplicative,
unital, compatible with the degree-one generators — are checked on the pullback-unit sections,
where `AlgebraicGeometry.pullbackUnit_naturality` moves `f^*(u_m)` past the unit and leaves the
corresponding property of `u` to be applied.

With both absorption lemmas the naturality square is a comparison of two instances of
`pullbackComparison` with the same source algebra, whose generators `κ ≫ v₁` and `f^*φ ≫ κ'`
agree by the hypothesis on `v`; `SheafOfModules.GradedAlgebra.pullbackComparison_congr` then
identifies them, the square carrying no dependence on the square-zero proofs.

## References

* [Stacks Project, Tag 01CI](https://stacks.math.columbia.edu/tag/01CI)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory RingedSpaceModuleAdjunction Stacks.RingedSpace
open TopologicalSpace

universe u

namespace SheafOfModules.GradedAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {F F' : SheafOfModules.{u} (structureSheafRing Y)}
  {A A' : GradedAlgebra.{u, u} (structureSheafRing Y)}
  {ι : F ⟶ A.piece 1} {ι' : F' ⟶ A'.piece 1}
  {B B' : GradedAlgebra.{u, u} (structureSheafRing X)}
  {κ : (modulePullback f).obj F ⟶ B.piece 1}
  {κ' : (modulePullback f).obj F' ⟶ B'.piece 1}
  (hA : IsExteriorAlgebra A ι) (hκ' : SquareZero κ') {φ : F ⟶ F'}

/-- **The canonical comparison of Stacks 01CI absorbs a unital homomorphism on the source.**
Let `u : A ⟶ A'` be a unital homomorphism of sheaves of graded algebras extending
`φ : F ⟶ F'` on the degree-one generators.  Pulling `u` back and following it with the
comparison `f^*(A'_n) ⟶ B'_n` attached to a square-zero generator `κ'` of `B'` gives the
comparison attached to the square-zero generator `f^*φ ≫ κ'` of `B'`. -/
theorem pullbackComparison_map_unitalHom (u : UnitalHom A A') (hu : ι ≫ u.app 1 = φ ≫ ι')
    (hA' : IsExteriorAlgebra A' ι') (n : ℤ) :
    (modulePullback f).map (u.app n) ≫ pullbackComparison f hA' hκ' n =
      pullbackComparison f hA (hκ'.comp ((modulePullback f).map φ)) n := by
  have key : ∀ (m : ℤ) (U : (Opens Y.carrier)ᵒᵖ) (y : (A.piece m).val.obj U) (z),
      (u.app m).val.app U y = z →
      ((modulePullback f).map (u.app m) ≫ pullbackComparison f hA' hκ' m).val.app
          ((opensMap f).op.obj U) (pullbackUnit f (A.piece m) U y) =
        (pullbackComparison f hA' hκ' m).val.app ((opensMap f).op.obj U)
          (pullbackUnit f (A'.piece m) U z) := by
    rintro m U y _ rfl
    exact congrArg (fun z => (pullbackComparison f hA' hκ' m).val.app ((opensMap f).op.obj U) z)
      (pullbackUnit_naturality f (u.app m) U y)
  refine pullbackComparison_unique f hA (hκ'.comp ((modulePullback f).map φ))
    (fun m => (modulePullback f).map (u.app m) ≫ pullbackComparison f hA' hκ' m)
    (fun i j U a b => ?_) (fun U => ?_) (fun U s => ?_) n
  · exact (key _ U _ _ (u.map_mul i j U a b)).trans
      ((pullbackComparison_mul f hA' hκ' i j U _ _).trans
        (congrArg₂ (fun x y => ((B'.mul i j).app ((opensMap f).op.obj U) x) y)
          (key i U a _ rfl).symm (key j U b _ rfl).symm))
  · exact (key 0 U _ _ (u.map_one U)).trans (pullbackComparison_one f hA' hκ' U)
  · exact (key 1 U _ _ (Hom.congr_val_app hu U s)).trans
      ((pullbackComparison_generator f hA' hκ' U (φ.val.app U s)).trans
        (congrArg (fun z => κ'.val.app ((opensMap f).op.obj U) z)
          (pullbackUnit_naturality f φ U s).symm))

/-- **The comparison of Stacks 01CI is natural in the sheaf of modules.**  Let `A` be an
exterior algebra of `F` and `A'` one of `F'` on `Y`, let `B`, `B'` carry square-zero degree-one
generators of `f^*F`, `f^*F'`, let `u : A ⟶ A'` extend `φ : F ⟶ F'` and let `v : B ⟶ B'` extend
`f^*φ`.  Then the square formed by `f^*(u_n)`, `v_n` and the two comparisons commutes. -/
theorem pullbackComparison_natural (hκ : SquareZero κ) (hA' : IsExteriorAlgebra A' ι')
    (u : UnitalHom A A') (hu : ι ≫ u.app 1 = φ ≫ ι')
    (v : UnitalHom B B') (hv : κ ≫ v.app 1 = (modulePullback f).map φ ≫ κ') (n : ℤ) :
    (modulePullback f).map (u.app n) ≫ pullbackComparison f hA' hκ' n =
      pullbackComparison f hA hκ n ≫ v.app n := by
  rw [pullbackComparison_map_unitalHom f hA hκ' u hu hA' n,
    pullbackComparison_comp_unitalHom f hA hκ v n]
  exact pullbackComparison_congr f hA hv.symm _ _ n

end SheafOfModules.GradedAlgebra

namespace Stacks.PullbackExteriorAlgebra

open SheafOfModules.GradedAlgebra

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)
  {M M' : SheafOfModules.{u} (Stacks.RingedSpace.structureRingSheaf Y)}
  {A A' : SheafOfModules.GradedAlgebra.{u, u} (Stacks.RingedSpace.structureRingSheaf Y)}
  {ι : M ⟶ A.piece 1} {ι' : M' ⟶ A'.piece 1}
  {B B' : SheafOfModules.GradedAlgebra.{u, u} (Stacks.RingedSpace.structureRingSheaf X)}
  {κ : (pullbackFunctor f).obj M ⟶ B.piece 1}
  {κ' : (pullbackFunctor f).obj M' ⟶ B'.piece 1}

/-- **The isomorphism of [Stacks, Tag 01CI] for exterior algebras is natural in the module**:
`Stacks.PullbackExteriorAlgebra.pieceIso` commutes with the inverse image of a unital
homomorphism `u : A ⟶ A'` extending `φ : M ⟶ M'` and with any unital homomorphism
`v : B ⟶ B'` extending `f^*φ`. -/
theorem pieceIso_natural (hA : IsExteriorAlgebra A ι) (hA' : IsExteriorAlgebra A' ι')
    (hB : IsExteriorAlgebra B κ) (hB' : IsExteriorAlgebra B' κ') {φ : M ⟶ M'}
    (u : UnitalHom A A') (hu : ι ≫ u.app 1 = φ ≫ ι')
    (v : UnitalHom B B') (hv : κ ≫ v.app 1 = (pullbackFunctor f).map φ ≫ κ') (n : ℤ) :
    (pullbackFunctor f).map (u.app n) ≫ (pieceIso f A' hA' hB'.1 hB' n).hom =
      (pieceIso f A hA hB.1 hB n).hom ≫ v.app n :=
  pullbackComparison_natural f hA hB'.1 hB.1 hA' u hu v hv n

end Stacks.PullbackExteriorAlgebra

namespace AlgebraicGeometry.Scheme.Modules

open SheafOfModules.GradedAlgebra

variable {X' X : Scheme.{u}} (f : X' ⟶ X) {F F' : X.Modules} (φ : F ⟶ F')

/-- **The isomorphism `f^*(⋀ⁿ F) ≅ ⋀ⁿ(f^*F)` of [Stacks, Tag 01CI] is natural in `F`.** -/
theorem exteriorPowerPullbackIso_natural (n : ℤ) :
    (Scheme.Modules.pullback f).map (exteriorPowerMap φ n) ≫
        (exteriorPowerPullbackIso f F' n).hom =
      (exteriorPowerPullbackIso f F n).hom ≫
        exteriorPowerMap ((Scheme.Modules.pullback f).map φ) n :=
  pullbackComparison_natural f.toLRSHom.toShHom
    (isExteriorAlgebra_exteriorAlgebra F) (isExteriorAlgebra_exteriorAlgebra _).1
    (isExteriorAlgebra_exteriorAlgebra _).1 (isExteriorAlgebra_exteriorAlgebra F')
    ((isExteriorAlgebra_exteriorAlgebra F).map (isExteriorAlgebra_exteriorAlgebra F') φ)
    ((isExteriorAlgebra_exteriorAlgebra F).map_app_one _ φ)
    ((isExteriorAlgebra_exteriorAlgebra _).map (isExteriorAlgebra_exteriorAlgebra _)
      ((Scheme.Modules.pullback f).map φ))
    ((isExteriorAlgebra_exteriorAlgebra _).map_app_one _ _) n

/-- The naturality square of [Stacks, Tag 01CI] in the orientation in which the comparison
appears as an inverse. -/
theorem exteriorPowerPullbackIso_inv_natural (n : ℤ) :
    (exteriorPowerPullbackIso f F n).inv ≫ (Scheme.Modules.pullback f).map
          (exteriorPowerMap φ n) =
      exteriorPowerMap ((Scheme.Modules.pullback f).map φ) n ≫
        (exteriorPowerPullbackIso f F' n).inv := by
  rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv,
    exteriorPowerPullbackIso_natural f φ n]

end AlgebraicGeometry.Scheme.Modules

end
