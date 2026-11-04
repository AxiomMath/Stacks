module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.InternalHomPullbackHomComplexRetract
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComplexCoherence

/-!
# The cochain-level comparison of Hom complexes at the structure sheaf

Let `h : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces.
`Stacks.Cohomology.DerivedInternalHomPullback.pullbackHomComplexMap` is the canonical map of
complexes

`h^*𝓗om^•_{𝒪_Y}(E, F) ⟶ 𝓗om^•_{𝒪_X}(h^*E, h^*F)`

at the internal Hom complex of Tag 0A8Z. This file proves it invertible at `E = 𝒪_Y[0]`, the
monoidal unit of the complexes of `𝒪_Y`-modules, with no hypothesis on `h` or on `F`, and more
generally at every direct summand of a finite free `𝒪_Y`-module in degree zero.

## Main definitions

* `rightUnitorAtUnitComplex`: the right unit constraint `Tot(W ⊗_{𝒪_Z} 𝒪_Z[0]) ≅ W`, the right
  unitor of the monoidal structure on complexes.
* `rightUnitorAtPullbackUnitComplex`: the right unit constraint
  `Tot(W ⊗_{𝒪_X} h^*(𝒪_Y[0])) ≅ W`, the right unitor composed with the unit comparison
  `ε : 𝒪_X[0] ≅ h^*(𝒪_Y[0])` of the monoidal lift of `h^*` to complexes.

## Main results

* `rightUnitorAtUnitComplex_naturality`, `rightUnitorAtPullbackUnitComplex_naturality`: the two
  right unit constraints are natural.
* `pullbackTensorComplexNatIso_rightUnitorCoherence`: the comparison of total tensor complexes of
  Tag 01CD is compatible with the two right unit constraints.
* `isIso_pullbackHomComplexMap_unitComplex`: the cochain-level comparison is invertible at
  `E = 𝒪_Y[0]`, for every morphism of ringed spaces and every `F`.
* `isIso_pullbackHomComplexMap_of_splitSumUnitComplex`: the cochain-level comparison is
  invertible at every direct summand of a finite free `𝒪_Y`-module in degree zero.

## References

* [Stacks Project, Tag 0GM7](https://stacks.math.columbia.edu/tag/0GM7)
* [Stacks Project, Tag 08I3](https://stacks.math.columbia.edu/tag/08I3)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Prod
open Stacks.Cohomology.DerivedPullbackTensor

namespace Stacks.Cohomology.DerivedInternalHomPullback

universe u

attribute [local instance_reducible] StacksDraft.KFlat.modulePullback
  CategoryTheory.sheafCompose AlgebraicGeometry.SheafedSpace.sheaf

-- The monoidal structures on `Mod(𝒪_Z)` and on `Comp(Mod(𝒪_Z))`, the abelian structure on
-- `Mod(𝒪_Z)`, and the monoidal structure on the degreewise pullback.
attribute [local instance] abelianModulesSheafTensor monoidalModules symmetricModules
  monoidalPreadditiveModules monoidalClosedModules hasTensorModules monoidalComplexes
  modulePullback_preservesAntidiagonalCoproducts liftMonoidal

-- The additivity of `⊗_{𝒪_Z}` in each variable and the existence of the total tensor
-- complexes, for the open-cover site of a space.
attribute [local instance 10000] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

/-! ### A reassociation lemma -/

/-- **A composite in which two isomorphisms cancel against their inverses.** If
`r = k' ≫ q ≫ m`, `k ≫ k' = 𝟙` and `p ≫ q = 𝟙`, then `p ≫ k ≫ r = m`. -/
private lemma cancel_two {C : Type*} [Category C] {A B B' D : C}
    (p : A ⟶ B) (q : B ⟶ A) (k : B ⟶ B') (k' : B' ⟶ B) (r : B' ⟶ D) (m : A ⟶ D)
    (hr : r = k' ≫ q ≫ m) (hk : k ≫ k' = 𝟙 B) (hpq : p ≫ q = 𝟙 A) :
    p ≫ k ≫ r = m := by
  rw [hr, ← Category.assoc k, hk, Category.id_comp, ← Category.assoc, hpq, Category.id_comp]

/-! ### The right unitor at the structure sheaf -/

section Unit

variable (Z : RingedSpace.{u, u})

/-- **The right unit constraint `Tot(W ⊗_{𝒪_Z} 𝒪_Z[0]) ≅ W` at the total tensor complex.** It is
the right unitor of the monoidal structure on complexes of `𝒪_Z`-modules, the total tensor complex
of the pair functor being the monoidal product. -/
def rightUnitorAtUnitComplex
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) :
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z).sheaf)).obj
        (W, 𝟙_ (CochainComplex
          (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ)) ≅ W :=
  ρ_ W

/-- The right unit constraint `rightUnitorAtUnitComplex` at the structure sheaf is natural in
`W`. -/
theorem rightUnitorAtUnitComplex_naturality
    (W W' : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ) (g : W ⟶ W') :
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Z).sheaf)).map
          (g ×ₘ 𝟙 (𝟙_ (CochainComplex
            (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Z) ℤ))) ≫
        (rightUnitorAtUnitComplex Z W').hom =
      (rightUnitorAtUnitComplex Z W).hom ≫ g := by
  rw [totalComplexPair_map]
  exact MonoidalCategory.rightUnitor_naturality g

end Unit

/-! ### The right unitor against the pullback of the structure sheaf -/

section PullbackUnit

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- **The right unit constraint `Tot(W ⊗_{𝒪_X} h^*(𝒪_Y[0])) ≅ W`.** It is `W ◁ ε⁻¹` followed by
the right unitor `ρ_ W`, where `ε = CategoryTheory.Functor.Monoidal.εIso (pullbackComplex h)` is
the unit comparison `𝒪_X[0] ≅ h^*(𝒪_Y[0])` of the monoidal lift of `h^*` to complexes. -/
def rightUnitorAtPullbackUnitComplex
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X).sheaf)).obj
        (W, (pullbackComplex h).obj (𝟙_ (CochainComplex
          (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))) ≅ W :=
  whiskerLeftIso W (CategoryTheory.Functor.Monoidal.εIso (pullbackComplex h)).symm ≪≫ ρ_ W

/-- The morphism underlying `rightUnitorAtPullbackUnitComplex h W` is `W ◁ ε⁻¹ ≫ (ρ_ W).hom`. -/
theorem rightUnitorAtPullbackUnitComplex_hom
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) :
    (rightUnitorAtPullbackUnitComplex h W).hom =
      W ◁ (CategoryTheory.Functor.Monoidal.εIso (pullbackComplex h)).inv ≫ (ρ_ W).hom :=
  rfl

/-- The right unit constraint `rightUnitorAtPullbackUnitComplex h` against `h^*(𝒪_Y[0])` is
natural in `W`. -/
theorem rightUnitorAtPullbackUnitComplex_naturality
    (W W' : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ) (g : W ⟶ W') :
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X).sheaf)).map
          (g ×ₘ 𝟙 ((pullbackComplex h).obj (𝟙_ (CochainComplex
            (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)))) ≫
        (rightUnitorAtPullbackUnitComplex h W').hom =
      (rightUnitorAtPullbackUnitComplex h W).hom ≫ g := by
  rw [totalComplexPair_map, rightUnitorAtPullbackUnitComplex_hom,
    rightUnitorAtPullbackUnitComplex_hom]
  exact Stacks.Cohomology.DerivedInternalHomPullback.paste_two _ _ _ _ _ _ _
    (MonoidalCategory.whisker_exchange g
      (CategoryTheory.Functor.Monoidal.εIso (pullbackComplex h)).inv).symm
    (MonoidalCategory.rightUnitor_naturality g)

/-- **The comparison of total tensor complexes of Tag 01CD is compatible with the right unit
constraints.** The component of `pullbackTensorComplexNatIso h` at `(W, 𝒪_Y[0])` followed by the
right unit constraint `rightUnitorAtPullbackUnitComplex h` at `h^*W` is `h^*` of the right unit
constraint `rightUnitorAtUnitComplex Y W`. -/
theorem pullbackTensorComplexNatIso_rightUnitorCoherence
    (W : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    (pullbackTensorComplexNatIso h).hom.app
          (W, 𝟙_ (CochainComplex
            (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)) ≫
        (rightUnitorAtPullbackUnitComplex h ((pullbackComplex h).obj W)).hom =
      (pullbackComplex h).map (rightUnitorAtUnitComplex Y W).hom := by
  rw [rightUnitorAtPullbackUnitComplex_hom]
  exact cancel_two _ _ _ _ _ _ (pullbackTensorComplexIso_rightUnitor h W)
    (MonoidalCategory.whiskerLeftIso ((pullbackComplex h).obj W)
      (CategoryTheory.Functor.Monoidal.εIso (pullbackComplex h)).symm).hom_inv_id
    (pullbackTensorComplexIsoOfIsIso h W
      (𝟙_ (CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))).hom_inv_id

end PullbackUnit

/-! ### The comparison at the structure sheaf -/

section Base

variable {X Y : RingedSpace.{u, u}} (h : X ⟶ Y)

/-- **The cochain-level comparison of Hom complexes is invertible at `E = 𝒪_Y[0]`.**

`h^*𝓗om^•_{𝒪_Y}(𝒪_Y[0], F) ⟶ 𝓗om^•_{𝒪_X}(h^*(𝒪_Y[0]), h^*F)`

is an isomorphism of complexes for every morphism of ringed spaces `h` and every complex `F` of
`𝒪_Y`-modules. No flatness, no finite tor dimension, no bound on `F`. -/
theorem isIso_pullbackHomComplexMap_unitComplex
    (F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) :
    IsIso (pullbackHomComplexMap h
      (𝟙_ (CochainComplex
        (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)) F) :=
  Transpose.isIso_homComparison_of_tensorUnit (pullbackComplex h)
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.sheafHomComplexBifunctor
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (Y).sheaf))
    (totalComplexPair (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} (X).sheaf))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite Y))
    (AlgebraicGeometry.RingedSite.curryHomEquivPair
      (AlgebraicGeometry.RingedSpace.ringedSite X))
    (pullbackTensorComplexNatIso h)
    (curryHomEquivPair_naturality_source Y) (curryHomEquivPair_naturality_source X)
    (𝟙_ (CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))
    (rightUnitorAtUnitComplex Y) (rightUnitorAtPullbackUnitComplex h)
    (rightUnitorAtUnitComplex_naturality Y) (rightUnitorAtPullbackUnitComplex_naturality h)
    (pullbackTensorComplexNatIso_rightUnitorCoherence h) F

/-- **The cochain-level comparison is invertible at every direct summand of a finite free
`𝒪_Y`-module in degree zero, unconditionally.**

The summand hypothesis is spelled as a finite split family: `E` carries `ι j : 𝒪_Y[0] ⟶ E` and
`π j : E ⟶ 𝒪_Y[0]` indexed by a finite type with `∑ j, π j ≫ ι j = 𝟙 E`. This is equivalent to the
retract spelling: from `i : E ⟶ (𝒪_Y[0])^{⊕ m}` and `r` with `i ≫ r = 𝟙 E` one takes
`ι j = biproduct.ι j ≫ r` and `π j = i ≫ biproduct.π j`, whose sum is `i ≫ 𝟙 ≫ r` by
`CategoryTheory.Limits.biproduct.total`; conversely a split family over `Fin m` exhibits `E` as a
summand of the `m`-fold biproduct. -/
theorem isIso_pullbackHomComplexMap_of_splitSumUnitComplex
    (F : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)
    {J : Type*} [Fintype J]
    {E : CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ}
    (ι : ∀ _ : J, 𝟙_ (CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ) ⟶ E)
    (π : ∀ _ : J, E ⟶ 𝟙_ (CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ))
    (hsum : ∑ j : J, π j ≫ ι j = 𝟙 E) :
    IsIso (pullbackHomComplexMap h E F) :=
  isIso_pullbackHomComplexMap_of_splitSum h F
    (fun _ : J => 𝟙_ (CochainComplex
      (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules Y) ℤ)) ι π hsum
    (fun _ => isIso_pullbackHomComplexMap_unitComplex h F)

end Base

end Stacks.Cohomology.DerivedInternalHomPullback

end
