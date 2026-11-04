module

public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionModuleEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveSetEssentialImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DualizingComplexGeometricStalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardSupport

/-!
# The essential image of the direct image of modules along an open immersion

Let `j : U ⟶ X` be an open immersion of algebraic spaces over a scheme `S`.  The direct image
`j_*` of `𝒪`-modules is fully faithful
(`AlgebraicGeometry.Space.fullyFaithfulModulePushforwardOfIsOpenImmersion`), so an
`𝒪_X`-module `G` is a direct image along `j` exactly when the unit `G ⟶ j_*j^*G` of the
adjunction of Stacks 03LU is invertible.  This file proves that it is invertible as soon as the
support of `G` is a closed subset of `|X|` contained in the image of `|U|`.

Invertibility is tested on the fibres at the geometric points of `X`.  At a geometric point lying
over the image of `|U|` the point comes from a geometric point of `U`; there the inverse image of
the unit is invertible by the triangle identity, the counit being invertible, the fibre of an
inverse image is the base change of the fibre at the image point (Stacks 05VQ), and the
homomorphism of stalk rings along the étale morphism `j` is bijective.  At a geometric point off
the image of `|U|` both fibres vanish: that of `G` because the point is off its support, and that
of `j_*j^*G` because its support lies in the closed set `Supp(G)`.

The closedness of the support cannot be dropped: if the support of `G` is contained in the image
of `|U|` without being closed in `|X|`, the direct image `j_*j^*G` may acquire support on its
closure, as for the extension by zero of `𝒪_U` along the inclusion of an open subscheme.

## Main results

* `AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_counit_of_isOpenImmersion`: the counit
  `j^*j_*F ⟶ F` is invertible.
* `AlgebraicGeometry.Space.isIso_modulePullbackAdjunction_unit_of_supportOfSheaf_subset`: the
  unit `G ⟶ j_*j^*G` is invertible when the support of `G` is closed and contained in the image
  of `|U|`.
* `AlgebraicGeometry.Space.supportOfSheaf_modulePushforward_subset_range_of_isClosed_image`: the
  support of a direct image `j_*F` lies in the image of `|U|` when the image of the support of
  `F` is closed.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 05VQ](https://stacks.math.columbia.edu/tag/05VQ)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {U X : AlgebraicSpaces B S hS}

/-- **The counit along an open immersion is invertible.**  For an open immersion
`j : U ⟶ X` of algebraic spaces and every `𝒪_U`-module `F`, the counit `j^*j_*F ⟶ F` of the
adjunction of Stacks 03LU is an isomorphism: the right adjoint `j_*` is fully faithful. -/
theorem isIso_modulePullbackAdjunction_counit_of_isOpenImmersion (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (F : Modules.{u, u} B S hS U.1 U.2) :
    IsIso ((modulePullbackAdjunction B S hS j).counit.app F) :=
  have := (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj).full
  have := (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj).faithful
  inferInstance

/-- A module is a direct image along an open immersion exactly when the unit of the adjunction
of Stacks 03LU is invertible at it, the direct image being fully faithful. -/
theorem essImage_modulePushforward_iff_isIso_unit_of_isOpenImmersion (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (G : Modules.{u, u} B S hS X.1 X.2) :
    (modulePushforward B S hS j).essImage G ↔
      IsIso ((modulePullbackAdjunction B S hS j).unit.app G) :=
  have := (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj).full
  have := (fullyFaithfulModulePushforwardOfIsOpenImmersion B S hS j hj).faithful
  ((modulePullbackAdjunction B S hS j).isIso_unit_app_iff_mem_essImage).symm

/-- **The unit along an open immersion is invertible on the fibre at a geometric point of the
open subspace.**  The inverse image of the unit is invertible, the fibre of an inverse image is
the base change of the fibre at the image point along the homomorphism of stalk rings, and that
homomorphism is bijective because `j` is étale. -/
theorem isIso_sheafModuleFiber_map_unit_of_isOpenImmersion (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (M : Modules.{u, u} B S hS X.1 X.2)
    (y : GeometricPoint B S hS U.1) :
    IsIso ((Stacks.sheafModuleFiber
      (etaleSitePoint B S hS X.1 (geometricPointMap j.hom y) X.2)
      (structureRingSheaf B S hS X)).map ((modulePullbackAdjunction B S hS j).unit.app M)) := by
  have htgt : IsIso ((ModuleCat.extendScalars (smallEtaleStalkPullbackRingMap B S hS j y)).map
      ((Stacks.sheafModuleFiberOfCommRing
        (etaleSitePoint B S hS X.1 (geometricPointMap j.hom y) X.2)
        (smallEtaleRingedTopos B S hS X).O).map
          ((modulePullbackAdjunction B S hS j).unit.app M))) :=
    Stacks.isIso_map_of_natIso_of_isIso (modulePullbackFiberIso B S hS j y)
      ((modulePullbackAdjunction B S hS j).unit.app M)
      (Stacks.isIso_functor_map
        (Stacks.sheafModuleFiberOfCommRing (etaleSitePoint B S hS U.1 y U.2)
          (smallEtaleRingedTopos B S hS U).O)
        ((modulePullback B S hS j).map ((modulePullbackAdjunction B S hS j).unit.app M))
        (Stacks.isIso_leftAdjoint_map_unit_app (modulePullbackAdjunction B S hS j) M
          (isIso_modulePullbackAdjunction_counit_of_isOpenImmersion B S hS j hj
            ((modulePullback B S hS j).obj M))))
  have hbij := bijective_smallEtaleStalkPullbackRingMap B S hS j
    (isEtale_of_isOpenImmersion B S hS hj) y
  have hker : ∀ a ∈ RingHom.ker (smallEtaleStalkPullbackRingMap B S hS j y), a = 0 :=
    fun a ha ↦ hbij.1 (by rw [RingHom.mem_ker.1 ha, map_zero])
  refine isIso_sheafModuleFiber_map_of_isIso_moduleStalkFunctor_map B S hS _ _ ?_
  refine Stacks.ModuleCat.isIso_of_isIso_extendScalars_map
    (smallEtaleStalkPullbackRingMap B S hS j y) hbij.2 _
    (fun a ha m ↦ by rw [hker a ha, zero_smul])
    (fun a ha n ↦ by rw [hker a ha, zero_smul]) htgt

/-- The fibre at a geometric point of a module vanishes when the point lies off the support. -/
theorem subsingleton_sheafModuleFiber_of_notMem_supportOfSheaf
    (M : Modules.{u, u} B S hS X.1 X.2) (x : GeometricPoint B S hS X.1)
    (hx : x.image ∉ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M)) :
    Subsingleton ((Stacks.sheafModuleFiber (etaleSitePoint B S hS X.1 x X.2)
      (structureRingSheaf B S hS X)).obj M) := by
  have hzero : Subsingleton (geometricModuleStalk B S hS X x M) := by
    rw [← not_nontrivial_iff_subsingleton]
    intro hnt
    exact hx ((mem_supportOfSheaf_iff_nontrivial_geometricModuleStalk B S hS X M x.image).mpr
      ⟨x, rfl, hnt⟩)
  refine ⟨fun c c' ↦ ?_⟩
  refine (Stacks.moduleStalkLargeFiberAddEquiv (etaleSitePoint B S hS X.1 x X.2)
    (smallEtaleRingedTopos B S hS X).O M).symm.injective ?_
  refine (geometricModuleStalkAddEquiv B S hS X x M).injective ?_
  exact hzero.elim _ _

/-- **The unit along an open immersion is invertible at a module supported on the open
subspace.**  For an open immersion `j : U ⟶ X` of algebraic spaces and an `𝒪_X`-module `G` whose
support is a closed subset of `|X|` contained in the image of `|U|`, the unit `G ⟶ j_*j^*G` of
the adjunction of Stacks 03LU is an isomorphism. -/
theorem isIso_modulePullbackAdjunction_unit_of_supportOfSheaf_subset (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    (hclosed : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G)))
    (hsupp : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) ⊆
      Set.range (pointsMap B S hS U.1 j.hom)) :
    IsIso ((modulePullbackAdjunction B S hS j).unit.app G) := by
  refine isIso_of_isIso_geometricModuleStalk B S hS X.1 X.2 (structureRingSheaf B S hS X)
    ((modulePullbackAdjunction B S hS j).unit.app G) fun x ↦ ?_
  by_cases hx : x.image ∈ Set.range (pointsMap B S hS U.1 j.hom)
  · obtain ⟨y, rfl⟩ := exists_geometricPoint_map_eq_of_mem_range_of_isOpenImmersion B S hS j hj x hx
    exact isIso_sheafModuleFiber_map_unit_of_isOpenImmersion B S hS j hj G y
  · have hG : x.image ∉ supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) :=
      fun h ↦ hx (hsupp h)
    have hjj : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        ((modulePushforward B S hS j).obj ((modulePullback B S hS j).obj G))) ⊆
        supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) :=
      supportOfSheaf_modulePushforward_subset_of_isClosed B S hS j _ _ hclosed
        (supportOfSheaf_modulePullback_subset_preimage B S hS j G)
    exact Stacks.isIso_of_subsingleton
      (subsingleton_sheafModuleFiber_of_notMem_supportOfSheaf B S hS G x hG)
      (subsingleton_sheafModuleFiber_of_notMem_supportOfSheaf B S hS _ x (fun h ↦ hG (hjj h))) _

/-- **A module supported on an open subspace is a direct image.**  For an open immersion
`j : U ⟶ X` of algebraic spaces, an `𝒪_X`-module whose support is a closed subset of `|X|`
contained in the image of `|U|` is isomorphic to a direct image along `j`, namely to that of its
restriction `j^*G`. -/
theorem essImage_modulePushforward_of_supportOfSheaf_subset (j : U ⟶ X)
    (hj : IsOpenImmersion B S hS j.hom) (G : Modules.{u, u} B S hS X.1 X.2)
    (hclosed : IsClosed (supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G)))
    (hsupp : supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj G) ⊆
      Set.range (pointsMap B S hS U.1 j.hom)) :
    (modulePushforward B S hS j).essImage G :=
  (essImage_modulePushforward_iff_isIso_unit_of_isOpenImmersion B S hS j hj G).2
    (isIso_modulePullbackAdjunction_unit_of_supportOfSheaf_subset B S hS j hj G hclosed hsupp)

/-- **The support of a direct image along an arbitrary morphism lies in the image when the image
of the support is closed.**  For `j : U ⟶ X` and an `𝒪_U`-module `F` such that the image of the
support of `F` in `|X|` is closed, the support of `j_*F` lies in the image of `|U|`. -/
theorem supportOfSheaf_modulePushforward_subset_range_of_isClosed_image (j : U ⟶ X)
    (F : Modules.{u, u} B S hS U.1 U.2)
    (himage : IsClosed (pointsMap B S hS U.1 j.hom ''
      supportOfSheaf B S hS U.1 ((SheafOfModules.toSheaf _).obj F))) :
    supportOfSheaf B S hS X.1
        ((SheafOfModules.toSheaf _).obj ((modulePushforward B S hS j).obj F)) ⊆
      Set.range (pointsMap B S hS U.1 j.hom) :=
  (supportOfSheaf_modulePushforward_subset_of_isClosed B S hS j F _ himage
    (Set.subset_preimage_image _ _)).trans (Set.image_subset_range _ _)

end AlgebraicGeometry.Space

end
