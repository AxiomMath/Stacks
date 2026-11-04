module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsSchemeComparisonMapSections

/-!
# The naturality square of Stacks 04CS for the mate comparison of Stacks 03LC (1)

Let `ψ : U ⟶ V` and `χ : V ⟶ W` be composable morphisms of schemes of the site, with `ψ̃`, `χ̃` the
morphisms of represented algebraic spaces they induce. The comparison map of Stacks 04CX of `ψ̃`
is compared with the Zariski comparison map `ψ^*Ω_{V/W} ⟶ Ω_{U/W}` of Stacks 01UV through a
commuting square, which involves an isomorphism of the two composite inverse images of
Stacks 03LC (1). The isomorphism used is
`AlgebraicGeometry.Space.representedAssociatedModulePullbackMateIso`, the mate of the comparison
`AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso` of the two composite right
adjoints.

## Main results

* `CategoryTheory.comp_hom_app_of_eq_comp_inv_app`: if `a = b ≫ e.inv.app X` for a natural
  isomorphism `e`, then `a ≫ e.hom.app X = b`.
* `AlgebraicGeometry.Space.representedAssociatedModulePullbackMate_square_of_postcomp`: the
  naturality square for the mate commutes provided the two morphisms out of `Ω_{V/W}` obtained by
  transposing its sides induce the same `W`-derivation of `𝒪`.
* `AlgebraicGeometry.Space.mono_pullbackDifferentialsMap_of_mate_square`: given that square, the
  comparison map of Stacks 04CX of `ψ̃` is a monomorphism whenever the Zariski comparison map of
  Stacks 01UV of `ψ` is.

## References

* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS)
* [Stacks Project, Tag 04CX](https://stacks.math.columbia.edu/tag/04CX)
* [Stacks Project, Tag 01UV](https://stacks.math.columbia.edu/tag/01UV)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03LC](https://stacks.math.columbia.edu/tag/03LC)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08H8](https://stacks.math.columbia.edu/tag/08H8)
-/


@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace CategoryTheory

/-- For a natural isomorphism `e : F ≅ G`, an object `X` and morphisms `a : Z ⟶ F.obj X`,
`b : Z ⟶ G.obj X`, if `a = b ≫ e.inv.app X` then `a ≫ e.hom.app X = b`. -/
theorem comp_hom_app_of_eq_comp_inv_app {C D : Type*} [Category C] [Category D]
    {F G : C ⥤ D} (e : F ≅ G) (X : C) {Z : D} {a : Z ⟶ F.obj X} {b : Z ⟶ G.obj X}
    (h : a = b ≫ e.inv.app X) : a ≫ e.hom.app X = b := by
  rw [h, Category.assoc, Iso.inv_hom_id_app, Category.comp_id]

end CategoryTheory

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {U V W : BigFppfOver B S hS}

/-- The naturality square of Stacks 04CS for the mate comparison of Stacks 03LC (1). Write `ψ̃`,
`χ̃` for the morphisms of represented algebraic spaces of `ψ : U ⟶ V` and `χ : V ⟶ W`. The square

```
ψ̃^*((Ω_{V/W})^a) ---- mate of 03LC (1) ----> (ψ^*Ω_{V/W})^a
        |                                           |
   ψ̃^*(04CS of χ)                       (Zariski c_ψ of 01UV)^a
        v                                           v
    ψ̃^*Ω_{χ̃} ------- c_ψ̃ then 04CS of ψ ≫ χ ------> (Ω_{U/W})^a
```

commutes as soon as its two sides, transposed across the composite adjunction of Stacks 03DU (4)
for `V` followed by the inverse image of Stacks 03LU along `ψ̃` and compared through the inverse
of `AlgebraicGeometry.Space.representedRestrictModuleBaseChangeIso`, induce the same `W`-derivation
of `𝒪` on the small Zariski site of the scheme underlying `V`. -/
theorem representedAssociatedModulePullbackMate_square_of_postcomp (ψ : U ⟶ V) (χ : V ⟶ W)
    (h : (Scheme.Hom.universalRelativeDerivation
            ((BigFppfOver.toScheme B S hS).map χ)).postcomp
          ((representedAssociatedModulePullbackAdjunction B S hS ψ).homEquiv _ _
            ((representedAssociatedModule B S hS U (schemeSpace U).property).map
              (schemeChartDifferentialsMap B S hS ψ χ))).val =
        (Scheme.Hom.universalRelativeDerivation
            ((BigFppfOver.toScheme B S hS).map χ)).postcomp
          ((representedAssociatedModuleAdjunction B S hS V).homEquiv _ _
              (representedDifferentialsComparison B S hS χ ≫
                (modulePullbackAdjunction B S hS (schemeSpaceMap ψ)).homEquiv _ _
                  (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
                    (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom)) ≫
            (representedRestrictModuleBaseChangeIso B S hS ψ).inv.app
              (representedRelativeDifferentials B S hS (ψ ≫ χ))).val) :
    (representedAssociatedModulePullbackMateIso B S hS ψ).hom.app
          (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ)) ≫
        (representedAssociatedModule B S hS U (schemeSpace U).property).map
          (schemeChartDifferentialsMap B S hS ψ χ) =
      (modulePullback B S hS (schemeSpaceMap ψ)).map
          (representedDifferentialsComparison B S hS χ) ≫
        pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
          (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom := by
  have key := Scheme.Hom.eq_of_postcomp_eq_universalRelativeDerivation
    ((BigFppfOver.toScheme B S hS).map χ) h
  refine ((representedAssociatedModuleSpacePullbackAdjunction B S hS ψ).homEquiv _ _).injective ?_
  refine Eq.trans (homEquiv_comp_conjugateEquiv
      (representedAssociatedModulePullbackAdjunction B S hS ψ)
      (representedAssociatedModuleSpacePullbackAdjunction B S hS ψ)
      (representedAssociatedModulePullbackMateIso B S hS ψ).hom _ _ _).symm ?_
  rw [conjugateEquiv_representedAssociatedModulePullbackMateIso_hom,
    homEquiv_representedAssociatedModuleSpacePullback]
  exact comp_hom_app_of_eq_comp_inv_app _ _ key

/-- Given the naturality square for the mate comparison of Stacks 03LC (1), the comparison map of
Stacks 04CX of `ψ`, read between represented algebraic spaces over the represented algebraic
space of `W`, is a monomorphism whenever the Zariski comparison map `ψ^*Ω_{V/W} ⟶ Ω_{U/W}` of
Stacks 01UV is. -/
theorem mono_pullbackDifferentialsMap_of_mate_square (ψ : U ⟶ V) (χ : V ⟶ W)
    (hsq : (representedAssociatedModulePullbackMateIso B S hS ψ).hom.app
            (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ)) ≫
          (representedAssociatedModule B S hS U (schemeSpace U).property).map
            (schemeChartDifferentialsMap B S hS ψ χ) =
        (modulePullback B S hS (schemeSpaceMap ψ)).map
            (representedDifferentialsComparison B S hS χ) ≫
          pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
            (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom)
    (hm : Mono (schemeChartDifferentialsMap B S hS ψ χ)) :
    Mono (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ)) := by
  have : Limits.PreservesFiniteLimits
      (representedAssociatedModule B S hS U (schemeSpace U).property) :=
    preservesFiniteLimits_representedAssociatedModule B S hS U
      (isAlgebraicSpace_yoneda B S hS U)
  have : (representedAssociatedModule B S hS U
      (schemeSpace U).property).PreservesMonomorphisms :=
    CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape _
  have := hm
  have : IsIso ((modulePullback B S hS (schemeSpaceMap ψ)).map
      (representedDifferentialsComparison B S hS χ)) :=
    ((modulePullback B S hS (schemeSpaceMap ψ)).mapIso
      (sheafOfDifferentialsRepresentedIso B S hS χ).symm).isIso_hom
  have : IsIso ((representedAssociatedModulePullbackMateIso B S hS ψ).hom.app
      (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ))) :=
    inferInstance
  have hA : Mono ((representedAssociatedModule B S hS U (schemeSpace U).property).map
      (schemeChartDifferentialsMap B S hS ψ χ)) := Functor.map_mono _ _
  have hleft := (mono_comp_iff_of_isIso
    ((representedAssociatedModulePullbackMateIso B S hS ψ).hom.app
      (Scheme.Hom.relativeDifferentials ((BigFppfOver.toScheme B S hS).map χ))) _).mpr hA
  have : Mono (pullbackDifferentialsMap B S hS (schemeSpaceMap ψ) (schemeSpaceMap χ) ≫
      (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom) := by
    refine (mono_comp_iff_of_isIso ((modulePullback B S hS (schemeSpaceMap ψ)).map
      (representedDifferentialsComparison B S hS χ)) _).mp ?_
    rw [← hsq]
    exact hleft
  exact mono_of_mono _ (sheafOfDifferentialsRepresentedIso B S hS (ψ ≫ χ)).hom

end AlgebraicGeometry.Space

end
