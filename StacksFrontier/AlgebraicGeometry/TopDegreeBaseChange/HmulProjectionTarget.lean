module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.BaseChangeSectionsBijection
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionScalar
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.HmulProjectionPaste

/-!
# The multiplication identity of [Stacks, Tag 0EX3] (c), reduced to the cohomology upstairs

`Stacks.AlgebraicGeometry.TopDegreeBaseChange.bijective_baseChangeSectionsMap` asks for one
identity: that the identification
`…TopDegreeBaseChange.topDegreeFunctorObjIsoTargetSections` of the right-hand end
`Γ(R^d f''_* (h')^* F', W)` with the value of the endofunctor `Φ` of conclusion (b) at the
functions on `W` carries `Φ(multiplication by a)` to multiplication by `a`.

That identification is a composite of three factors, and only the **first** —
`…TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs`, which runs through the
projection formula and the Leray comparison — carries geometric content. The other two are a
transport along an equality of ring maps and the restriction of scalars of [Stacks, Tag 01XK]
over the affine open `W`. This file discharges those two: **once multiplication by `a` is known
to cross the first factor into multiplication by the pullback of `a` on the cohomology over
`f''⁻¹(W)`, the whole identity follows.**

## Main results

* `…TopDegreeBaseChange.hmul_of_mulUpstairs`: **the hypothesis `hmul` of
  `…TopDegreeBaseChange.bijective_baseChangeSectionsMap`, from the single square across
  `topDegreeFunctorObjIsoCohomologyUpstairs`.**

## Implementation notes

*Why the square across the first factor is taken as a hypothesis in the shape
`(ModuleCat.restrictScalars _).map (c • 𝟙 _)`.* The multiplication on the cohomology over
`f''⁻¹(W)` is multiplication by the pullback `c` of `a`, and what the two remaining factors need
of it is only that it is a scalar: transport along an equality of ring maps commutes with it
(`…TopDegreeBaseChange.restrictScalars_map_comp_eqToHom`), and a scalar multiple of an identity
is carried across a linear map by its linearity. No geometry is used here, and the hypothesis
names `c` with its defining equation so that a consumer may supply whichever spelling of the
pullback it has.

*The two scalars agree because the two ring maps do.* The transport of the second factor is
along `…TopDegreeBaseChange.appTop_comp_eq_appTop_comp_algebraMap`, the equality of the two
readings of the action of the functions on `V`; multiplication by `c` is the same morphism on
either side of it, which is exactly what `restrictScalars_map_comp_eqToHom` says.

*Why the two steps are proved at variable level.* The objects involved are values of a right
derived functor at a tensor product of module sheaves, and a goal mentioning them is large
enough that `rw` and `simp only` fail to locate even `CategoryTheory.Category.assoc`. The
pasting of the squares (`…TopDegreeBaseChange.comp_two_squares`) and the scalar step
(`smul_restrictScalars_comp_map`) are therefore stated for bare variables, and the
identification of their instances with the factors of
`…TopDegreeBaseChange.topDegreeFunctorObjIsoTargetSections` is left to the kernel.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.AffineBase
open Stacks.RingedSpace
open scoped ChangeOfRings

universe u

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

/-- **A linear map out of a doubly restricted module carries multiplication by the image scalar
to multiplication by the scalar.** Let `χ : R₀ →+* A`, `σ : A →+* A'` and `υ : A' →+* B` be ring
maps, let `H` be a `B`-module and `T` an `A`-module, and let `ι` be an `A`-linear map from `H`
with its scalars restricted along `υ` and then `σ` to `T`. For `a : A` with image `c = υ (σ a)`,
multiplication by `c` on `H` crosses `ι` into multiplication by `a` on `T`, both read over
`R₀`.

On an element the two sides are `ι (c • x)` and `a • ι x`, equal because the `A`-action on the
restricted module is through `υ ∘ σ` and `ι` is `A`-linear. -/
private theorem smul_restrictScalars_comp_map {R₀ A A' B : Type u} [CommRing R₀] [CommRing A]
    [CommRing A'] [CommRing B] (χ : R₀ →+* A) (σ : A →+* A') (υ : A' →+* B)
    {H : ModuleCat.{u} B} {T : ModuleCat.{u} A}
    (ι : (ModuleCat.restrictScalars σ).obj ((ModuleCat.restrictScalars υ).obj H) ⟶ T)
    (a : A) (c : B) (hc : υ (σ a) = c) :
    (ModuleCat.restrictScalars (υ.comp (σ.comp χ))).map (c • 𝟙 H) ≫
        (ModuleCat.restrictScalars χ).map ι =
      (ModuleCat.restrictScalars χ).map ι ≫
        (ModuleCat.restrictScalars χ).map (a • 𝟙 T) := by
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  subst hc
  have key : ∀ y : ↑((ModuleCat.restrictScalars σ).obj
      ((ModuleCat.restrictScalars υ).obj H)),
      (ModuleCat.Hom.hom ι) (a • y) = a • (ModuleCat.Hom.hom ι) y :=
    fun y => map_smul (ModuleCat.Hom.hom ι) a y
  exact key x

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] AlgebraicGeometry.modulesLinear baseSectionsAlgebra

variable {X'' Y'' : Scheme.{u}}
  (S : Stacks.AlgebraicGeometry.TopDegreeBaseChangeSituation.{u})
  (F' : S.X'.Modules) [F'.IsQuasicoherent]
  (h' : X'' ⟶ S.X') (f'' : X'' ⟶ Y'') (h : Y'' ⟶ S.Y') (hsq : IsPullback h' f'' S.f' h)
  {V : S.Y'.Opens} [IsAffine (V : Scheme)] {W : Y''.Opens} [IsAffine (W : Scheme)]
  (hWV : W ≤ h ⁻¹ᵁ V)

/-- **The hypothesis `hmul` of `…TopDegreeBaseChange.bijective_baseChangeSectionsMap`, from the
square across the cohomology upstairs.** Let `a` be a function on the affine open `W` of `Y''`
and `c` its pullback to `f''⁻¹(W)`. If the identification
`…TopDegreeBaseChange.topDegreeFunctorObjIsoCohomologyUpstairs` of the value of the endofunctor
`Φ` of [Stacks, Tag 0EX3] (b) at the functions on `W` with the degree-`d` cohomology of
`((h')^* F')|` over `f''⁻¹(W)` carries `Φ(multiplication by a)` to multiplication by `c`, then
the full identification `…TopDegreeBaseChange.topDegreeFunctorObjIsoTargetSections` of that
value with `Γ(R^d f''_* (h')^* F', W)` carries `Φ(multiplication by a)` to multiplication by
`a`.

The two factors discharged here are a transport along
`…TopDegreeBaseChange.appTop_comp_eq_appTop_comp_algebraMap` and the restriction of scalars of
[Stacks, Tag 01XK] over `W`; neither sees the module, so both commute with a scalar
multiplication. -/
theorem hmul_of_mulUpstairs (a : Γ(Y'', W)) (c : Γ((f'' ⁻¹ᵁ W : Scheme), ⊤))
    (hc : (f'' ∣_ W).appTop.hom ((Scheme.Opens.topIso W).inv.hom a) = c)
    (hup : ((S.restrictBase V).topDegreeFunctor
            ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
              (inferInstance :
                ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                  F').IsQuasicoherent)⟩).map
            (mulLeftRestrictScalars ((h.appLE V W hWV).hom.comp
              (Scheme.Opens.topIso V).hom.hom) a) ≫
          (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).hom =
        (topDegreeFunctorObjIsoCohomologyUpstairs S F' h' f'' h hsq hWV).hom ≫
          (ModuleCat.restrictScalars
              ((h'.resLE (S.f' ⁻¹ᵁ V) (f'' ⁻¹ᵁ W)
                  (preimage_le_preimage_of_isPullback hsq hWV)).appTop.hom.comp
                (algebraMap (S.restrictBase V).affineBaseRing
                  Γ((((S.restrictBase V).affineBaseOver)).left, ⊤)))).map
            (c • 𝟙 (((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerivedPlus
              (S.d : ℤ)).obj
                ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
                  ((Scheme.Modules.pullback h').obj F'))))) :
    ((S.restrictBase V).topDegreeFunctor
          ⟨(Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj F',
            (inferInstance :
              ((Scheme.Modules.restrictFunctor (S.f' ⁻¹ᵁ V).ι).obj
                F').IsQuasicoherent)⟩).map
          (mulLeftRestrictScalars ((h.appLE V W hWV).hom.comp
            (Scheme.Opens.topIso V).hom.hom) a) ≫
        (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom =
      (topDegreeFunctorObjIsoTargetSections S F' h' f'' h hsq hWV).hom ≫
        (ModuleCat.restrictScalars ((h.appLE V W hWV).hom.comp
            (Scheme.Opens.topIso V).hom.hom)).map
          (a • 𝟙 (ModuleCat.of Γ(Y'', W)
            Γ(((Scheme.Modules.pushforward f'').rightDerivedPlus (S.d : ℤ)).obj
              ((Scheme.Modules.pullback h').obj F'), W))) :=
  comp_two_squares hup
    (comp_two_squares (restrictScalars_map_comp_eqToHom
      (appTop_comp_eq_appTop_comp_algebraMap S h' f'' h hsq hWV).symm
      (c • 𝟙 (((moduleGlobalSections (f'' ⁻¹ᵁ W : Scheme)).rightDerivedPlus (S.d : ℤ)).obj
        ((Scheme.Modules.restrictFunctor (f'' ⁻¹ᵁ W).ι).obj
          ((Scheme.Modules.pullback h').obj F')))))
      (smul_restrictScalars_comp_map
        ((h.appLE V W hWV).hom.comp (Scheme.Opens.topIso V).hom.hom)
        (Scheme.Opens.topIso W).inv.hom (f'' ∣_ W).appTop.hom
        (targetSectionsIsoCohomology S F' h' f''
          (quasiCompact_of_isPullback S h' f'' h hsq)
          (quasiSeparated_of_isPullback S h' f'' h hsq) W).hom a c hc))

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
