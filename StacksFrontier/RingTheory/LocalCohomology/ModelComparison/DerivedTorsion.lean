module

public import StacksFrontier.AlgebraicGeometry.Duality.TorsionCounit.KInjectiveCriterion
public import StacksFrontier.RingTheory.LocalCohomology.DepthVanishing.Supported
public import StacksFrontier.RingTheory.LocalCohomology.Sweep.ClosedSupportColimit

/-!
# Sections with support in `V(I)` and the derived `I`-power-torsion functor agree

Let `A` be a commutative ring and `I ⊆ A` a finitely generated ideal. This library carries two
constructions of derived torsion on `D(A)` which have never been compared.

* `Stacks.LocalCohomology.derivedSectionsWithSupportIn A T`, for a subset `T ⊆ Spec(A)`, is the
  total right derived functor of the degree-zero `T`-supported sections `Γ_T`, computed inside
  `ModuleCat A`.
* `Dualizing.derivedPowerTorsion A I hI` is the total right derived functor of the
  `I`-power-torsion submodule functor `Γ_I`, computed as a functor into the derived category of
  the abelian category of `I`-power-torsion modules.

They are the same functor. On modules, `Γ_{V(I)}` *is* `Γ_I`: the defining supremum over the
ideals `J` with `V(J) ⊆ V(I)` collapses onto `J = I`, because `V(J) ⊆ V(I)` means `I ⊆ √J` and a
finitely generated `I` then has `I^n ⊆ J`, so `J`-power torsion is `I`-power torsion. Derived
functors of isomorphic functors are isomorphic, and both constructions are computed by K-injective
resolutions, so the identification is a natural isomorphism of functors `D(A) ⥤ D(A)` rather than
an objectwise statement.

Composing with the comparison of [Stacks, Tag 0A6U] — already in the library as
`Dualizing.compareTorsionFunctors` — this produces the canonical map from `RΓ_{V(I)}` to
  local
cohomology `RΓ_Z` in the sense of [Stacks, Tag 0A6Q], the right adjoint of the inclusion of
`D_{I^∞-torsion}(A)`.

**That last map is not invertible in general, and no claim here says it is.** The source is
explicit: of the two functors it writes

> this functor does not deserve the name local cohomology unless the ring `A` is Noetherian
> [...] the notation `RΓ_Z` is going to be used for a different functor [...] which agrees with
> the functor `RΓ_I` only (as far as we know) in case `A` is Noetherian

and, at the construction of `RΓ_Z`,

> By Lemma 0A6P this functor will in general **not** be equal to `RΓ_I(-)` even viewed as
> functors into `D(A)`.

The obstruction is [Stacks, Tag 0A6P]: the comparison `D(I^∞-torsion) → D_{I^∞-torsion}(A)` is
not an equivalence, witnessed over `A = ℤ[f, x, xₙ]/(fx, fⁿxₙ - x)` with `I = (f)`, where
`Ext²` does not surject. Invertibility for Noetherian `A` is [Stacks, Tag 0955], which this
library does not have; see the implementation notes.

## Main results

* `Stacks.LocalCohomology.sectionsWithSupportIn_zeroLocus_eq_primaryComponent` — on modules,
  `Γ_{V(I)} = Γ_I` for a finitely generated `I`.
* `Stacks.LocalCohomology.sectionsWithSupportInFunctorIsoPowerTorsionFunctor` — the same,
  naturally in the module.
* `Stacks.LocalCohomology.derivedSectionsWithSupportInIsoDerivedPowerTorsion` — **the
  comparison**: `RΓ_{V(I)} ≅ RΓ_I` as functors `D(A) ⥤ D(A)`.
* `Stacks.LocalCohomology.derivedPowerTorsionProperty_derivedSectionsWithSupportIn` —
  `RΓ_{V(I)}(K)` has `I`-power-torsion cohomology, so it lands in the subcategory that local
  cohomology coreflects onto.
* `Stacks.LocalCohomology.compareSectionsWithSupportLocalCohomology` — the resulting canonical
  natural transformation `RΓ_{V(I)} ⟶ RΓ_Z` of [Stacks, Tag 0A6U]. A natural transformation, not
  an isomorphism.

## Implementation notes

The comparison is obtained from the universal property of a right derived functor: the natural
transformation is `Functor.rightDerivedDesc` applied to the unit of `RΓ_I` transported along the
underived isomorphism, and it is invertible because both units are invertible at a K-injective
complex (`Stacks.LocalCohomology.isIso_derivedSectionsWithSupportInUnit_app` and
`Dualizing.TorsionCounit.isIso_derivedPowerTorsionUnit_app_of_isKInjective`) and every object of
`D(A)` is isomorphic to the image of one.

`HasDerivedCategory.standard` is used as a local instance, as it must be: both
`derivedSectionsWithSupportIn` and `derivedPowerTorsion` are defined under it, and a statement
about a functor has to name the instance the functor was defined with.

**What is still missing, and exactly what it is.** `compareSectionsWithSupportLocalCohomology` is
invertible when `A` is Noetherian — [Stacks, Tag 0955] — and that statement is not proved
anywhere in this library. Through the isomorphism of this file, invertibility of this
transformation is invertibility of `Dualizing.compareTorsionFunctors A I hI`, and on the
subcategory `D_{I^∞-torsion}(A)` that is in turn equivalent, by
`Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_iff_isIso_compareTorsionFunctors`,
to part (1) of Tag 0955: the counit `RΓ_I(K) ⟶ K` is invertible for every `K` with
`I`-power-torsion cohomology. (The source deduces parts (2) and (3) from part (1) by a formal
argument it omits.) The one missing input to part (1) is the statement that every object of
`D_{I^∞-torsion}(A)` admits a K-injective representative whose terms are all `I`-power torsion;
given it,
`Dualizing.TorsionCounit.isIso_derivedPowerTorsionCounit_app_of_isIPowerTorsion_kInjective`
finishes, and its Noetherian input — `J[I^∞]` is injective for `J` injective, Tag 08XW — is
already in the library in `StacksFrontier/Algebra/Module/InjectiveHull/Basic.lean`.

No `@[stacks]` attribute is placed. The isomorphism of this file is not a tagged statement of the
source — the source asserts only that `Γ_I` and its satellites "only depend on the closed subset
`Z`", in prose, in the discussion preceding Tag 0A6L — and the natural transformation, although
it is the content of Tag 0A6U, is not that tag's covering set: Tag 0A6U is already carried by
`Dualizing.compareTorsionFunctors`, and a second attribute here would claim the tag twice.

## References

* [Stacks Project, Tag 0A6L](https://stacks.math.columbia.edu/tag/0A6L)
* [Stacks Project, Tag 0A6P](https://stacks.math.columbia.edu/tag/0A6P)
* [Stacks Project, Tag 0A6U](https://stacks.math.columbia.edu/tag/0A6U)
* [Stacks Project, Tag 0953](https://stacks.math.columbia.edu/tag/0953)
* [Stacks Project, Tag 0955](https://stacks.math.columbia.edu/tag/0955)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- Across a natural transformation, invertibility at an object transfers to any isomorphic
object. -/
lemma isIso_app_of_iso_source {C D : Type*} [Category C] [Category D] {G H : C ⥤ D}
    (τ : G ⟶ H) {X Y : C} (e : X ≅ Y) (h : IsIso (τ.app Y)) : IsIso (τ.app X) :=
  (NatTrans.isIso_app_iff_of_iso τ e).mpr h

/-- **Sections supported in `V(I)` are the `I`-power-torsion submodule.** The supremum defining
`sectionsWithSupportIn` ranges over the ideals `J` with `V(J) ⊆ V(I)`; for such a `J` one has
`I ⊆ √J`, hence `I ^ n ⊆ J` because `I` is finitely generated, so every `J`-power-torsion element
is `I`-power torsion. The reverse inclusion is the term `J = I`. -/
theorem sectionsWithSupportIn_zeroLocus_eq_primaryComponent
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : Type v) [AddCommGroup M] [Module A M] :
    sectionsWithSupportIn A (PrimeSpectrum.zeroLocus (I : Set A)) M =
      I.primaryComponent M := by
  apply le_antisymm
  · rw [sectionsWithSupportIn]
    refine iSup_le fun J ↦ iSup_le fun hJ ↦ ?_
    rw [PrimeSpectrum.zeroLocus_subset_zeroLocus_iff] at hJ
    obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hJ hI
    intro x hx
    obtain ⟨m, hm⟩ := (Ideal.primaryComponent_mem M J x).mp hx
    refine (Ideal.primaryComponent_mem M I x).mpr ⟨n * m, ?_⟩
    refine Submodule.torsionBySet_le_torsionBySet_of_subset ?_ hm
    rw [pow_mul]
    exact Ideal.pow_right_mono hn m
  · exact le_iSup_of_le I (le_iSup_of_le (le_refl _) (le_refl _))

/-- **`Γ_{V(I)} = Γ_I` as functors on modules.** Both send a module to the same submodule, and
both act on morphisms by restriction, so the equality of submodules is natural. -/
def sectionsWithSupportInFunctorIsoPowerTorsionFunctor
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    Dualizing.powerTorsionFunctor.{u, v} A I ⋙
        (ObjectProperty.ι (fun M : ModuleCat.{max u v} A => IsIPowerTorsion A M I)) ≅
      sectionsWithSupportInFunctor.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A)) :=
  NatIso.ofComponents
    (fun M ↦ (LinearEquiv.ofEq _ _
      (sectionsWithSupportIn_zeroLocus_eq_primaryComponent A I hI M).symm).toModuleIso)
    (fun _ ↦ by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      rfl)

/-- **The two models of derived torsion agree.** For a finitely generated ideal `I` of a
commutative ring `A`, the total right derived functor of sections supported in the closed subset
`V(I)` is isomorphic, naturally in the object of `D(A)`, to the total right derived functor of the
`I`-power-torsion submodule functor read in `D(A)`.

The isomorphism is the canonical one: it is the unique natural transformation out of the right
derived functor whose composite with the derived unit of `Γ_{V(I)}` is the derived unit of `Γ_I`
transported along `sectionsWithSupportInFunctorIsoPowerTorsionFunctor`. -/
def derivedSectionsWithSupportInIsoDerivedPowerTorsion
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    letI P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
    letI : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
    letI : PreservesFiniteLimits P.ι :=
      ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
    letI : PreservesFiniteColimits P.ι :=
      ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
    derivedSectionsWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A)) ≅
      Dualizing.derivedPowerTorsion.{u, v} A I hI ⋙ P.ι.mapDerivedCategory := by
  let P : ObjectProperty (ModuleCat.{max u v} A) := fun M ↦ IsIPowerTorsion A M I
  let : P.IsSerreClass := isSerreClass_isIPowerTorsion I hI
  let : PreservesFiniteLimits P.ι :=
    ObjectProperty.preservesFiniteLimits_ι_of_isWeakSerreClass P
  let : PreservesFiniteColimits P.ι :=
    ObjectProperty.preservesFiniteColimits_ι_of_isWeakSerreClass P
  set W := HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ) with hW
  set T := PrimeSpectrum.zeroLocus (I : Set A) with hT
  set β : (sectionsWithSupportInFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙
        (Dualizing.derivedPowerTorsion.{u, v} A I hI ⋙ P.ι.mapDerivedCategory) :=
    (Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso
          (sectionsWithSupportInFunctorIsoPowerTorsionFunctor.{u, v} A I hI)
          (ComplexShape.up ℤ)).symm DerivedCategory.Qh).hom ≫
      (Functor.isoWhiskerLeft
        ((Dualizing.powerTorsionFunctor.{u, v} A I).mapHomotopyCategory (ComplexShape.up ℤ))
        (P.ι.mapDerivedCategoryFactorsh).symm).hom ≫
      Functor.whiskerRight (Dualizing.derivedPowerTorsionUnit.{u, v} A I hI)
        P.ι.mapDerivedCategory with hβ
  set τ := (derivedSectionsWithSupportIn.{u, v} A T).rightDerivedDesc
    (derivedSectionsWithSupportInUnit.{u, v} A T) W
    (Dualizing.derivedPowerTorsion.{u, v} A I hI ⋙ P.ι.mapDerivedCategory) β with hτ
  have hβiso : ∀ (J : CochainComplex (ModuleCat.{max u v} A) ℤ), J.IsKInjective →
      IsIso (β.app ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
        (ComplexShape.up ℤ)).obj J)) := by
    intro J hJ
    have h : IsIso ((Dualizing.derivedPowerTorsionUnit.{u, v} A I hI).app
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj J)) :=
      Dualizing.TorsionCounit.isIso_derivedPowerTorsionUnit_app_of_isKInjective.{u, v}
        (A := A) (I := I) hI J hJ
    rw [hβ]
    simp only [NatTrans.comp_app, whiskerRight_app]
    infer_instance
  have hτiso : ∀ K, IsIso (τ.app K) := by
    intro K
    obtain ⟨L, q, hL, hq⟩ := exists_quasiIso_isKInjective_moduleCat.{u, v} (A := A)
      (DerivedCategory.Q.objPreimage K)
    let e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient (ModuleCat.{max u v} A)
        (ComplexShape.up ℤ)).obj L) ≅ K :=
      (DerivedCategory.quotientCompQhIso (ModuleCat.{max u v} A)).app L ≪≫
        (asIso (DerivedCategory.Q.map q)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso K
    refine isIso_app_of_iso_source τ e.symm ?_
    have hfac := Functor.rightDerived_fac_app (derivedSectionsWithSupportIn.{u, v} A T)
      (derivedSectionsWithSupportInUnit.{u, v} A T) W
      (Dualizing.derivedPowerTorsion.{u, v} A I hI ⋙ P.ι.mapDerivedCategory) β
      ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj L)
    have h1 : IsIso ((derivedSectionsWithSupportInUnit.{u, v} A T).app
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj L)) :=
      inferInstance
    have h2 := hβiso L hL
    rw [← hτ] at hfac
    have h3 : IsIso ((derivedSectionsWithSupportInUnit.{u, v} A T).app
          ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj L) ≫
        τ.app (DerivedCategory.Qh.obj
          ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj L))) := by
      rw [hfac]
      exact h2
    exact IsIso.of_isIso_comp_left
      ((derivedSectionsWithSupportInUnit.{u, v} A T).app
        ((HomotopyCategory.quotient (ModuleCat.{max u v} A) (ComplexShape.up ℤ)).obj L)) _
  have : IsIso τ := NatIso.isIso_of_isIso_app τ
  exact asIso τ

/-- **`RΓ_{V(I)}` lands in the `I`-power-torsion subcategory of `D(A)`.** Every cohomology module
of `RΓ_{V(I)}(K)` is supported in `V(I)`, and for a finitely generated ideal that is exactly being
`I`-power torsion (Stacks 0953). This is the half of the comparison with local cohomology that
holds over an arbitrary ring. -/
theorem derivedPowerTorsionProperty_derivedSectionsWithSupportIn
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (K : DerivedCategory (ModuleCat.{max u v} A)) :
    Dualizing.derivedPowerTorsionProperty A I hI
      ((derivedSectionsWithSupportIn.{u, v} A
        (PrimeSpectrum.zeroLocus (I : Set A))).obj K) := by
  intro i
  rw [isIPowerTorsion_iff_support_subset _ _ _ hI]
  exact support_localCohomologyWithSupportIn_subset.{u, v}
    (PrimeSpectrum.zeroLocus (I : Set A)) K i

/-- **The canonical map from sections with support in `V(I)` to local cohomology `RΓ_Z`.** This is
the transformation (0A6U) of the Stacks project, read on the set-indexed model: the composite of
the identification `RΓ_{V(I)} ≅ RΓ_I` with the comparison `RΓ_I ⟶ RΓ_Z` already in the library.

It is **not** an isomorphism in general — see the module docstring and Stacks 0A6P. Over a
Noetherian ring it is one, which is Stacks 0955 and is not proved in this library. -/
def compareSectionsWithSupportLocalCohomology
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG) :
    derivedSectionsWithSupportIn.{u, v} A (PrimeSpectrum.zeroLocus (I : Set A)) ⟶
      Dualizing.localCohomologyFunctor.{u, max u v} A I hI ⋙
        (Dualizing.derivedPowerTorsionProperty A I hI).ι :=
  (derivedSectionsWithSupportInIsoDerivedPowerTorsion.{u, v} A I hI).hom ≫
    (Functor.isoWhiskerLeft (Dualizing.derivedPowerTorsion.{u, v} A I hI)
      (Dualizing.powerTorsionComparisonCompInclusionIso.{u, max u v} A I hI)).inv ≫
    Functor.whiskerRight (Dualizing.compareTorsionFunctors.{u, v} A I hI)
      (Dualizing.derivedPowerTorsionProperty A I hI).ι

end Stacks.LocalCohomology

end
