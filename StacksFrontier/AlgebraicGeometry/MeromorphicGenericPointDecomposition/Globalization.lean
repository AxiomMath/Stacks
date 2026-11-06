module

public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.StalksReduced
public import StacksFrontier.AlgebraicGeometry.MeromorphicGenericPointDecomposition.AffineModule
public import StacksFrontier.AlgebraicGeometry.Meromorphic.NoEmbeddedPoints
public import StacksFrontier.Topology.Sheaves.OpenImmersion.ModuleExtensionByZero

/-!
# Part (2) of Tag 0EMF: the generic-point decomposition of meromorphic sections

Let `X` be a scheme whose weakly associated points are generic points of irreducible components
and whose quasi-compact opens have only finitely many irreducible components, and let `F` be a
quasi-coherent `𝒪_X`-module. Part (2) of [Stacks, Tag 0EMF] asserts that the sheaf `K_X(F)` of
meromorphic sections of `F` is the product, and equally the direct sum, over the generic points
`η` of the irreducible components, of the contributions `j_{η, *} j_η^* F`, and that it is
quasi-coherent.

The affine-local content of that assertion is
`AlgebraicGeometry.isLocalizedModule_pi_toGenericPointStalkSections`: on an affine open the
product of the sections of the contributions is the localization of `Γ(F, U)` at the
nonzerodivisors of `Γ(X, U)`. What this file supplies is the passage from the affine open to the
whole of `X`.

That passage cannot be made by testing an isomorphism on affine opens, because `K_X(F)` is a
*sheafification* — the sectionwise extension of scalars `U ↦ K_X(U) ⊗_{𝒪_X(U)} Γ(F, U)`,
sheafified — so its sections over an affine open are not the sectionwise tensor product. The
route is instead the one taken for the sheaf of meromorphic *functions* in
`StacksDraft.AlgebraicGeometry.F3b.GenericPointDecomposition.Basic`: a comparison is built at the
level of the presheaf before sheafification, shown to be bijective on the affine opens, hence an
isomorphism on stalks since the affine opens are a basis; the sheafification map is an
isomorphism on stalks as well, so the comparison of sheaves is, and a morphism of sheaves of
modules which is an isomorphism on every stalk is an isomorphism.

## Main definitions

* `AlgebraicGeometry.meromorphicSectionPresheaf`,
  `AlgebraicGeometry.meromorphicSectionPresheafAsModule`: the sectionwise extension of scalars
  `U ↦ K_X(U) ⊗_{𝒪_X(U)} Γ(F, U)`, as a presheaf of `K_X`-modules and of `𝒪_X`-modules. Its
  sheafification is `K_X(F)`.
* `AlgebraicGeometry.toMeromorphicSectionPresheaf`: the canonical map `x ↦ 1 ⊗ x`.
* `AlgebraicGeometry.genericPointComparison`,
  `AlgebraicGeometry.genericPointComparisonPi`: the comparison morphisms
  `K_X(F) ⟶ j_{η, *} j_η^* F` and `K_X(F) ⟶ ∏_{η} j_{η, *} j_η^* F`.

## Main results

* `AlgebraicGeometry.isLocalization_totalQuotientSheaf_obj`: on an affine open the sections of
  the *sheaf* `K_X` are the localization of `Γ(X, U)` at its nonzerodivisors. This is part (5)
  of Tag 0EMF, and upgrades part (5) of [Stacks, Tag 02OW] from the presheaf to the sheaf.
* `AlgebraicGeometry.bijective_genericPointComparisonSectionsPi`: the affine case.
* `AlgebraicGeometry.isIso_genericPointComparisonPi`,
  `AlgebraicGeometry.nonempty_meromorphicSections_iso_pi_genericPointStalkModuleOf`,
  `AlgebraicGeometry.nonempty_meromorphicSections_iso_sigma_genericPointStalkModuleOf` and
  `AlgebraicGeometry.meromorphicSections_isQuasicoherent_of_genericHypotheses`: part (2) of
  Tag 0EMF, in its product, direct-sum and quasi-coherence forms.
* `AlgebraicGeometry.nonempty_meromorphicSections_iso_product_genericPointStalks_of_isReduced`
  and its two companions: part (2) of [Stacks, Tag 02OW].
* `nonempty_meromorphicSections_iso_product_genericPointStalks_of_hasNoEmbeddedPoints` and its
  two companions, in the same namespace: the module-valued half of [Stacks, Tag 0EMH].

## Implementation notes

The comparison morphism is built by hand rather than directly from the change-of-rings and
pullback-pushforward adjunctions, because what the source asserts is the existence of an
isomorphism and a hand-built comparison has computable sections. At the presheaf
level the extension of scalars is `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings`, whose
  universal property is
available as the explicit pair `Stacks.PresheafOfModules.ChangeOfRings.unitHom` /
  `Stacks.PresheafOfModules.ChangeOfRings.counitHom` rather than through
an adjunction, so the comparison out of the sectionwise tensor product is
`Stacks.PresheafOfModules.ChangeOfRings.counitHom` applied to the unit of `j_η^* ⊣ j_{η, *}`;
  `changeOfRings_unitHom_eq`
records that the composite with `x ↦ 1 ⊗ x` recovers that unit, which is what identifies the
comparison on sections. The passage to the sheaf is
`PresheafOfModules.sheafificationHomEquiv`, and
`PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def` is what carries the presheaf-level
identity across it.

Two module structures sit on the sections of the sectionwise tensor product — over `Γ(X, U)` and
over `Γ(K_X, U)` — and neither is found by instance search at the spelling `Γ(X, U)` that the
affine statement uses, so both are supplied as `@[instance_reducible]` definitions and passed as
explicit arguments, exactly as in
`StacksDraft.AlgebraicGeometry.F3b.GenericPointDecomposition.AffineModule`. For the same reason
`isBaseChange_of_tmul_one` and `bijective_of_isLocalizedModule_comp` are stated at abstract
types: at the concrete section types the comparison of the two `Γ(X, U)`-module structures on a
tensor product is expensive, and stating them generically pays for it once.

## References

* [Stacks Project, Tag 0EMF](https://stacks.math.columbia.edu/tag/0EMF)
* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TensorProduct
open Stacks.AlgebraicGeometry.GenericPointDecomposition
  (genericPointStalkModuleOf meromorphicSections)

universe u

noncomputable section

namespace AlgebraicGeometry

/-! ### Two statements about localizations of modules, at abstract types -/

/-- A map into which a module base-changes along a ring map is a base change in the sense of
`IsBaseChange` as soon as the base change is realised by the standard tensor product. -/
theorem isBaseChange_of_tmul_one {R S M P : Type u} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module S P] [Module R P]
    [IsScalarTower R S P] (ι : M →ₗ[R] P) (e : P ≃ₗ[S] TensorProduct R S M)
    (he : ∀ m, e (ι m) = (1 : S) ⊗ₜ[R] m) : IsBaseChange S ι :=
  IsBaseChange.of_linearEquiv (TensorProduct.isBaseChange R M S) (LinearEquiv.refl R M) e ι he

/-- **Two localizations of one module are compared bijectively.** If `ι : M ⟶ P` and
`g : M ⟶ N` both exhibit their targets as the localization of `M` at `p`, then any linear map
`T : P ⟶ N` with `T ∘ ι = g` is bijective. -/
theorem bijective_of_isLocalizedModule_comp {R M P N : Type u} [CommRing R] (p : Submonoid R)
    [AddCommGroup M] [Module R M] [AddCommGroup P] [Module R P] [AddCommGroup N] [Module R N]
    (ι : M →ₗ[R] P) (hι : IsLocalizedModule p ι)
    (g : M →ₗ[R] N) (hg : IsLocalizedModule p g)
    (T : P →ₗ[R] N) (hT : ∀ m, T (ι m) = g m) : Function.Bijective T := by
  have := hι
  have := hg
  have h2 : T = IsLocalizedModule.linearEquiv p ι g :=
    IsLocalizedModule.linearMap_ext p ι g (LinearMap.ext fun m =>
      (hT m).trans (IsLocalizedModule.linearEquiv_apply p ι g m).symm)
  rw [h2]
  exact (IsLocalizedModule.linearEquiv p ι g).bijective

/-- The unit of the presheaf-level change-of-rings adjunction at a morphism factors through the
unit at the identity. -/
theorem changeOfRings_unitHom_eq {C : Type*} [Category C] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat}
    (θ : O₁ ⟶ O₂) {G : Stacks.PresheafOfModules.ChangeOfRings.PMod O₁} {N :
      Stacks.PresheafOfModules.ChangeOfRings.PMod O₂}
    (ψ : (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj G ⟶ N) :
    Stacks.PresheafOfModules.ChangeOfRings.unitHom θ ψ =
      Stacks.PresheafOfModules.ChangeOfRings.unitHom θ (𝟙
        ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj G)) ≫
        (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars θ).map ψ := by
  refine PresheafOfModules.hom_ext fun Y => ?_
  refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
  let _ := (θ.app Y).hom.toAlgebra
  have h3 : ((Stacks.PresheafOfModules.ChangeOfRings.unitHom θ (𝟙
    ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj G)) ≫
      (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars θ).map ψ).app Y).hom x =
      (ψ.app Y).hom ((Stacks.PresheafOfModules.ChangeOfRings.unitApp θ
        (𝟙 ((Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ).obj G)) Y).hom x) := rfl
  rw [h3, Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply]
  have h4 : ((Stacks.PresheafOfModules.ChangeOfRings.unitHom θ ψ).app Y).hom x =
      (Stacks.PresheafOfModules.ChangeOfRings.unitApp θ ψ Y).hom x := rfl
  rw [h4, Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply]
  rfl

variable {X : Scheme.{u}}

/-! ### The sections of the sheaf of total quotient rings on an affine open -/

/-- The sheafification map of the presheaf of meromorphic functions is bijective on an affine
open: composed with the comparison to the product of the generic-point contributions it is the
presheaf-level comparison, which is bijective there, and that comparison is an isomorphism. -/
theorem bijective_toSheafify_totalQuotientPresheaf_app
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective ((toSheafify (Opens.grothendieckTopology X)
      X.presheaf.totalQuotientPresheaf).app (op U)).hom := by
  have hcomp := bijective_toGenericPointStalkProductPresheaf_app hass hfinite hU
  have hring : IsIso (toGenericPointStalkProduct X) :=
    isIso_toGenericPointStalkProduct hass hfinite
  have hhom : IsIso (toGenericPointStalkProduct X).hom :=
    Functor.map_isIso (TopCat.Sheaf.forget CommRingCat.{u} X) (toGenericPointStalkProduct X)
  have h2 : Function.Bijective (((toGenericPointStalkProduct X).hom.app (op U)).hom) := by
    rw [← ConcreteCategory.isIso_iff_bijective]; infer_instance
  exact (Function.Bijective.of_comp_iff' h2 _).1 hcomp

/-- **Part (5) of [Stacks, Tag 0EMF].** On an affine open `U` of a scheme whose weakly associated
points are generic points of irreducible components and whose quasi-compact opens have finitely
many irreducible components, the sections `K_X(U)` of the *sheaf* of meromorphic functions — not
only those of the presheaf — are the total quotient ring of `Γ(X, U)`, that is, its localization
at its nonzerodivisors. -/
@[stacks 0EMF "part (5)"]
theorem isLocalization_totalQuotientSheaf_obj
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    {U : X.Opens} (hU : IsAffineOpen U) :
    letI : Algebra Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) :=
      (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra
    IsLocalization (nonZeroDivisors Γ(X, U)) (X.totalQuotientSheaf.obj.obj (op U)) := by
  let _ : Algebra Γ(X, U) (X.presheaf.totalQuotientPresheaf.obj (op U)) :=
    (X.presheaf.toTotalQuotientPresheaf.app (op U)).hom.toAlgebra
  let _ : Algebra Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) :=
    (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra
  have hpre : IsLocalization (nonZeroDivisors Γ(X, U))
      (X.presheaf.totalQuotientPresheaf.obj (op U)) :=
    hU.isLocalization_totalQuotientPresheaf_obj
  have hb := bijective_toSheafify_totalQuotientPresheaf_app hass hfinite hU
  let e : X.presheaf.totalQuotientPresheaf.obj (op U) ≃ₐ[Γ(X, U)]
      X.totalQuotientSheaf.obj.obj (op U) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective _ hb) (fun a => by
      show ((toSheafify (Opens.grothendieckTopology X)
          X.presheaf.totalQuotientPresheaf).app (op U)).hom
          ((X.presheaf.toTotalQuotientPresheaf.app (op U)).hom a) =
        (X.toTotalQuotientSheaf.hom.app (op U)).hom a
      rw [Scheme.toTotalQuotientSheaf_hom]
      rfl)
  exact IsLocalization.isLocalization_of_algEquiv _ e

/-! ### The presheaf whose sheafification is the sheaf of meromorphic sections -/

/-- The sectionwise extension of scalars `U ↦ K_X(U) ⊗_{𝒪_X(U)} F(U)`, as a presheaf of
`K_X`-modules. Its sheafification is the sheaf `K_X(F)` of meromorphic sections of `F`. -/
abbrev meromorphicSectionPresheaf (X : Scheme.{u}) (F : X.Modules) :
    Stacks.PresheafOfModules.ChangeOfRings.PMod X.totalQuotientSheaf.obj :=
  (Stacks.PresheafOfModules.ChangeOfRings.changeOfRings X.toTotalQuotientSheaf.hom).obj F.val

/-- The sectionwise extension of scalars, read as a presheaf of `𝒪_X`-modules. -/
abbrev meromorphicSectionPresheafAsModule (X : Scheme.{u}) (F : X.Modules) :
    Stacks.PresheafOfModules.ChangeOfRings.PMod X.sheaf.obj :=
  (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars X.toTotalQuotientSheaf.hom).obj
    (meromorphicSectionPresheaf X F)

/-- The canonical `𝒪_X`-linear map `F ⟶ K_X ⊗_{𝒪_X} F` of presheaves, sending a section `x` to
`1 ⊗ x`. -/
def toMeromorphicSectionPresheaf (F : X.Modules) :
    F.val ⟶ meromorphicSectionPresheafAsModule X F :=
  Stacks.PresheafOfModules.ChangeOfRings.unitHom X.toTotalQuotientSheaf.hom (𝟙
    (meromorphicSectionPresheaf X F))

/-- The `Γ(X, U)`-module structure on the sections of the sectionwise extension of scalars, at
the spelling `Γ(X, U)` rather than the one instance search produces. -/
@[instance_reducible]
def meromorphicSectionPresheafSectionsModule (F : X.Modules) (U : X.Opens) :
    Module Γ(X, U) ((meromorphicSectionPresheafAsModule X F).obj (op U)) :=
  ((meromorphicSectionPresheafAsModule X F).obj (op U)).isModule

/-- The `Γ(K_X, U)`-module structure on the sections of the sectionwise extension of scalars,
read at the `𝒪_X`-module spelling of the presheaf. -/
@[instance_reducible]
def meromorphicSectionPresheafSectionsKModule (F : X.Modules) (U : X.Opens) :
    Module (X.totalQuotientSheaf.obj.obj (op U))
      ((meromorphicSectionPresheafAsModule X F).obj (op U)) :=
  ((meromorphicSectionPresheaf X F).obj (op U)).isModule

/-- The two module structures on the sections of the sectionwise extension of scalars form a
scalar tower over the canonical map `Γ(X, U) ⟶ Γ(K_X, U)`. -/
theorem meromorphicSectionPresheafSectionsIsScalarTower (F : X.Modules) (U : X.Opens) :
    letI : Algebra Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) :=
      (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra
    letI := meromorphicSectionPresheafSectionsModule F U
    letI := meromorphicSectionPresheafSectionsKModule F U
    IsScalarTower Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U))
      ((meromorphicSectionPresheafAsModule X F).obj (op U)) := by
  let _ : Algebra Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) :=
    (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra
  let _ := meromorphicSectionPresheafSectionsModule F U
  let _ := meromorphicSectionPresheafSectionsKModule F U
  constructor
  intro r b n
  show (((X.toTotalQuotientSheaf.hom.app (op U)).hom r) * b) • n = _
  rw [mul_smul]
  rfl

/-- The canonical map on sections, as a `Γ(X, U)`-linear map. -/
def toMeromorphicSectionPresheafSections (F : X.Modules) (U : X.Opens) :
    letI := meromorphicSectionPresheafSectionsModule F U
    Γ(F, U) →ₗ[Γ(X, U)] ((meromorphicSectionPresheafAsModule X F).obj (op U)) :=
  ((toMeromorphicSectionPresheaf F).app (op U)).hom

/-- The canonical map on sections sends `x` to `1 ⊗ₜ x`. -/
theorem toMeromorphicSectionPresheafSections_apply (F : X.Modules) (U : X.Opens) (x : Γ(F, U)) :
    letI : Algebra Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) :=
      (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra
    letI := meromorphicSectionPresheafSectionsModule F U
    (toMeromorphicSectionPresheafSections F U x :
        TensorProduct Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) Γ(F, U)) =
      (1 : X.totalQuotientSheaf.obj.obj (op U)) ⊗ₜ[Γ(X, U)] x :=
  Stacks.PresheafOfModules.ChangeOfRings.unitApp_apply X.toTotalQuotientSheaf.hom
    (𝟙 (meromorphicSectionPresheaf X F)) (op U) x

/-- On sections over `U`, the canonical map exhibits the sections of the meromorphic section
presheaf as the base change of `Γ(F, U)` to the sections of the sheaf of total quotient rings. -/
theorem isBaseChange_toMeromorphicSectionPresheafSections (F : X.Modules) (U : X.Opens) :
    letI : Algebra Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) :=
      (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra
    letI := meromorphicSectionPresheafSectionsModule F U
    letI := meromorphicSectionPresheafSectionsKModule F U
    letI := meromorphicSectionPresheafSectionsIsScalarTower F U
    IsBaseChange (X.totalQuotientSheaf.obj.obj (op U))
      (toMeromorphicSectionPresheafSections F U) := by
  let _ : Algebra Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) :=
    (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra
  let hm := meromorphicSectionPresheafSectionsModule F U
  let hk := meromorphicSectionPresheafSectionsKModule F U
  let ht := meromorphicSectionPresheafSectionsIsScalarTower F U
  exact @isBaseChange_of_tmul_one Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) Γ(F, U)
    ((meromorphicSectionPresheafAsModule X F).obj (op U)) _ _ _ _ _ _ hk hm ht
    (toMeromorphicSectionPresheafSections F U) (LinearEquiv.refl _ _)
    (fun m => toMeromorphicSectionPresheafSections_apply F U m)

/-- **On an affine open the sectionwise extension of scalars is the localization.** The sections
of `K_X ⊗_{𝒪_X} F` over an affine open `U` are the localization of `Γ(F, U)` at the
nonzerodivisors of `Γ(X, U)`. -/
theorem isLocalizedModule_toMeromorphicSectionPresheafSections
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    letI := meromorphicSectionPresheafSectionsModule F U
    IsLocalizedModule (nonZeroDivisors Γ(X, U))
      (toMeromorphicSectionPresheafSections F U) := by
  let _ : Algebra Γ(X, U) (X.totalQuotientSheaf.obj.obj (op U)) :=
    (X.toTotalQuotientSheaf.hom.app (op U)).hom.toAlgebra
  let hm := meromorphicSectionPresheafSectionsModule F U
  let hk := meromorphicSectionPresheafSectionsKModule F U
  let ht := meromorphicSectionPresheafSectionsIsScalarTower F U
  exact (@isLocalizedModule_iff_isBaseChange _ _ (nonZeroDivisors Γ(X, U))
    (X.totalQuotientSheaf.obj.obj (op U)) _ _
    (isLocalization_totalQuotientSheaf_obj hass hfinite hU) _ _ _ _ _ hm hk ht
    (toMeromorphicSectionPresheafSections F U)).mpr
    (isBaseChange_toMeromorphicSectionPresheafSections F U)

/-! ### The comparison morphisms -/

/-- The unit of `j_η^* ⊣ j_{η, *}` on presheaves, read into the spelling in which the target
carries a `K_X`-action. -/
def toGenericPointStalkKModuleUnit (F : X.Modules) (η : genericPoints X) :
    F.val ⟶ (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars X.toTotalQuotientSheaf.hom).obj
      ((genericPointStalkKModule F η).val) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (X.fromSpecStalk η.1)).unit.app F ≫
    eqToHom (restrictScalars_genericPointStalkKModule F η).symm).val

/-- The presheaf-level comparison `K_X ⊗_{𝒪_X} F ⟶ j_{η, *} j_η^* F`, as presheaves of
`K_X`-modules: the `K_X`-linear extension of the unit of `j_η^* ⊣ j_{η, *}`. -/
def genericPointComparisonKPresheaf (F : X.Modules) (η : genericPoints X) :
    meromorphicSectionPresheaf X F ⟶ (genericPointStalkKModule F η).val :=
  Stacks.PresheafOfModules.ChangeOfRings.counitHom X.toTotalQuotientSheaf.hom
    (toGenericPointStalkKModuleUnit F η)

/-- The presheaf-level comparison, as presheaves of `𝒪_X`-modules. -/
def genericPointComparisonPresheaf (F : X.Modules) (η : genericPoints X) :
    meromorphicSectionPresheafAsModule X F ⟶ (genericPointStalkModuleOf X F η).val :=
  (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars X.toTotalQuotientSheaf.hom).map
      (genericPointComparisonKPresheaf F η) ≫
    (eqToHom (restrictScalars_genericPointStalkKModule F η)).val

/-- The characterising property of the presheaf-level comparison: precomposing with `x ↦ 1 ⊗ x`
gives the unit of `j_η^* ⊣ j_{η, *}`. -/
theorem toMeromorphicSectionPresheaf_comp_genericPointComparisonPresheaf
    (F : X.Modules) (η : genericPoints X) :
    toMeromorphicSectionPresheaf F ≫ genericPointComparisonPresheaf F η =
      ((Scheme.Modules.pullbackPushforwardAdjunction (X.fromSpecStalk η.1)).unit.app F).val := by
  have h1 : toMeromorphicSectionPresheaf F ≫
      (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars X.toTotalQuotientSheaf.hom).map
        (genericPointComparisonKPresheaf F η) = toGenericPointStalkKModuleUnit F η :=
    ((changeOfRings_unitHom_eq X.toTotalQuotientSheaf.hom
        (genericPointComparisonKPresheaf F η)).symm.trans
      ((Stacks.PresheafOfModules.ChangeOfRings.homEquivCore X.toTotalQuotientSheaf.hom F.val
        ((genericPointStalkKModule F η).val)).right_inv
          (toGenericPointStalkKModuleUnit F η)))
  have h2 : toMeromorphicSectionPresheaf F ≫ genericPointComparisonPresheaf F η =
      (toMeromorphicSectionPresheaf F ≫
        (Stacks.PresheafOfModules.ChangeOfRings.restrictScalars X.toTotalQuotientSheaf.hom).map
          (genericPointComparisonKPresheaf F η)) ≫
        (eqToHom (restrictScalars_genericPointStalkKModule F η)).val :=
    (Category.assoc _ _ _).symm
  have h4 : (Scheme.Modules.pullbackPushforwardAdjunction (X.fromSpecStalk η.1)).unit.app F ≫
      eqToHom (restrictScalars_genericPointStalkKModule F η).symm ≫
      eqToHom (restrictScalars_genericPointStalkKModule F η) =
      (Scheme.Modules.pullbackPushforwardAdjunction (X.fromSpecStalk η.1)).unit.app F :=
    (congrArg (fun t => (Scheme.Modules.pullbackPushforwardAdjunction
        (X.fromSpecStalk η.1)).unit.app F ≫ t)
      ((eqToHom_trans (restrictScalars_genericPointStalkKModule F η).symm
        (restrictScalars_genericPointStalkKModule F η)).trans
          (eqToHom_refl _ _))).trans (Category.comp_id _)
  have h5 : toGenericPointStalkKModuleUnit F η ≫
      (eqToHom (restrictScalars_genericPointStalkKModule F η)).val =
      ((Scheme.Modules.pullbackPushforwardAdjunction (X.fromSpecStalk η.1)).unit.app F ≫
        eqToHom (restrictScalars_genericPointStalkKModule F η).symm ≫
        eqToHom (restrictScalars_genericPointStalkKModule F η)).val := rfl
  exact h2.trans ((congrArg (fun t => t ≫
    (eqToHom (restrictScalars_genericPointStalkKModule F η)).val) h1).trans
      (h5.trans (congrArg (fun t : F ⟶ genericPointStalkModuleOf X F η => t.val) h4)))

/-- The comparison `K_X(F) ⟶ j_{η, *} j_η^* F` of sheaves of `K_X`-modules, obtained from the
presheaf-level comparison by the sheafification adjunction. -/
def genericPointComparisonKSheaf (F : X.Modules) (η : genericPoints X) :
    meromorphicSectionSheaf X.sheaf F ⟶ genericPointStalkKModule F η :=
  (PresheafOfModules.sheafificationHomEquiv
    (𝟙 (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.totalQuotientSheaf).obj)).symm (genericPointComparisonKPresheaf F η)

/-- **The comparison `K_X(F) ⟶ j_{η, *} j_η^* F` of `𝒪_X`-modules.** -/
def genericPointComparison (F : X.Modules) (η : genericPoints X) :
    meromorphicSections X F ⟶ genericPointStalkModuleOf X F η :=
  (SheafOfModules.restrictScalars (toTotalQuotientRingSheaf X)).map
      (genericPointComparisonKSheaf F η) ≫
    eqToHom (restrictScalars_genericPointStalkKModule F η)

/-- The comparison from the sheaf of meromorphic sections to the product of the generic-point
contributions. -/
def genericPointComparisonPi (F : X.Modules) :
    meromorphicSections X F ⟶
      ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η :=
  Pi.lift fun η ↦ genericPointComparison F η


/-- The comparison of `𝒪_X`-modules, read on underlying abelian presheaves, is the
presheaf-level comparison precomposed with the sheafification map. -/
theorem toAb_genericPointComparison (F : X.Modules) (η : genericPoints X) :
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map (genericPointComparisonPresheaf F η) =
      toSheafify (Opens.grothendieckTopology X)
          (meromorphicSectionPresheafAsModule X F).presheaf ≫
        (ExtensionByZeroModules.toAb X.ringCatSheaf).map (genericPointComparison F η) := by
  have hdef := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (𝟙 (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
      X.totalQuotientSheaf).obj) (genericPointComparisonKSheaf F η)
  rw [show PresheafOfModules.sheafificationHomEquiv
      (𝟙 (Stacks.Sheaves.Differentials.ringSheaf (J := Opens.grothendieckTopology X)
        X.totalQuotientSheaf).obj) (genericPointComparisonKSheaf F η) =
      genericPointComparisonKPresheaf F η from Equiv.apply_symm_apply _ _] at hdef
  have hL : (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      (genericPointComparisonPresheaf F η) =
      (PresheafOfModules.toPresheaf (Stacks.Sheaves.Differentials.ringSheaf
          (J := Opens.grothendieckTopology X) X.totalQuotientSheaf).obj).map
        (genericPointComparisonKPresheaf F η) ≫
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((eqToHom (restrictScalars_genericPointStalkKModule F η)).val) := rfl
  have hR : (ExtensionByZeroModules.toAb X.ringCatSheaf).map (genericPointComparison F η) =
      (PresheafOfModules.toPresheaf (Stacks.Sheaves.Differentials.ringSheaf
          (J := Opens.grothendieckTopology X) X.totalQuotientSheaf).obj).map
        (genericPointComparisonKSheaf F η).val ≫
      (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        ((eqToHom (restrictScalars_genericPointStalkKModule F η)).val) := rfl
  exact hL.trans (((congrArg (fun t => t ≫
    (PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
      ((eqToHom (restrictScalars_genericPointStalkKModule F η)).val)) hdef).trans
        (Category.assoc _ _ _)).trans
      (congrArg (fun t => toSheafify (Opens.grothendieckTopology X)
        (meromorphicSectionPresheafAsModule X F).presheaf ≫ t) hR.symm))

/-! ### The affine case -/

/-- The presheaf-level comparison on sections, as a `Γ(X, U)`-linear map. -/
def genericPointComparisonSections (F : X.Modules) (η : genericPoints X) (U : X.Opens) :
    letI := meromorphicSectionPresheafSectionsModule F U
    ((meromorphicSectionPresheafAsModule X F).obj (op U)) →ₗ[Γ(X, U)]
      Γ(genericPointStalkModuleOf X F η, U) :=
  ((genericPointComparisonPresheaf F η).app (op U)).hom

/-- The presheaf-level comparison into the product of the generic-point contributions, on
sections. -/
def genericPointComparisonSectionsPi (F : X.Modules) (U : X.Opens) :
    letI := meromorphicSectionPresheafSectionsModule F U
    ((meromorphicSectionPresheafAsModule X F).obj (op U)) →ₗ[Γ(X, U)]
      (∀ η : genericPoints X, Γ(genericPointStalkModuleOf X F η, U)) :=
  letI := meromorphicSectionPresheafSectionsModule F U
  LinearMap.pi fun η ↦ genericPointComparisonSections F η U

/-- The presheaf-level comparison at a generic point `η`, composed with the canonical map
from `F`, is the unit of the pullback-pushforward adjunction along `Spec 𝒪_{X,η} → X`,
evaluated on sections. -/
theorem genericPointComparisonPresheaf_app_apply_toMeromorphicSectionPresheaf_app_apply
    (F : X.Modules) (η : genericPoints X) (U : X.Opens) (x : F.val.obj (op U)) :
    ((genericPointComparisonPresheaf F η).app (op U)).hom
        (((toMeromorphicSectionPresheaf F).app (op U)).hom x) =
      (((Scheme.Modules.pullbackPushforwardAdjunction (X.fromSpecStalk η.1)).unit.app
        F).val.app (op U)).hom x :=
  ConcreteCategory.congr_hom (congrArg
    (fun n : F.val ⟶ (genericPointStalkModuleOf X F η).val => n.app (op U))
      (toMeromorphicSectionPresheaf_comp_genericPointComparisonPresheaf F η)) x

/-- On sections over `U`, the comparison at a generic point `η` composed with the canonical
map from `Γ(F, U)` is `toGenericPointStalkSections F η U`. -/
theorem genericPointComparisonSections_toMeromorphicSectionPresheafSections
    (F : X.Modules) (η : genericPoints X) (U : X.Opens) (x : Γ(F, U)) :
    letI := meromorphicSectionPresheafSectionsModule F U
    genericPointComparisonSections F η U (toMeromorphicSectionPresheafSections F U x) =
      toGenericPointStalkSections F η U x :=
  genericPointComparisonPresheaf_app_apply_toMeromorphicSectionPresheaf_app_apply F η U x

/-- **The affine case of part (2) of Tag 0EMF, for the presheaf-level comparison.** On an affine
open the comparison from the sectionwise extension of scalars to the product of the
generic-point contributions is bijective: both sides are the localization of `Γ(F, U)` at the
nonzerodivisors of `Γ(X, U)`. -/
theorem bijective_genericPointComparisonSectionsPi
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    letI := meromorphicSectionPresheafSectionsModule F U
    Function.Bijective (genericPointComparisonSectionsPi F U) :=
  @bijective_of_isLocalizedModule_comp Γ(X, U) Γ(F, U)
    ((meromorphicSectionPresheafAsModule X F).obj (op U))
    (∀ η : genericPoints X, Γ(genericPointStalkModuleOf X F η, U))
    _ (nonZeroDivisors Γ(X, U)) _ _ _ (meromorphicSectionPresheafSectionsModule F U) _ _
    (toMeromorphicSectionPresheafSections F U)
    (isLocalizedModule_toMeromorphicSectionPresheafSections hass hfinite F hU)
    (LinearMap.pi fun η : genericPoints X ↦ toGenericPointStalkSections F η U)
    (isLocalizedModule_pi_toGenericPointStalkSections hass hfinite F hU)
    (genericPointComparisonSectionsPi F U)
    (fun x => funext fun η =>
      genericPointComparisonSections_toMeromorphicSectionPresheafSections F η U x)

/-! ### From the affine case to the whole of `X` -/

/-- The comparison from the sectionwise extension of scalars to the product of the generic-point
contributions, on underlying abelian presheaves. The sheaf of meromorphic sections is the
sheafification of the source, so this is the presheaf-level comparison whose bijectivity on the
affine opens makes the comparison of sheaves an isomorphism on stalks. -/
def genericPointComparisonAbPresheaf (F : X.Modules) :
    (meromorphicSectionPresheafAsModule X F).presheaf ⟶
      (ExtensionByZeroModules.toAb X.ringCatSheaf).obj
        (∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) :=
  toSheafify (Opens.grothendieckTopology X)
      (meromorphicSectionPresheafAsModule X F).presheaf ≫
    (ExtensionByZeroModules.toAb X.ringCatSheaf).map (genericPointComparisonPi F)

/-- On sections over `U`, the comparison into the product followed by the projection to the
factor at `η` is the comparison at `η`. -/
theorem modulesSectionsFunctor_map_genericPointComparisonPi_comp_π
    (F : X.Modules) (U : X.Opens) (η : genericPoints X) :
    (modulesSectionsFunctor X U).map (genericPointComparisonPi F) ≫
        (modulesSectionsFunctor X U).map
          (Pi.π (fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) η) =
      (modulesSectionsFunctor X U).map (genericPointComparison F η) := by
  rw [← Functor.map_comp]
  exact congrArg (modulesSectionsFunctor X U).map
    (Pi.lift_comp_π (fun η ↦ genericPointComparison F η) η)

/-- On sections over `U`, the comparison at `η` applied to the image of `t` in the
sheafification is the presheaf-level comparison at `η` applied to `t`. -/
theorem toAb_genericPointComparison_app_apply (F : X.Modules) (η : genericPoints X)
    (U : X.Opens) (t : (meromorphicSectionPresheafAsModule X F).presheaf.obj (op U)) :
    ((ExtensionByZeroModules.toAb X.ringCatSheaf).map (genericPointComparison F η)).app
        (op U) (((toSheafify (Opens.grothendieckTopology X)
          (meromorphicSectionPresheafAsModule X F).presheaf).app (op U)).hom t) =
      ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map
        (genericPointComparisonPresheaf F η)).app (op U) t :=
  (ConcreteCategory.congr_hom (congrArg
    (fun n : (meromorphicSectionPresheafAsModule X F).presheaf ⟶
      (ExtensionByZeroModules.toAb X.ringCatSheaf).obj (genericPointStalkModuleOf X F η) =>
        n.app (op U)) (toAb_genericPointComparison F η)) t).symm

/-- The `η`-component of the comparison of abelian presheaves, applied to `t`, is the
presheaf-level comparison at `η` applied to `t`. -/
theorem modulesSectionsPiEquiv_genericPointComparisonAbPresheaf (F : X.Modules)
    (U : X.Opens) (η : genericPoints X)
    (t : (meromorphicSectionPresheafAsModule X F).presheaf.obj (op U)) :
    modulesSectionsPiEquiv (fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) U
        (((genericPointComparisonAbPresheaf F).app (op U)).hom t) η =
      genericPointComparisonSections F η U t := by
  refine (modulesSectionsPiEquiv_apply _ _ _ η).trans ?_
  exact (ConcreteCategory.congr_hom
    (modulesSectionsFunctor_map_genericPointComparisonPi_comp_π F U η)
    (((toSheafify (Opens.grothendieckTopology X)
      (meromorphicSectionPresheafAsModule X F).presheaf).app (op U)).hom t)).trans
    (toAb_genericPointComparison_app_apply F η U t)

/-- On an affine open the comparison of abelian presheaves is bijective: its components are the
presheaf-level comparison, which is bijective there. -/
theorem bijective_genericPointComparisonAbPresheaf_app
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens} (hU : IsAffineOpen U) :
    Function.Bijective ((genericPointComparisonAbPresheaf F).app (op U)).hom := by
  have h := bijective_genericPointComparisonSectionsPi hass hfinite F hU
  have hcomp : (modulesSectionsPiEquiv
      (fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) U) ∘
        ((genericPointComparisonAbPresheaf F).app (op U)).hom =
      genericPointComparisonSectionsPi F U :=
    funext fun t => funext fun η =>
      modulesSectionsPiEquiv_genericPointComparisonAbPresheaf F U η t
  exact (Function.Bijective.of_comp_iff' (Equiv.bijective _) _).1 (hcomp ▸ h)

/-- The comparison of abelian presheaves is an isomorphism on every stalk: it is bijective on
the affine opens, which form a basis. -/
theorem isIso_stalkFunctor_map_genericPointComparisonAbPresheaf
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (F : X.Modules) [F.IsQuasicoherent] (x : X) :
    IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (genericPointComparisonAbPresheaf F)) := by
  rw [ConcreteCategory.isIso_iff_bijective]
  refine ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis X.isBasis_affineOpens
    (fun V hV => (bijective_genericPointComparisonAbPresheaf_app hass hfinite F hV).1) x,
    fun t => ?_⟩
  obtain ⟨V, hxV, hVB, s, hs⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis
    X.isBasis_affineOpens ((ExtensionByZeroModules.toAb X.ringCatSheaf).obj
      (∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η)) x t
  obtain ⟨y, hy⟩ := (bijective_genericPointComparisonAbPresheaf_app hass hfinite F hVB).2 s
  refine ⟨((TopCat.Presheaf.germ
    (meromorphicSectionPresheafAsModule X F).presheaf V x hxV).hom y), ?_⟩
  rw [TopCat.Presheaf.stalkFunctor_map_germ_apply, hy, hs]

/-- **Part (2) of Tag 0EMF, as the invertibility of the comparison morphism.** -/
theorem isIso_genericPointComparisonPi
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (F : X.Modules) [F.IsQuasicoherent] : IsIso (genericPointComparisonPi F) := by
  refine ExtensionByZeroModules.isIso_of_stalk_isIso X.ringCatSheaf
    (genericPointComparisonPi F) fun x => ?_
  have h1 : IsIso ((TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X)
        (meromorphicSectionPresheafAsModule X F).presheaf)) :=
    TopCat.Presheaf.stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u} _
  exact IsIso.of_isIso_fac_left
    (f := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (toSheafify (Opens.grothendieckTopology X)
        (meromorphicSectionPresheafAsModule X F).presheaf))
    (g := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      ((ExtensionByZeroModules.toAb X.ringCatSheaf).map (genericPointComparisonPi F)))
    (h := (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (genericPointComparisonAbPresheaf F))
    (hh := isIso_stalkFunctor_map_genericPointComparisonAbPresheaf hass hfinite F x)
    (Functor.map_comp _ _ _).symm

/-- **Part (2) of [Stacks, Tag 0EMF], the product decomposition.** For a quasi-coherent module `F`
on a scheme whose weakly associated points are generic points of irreducible components and whose
quasi-compact opens have finitely many irreducible components, the sheaf `K_X(F)` of meromorphic
sections of `F` is the product over the generic points of the irreducible components of the
generic-point contributions. -/
@[stacks 0EMF "part (2), product"]
theorem nonempty_meromorphicSections_iso_pi_genericPointStalkModuleOf
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (F : X.Modules) [F.IsQuasicoherent] :
    Nonempty (meromorphicSections X F ≅
      ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) :=
  ⟨@asIso _ _ _ _ _ (isIso_genericPointComparisonPi hass hfinite F)⟩

/-- **Part (2) of [Stacks, Tag 0EMF], the direct-sum decomposition.** The family of generic-point
contributions is locally finite, so the product of the previous theorem is also their direct
sum. -/
@[stacks 0EMF "part (2), direct sum"]
theorem nonempty_meromorphicSections_iso_sigma_genericPointStalkModuleOf
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (F : X.Modules) [F.IsQuasicoherent] :
    Nonempty (meromorphicSections X F ≅
      ∐ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) :=
  (nonempty_meromorphicSections_iso_coproduct_iff_product X F hfinite).mpr
    (nonempty_meromorphicSections_iso_pi_genericPointStalkModuleOf hass hfinite F)

/-- **Part (2) of [Stacks, Tag 0EMF], quasi-coherence.** The sheaf `K_X(F)` of meromorphic
sections of a quasi-coherent module `F` is quasi-coherent, being the product of the generic-point
contributions. -/
@[stacks 0EMF "part (2), quasi-coherence"]
theorem meromorphicSections_isQuasicoherent_of_genericHypotheses
    (hass : Stacks.Divisors.schemeWeaklyAssociatedPoints X ⊆ genericPoints X)
    (hfinite : ∀ V : X.Opens, IsCompact (V : Set X) → (irreducibleComponents V).Finite)
    (F : X.Modules) [F.IsQuasicoherent] :
    (meromorphicSections X F).IsQuasicoherent :=
  meromorphicSections_isQuasicoherent_of_nonempty_iso_product X F hfinite
    (nonempty_meromorphicSections_iso_pi_genericPointStalkModuleOf hass hfinite F)

/-! ### Part (2) under the hypotheses of the two consumers -/

/-- **Stacks 02OW, part (2), product decomposition.** On a reduced scheme whose quasi-compact
opens have finitely many irreducible components, the sheaf of meromorphic sections of a
quasi-coherent module is the product over the generic points of the irreducible components of
the generic-point contributions. -/
@[stacks 02OW "part (2), product"]
theorem nonempty_meromorphicSections_iso_product_genericPointStalks_of_isReduced
    (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (F : X.Modules) [F.IsQuasicoherent] :
    Nonempty (meromorphicSections X F ≅
      ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) :=
  nonempty_meromorphicSections_iso_pi_genericPointStalkModuleOf
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).subset hfinite F

/-- **Stacks 02OW, part (2), direct-sum decomposition.** -/
@[stacks 02OW "part (2), direct sum"]
theorem nonempty_meromorphicSections_iso_coproduct_genericPointStalks_of_isReduced
    (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (F : X.Modules) [F.IsQuasicoherent] :
    Nonempty (meromorphicSections X F ≅
      ∐ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) :=
  nonempty_meromorphicSections_iso_sigma_genericPointStalkModuleOf
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).subset hfinite F

/-- **Stacks 02OW, part (2), quasi-coherence.** -/
@[stacks 02OW "part (2), quasi-coherence"]
theorem meromorphicSections_isQuasicoherent_of_isReduced
    (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (F : X.Modules) [F.IsQuasicoherent] :
    (meromorphicSections X F).IsQuasicoherent :=
  meromorphicSections_isQuasicoherent_of_genericHypotheses
    (weaklyAssociatedPointsOfScheme_eq_genericPoints X).subset hfinite F

/-- **Stacks 0EMH**, the product decomposition of the sheaf of meromorphic sections. -/
@[stacks 0EMH "meromorphic sections as a product"]
theorem nonempty_meromorphicSections_iso_product_genericPointStalks_of_hasNoEmbeddedPoints
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : HasNoEmbeddedPoints X)
    (F : X.Modules) [F.IsQuasicoherent] :
    Nonempty (meromorphicSections X F ≅
      ∏ᶜ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) :=
  nonempty_meromorphicSections_iso_pi_genericPointStalkModuleOf
    (schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints X hX).le
    (finite_irreducibleComponents_of_isCompact X) F

/-- **Stacks 0EMH**, the direct-sum decomposition of the sheaf of meromorphic sections. -/
@[stacks 0EMH "meromorphic sections as a direct sum"]
theorem nonempty_meromorphicSections_iso_coproduct_genericPointStalks_of_hasNoEmbeddedPoints
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : HasNoEmbeddedPoints X)
    (F : X.Modules) [F.IsQuasicoherent] :
    Nonempty (meromorphicSections X F ≅
      ∐ fun η : genericPoints X ↦ genericPointStalkModuleOf X F η) :=
  nonempty_meromorphicSections_iso_sigma_genericPointStalkModuleOf
    (schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints X hX).le
    (finite_irreducibleComponents_of_isCompact X) F

/-- **Stacks 0EMH**, quasi-coherence of the sheaf of meromorphic sections. -/
@[stacks 0EMH "quasi-coherence of meromorphic sections"]
theorem meromorphicSections_isQuasicoherent_of_hasNoEmbeddedPoints
    (X : Scheme.{u}) [IsLocallyNoetherian X] (hX : HasNoEmbeddedPoints X)
    (F : X.Modules) [F.IsQuasicoherent] :
    (meromorphicSections X F).IsQuasicoherent :=
  meromorphicSections_isQuasicoherent_of_genericHypotheses
    (schemeWeaklyAssociatedPoints_eq_genericPoints_of_hasNoEmbeddedPoints X hX).le
    (finite_irreducibleComponents_of_isCompact X) F

end AlgebraicGeometry
