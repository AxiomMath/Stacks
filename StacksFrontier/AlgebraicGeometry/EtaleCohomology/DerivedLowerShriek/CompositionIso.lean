module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.FiniteComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ModuleDerivedProperBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.DerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ThickeningInvariance
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryPlusCompIsoh
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactIdentityComparison
import StacksCore.Tactic.StacksAttribute

/-!
# The composition of derived lower shrieks ([Stacks, Tag 0F7J])

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be separated morphisms of finite type of quasi-compact and
quasi-separated schemes and let `Λ` be a ring. Then `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` on
`D⁺_tors(X_étale, Λ)`.

The proof is the source's. Choose a compactification `i : Y ⟶ Ȳ` of `Y` over `Z`, a
compactification `X ⟶ X̄` of `X` over `Ȳ`, and let `U = X̄ ×_Ȳ Y`, with `j' : U ⟶ X̄`,
`f' : U ⟶ Y` and `f̄ : X̄ ⟶ Ȳ`. The assembly
`Stacks.EtaleCohomology.derivedLowerShriekCompOverIsoOfBaseChange` reduces the statement to the
identification `Rf̄_* ∘ j'_! ≅ i_! ∘ Rf'_*` on `D⁺_tors(U_étale, Λ)`, the case of an open immersion
of [Stacks, Tag 0F7B]. That identification is built here: the transformation
`i_! Rf'_* ⟶ Rf̄_* j'_!` adjoint to `Rf'_* ≅ Rf'_* j'^{-1} j'_! ≅ i^{-1} Rf̄_* j'_!` (proper base
change along `i`, [Stacks, Tag 0DDE]) is invertible after restriction to `Y`, `i_!` being fully
faithful, and after restriction to the closed complement of `Y`, where both sides vanish (proper
base change along the complement). Restrictions to an open and to its closed complement jointly
reflect isomorphisms of `D⁺`, through the cohomology sheaves.

Independence of the compactifications is [Stacks, Tag 0F7I]
(`Stacks.EtaleCohomology.derivedLowerShriekCompactificationIso`): the isomorphism is stated for
arbitrary compactifications of `f`, `g` and `g ∘ f`.

Everything is stated in the standard model `HasDerivedCategory.standard` of the derived
category, the model in which `Stacks.EtaleCohomology.derivedLowerShriek` is defined.

## Main results

* `Stacks.EtaleCohomology.isIso_of_isIso_etaleModuleDerivedInverseImagePlus`: restrictions to an
  open and to its closed complement jointly reflect isomorphisms of `D⁺(X_étale, Λ)`.
* `Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper`:
  `Rf̄_* ∘ j'_! ≅ i_! ∘ Rf'_*` on `D⁺_tors` for `f̄` proper and `i` an open immersion.
* `Stacks.EtaleCohomology.derivedLowerShriekCompIso`: **[Stacks, Tag 0F7J]**.
* `Stacks.EtaleCohomology.isTorsionPlus_derivedLowerShriek_obj`: `Rf_!` carries `D⁺_tors` into
  `D⁺_tors`.

## References

* [Stacks Project, Tag 0F7J](https://stacks.math.columbia.edu/tag/0F7J)
* [Stacks Project, Tag 0F7B](https://stacks.math.columbia.edu/tag/0F7B)
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 0F7I](https://stacks.math.columbia.edu/tag/0F7I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

-- the structure projections of `Stacks.Models.RegularModelSituation` are global instances whose
-- conclusions (`Field ?k`, `QuasiCompact ?f`, ...) match every goal and send instance search
-- through `Submodule ?R ?R`; they are irrelevant here
attribute [-instance] Stacks.Models.RegularModelSituation.commRingR
  Stacks.Models.RegularModelSituation.isDomainR
  Stacks.Models.RegularModelSituation.isDiscreteValuationRingR
  Stacks.Models.RegularModelSituation.fieldK Stacks.Models.RegularModelSituation.algebraRK
  Stacks.Models.RegularModelSituation.isFractionRingRK Stacks.Models.RegularModelSituation.fieldk
  Stacks.Models.RegularModelSituation.algebraRk Stacks.Models.RegularModelSituation.isCurve
  Stacks.Models.RegularModelSituation.smooth Stacks.Models.RegularModelSituation.flat
  Stacks.Models.RegularModelSituation.locallyOfFiniteType
  Stacks.Models.RegularModelSituation.quasiCompact

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (Λ : Type) [Ring Λ]

/-! ### Cohomology sheaves and restriction -/

section Homology

/-- An object of `D⁺(𝒜)` all of whose cohomology objects vanish is zero. -/
theorem isZero_of_forall_isZero_homology_plus {C : Type*} [Category* C]
    [Abelian C] [HasDerivedCategory C] (K : DerivedCategory.Plus C)
    (h : ∀ q : ℤ, IsZero ((DerivedCategory.Plus.homologyFunctor C q).obj K)) : IsZero K := by
  have : IsIso (0 : K ⟶ K) := by
    rw [DerivedCategory.Plus.isIso_iff]
    intro q
    exact (h q).isIso (h q) _
  rw [IsZero.iff_id_eq_zero, ← IsIso.inv_hom_id (0 : K ⟶ K), comp_zero]

/-- The cohomology sheaves of the inverse image of an object of `D⁺` are the inverse images of
its cohomology sheaves, inverse image being exact. -/
def etaleModuleDerivedInverseImagePlusHomologyIso {W X : Scheme.{u}} (e : W ⟶ X)
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ q).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ e).obj K) ≅
      (etaleModuleInverseImage.{u, 0} Λ e).obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K) :=
  (Stacks.Homology.derivedHomologyIso (etaleModuleInverseImage.{u, 0} Λ e) q).app
    (DerivedCategory.Plus.ι.obj K)

/-- The cohomology sheaves of the derived extension by zero of an object of `D⁺` are the
extensions by zero of its cohomology sheaves, extension by zero being exact. -/
def etaleModuleDerivedExtensionByZeroHomologyIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j]
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ U)) (q : ℤ) :
    (DerivedCategory.Plus.homologyFunctor _ q).obj
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j).obj K) ≅
      (etaleModuleExtensionByZero.{u, 0} Λ j).obj
        ((DerivedCategory.Plus.homologyFunctor _ q).obj K) :=
  (DerivedCategory.Plus.homologyFunctor _ q).mapIso
      ((Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus
        (etaleModuleExtensionByZero.{u, 0} Λ j)).app K) ≪≫
    (Stacks.Homology.derivedHomologyIso (etaleModuleExtensionByZero.{u, 0} Λ j) q).app
      (DerivedCategory.Plus.ι.obj K)

/-- If the inverse image along `e` of a morphism of `D⁺` is invertible, so is the inverse image of
each of its cohomology sheaves. -/
theorem isIso_etaleModuleInverseImage_map_homology_of_isIso {W X : Scheme.{u}} (e : W ⟶ X)
    {K L : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)} (γ : K ⟶ L) (q : ℤ)
    (h : IsIso ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ e).map γ)) :
    IsIso ((etaleModuleInverseImage.{u, 0} Λ e).map
      ((DerivedCategory.Plus.homologyFunctor _ q).map γ)) := by
  have h1 : IsIso (((etaleModuleInverseImage.{u, 0} Λ e).mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor _ q).map (DerivedCategory.Plus.ι.map γ)) := by
    change IsIso ((DerivedCategory.Plus.homologyFunctor _ q).map
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ e).map γ))
    infer_instance
  exact (NatIso.isIso_map_iff
    (Stacks.Homology.derivedHomologyIso (etaleModuleInverseImage.{u, 0} Λ e) q) _).mp h1

/-- **Restrictions to an open and to its closed complement jointly reflect isomorphisms of
`D⁺(X_étale, Λ)`.** A morphism of `D⁺` is invertible when its cohomology sheaves are, inverse
images commute with cohomology sheaves, and on sheaves of modules the two inverse images jointly
reflect isomorphisms (the module form of [Stacks, Tag 095L]). -/
theorem isIso_of_isIso_etaleModuleDerivedInverseImagePlus {Z U X : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (j : U ⟶ X) [IsOpenImmersion j]
    (hij : Set.range j.base = (Set.range i.base)ᶜ)
    {K L : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X)} (γ : K ⟶ L)
    (hi : IsIso ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map γ))
    (hj : IsIso ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ j).map γ)) : IsIso γ := by
  rw [DerivedCategory.Plus.isIso_iff]
  intro q
  haveI := isIso_etaleModuleInverseImage_map_homology_of_isIso Λ i γ q hi
  haveI := isIso_etaleModuleInverseImage_map_homology_of_isIso Λ j γ q hj
  exact isIso_of_isIso_etaleModuleInverseImage Λ i j hij _

/-- The inverse image along `c` of a derived extension by zero along `j` vanishes when the images
of `c` and `j` are disjoint. -/
theorem isZero_etaleModuleDerivedInverseImagePlus_extensionByZero_of_disjoint {W U X : Scheme.{u}}
    (c : W ⟶ X) (j : U ⟶ X) [Etale j] (hcj : Disjoint (Set.range c.base) (Set.range j.base))
    (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ U)) :
    IsZero ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).obj
      ((etaleModuleDerivedExtensionByZero.{u, 0} Λ j).obj K)) := by
  refine isZero_of_forall_isZero_homology_plus _ fun q => ?_
  refine IsZero.of_iso ?_ (etaleModuleDerivedInverseImagePlusHomologyIso Λ c _ q ≪≫
    (etaleModuleInverseImage.{u, 0} Λ c).mapIso (etaleModuleDerivedExtensionByZeroHomologyIso Λ j K q))
  exact isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ c j hcj _

end Homology

/-! ### Restriction along an open immersion on `D⁺` -/

section Restriction

variable {U X : Scheme.{u}} (j : U ⟶ X)

/-- On `D⁺`, derived restriction along an étale morphism is the inverse image: both are exact,
and they agree on sheaves (`Stacks.EtaleCohomology.etaleModuleInverseImageRestrictionIso`). -/
def etaleModuleDerivedRestrictionIsoInverseImagePlus [Etale j] :
    etaleModuleDerivedRestriction.{u, 0} Λ j ≅ etaleModuleDerivedInverseImagePlus.{u, 0} Λ j :=
  Functor.rightDerivedFunctorPlusIsoMapDerivedCategoryPlus (etaleModuleRestriction.{u, 0} Λ j) ≪≫
    (Functor.rightUnitor _).symm ≪≫
    Functor.isoWhiskerLeft _ Functor.mapDerivedCategoryPlusIdIso.symm ≪≫
    Functor.mapDerivedCategoryPlusCompIsoh
      (Functor.rightUnitor _ ≪≫ (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).symm)

/-- **Derived restriction undoes derived extension by zero along an open immersion**:
`j^{-1} ∘ Rj_! ≅ 𝟭` on `D⁺(U_étale, Λ)`. Both functors are exact and the underived unit is
invertible. -/
def etaleModuleDerivedExtensionByZeroCompRestrictionIso [IsOpenImmersion j] :
    etaleModuleDerivedExtensionByZero.{u, 0} Λ j ⋙ etaleModuleDerivedRestriction.{u, 0} Λ j ≅
      𝟭 _ :=
  Functor.rightDerivedFunctorPlusCompIsoOfExact (etaleModuleExtensionByZero.{u, 0} Λ j)
      (etaleModuleRestriction.{u, 0} Λ j) _ (Iso.refl _) ≪≫
    Functor.rightDerivedFunctorPlusIdIsoOf _ (asIso (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit).symm

/-- The unit of `Rj_! ⊣ j^{-1}` on `D⁺` is invertible for an open immersion `j`. -/
instance isIso_etaleModuleDerivedExtensionByZeroAdj_unit [IsOpenImmersion j] :
    IsIso (etaleModuleDerivedExtensionByZeroAdj.{u, 0} Λ j).unit :=
  (etaleModuleDerivedExtensionByZeroAdj.{u, 0} Λ j).isIso_unit_of_iso
    (etaleModuleDerivedExtensionByZeroCompRestrictionIso Λ j)

/-- **The inverse image undoes derived extension by zero along an open immersion**:
`j^{-1} ∘ Rj_! ≅ 𝟭` on `D⁺(U_étale, Λ)`, with `j^{-1}` the inverse image. -/
def etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso [IsOpenImmersion j] :
    etaleModuleDerivedExtensionByZero.{u, 0} Λ j ⋙ etaleModuleDerivedInverseImagePlus.{u, 0} Λ j ≅
      𝟭 _ :=
  Functor.isoWhiskerLeft _ (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ j).symm ≪≫
    etaleModuleDerivedExtensionByZeroCompRestrictionIso Λ j

end Restriction

/-! ### The open immersion case of [Stacks, Tag 0F7B] -/

section OpenBaseChange

variable {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
  (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i)

/-- The isomorphism `Rf'_* ≅ i^{-1} Rf̄_* Rb_!` on `D⁺_tors(P_étale, Λ)`: `Rb_!` followed by
`b^{-1}` is the identity, and `i^{-1} Rf̄_* ≅ Rf'_* b^{-1}` on torsion objects is proper base
change ([Stacks, Tag 0DDE]), at `Rb_! K`, which has torsion cohomology sheaves. -/
def etaleModuleDerivedDirectImageIsoRestrictionOfIsProper :
    (isTorsionPlus.{u, 0} Λ P).ι ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ f' ≅
      (isTorsionPlus.{u, 0} Λ P).ι ⋙ etaleModuleDerivedExtensionByZero.{u, 0} Λ b ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ fb ⋙ etaleModuleDerivedRestriction.{u, 0} Λ i := by
  let BC := etaleModuleDerivedBaseChange.{u, 0} Λ fb f' i b sq.w.symm
  haveI : ∀ K : (isTorsionPlus.{u, 0} Λ P).FullSubcategory,
      IsIso ((Functor.whiskerLeft ((isTorsionPlus.{u, 0} Λ P).ι ⋙
        etaleModuleDerivedExtensionByZero.{u, 0} Λ b) BC).app K) := fun K =>
    isIso_etaleModuleDerivedBaseChange_of_isProper Λ fb sq _
      (isTorsionPlus_etaleModuleDerivedExtensionByZero_obj Λ b K.obj K.property)
  haveI : IsIso (Functor.whiskerLeft ((isTorsionPlus.{u, 0} Λ P).ι ⋙
      etaleModuleDerivedExtensionByZero.{u, 0} Λ b) BC) := NatIso.isIso_of_isIso_app _
  exact (Functor.isoWhiskerLeft (isTorsionPlus.{u, 0} Λ P).ι
        (Functor.leftUnitor _).symm ≪≫
      Functor.isoWhiskerLeft (isTorsionPlus.{u, 0} Λ P).ι
        (Functor.isoWhiskerRight (etaleModuleDerivedExtensionByZeroCompInverseImagePlusIso Λ b).symm
          (etaleModuleDerivedDirectImage.{u, 0} Λ f'))) ≪≫
    (asIso (Functor.whiskerLeft ((isTorsionPlus.{u, 0} Λ P).ι ⋙
      etaleModuleDerivedExtensionByZero.{u, 0} Λ b) BC)).symm ≪≫
    Functor.isoWhiskerLeft ((isTorsionPlus.{u, 0} Λ P).ι ⋙
        etaleModuleDerivedExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ fb)
      (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ i).symm

/-- The transformation `i_! Rf'_* ⟶ Rf̄_* Rb_!` on `D⁺_tors(P_étale, Λ)`, adjoint under
`Ri_! ⊣ i^{-1}` to `etaleModuleDerivedDirectImageIsoRestrictionOfIsProper`. -/
@[sga "4 XVII 7.0.3" "special case"]
def etaleModuleDerivedExtensionByZeroDirectImageMapOfIsProper :
    (isTorsionPlus.{u, 0} Λ P).ι ⋙ etaleModuleDerivedDirectImage.{u, 0} Λ f' ⋙
        etaleModuleDerivedExtensionByZero.{u, 0} Λ i ⟶
      (isTorsionPlus.{u, 0} Λ P).ι ⋙ etaleModuleDerivedExtensionByZero.{u, 0} Λ b ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ fb :=
  Functor.whiskerRight (etaleModuleDerivedDirectImageIsoRestrictionOfIsProper Λ fb i b f' sq).hom
      (etaleModuleDerivedExtensionByZero.{u, 0} Λ i) ≫
    Functor.whiskerLeft ((isTorsionPlus.{u, 0} Λ P).ι ⋙ etaleModuleDerivedExtensionByZero.{u, 0} Λ b ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ fb)
      (etaleModuleDerivedExtensionByZeroAdj.{u, 0} Λ i).counit

/-- The map `i_! Rf'_* K ⟶ Rf̄_* Rb_! K` is invertible for `K` with torsion cohomology sheaves.
Over `Y` its restriction is, up to the invertible unit of `Ri_! ⊣ i^{-1}`, the isomorphism it is
adjoint to. Over a closed complement `c : W ⟶ Ū` of `Y` both sides vanish: the source because
`c^{-1} i_! = 0`, the target by proper base change along `c`
(`Stacks.EtaleCohomology.isIso_etaleModuleDerivedBaseChange_of_isProper`), the inverse image of
`Rb_! K` to `W ×_Ū T` being zero. -/
@[sga "4 XVII 7.0.3" "special case"]
theorem isIso_etaleModuleDerivedExtensionByZeroDirectImageMapOfIsProper_app
    (K : (isTorsionPlus.{u, 0} Λ P).FullSubcategory) :
    IsIso ((etaleModuleDerivedExtensionByZeroDirectImageMapOfIsProper Λ fb i b f' sq).app K) := by
  let Zc : Ub.IdealSheafData := Scheme.IdealSheafData.vanishingIdeal
    ⟨(Set.range i.base)ᶜ, i.isOpenEmbedding.isOpen_range.isClosed_compl⟩
  let c := Zc.subschemeι
  have hic : Set.range i.base = (Set.range c.base)ᶜ := by
    rw [Scheme.IdealSheafData.range_subschemeι,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact (compl_compl _).symm
  let φ := (etaleModuleDerivedExtensionByZeroDirectImageMapOfIsProper Λ fb i b f' sq).app K
  -- over the open `Y`
  have hY : IsIso ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ i).map φ) := by
    rw [← NatIso.isIso_map_iff (etaleModuleDerivedRestrictionIsoInverseImagePlus Λ i)]
    have hφ : φ = (etaleModuleDerivedExtensionByZero.{u, 0} Λ i).map
        ((etaleModuleDerivedDirectImageIsoRestrictionOfIsProper Λ fb i b f' sq).hom.app K) ≫
        (etaleModuleDerivedExtensionByZeroAdj.{u, 0} Λ i).counit.app _ := rfl
    have htri := (etaleModuleDerivedExtensionByZeroAdj.{u, 0} Λ i).right_triangle_components
      ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ fb).obj K.obj)
    have hε : IsIso ((etaleModuleDerivedRestriction.{u, 0} Λ i).map
        ((etaleModuleDerivedExtensionByZeroAdj.{u, 0} Λ i).counit.app
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b ⋙
            etaleModuleDerivedDirectImage.{u, 0} Λ fb).obj K.obj))) :=
      IsIso.of_isIso_fac_left htri
    rw [hφ, Functor.map_comp]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ (Functor.map_isIso _ _) hε
  -- over the closed complement
  have hZ : IsIso ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).map φ) := by
    have h₁ : IsZero ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).obj
        ((etaleModuleDerivedExtensionByZero.{u, 0} Λ i).obj
          ((etaleModuleDerivedDirectImage.{u, 0} Λ f').obj K.obj))) := by
      refine isZero_etaleModuleDerivedInverseImagePlus_extensionByZero_of_disjoint Λ c i ?_ _
      rw [hic]
      exact disjoint_compl_right
    have sqc := IsPullback.of_hasPullback fb c
    have hT := isIso_etaleModuleDerivedBaseChange_of_isProper Λ fb sqc
      ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b).obj K.obj)
      (isTorsionPlus_etaleModuleDerivedExtensionByZero_obj Λ b K.obj K.property)
    have h₂ : IsZero ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ c).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ fb).obj
          ((etaleModuleDerivedExtensionByZero.{u, 0} Λ b).obj K.obj))) := by
      refine IsZero.of_iso ?_ (asIso ((etaleModuleDerivedBaseChange.{u, 0} Λ fb
        (pullback.snd fb c) c (pullback.fst fb c) sqc.w.symm).app _))
      refine (etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd fb c)).map_isZero ?_
      refine isZero_etaleModuleDerivedInverseImagePlus_extensionByZero_of_disjoint Λ _ b ?_ _
      rw [Set.disjoint_left]
      rintro _ ⟨z, rfl⟩ ⟨x, hx⟩
      have h₁ : fb.base ((pullback.fst fb c).base z) ∈ Set.range c.base :=
        ⟨(pullback.snd fb c).base z, by
          rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply]⟩
      have h₂ : fb.base ((pullback.fst fb c).base z) ∈ Set.range i.base :=
        ⟨f'.base x, by rw [← hx, ← Scheme.Hom.comp_apply, ← sq.w, Scheme.Hom.comp_apply]⟩
      rw [hic] at h₂
      exact h₂ h₁
    exact h₁.isIso h₂ _
  exact isIso_of_isIso_etaleModuleDerivedInverseImagePlus Λ c i hic φ hZ hY

/-- **The open immersion case of [Stacks, Tag 0F7B]**: for a cartesian square
`b ≫ f̄ = f' ≫ i` with `f̄` proper and `i` an open immersion, `Rf̄_* ∘ Rb_! ≅ Ri_! ∘ Rf'_*` on
`D⁺_tors(P_étale, Λ)`, for an arbitrary ring `Λ`. -/
def etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper :
    (isTorsionPlus.{u, 0} Λ P).ι ⋙ (etaleModuleDerivedExtensionByZero.{u, 0} Λ b ⋙
        etaleModuleDerivedDirectImage.{u, 0} Λ fb) ≅
      (isTorsionPlus.{u, 0} Λ P).ι ⋙ (etaleModuleDerivedDirectImage.{u, 0} Λ f' ⋙
        etaleModuleDerivedExtensionByZero.{u, 0} Λ i) :=
  haveI : ∀ K, IsIso ((etaleModuleDerivedExtensionByZeroDirectImageMapOfIsProper Λ fb i b f'
      sq).app K) := fun K =>
    isIso_etaleModuleDerivedExtensionByZeroDirectImageMapOfIsProper_app Λ fb i b f' sq K
  haveI : IsIso (etaleModuleDerivedExtensionByZeroDirectImageMapOfIsProper Λ fb i b f' sq) :=
    NatIso.isIso_of_isIso_app _
  (asIso (etaleModuleDerivedExtensionByZeroDirectImageMapOfIsProper Λ fb i b f' sq)).symm

end OpenBaseChange

/-! ### [Stacks, Tag 0F7J] -/

section Composition

/-- A proper morphism is quasi-compact and quasi-separated. -/
private theorem quasiCompact_and_quasiSeparated_of_isProper {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsProper f] : QuasiCompact f ∧ QuasiSeparated f := by
  have : UniversallyClosed f := IsProper.toUniversallyClosed
  have : IsSeparated f := IsProper.toIsSeparated
  exact ⟨instQuasiCompactOfUniversallyClosed f, IsSeparated.instQuasiSeparated f⟩

/-- **`Rf_!` carries `D⁺_tors` into `D⁺_tors`**, for any compactification: `j_!` does
(`Stacks.EtaleCohomology.isTorsionPlus_etaleModuleDerivedExtensionByZero_obj`), and so does the
derived direct image along the proper morphism `X̄ ⟶ Y`
(`Stacks.EtaleCohomology.isTorsionPlus_etaleModuleDerivedDirectImage_obj`). This is what makes
`Rg_! ∘ Rf_!` a functor on `D⁺_tors` in [Stacks, Tag 0F7J]. -/
theorem isTorsionPlus_derivedLowerShriek_obj {X Y : Scheme.{u}} (f : X ⟶ Y)
    (j : CompactificationOf (Over.mk f)) (K : DerivedCategory.Plus (EtaleModules.{u, 0} Λ X))
    (hK : isTorsionPlus.{u, 0} Λ X K) :
    isTorsionPlus.{u, 0} Λ Y ((derivedLowerShriek.{u, 0} f j Λ).obj K) := by
  obtain ⟨_, _⟩ := quasiCompact_and_quasiSeparated_of_isProper j.toBase
  exact isTorsionPlus_etaleModuleDerivedDirectImage_obj Λ j.toBase _
    (isTorsionPlus_etaleModuleDerivedExtensionByZero_obj Λ j.immersion K hK)

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)

/-- **`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` through the compactifications of the proof of
[Stacks, Tag 0F7J]**: for a compactification `i : Y ⟶ Ȳ` of `g` and a compactification
`X ⟶ X̄` of `X` over `Ȳ`, with `Rf_!` computed through `X ⟶ X̄ ×_Ȳ Y` and `R(g ∘ f)_!` through
`X ⟶ X̄ ⟶ Ȳ ⟶ Z`. The open immersion case of [Stacks, Tag 0F7B]
(`Stacks.EtaleCohomology.etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper`) is the input
of the assembly `Stacks.EtaleCohomology.derivedLowerShriekCompOverIsoOfBaseChange`. -/
def derivedLowerShriekCompOverIso (jg : CompactificationOf (Over.mk g))
    (jX : CompactificationOf (Over.mk (f ≫ jg.immersion))) :
    (isTorsionPlus.{u, 0} Λ X).ι ⋙
        derivedLowerShriek.{u, 0} (f ≫ g) (CompactificationOf.compOver jg jX) Λ ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙
        derivedLowerShriek.{u, 0} f (CompactificationOf.restrictBase jg jX) Λ ⋙
          derivedLowerShriek.{u, 0} g jg Λ :=
  derivedLowerShriekCompOverIsoOfBaseChange Λ jg jX
    (etaleModuleDerivedExtensionByZeroDirectImageIsoOfIsProper Λ jX.toBase jg.immersion
      (CompactificationOf.restrictBaseι jg jX) (CompactificationOf.restrictBase jg jX).toBase
      (IsPullback.of_hasPullback jX.toBase jg.immersion))
    (fun K hK => isTorsionPlus_etaleModuleDerivedExtensionByZero_obj Λ _ K hK)

/-- A compactification of `X ⟶ Y ⟶ Ȳ` over `Ȳ`, for a compactification `Y ⟶ Ȳ` of `Y` over a
quasi-compact quasi-separated `Z` and `f` separated of finite type with `X` quasi-compact: Nagata's
theorem, [Stacks, Tag 0F41]. -/
theorem nonempty_compactificationOf_comp_immersion [CompactSpace X] [QuasiSeparatedSpace Z]
    [CompactSpace Z] [IsSeparated f] [LocallyOfFiniteType f]
    (jg : CompactificationOf (Over.mk g)) :
    Nonempty (CompactificationOf (Over.mk (f ≫ jg.immersion))) := by
  obtain ⟨_, _⟩ := quasiCompact_and_quasiSeparated_of_isProper jg.toBase
  have : CompactSpace jg.space := QuasiCompact.compactSpace_of_compactSpace jg.toBase
  have : QuasiSeparatedSpace jg.space := quasiSeparatedSpace_of_quasiSeparated jg.toBase
  have : QuasiCompact (f ≫ jg.immersion) := quasiCompact_of_compactSpace _
  exact IsCofiltered.nonempty

/-- **Stacks Project, Tag 0F7J.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be separated morphisms of
finite type of quasi-compact and quasi-separated schemes, and let `Λ` be a ring. Then
`R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` as functors on `D⁺_tors(X_étale, Λ)`, where `Rf_!`, `Rg_!` and
`R(g ∘ f)_!` are computed through arbitrary compactifications `jf`, `jg` and `j`.

The isomorphism is that of the source: through a compactification `X ⟶ X̄` of `X` over `Ȳ`
(Nagata's theorem, [Stacks, Tag 0F41]) it is
`R(ḡ ∘ f̄)_* (j' ∘ j)_! ≅ Rḡ_* Rf̄_* j'_! j_! ≅ Rḡ_* i_! Rf'_* j_!`
(`Stacks.EtaleCohomology.derivedLowerShriekCompOverIso`, which uses [Stacks, Tag 0F7B] for the
open immersion `i`), and it is transported to the given compactifications by
[Stacks, Tag 0F7I] (`Stacks.EtaleCohomology.derivedLowerShriekCompactificationIso`), which is the
independence of the choices made. `Rf_!` carries `D⁺_tors` into `D⁺_tors` by
`Stacks.EtaleCohomology.isTorsionPlus_derivedLowerShriek_obj`. -/
@[stacks 0F7J]
def derivedLowerShriekCompIso [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z] [IsSeparated f]
    [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]
    (jf : CompactificationOf (Over.mk f)) (jg : CompactificationOf (Over.mk g))
    (j : CompactificationOf (Over.mk (f ≫ g))) :
    (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} (f ≫ g) j Λ ≅
      (isTorsionPlus.{u, 0} Λ X).ι ⋙ derivedLowerShriek.{u, 0} f jf Λ ⋙
        derivedLowerShriek.{u, 0} g jg Λ :=
  haveI : QuasiCompact f := quasiCompact_of_compactSpace f
  haveI : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  let jX := (nonempty_compactificationOf_comp_immersion f g jg).some
  derivedLowerShriekCompactificationIso (f ≫ g) j (CompactificationOf.compOver jg jX) Λ ≪≫
    derivedLowerShriekCompOverIso Λ f g jg jX ≪≫
    Functor.isoWhiskerRight
      (derivedLowerShriekCompactificationIso f (CompactificationOf.restrictBase jg jX) jf Λ)
      (derivedLowerShriek.{u, 0} g jg Λ)

end Composition

end Stacks.EtaleCohomology

end
