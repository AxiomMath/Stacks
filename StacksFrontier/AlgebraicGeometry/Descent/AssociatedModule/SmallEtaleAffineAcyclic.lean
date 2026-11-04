module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedSections
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCounit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CechComparison.QuasiCoherentAffineAcyclicity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleRingedSiteGrothendieck
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.StalkComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.CechAmitsurSmallSites
public import StacksFrontier.AlgebraicGeometry.Topologies.SmallEtaleAbelian
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ObjectSections.DerivedSectionsVanishing
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A quasi-coherent module on the small étale site is acyclic on affine objects

Let `S` be a scheme contained in a big étale site `B`, and let `𝓗` be a quasi-coherent
`𝒪`-module on the small étale site `S_étale`, `AlgebraicGeometry.SmallEtale B S hS`. This file
proves that for every object `V` of `S_étale` whose underlying scheme is affine and every `p > 0`

```
H^p(V, 𝓗) = 0,
```

as the vanishing of the `p`-th right derived functor of the module-valued sections over `V`.

## Main results

* `AlgebraicGeometry.SmallEtale.isZero_sheafH'_restrict_fpqcOverAssociatedSheaf`: the higher
  cohomology of the restriction of `𝓕ᵃ` vanishes on affine objects.
* `AlgebraicGeometry.SmallEtale.isZero_rightDerived_evaluation_of_isAffine`: the higher
  cohomology of a quasi-coherent `𝒪`-module vanishes on affine objects.

## References

* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
* [Stacks Project, Tag 03XA](https://stacks.math.columbia.edu/tag/03XA)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.CechSite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The data of the Čech criterion -/

/-- The objects of the small étale site with affine underlying scheme. -/
public def affineObjectSet : Set (SmallEtale B S hS) :=
  {V | AlgebraicGeometry.IsAffine ((toScheme B S hS).obj V)}

/-- The coverings of an object of the small étale site whose image in Mathlib's small étale site
is a small-étale-standard covering, i.e. a standard étale covering of an affine in the sense of
[Stacks, Tag 03X9]. -/
public def affineStandardCoverings (U : SmallEtale B S hS) :
    Set { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ topology B S hS U } :=
  {E | IsSmallEtaleStandardCovering S (E.1.map (toEtaleSite B S hS))}

/-- The iterated fibre products of a covering in `affineStandardCoverings` exist. -/
public theorem affineStandardCoverings_hasProducts :
    ∀ {U : SmallEtale B S hS}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ topology B S hS U }),
      E ∈ affineStandardCoverings B S hS U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))) :=
  fun E _ p i ↦ Stacks.Sites.hasProduct_fibreProducts E.1 (fun _ _ _ ↦ inferInstance) p i

/-- The iterated fibre products of the image in Mathlib's small étale site of a covering in
`affineStandardCoverings` exist. -/
public theorem affineStandardCoverings_hasImageProducts :
    ∀ {U : SmallEtale B S hS}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ topology B S hS U }),
      E ∈ affineStandardCoverings B S hS U → ∀ (p : ℕ)
        (i : Fin (p + 1) → (E.1.map (toEtaleSite B S hS)).I₀),
        HasProduct (fun a ↦ Over.mk ((E.1.map (toEtaleSite B S hS)).f (i a))) :=
  fun _ _ _ _ ↦ inferInstance

/-- A functor preserving pullbacks, out of a category with pullbacks, preserves the iterated fibre
products of a family of arrows into `U`. -/
private theorem preservesLimit_overPost_fibreProducts {C D : Type*} [Category C] [Category D]
    [HasPullbacks C] {U : C} (u : C ⥤ D) [PreservesLimitsOfShape WalkingCospan u]
    (E : PreZeroHypercover.{u} U) (p : ℕ) (i : Fin (p + 1) → E.I₀) :
    PreservesLimit (Discrete.functor (fun a ↦ Over.mk (E.f (i a)))) (Over.post (X := U) u) :=
  Stacks.Sites.preservesLimit_fibreProducts_overPost u E
    (fun _ _ _ ↦ inferInstance) (fun _ _ _ ↦ inferInstance) p i

/-- An iterated fibre product, in the small étale site, of objects with affine underlying scheme
over an object with affine underlying scheme again has affine underlying scheme. -/
public theorem isAffine_toScheme_piObj {U : SmallEtale B S hS}
    (hU : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj U)) (E : PreZeroHypercover.{u} U)
    (hX : ∀ i, AlgebraicGeometry.IsAffine ((toScheme B S hS).obj (E.X i))) (p : ℕ)
    (i : Fin (p + 1) → E.I₀) :
    letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.I₀),
        HasProduct (fun a ↦ Over.mk (E.f (j a))) := fun q j ↦
      Stacks.Sites.hasProduct_fibreProducts E (fun _ _ _ ↦ inferInstance) q j
    AlgebraicGeometry.IsAffine ((toScheme B S hS).obj (∏ᶜ (fun a ↦ Over.mk (E.f (i a)))).left) := by
  let w : SmallEtale B S hS ⥤ Scheme.{u} := toScheme B S hS
  let A : Fin (p + 1) → Over U := fun a ↦ Over.mk (E.f (i a))
  let _ : AlgebraicGeometry.IsAffine (w.obj U) := hU
  have := preservesLimit_overPost_fibreProducts w E p i
  have hF : ∀ a, IsAffineHom ((Over.post (X := U) w).obj (A a)).hom := fun a ↦ by
    let _ : AlgebraicGeometry.IsAffine ((Over.post (X := U) w).obj (A a)).left := hX (i a)
    exact isAffineHom_of_isAffine _
  let _ : IsAffineHom (∏ᶜ (fun a ↦ (Over.post (X := U) w).obj (A a))).hom :=
    isAffineHom_over_finiteProduct _ hF
  have haff : AlgebraicGeometry.IsAffine (∏ᶜ (fun a ↦ (Over.post (X := U) w).obj (A a))).left :=
    isAffine_of_isAffineHom (∏ᶜ (fun a ↦ (Over.post (X := U) w).obj (A a))).hom
  have e : w.obj (∏ᶜ A).left ≅ (∏ᶜ (fun a ↦ (Over.post (X := U) w).obj (A a))).left :=
    (Over.forget (w.obj U)).mapIso (PreservesProduct.iso (Over.post (X := U) w) A)
  exact AlgebraicGeometry.IsAffine.of_isIso e.hom

/-- The target of a covering in `affineStandardCoverings`, each of its members, and each of its
iterated fibre products have affine underlying scheme. -/
public theorem affineStandardCoverings_covObjects :
    ∀ {U : SmallEtale B S hS}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ topology B S hS U })
      (hE : E ∈ affineStandardCoverings B S hS U),
      U ∈ affineObjectSet B S hS ∧ (∀ i, E.1.X i ∈ affineObjectSet B S hS) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) :=
              affineStandardCoverings_hasProducts B S hS E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ affineObjectSet B S hS := by
  intro U E hE
  obtain ⟨hU, hX⟩ := IsSmallEtaleStandardCovering.isAffine S hE
  exact ⟨hU, hX, fun p i ↦ isAffine_toScheme_piObj B S hS hU E.1 hX p i⟩

/-- For a covering in `affineStandardCoverings`, the comparison maps
`Stacks.CechSite.cechProductMapOfFunctor` along the embedding into Mathlib's small étale site are
isomorphisms. -/
public theorem affineStandardCoverings_comparison :
    ∀ {U : SmallEtale B S hS}
      (E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ topology B S hS U })
      (hE : E ∈ affineStandardCoverings B S hS U) (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (j a))) :=
            affineStandardCoverings_hasProducts B S hS E hE
        letI : ∀ (q : ℕ) (j : Fin (q + 1) → (E.1.map (toEtaleSite B S hS)).I₀),
          HasProduct (fun a ↦ Over.mk ((E.1.map (toEtaleSite B S hS)).f (j a))) :=
            affineStandardCoverings_hasImageProducts B S hS E hE
        IsIso (cechProductMapOfFunctor (toEtaleSite B S hS) E.1 p i) := by
  intro U E hE p i
  have := preservesPullbacks_toEtaleSite B S hS
  have := preservesLimit_overPost_fibreProducts (toEtaleSite B S hS) E.1 p i
  exact isIso_cechProductMapOfFunctor (toEtaleSite B S hS) E.1 p i

/-- An object of Mathlib's small étale site with affine underlying scheme, as an object of the
small étale site `AlgebraicGeometry.SmallEtale B S hS`. -/
public def ofAffineEtale (T : S.Etale) (hT : AlgebraicGeometry.IsAffine T.left) :
    SmallEtale B S hS :=
  have := hT
  have hR : B.Contains T.left :=
    (Scheme.size_le_of_locallyOfFiniteType (X := T.left) (S := S) T.hom).trans_lt hS
  ⟨CategoryTheory.Over.mk
      (ObjectProperty.homMk T.hom : B.obj T.left hR ⟶ B.obj S hS), T.prop⟩

/-- Every covering sieve of an object of the small étale site with affine underlying scheme
contains the sieve of a covering in `affineStandardCoverings`. -/
public theorem affineStandardCoverings_cofinal :
    ∀ U ∈ affineObjectSet B S hS, ∀ R ∈ topology B S hS U,
      ∃ E : { E : PreZeroHypercover.{u} U // E.sieve₀ ∈ topology B S hS U },
        E ∈ affineStandardCoverings B S hS U ∧ E.1.sieve₀ ≤ R := by
  intro U hU R hR
  let u := toEtaleSite B S hS
  have hR' : R.functorPushforward u ∈ S.smallEtaleTopology (u.obj U) := by
    have h := topology_le_restrictedTopology B S hS U hR
    rwa [Functor.mem_restrictedTopology_iff] at h
  have hU' : AlgebraicGeometry.IsAffine (u.obj U).left := hU
  obtain ⟨E', hE', hle⟩ := exists_isSmallEtaleStandardCovering_sieve₀_le S hU' hR'
  have hX' := (IsSmallEtaleStandardCovering.isAffine S hE').2
  let X : E'.I₀ → SmallEtale B S hS := fun i ↦ ofAffineEtale B S hS (E'.X i) (hX' i)
  let f : ∀ i, X i ⟶ U := fun i ↦ u.preimage (E'.f i)
  let E : PreZeroHypercover.{u} U := ⟨E'.I₀, X, f⟩
  have hmap : ∀ i, u.map (f i) = E'.f i := fun i ↦ u.map_preimage _
  have hstd : IsSmallEtaleStandardCovering S (E.map u) := by
    obtain ⟨h, hs⟩ := hE'
    refine ⟨h, ?_⟩
    have : (fun i ↦ ((E.map u).f i).left) = fun i ↦ (E'.f i).left :=
      funext fun i ↦ congrArg (fun φ ↦ φ.left) (hmap i)
    convert hs using 1 <;> first | rfl | exact heq_of_eq this
  have hsieve : E.sieve₀ ≤ R := by
    rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro W g ⟨i⟩
    obtain ⟨Z, g', k, hg', hfac⟩ := hle _ (Sieve.ofArrows_mk _ _ i)
    have : f i = u.preimage (show u.obj (X i) ⟶ u.obj Z from k) ≫ g' :=
      u.map_injective (by rw [hmap, Functor.map_comp, Functor.map_preimage]; exact hfac)
    show R.arrows (f i)
    rw [this]
    exact R.downward_closed hg' _
  have hcov : E.sieve₀ ∈ topology B S hS U := by
    rw [topology_eq_restrictedTopology B S hS, Functor.mem_restrictedTopology_iff]
    refine S.smallEtaleTopology.superset_covering ?_
      (IsSmallEtaleStandardCovering.sieve₀_mem_smallEtaleTopology S _ hstd)
    rw [PreZeroHypercover.sieve₀, Sieve.generate_le_iff]
    rintro W g ⟨i⟩
    exact Sieve.image_mem_functorPushforward u _ (Sieve.ofArrows_mk _ _ i)
  exact ⟨⟨E, hcov⟩, hstd, hsieve⟩

/-! ### The vanishing -/

attribute [local instance] HasExt.standard

/-- For a quasi-coherent `𝒪_S`-module `𝓕` and an object `V` of the small étale site with affine
underlying scheme, `H^p(V, 𝓕ᵃ) = 0` for `p > 0`, for the cohomology `CategoryTheory.Sheaf.H'`
of the restriction to the small étale site `AlgebraicGeometry.SmallEtale B S hS` of the sheaf
`AlgebraicGeometry.fpqcOverAssociatedSheaf` on Mathlib's small étale site. -/
public theorem isZero_sheafH'_restrict_fpqcOverAssociatedSheaf (F : S.Modules)
    [F.IsQuasicoherent] (V : SmallEtale B S hS)
    (hV : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj V)) (p : ℕ) (hp : 0 < p) :
    IsZero (Sheaf.H'.{u + 1}
      (((toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{u} (topology B S hS)
        S.smallEtaleTopology).obj
        (((Scheme.Etale.forget S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Scheme.smallEtaleTopology S) (Scheme.fpqcTopology.{u}.over S)).obj
          (fpqcOverAssociatedSheaf S F))) p V) := by
  have := isContinuous_toEtaleSite B S hS
  refine sheafCohomology_isZero_of_cechCohomology_isZero_of_functor_of_enoughInjectives
    (topology B S hS) S.smallEtaleTopology (toEtaleSite B S hS) (affineObjectSet B S hS)
    (affineStandardCoverings B S hS) (affineStandardCoverings_hasProducts B S hS)
    (affineStandardCoverings_hasImageProducts B S hS)
    (affineStandardCoverings_covObjects B S hS) (affineStandardCoverings_cofinal B S hS)
    (affineStandardCoverings_comparison B S hS) _ ?_ V hV p hp
  intro W E hE q hq
  exact isZero_cechCohomology_succ_quasiCoherentPresheaf_smallEtale S F
    (E.1.map (toEtaleSite B S hS)) hE q hq

/-- The abelian sheaf underlying a quasi-coherent `𝒪`-module on the small étale site is
isomorphic to the restriction of `𝓕ᵃ`, for `𝓕` its restriction to the small Zariski site. -/
public def toSheafIsoRestrictFpqcOverAssociatedSheaf
    (H : SheafOfModules.{u} (structureSheaf B S hS)) (hH : H.IsQuasicoherentOnSite) :
    letI : ((restrictModule B S hS).obj H).IsQuasicoherent :=
      isQuasicoherent_restrictModule B S hS H hH
    (SheafOfModules.toSheaf (structureSheaf B S hS)).obj H ≅
      ((toEtaleSite B S hS).sheafPushforwardContinuous AddCommGrpCat.{u} (topology B S hS)
        S.smallEtaleTopology).obj
        (((Scheme.Etale.forget S).sheafPushforwardContinuous AddCommGrpCat.{u}
          (Scheme.smallEtaleTopology S) (Scheme.fpqcTopology.{u}.over S)).obj
          (fpqcOverAssociatedSheaf S ((restrictModule B S hS).obj H))) :=
  letI : ((restrictModule B S hS).obj H).IsQuasicoherent :=
    isQuasicoherent_restrictModule B S hS H hH
  have := isContinuous_toEtaleSite B S hS
  (SheafOfModules.toSheaf (structureSheaf B S hS)).mapIso
    ((@asIso _ _ _ _ _ (isIso_counit B S hS H hH
      (isQuasicoherent_restrictModule B S hS H hH))).symm ≪≫
      associatedModuleIsoSectionsSheaf B S hS ((restrictModule B S hS).obj H)) ≪≫
    Iso.refl _

/-- For a quasi-coherent `𝒪`-module `𝓗` on `S_étale`, an object `V` with affine
underlying scheme and `p > 0`, the `p`-th right derived functor of the module-valued sections
over `V` vanishes at `𝓗`:

```
H^p(V, 𝓗) = 0.
``` -/
@[sga "4 VII 4.4" "more general"]
public theorem isZero_rightDerived_evaluation_of_isAffine
    (H : SheafOfModules.{u} (structureSheaf B S hS)) (hH : H.IsQuasicoherentOnSite)
    (V : SmallEtale B S hS) (hV : AlgebraicGeometry.IsAffine ((toScheme B S hS).obj V)) (p : ℕ)
    (hp : 0 < p) :
    IsZero (((SheafOfModules.evaluation (structureSheaf B S hS) (op V)).rightDerived p).obj
      H) := by
  let : ((restrictModule B S hS).obj H).IsQuasicoherent :=
    isQuasicoherent_restrictModule B S hS H hH
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have h1 : IsZero (Sheaf.H'.{u + 1}
      ((SheafOfModules.toSheaf (structureSheaf B S hS)).obj H) (n + 1) V) :=
    (isZero_sheafH'_restrict_fpqcOverAssociatedSheaf B S hS
      ((restrictModule B S hS).obj H) V hV (n + 1) hp).of_iso
        (((Sheaf.cohomologyPresheafFunctor (topology B S hS) (n + 1)).mapIso
          (toSheafIsoRestrictFpqcOverAssociatedSheaf B S hS H hH)).app (op V))
  exact ModuleCat.isZero_iff_subsingleton.2
    (Stacks.Cohomology.ObjectSections.subsingleton_rightDerived_evaluation
      (topology B S hS) (structureSheaf B S hS) H V n h1)

end AlgebraicGeometry.SmallEtale

end
