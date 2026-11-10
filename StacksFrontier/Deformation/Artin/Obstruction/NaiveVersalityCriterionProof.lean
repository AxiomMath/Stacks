module

public import StacksFrontier.Deformation.Artin.Obstruction.DerivedFibreCoefficientChange
public import StacksFrontier.Deformation.Artin.Obstruction.DualNumbersPresentations
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityConverse
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityDualNumbersExtends
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityObjectBaseLift
public import StacksFrontier.Deformation.Artin.Versality.AffineChartApproximation
public import StacksFrontier.Deformation.Artin.Versality.ApproximationPredeformationData
public import StacksFrontier.Deformation.Artin.Versality.DualNumbersWeakExtends
public import StacksFrontier.AlgebraicGeometry.Topologies.FppfCompletedLocalRing
public import StacksFrontier.Deformation.Artin.RimSchlessinger

/-!
# Stacks 07YM, the direction `(2) ⇒ (1)`, and the whole tag

Let `Spec A` be affine of finite type over the ring `Λ` of an affine open `Spec Λ ⊆ S`, let `x`
be an object over `Spec A` of a category fibred in groupoids over the big fppf site of `S`
satisfying (RS\*), and let `ξ : E ⟶ NL_{A/Λ}` be a morphism of `D⁻(A)` satisfying hypotheses
(i) and (ii) of [Stacks, Tag 07YM]. The tag says that at a finite type point `u₀` of `Spec A`
the two cohomological conditions on the derived fibre of `ξ` imply versality of `x` at `u₀`,
and that at a *closed* point versality implies them.

The direction `(1) ⇒ (2)` is `Deformation.Artin.derivedFibreHomologyMap_conditions_of_isVersalAt`,
proved unconditionally. This file proves the direction `(2) ⇒ (1)` and states the two
directions together.

## Main results

* `Deformation.Artin.presentationResidueAlgEquiv` — **the residue field at `u₀` is the residue
  field of a complete local presentation there, `A`-linearly.** This is what carries the two
  cohomological conditions, stated at `κ(u₀)`, to the residue field of the base of the
  approximation formal object, where the criterion of [Stacks, Tag 06IU] is applied.
* `Deformation.Artin.isVersalAt_of_derivedFibreHomologyMap_conditions` — **the direction
  `(2) ⇒ (1)` of [Stacks, Tag 07YM]**.
* `Deformation.Artin.isVersalAt_iff_derivedFibreHomologyMap_conditions` — the two directions of
  the tag, in one statement.

## Implementation notes

The route is the one of the source. `Deformation.Artin.isVersalAt_of_forall_approximation`
reduces versality at `u₀` to versality, relative to `Λ`, of any formal object arising as the
approximation of a complete local object restricting `x` at `u₀`; the remaining site
containment it asks for is discharged by
`AlgebraicGeometry.BigFppfSite.contains_spec_completedLocalRing`, `A` being Noetherian. What
is then to be proved is `Deformation.Artin.FormalObject.IsVersal`, which by
`Deformation.Artin.FormalObject.isVersal_iff` is versality of the associated formal object of
the predeformation category of the closed fibre — the form
`Deformation.isVersal_iff_differential_surjective_and_base_lifts` ([Stacks, Tag 06IU]) is
stated in. Its two conditions are supplied by
`Deformation.Artin.surjective_mapIsomorphismClasses_associatedMorphism` and
`Deformation.Artin.levelLifts_of_surjective_derivedTensorFibre_neg_one` through
`Deformation.baseLifts_of_levelLifts`, and the levelwise data both of them consume is the
exported package of [Stacks, Tag 0CXK] in
`StacksFrontier/Deformation/Artin/Versality/ApproximationPredeformationData.lean`. The two
Schlessinger conditions come from axiom (RS\*) through
`Deformation.Artin.isDeformationCategory_predeformationCategory_of_satisfiesRSStar`.

The criterion of [Stacks, Tag 06IU] is read over the residue field `κ` of the base `R` of the
approximation, while the hypotheses `hsurj` and `hinj` are stated over the residue field of the
prime at `u₀`. The `A`-algebra structure on `κ` is *defined* as the residue map of `R` composed
with the ring map `A ⟶ R` read off the presentation `g`, and that choice is what makes the
comparison cheap: the residue point of the formal base is then literally the `A`-algebra point,
so `Deformation.Artin.approximationRestriction_residue` already gives the hypothesis `hr₀` of
the criterion, and the `A`-linearity of
`Deformation.Artin.presentationResidueEquiv` reduces to one application of
`CategoryTheory.Spec.map_injective`. The conditions are then carried along that isomorphism by
`Deformation.Artin.surjective_derivedTensorFibre_congr` and its injective counterpart, in the
chosen-derived-tensor-product presentation, at
`Deformation.Artin.canonicalDerivedTensorProduct`.

Hypothesis (i) carries one assumption beyond the lifting equivalence itself: that the structure
morphism of `Spec A'` is the one the chart gives, which a
`Deformation.Artin.SquareZeroThickening` does not record and `Spec A → Spec A'`, being a closed
immersion rather than an epimorphism, does not force. It sits in the antecedent, so it weakens
the hypothesis and strengthens the statements here, and it is what makes the two directions
consumable by `Deformation.Artin.NaiveObstructionAt`.

`RingHom.toAlgebra` replaces the scalar action by multiplication, so the `A`-algebra structure
on `κ` is introduced once with `letI` and the equation naming its structure map is passed
explicitly to everything that mentions it.

`Deformation.Artin.isVersal_of_surjective_derivedTensorFibre_neg_one` is not used: it is stated
for a category fibred in groupoids whose carrier lies in the same universe as the site, whereas
the tag is read here at arbitrary `Type v` and `Category.{w}`. Its three ingredients are
universe-polymorphic, so they are composed again here.

## References

* [Stacks Project, Tag 07YM](https://stacks.math.columbia.edu/tag/07YM)
* [Stacks Project, Tag 06IU](https://stacks.math.columbia.edu/tag/06IU)
* [Stacks Project, Tag 0CXK](https://stacks.math.columbia.edu/tag/0CXK)
* [Stacks Project, Tag 0CXJ](https://stacks.math.columbia.edu/tag/0CXJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace Deformation.Artin

universe u v w

attribute [local instance 10000] HasDerivedCategory.standard
section ResidueComparison

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (u₀ : Spec (CommRingCat.of A))
  {R : Type u} [CommRing R] [IsLocalRing R]
  (e : AlgebraicGeometry.Scheme.completedLocalRing (Spec (CommRingCat.of A)) u₀ ≃+* R)

/-- The residue field at `u₀` of an affine scheme, read as the residue field of the prime,
and the residue field of a complete local presentation of the completed local ring there are
isomorphic as rings. -/
public def presentationResidueEquiv : u₀.asIdeal.ResidueField ≃+* ResidueField R :=
  ((Scheme.Spec.residueFieldIso (CommRingCat.of A) u₀).commRingCatIsoToRingEquiv).symm.trans
    (completionResidueEquiv (Spec (CommRingCat.of A)) u₀ e)

variable (g : Spec (CommRingCat.of R) ⟶ Spec (CommRingCat.of A))
  (hg : g = Spec.map (CommRingCat.ofHom e.toRingHom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap
      ((Spec (CommRingCat.of A)).presheaf.stalk u₀)
      (AlgebraicGeometry.Scheme.completedLocalRing (Spec (CommRingCat.of A)) u₀))) ≫
    (Spec (CommRingCat.of A)).fromSpecStalk u₀)

include hg in
/-- The isomorphism of residue fields carries the residue point of `u₀` to the residue point
of the presentation. -/
public theorem specMap_presentationResidueEquiv :
    Spec.map (CommRingCat.ofHom (presentationResidueEquiv u₀ e).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A u₀.asIdeal.ResidueField)) =
      Spec.map (CommRingCat.ofHom (residue R)) ≫ g := by
  have hΨ : CommRingCat.ofHom (presentationResidueEquiv u₀ e).toRingHom =
      (Scheme.Spec.residueFieldIso (CommRingCat.of A) u₀).inv ≫
        CommRingCat.ofHom (completionResidueEquiv (Spec (CommRingCat.of A)) u₀ e).toRingHom :=
    rfl
  have h1 : Spec.map (CommRingCat.ofHom (presentationResidueEquiv u₀ e).toRingHom) =
      Spec.map (CommRingCat.ofHom
          (completionResidueEquiv (Spec (CommRingCat.of A)) u₀ e).toRingHom) ≫
        Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of A) u₀).inv := by
    rw [hΨ]
    exact Spec.map_comp _ _
  calc Spec.map (CommRingCat.ofHom (presentationResidueEquiv u₀ e).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap A u₀.asIdeal.ResidueField))
      = Spec.map (CommRingCat.ofHom
            (completionResidueEquiv (Spec (CommRingCat.of A)) u₀ e).toRingHom) ≫
          Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of A) u₀).inv ≫
          Spec.map (CommRingCat.ofHom (algebraMap A u₀.asIdeal.ResidueField)) := by
        rw [h1, Category.assoc]
    _ = Spec.map (CommRingCat.ofHom
            (completionResidueEquiv (Spec (CommRingCat.of A)) u₀ e).toRingHom) ≫
          (Spec (CommRingCat.of A)).fromSpecResidueField u₀ := by
        rw [Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField]
    _ = Spec.map (CommRingCat.ofHom (residue R)) ≫ g := by
        rw [hg]
        exact completionResidueEquiv_spec (Spec (CommRingCat.of A)) u₀ e

variable [Algebra A (ResidueField R)]
  (halg : algebraMap A (ResidueField R) = (residue R).comp (ringHom_of_schemeMap g))

include hg halg in
/-- **The residue field at `u₀` is the residue field of a complete local presentation there,
`A`-linearly.** The underlying ring equivalence is
`Deformation.Artin.presentationResidueEquiv`; that it commutes with the two structure maps
from `A` is forced by `Deformation.Artin.specMap_presentationResidueEquiv`, both sides being
the spectrum of a map of affine schemes. -/
public def presentationResidueAlgEquiv : u₀.asIdeal.ResidueField ≃ₐ[A] ResidueField R :=
  { presentationResidueEquiv u₀ e with
    commutes' := by
      have key : Spec.map (CommRingCat.ofHom
            ((presentationResidueEquiv u₀ e).toRingHom.comp
              (algebraMap A u₀.asIdeal.ResidueField))) =
          Spec.map (CommRingCat.ofHom ((residue R).comp (ringHom_of_schemeMap g))) := by
        rw [CommRingCat.ofHom_comp, CommRingCat.ofHom_comp, Spec.map_comp, Spec.map_comp,
          specMap_ringHom_of_schemeMap]
        exact specMap_presentationResidueEquiv u₀ e g hg
      have hring := congrArg CommRingCat.Hom.hom (Spec.map_injective key)
      intro r
      rw [halg]
      exact DFunLike.congr_fun hring r }

end ResidueComparison

section Forward

variable (Λ A : Type u) [CommRing Λ] [CommRing A] [Algebra Λ A]
  [IsNoetherianRing Λ] [Algebra.FiniteType Λ A]
variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (CommRingCat.of A) ⟶ S) (hA : B.Contains (Spec (CommRingCat.of A)))
  (baseMap : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion baseMap]
  (hbase : Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap = toS)
variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hΩ : B.Contains (Spec (squareZeroRing A (differentialsModule Λ A))))
variable (E : DerivedCategory (ModuleCat.{u} A))
  (hE : (DerivedCategory.TStructure.t (C := ModuleCat.{u} A)).minus E)
  (ξ : E ⟶ derivedNaiveCotangentComplex Λ A)
  (hLifts : ∀ (A' : Type u) [CommRing A'] [Algebra Λ A'] [Algebra A' A]
    [IsScalarTower Λ A' A] (D : SquareZeroThickening A B S hS toS hA A'),
    D.q = algebraMap A' A →
    Spec.map (CommRingCat.ofHom (algebraMap Λ A')) ≫ baseMap = B.inclusion.map D.toS' →
    (Nonempty ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ D.arrow))) ↔
      ξ ≫ naiveCotangentBaseMap Λ A' A = 0))
  (tangentEquiv : ∀ M : SiteModule A B,
    ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M : Type _) ≃+
      (E ⟶ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M.obj))
  (tangentEquiv_natural : ∀ {M N : SiteModule A B} (f : M ⟶ N)
    (z : (tangentFunctor A B S hS toS hA p x hx hp hRS).functor.obj M),
    tangentEquiv N ((tangentFunctor A B S hS toS hA p x hx hp hRS).functor.map f z) =
      tangentEquiv M z ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).map f.hom)
  (tangentEquiv_canonical : tangentEquiv (differentialsSiteModule Λ A B hΩ)
      (canonicalDeformationElement Λ A B S hS toS hA p x hx hp hRS hΩ baseMap
        hbase).element =
      ξ ≫ naiveCotangentToDifferentials Λ A)
variable (u₀ : Spec (CommRingCat.of A)) (hu₀ : AlgebraicGeometry.IsFiniteTypePoint u₀)

include hbase hp hRS hΩ hE hLifts tangentEquiv_natural tangentEquiv_canonical hu₀ in
/-- **Stacks 07YM, the direction `(2) ⇒ (1)`.** Let `x` be a family over `Spec A`, of finite
type over the ring `Λ` of an affine open `Spec Λ ⊆ S`, whose deformation theory is controlled
by `ξ : E ⟶ NL_{A/Λ}` as in hypotheses (i) and (ii) of the tag. If `ξ` induces a surjection on
`H^{-1}` and an injection on `H^0` of its derived fibre at a finite type point `u₀` of
`Spec A`, then `x` is versal at `u₀`.

Versality at `u₀` is reduced to versality of an approximation formal object over `Λ` by
`Deformation.Artin.isVersalAt_of_forall_approximation`, and that is the conclusion of the
criterion of [Stacks, Tag 06IU], whose two conditions are the degree `0` and degree `-1`
halves of the hypothesis. Only the first direction of hypothesis (i) is used. -/
public theorem isVersalAt_of_derivedFibreHomologyMap_conditions
    (hsurj : Function.Surjective (derivedFibreHomologyMap ξ u₀ (-1)))
    (hinj : Function.Injective (derivedFibreHomologyMap ξ u₀ 0)) :
    IsVersalAt (Over.mk toS) (p ⋙ Over.post B.inclusion) u₀ x
      (by change (Over.post B.inclusion).obj (p.obj x) = _; rw [hx]; rfl) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing Λ A
  subst hbase
  refine isVersalAt_of_forall_approximation Λ A B S hS _ baseMap rfl p hp x _ u₀ hu₀ ?_ ?_
  · exact BigFppfSite.contains_spec_completedLocalRing B hA u₀
  · intro xR ζ hζ e g hg hbase' hclosed r hr hrbase algR hΛ hAR
    -- The `A`-algebra structure on the residue field of the complete local base, read off the
    -- presentation `g`.
    let algAk : Algebra A (ResidueField ζ.base.R) :=
      ((residue ζ.base.R).comp (ringHom_of_schemeMap g)).toAlgebra
    have halgAk : algebraMap A (ResidueField ζ.base.R) =
        (residue ζ.base.R).comp (ringHom_of_schemeMap g) := RingHom.algebraMap_toAlgebra _
    have hresg : Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField ζ.base.R))) =
        Spec.map (CommRingCat.ofHom (residue ζ.base.R)) ≫ g := by
      rw [halgAk, CommRingCat.ofHom_comp, Spec.map_comp, specMap_ringHom_of_schemeMap]
    -- The `A`-linear comparison of the two residue fields.
    let φ : u₀.asIdeal.ResidueField ≃ₐ[A] ResidueField ζ.base.R :=
      presentationResidueAlgEquiv u₀ e g hg halgAk
    let T : DerivedTensorProduct A := canonicalDerivedTensorProduct A
    let εM : ModuleCat.of A u₀.asIdeal.ResidueField ≅
        ModuleCat.of A (ResidueField ζ.base.R) :=
      LinearEquiv.toModuleIso φ.toLinearEquiv
    have hsurjk : Function.Surjective
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) (-1)).map
          ((T.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (ResidueField ζ.base.R)))).map ξ)) :=
      (surjective_derivedTensorFibre_congr T ξ (-1) εM).mp
        ((surjective_derivedTensorFibre_iff_surjective_derivedExtensionScalars T ξ
          (-1)).mpr hsurj)
    have hinjk : Function.Injective
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
          ((T.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
            (ModuleCat.of A (ResidueField ζ.base.R)))).map ξ)) :=
      (injective_derivedTensorFibre_congr T ξ 0 εM).mp
        ((injective_derivedTensorFibre_iff_injective_derivedExtensionScalars T ξ 0).mpr hinj)
    -- The residue field is small enough for the site.
    have hmk : Cardinal.mk (ResidueField ζ.base.R) ≤
        max Cardinal.aleph0 (Cardinal.mk A) := by
      have h := Cardinal.mk_residueField_le_max (R := A) u₀.asIdeal
      rwa [Cardinal.mk_congr φ.toEquiv] at h
    have hAk : B.Contains (Spec (CommRingCat.of (ResidueField ζ.base.R))) :=
      contains_spec_of_mk_le B hA _ hmk
    have hkS : B.Contains (Spec (squareZeroRing A
        (ModuleCat.of A (ResidueField ζ.base.R)))) :=
      contains_spec_squareZeroRing_of_mk_le B hA A _ (le_max_right _ _) hmk
    have hkk : B.Contains (Spec (squareZeroRing (ResidueField ζ.base.R)
        (ModuleCat.of (ResidueField ζ.base.R) (ResidueField ζ.base.R)))) :=
      contains_spec_squareZeroRing_of_mk_le B hA _ _ hmk hmk
    -- The residue point of the complete local base is the residue point of `u₀`.
    have hiR : Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField ζ.base.R))) ≫ baseMap =
        Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField ζ.base.R))) ≫
          (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap) := by
      have hΛk : (algebraMap Λ (ResidueField ζ.base.R)) =
          (residue ζ.base.R).comp (algebraMap Λ ζ.base.R) := rfl
      rw [hΛk, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc, hΛ, hbase', hresg,
        Category.assoc]
    -- Condition (a) of Stacks 06IU, in degree `0`: the map on tangent spaces is surjective.
    have hcomp : Function.Surjective (fun f : derivedNaiveCotangentComplex Λ A ⟶
        (DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj
          (ModuleCat.of A (ResidueField ζ.base.R)) => ξ ≫ f) := by
      refine surjective_comp_of_iso ξ
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).mapIso
          ((uliftRestrictScalarsIso A (ResidueField ζ.base.R) ≪≫
            LinearEquiv.toModuleIso
              (ULift.moduleEquiv (R := A) (M := ResidueField ζ.base.R))).symm)) ?_
      exact (injective_derivedTensorFibre_zero_iff_surjective_comp T E hE ξ).mp hinjk
    have htan : Function.Surjective (canonicalTangentMap Λ A (ResidueField ζ.base.R) B S hS
        (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap) hA p x hx hp hRS hΩ hkS
        baseMap rfl) :=
      surjective_canonicalTangentMap_of_surjective_comp Λ A _ B S hS _ hA p x hx hp hRS hΩ hkS
        baseMap rfl E ξ tangentEquiv tangentEquiv_natural tangentEquiv_canonical hcomp
    -- Every deformation of the closed fibre over the dual numbers extends to `x`.
    let : p.IsFibered := hp.isFibered
    let q := Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap
    let O : Over S := Over.mk q
    have hxS : (p ⋙ Over.post B.inclusion).obj x = O := congrArg (Over.post B.inclusion).obj hx
    let ζ₀ := ζ.basePoint Λ baseMap hΛ
    let ζF := ζ.predeformationFormalObject Λ baseMap hΛ
    let P := approximationPredeformationCategory B S hS p ζ Λ baseMap hΛ
    let ζr := approximationLevelToOriginal B S hS p hp xR ζ hζ r 0
    let rest := approximationRestriction B S hS p hp x xR ζ hζ r Λ baseMap hΛ
    let bmap := approximationBaseMap B S hS p O ζ g Λ baseMap hΛ
    let κ₀ := squareZeroArtinianObj Λ (ResidueField ζ.base.R)
      (ModuleCat.of (ResidueField ζ.base.R) (ResidueField ζ.base.R))
    set fmap := algebraOverMapOfRingHom (algebraMap A (ResidueField ζ.base.R)) B S hS q
      (Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField ζ.base.R))) ≫ q) hA hAk rfl
      with hfmap
    have : IsLocallyNoetherian O.left :=
      inferInstanceAs (IsLocallyNoetherian (Spec (CommRingCat.of A)))
    have hRHS : schemeMap (p ⋙ Over.post B.inclusion) ζ₀ hxS ζr =
        Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField ζ.base.R))) := by
      rw [hresg]
      exact approximationRestriction_residue B S hS p hp O x hxS xR ζ hζ g r hrbase Λ baseMap hΛ
    -- The lifting statement at the closed fibre transports to level `0` of `ζ`.
    have key : ∀ (y : X) (hy : (p ⋙ Over.post B.inclusion).obj y =
          Over.mk (Spec.map (CommRingCat.ofHom (algebraMap Λ (ResidueField ζ.base.R))) ≫ baseMap))
          (ρ : y ⟶ x), p.IsHomLift fmap ρ →
        ExtendsAtArtinianBase (k := ResidueField ζ.base.R) baseMap
            (p ⋙ Over.post B.inclusion) hy O hxS ρ κ₀ →
          ExtendsAtArtinianBase (k := ResidueField ζ.base.R) baseMap
            (p ⋙ Over.post B.inclusion) ζ₀ O hxS ζr κ₀ := by
      intro y hy ρ hlift hext
      have := hlift
      have hLHS := schemeMap_eq_of_isHomLift B S hS p fmap ρ hy hxS rfl rfl
      refine (extendsAtArtinianBase_congr B S hS p _ _ hxS _ _ _ ?_ _).mp hext
      rw [hRHS]
      refine hLHS.trans ?_
      rfl
    let Z := ((Functor.chosenPullbacks p).pullbackFunctor fmap).obj ⟨x, hx⟩
    have hextZ := key Z.1
      ((congrArg (Over.post B.inclusion).obj Z.2).trans
        (algebraOver_post_eq A (ResidueField ζ.base.R) B S hS q hAk Λ baseMap hiR))
      ((Functor.chosenPullbacks p).map fmap ⟨x, hx⟩)
      ((Functor.chosenPullbacks p).isStronglyCartesian fmap ⟨x, hx⟩).toIsHomLift
      (extendsAtArtinianBase_of_exists_extends A (ResidueField ζ.base.R) B S hS q hAk p Λ
        baseMap hiR
        (⟨ModuleCat.of (ResidueField ζ.base.R) (ResidueField ζ.base.R), hkk⟩ :
          SiteModule (ResidueField ζ.base.R) B)
        Z.2 ((Functor.chosenPullbacks p).map fmap ⟨x, hx⟩) hA hx hp
        (exists_extends_of_surjective_canonicalTangentMap Λ A (ResidueField ζ.base.R) B S hS q hA
          hAk p x hx hp hRS hΩ hkS hkk baseMap rfl htan))
    -- Rim--Schlessinger for the predeformation category of the closed fibre.
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ A))) :=
      (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
        (RingHom.finiteType_algebraMap.mpr inferInstance)
    have : QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap Λ A)) ≫ baseMap) :=
      ⟨fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _⟩
    have : LocallyOfFiniteType ((Spec (CommRingCat.of A)).fromSpecResidueField u₀) := hu₀.1
    have : QuasiCompact ((Spec (CommRingCat.of A)).fromSpecResidueField u₀) := hu₀.2
    have : IsIso (CommRingCat.ofHom (presentationResidueEquiv u₀ e).toRingHom) :=
      ⟨CommRingCat.ofHom (presentationResidueEquiv u₀ e).symm.toRingHom,
        CommRingCat.hom_ext (RingHom.ext fun t =>
          (presentationResidueEquiv u₀ e).symm_apply_apply t),
        CommRingCat.hom_ext (RingHom.ext fun t =>
          (presentationResidueEquiv u₀ e).apply_symm_apply t)⟩
    have hcompose : Spec.map (CommRingCat.ofHom (algebraMap A (ResidueField ζ.base.R))) =
        Spec.map (CommRingCat.ofHom (presentationResidueEquiv u₀ e).toRingHom) ≫
          Spec.map (Scheme.Spec.residueFieldIso (CommRingCat.of A) u₀).hom ≫
          (Spec (CommRingCat.of A)).fromSpecResidueField u₀ := by
      rw [specMap_residueFieldIso_hom_comp_fromSpecResidueField u₀,
        specMap_presentationResidueEquiv u₀ e g hg, hresg]
    have : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom
        (algebraMap Λ (ResidueField ζ.base.R))) ≫ baseMap) := by
      rw [hiR, hcompose, Category.assoc, Category.assoc]
      infer_instance
    have : QuasiCompact (Spec.map (CommRingCat.ofHom
        (algebraMap Λ (ResidueField ζ.base.R))) ≫ baseMap) := by
      rw [hiR, hcompose, Category.assoc, Category.assoc]
      infer_instance
    have hdef := isDeformationCategory_predeformationCategory_of_satisfiesRSStar B S hS p hp hRS
      baseMap (ζ.level 0) (ζ.basePoint Λ baseMap hΛ) inferInstance inferInstance
    have hS1 := Deformation.schlessingerConditionS1_of_satisfiesRS hdef.satisfiesRS
    have hS2 := Deformation.schlessingerConditionS2_of_satisfiesRS hdef.satisfiesRS
    have hpre := predeformationCategory_isPredeformationCategory B hS baseMap p (ζ.level 0) ζ₀ hp
    have hpts := approximationPoints B S hS p hp O x hxS u₀ xR ζ hζ e g hg hbase' r hrbase Λ
      baseMap hΛ
    have hrb := approximationRestriction_base B S hS p hp O x hxS xR ζ hζ g r hrbase Λ baseMap hΛ
    have hrc := approximationRestriction_closedPoint B S hS p hp x xR ζ hζ r Λ baseMap hΛ
    -- Condition (a) of Stacks 06IU at the dual numbers.
    have hcondA := surjective_mapIsomorphismClasses_associatedMorphism B S hS p hp ζ₀ P
      hpre.cofibered O hxS ζr ζF
      (Deformation.associatedMorphism hpre.cofibered ζF
        (Deformation.chosenPushforwardsOfCofibered P.projection hpre.cofibered))
      rest (approximationRestriction_transition B S hS p hp x xR ζ hζ r Λ baseMap hΛ) bmap hrb
      hrc hpts κ₀ hextZ
    have htangent :=
      surjective_mapIsomorphismClasses_artinianDualNumbers_of_squareZeroArtinianObj _ _ _ hcondA
    -- Condition (b) of Stacks 06IU: the base lifts across every small extension.
    have hbaseLifts := Deformation.baseLifts_of_levelLifts (BasedCategory.ofFunctor P.projection)
      hpre ζF
      (levelLifts_of_surjective_derivedTensorFibre_neg_one B S hS p hp hRS baseMap hA hmk T E hE
        ξ hsurjk hx (fun A' _ _ _ _ D hD hch => (hLifts A' D hD hch).mp) ζ₀ P ζF rest bmap hrb
        ζr hrc hRHS hpts
        (approximationPoints_injective B S hS p O u₀ ζ e g hg Λ baseMap hΛ))
    exact (FormalObject.isVersal_iff B S hS p hp ζ Λ baseMap hΛ).mpr
      ((Deformation.isVersal_iff_differential_surjective_and_base_lifts
        (BasedCategory.ofFunctor P.projection) hpre hS1 hS2 ζF
        (Deformation.chosenPushforwardsOfCofibered P.projection hpre.cofibered)).mpr
        ⟨htangent, hbaseLifts⟩)

include hbase hp hRS hΩ hE hLifts tangentEquiv_natural tangentEquiv_canonical hu₀ in
/-- **Stacks 07YM.** Let `S` be a scheme, `𝒳` a category fibred in groupoids over the big fppf
site of `S` satisfying (RS\*), `x` an object of `𝒳` over an affine `Spec A` of finite type over
the ring `Λ` of an affine open `Spec Λ ⊆ S`, and `ξ : E ⟶ NL_{A/Λ}` a morphism of `D⁻(A)`
satisfying hypotheses (i) and (ii) of the tag. Let `u₀` be a finite type point of `Spec A`.

Then, first, if `ξ` is surjective on `H^{-1}` and injective on `H^0` of its derived fibre at
`u₀`, the family `x` is versal at `u₀`; and second, if `u₀` is a closed point at which `x` is
versal, `ξ` has those two properties at `u₀`.

The first conjunct is `Deformation.Artin.isVersalAt_of_derivedFibreHomologyMap_conditions` and
the second is `Deformation.Artin.derivedFibreHomologyMap_conditions_of_isVersalAt`; the two
halves of hypothesis (i) are what each of them uses, and closedness of `u₀` enters only in the
second, exactly as in the source. -/
public theorem isVersalAt_iff_derivedFibreHomologyMap_conditions :
    ((Function.Surjective (derivedFibreHomologyMap ξ u₀ (-1)) ∧
        Function.Injective (derivedFibreHomologyMap ξ u₀ 0)) →
      IsVersalAt (Over.mk toS) (p ⋙ Over.post B.inclusion) u₀ x
        (by change (Over.post B.inclusion).obj (p.obj x) = _; rw [hx]; rfl)) ∧
    (IsClosed ({u₀} : Set (Spec (CommRingCat.of A))) →
      IsVersalAt (Over.mk toS) (p ⋙ Over.post B.inclusion) u₀ x
          (by change (Over.post B.inclusion).obj (p.obj x) = _; rw [hx]; rfl) →
      Function.Surjective (derivedFibreHomologyMap ξ u₀ (-1)) ∧
        Function.Injective (derivedFibreHomologyMap ξ u₀ 0)) := by
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing Λ A
  refine ⟨fun h => isVersalAt_of_derivedFibreHomologyMap_conditions Λ A B S hS toS hA baseMap
      hbase p x hx hp hRS hΩ E hE ξ hLifts tangentEquiv tangentEquiv_natural
      tangentEquiv_canonical u₀ hu₀ h.1 h.2,
    fun hclosed hversal => derivedFibreHomologyMap_conditions_of_isVersalAt Λ A B S hS toS hA
      baseMap hbase p x hx hp hRS hΩ E hE ξ tangentEquiv tangentEquiv_natural
      tangentEquiv_canonical u₀ hclosed
      (fun A' _ _ _ _ D hD hch => (hLifts A' D hD hch).mpr) hversal⟩

end Forward

end Deformation.Artin

end
