module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedBelowCompact
public import StacksFrontier.AlgebraicGeometry.Perfect.ChartTorDimensionSectionsCrossing
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibrewiseChartCriterion
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentStandardModel
public import StacksFrontier.AlgebraicGeometry.Modules.TildeExactness
public import StacksFrontier.Homology.RelativelyPerfect.BaseChange

/-!
# The two conditions of the fibrewise criterion on an affine chart

Let `f : X ⟶ S` be flat, let `E` be an object of `D(𝒪_X)` with quasi-coherent cohomology, and
let `U ⊆ f⁻¹(V)` be an affine chart, `V ⊆ S` affine. Condition (2) of Stacks 0GEH is stated on
sheaves: `E` is locally bounded below, and so is its derived restriction `L(X_s ⟶ X)^*E` to every
fibre. The ring-level criterion Stacks 0GHJ, which the proof of Stacks 0GEH applies on the charts,
asks instead that `RΓ(U, E)` be bounded below and that its derived fibres
`RΓ(U, E) ⊗ᴸ_{Γ(S, V)} κ(𝔭)` be bounded below. This file proves that the sheaf conditions give
the chart conditions.

## Main results

* `AlgebraicGeometry.exists_isOpenImmersion_toFibre`: for a pushout `B'` of
  `Γ(X, U) ← Γ(S, V) → κ(𝔭)`, `Spec B'` is an open subscheme of the fibre of `f` over `𝔭`,
  namely the base change of `Spec Γ(X, U) ⟶ X`.
* `AlgebraicGeometry.exists_isGE_derivedSections_of_isLocallyBoundedBelow`: the first chart
  condition.
* `AlgebraicGeometry.exists_isGE_derivedFibre_derivedSections`: the second chart condition, for a
  flat `f`.

## Implementation notes

The fibre computation is the affine case of Stacks 08IB, assembled from: the composition formula
for derived pullbacks (Stacks 0D5S), the identification of `E|_U` with the derived sheafification
of `RΓ(U, E)` (Stacks 06Z0, `nonempty_derivedPullback_isoSpec_iso_tilde_derivedSections`), the
affine comparison of Stacks 08DW (2) at the standard model, and the base-change comparison of
Stacks 065Z, invertible because `Γ(X, U)` is flat over `Γ(S, V)` (Stacks 0661). Only lower bounds
are transported, so no comparison isomorphism has to be pinned.

## References

* [Stacks Project, Lemma 36.35.13 (Tag 0GEH)](https://stacks.math.columbia.edu/tag/0GEH)
* [Stacks Project, Lemma 36.22.5 (Tag 08IB)](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Lemma 15.85.10 (Tag 0GHJ)](https://stacks.math.columbia.edu/tag/0GHJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open scoped AlgebraicGeometry TensorProduct

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-- A module vanishing on an open `O` has a restriction along an open immersion `θ` vanishing on
`θ⁻¹(O)`. -/
theorem isZero_restrictModules_preimage_restrictFunctor {W Y : Scheme.{u}} (θ : W ⟶ Y)
    [IsOpenImmersion θ] (O : Y.Opens) (M : Y.Modules)
    (hM : IsZero ((RingedSpace.restrictModules Y.toRingedSpace O).obj M)) :
    IsZero ((RingedSpace.restrictModules W.toRingedSpace (θ ⁻¹ᵁ O)).obj
      ((Scheme.Modules.restrictFunctor θ).obj M)) := by
  have hH : IsZero ((Scheme.Modules.restrictFunctor O.ι).obj M) :=
    hM.of_iso ((RingedSpace.restrictModulesIsoRestrictFunctor Y O).app M).symm
  have h1 : IsZero ((Scheme.Modules.restrictFunctor (θ ∣_ O)).obj
      ((Scheme.Modules.restrictFunctor O.ι).obj M)) :=
    (Scheme.Modules.restrictFunctor (θ ∣_ O)).map_isZero hH
  have h2 : IsZero ((Scheme.Modules.restrictFunctor (θ ⁻¹ᵁ O).ι).obj
      ((Scheme.Modules.restrictFunctor θ).obj M)) :=
    h1.of_iso (((Scheme.Modules.restrictFunctorComp (θ ⁻¹ᵁ O).ι θ).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr (morphismRestrict_ι θ O)).symm.app M ≪≫
      (Scheme.Modules.restrictFunctorComp (θ ∣_ O) O.ι).app M)
  exact h2.of_iso ((RingedSpace.restrictModulesIsoRestrictFunctor W (θ ⁻¹ᵁ O)).app _)

/-- Local boundedness below restricts along an open immersion. -/
theorem isLocallyBoundedBelow_restrict_of_isOpenImmersion {W Y : Scheme.{u}} (θ : W ⟶ Y)
    [IsOpenImmersion θ] (L : DerivedCategory Y.Modules)
    (hL : RingedSpace.IsLocallyBoundedBelow Y.toRingedSpace L) :
    RingedSpace.IsLocallyBoundedBelow W.toRingedSpace
      ((Scheme.Modules.restrictFunctor θ).mapDerivedCategory.obj L) := by
  intro w
  obtain ⟨O, hO, N, hN⟩ := hL (θ w)
  refine ⟨θ ⁻¹ᵁ O, hO, N, fun j hj => ?_⟩
  exact (isZero_restrictModules_preimage_restrictFunctor θ O _ (hN j hj)).of_iso
    ((RingedSpace.restrictModules W.toRingedSpace (θ ⁻¹ᵁ O)).mapIso
      (((Scheme.Modules.restrictFunctor θ).mapDerivedCategoryHomologyIso j).app L))

/-- **The chart of a fibre.** Let `U ⊆ X` and `V ⊆ S` be affine opens with `U ⊆ f⁻¹(V)`, let `p`
be a prime of `Γ(S, V)` and let `P` be a pushout of `Γ(X, U) ← Γ(S, V) → κ(p)`. Then `Spec P`
maps by an open immersion into the fibre of `f` over the point of `V` corresponding to `p`,
compatibly with `Spec P ⟶ Spec Γ(X, U) ≅ U ⊆ X`: it is the base change of `Spec Γ(X, U) ⟶ X`
along the projection from the fibre. -/
theorem exists_isOpenImmersion_toFibre {X S : Scheme.{u}} (f : X ⟶ S) {U : X.Opens}
    {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    (p : PrimeSpectrum Γ(S, V)) {P : CommRingCat.{u}} (inl : Γ(X, U) ⟶ P)
    (inr : CommRingCat.of p.asIdeal.ResidueField ⟶ P)
    (hP : IsPushout (f.appLE V U e)
      (CommRingCat.ofHom (algebraMap Γ(S, V) p.asIdeal.ResidueField)) inl inr) :
    ∃ θ : Spec P ⟶ pullback f (S.fromSpecResidueField (hV.fromSpec p)),
      IsOpenImmersion θ ∧ θ ≫ pullback.fst _ _ = Spec.map inl ≫ hU.fromSpec := by
  set j := S.fromSpecResidueField (hV.fromSpec p)
  have sq1 := isPullback_SpecMap_of_isPushout _ _ _ _ hP
  let c : S.residueField (hV.fromSpec p) ⟶ CommRingCat.of p.asIdeal.ResidueField :=
    hV.fromSpec.residueFieldMap p ≫ (Scheme.Spec.residueFieldIso Γ(S, V) p).hom
  have hc : Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) p.asIdeal.ResidueField)) ≫
      hV.fromSpec = Spec.map c ≫ j := by
    have h1 := Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField Γ(S, V) p
    have h2 := Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField hV.fromSpec p
    simp only [c, j, Spec.map_comp, Category.assoc, h2]
    rw [← h1, ← Category.assoc, ← Spec.map_comp, ← Spec.map_comp, Category.assoc,
      Iso.inv_hom_id, Category.comp_id]
  have hiso : ∀ x : Spec Γ(S, V), IsIso (hV.fromSpec.residueFieldMap x) := fun x => inferInstance
  have : IsIso (hV.fromSpec.residueFieldMap p) := hiso p
  have : IsIso c := IsIso.comp_isIso
  have sq2 : IsPullback (Spec.map (CommRingCat.ofHom (algebraMap Γ(S, V) p.asIdeal.ResidueField)))
      (Spec.map c) hV.fromSpec j := IsPullback.of_vert_isIso_mono ⟨hc⟩
  have outer := sq1.paste_vert sq2
  rw [IsAffineOpen.SpecMap_appLE_fromSpec f hV hU e] at outer
  let θ : Spec P ⟶ pullback f j := pullback.lift (Spec.map inl ≫ hU.fromSpec)
    (Spec.map inr ≫ Spec.map c) (by rw [Category.assoc]; exact outer.w)
  have hθ₁ : θ ≫ pullback.fst f j = Spec.map inl ≫ hU.fromSpec := pullback.lift_fst _ _ _
  have hθ₂ : θ ≫ pullback.snd f j = Spec.map inr ≫ Spec.map c := pullback.lift_snd _ _ _
  rw [← hθ₂] at outer
  have L := (IsPullback.paste_vert_iff (IsPullback.of_hasPullback f j) hθ₁.symm).1 outer
  exact ⟨θ, MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsOpenImmersion) L
    inferInstance, hθ₁⟩

/-! ### Boundedness below across exact functors and the affine dictionary -/

/-- An exact functor carries an object bounded below by `n` to one bounded below by `n`. -/
theorem isGE_mapDerivedCategory_obj {A B : Type*} [Category A] [Category B] [Abelian A]
    [Abelian B] [HasDerivedCategory A] [HasDerivedCategory B] (G : A ⥤ B) [G.Additive]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (N : DerivedCategory A) (n : ℤ)
    (hN : N.IsGE n) : (G.mapDerivedCategory.obj N).IsGE n := by
  rw [DerivedCategory.isGE_iff] at hN ⊢
  exact fun i hi => (isZero_homology_mapDerivedCategory_iff G N i).2 (G.map_isZero (hN i hi))

/-- An object of `D(R)` is bounded below by `n` as soon as its derived sheafification is. -/
theorem isGE_of_isGE_tilde {R : CommRingCat.{u}} (M : DerivedCategory (ModuleCat.{u} R)) (n : ℤ)
    (h : ((tilde.functor R).mapDerivedCategory.obj M).IsGE n) : M.IsGE n := by
  rw [DerivedCategory.isGE_iff] at h ⊢
  intro i hi
  rw [IsZero.iff_id_eq_zero]
  refine (tilde.functor R).map_injective ?_
  rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_zero]
  exact ((isZero_homology_mapDerivedCategory_iff (tilde.functor R) M i).1 (h i hi)).eq_of_src
    _ _

/-- On a quasi-compact source, the derived pullback along an open immersion of a locally bounded
below object is bounded below. -/
theorem exists_isGE_derivedPullback_of_isOpenImmersion {W Y : Scheme.{u}} (θ : W ⟶ Y)
    [IsOpenImmersion θ] [CompactSpace W] (L : DerivedCategory Y.Modules)
    (hL : RingedSpace.IsLocallyBoundedBelow Y.toRingedSpace L) :
    ∃ n : ℤ, ((derivedPullback θ.toLRSHom.toShHom).obj L).IsGE n := by
  obtain ⟨n, hn⟩ := RingedSpace.exists_isGE_of_isLocallyBoundedBelow W.toRingedSpace _
    (isLocallyBoundedBelow_restrict_of_isOpenImmersion θ L hL)
  have : DerivedCategory.TStructure.t.IsGE
      ((Scheme.Modules.restrictFunctor θ).mapDerivedCategory.obj L) n := hn
  exact ⟨n, DerivedCategory.TStructure.t.isGE_of_iso
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback θ).app L) n⟩

/-- Derived pullback along two composable morphisms is derived pullback along any morphism equal
to their composite. -/
theorem nonempty_derivedPullback_comp_iso {W Y Z : Scheme.{u}} (a : W ⟶ Y) (b : Y ⟶ Z)
    (c : W ⟶ Z) (h : a ≫ b = c) (E : DerivedCategory Z.Modules) :
    Nonempty ((derivedPullback a.toLRSHom.toShHom).obj
        ((derivedPullback b.toLRSHom.toShHom).obj E) ≅
      (derivedPullback c.toLRSHom.toShHom).obj E) := by
  have hs : a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom = c.toLRSHom.toShHom := by
    subst h
    rfl
  exact ⟨(Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      a.toLRSHom.toShHom b.toLRSHom.toShHom).app E ≪≫
    eqToIso (congrArg (fun k : W.toRingedSpace ⟶ Z.toRingedSpace =>
      (derivedPullback k).obj E) hs)⟩

/-- **The first condition on a chart.** If `E` has quasi-coherent cohomology and is locally
bounded below, then on every affine open `U` the complex `RΓ(U, E)` is bounded below. -/
theorem exists_isGE_derivedSections_of_isLocallyBoundedBelow {X : Scheme.{u}}
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (hb : RingedSpace.IsLocallyBoundedBelow X.toRingedSpace E) {U : X.Opens}
    (hU : IsAffineOpen U) :
    ∃ a : ℤ, ((derivedSectionsUnbounded X U).obj E).IsGE a := by
  obtain ⟨eL⟩ := Scheme.Hom.nonempty_derivedPullback_isoSpec_iso_tilde_derivedSections E hE hU
  obtain ⟨n, hn⟩ := exists_isGE_derivedPullback_of_isOpenImmersion hU.isoSpec.inv _
    (isLocallyBoundedBelow_restrict_of_isOpenImmersion U.ι E hb)
  exact ⟨n, isGE_of_isGE_tilde _ n (DerivedCategory.TStructure.t.isGE_of_iso eL n)⟩

section BaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open CochainComplex.DerivedExtensionScalars RingTheory.TorIndependence in
/-- **Flat base change of a lower bound.** Let `A` be a flat `R`-algebra and `R'` an
`R`-algebra. If `(A ⊗_R R') ⊗ᴸ_A K` is bounded below by `n` for an object `K` of `D(A)`, then so is
`R' ⊗ᴸ_R K`, the object `K` being read over `R`: the two agree after restriction of scalars to
`R'`, by the base-change comparison of Stacks 065Z, invertible since `A` is Tor independent from
`R'` over `R` (Stacks 0661). -/
theorem isGE_derivedExtensionScalars_of_isGE_tensorProduct {R A R' : Type u} [CommRing R]
    [CommRing A] [CommRing R'] [Algebra R A] [Algebra R R'] [Module.Flat R A]
    (K : DerivedCategory (ModuleCat.{u} A)) (n : ℤ)
    (h : ((totalDerivedExtensionScalars.{u, u, u}
      (algebraMap A (A ⊗[R] R'))).functor.obj K).IsGE n) :
    ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.obj
      ((ModuleCat.restrictScalars (algebraMap R A)).mapDerivedCategory.obj K)).IsGE n := by
  let Dbase := totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')
  let Dtop := totalDerivedExtensionScalars.{u, u, u} (algebraMap A (A ⊗[R] R'))
  have sq : (algebraMap A (A ⊗[R] R')).comp (algebraMap R A) =
      (algebraMap R' (A ⊗[R] R')).comp (algebraMap R R') :=
    (IsScalarTower.algebraMap_eq R A (A ⊗[R] R')).symm.trans
      (IsScalarTower.algebraMap_eq R R' (A ⊗[R] R'))
  let cmp :=
    @derivedBaseChangeComparison.{u, u, u, u, u, u + 1, u + 1, u + 1, u + 1}
    R A R' (A ⊗[R] R') _ _ _ _ _ _ _ _
    (algebraMap R A) (algebraMap R R') (algebraMap A (A ⊗[R] R')) (algebraMap R' (A ⊗[R] R'))
    sq Dbase.functor Dtop.functor Dbase.comparison Dtop.comparison
    Dbase.isLeftDerived Dtop.isLeftDerived
  have hcmp : IsIso cmp.2.1 :=
    @derivedBaseChangeComparison_isIso_of_torIndependent.{u, u, u, u,
      u, u + 1, u + 1, u + 1, u + 1}
    R A R' (A ⊗[R] R') _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    PseudoCoherence.torIndependent_of_flat Dbase.functor Dtop.functor Dbase.comparison
    Dtop.comparison Dbase.isLeftDerived Dtop.isLeftDerived
  have h2 := isGE_mapDerivedCategory_obj (ModuleCat.restrictScalars.{u}
    (algebraMap R' (A ⊗[R] R'))) _ n h
  have : DerivedCategory.TStructure.t.IsGE
      ((Dtop.functor ⋙
        (ModuleCat.restrictScalars (algebraMap R' (A ⊗[R] R'))).mapDerivedCategory).obj K) n :=
    h2
  exact DerivedCategory.TStructure.t.isGE_of_iso (asIso (cmp.2.1.app K)).symm n

end BaseChange

section Fibre

attribute [local instance] Algebra.TensorProduct.rightAlgebra

open CochainComplex.DerivedExtensionScalars

/-- **The second condition on a chart.** Let `f : X ⟶ S` be flat, let `E` have quasi-coherent
cohomology, and suppose the derived restriction of `E` to every fibre of `f` is locally bounded
below. Then on an affine chart `U ⊆ f⁻¹(V)` the derived fibre
`RΓ(U, E) ⊗ᴸ_{Γ(S, V)} κ(𝔭)` is bounded below for every prime `𝔭` of `Γ(S, V)`.

With `B = Γ(X, U)` and `B' = B ⊗_{Γ(S, V)} κ(𝔭)`, the scheme `Spec B'` is an open subscheme of
the fibre over `𝔭` (`exists_isOpenImmersion_toFibre`), so the derived restriction of the fibre
object to it is bounded below; by the composition formula for derived pullbacks and the
identification of `E|_U` with the derived sheafification of `RΓ(U, E)`, that object is the
derived sheafification of `B' ⊗ᴸ_B RΓ(U, E)` (Stacks 08DW (2)), which is therefore bounded
below; and flat base change (`isGE_derivedExtensionScalars_of_isGE_tensorProduct`) passes the
bound to `κ(𝔭) ⊗ᴸ_{Γ(S, V)} RΓ(U, E)`. -/
theorem exists_isGE_derivedFibre_derivedSections {X S : Scheme.{u}} (f : X ⟶ S) [Flat f]
    (E : DerivedCategory X.Modules)
    (hE : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent)
    (hfib : ∀ s : S, RingedSpace.IsLocallyBoundedBelow
      (Limits.pullback f (S.fromSpecResidueField s)).toRingedSpace
      ((derivedPullback (Limits.pullback.fst f (S.fromSpecResidueField s)).toLRSHom.toShHom).obj
        E))
    {U : X.Opens} {V : S.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : U ≤ f ⁻¹ᵁ V)
    (p : PrimeSpectrum Γ(S, V)) :
    letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
    ∃ a : ℤ, ((totalDerivedExtensionScalars.{u, u, u}
        (algebraMap Γ(S, V) p.asIdeal.ResidueField)).functor.obj
      ((ModuleCat.restrictScalars (algebraMap Γ(S, V) Γ(X, U))).mapDerivedCategory.obj
        ((derivedSectionsUnbounded X U).obj E))).IsGE a := by
  let : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U e).hom.toAlgebra
  have : Module.Flat Γ(S, V) Γ(X, U) := Scheme.Hom.moduleFlat_appLE f hV hU e rfl
  let κ := p.asIdeal.ResidueField
  let B' := Γ(X, U) ⊗[Γ(S, V)] κ
  let q : Spec (CommRingCat.of B') ⟶ Spec Γ(X, U) :=
    Spec.map (CommRingCat.ofHom (algebraMap Γ(X, U) B'))
  obtain ⟨θ, hθ, hθi⟩ := exists_isOpenImmersion_toFibre f hU hV e p
    (CommRingCat.ofHom (algebraMap Γ(X, U) B')) (CommRingCat.ofHom (algebraMap κ B'))
    (CommRingCat.isPushout_tensorProduct Γ(S, V) Γ(X, U) κ)
  have := hθ
  let i := Limits.pullback.fst f (S.fromSpecResidueField (hV.fromSpec p))
  let M := (derivedSectionsUnbounded X U).obj E
  let rE := (Scheme.Modules.restrictFunctor U.ι).mapDerivedCategory.obj E
  obtain ⟨n, hn⟩ := @exists_isGE_derivedPullback_of_isOpenImmersion _ _ θ hθ _ _
    (hfib (hV.fromSpec p))
  obtain ⟨e1⟩ := nonempty_derivedPullback_comp_iso θ i _ rfl E
  obtain ⟨e2⟩ := nonempty_derivedPullback_comp_iso (q ≫ hU.isoSpec.inv) U.ι (θ ≫ i)
    (by rw [hθi, Category.assoc, IsAffineOpen.isoSpec_inv_ι]) E
  obtain ⟨e3⟩ := nonempty_derivedPullback_comp_iso q hU.isoSpec.inv _ rfl
    ((derivedPullback U.ι.toLRSHom.toShHom).obj E)
  obtain ⟨e5⟩ := Scheme.Hom.nonempty_derivedPullback_isoSpec_iso_tilde_derivedSections E hE hU
  let e4 : (derivedPullback U.ι.toLRSHom.toShHom).obj E ≅ rE :=
    ((Scheme.Modules.derivedRestrictIsoDerivedPullback U.ι).app E).symm
  let e6 := (StandardModel.affinePullbackComparison Γ(X, U) (CommRingCat.of B')
    (CommRingCat.ofHom (algebraMap Γ(X, U) B'))).app M
  have iso : (derivedPullback θ.toLRSHom.toShHom).obj
      ((derivedPullback i.toLRSHom.toShHom).obj E) ≅
      (tilde.functor (CommRingCat.of B')).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap Γ(X, U) B')).functor.obj M) :=
    e1 ≪≫ e2.symm ≪≫ e3.symm ≪≫
      (derivedPullback q.toLRSHom.toShHom).mapIso
        ((derivedPullback hU.isoSpec.inv.toLRSHom.toShHom).mapIso e4 ≪≫ e5) ≪≫ e6
  have := hn
  have h1 := isGE_of_isGE_tilde _ n (DerivedCategory.TStructure.t.isGE_of_iso iso n)
  exact ⟨n, isGE_derivedExtensionScalars_of_isGE_tensorProduct M n h1⟩

end Fibre

end AlgebraicGeometry
