module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedParasitic
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedZariskiQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.DerivedPushforwardAdequate
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackOfToposHomTriangulatedUniverses

/-!
# `D_Adeq(𝒪)/D_𝒞(𝒪) ≌ D_QCoh(S)`

Let `S` be a scheme, `(Sch/S)_τ` a chosen big site over `S` for `τ` one of the Zariski, étale,
smooth, syntomic and fppf topologies, and `f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` the morphism of
ringed topoi of [Stacks, Tag 070U]. Let `𝒞` be the category of parasitic adequate modules and
`D_𝒞(𝒪) ⊂ D_Adeq(𝒪)` the complexes whose cohomology modules lie in `𝒞`. [Stacks, Tag 070X]
asserts that the derived direct image induces an equivalence

  `D_Adeq(𝒪)/D_𝒞(𝒪) ⟶ D_QCoh(S)`.

The source's argument, followed here, deduces it from [Stacks, Tag 070W]:

* `D_𝒞(𝒪)` is the kernel of `Rf_* : D_Adeq(𝒪) ⥤ D_QCoh(S)`: for `K` in `D_Adeq(𝒪)` one has
  `Hⁿ(Rf_*K) ≅ f_*Hⁿ(K)`, and an adequate module `𝓕` has `f_*𝓕 = 𝓕|_{S_Zar} = 0` exactly when it
  is parasitic ([Stacks, Tag 06ZM]);
* the counit `Lf^*Rf_*X ⟶ X` is carried by `Rf_*` to an isomorphism, so becomes invertible in
  the quotient;
* `Rf_*` is bijective on `Hom`-sets of the quotient, `Lf^*` giving an inverse, because the unit
  `id ⟶ Rf_*Lf^*` is invertible on `D_QCoh(S)`, i.e. `Lf^*` is fully faithful.

The quotient is the Verdier quotient, the localization at the morphisms whose cone lies in
`D_𝒞(𝒪)`; for this to be the class of morphisms that `Rf_*` inverts, `Rf_*` must be a
triangulated functor, which it is as the right adjoint of the triangulated functor `Lf^*`
([Stacks, Tag 06YY]).

## Main results

* `Stacks.Adequate.BigSite.isTriangulated_derivedAdequate_ringedSite` and
  `Stacks.Adequate.isTriangulated_derivedQuasicoherent_zariskiRingedSite` — `D_Adeq(𝒪)` and
  `D_QCoh(S)`, on the modules of the two ringed sites of `f`, are triangulated subcategories, so
  they are pretriangulated and triangulated categories.
* `Stacks.Adequate.BigSite.isIso_derivedQuasicoherentAdequateAdjunction_unit_app` and
  `Stacks.Adequate.BigSite.fullyFaithfulDerivedQuasicoherentPullback` — `Lf^*` is fully faithful
  on `D_QCoh(S)`.
* `Stacks.Adequate.BigSite.isTriangulated_derivedAdequateDirectImage` — the restricted `Rf_*`
  is triangulated, for the shift datum `derivedAdequateDirectImageCommShift` transported across
  the adjunction.
* `Stacks.Adequate.BigSite.kernel_derivedAdequateDirectImage` — `D_𝒞(𝒪)` is the kernel of `Rf_*`.
* `Stacks.Adequate.BigSite.isLocalization_trW_derivedParasitic_derivedAdequateDirectImage` and
  `Stacks.Adequate.BigSite.derivedAdequateParasiticQuotientEquivalence` — [Stacks, Tag 070X].

## Implementation notes

The derived categories are the standard models, in which the derived functors of
[Stacks, Tag 07A6] for the morphism of [Stacks, Tag 070U] are formed
(`Stacks.Adequate.BigSite.derivedZariskiAdjunction`); the declarations which mention those
functors seat the standard model locally.

The source first reduces to the Zariski topology by [Stacks, Tag 070V]. That reduction is not
needed: the inputs from [Stacks, Tag 070W] are proved for each of the five topologies directly.

## References

* [Stacks Project, Tag 070X](https://stacks.math.columbia.edu/tag/070X)
* [Stacks Project, Tag 070W](https://stacks.math.columbia.edu/tag/070W)
* [Stacks Project, Tag 06ZM](https://stacks.math.columbia.edu/tag/06ZM)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Adequate

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.DerivedTensor.ResolutionByExtensionsByZero.instAbelian

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-! ### The two subcategories on the ringed sites of `f` -/

attribute [local instance 2000] HasDerivedCategory.standard in
/-- `D_Adeq(𝒪)` is a triangulated subcategory of `D(𝒪)`, read on the modules over the ringed
site of a chosen big site, the source of the morphism of [Stacks, Tag 070U]. -/
public instance BigSite.isTriangulated_derivedAdequate_ringedSite :
    (DerivedCategoryB.derivedCategoryB (adequate.{u, u} B : ObjectProperty (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)))).IsTriangulated :=
  B.isTriangulated_derivedAdequate

attribute [local instance 2000] HasDerivedCategory.standard in
/-- `D_QCoh(S)` is a triangulated subcategory of `D(𝒪_S)`, read on the modules over the small
Zariski ringed site of `S`, the target of the morphism of [Stacks, Tag 070U]. -/
public instance isTriangulated_derivedQuasicoherent_zariskiRingedSite :
    (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf :
      ObjectProperty (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          S.zariskiRingedSite.toRingedTopos.O)))).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _
    (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre S)

/-! ### `Lf^*` is fully faithful -/

attribute [local instance 2000] HasDerivedCategory.standard in
/-- The unit of `Lf^* ⊣ Rf_*` between `D_QCoh(S)` and `D_Adeq(𝒪)` is invertible: it is the unit
of the ambient derived adjunction, invertible on `D_QCoh(S)` by [Stacks, Tag 070W]. -/
public theorem BigSite.isIso_derivedQuasicoherentAdequateAdjunction_unit_app
    (K : (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf :
      ObjectProperty (SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf
          S.zariskiRingedSite.toRingedTopos.O)))).FullSubcategory) :
    IsIso (B.derivedQuasicoherentAdequateAdjunction.unit.app K) :=
  DerivedCategoryB.isIso_restrictAdjunction_unit_app _ _ _ _ B.derivedZariskiAdjunction
    (fun K hK ↦ B.isIso_derivedZariskiAdjunction_unit_app K hK) K

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **`Lf^* : D_QCoh(S) ⥤ D_Adeq(𝒪)` is fully faithful**, the unit of `Lf^* ⊣ Rf_*` being
invertible. -/
public def BigSite.fullyFaithfulDerivedQuasicoherentPullback :
    B.derivedQuasicoherentPullback.FullyFaithful :=
  haveI := B.isIso_derivedQuasicoherentAdequateAdjunction_unit_app
  haveI : IsIso B.derivedQuasicoherentAdequateAdjunction.unit := NatIso.isIso_of_isIso_app _
  B.derivedQuasicoherentAdequateAdjunction.fullyFaithfulLOfIsIsoUnit

/-! ### `Rf_*` is triangulated -/

attribute [local instance 2000] HasDerivedCategory.standard in
/-- The restricted `Lf^* : D_QCoh(S) ⥤ D_Adeq(𝒪)` commutes with the shifts, as the ambient
derived pullback does ([Stacks, Tag 06YY]). -/
@[instance_reducible]
public def BigSite.derivedQuasicoherentPullbackCommShift :
    B.derivedQuasicoherentPullback.CommShift ℤ :=
  haveI := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    B.zariskiRingedToposHom
  @DerivedCategoryB.commShift_liftLeft _ _ _ _ _ _ _ _ _ _
    B.isTriangulated_derivedAdequate_ringedSite
    (isTriangulated_derivedQuasicoherent_zariskiRingedSite (S := S)) B.derivedZariskiPullback _
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_commShift B.zariskiRingedToposHom)

attribute [local instance 2000] HasDerivedCategory.standard in
/-- The restricted `Lf^* : D_QCoh(S) ⥤ D_Adeq(𝒪)` is triangulated, as the ambient derived
pullback is ([Stacks, Tag 06YY]). -/
public theorem BigSite.isTriangulated_derivedQuasicoherentPullback :
    letI := B.derivedQuasicoherentPullbackCommShift
    B.derivedQuasicoherentPullback.IsTriangulated := by
  have := Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy
    B.zariskiRingedToposHom
  exact @DerivedCategoryB.isTriangulated_liftLeft _ _ _ _ _ _ _ _ _ _
    B.isTriangulated_derivedAdequate_ringedSite
    (isTriangulated_derivedQuasicoherent_zariskiRingedSite (S := S)) B.derivedZariskiPullback _
    (Stacks.Cohomology.DerivedPullbackOfToposHom.derivedPullback_commShift B.zariskiRingedToposHom)
    (Stacks.Cohomology.DerivedPullbackOfToposHom.isTriangulated_derivedPullback
      B.zariskiRingedToposHom)

attribute [local instance 2000] HasDerivedCategory.standard in
/-- The shift datum of the restricted `Rf_* : D_Adeq(𝒪) ⥤ D_QCoh(S)`, transported across the
adjunction `Lf^* ⊣ Rf_*` from that of `Lf^*`. -/
@[instance_reducible]
public def BigSite.derivedAdequateDirectImageCommShift :
    B.derivedAdequateDirectImage.CommShift ℤ :=
  letI := B.derivedQuasicoherentPullbackCommShift
  B.derivedQuasicoherentAdequateAdjunction.rightAdjointCommShift ℤ

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **The restricted `Rf_* : D_Adeq(𝒪) ⥤ D_QCoh(S)` is triangulated**, as the right adjoint of
the triangulated functor `Lf^*`. -/
public theorem BigSite.isTriangulated_derivedAdequateDirectImage :
    letI := B.derivedAdequateDirectImageCommShift
    B.derivedAdequateDirectImage.IsTriangulated := by
  let := B.derivedQuasicoherentPullbackCommShift
  let := B.derivedAdequateDirectImageCommShift
  have := B.isTriangulated_derivedQuasicoherentPullback
  have : B.derivedQuasicoherentAdequateAdjunction.CommShift ℤ :=
    B.derivedQuasicoherentAdequateAdjunction.commShift_of_leftAdjoint ℤ
  exact B.derivedQuasicoherentAdequateAdjunction.isTriangulated_rightAdjoint

/-! ### `D_𝒞(𝒪)` is the kernel of `Rf_*` -/

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **The first step of [Stacks, Tag 070X]: `D_𝒞(𝒪)` is the kernel of `Rf_*`.** A complex `K`
with adequate cohomology has `Rf_*K = 0` exactly when its cohomology modules are parasitic:
`Hⁿ(Rf_*K) ≅ f_*Hⁿ(K)`, and an adequate module is parasitic exactly when its restriction to the
small Zariski site of `S` vanishes ([Stacks, Tag 06ZM]). -/
public theorem BigSite.kernel_derivedAdequateDirectImage :
    B.derivedAdequateDirectImage.kernel =
      (BigSite.derivedParasitic B).inverseImage
        (DerivedCategoryB.derivedCategoryB (adequate.{u, u} B : ObjectProperty (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)))).ι := by
  ext K
  have hzero : IsZero (B.derivedAdequateDirectImage.obj K) ↔
      IsZero (B.derivedZariskiPushforward.obj K.obj) :=
    ⟨fun h ↦ (ObjectProperty.ι _).map_isZero h,
      fun h ↦ IsZero.of_full_of_faithful_of_isZero (ObjectProperty.ι _) _ h⟩
  refine hzero.trans ⟨fun h n ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨e⟩ := B.nonempty_homology_derivedZariskiPushforward_iso K.obj K.property n
    exact (B.parasiticModule_iff_isZero _ (K.property n)).2
      ((((DerivedCategory.homologyFunctor _ n).map_isZero h)).of_iso e.symm)
  · set X := B.derivedZariskiPushforward.obj K.obj
    have hX : ∀ n : ℤ, IsZero ((DerivedCategory.homologyFunctor _ n).obj X) := fun n ↦ by
      obtain ⟨e⟩ := B.nonempty_homology_derivedZariskiPushforward_iso K.obj K.property n
      exact ((B.parasiticModule_iff_isZero _ (K.property n)).1 (h n)).of_iso e
    have : IsIso (0 : X ⟶ X) := (DerivedCategory.isIso_iff _ _).2 fun n ↦ (hX n).isIso (hX n) _
    exact (IsZero.iff_id_eq_zero _).2 ((cancel_mono (0 : X ⟶ X)).1 (by simp))

/-! ### The equivalence -/

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 070X].** Let `S` be a scheme and `f : ((Sch/S)_τ, 𝒪) ⟶ (S_Zar, 𝒪_S)` the
morphism of [Stacks, Tag 070U], for a chosen big site and any of the five topologies. The derived
direct image `Rf_* : D_Adeq(𝒪) ⥤ D_QCoh(S)` is the Verdier quotient of `D_Adeq(𝒪)` by
`D_𝒞(𝒪)`, the complexes whose cohomology modules are parasitic adequate: it is a localization
functor for the morphisms whose cone lies in `D_𝒞(𝒪)`, so that it induces an equivalence
`D_Adeq(𝒪)/D_𝒞(𝒪) ⟶ D_QCoh(S)`. -/
@[stacks 070X "the equivalence D_Adeq(O)/D_C(O) -> D_QCoh(S) induced by Rf_*, with the quotient
the Verdier quotient by the complexes with parasitic adequate cohomology, for the derived functors
of the morphism of Tag 070U on a chosen big site and each of the five topologies"]
public theorem BigSite.isLocalization_trW_derivedParasitic_derivedAdequateDirectImage :
    B.derivedAdequateDirectImage.IsLocalization
      ((BigSite.derivedParasitic B).inverseImage
        (DerivedCategoryB.derivedCategoryB (adequate.{u, u} B : ObjectProperty (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf B.ringedSite.toRingedTopos.O)))).ι).trW := by
  let := B.derivedAdequateDirectImageCommShift
  have := B.isTriangulated_derivedAdequateDirectImage
  have := B.fullyFaithfulDerivedQuasicoherentPullback.full
  have := B.fullyFaithfulDerivedQuasicoherentPullback.faithful
  exact B.isLocalization_trW_derivedParasitic_of_adjunction
    B.derivedQuasicoherentAdequateAdjunction B.kernel_derivedAdequateDirectImage

attribute [local instance 2000] HasDerivedCategory.standard in
/-- **[Stacks, Tag 070X], the equivalence `D_Adeq(𝒪)/D_𝒞(𝒪) ≌ D_QCoh(S)`.** The Verdier
quotient of `D_Adeq(𝒪)` by the complexes with parasitic adequate cohomology is equivalent to
`D_QCoh(S)`, by the functor induced by `Rf_*`. -/
@[stacks 070X "the equivalence of categories D_Adeq(O)/D_C(O) ≌ D_QCoh(S) itself, for the
derived functors of the morphism of Tag 070U on a chosen big site and each of the five
topologies"]
public def BigSite.derivedAdequateParasiticQuotientEquivalence :
    ((BigSite.derivedParasitic B).inverseImage
        (DerivedCategoryB.derivedCategoryB (adequate.{u, u} B : ObjectProperty (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            B.ringedSite.toRingedTopos.O)))).ι).trW.Localization ≌
      (DerivedCategoryB.derivedCategoryB (SheafOfModules.isQuasicoherent S.ringCatSheaf :
        ObjectProperty (SheafOfModules.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf
            S.zariskiRingedSite.toRingedTopos.O)))).FullSubcategory :=
  haveI := B.isLocalization_trW_derivedParasitic_derivedAdequateDirectImage
  Localization.equivalenceFromModel B.derivedAdequateDirectImage _

end Stacks.Adequate

end
