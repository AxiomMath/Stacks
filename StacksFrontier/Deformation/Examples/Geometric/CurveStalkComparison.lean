module

public import StacksFrontier.Deformation.Examples.Geometric.CurveChartGeometry
public import StacksFrontier.Deformation.Examples.Geometric.IsolatedSingularitiesChain
public import StacksFrontier.Deformation.Examples.Geometric.SchemesTwoOpenCoverSmooth
public import StacksFrontier.Examples.Deformations.Schemes.LocalRing

/-!
# The local ring of a deformation at a point of an affine chart

Let `X` be a scheme over a field `k`, `U ⊆ X` an affine open and `x ∈ U`. A deformation `Y` of
`X` gives two deformations of the local ring `𝒪_{X, x}`: its own local ring at `x`
(Stacks 0DZM), and the localization at the prime of `x` of the deformation of `Γ(X, U)` obtained
by restricting `Y` to `U` and taking sections (Stacks 0DYW, 0DYX, 0DYS), read at `𝒪_{X, x}`
through `Γ(X, U)_{𝔭_x} ≅ 𝒪_{X, x}`. This file proves the two functors isomorphic over `𝒞_Λ`.

## Main results

* `Deformation.Examples.localRingAtEquivStalk`: `Γ(X, U)_{𝔭_x} ≅ 𝒪_{X, x}`, and its
  `k`-linearity `Deformation.Examples.localRingAtEquivStalk_algebraMap`.
* `Deformation.Examples.isLocalization_chartStalkMap`: the local ring of a deformation at `x` is
  the localization of the sections of its chart at the inverse image of the prime of `x`.
* `Deformation.Examples.nonempty_iso_localRingDeformationFunctor`: **the comparison**.

## Implementation notes

The fibre isomorphism is the comparison of two localizations at the same submonoid. That the
submonoids agree is checked on units: an element of the chart is inverted in the local ring of
the deformation exactly when its image in `𝒪_{X, x}` is, the stalk map of the special-fibre
immersion being local, and that image is the germ of its reduction
(`Deformation.Examples.stalkMap_chartStalkMap`).
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace Deformation.Examples

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The `k`-algebra structure on the local ring of a scheme over `k` at a point, the one used by
`Deformation.Examples.localRingDeformationFunctor` (Stacks 0DZM). -/
@[instance_reducible]
noncomputable def stalkAlgebraOver (X : Over (Spec (.of k))) (x : X.left) :
    Algebra k (X.left.presheaf.stalk x) :=
  letI : Algebra k ((Spec (.of k)).presheaf.stalk (X.hom.base x)) :=
    StructureSheaf.stalkAlgebra k (X.hom.base x)
  ((X.hom.stalkMap x).hom.comp (algebraMap k _)).toAlgebra

/-- The local ring of `X` at a point of an affine open `U` is the localization of `Γ(X, U)` at the
corresponding prime. -/
noncomputable def localRingAtEquivStalk (X : Over (Spec (.of k))) {U : X.left.Opens}
    (hU : IsAffineOpen U) (x : U) :
    localRingAt (hU.primeIdealOf x) ≃+* X.left.presheaf.stalk (x : X.left) :=
  letI : Algebra Γ(X.left, U) (X.left.presheaf.stalk (x : X.left)) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf x
  haveI := hU.isLocalization_stalk x
  (IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl
    (localRingAt (hU.primeIdealOf x)) (X.left.presheaf.stalk (x : X.left))).toRingEquiv

/-- The identification of the local ring with the stalk carries the image of a section to its
germ. -/
theorem localRingAtEquivStalk_algebraMap_section (X : Over (Spec (.of k))) {U : X.left.Opens}
    (hU : IsAffineOpen U) (x : U) (r : Γ(X.left, U)) :
    localRingAtEquivStalk X hU x (algebraMap Γ(X.left, U) (localRingAt (hU.primeIdealOf x)) r) =
      X.left.presheaf.germ U x x.2 r := by
  let : Algebra Γ(X.left, U) (X.left.presheaf.stalk (x : X.left)) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf x
  have := hU.isLocalization_stalk x
  exact (IsLocalization.algEquiv (hU.primeIdealOf x).asIdeal.primeCompl
    (localRingAt (hU.primeIdealOf x)) (X.left.presheaf.stalk (x : X.left))).commutes r

/-- The germ of a section pulled back along `appLE` is the image of the germ under the stalk map. -/
private theorem germ_appLE_apply {S T : Scheme.{u}} (f : S ⟶ T) (U : T.Opens) (V : S.Opens)
    (e : V ≤ f ⁻¹ᵁ U) (p : S) (hp : p ∈ V) (s : Γ(T, U)) :
    S.presheaf.germ V p hp (f.appLE U V e s) = f.stalkMap p (T.presheaf.germ U (f p) (e hp) s) := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, TopCat.Presheaf.germ_res_apply]
  exact (Scheme.Hom.germ_stalkMap_apply f U p (e hp) s).symm

/-- That identification is `k`-linear. -/
theorem localRingAtEquivStalk_algebraMap (X : Over (Spec (.of k))) {U : X.left.Opens}
    (hU : IsAffineOpen U) (x : U) (a : k) :
    letI := sectionsAlgebra X.hom U
    letI := stalkAlgebraOver X (x : X.left)
    localRingAtEquivStalk X hU x (algebraMap k _ a) = algebraMap k _ a := by
  let := sectionsAlgebra X.hom U
  let := stalkAlgebraOver X (x : X.left)
  rw [IsScalarTower.algebraMap_apply k Γ(X.left, U) (localRingAt (hU.primeIdealOf x)),
    localRingAtEquivStalk_algebraMap_section]
  show X.left.presheaf.germ U x x.2 ((X.hom.appLE ⊤ U _) ((Scheme.ΓSpecIso (.of k)).inv a)) =
    (X.hom.stalkMap x) (StructureSheaf.toStalk k (X.hom.base x) a)
  exact germ_appLE_apply X.hom ⊤ U _ _ x.2 _

section Chart

variable (X : Over (Spec (.of k))) {U : X.left.Opens} (hU : IsAffineOpen U) (x : U)

/-- The deformation of `Γ(X, U)` obtained from a deformation of `X` by restricting it to `U` and
reading it through the presentation of `U` as a spectrum (Stacks 0DYX). -/
noncomputable abbrev chartDeformation (Y : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    letI := sectionsAlgebra X.hom U
    ringDeformationCategory (Λ := Λ) (k := k) Γ(X.left, U) :=
  letI := sectionsAlgebra X.hom U
  (chartBasedFunctor (Λ := Λ) Γ(X.left, U)
    (Over.isoMk hU.isoSpec (isoSpec_hom_comp_specMap_algebraMap X.hom hU))).obj
      ((openRestrictionFunctor X U).obj Y)

/-- The point of a deformation corresponding to `x` lies in the open corresponding to `U`. -/
theorem specialMap_mem_restrictedOpen (Y : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    Y.specialMap (x : X.left) ∈ restrictedOpen Y U :=
  ⟨x, x.2, rfl⟩

/-- The germ map from the sections of the chart deformation to the local ring of the
deformation at `x`. -/
noncomputable def chartStalkMap (Y : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    (chartDeformation X hU Y).left.fiber →+* Y.scheme.presheaf.stalk (Y.specialMap (x : X.left)) :=
  ((restrictedOpen Y U).toScheme.presheaf.germ ⊤ ⟨_, specialMap_mem_restrictedOpen X x Y⟩
      trivial ≫ ((restrictedOpen Y U).stalkIso ⟨_, specialMap_mem_restrictedOpen X x Y⟩).hom).hom

/-- The special-fibre map of the chart deformation, on sections: restrict along the special-fibre
immersion of the deformation to `U`. -/
theorem chartDeformation_special_apply (Y : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (t : Γ((restrictedOpen Y U).toScheme, ⊤)) :
    (chartDeformation X hU Y).hom.map.hom t =
      Y.specialMap.appLE (restrictedOpen Y U) U (le_specialMap_preimage_restrictedOpen Y U)
        ((restrictedOpen Y U).topIso.hom t) := by
  show (Scheme.ΓSpecIso Γ(X.left, U)).hom ((hU.isoSpec.inv ≫
    Y.specialMap.resLE (restrictedOpen Y U) U (le_specialMap_preimage_restrictedOpen Y U)).appTop
      t) = _
  rw [Scheme.Hom.comp_appTop, CommRingCat.comp_apply, hU.isoSpec_inv_appTop, Scheme.Hom.appTop,
    Scheme.Hom.resLE_app_top]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]

/-- The germ map, on sections: the germ at the point of the deformation of the corresponding
section of the deformation over the open corresponding to `U`. -/
theorem chartStalkMap_apply (Y : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (t : Γ((restrictedOpen Y U).toScheme, ⊤)) :
    chartStalkMap X hU x Y t =
      Y.scheme.presheaf.germ (restrictedOpen Y U) (Y.specialMap (x : X.left))
        (specialMap_mem_restrictedOpen X x Y) ((restrictedOpen Y U).topIso.hom t) := by
  show ((restrictedOpen Y U).stalkIso ⟨_, specialMap_mem_restrictedOpen X x Y⟩).hom
    ((restrictedOpen Y U).toScheme.presheaf.germ ⊤ ⟨_, specialMap_mem_restrictedOpen X x Y⟩
      trivial t) = _
  refine (congrArg (fun φ => φ.hom t) (Scheme.Opens.germ_stalkIso_hom (restrictedOpen Y U)
    (V := ⊤) ⟨_, specialMap_mem_restrictedOpen X x Y⟩ trivial)).trans ?_
  rw [Scheme.Opens.topIso_hom]
  exact (TopCat.Presheaf.germ_res_apply Y.scheme.presheaf _ (Y.specialMap (x : X.left))
    (specialMap_mem_restrictedOpen X x Y) t).symm

/-- **The germ map lifts the germ map of the special fibre.** -/
theorem stalkMap_chartStalkMap (Y : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (t : Γ((restrictedOpen Y U).toScheme, ⊤)) :
    Y.specialMap.stalkMap (x : X.left) (chartStalkMap X hU x Y t) =
      X.left.presheaf.germ U x x.2 ((chartDeformation X hU Y).hom.map.hom t) := by
  rw [chartStalkMap_apply, chartDeformation_special_apply, germ_appLE_apply]

include hU in
/-- The open of a deformation corresponding to an affine open is affine: it is a thickening of
it. -/
theorem isAffineOpen_restrictedOpen (Y : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    IsAffineOpen (restrictedOpen Y U) := by
  have : IsAffine U.toScheme := hU
  have : IsAffine (Over.mk (U.ι ≫ X.hom)).left := hU
  exact Stacks.Thickenings.isAffine_of_isThickening
    (i := (restrictDeformation U Y).specialMap)
    ⟨deformationSpecialMap_isClosedImmersion _, deformationSpecialMap_surjective _⟩

/-- **The local ring of a deformation at `x` is the localization of the sections of its chart at
the inverse image of the prime of `x`.** -/
theorem isLocalization_chartStalkMap (Y : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    letI := (chartStalkMap X hU x Y).toAlgebra
    IsLocalization ((hU.primeIdealOf x).asIdeal.primeCompl.comap
      (chartDeformation X hU Y).hom.map.hom)
      (Y.scheme.presheaf.stalk (Y.specialMap (x : X.left))) := by
  have h𝒰 := isAffineOpen_restrictedOpen X hU Y
  let y : restrictedOpen Y U := ⟨_, specialMap_mem_restrictedOpen X x Y⟩
  let : Algebra Γ(Y.scheme, restrictedOpen Y U)
      (Y.scheme.presheaf.stalk (Y.specialMap (x : X.left))) :=
    TopCat.Presheaf.algebra_section_stalk Y.scheme.presheaf y
  have hloc := h𝒰.isLocalization_stalk y
  let : Algebra Γ(X.left, U) (X.left.presheaf.stalk (x : X.left)) :=
    TopCat.Presheaf.algebra_section_stalk X.left.presheaf x
  have hlocX := hU.isLocalization_stalk x
  let h : Γ(Y.scheme, restrictedOpen Y U) ≃+* Γ((restrictedOpen Y U).toScheme, ⊤) :=
    (restrictedOpen Y U).topIso.symm.commRingCatIsoToRingEquiv
  have key := IsLocalization.isLocalization_of_base_ringEquiv
    (h𝒰.primeIdealOf y).asIdeal.primeCompl
    (Y.scheme.presheaf.stalk (Y.specialMap (x : X.left))) h
  have halg : (chartStalkMap X hU x Y).toAlgebra =
      ((algebraMap Γ(Y.scheme, restrictedOpen Y U)
        (Y.scheme.presheaf.stalk (Y.specialMap (x : X.left)))).comp h.symm.toRingHom).toAlgebra :=
    congrArg RingHom.toAlgebra (RingHom.ext fun t => chartStalkMap_apply X hU x Y t)
  have hsub : (hU.primeIdealOf x).asIdeal.primeCompl.comap
      (chartDeformation X hU Y).hom.map.hom =
      (h𝒰.primeIdealOf y).asIdeal.primeCompl.map h := by
    ext t
    have hmem : t ∈ (h𝒰.primeIdealOf y).asIdeal.primeCompl.map h ↔
        h.symm t ∈ (h𝒰.primeIdealOf y).asIdeal.primeCompl :=
      ⟨fun ⟨a, ha, hat⟩ => by rw [← hat]; simpa using ha,
        fun ht => ⟨_, ht, h.apply_symm_apply t⟩⟩
    refine Iff.trans ?_ hmem.symm
    have h1 := IsLocalization.AtPrime.isUnit_to_map_iff (X.left.presheaf.stalk (x : X.left))
      (hU.primeIdealOf x).asIdeal ((chartDeformation X hU Y).hom.map.hom t)
    have h2 := IsLocalization.AtPrime.isUnit_to_map_iff
      (Y.scheme.presheaf.stalk (Y.specialMap (x : X.left))) (h𝒰.primeIdealOf y).asIdeal
      ((restrictedOpen Y U).topIso.hom t)
    refine h1.symm.trans (Iff.trans ?_ h2)
    show IsUnit (X.left.presheaf.germ U x x.2 ((chartDeformation X hU Y).hom.map.hom t)) ↔
      IsUnit (Y.scheme.presheaf.germ (restrictedOpen Y U) _ (specialMap_mem_restrictedOpen X x Y)
        ((restrictedOpen Y U).topIso.hom t))
    rw [← chartStalkMap_apply X hU x Y t]
    exact (iff_of_eq (congrArg IsUnit (stalkMap_chartStalkMap X hU x Y t).symm)).trans
      (isUnit_map_iff (Y.specialMap.stalkMap (x : X.left)).hom _)
  rw [halg, hsub]
  exact key

/-- The germ map is linear over the Artinian base. -/
theorem chartStalkMap_algebraMap (Y : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (a : (chartDeformation X hU Y).left.base) :
    chartStalkMap X hU x Y
        (algebraMap (chartDeformation X hU Y).left.base (chartDeformation X hU Y).left.fiber a) =
      Y.toBase.stalkMap (Y.specialMap (x : X.left))
        (StructureSheaf.toStalk Y.base (Y.toBase (Y.specialMap (x : X.left))) a) := by
  show chartStalkMap X hU x Y ((((restrictedOpen Y U).ι ≫ Y.toBase).appTop)
    ((Scheme.ΓSpecIso (.of Y.base)).inv a)) = _
  rw [chartStalkMap_apply, Scheme.Hom.comp_appTop, CommRingCat.comp_apply,
    Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom]
  refine (TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans
    ((TopCat.Presheaf.germ_res_apply _ _ _ _ _).trans ?_)
  refine (Scheme.Hom.germ_stalkMap_apply Y.toBase ⊤ (Y.specialMap (x : X.left)) trivial
    ((Scheme.ΓSpecIso (.of Y.base)).inv a)).symm.trans ?_
  rfl

/-- The morphism of chart deformations induced by a morphism of deformations of `X`. -/
noncomputable abbrev chartDeformationMap {Y₁ Y₂ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (f : Y₁ ⟶ Y₂) : chartDeformation X hU Y₁ ⟶ chartDeformation X hU Y₂ :=
  letI := sectionsAlgebra X.hom U
  (chartBasedFunctor (Λ := Λ) Γ(X.left, U)
    (Over.isoMk hU.isoSpec (isoSpec_hom_comp_specMap_algebraMap X.hom hU))).map
      ((openRestrictionFunctor X U).map f)

omit [CommRing Λ] [Algebra Λ k] in
/-- Transporting a germ along an equality of points. -/
theorem eqToHom_stalk_germ {T : Scheme.{u}} {p q : T} (h : p = q) (V : T.Opens) (hp : p ∈ V)
    (r : Γ(T, V)) :
    (eqToHom (congrArg (fun y : T => T.presheaf.stalk y) h)).hom (T.presheaf.germ V p hp r) =
      T.presheaf.germ V q (h ▸ hp) r := by
  subst h
  rfl

/-- The germ map is natural in morphisms of deformations. -/
theorem chartStalkMap_naturality {Y₁ Y₂ : SchemeDeformationCategory (Λ := Λ) (k := k) X}
    (f : Y₁ ⟶ Y₂) (t : Γ((restrictedOpen Y₁ U).toScheme, ⊤)) :
    chartStalkMap X hU x Y₂ ((chartDeformationMap X hU f).left.map.hom t) =
      stalkMorphismRingHom X x f (chartStalkMap X hU x Y₁ t) := by
  have hpt : f.map (Y₂.specialMap (x : X.left)) = Y₁.specialMap (x : X.left) :=
    congrArg (fun t : X.left ⟶ Y₁.scheme => t (x : X.left)) f.special_compat
  show chartStalkMap X hU x Y₂ ((f.map.resLE (restrictedOpen Y₁ U) (restrictedOpen Y₂ U)
    (le_map_preimage_restrictedOpen f)).appTop t) = _
  rw [chartStalkMap_apply, chartStalkMap_apply, Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
  simp only [CommRingCat.comp_apply, Iso.inv_hom_id_apply]
  rw [germ_appLE_apply]
  unfold stalkMorphismRingHom
  rw [RingHom.comp_apply, eqToHom_stalk_germ]
  exact hpt.symm

end Chart


/-! ### The fibre isomorphism -/

section Fiber

variable (X : Over (Spec (.of k))) {U : X.left.Opens} (hU : IsAffineOpen U) (x : U)

/-- The localization functor of Stacks 0DYS at the prime of `x`. -/
noncomputable abbrev chartLocalization :=
  letI := sectionsAlgebra X.hom U
  localizationFunctor (Λ := Λ) (k := k) (hU.primeIdealOf x).asIdeal.primeCompl

/-- The localization of the chart deformation at the prime of `x` is the local ring of the
deformation at `x`. -/
noncomputable def chartFiberEquiv (Y : SchemeDeformationCategory (Λ := Λ) (k := k) X) :
    letI := sectionsAlgebra X.hom U
    ((chartLocalization X hU x).functor.obj (chartDeformation X hU Y)).left.fiber ≃+*
      Y.scheme.presheaf.stalk (Y.specialMap (x : X.left)) :=
  letI := sectionsAlgebra X.hom U
  letI := ((chartLocalization X hU x).localizationMap (chartDeformation X hU Y)).toAlgebra
  haveI := (chartLocalization X hU x).isLocalization (chartDeformation X hU Y)
  letI := (chartStalkMap X hU x Y).toAlgebra
  haveI := isLocalization_chartStalkMap X hU x Y
  (IsLocalization.algEquiv ((hU.primeIdealOf x).asIdeal.primeCompl.comap
    (chartDeformation X hU Y).hom.map.hom) _ _).toRingEquiv

/-- The isomorphism `chartFiberEquiv` sends the image of a section of the chart deformation in
its localization to the germ of that section at `x`. -/
theorem chartFiberEquiv_localizationMap (Y : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (t : (chartDeformation X hU Y).left.fiber) :
    letI := sectionsAlgebra X.hom U
    chartFiberEquiv X hU x Y
        ((chartLocalization X hU x).localizationMap (chartDeformation X hU Y) t) =
      chartStalkMap X hU x Y t := by
  let := sectionsAlgebra X.hom U
  let := ((chartLocalization X hU x).localizationMap (chartDeformation X hU Y)).toAlgebra
  have := (chartLocalization X hU x).isLocalization (chartDeformation X hU Y)
  let := (chartStalkMap X hU x Y).toAlgebra
  have := isLocalization_chartStalkMap X hU x Y
  exact (IsLocalization.algEquiv ((hU.primeIdealOf x).asIdeal.primeCompl.comap
    (chartDeformation X hU Y).hom.map.hom) _ _).commutes t

/-- Two ring maps out of the localization of the chart deformation agree as soon as they agree
on sections. -/
theorem chartLocalization_ringHom_ext (Y : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    {T : Type u} [CommRing T]
    (φ ψ : letI := sectionsAlgebra X.hom U
      ((chartLocalization X hU x).functor.obj (chartDeformation X hU Y)).left.fiber →+* T)
    (h : letI := sectionsAlgebra X.hom U
      ∀ t, φ ((chartLocalization X hU x).localizationMap (chartDeformation X hU Y) t) =
      ψ ((chartLocalization X hU x).localizationMap (chartDeformation X hU Y) t)) : φ = ψ := by
  let := sectionsAlgebra X.hom U
  exact @IsLocalization.ringHom_ext _ _ ((hU.primeIdealOf x).asIdeal.primeCompl.comap
    (chartDeformation X hU Y).hom.map.hom) _ _
    ((chartLocalization X hU x).localizationMap (chartDeformation X hU Y)).toAlgebra
    ((chartLocalization X hU x).isLocalization (chartDeformation X hU Y)) _ _ φ ψ
    (RingHom.ext h)

end Fiber

/-- **The local ring of a deformation at a point of an affine chart.** Restricting a deformation
of `X` to an affine open `U`, reading it as a deformation of `Γ(X, U)` (Stacks 0DYX), localizing at
the prime of a point `x ∈ U` (Stacks 0DYS) and transporting to the local ring of `X` at `x` is
isomorphic, over `𝒞_Λ`, to taking the local ring of the deformation at `x` (Stacks 0DZM). -/
theorem nonempty_iso_localRingDeformationFunctor (X : Over (Spec (.of k))) {U : X.left.Opens}
    (hU : IsAffineOpen U) (x : U) :
    letI := sectionsAlgebra X.hom U
    letI := stalkAlgebraOver X (x : X.left)
    Nonempty (BasedFunctor.comp
        (BasedFunctor.comp
          (BasedFunctor.comp (openRestrictionFunctor X U)
            (chartBasedFunctor (Λ := Λ) Γ(X.left, U)
              (Over.isoMk hU.isoSpec (isoSpec_hom_comp_specMap_algebraMap X.hom hU))))
          (localizationFunctor (Λ := Λ) (k := k) (hU.primeIdealOf x).asIdeal.primeCompl).functor)
        (ringDeformationTransport (localRingAtEquivStalk X hU x)
          (localRingAtEquivStalk_algebraMap X hU x)) ≅
      localRingDeformationFunctor (Λ := Λ) X (x : X.left)) := by
  let := sectionsAlgebra X.hom U
  let := stalkAlgebraOver X (x : X.left)
  refine ⟨basedIsoOfFiberEquiv _ _ (fun Y => chartFiberEquiv X hU x Y)
    (fun Y a => ?_) (fun Y z => ?_) (fun Y₁ Y₂ f z => ?_)⟩
  · -- linearity over the Artinian base
    refine (congrArg (chartFiberEquiv X hU x Y)
      (LocalizationFunctorData.algebraMap_base (chartLocalization (Λ := Λ) X hU x)
        (chartDeformation X hU Y) a)).trans ?_
    refine (chartFiberEquiv_localizationMap X hU x Y _).trans ?_
    refine (chartStalkMap_algebraMap X hU x Y _).trans ?_
    rfl
  · -- compatibility with the reductions to the special fibres
    let φ := (Y.specialMap.stalkMap (x : X.left)).hom.comp
      (chartFiberEquiv X hU x Y).toRingHom
    let ψ := (localRingAtEquivStalk X hU x).toRingHom.comp
      ((chartLocalization (Λ := Λ) X hU x).functor.obj (chartDeformation X hU Y)).hom.map.hom
    have hφψ : φ = ψ := by
      refine chartLocalization_ringHom_ext X hU x Y φ ψ fun t => ?_
      show Y.specialMap.stalkMap (x : X.left) (chartFiberEquiv X hU x Y
          ((chartLocalization (Λ := Λ) X hU x).localizationMap (chartDeformation X hU Y) t)) =
        localRingAtEquivStalk X hU x
          (((chartLocalization (Λ := Λ) X hU x).functor.obj (chartDeformation X hU Y)).hom.map.hom
            ((chartLocalization (Λ := Λ) X hU x).localizationMap (chartDeformation X hU Y) t))
      refine (congrArg _ (chartFiberEquiv_localizationMap X hU x Y t)).trans ?_
      refine (stalkMap_chartStalkMap X hU x Y t).trans ?_
      refine (localRingAtEquivStalk_algebraMap_section X hU x _).symm.trans ?_
      exact congrArg _ ((chartLocalization (Λ := Λ) X hU x).specialFiber_comm
        (chartDeformation X hU Y) t)
    exact RingHom.congr_fun hφψ z
  · -- naturality
    let φ := (chartFiberEquiv X hU x Y₂).toRingHom.comp
      ((chartLocalization (Λ := Λ) X hU x).functor.map (chartDeformationMap X hU f)).left.map.hom
    let ψ := (stalkMorphismRingHom X x f).comp (chartFiberEquiv X hU x Y₁).toRingHom
    have hφψ : φ = ψ := by
      refine chartLocalization_ringHom_ext X hU x Y₁ φ ψ fun t => ?_
      show chartFiberEquiv X hU x Y₂
          (((chartLocalization (Λ := Λ) X hU x).functor.map
              (chartDeformationMap X hU f)).left.map.hom
            ((chartLocalization (Λ := Λ) X hU x).localizationMap (chartDeformation X hU Y₁) t)) =
        stalkMorphismRingHom X x f (chartFiberEquiv X hU x Y₁
          ((chartLocalization (Λ := Λ) X hU x).localizationMap (chartDeformation X hU Y₁) t))
      refine (congrArg _ ((chartLocalization (Λ := Λ) X hU x).naturality
        (chartDeformationMap X hU f) t).symm).trans ?_
      refine (chartFiberEquiv_localizationMap X hU x Y₂ _).trans ?_
      refine (chartStalkMap_naturality X hU x f t).trans ?_
      exact congrArg _ (chartFiberEquiv_localizationMap X hU x Y₁ t).symm
    exact RingHom.congr_fun hφψ z

end Deformation.Examples
