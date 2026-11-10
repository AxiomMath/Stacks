module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# The stalk of a quasi-coherent module on an affine open is a localization

Let `F` be a quasi-coherent `𝒪_X`-module on a scheme `X` and let `U` be an affine open of `X`.
The germ map `Γ(F, U) → F_x` at a point `x ∈ U` exhibits the stalk `F_x` as the localization of
the module of sections `Γ(F, U)` at the prime of `Γ(X, U)` corresponding to `x`.

This is the affine-local bridge through which statements about associated points of `F` at `x`
are translated into statements about associated primes of the `Γ(X, U)`-module `Γ(F, U)`.

## Main definitions

* `AlgebraicGeometry.affineStalkModule` is the `Γ(X, U)`-module structure on the stalk `F_x`
  obtained by restricting scalars along the germ map of the structure sheaf.
* `AlgebraicGeometry.affineGerm` is the germ map `Γ(F, U) → F_x`, as a `Γ(X, U)`-linear map.
* `AlgebraicGeometry.fromSpecSectionsIso` and
  `AlgebraicGeometry.fromSpecSectionsLinearEquiv` identify the global sections of the
  restriction of `F` along `IsAffineOpen.fromSpec` with `Γ(F, U)`.

## Main results

* `AlgebraicGeometry.affineGerm_isLocalized`: the germ map is a localization of modules at the
  prime corresponding to the point.
* `AlgebraicGeometry.germ_eq_zero_iff_exists_smul_eq_zero_affine`: a section of `F` over an
  affine open has vanishing germ at `x` exactly when some element of `Γ(X, U)` outside the
  corresponding prime kills it.
* `AlgebraicGeometry.affine_exists_global_multiple`: every element of the stalk becomes the
  germ of a global section after multiplication by an element outside the prime.

## Implementation notes

The module structure on the stalk of an `𝒪_X`-module over the stalk of the structure sheaf is
supplied explicitly throughout, because typeclass resolution does not find it for an
`X.Modules`; see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Divisors/AssociatedPoints.lean`.

The affine case is reduced to the case of a global `Spec` by restricting `F` along
`IsAffineOpen.fromSpec`; the comparison of sections, of germs and of the scalar action under
that restriction is what the `fromSpecSectionsIso` family of lemmas provides.

## References

* [Stacks Project, Tag 02OK](https://stacks.math.columbia.edu/tag/02OK)
* [Stacks Project, Tag 056M](https://stacks.math.columbia.edu/tag/056M)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The stalk `F_x` of an `𝒪_X`-module at a point of an open `U`, as a module over the ring of
sections `Γ(X, U)`: scalars act through the germ map `Γ(X, U) → 𝒪_{X, x}`. -/
@[instance_reducible]
noncomputable def affineStalkModule {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (x : X)
    (hx : x ∈ U) :
    Module Γ(X, U) (F.presheaf.stalk x) :=
  letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  Module.compHom _ (X.presheaf.germ U x hx).hom

/-- The germ map `Γ(F, U) → F_x` of an `𝒪_X`-module at a point of an open `U`, as a
`Γ(X, U)`-linear map. -/
noncomputable def affineGerm {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (x : X)
    (hx : x ∈ U) :
    letI := affineStalkModule F U x hx
    Γ(F, U) →ₗ[Γ(X, U)] F.presheaf.stalk x :=
  letI := affineStalkModule F U x hx
  { toFun := F.presheaf.germ U x hx
    map_add' := by simp
    map_smul' r m := F.val.germ_smul x U hx r m }

/-- On an affine open, every element of `Γ(X, U)` outside the prime corresponding to `x` acts
invertibly on the stalk `F_x`. -/
lemma affineGerm_map_units {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) (hU : IsAffineOpen U)
    (x : X) (hx : x ∈ U) :
    letI := affineStalkModule F U x hx
    ∀ s : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl,
      IsUnit (algebraMap Γ(X, U) (Module.End Γ(X, U) (F.presheaf.stalk x)) s.1) := by
  let := affineStalkModule F U x hx
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hx).hom.toAlgebra
  let : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hx⟩
  intro s
  rw [Module.End.isUnit_iff]
  change Function.Bijective
    (fun a : F.presheaf.stalk x => (X.presheaf.germ U x hx).hom s.1 • a)
  exact ((IsLocalization.AtPrime.isUnit_to_map_iff
    (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hx⟩).asIdeal s.1).mpr s.2).smul_bijective

/-- A global section of a quasi-coherent module on `Spec R` has vanishing germ at a point
exactly when it is killed by a ring element outside the corresponding prime. -/
lemma germ_eq_zero_iff_exists_smul_eq_zero {R : CommRingCat.{u}} (F : (Spec R).Modules)
    [F.IsQuasicoherent] (s : Γ(F, ⊤)) (x : Spec R) :
    F.presheaf.germ ⊤ x trivial s = 0 ↔ ∃ r : R, r ∉ x.asIdeal ∧ r • s = 0 := by
  let M := modulesSpecToSheaf.obj F
  let φ (f : R) := (M.obj.map (PrimeSpectrum.basicOpen f).leTop.op).hom
  have hφ (f : R) : IsLocalizedModule.Away f (φ f) :=
    (isIso_fromTildeΓ_iff_isLocalizing F).mp inferInstance f
  constructor
  · intro hs
    have hs' : F.presheaf.germ ⊤ x trivial s = F.presheaf.germ ⊤ x trivial 0 := by simpa
    obtain ⟨V, hxV, i, hi, his⟩ := TopCat.Presheaf.germ_eq
      (U := ⊤) (V := ⊤) F.presheaf x trivial trivial s (0 : Γ(F, ⊤)) hs'
    obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hxr, hrV⟩ :=
      PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hxV V.2
    have hzV : F.presheaf.map i.op s = 0 := his.trans (map_zero _)
    have hle : (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ ⊤ := le_top
    have hrV' : (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ V := hrV
    have hh : (homOfLE hle).op = i.op ≫ (homOfLE hrV').op := Subsingleton.elim _ _
    have hz : F.presheaf.map (homOfLE hle).op s = 0 :=
      (congrArg (fun m => (ConcreteCategory.hom (F.presheaf.map m)) s) hh).trans
        ((F.presheaf.map_comp_apply i.op (homOfLE hrV').op s).trans
          (by rw [hzV, map_zero]))
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := (IsLocalizedModule.eq_zero_iff (.powers r) (φ r)).mp hz
    exact ⟨r ^ n, fun h ↦ hxr (Ideal.IsPrime.mem_of_pow_mem x.isPrime n h), hn⟩
  · rintro ⟨r, hrx, hrs⟩
    have hz : φ r s = 0 :=
      (IsLocalizedModule.eq_zero_iff (.powers r) (φ r)).mpr ⟨⟨r, Submonoid.mem_powers r⟩, hrs⟩
    rw [← F.presheaf.germ_res (PrimeSpectrum.basicOpen r).leTop x hrx]
    change F.presheaf.germ (PrimeSpectrum.basicOpen r) x hrx (φ r s) = 0
    rw [hz]
    exact map_zero _

/-- The map on sections of `IsAffineOpen.fromSpec` from `U` to the whole of `Spec Γ(X, U)` is
the inverse of the canonical identification `Γ(Spec Γ(X, U), ⊤) ≅ Γ(X, U)`. -/
lemma fromSpec_appLE_top {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec.appLE U ⊤ (by rw [hU.fromSpec_preimage_self]) =
      (Scheme.ΓSpecIso Γ(X, U)).inv := by
  simp only [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
  simp

/-- The global sections of the restriction of `F` along `IsAffineOpen.fromSpec` are the
sections of `F` over the affine open `U`. -/
noncomputable def fromSpecSectionsIso {X : Scheme.{u}} (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) :
    Γ(F.restrict hU.fromSpec, ⊤) ≅ Γ(F, U) :=
  F.restrictAppIso hU.fromSpec ⊤ ≪≫
    F.presheaf.mapIso (eqToIso (by
      rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec])).symm.op

/-- The identification `fromSpecSectionsIso` is `Γ(X, U)`-linear. -/
lemma fromSpecSectionsIso_smul {X : Scheme.{u}} (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) (r : Γ(X, U)) (t : Γ(F.restrict hU.fromSpec, ⊤)) :
    (fromSpecSectionsIso F hU).hom (r • t) = r • (fromSpecSectionsIso F hU).hom t := by
  let f := hU.fromSpec
  have he : f ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  have hr : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (f.appIso ⊤).inv =
      X.presheaf.map (eqToHom he).op := by
    rw [← fromSpec_appLE_top hU]
    exact f.appLE_appIso_inv _
  change F.presheaf.map (eqToHom he.symm).op ((F.restrictAppIso f ⊤).hom (r • t)) = _
  rw [Scheme.Modules.smul_Spec_def]
  simp only [Opens.leTop, homOfLE_refl, op_id]
  rw [(Spec Γ(X, U)).presheaf.map_id]
  simp only [CommRingCat.id_apply]
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, F.map_smul]
  have hr' : X.presheaf.map (eqToHom he.symm).op
      ((f.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv r)) = r := by
    simp only [← CommRingCat.comp_apply, hr, ← Functor.map_comp]
    simp
  rw [hr']
  rfl

/-- The identification `fromSpecSectionsIso` is compatible with germs: the germ at a point of
`Spec Γ(X, U)` of a global section of the restriction is carried by the stalk comparison
isomorphism to the germ of the corresponding section of `F`. -/
lemma fromSpecSectionsIso_germ {X : Scheme.{u}} (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) (t : Γ(F.restrict hU.fromSpec, ⊤)) (y : Spec Γ(X, U)) :
    ((Scheme.Modules.restrictStalkNatIso hU.fromSpec y).hom.app F).hom
        ((F.restrict hU.fromSpec).presheaf.germ ⊤ y trivial t) =
      F.presheaf.germ U (hU.fromSpec y) (hU.isoSpec.inv y).2
        ((fromSpecSectionsIso F hU).hom t) := by
  let f := hU.fromSpec
  have he : f ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  change _ = F.presheaf.germ U (f y) _ (F.presheaf.map (eqToHom he.symm).op t)
  exact (ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app f y F (U := ⊤) trivial) t).trans
    (F.presheaf.germ_res_apply (eqToHom he.symm) (f y) (hU.isoSpec.inv y).2 t).symm

/-- Vanishing of the germ of a section of `F` over `U` at a point is vanishing of the germ of
the corresponding global section of the restriction along `IsAffineOpen.fromSpec`. -/
lemma fromSpecSectionsIso_germ_eq_zero_iff {X : Scheme.{u}} (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) (t : Γ(F.restrict hU.fromSpec, ⊤)) (x : Spec Γ(X, U)) :
    F.presheaf.germ U (hU.fromSpec x) (hU.isoSpec.inv x).2
        ((fromSpecSectionsIso F hU).hom t) = 0 ↔
      (F.restrict hU.fromSpec).presheaf.germ ⊤ x trivial t = 0 := by
  rw [← fromSpecSectionsIso_germ F hU t x]
  exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso
    ((Scheme.Modules.restrictStalkNatIso hU.fromSpec x).hom.app F)).injective

/-- A section of a quasi-coherent module over an affine open has vanishing germ at a point
exactly when it is killed by an element of `Γ(X, U)` outside the corresponding prime. -/
lemma germ_eq_zero_iff_exists_smul_eq_zero_affine {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) (s : Γ(F, U)) :
    F.presheaf.germ U x hx s = 0 ↔
      ∃ r : Γ(X, U), r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ∧ r • s = 0 := by
  let G := F.restrict hU.fromSpec
  let : G.IsQuasicoherent := inferInstance
  let e := fromSpecSectionsIso F hU
  let t : Γ(G, ⊤) := e.inv s
  have ht : e.hom t = s := by simp [t]
  let y := hU.primeIdealOf ⟨x, hx⟩
  have hy : hU.fromSpec y = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  have hs (r : Γ(X, U)) : r • s = 0 ↔ r • t = 0 := by
    rw [← ht, ← fromSpecSectionsIso_smul F hU r t]
    exact map_eq_zero_iff _ (ConcreteCategory.bijective_of_isIso e.hom).injective
  have hg : F.presheaf.germ U x hx s = 0 ↔ G.presheaf.germ ⊤ y trivial t = 0 := by
    have h := fromSpecSectionsIso_germ_eq_zero_iff F hU t y
    have hy' : hU.isoSpec.inv y = ⟨x, hx⟩ := Subtype.ext hy
    change F.presheaf.germ U (hU.isoSpec.inv y).1 (hU.isoSpec.inv y).2 (e.hom t) = 0 ↔ _ at h
    rwa [hy', ht] at h
  rw [hg, germ_eq_zero_iff_exists_smul_eq_zero G t y]
  exact exists_congr fun r => and_congr_right fun _ => (hs r).symm

/-- Two sections of a quasi-coherent module over an affine open with the same germ at a point
agree after multiplication by an element outside the corresponding prime. -/
lemma affineGerm_exists_of_eq {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) {a b : Γ(F, U)}
    (hab : F.presheaf.germ U x hx a = F.presheaf.germ U x hx b) :
    ∃ c : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl, c.1 • a = c.1 • b := by
  have hz : F.presheaf.germ U x hx (a - b) = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨c, hc, hzero⟩ :=
    (germ_eq_zero_iff_exists_smul_eq_zero_affine F U hU x hx (a - b)).mp hz
  exact ⟨⟨c, hc⟩, sub_eq_zero.mp (by simpa only [smul_sub] using hzero)⟩

/-- Every element of the stalk at a point of a quasi-coherent module on `Spec R` becomes the
germ of a global section after multiplication by a ring element outside the corresponding
prime. -/
lemma spec_exists_global_multiple {R : CommRingCat.{u}} (G : (Spec R).Modules)
    [G.IsQuasicoherent] (y : Spec R) (z : G.presheaf.stalk y) :
    letI : Module ((Spec R).presheaf.stalk y) (G.presheaf.stalk y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := (Spec R).presheaf) G.val y
    ∃ r : R, r ∉ y.asIdeal ∧ ∃ m : Γ(G, ⊤),
      (Spec R).presheaf.germ ⊤ y trivial ((Scheme.ΓSpecIso R).inv r) • z =
        G.presheaf.germ ⊤ y trivial m := by
  let : Module ((Spec R).presheaf.stalk y) (G.presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (Spec R).presheaf) G.val y
  let M := modulesSpecToSheaf.obj G
  obtain ⟨V, hyV, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf z
  obtain ⟨a, ⟨_, ⟨r, rfl⟩, rfl⟩, hyr, hrV⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open hyV V.2
  let b : Γ(G, PrimeSpectrum.basicOpen r) := G.presheaf.map (homOfLE hrV).op t
  let φ := (M.obj.map (PrimeSpectrum.basicOpen r).leTop.op).hom
  have hφ : IsLocalizedModule (.powers r) φ :=
    (isIso_fromTildeΓ_iff_isLocalizing G).mp inferInstance r
  obtain ⟨⟨m, s⟩, hms⟩ := IsLocalizedModule.surj (.powers r) φ b
  refine ⟨s.1, ?_, m, ?_⟩
  · obtain ⟨n, hn⟩ := s.2
    rw [← hn]
    exact fun h ↦ hyr (y.isPrime.mem_of_pow_mem n h)
  · have hEq := congrArg (fun w : Γ(G, PrimeSpectrum.basicOpen r) =>
      TopCat.Presheaf.germ G.val.presheaf (PrimeSpectrum.basicOpen r) y hyr w) hms
    let : Module ((Spec R).presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := (Spec R).presheaf) G.val y
    let : Module Γ(Spec R, PrimeSpectrum.basicOpen r) Γ(G, PrimeSpectrum.basicOpen r) :=
      (G.val.obj (.op (PrimeSpectrum.basicOpen r))).isModule
    let : Module R Γ(G, PrimeSpectrum.basicOpen r) :=
      (M.obj.obj (.op (PrimeSpectrum.basicOpen r))).isModule
    rw [← (Spec R).presheaf.germ_res_apply
      (homOfLE (show PrimeSpectrum.basicOpen r ≤ (⊤ : (Spec R).Opens) from le_top))
      y hyr ((Scheme.ΓSpecIso R).inv s.1), ← G.presheaf.germ_res_apply (homOfLE hrV) y hyr t,
      ← G.presheaf.germ_res_apply
        (homOfLE (show PrimeSpectrum.basicOpen r ≤ (⊤ : (Spec R).Opens) from le_top)) y hyr m]
    change (Spec R).presheaf.germ (PrimeSpectrum.basicOpen r) y hyr
        ((Spec R).presheaf.map (PrimeSpectrum.basicOpen r).leTop.op
          ((Scheme.ΓSpecIso R).inv s.1)) •
        TopCat.Presheaf.germ G.val.presheaf (PrimeSpectrum.basicOpen r) y hyr b =
      TopCat.Presheaf.germ G.val.presheaf (PrimeSpectrum.basicOpen r) y hyr (φ m)
    have hc := G.val.germ_smul y (PrimeSpectrum.basicOpen r) hyr
      ((Spec R).presheaf.map (PrimeSpectrum.basicOpen r).leTop.op
        ((Scheme.ΓSpecIso R).inv s.1)) b
    have hc' :
        TopCat.Presheaf.germ G.val.presheaf (PrimeSpectrum.basicOpen r) y hyr
            (((Spec R).presheaf.map (PrimeSpectrum.basicOpen r).leTop.op
              ((Scheme.ΓSpecIso R).inv s.1)) • b) =
          (Spec R).presheaf.germ (PrimeSpectrum.basicOpen r) y hyr
              ((Spec R).presheaf.map (PrimeSpectrum.basicOpen r).leTop.op
                ((Scheme.ΓSpecIso R).inv s.1)) •
            TopCat.Presheaf.germ G.val.presheaf (PrimeSpectrum.basicOpen r) y hyr b := by
      convert hc using 1 <;> rfl
    have hsmul : ((Spec R).presheaf.map (PrimeSpectrum.basicOpen r).leTop.op
        ((Scheme.ΓSpecIso R).inv s.1)) • b = (s.1 : R) • b :=
      (Scheme.Modules.smul_Spec_def s.1 b).symm
    rw [← hc', hsmul]
    exact hEq

/-- The stalk comparison isomorphism for the restriction along `IsAffineOpen.fromSpec`
transports the action of a global section of the structure sheaf of `Spec Γ(X, U)` to the
action of the corresponding section of `𝒪_X` over `U`. -/
lemma fromSpec_stalk_smul_global {X : Scheme.{u}} (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) (y : Spec Γ(X, U)) (r : Γ(X, U))
    (z : (F.restrict hU.fromSpec).presheaf.stalk y) :
    letI : Module ((Spec Γ(X, U)).presheaf.stalk y)
        ((F.restrict hU.fromSpec).presheaf.stalk y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := (Spec Γ(X, U)).presheaf) (F.restrict hU.fromSpec).val y
    letI : Module (X.presheaf.stalk (hU.fromSpec y)) (F.presheaf.stalk (hU.fromSpec y)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val (hU.fromSpec y)
    ((Scheme.Modules.restrictStalkNatIso hU.fromSpec y).hom.app F).hom
        ((Spec Γ(X, U)).presheaf.germ ⊤ y trivial ((Scheme.ΓSpecIso Γ(X, U)).inv r) • z) =
      X.presheaf.germ U (hU.fromSpec y) (hU.isoSpec.inv y).2 r •
        (show F.presheaf.stalk (hU.fromSpec y) from
          ((Scheme.Modules.restrictStalkNatIso hU.fromSpec y).hom.app F).hom z) := by
  let f := hU.fromSpec
  let G := F.restrict f
  let : Module ((Spec Γ(X, U)).presheaf.stalk y) (G.presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := (Spec Γ(X, U)).presheaf) G.val y
  let : Module (X.presheaf.stalk (f y)) (F.presheaf.stalk (f y)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (f y)
  obtain ⟨V, hyV, t, ht⟩ := TopCat.Presheaf.exists_germ_eq G.presheaf z
  rw [← ht]
  let rv : Γ(Spec Γ(X, U), V) :=
    (Spec Γ(X, U)).presheaf.map V.leTop.op ((Scheme.ΓSpecIso Γ(X, U)).inv r)
  have hVU : V ≤ f ⁻¹ᵁ U := by
    rw [hU.fromSpec_preimage_self]
    exact le_top
  have hVimage : f ''ᵁ V ≤ U :=
    (f.image_mono hVU).trans (f.image_preimage_eq_opensRange_inf U ▸ inf_le_right)
  have hrv : (f.appIso V).inv rv = X.presheaf.map (homOfLE hVimage).op r := by
    have hm := f.appLE_map (e := show ⊤ ≤ f ⁻¹ᵁ U from by
      rw [hU.fromSpec_preimage_self]) V.leTop.op
    have hv : rv = f.appLE U V hVU r := by
      dsimp [rv]
      rw [← fromSpec_appLE_top hU]
      exact (ConcreteCategory.congr_hom hm r).symm
    rw [hv]
    exact ConcreteCategory.congr_hom (f.appLE_appIso_inv hVU) r
  have hg (w : Γ(G, V)) :
      ((Scheme.Modules.restrictStalkNatIso f y).hom.app F).hom (G.presheaf.germ V y hyV w) =
        F.presheaf.germ (f ''ᵁ V) (f y) (by simpa) ((F.restrictAppIso f V).hom w) :=
    ConcreteCategory.congr_hom
      (Scheme.Modules.germ_restrictStalkNatIso_hom_app f y F hyV) w
  rw [← (Spec Γ(X, U)).presheaf.germ_res_apply V.leTop y hyV
    ((Scheme.ΓSpecIso Γ(X, U)).inv r)]
  change ((Scheme.Modules.restrictStalkNatIso f y).hom.app F).hom
      ((Spec Γ(X, U)).presheaf.germ V y hyV rv • G.presheaf.germ V y hyV t) = _
  have hsmul := (G.val.germ_smul y V hyV rv t).symm
  have hsmulq := congrArg (fun w : G.presheaf.stalk y =>
    ((Scheme.Modules.restrictStalkNatIso f y).hom.app F).hom w) hsmul
  refine hsmulq.trans ((hg (rv • t)).trans ?_)
  rw [Scheme.Modules.smul_restrictAppIso_hom_apply, hrv,
    ← X.presheaf.germ_res_apply (homOfLE hVimage) (f y) (by simpa) r, hg]
  convert F.val.germ_smul (f y) (f ''ᵁ V) (by simpa)
    (X.presheaf.map (homOfLE hVimage).op r) ((F.restrictAppIso f V).hom t) using 1
  rfl

/-- Every element of the stalk of a quasi-coherent module at a point of an affine open becomes
the germ of a section over that open after multiplication by an element of `Γ(X, U)` outside
the corresponding prime. -/
lemma affine_exists_global_multiple {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (y : Spec Γ(X, U))
    (z : F.presheaf.stalk (hU.fromSpec y)) :
    letI : Module (X.presheaf.stalk (hU.fromSpec y)) (F.presheaf.stalk (hU.fromSpec y)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val (hU.fromSpec y)
    ∃ r : Γ(X, U), r ∉ y.asIdeal ∧ ∃ m : Γ(F, U),
      X.presheaf.germ U (hU.fromSpec y) (hU.isoSpec.inv y).2 r • z =
        F.presheaf.germ U (hU.fromSpec y) (hU.isoSpec.inv y).2 m := by
  let f := hU.fromSpec
  let G := F.restrict f
  let : G.IsQuasicoherent := inferInstance
  let : Module (X.presheaf.stalk (f y)) (F.presheaf.stalk (f y)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (f y)
  let q := (Scheme.Modules.restrictStalkNatIso f y).hom.app F
  let z' : G.presheaf.stalk y := ((Scheme.Modules.restrictStalkNatIso f y).inv.app F).hom z
  obtain ⟨r, hr, m, hm⟩ := spec_exists_global_multiple G y z'
  refine ⟨r, hr, (fromSpecSectionsIso F hU).hom m, ?_⟩
  have hq : q.hom z' = z := by
    change (ConcreteCategory.hom ((Scheme.Modules.restrictStalkNatIso f y).inv.app F ≫
      (Scheme.Modules.restrictStalkNatIso f y).hom.app F)) z = z
    rw [(Scheme.Modules.restrictStalkNatIso f y).inv_hom_id_app]
    rfl
  have hmq := congrArg q.hom hm
  rwa [fromSpec_stalk_smul_global F hU y r z', fromSpecSectionsIso_germ F hU m y, hq] at hmq

/-- Transport of the statement that an element of a stalk is a multiple of the germ of a
section along an equality of points. -/
lemma germ_multiple_transport {X : Scheme.{u}} (F : X.Modules) (U : X.Opens) {x₁ x₂ : X}
    (he : x₁ = x₂) (hx₁ : x₁ ∈ U) (hx₂ : x₂ ∈ U) (r : Γ(X, U)) (m : Γ(F, U))
    (z : F.presheaf.stalk x₂) :
    letI : Module (X.presheaf.stalk x₁) (F.presheaf.stalk x₁) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x₁
    letI : Module (X.presheaf.stalk x₂) (F.presheaf.stalk x₂) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x₂
    X.presheaf.germ U x₁ hx₁ r • (he ▸ z) = F.presheaf.germ U x₁ hx₁ m →
      X.presheaf.germ U x₂ hx₂ r • z = F.presheaf.germ U x₂ hx₂ m := by
  cases he
  intro h
  simpa using h

/-- **The stalk is a localization.** For a quasi-coherent module on a scheme, the germ map at a
point of an affine open exhibits the stalk as the localization of the module of sections at the
corresponding prime. -/
lemma affineGerm_isLocalized {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (U : X.Opens) (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) :
    letI := affineStalkModule F U x hx
    IsLocalizedModule (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl (affineGerm F U x hx) := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  let := affineStalkModule F U x hx
  refine ⟨affineGerm_map_units F U hU x hx, fun z => ?_,
    fun hab => affineGerm_exists_of_eq F U hU x hx hab⟩
  let y := hU.primeIdealOf ⟨x, hx⟩
  have hy : hU.fromSpec y = x := hU.fromSpec_primeIdealOf ⟨x, hx⟩
  obtain ⟨r, hr, m, hm⟩ := affine_exists_global_multiple F U hU y (hy ▸ z)
  refine ⟨⟨m, ⟨r, by simpa [y] using hr⟩⟩, ?_⟩
  change (X.presheaf.germ U x hx).hom r • z = F.presheaf.germ U x hx m
  exact germ_multiple_transport F U hy (hU.isoSpec.inv y).2 hx r m z hm

/-- The global sections of the restriction of `F` along `IsAffineOpen.fromSpec`, as a
`Γ(X, U)`-module, are the sections of `F` over `U`. -/
noncomputable def fromSpecSectionsLinearEquiv {X : Scheme.{u}} (F : X.Modules) {U : X.Opens}
    (hU : IsAffineOpen U) :
    Γ(F.restrict hU.fromSpec, ⊤) ≃ₗ[Γ(X, U)] Γ(F, U) :=
  let e := fromSpecSectionsIso F hU
  { toEquiv := Equiv.ofBijective (ConcreteCategory.hom e.hom)
      (ConcreteCategory.bijective_of_isIso e.hom)
    map_add' := by simp [e]
    map_smul' := fromSpecSectionsIso_smul F hU }

end AlgebraicGeometry
