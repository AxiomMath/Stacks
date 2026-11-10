module

public import Mathlib.Algebra.Polynomial.Eval.Coeff
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.RingTheory.IntegralClosure.Algebra.Basic
public import Mathlib.RingTheory.Localization.Integral
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Properties.QuasicoherentAlgebra

/-!
# Integral closure of the structure sheaf in a quasi-coherent algebra

Let `A` be a sheaf of commutative `𝒪_X`-algebras on a scheme `X`. The sections of `A` over an
open `U` whose germ at every point `x` of `U` is integral over the local ring `𝒪_{X,x}` form a
subsheaf of `𝒪_X`-algebras, the integral closure of the structure sheaf in `A`. When `A` is
quasi-coherent so is this subalgebra, its stalk at `x` is the integral closure of `𝒪_{X,x}` in
the stalk `A_x`, and its sections over an affine open `U` form the integral closure of
`𝒪_X(U)` in `A(U)`.

## Main definitions

* `AlgebraicGeometry.Scheme.QuasicoherentAlgebra.integralSectionsSubring` is the subring of
  sections over an open whose germs are everywhere integral over the local rings.
* `AlgebraicGeometry.Scheme.QuasicoherentAlgebra.integralClosureAlgebra` is the resulting
  sheaf of `𝒪_X`-algebras, and `integralClosureAlgebraι` its inclusion into the ambient algebra.

## Main results

* `AlgebraicGeometry.Scheme.QuasicoherentAlgebra.mem_range_integralClosureAlgebraι_app_iff`:
  the sections of the subalgebra over `U` are exactly those sections of `A` all of whose germs
  are integral over the corresponding local rings.
* `AlgebraicGeometry.Scheme.QuasicoherentAlgebra.isQuasicoherent_integralClosureAlgebra`: the
  subalgebra is quasi-coherent as soon as the ambient algebra is.
* `AlgebraicGeometry.Scheme.QuasicoherentAlgebra.range_stalkFunctor_map_integralClosureAlgebraι`:
  the stalk at `x` is the integral closure of `𝒪_{X,x}` in the stalk of `A`.
* `AlgebraicGeometry.Scheme.QuasicoherentAlgebra.range_integralClosureAlgebraι_app_of_isAffineOpen`
  identifies the sections over an affine open `U` with the integral closure of `𝒪_X(U)` in
  `A(U)`.

## Implementation notes

A sheaf of `𝒪_X`-algebras is an object of `Under X.sheaf`, so the subalgebra is built as the
sheaf of integral sections together with its structural map from `𝒪_X`, and the inclusion is a
morphism in `Under X.sheaf`, monomorphic because it is injective on sections. The stalk and
affine-section statements identify the ranges of the induced injective ring maps with
`integralClosure`, which is the sense in which the source writes `A'_x ⊆ A_x` and
`A'(U) ⊆ A(U)`.

Quasi-coherence of the subalgebra is checked on the standard opens of an affine open: the
sections of `A` over `X.basicOpen r` are the localization of the sections over `U` away from
`r`, and integrality of an element of such a localization can be cleared of denominators.

## References

* [Stacks Project, Tag 035F](https://stacks.math.columbia.edu/tag/035F)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace TopologicalSpace.Opens

universe u

namespace AlgebraicGeometry.Scheme.QuasicoherentAlgebra

section
open Scheme.Modules CategoryTheory.Limits

/-- The germ at `x` of a section of `A` over `U` is integral over the local ring of `X` at `x`. -/
def integralAt (X : Scheme.{u}) (A : X.QuasicoherentAlgebra)
     (U : Opens X) (x : X) (hx : x ∈ U)
    (s : A.right.presheaf.obj (.op U)) : Prop :=
  RingHom.IsIntegralElem ((TopCat.Presheaf.stalkFunctor CommRingCat x).map A.hom.hom).hom
    (A.right.presheaf.germ U x hx s)


private lemma isLocalizedModule_basicOpen_iff
    {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) :
    letI : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    letI : Module Γ(X, U) Γ(M, X.basicOpen r) :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r))
    IsLocalizedModule.Away r (basicOpenSectionMap M r) ↔
      IsLocalizedModule.Away r (((modulesSpecToSheaf.obj (M.restrict hU.fromSpec)).obj.map
        (PrimeSpectrum.basicOpen r).leTop.op).hom) := by
  let N := M.restrict hU.fromSpec
  let Q := modulesSpecToSheaf.obj N
  have hImage : U = hU.fromSpec ''ᵁ ⊤ := by
    rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec]
  let eTopAb : Γ(N, ⊤) ≅ Γ(M, U) :=
    M.restrictAppIso hU.fromSpec ⊤ ≪≫
      M.presheaf.mapIso (eqToIso hImage).op
  let eTop0 : Q.presheaf.obj (.op ⊤) ≃+ Γ(M, U) :=
    eTopAb.addCommGroupIsoToAddEquiv
  let eRing : Γ(X, hU.fromSpec ''ᵁ ⊤) ≅ Γ(X, U) :=
    X.presheaf.mapIso (eqToIso hImage).op
  have hR (a : Γ(X, U)) :
      eRing.hom ((hU.fromSpec.appIso ⊤).inv ((Scheme.ΓSpecIso Γ(X, U)).inv a)) = a := by
    have hAEq : eRing.hom ≫ (Scheme.ΓSpecIso Γ(X, U)).inv =
        (hU.fromSpec.appIso ⊤).hom := by
      simp only [eRing, Functor.mapIso_hom, Iso.op_hom, Scheme.Hom.appIso_hom']
      have hAppLE : hU.fromSpec.appLE U ⊤ (by simp [hU.fromSpec_preimage_self]) =
          (Scheme.ΓSpecIso Γ(X, U)).inv := by
        simp only [Scheme.Hom.appLE, hU.fromSpec_app_self, Category.assoc,
          ← Functor.map_comp]
        simp
      rw [← hAppLE]
      simpa only [eqToIso.hom] using
        (hU.fromSpec.map_appLE' (V := ⊤) (by simp) hImage)
    have hAEq' : eRing.hom =
        (hU.fromSpec.appIso ⊤).hom ≫ (Scheme.ΓSpecIso Γ(X, U)).hom := by
      rw [← hAEq, Category.assoc, Iso.inv_hom_id, Category.comp_id]
    simp only [hAEq', ConcreteCategory.comp_apply, Iso.inv_hom_id_apply]
  have htop (a : Γ(X, U)) (m : Γ(N, ⊤)) :
      eTop0 (a • m) = a • eTop0 m := by
    change eTopAb.hom (a • m) = a • eTopAb.hom m
    rw [Scheme.Modules.smul_Spec_def]
    have hres : (Spec Γ(X, U)).presheaf.map (⊤ : (Spec Γ(X, U)).Opens).leTop.op = 𝟙 _ := by rfl
    rw [hres]
    simp only [CategoryTheory.id_apply]
    simp only [eTopAb, Iso.trans_hom, ConcreteCategory.comp_apply]
    rw [Scheme.Modules.smul_restrictAppIso_hom_apply]
    simp only [Functor.mapIso_hom, Iso.op_hom] at *
    rw [M.map_smul]
    congr 1
    exact hR a
  let eTop : Γ(N, ⊤) ≃ₗ[Γ(X, U)] Γ(M, U) :=
    { eTop0 with map_smul' := htop }
  have hBasicImage : X.basicOpen r =
      hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen r :=
    (hU.fromSpec_image_basicOpen r).symm
  let eBasicAb : Γ(N, PrimeSpectrum.basicOpen r) ≅ Γ(M, X.basicOpen r) :=
    M.restrictAppIso hU.fromSpec (PrimeSpectrum.basicOpen r) ≪≫
      M.presheaf.mapIso (eqToIso hBasicImage).op
  let eBasic0 : Γ(N, PrimeSpectrum.basicOpen r) ≃+
      Γ(M, X.basicOpen r) := eBasicAb.addCommGroupIsoToAddEquiv
  let eRingBasic : Γ(X, hU.fromSpec ''ᵁ PrimeSpectrum.basicOpen r) ≅
      Γ(X, X.basicOpen r) :=
    X.presheaf.mapIso (eqToIso hBasicImage).op
  have hRBasic (a : Γ(X, U)) :
      eRingBasic.hom ((hU.fromSpec.appIso (PrimeSpectrum.basicOpen r)).inv
        ((Spec Γ(X, U)).presheaf.map (PrimeSpectrum.basicOpen r).leTop.op
          ((Scheme.ΓSpecIso Γ(X, U)).inv a))) =
      X.presheaf.map (homOfLE (X.basicOpen_le r)).op a := by
    have hNatRing :
        (Spec Γ(X, U)).presheaf.map (PrimeSpectrum.basicOpen r).leTop.op ≫
            (hU.fromSpec.appIso (PrimeSpectrum.basicOpen r)).inv ≫ eRingBasic.hom =
          (hU.fromSpec.appIso ⊤).inv ≫ eRing.hom ≫
            X.presheaf.map (homOfLE (X.basicOpen_le r)).op := by
      have hNat0 := hU.fromSpec.appIso_inv_naturality
        (i := ((PrimeSpectrum.basicOpen r : (Spec Γ(X, U)).Opens).leTop).op)
      have hEq :
          X.presheaf.map ((hU.fromSpec.opensFunctor).op.map
              (PrimeSpectrum.basicOpen r).leTop.op) ≫ eRingBasic.hom =
            eRing.hom ≫ X.presheaf.map (homOfLE (X.basicOpen_le r)).op := by
        simp only [eRingBasic, eRing, Functor.mapIso_hom, Iso.op_hom]
        rw [← Functor.map_comp, ← Functor.map_comp]
        rfl
      calc
        _ = ((Spec Γ(X, U)).presheaf.map (PrimeSpectrum.basicOpen r).leTop.op ≫
              (hU.fromSpec.appIso (PrimeSpectrum.basicOpen r)).inv) ≫ eRingBasic.hom := by
                rw [Category.assoc]
        _ = ((hU.fromSpec.appIso ⊤).inv ≫
              X.presheaf.map ((hU.fromSpec.opensFunctor).op.map
                (PrimeSpectrum.basicOpen r).leTop.op)) ≫ eRingBasic.hom :=
              congrArg (fun φ => φ ≫ eRingBasic.hom) hNat0
        _ = _ := by rw [Category.assoc, hEq, ← Category.assoc]
    have hEval := congrArg (fun φ => φ ((Scheme.ΓSpecIso Γ(X, U)).inv a)) hNatRing
    simp only [ConcreteCategory.comp_apply, hR] at hEval
    exact hEval
  let : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
  let : Module Γ(X, U) Γ(M, X.basicOpen r) :=
    Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r))
  let : Module Γ(Spec Γ(X, U), PrimeSpectrum.basicOpen r)
      Γ(N, PrimeSpectrum.basicOpen r) :=
    (N.val.obj (.op (PrimeSpectrum.basicOpen r))).isModule
  let : Module Γ(X, U) Γ(N, PrimeSpectrum.basicOpen r) :=
    Module.compHom _
      (((Spec Γ(X, U)).presheaf.map
        (PrimeSpectrum.basicOpen r).leTop.op).hom.comp
        (Scheme.ΓSpecIso Γ(X, U)).inv.hom)
  have hbasic (a : Γ(X, U)) (m : Γ(N, PrimeSpectrum.basicOpen r)) :
      eBasic0 (a • m) = a • eBasic0 m := by
    change eBasicAb.hom (a • m) = a • eBasicAb.hom m
    change eBasicAb.hom
      (((Spec Γ(X, U)).presheaf.map (PrimeSpectrum.basicOpen r).leTop.op
        ((Scheme.ΓSpecIso Γ(X, U)).inv a)) • m) = a • eBasicAb.hom m
    simp only [eBasicAb, Iso.trans_hom, ConcreteCategory.comp_apply]
    have hsmul := Scheme.Modules.smul_restrictAppIso_hom_apply hU.fromSpec M
      (PrimeSpectrum.basicOpen r)
      ((Spec Γ(X, U)).presheaf.map (PrimeSpectrum.basicOpen r).leTop.op
        ((Scheme.ΓSpecIso Γ(X, U)).inv a)) m
    rw [hsmul]
    simp only [Functor.mapIso_hom, Iso.op_hom]
    rw [M.map_smul]
    congr 1
    exact hRBasic a
  let eBasic : Γ(N, PrimeSpectrum.basicOpen r) ≃ₗ[Γ(X, U)]
      Γ(M, X.basicOpen r) := { eBasic0 with map_smul' := hbasic }
  have hSquare (m : Γ(N, ⊤)) :
      eBasic ((N.presheaf.map (PrimeSpectrum.basicOpen r).leTop.op) m) =
        (M.presheaf.map (homOfLE (X.basicOpen_le r)).op) (eTop m) := by
    have hNat0 := M.map_restrictAppIso_hom (f := hU.fromSpec)
      ((PrimeSpectrum.basicOpen r : (Spec Γ(X, U)).Opens).leTop.op)
    have hEq :
        M.presheaf.map
            ((homOfLE (hU.fromSpec.image_mono
              (show PrimeSpectrum.basicOpen r ≤ (⊤ : (Spec Γ(X, U)).Opens) from le_top))).op) ≫
          (M.presheaf.mapIso (eqToIso hBasicImage).op).hom =
        (M.presheaf.mapIso (eqToIso hImage).op).hom ≫
          M.presheaf.map (homOfLE (X.basicOpen_le r)).op := by
      simp only [Functor.mapIso_hom, Iso.op_hom]
      rw [← Functor.map_comp, ← Functor.map_comp]
      rfl
    have hNatElem := congrArg (fun φ => φ m) hNat0
    simp only [ConcreteCategory.comp_apply] at hNatElem
    have hEqElem := congrArg (fun φ => φ ((M.restrictAppIso hU.fromSpec ⊤).hom m)) hEq
    simp only [ConcreteCategory.comp_apply] at hEqElem
    change eBasicAb.hom ((N.presheaf.map (PrimeSpectrum.basicOpen r).leTop.op) m) =
      (M.presheaf.map (homOfLE (X.basicOpen_le r)).op) (eTopAb.hom m)
    simp only [eBasicAb, eTopAb, Iso.trans_hom, ConcreteCategory.comp_apply]
    rw [hNatElem]
    exact hEqElem
  let ψ := ((modulesSpecToSheaf.obj N).obj.map
    ((PrimeSpectrum.basicOpen r : (Spec Γ(X, U)).Opens).leTop.op)).hom
  let φ : Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen r) := by
    refine { (M.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom with
      map_smul' := ?_ }
    intro a m; exact M.map_smul (homOfLE (X.basicOpen_le r)) a m
  have hψ (m : Γ(N, ⊤)) : ψ m =
      (N.presheaf.map (PrimeSpectrum.basicOpen r).leTop.op) m := rfl
  have hφ : φ = eBasic.toLinearMap ∘ₗ ψ ∘ₗ eTop.symm.toLinearMap := by
    ext m
    have := hSquare (eTop.symm m)
    change (M.presheaf.map (homOfLE (X.basicOpen_le r)).op) m =
      eBasic (ψ (eTop.symm m))
    rw [hψ]
    simpa only [LinearEquiv.apply_symm_apply] using this.symm
  change IsLocalizedModule.Away r φ ↔ IsLocalizedModule.Away r ψ
  rw [hφ]
  exact (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers r)
    (f := ψ ∘ₗ eTop.symm.toLinearMap) eBasic.toLinearMap eBasic.bijective).trans
      (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers r)
        (f := ψ) eTop.symm.toLinearMap eTop.symm.bijective)

private lemma isLocalizedModule_basicOpenSectionMap
    {X : Scheme.{u}} (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (r : Γ(X, U)) :
    letI : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
    letI : Module Γ(X, U) Γ(M, X.basicOpen r) :=
      Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r))
    IsLocalizedModule.Away r (basicOpenSectionMap M r) :=
  (isLocalizedModule_basicOpen_iff M hU r).mpr
    ((isIso_fromTildeΓ_iff_isLocalizing (M.restrict hU.fromSpec)).mp inferInstance r)

private theorem isLocalization_algebraSections_basicOpen (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra)
    [((underlyingModule A)).IsQuasicoherent]
    (U : Opens X) (hU : IsAffineOpen U) (f : X.presheaf.obj (.op U)) :
    letI : Algebra (A.right.presheaf.obj (.op U))
        (A.right.presheaf.obj (.op (X.basicOpen f))) :=
      (A.right.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
    IsLocalization
      (Submonoid.map (A.hom.hom.app (.op U)).hom (Submonoid.powers f))
      (A.right.presheaf.obj (.op (X.basicOpen f))) := by
  let M := underlyingModule A
  let R := X.presheaf.obj (.op U)
  let S := A.right.presheaf.obj (.op U)
  let T := A.right.presheaf.obj (.op (X.basicOpen f))
  let ρ := (A.right.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let α := (A.hom.hom.app (.op U)).hom
  let β := (A.hom.hom.app (.op (X.basicOpen f))).hom
  let γ := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let R' := X.presheaf.obj (.op (X.basicOpen f))
  let N := Γ(M, X.basicOpen f)
  let : Algebra R S := (A.hom.hom.app (.op U)).hom.toAlgebra
  let : Algebra S T := ρ.toAlgebra
  let : Algebra R R' :=
    (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom.toAlgebra
  let : Algebra R' T := (A.hom.hom.app (.op (X.basicOpen f))).hom.toAlgebra
  let : Module R' N := inferInstance
  let : Module R N := Module.compHom N γ
  let : Algebra R T := (β.comp γ).toAlgebra
  have hcompat : ρ.comp α = β.comp γ :=
    RingHom.ext fun r => congrArg (fun q => q r) (congrArg CommRingCat.Hom.hom
      (A.hom.hom.naturality (homOfLE (X.basicOpen_le f)).op)).symm
  let : IsScalarTower R R' T := IsScalarTower.of_algebraMap_eq fun r => rfl
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (fun q => q r) hcompat.symm
  have hloc : IsLocalizedModule (Submonoid.powers f)
      (basicOpenSectionMap M f) :=
    isLocalizedModule_basicOpenSectionMap M hU f
  have hloc' : IsLocalizedModule (Submonoid.powers f)
      (IsScalarTower.toAlgHom R S T).toLinearMap := by
    convert! hloc using 1
  exact (isLocalizedModule_iff_isLocalization (S := Submonoid.powers f)
    (R := R) (A := S) (Aₛ := T)).mp hloc'

/-- The subring of sections of `A` over `U` whose germ at every point of `U` is integral over
the local ring of `X` there. -/
def integralSectionsSubring (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra) (U : Opens X) :
    Subring (A.right.presheaf.obj (.op U)) := by
  classical
  let carrier : Set (A.right.presheaf.obj (.op U)) :=
    {s | ∀ (x : X), ∀ (hx : x ∈ U), integralAt X A U x hx s}
  exact {
    carrier := carrier
    zero_mem' := by
      change ∀ x hx, integralAt X A U x hx 0
      intro x hx
      change RingHom.IsIntegralElem _ _
      rw [map_zero]
      exact RingHom.isIntegralElem_zero _
    one_mem' := by
      change ∀ x hx, integralAt X A U x hx 1
      intro x hx
      change RingHom.IsIntegralElem _ _
      rw [map_one]
      exact RingHom.isIntegralElem_one _
    add_mem' := by
      intro s t hs ht
      change ∀ x hx, integralAt X A U x hx (s + t)
      intro x hx
      change RingHom.IsIntegralElem _ _
      rw [map_add]
      exact RingHom.IsIntegralElem.add _ (hs x hx) (ht x hx)
    mul_mem' := by
      intro s t hs ht
      change ∀ x hx, integralAt X A U x hx (s * t)
      intro x hx
      change RingHom.IsIntegralElem _ _
      rw [map_mul]
      exact RingHom.IsIntegralElem.mul _ (hs x hx) (ht x hx)
    neg_mem' := by
      intro s hs
      change ∀ x hx, integralAt X A U x hx (-s)
      intro x hx
      change RingHom.IsIntegralElem _ _
      rw [map_neg]
      exact RingHom.IsIntegralElem.neg _ (hs x hx)
  }

/-- Restricting a section with everywhere integral germs to a smaller open keeps that property. -/
theorem integralSectionsSubring_map_le (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra)
    {U V : Opens X} (h : U ≤ V) :
    integralSectionsSubring X A V ≤
      (integralSectionsSubring X A U).comap (A.right.presheaf.map (homOfLE h).op).hom := by
  intro s hs
  change ∀ (x : X) (hx : x ∈ U),
    integralAt X A U x hx ((A.right.presheaf.map (homOfLE h).op).hom s)
  change ∀ (x : X) (hx : x ∈ V), integralAt X A V x hx s at hs
  intro x hx
  dsimp [integralAt]
  rw [← ConcreteCategory.comp_apply, A.right.presheaf.germ_res (homOfLE h) x hx]
  exact hs x (h hx)

/-- A commuting square of ring maps carries `eval₂` of a polynomial to `eval₂` of its image. -/
private theorem map_eval₂_of_commutes {R S T V : Type*}
    [CommSemiring R] [CommSemiring S] [CommSemiring T] [CommSemiring V]
    {a : R →+* S} {b : T →+* V} {f : R →+* T} {g : S →+* V} (h : g.comp a = b.comp f)
    (s : S) (p : Polynomial R) : g (p.eval₂ a s) = (p.map f).eval₂ b (g s) := by
  rw [Polynomial.hom_eval₂, h, Polynomial.eval₂_map]

/-- A commuting square of ring maps carries integral elements to integral elements. -/
private lemma isIntegral_map_of_commutes {R S T V : Type*}
    [CommRing R] [CommRing S] [CommRing T] [CommRing V]
    {a : R →+* S} {b : T →+* V} {f : R →+* T} {g : S →+* V}
    (h : g.comp a = b.comp f) {s : S} (hs : a.IsIntegralElem s) :
    b.IsIntegralElem (g s) := by
  obtain ⟨p, hp, he⟩ := hs
  exact ⟨p.map f, hp.map f, by rw [← map_eval₂_of_commutes h, he, map_zero]⟩

/-- Sections with the same germ at `x` agree on every open below a common neighbourhood of `x`. -/
private lemma exists_map_eq_of_germ_eq {X : Scheme.{u}} (F : TopCat.Presheaf CommRingCat.{u} X)
    {x : X} {U V : Opens X} (hU : x ∈ U) (hV : x ∈ V) (s : F.obj (.op U)) (t : F.obj (.op V))
    (h : F.germ U x hU s = F.germ V x hV t) :
    ∃ (W : Opens X) (_ : x ∈ W) (hWU : W ≤ U) (hWV : W ≤ V), ∀ (O : Opens X) (hO : O ≤ W),
      F.map (homOfLE (hO.trans hWU)).op s = F.map (homOfLE (hO.trans hWV)).op t := by
  obtain ⟨W, hxW, i, j, e⟩ := F.germ_eq x hU hV s t h
  refine ⟨W, hxW, i.le, j.le, fun O hO => ?_⟩
  simpa only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp,
    Subsingleton.elim (homOfLE hO ≫ i) (homOfLE (hO.trans i.le)),
    Subsingleton.elim (homOfLE hO ≫ j) (homOfLE (hO.trans j.le))] using
    congrArg (F.map (homOfLE hO).op) e

/-- Taking germs commutes with the structure map `𝒪_X → A` and the induced map on stalks. -/
private lemma germ_comp_app_eq {X : Scheme.{u}} (A : X.QuasicoherentAlgebra) (U : Opens X) (x : X)
    (hx : x ∈ U) :
    (A.right.presheaf.germ U x hx).hom.comp (A.hom.hom.app (.op U)).hom =
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map A.hom.hom).hom.comp
        (X.presheaf.germ U x hx).hom :=
  RingHom.ext fun t => (TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx A.hom.hom t).symm

private theorem exists_integral_section_near (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra) (x : X)
    (y : A.right.presheaf.stalk x)
    (hy : RingHom.IsIntegralElem
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map A.hom.hom).hom y) :
    ∃ (U : Opens X) (hx : x ∈ U) (s : A.right.presheaf.obj (.op U)),
      A.right.presheaf.germ U x hx s = y ∧ s ∈ integralSectionsSubring X A U ∧
        RingHom.IsIntegralElem (A.hom.hom.app (.op U)).hom s := by
  classical
  obtain ⟨p, hp, hpy⟩ := hy
  obtain ⟨U₀, hx₀, s₀, hs₀⟩ := A.right.presheaf.exists_germ_eq y
  choose V hVU hxV c hc using fun i : ℕ => X.presheaf.exists_le_germ_eq (p.coeff i) hx₀
  let W : Opens X := U₀ ⊓ p.support.inf V
  have hxInf (s : Finset ℕ) : x ∈ s.inf V := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
      simp [hxV i, ih]
  have hxW : x ∈ W := by
    change x ∈ U₀ ∧ x ∈ p.support.inf V
    exact ⟨hx₀, hxInf p.support⟩
  have hWU₀ : W ≤ U₀ := inf_le_left
  have hWVi (i : ℕ) (hi : i ∈ p.support) : W ≤ V i :=
    (inf_le_right.trans (Finset.inf_le hi))
  let coeff : ℕ → X.presheaf.obj (.op W) := fun i =>
    if hi : i ∈ p.support then
      (X.presheaf.map (homOfLE (hWVi i hi)).op).hom (c i)
    else 0
  have hcoeffsupport : ∀ i, coeff i ≠ 0 → i ∈ p.support := by
    intro i hi
    by_contra hnot
    change (if h : i ∈ p.support then _ else 0) ≠ 0 at hi
    rw [dite_eq_right hnot] at hi
    exact hi rfl
  let q : Polynomial (X.presheaf.obj (.op W)) :=
    Polynomial.ofFinsupp (AddMonoidAlgebra.ofCoeff (Finsupp.onFinset p.support coeff hcoeffsupport))
  have hq0 (i : ℕ) (hi : i ∉ p.support) : q.coeff i = 0 := by
    change (Finsupp.onFinset p.support coeff hcoeffsupport) i = 0
    rw [Finsupp.onFinset_apply]
    change (if h : i ∈ p.support then _ else 0) = 0
    rw [dite_eq_right hi]
  have hcoeff (i : ℕ) :
      (X.presheaf.germ W x hxW).hom (q.coeff i) = p.coeff i := by
    by_cases hi : i ∈ p.support
    · have hq : q.coeff i = coeff i := by
        simp [q, Polynomial.coeff_ofFinsupp, coeff]
      rw [hq]
      simp only [coeff, dite_eq_left hi]
      rw [← ConcreteCategory.comp_apply, X.presheaf.germ_res (homOfLE (hWVi i hi)) x hxW]
      exact hc i
    · rw [hq0 i hi, map_zero]
      exact (Polynomial.notMem_support_iff.mp hi).symm
  have hmap : Polynomial.map (X.presheaf.germ W x hxW).hom q = p :=
    Polynomial.ext fun i => by rw [Polynomial.coeff_map]; exact hcoeff i
  let sW : A.right.presheaf.obj (.op W) :=
    (A.right.presheaf.map (homOfLE hWU₀).op).hom s₀
  have hsW : A.right.presheaf.germ W x hxW sW = y := by
    calc
      A.right.presheaf.germ W x hxW sW = A.right.presheaf.germ U₀ x hx₀ s₀ := by
        dsimp [sW]
        rw [← ConcreteCategory.comp_apply,
          A.right.presheaf.germ_res (homOfLE hWU₀) x hxW]
      _ = y := hs₀
  let rW : A.right.presheaf.obj (.op W) :=
    Polynomial.eval₂ (A.hom.hom.app (.op W)).hom sW q
  have hvalW : A.right.presheaf.germ W x hxW rW = 0 := by
    have h := map_eval₂_of_commutes (germ_comp_app_eq A W x hxW) sW q
    rw [show (A.right.presheaf.germ W x hxW).hom sW = y from hsW] at h
    exact h.trans ((congrArg (Polynomial.eval₂ _ y) hmap).trans hpy)
  obtain ⟨W₁, hxW₁, h₁, h₁', hrel⟩ :=
    exists_map_eq_of_germ_eq A.right.presheaf hxW hxW rW 0 (by simpa using hvalW)
  have hlead : X.presheaf.germ W x hxW (q.coeff p.natDegree) = 1 := by
    rw [hcoeff, hp.coeff_natDegree]
    rfl
  obtain ⟨W₂, hxW₂, h₂, h₂', hleadEq⟩ :=
    exists_map_eq_of_germ_eq X.presheaf hxW hxW (q.coeff p.natDegree) 1 (by simpa using hlead)
  let U := W₁ ⊓ W₂
  have hxU : x ∈ U := ⟨hxW₁, hxW₂⟩
  let kW : U ⟶ W := homOfLE (inf_le_left.trans h₁)
  let sU : A.right.presheaf.obj (.op U) := (A.right.presheaf.map kW.op).hom sW
  let qU : Polynomial (X.presheaf.obj (.op U)) := Polynomial.map (X.presheaf.map kW.op).hom q
  have hrelU : Polynomial.eval₂ (A.hom.hom.app (.op U)).hom sU qU = 0 := by
    have hnatA : (A.right.presheaf.map kW.op).hom.comp (A.hom.hom.app (.op W)).hom =
        (A.hom.hom.app (.op U)).hom.comp (X.presheaf.map kW.op).hom :=
      RingHom.ext fun t => congrArg (fun g => g t)
        (congrArg CommRingCat.Hom.hom (A.hom.hom.naturality kW.op)).symm
    exact (map_eval₂_of_commutes hnatA sW q).symm.trans (by simpa using hrel U inf_le_left)
  have hleadU : qU.coeff p.natDegree = 1 := by
    rw [Polynomial.coeff_map]
    simpa using hleadEq U inf_le_right
  have hdegU : qU.degree ≤ (p.natDegree : WithBot ℕ) := by
    rw [Polynomial.degree_le_iff_coeff_zero]
    intro i hi
    have hnot : i ∉ p.support := by
      intro his
      have hiNat : p.natDegree < i := WithBot.coe_lt_coe.mp hi
      have := Polynomial.le_natDegree_of_mem_supp i his
      omega
    rw [Polynomial.coeff_map]
    rw [hq0 i hnot]
    simp
  have hmonicU : qU.Monic := Polynomial.monic_of_degree_le _ hdegU hleadU
  have hIntU : RingHom.IsIntegralElem (A.hom.hom.app (.op U)).hom sU :=
    ⟨qU, hmonicU, hrelU⟩
  refine ⟨U, hxU, sU, ?_,
    fun z hz => isIntegral_map_of_commutes (germ_comp_app_eq A U z hz) hIntU, hIntU⟩
  calc
    A.right.presheaf.germ U x hxU sU = A.right.presheaf.germ W x hxW sW := by
      dsimp [sU]
      rw [← ConcreteCategory.comp_apply, A.right.presheaf.germ_res kW x hxU]
    _ = y := hsW

private lemma exists_integral_multiple_of_localization
    {R S Rf Sf : Type*} [CommRing R] [CommRing S] [CommRing Rf] [CommRing Sf]
    [Algebra R S] [Algebra R Rf] [Algebra S Sf] [Algebra Rf Sf] [Algebra R Sf]
    [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
    (M : Submonoid R) [IsLocalization M Rf]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sf]
    (x : S) (hx : IsIntegral Rf (algebraMap S Sf x)) :
    ∃ m ∈ M, IsIntegral R (m • x) := by
  obtain ⟨m, hm⟩ := IsIntegral.exists_multiple_integral_of_isLocalization M _ hx
  have he : m • algebraMap S Sf x = algebraMap S Sf ((m : R) • x) := by
    simp only [Submonoid.smul_def, Algebra.smul_def, map_mul,
      ← IsScalarTower.algebraMap_apply]
  rw [he] at hm
  obtain ⟨n, hn, hnx⟩ := IsLocalization.exists_isIntegral_smul_of_isIntegral_map M hm
  exact ⟨n * m, M.mul_mem hn m.property, by simpa only [mul_smul] using hnx⟩

private lemma exists_integral_numerator
    {R S Rf Sf : Type*} [CommRing R] [CommRing S] [CommRing Rf] [CommRing Sf]
    [Algebra R S] [Algebra R Rf] [Algebra S Sf] [Algebra Rf Sf] [Algebra R Sf]
    [IsScalarTower R S Sf] [IsScalarTower R Rf Sf]
    (M : Submonoid R) [IsLocalization M Rf]
    [IsLocalization (Algebra.algebraMapSubmonoid S M) Sf]
    (y : Sf) (hy : IsIntegral Rf y) :
    ∃ (x : S) (_ : IsIntegral R x) (m : M), m • y = algebraMap S Sf x := by
  obtain ⟨⟨x, _, m, hm, rfl⟩, e⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid S M) y
  simp only [← IsScalarTower.algebraMap_apply] at e
  have hx : IsIntegral Rf (algebraMap S Sf x) := by
    rw [← e]
    apply hy.mul
    rw [IsScalarTower.algebraMap_apply R Rf Sf]
    exact isIntegral_algebraMap
  obtain ⟨n, hn, hnx⟩ := exists_integral_multiple_of_localization (Rf := Rf) M x hx
  refine ⟨n • x, hnx, ⟨n * m, M.mul_mem hn hm⟩, ?_⟩
  simp only [Submonoid.smul_def, Algebra.smul_def, map_mul,
    ← IsScalarTower.algebraMap_apply, ← e]
  ring

private lemma integral_restriction_basicOpen_multiple (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra)
    [(underlyingModule A).IsQuasicoherent]
    (U : Opens X) (hU : IsAffineOpen U) (f : X.presheaf.obj (.op U))
    (s : A.right.presheaf.obj (.op U))
    (hs : (A.hom.hom.app (.op (X.basicOpen f))).hom.IsIntegralElem
      (A.right.presheaf.map (homOfLE (X.basicOpen_le f)).op s)) :
    ∃ n : ℕ, (A.hom.hom.app (.op U)).hom.IsIntegralElem
      ((A.hom.hom.app (.op U)).hom (f ^ n) * s) := by
  let R := X.presheaf.obj (.op U)
  let S := A.right.presheaf.obj (.op U)
  let Rf := X.presheaf.obj (.op (X.basicOpen f))
  let Sf := A.right.presheaf.obj (.op (X.basicOpen f))
  let ρ := (A.right.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let α := (A.hom.hom.app (.op U)).hom
  let β := (A.hom.hom.app (.op (X.basicOpen f))).hom
  let γ := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let : Algebra R S := α.toAlgebra
  let : Algebra S Sf := ρ.toAlgebra
  let : Algebra R Rf := γ.toAlgebra
  let : Algebra Rf Sf := β.toAlgebra
  let : Algebra R Sf := (β.comp γ).toAlgebra
  let : IsScalarTower R Rf Sf := IsScalarTower.of_algebraMap_eq fun r => rfl
  let : IsScalarTower R S Sf := IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (fun q => q r) (congrArg CommRingCat.Hom.hom
      (A.hom.hom.naturality (homOfLE (X.basicOpen_le f)).op))
  let : IsLocalization (Submonoid.powers f) Rf := hU.isLocalization_basicOpen f
  let : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) Sf :=
    isLocalization_algebraSections_basicOpen X A U hU f
  obtain ⟨m, ⟨n, rfl⟩, hm⟩ :=
    exists_integral_multiple_of_localization (Rf := Rf) (Submonoid.powers f) s (by
      exact hs)
  exact ⟨n, hm⟩

private lemma integralSectionsSubring_mem_iff (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra)
    [(underlyingModule A).IsQuasicoherent]
    (U : Opens X) (hU : IsAffineOpen U) (s : A.right.presheaf.obj (.op U)) :
    s ∈ integralSectionsSubring X A U ↔ (A.hom.hom.app (.op U)).hom.IsIntegralElem s := by
  constructor
  · intro hs
    let R := X.presheaf.obj (.op U)
    let S := A.right.presheaf.obj (.op U)
    let : Algebra R S := (A.hom.hom.app (.op U)).hom.toAlgebra
    let D : Set R := {f | (A.hom.hom.app (.op (X.basicOpen f))).hom.IsIntegralElem
      (A.right.presheaf.map (homOfLE (X.basicOpen_le f)).op s)}
    have hD : Ideal.span D = ⊤ := by
      apply hU.self_le_iSup_basicOpen_iff.mp
      intro x hx
      obtain ⟨V, hxV, t, ht, _, hti⟩ :=
        exists_integral_section_near X A x (A.right.presheaf.germ U x hx s) (hs x hx)
      obtain ⟨W, hxW, hWV, hWU, he⟩ := exists_map_eq_of_germ_eq A.right.presheaf hxV hx t s ht
      obtain ⟨f, hfW, hxf⟩ := hU.exists_basicOpen_le ⟨x, hxW⟩ hx
      have hi : (A.hom.hom.app (.op (X.basicOpen f))).hom.IsIntegralElem
          (A.right.presheaf.map (homOfLE (hfW.trans hWV)).op t) :=
        isIntegral_map_of_commutes
          (congrArg CommRingCat.Hom.hom
            (A.hom.hom.naturality (homOfLE (hfW.trans hWV)).op)).symm hti
      rw [he (X.basicOpen f) hfW] at hi
      exact Opens.mem_iSup.mpr ⟨⟨f, hi⟩, hxf⟩
    exact (integralClosure R S).toSubmodule.mem_of_span_eq_top_of_smul_pow_mem D hD s
      (fun f => integral_restriction_basicOpen_multiple X A U hU f s f.property)
  · intro hs x hx
    exact isIntegral_map_of_commutes (germ_comp_app_eq A U x hx) hs

/-- The presheaf of sections of `A` whose germs are everywhere integral over the local rings. -/
def integralSectionsPresheaf (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra) :
    TopCat.Presheaf CommRingCat.{u} X where
  obj U := CommRingCat.of (integralSectionsSubring X A U.unop)
  map {U V} i := by
    let K := integralSectionsSubring X A U.unop
    let L := integralSectionsSubring X A V.unop
    let f := A.right.presheaf.map i
    have hKL : K ≤ L.comap f.hom :=
      integralSectionsSubring_map_le X A i.unop.le
    exact CommRingCat.ofHom <|
      (f.hom.comp K.subtype).codRestrict L (fun x => hKL x.2)
  map_id U := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    apply Subtype.ext
    simp
  map_comp {U V W} i j := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    apply Subtype.ext
    change (A.right.presheaf.map (i ≫ j)).hom s.1 =
      (A.right.presheaf.map j).hom ((A.right.presheaf.map i).hom s.1)
    rw [A.right.presheaf.map_comp]
    simp only [ConcreteCategory.comp_apply]

/-- The inclusion of the presheaf of integral sections into the presheaf underlying `A`. -/
def integralSectionsInclusion (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra) :
    integralSectionsPresheaf X A ⟶ A.right.presheaf where
  app U := CommRingCat.ofHom (integralSectionsSubring X A U.unop).subtype
  naturality {U V} i := by
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro s
    rfl

/-- Integrality of all germs is a local condition, so the integral sections form a sheaf. -/
@[ega "II 6.3.2" "partial"]
theorem integralSectionsPresheaf_isSheaf (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra) :
    (integralSectionsPresheaf X A).IsSheaf := by
  classical
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).2
  intro ι U sf hsf
  let incl := integralSectionsInclusion X A
  let sfA : ∀ i, A.right.presheaf.obj (op (U i)) := fun i =>
    (incl.app (op (U i))).hom (sf i)
  have hsfA : A.right.presheaf.IsCompatible U sfA := by
    intro i j
    have hi : (incl.app (op (U i ⊓ U j))).hom
        (((integralSectionsPresheaf X A).map (Opens.infLELeft (U i) (U j)).op).hom
          (sf i)) =
        (A.right.presheaf.map (Opens.infLELeft (U i) (U j)).op).hom
          ((incl.app (op (U i))).hom (sf i)) := by
      simpa only [CommRingCat.comp_apply] using
        congrArg (fun g => g (sf i))
          (congrArg CommRingCat.Hom.hom
            (incl.naturality (Opens.infLELeft (U i) (U j)).op))
    have hj : (incl.app (op (U i ⊓ U j))).hom
        (((integralSectionsPresheaf X A).map (Opens.infLERight (U i) (U j)).op).hom
          (sf j)) =
        (A.right.presheaf.map (Opens.infLERight (U i) (U j)).op).hom
          ((incl.app (op (U j))).hom (sf j)) := by
      simpa only [CommRingCat.comp_apply] using
        congrArg (fun g => g (sf j))
          (congrArg CommRingCat.Hom.hom
            (incl.naturality (Opens.infLERight (U i) (U j)).op))
    rw [← hi, ← hj]
    exact congrArg (incl.app (op (U i ⊓ U j))).hom (hsf i j)
  obtain ⟨sA, hsA, hsAuniq⟩ := A.right.existsUnique_gluing U sfA hsfA
  let s : (integralSectionsPresheaf X A).obj (op (iSup U)) := ⟨sA, by
    intro x hx
    obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp hx
    have hi : A.right.presheaf.map (Opens.leSupr U i).op sA = sfA i := hsA i
    change RingHom.IsIntegralElem _ (A.right.presheaf.germ (iSup U) x hx sA)
    have hres : A.right.presheaf.germ (iSup U) x hx sA =
        A.right.presheaf.germ (U i) x hxi
          ((A.right.presheaf.map (Opens.leSupr U i).op).hom sA) := by
      simpa only [CommRingCat.comp_apply] using congrArg (fun f => f sA)
        (A.right.presheaf.germ_res (Opens.leSupr U i) x hxi).symm
    rw [hres, hi]
    change RingHom.IsIntegralElem _
      (A.right.presheaf.germ (U i) x hxi ((incl.app (op (U i))).hom (sf i)))
    exact (sf i).2 x hxi
    ⟩
  refine ⟨s, ?_, ?_⟩
  · exact fun i => Subtype.ext (hsA i)
  · intro t ht
    apply Subtype.ext
    apply hsAuniq
    intro i
    have hi : (incl.app (op (U i))).hom
        (((integralSectionsPresheaf X A).map (Opens.leSupr U i).op).hom t) =
        (A.right.presheaf.map (Opens.leSupr U i).op).hom
          ((incl.app (op (iSup U))).hom t) := by
      simpa only [CommRingCat.comp_apply] using congrArg (fun g => g t)
        (congrArg CommRingCat.Hom.hom
          (incl.naturality (Opens.leSupr U i).op))
    rw [ht i] at hi
    change (A.right.presheaf.map (Opens.leSupr U i).op).hom t.1 = sfA i
    exact hi.symm

/-- The sheaf of sections of `A` whose germs are everywhere integral over the local rings. -/
@[ega "II 6.3.2"]
noncomputable def integralSectionsSheaf (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra) :
    TopCat.Sheaf CommRingCat.{u} X :=
  ⟨integralSectionsPresheaf X A, integralSectionsPresheaf_isSheaf X A⟩

/-- The inclusion of the sheaf of integral sections into `A`. -/
@[ega "II 6.3.2" "special case"]
noncomputable def integralSectionsSheafInclusion (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra) :
    integralSectionsSheaf X A ⟶ A.right where
  hom := integralSectionsInclusion X A

/-- The structure sheaf maps to the sheaf of integral sections, since the germ of a function on
`X` is integral over the local ring it lies in. -/
noncomputable def integralSectionsStructureMap (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra) :
    X.sheaf ⟶ integralSectionsSheaf X A where
  hom := {
    app U := CommRingCat.ofHom <|
      ((A.hom.hom.app U).hom).codRestrict (integralSectionsSubring X A U.unop) (by
        intro s
        change ∀ x hx, integralAt X A U.unop x hx ((A.hom.hom.app U).hom s)
        intro x hx
        change RingHom.IsIntegralElem _ _
        rw [← TopCat.Presheaf.stalkFunctor_map_germ_apply U.unop x hx A.hom.hom s]
        exact RingHom.isIntegralElem_map _)
    naturality {U V} i := by
      apply CommRingCat.hom_ext
      apply RingHom.ext
      intro s
      apply Subtype.ext
      exact congrArg (fun f => f s) (congrArg CommRingCat.Hom.hom (A.hom.hom.naturality i))
  }

private theorem integralSectionsInclusion_mono (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra) :
    Mono (integralSectionsSheafInclusion X A) := by
  apply (Sheaf.Hom.mono_iff_presheaf_mono _ _ _).mpr
  apply (NatTrans.mono_iff_mono_app _).mpr
  intro U
  apply ConcreteCategory.mono_of_injective
  exact fun s t h => Subtype.ext h

private lemma quasicoherent_of_basicOpen_localization {X : Scheme.{u}} (M : X.Modules)
    (h : ∀ (U : X.Opens) (_ : IsAffineOpen U) (r : Γ(X, U)),
      letI : Algebra Γ(X, U) Γ(X, X.basicOpen r) :=
        (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom.toAlgebra
      letI : Module Γ(X, U) Γ(M, X.basicOpen r) :=
        Module.compHom _ (algebraMap Γ(X, U) Γ(X, X.basicOpen r))
      IsLocalizedModule.Away r (basicOpenSectionMap M r)) : M.IsQuasicoherent := by
  obtain ⟨S, hS, hcov⟩ := Opens.isBasis_iff_cover.mp X.isBasis_affineOpens ⊤
  let U : S → X.Opens := fun i => i.1
  have cov : (Opens.grothendieckTopology X).CoversTop U := by
    rw [Opens.coversTop_iff, IsOpenCover]
    exact (sSup_eq_iSup' S).symm.trans hcov.symm
  refine SheafOfModules.QuasicoherentData.isQuasicoherent.{u, u, u, u} (M := M)
    (SheafOfModules.QuasicoherentData.mk (M := M) S U cov (fun i => ?_))
  let hU : IsAffineOpen (U i) := hS i.2
  let N := M.restrict hU.fromSpec
  let fN := N.fromTildeΓ
  have : IsIso fN := (isIso_fromTildeΓ_iff_isLocalizing N).mpr fun r =>
    (isLocalizedModule_basicOpen_iff M hU r).mp (h (U i) hU r)
  let P := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ fN
    ‹IsIso fN›
    (presentationTilde (moduleSpecΓFunctor.obj N) Set.univ (by simp) _
      (Submodule.span_eq _))
  let P' := presentationRestrict hU.isoSpec.hom P
  let isoQ := ((restrictFunctorComp hU.isoSpec.hom hU.fromSpec).symm ≪≫
    restrictFunctorCongr hU.isoSpec_hom_fromSpec).app M
  have : IsIso isoQ.hom := isoQ.isIso_hom
  let Q := @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ isoQ.hom
    ‹IsIso isoQ.hom› P'
  have : ((overEquiv (U i)).inverse).IsLeftAdjoint :=
    (overEquiv (U i)).symm.isLeftAdjoint_functor
  let preserve : PreservesColimitsOfSize.{u, u, u, u, u + 1, u + 1}
      (overEquiv (U i)).inverse := inferInstance
  let Q' := @SheafOfModules.Presentation.map _ _ _ _ _ _ _ _ _ _ _ _ _ Q
    (overEquiv (U i)).inverse preserve
    (Opens.sheafOfModulesEquivOverInverseUnit (U i) X.ringCatSheaf).symm
  exact Q'.ofIsIso (((overEquiv (U i)).inverse.mapIso
    ((overFunctorEquiv (U i)).app M).symm) ≪≫
      ((overEquiv (U i)).unitIso.app (M.over (U i))).symm).hom

private lemma integralSections_quasicoherent (X : Scheme.{u})
    (A : X.QuasicoherentAlgebra)
    [(underlyingModule A).IsQuasicoherent] :
    (underlyingModule (Under.mk (integralSectionsStructureMap X A))).IsQuasicoherent := by
  let M := underlyingModule A
  let N := underlyingModule (Under.mk (integralSectionsStructureMap X A))
  apply quasicoherent_of_basicOpen_localization N
  intro U hU f
  let R := X.presheaf.obj (.op U)
  let S := A.right.presheaf.obj (.op U)
  let Rf := X.presheaf.obj (.op (X.basicOpen f))
  let Sf := A.right.presheaf.obj (.op (X.basicOpen f))
  let ρ := (A.right.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let α := (A.hom.hom.app (.op U)).hom
  let β := (A.hom.hom.app (.op (X.basicOpen f))).hom
  let γ := (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
  let : Algebra R S := α.toAlgebra
  let : Algebra S Sf := ρ.toAlgebra
  let : Algebra R Rf := γ.toAlgebra
  let : Algebra Rf Sf := β.toAlgebra
  let : Algebra R Sf := (β.comp γ).toAlgebra
  let : IsScalarTower R Rf Sf := IsScalarTower.of_algebraMap_eq fun r => rfl
  let : IsScalarTower R S Sf := IsScalarTower.of_algebraMap_eq fun r =>
    congrArg (fun q => q r) (congrArg CommRingCat.Hom.hom
      (A.hom.hom.naturality (homOfLE (X.basicOpen_le f)).op))
  let : IsLocalization (Submonoid.powers f) Rf := hU.isLocalization_basicOpen f
  let : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers f)) Sf :=
    isLocalization_algebraSections_basicOpen X A U hU f
  let : Module R Γ(N, X.basicOpen f) := Module.compHom _ γ
  let : Module R Γ(M, X.basicOpen f) := Module.compHom _ γ
  let := isLocalizedModule_basicOpenSectionMap M hU f
  refine ⟨?_, ?_, ?_⟩
  · intro m
    apply (Module.End.isUnit_iff _).mpr
    change Function.Bijective (fun y : Γ(N, X.basicOpen f) => γ (m : R) • y)
    exact (IsLocalization.map_units (S := Rf) m).smul_bijective
  · intro y
    have hy : IsIntegral Rf y.1 :=
      (integralSectionsSubring_mem_iff X A (X.basicOpen f) (hU.basicOpen f) y.1).mp y.property
    obtain ⟨x, hx, m, hm⟩ := exists_integral_numerator (S := S) (Rf := Rf)
      (Submonoid.powers f) y.1 hy
    exact ⟨(⟨x, (integralSectionsSubring_mem_iff X A U hU x).mpr hx⟩, m), Subtype.ext hm⟩
  · intro y z he
    obtain ⟨m, hm⟩ := IsLocalizedModule.exists_of_eq (S := Submonoid.powers f)
      (f := basicOpenSectionMap M f) (congrArg Subtype.val he)
    exact ⟨m, Subtype.ext hm⟩

end

/-- The integral closure of the structure sheaf in a sheaf of `𝒪_X`-algebras `A`: the sheaf of
sections of `A` whose germs are everywhere integral over the local rings of `X`, with the
`𝒪_X`-algebra structure induced from `A`. -/
@[ega "II 6.3.2" "special case"]
def integralClosureAlgebra {X : Scheme.{u}} (A : X.QuasicoherentAlgebra) :
    X.QuasicoherentAlgebra :=
  Under.mk (integralSectionsStructureMap X A)

/-- The inclusion of the integral closure of the structure sheaf in `A` into `A`, as a morphism
of sheaves of `𝒪_X`-algebras. -/
def integralClosureAlgebraι {X : Scheme.{u}} (A : X.QuasicoherentAlgebra) :
    integralClosureAlgebra A ⟶ A :=
  Under.homMk (integralSectionsSheafInclusion X A) (by
    apply Sheaf.hom_ext
    ext U s
    rfl)

/-- The inclusion of the integral closure of the structure sheaf in `A` is a monomorphism of
sheaves of `𝒪_X`-algebras. -/
instance mono_integralClosureAlgebraι {X : Scheme.{u}} (A : X.QuasicoherentAlgebra) :
    Mono (integralClosureAlgebraι A) :=
  haveI : Mono (integralClosureAlgebraι A).right := integralSectionsInclusion_mono X A
  Under.mono_of_mono_right _

/-- The inclusion of the integral closure of the structure sheaf in `A` is injective on
sections over every open. -/
theorem injective_integralClosureAlgebraι_app {X : Scheme.{u}} (A : X.QuasicoherentAlgebra)
    (U : Opens X) :
    Function.Injective ((integralClosureAlgebraι A).right.hom.app (.op U)) :=
  fun _ _ h => Subtype.ext h

/-- The inclusion of the integral closure of the structure sheaf in `A` is injective on every
stalk, so the stalk of the subalgebra is identified with its image in the stalk of `A`. -/
theorem injective_stalkFunctor_map_integralClosureAlgebraι {X : Scheme.{u}}
    (A : X.QuasicoherentAlgebra) (x : X) :
    Function.Injective ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
      (integralClosureAlgebraι A).right.hom) :=
  TopCat.Presheaf.stalkFunctor_map_injective_of_app_injective
    (fun U => injective_integralClosureAlgebraι_app A U) x

/-- A section of `A` over `U` lies in the integral closure of the structure sheaf exactly when
its germ at every point of `U` is integral over the local ring of `X` at that point. -/
@[stacks 035F "the defining rule"]
theorem mem_range_integralClosureAlgebraι_app_iff {X : Scheme.{u}}
    (A : X.QuasicoherentAlgebra) (U : Opens X) (s : A.right.presheaf.obj (.op U)) :
    s ∈ Set.range ((integralClosureAlgebraι A).right.hom.app (.op U)) ↔
      ∀ (x : X) (hx : x ∈ U),
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).map A.hom.hom).hom.IsIntegralElem
          (A.right.presheaf.germ U x hx s) := by
  change s ∈ Set.range (integralSectionsSubring X A U).subtype ↔ _
  constructor
  · rintro ⟨t, rfl⟩
    exact t.2
  · exact fun hs => ⟨⟨s, hs⟩, rfl⟩

/-- The integral closure of the structure sheaf in a quasi-coherent sheaf of `𝒪_X`-algebras is
itself a quasi-coherent sheaf of `𝒪_X`-algebras. -/
@[stacks 035F "quasi-coherence", ega "II 6.3.4" "quasi-coherence"]
theorem isQuasicoherent_integralClosureAlgebra {X : Scheme.{u}} (A : X.QuasicoherentAlgebra)
    [(underlyingModule A).IsQuasicoherent] :
    (underlyingModule (integralClosureAlgebra A)).IsQuasicoherent :=
  integralSections_quasicoherent X A

/-- The stalk at `x` of the integral closure of the structure sheaf in `A` is the integral
closure of the local ring `𝒪_{X,x}` in the stalk `A_x`. -/
@[stacks 035F "stalks", ega "II 6.3.2" "special case"]
theorem range_stalkFunctor_map_integralClosureAlgebraι {X : Scheme.{u}}
    (A : X.QuasicoherentAlgebra) (x : X) :
    letI : Algebra ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj X.presheaf)
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj A.right.presheaf) :=
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).map A.hom.hom).hom.toAlgebra
    Set.range (((TopCat.Presheaf.stalkFunctor CommRingCat x).map
        (integralClosureAlgebraι A).right.hom).hom) =
      (integralClosure ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj X.presheaf)
        ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj A.right.presheaf) : Set _) := by
  dsimp
  let B := integralSectionsSheaf X A
  let β := ((TopCat.Presheaf.stalkFunctor CommRingCat x).map
    (integralSectionsSheafInclusion X A).hom).hom
  let α := ((TopCat.Presheaf.stalkFunctor CommRingCat x).map A.hom.hom).hom
  let : Algebra ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj X.presheaf)
      ((TopCat.Presheaf.stalkFunctor CommRingCat x).obj A.right.presheaf) := α.toAlgebra
  ext y
  change y ∈ Set.range β ↔ α.IsIntegralElem y
  constructor
  · rintro ⟨b, rfl⟩
    obtain ⟨U, hx, t, ht⟩ := B.presheaf.exists_germ_eq b
    rw [← ht, TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change RingHom.IsIntegralElem α ((A.right.presheaf.germ U x hx).hom t.1)
    exact t.2 x hx
  · intro hy
    obtain ⟨U, hx, s, hs, hsi, _⟩ := exists_integral_section_near X A x y hy
    let t : B.presheaf.obj (.op U) := ⟨s, hsi⟩
    refine ⟨(B.presheaf.germ U x hx).hom t, ?_⟩
    rw [TopCat.Presheaf.stalkFunctor_map_germ_apply]
    change A.right.presheaf.germ U x hx s = y
    exact hs

/-- Over an affine open `U`, the sections of the integral closure of the structure sheaf in a
quasi-coherent `A` form the integral closure of `𝒪_X(U)` in `A(U)`. -/
@[stacks 035F "affine sections", ega "II 6.3.4" "affine sections"]
theorem range_integralClosureAlgebraι_app_of_isAffineOpen {X : Scheme.{u}}
    (A : X.QuasicoherentAlgebra) [(underlyingModule A).IsQuasicoherent]
    (U : Opens X) (hU : IsAffineOpen U) :
    letI : Algebra (X.presheaf.obj (.op U)) (A.right.presheaf.obj (.op U)) :=
      (A.hom.hom.app (.op U)).hom.toAlgebra
    Set.range ((integralClosureAlgebraι A).right.hom.app (.op U)) =
      (integralClosure (X.presheaf.obj (.op U)) (A.right.presheaf.obj (.op U)) : Set _) := by
  ext s
  change s ∈ Set.range (integralSectionsSubring X A U).subtype ↔
    (A.hom.hom.app (.op U)).hom.IsIntegralElem s
  constructor
  · rintro ⟨t, rfl⟩; exact (integralSectionsSubring_mem_iff X A U hU t.1).mp t.2
  · intro hs; exact ⟨⟨s, (integralSectionsSubring_mem_iff X A U hU s).mpr hs⟩, rfl⟩

end AlgebraicGeometry.Scheme.QuasicoherentAlgebra

add_to_stacks 035G AlgebraicGeometry.Scheme.QuasicoherentAlgebra.integralClosureAlgebra

end
