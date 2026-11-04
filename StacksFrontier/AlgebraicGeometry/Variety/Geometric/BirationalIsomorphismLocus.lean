module

public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.AlgebraicGeometry.SpreadingOut
public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.Topology.Maps.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Defs
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalExtension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.LocalUniqueness
public import StacksFrontier.AlgebraicGeometry.Properties.GermInjective
public import StacksFrontier.RingTheory.EssentialFiniteness.ZariskiApplication
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.QuasiFinite.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.OpenImmersionCriterion

/-!
# The isomorphism locus of a proper birational morphism at a normal point

Let `f : Y ⟶ X` be a proper birational morphism from a reduced scheme to a Noetherian scheme,
and let `x` be a point of `X` whose local ring is normal. Then `f` is an isomorphism over a
neighbourhood of `x` as soon as the fibre over `x` is finite, and — more generally — `x` lies
in the maximal open over which `f` is an isomorphism as soon as `f` is quasi-finite at some
point above `x`.

## Main results

* `AlgebraicGeometry.exists_isIso_restrict_of_finite_fiber_of_normal`: a proper birational
  morphism from a reduced scheme is an isomorphism over a neighbourhood of a point with finite
  fibre and normal local ring.
* `AlgebraicGeometry.mem_maximal_isomorphism_open_of_quasiFiniteAt_of_isNormal`: the maximal
  isomorphism open contains a normal point admitting a quasi-finite preimage.
* `AlgebraicGeometry.mem_maximal_isomorphism_open_of_exists_isIso_restrict`: a point admitting
  such an isomorphism neighbourhood belongs to the maximal isomorphism open.

## Implementation notes

The maximal open is expressed as the greatest open `U` for which the restriction `f ∣_ U` is an
isomorphism, and `mem_maximal_isomorphism_open_of_exists_isIso_restrict` is the bridge from the
intrinsic local-neighbourhood form to membership in it. Normality is expressed by the predicate
`IsNormalRing` on the local ring, that is, by every localization at a prime being an integrally
closed domain; for a local ring this is the same as being a normal domain.

For a finite fibre, Zariski's main theorem gives an affine neighbourhood over which `f` is
finite, and on it the sections upstairs form a finite algebra inside the function field which,
by integral closedness, agrees with the base after inverting one element. For a quasi-finite
point the argument is at the level of local rings: quasi-finiteness makes the residue field
extension finite and the closed fibre zero-dimensional, so the stalk map is an isomorphism, and
that isomorphism spreads out to an open neighbourhood.

## References

* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Topology
open scoped TensorProduct

namespace AlgebraicGeometry

universe u

/-- A reduced scheme birational to an integral scheme is integral. -/
theorem integral_of_reduced_birational_to_integral
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsReduced X] [IsIntegral Y]
    (hf : IsBirational f) : IsIntegral X := by
  have hηY : genericPoint Y ∈ genericPoints Y := by
    simp [genericPoints_eq_singleton]
  obtain ⟨η, hη, hmap⟩ := hf.bijOn.surjOn hηY
  have hsingleton : genericPoints X = {η} := by
    ext z
    constructor
    · intro hz
      have hzY := hf.bijOn.mapsTo hz
      have hzy : f z = genericPoint Y := by
        simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using hzY
      exact Set.mem_singleton_iff.mpr (hf.bijOn.injOn hz hη (hzy.trans hmap.symm))
    · intro hz
      simpa only [Set.mem_singleton_iff] using hz ▸ hη
  have hdense : closure ({η} : Set X) = Set.univ := by
    simpa [hsingleton] using (genericPoints.closure (α := X))
  have : IrreducibleSpace X := by
    have hI : IsIrreducible (Set.univ : Set X) := hdense ▸ isIrreducible_singleton.closure
    exact { isPreirreducible_univ := hI.2, toNonempty := ⟨hI.1.some⟩ }
  exact isIntegral_of_irreducibleSpace_of_isReduced X

/-- Generic points lying in the range of an open immersion remain generic in its source. -/
private theorem genericPoints_preimage_of_isOpenImmersion
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i]
    {x : X} (hx : i x ∈ genericPoints Y) : x ∈ genericPoints X := by
  have hmeet : (closure {i x} ∩ Set.range i).Nonempty :=
    ⟨i x, subset_closure (Set.mem_singleton _), ⟨x, rfl⟩⟩
  have hpre : i ⁻¹' closure {i x} ∈ irreducibleComponents X :=
    preimage_mem_irreducibleComponents hx i.isOpenEmbedding hmeet
  change closure {x} ∈ irreducibleComponents X
  rw [i.isOpenEmbedding.closure_eq_preimage_closure_image]
  simpa using hpre

/-- Birationality is preserved by restriction to an open in the target. -/
theorem birational_morphismRestrict
    {X Y : Scheme.{u}} (f : X ⟶ Y) (hf : IsBirational f)
    (U : Y.Opens) : IsBirational (f ∣_ U) := by
  let V := f ⁻¹ᵁ U
  have hcomm : (f ∣_ U) ≫ U.ι = V.ι ≫ f := morphismRestrict_ι f U
  have hmap (z : V) : U.ι ((f ∣_ U) z) = f (V.ι z) := by
    have h := congrArg (fun g : V.toScheme ⟶ Y => g z) hcomm
    change U.ι ((f ∣_ U) z) = f (V.ι z) at h
    exact h
  refine ⟨Set.BijOn.mk ?_ ?_ ?_, ?_⟩
  · intro z hz
    apply genericPoints_preimage_of_isOpenImmersion U.ι
    rw [hmap z]
    exact hf.bijOn.mapsTo (AlgebraicGeometry.genericPoints_map_of_openImmersion V.ι hz)
  · intro z hz z' hz' h
    apply V.ι.isOpenEmbedding.injective
    apply hf.bijOn.injOn
      (AlgebraicGeometry.genericPoints_map_of_openImmersion V.ι hz)
      (AlgebraicGeometry.genericPoints_map_of_openImmersion V.ι hz')
    calc
      f (V.ι z) = U.ι ((f ∣_ U) z) := (hmap z).symm
      _ = U.ι ((f ∣_ U) z') := congrArg U.ι h
      _ = f (V.ι z') := hmap z'
  · intro y hy
    have hy' : U.ι y ∈ genericPoints Y :=
      AlgebraicGeometry.genericPoints_map_of_openImmersion U.ι hy
    obtain ⟨z, hz, hzy⟩ := hf.bijOn.surjOn hy'
    have hzV : z ∈ V := by
      change f z ∈ U
      rw [hzy]
      exact y.2
    let z' : V := ⟨z, hzV⟩
    refine ⟨z', genericPoints_preimage_of_isOpenImmersion V.ι hz, ?_⟩
    apply U.ι.isOpenEmbedding.injective
    simpa only [hmap z', z', Scheme.Opens.ι_apply] using hzy
  · intro z hz
    have hfg : IsIso (f.stalkMap (V.ι z)) :=
      hf.isIso_stalkMap _ (AlgebraicGeometry.genericPoints_map_of_openImmersion V.ι hz)
    exact (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
      (morphismRestrictStalkMap f U z)).mpr hfg

/-- A finite algebra inside the fraction field becomes equal to the base near a normal
localization. -/
@[ega "IV 8.12.12" "special case"]
private theorem exists_localizedModuleMap_bijective_of_finite_of_normal_atPrime
    (R S : Type*) [CommRing R] [IsDomain R] [CommRing S] [IsDomain S]
    [Algebra R S] [IsNoetherianRing R] [Module.Finite R S]
    (p : Ideal R) [p.IsPrime]
    [IsIntegrallyClosed (Localization.AtPrime p)]
    (i : S →ₐ[R] FractionRing R) (hi : Function.Injective i) :
    ∃ r ∉ p, Function.Bijective
      ((LocalizedModule.map (Submonoid.powers r)) (Algebra.linearMap R S)) := by
  classical
  have hRS : Function.Injective (algebraMap R S) := by
    intro a b hab
    apply IsFractionRing.injective R (FractionRing R)
    simpa using congrArg i hab
  let : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hRS
  let M := p.primeCompl
  let T := Localization (Algebra.algebraMapSubmonoid S M)
  let : Algebra (Localization.AtPrime p) T := inferInstance
  let : IsScalarTower R (Localization.AtPrime p) T := inferInstance
  let : Algebra (Localization.AtPrime p) (FractionRing R) := inferInstance
  let : IsScalarTower R (Localization.AtPrime p) (FractionRing R) := inferInstance
  let : IsFractionRing (Localization.AtPrime p) (FractionRing R) := inferInstance
  let : Module.Finite (Localization.AtPrime p) T := inferInstance
  let : Algebra.IsIntegral (Localization.AtPrime p) T := inferInstance
  let : IsDomain T := inferInstance
  have hd : ∀ y : Algebra.algebraMapSubmonoid S M, IsUnit (i y) := by
    intro y
    obtain ⟨r, hr, hy⟩ := y.property
    have hr0 : r ≠ 0 := by
      intro he
      subst r
      exact hr (Ideal.zero_mem _)
    have hy0 : (y : S) ≠ 0 := by
      rw [← hy]
      simpa using hRS.ne hr0
    exact isUnit_iff_ne_zero.mpr (by simpa using hi.ne hy0)
  let jR : T →ₐ[R] FractionRing R := IsLocalization.liftAlgHom hd
  have hj : Function.Injective jR := by
    apply IsLocalization.injective_of_map_algebraMap_zero
      (R := S) (M := Algebra.algebraMapSubmonoid S M) T jR.toRingHom
    intro s hs
    have hs' : i s = 0 := by simpa [jR] using hs
    have hs0 : s = 0 := hi (by simpa using hs')
    simp [hs0]
  have hcomm (a : Localization.AtPrime p) :
      jR (algebraMap (Localization.AtPrime p) T a) =
        algebraMap (Localization.AtPrime p) (FractionRing R) a := by
    have heq :
        jR.toRingHom.comp (algebraMap (Localization.AtPrime p) T) =
          algebraMap (Localization.AtPrime p) (FractionRing R) := by
      apply IsLocalization.ringHom_ext M
      ext r
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply R (Localization.AtPrime p) T,
        ← IsScalarTower.algebraMap_apply R (Localization.AtPrime p) (FractionRing R)]
      exact jR.commutes r
    exact congrArg (fun g : Localization.AtPrime p →+* FractionRing R => g a) heq
  let j : T →ₐ[Localization.AtPrime p] FractionRing R :=
    { jR with commutes' := hcomm }
  have hbij : Function.Bijective (algebraMap (Localization.AtPrime p) T) := by
    constructor
    · intro a b hab
      apply IsFractionRing.injective (Localization.AtPrime p) (FractionRing R)
      have h := congrArg jR hab
      rw [hcomm, hcomm] at h
      exact h
    · intro t
      obtain ⟨a, ha⟩ :=
        (isIntegrallyClosed_iff (FractionRing R)).mp
          (inferInstance : IsIntegrallyClosed (Localization.AtPrime p))
          ((Algebra.IsIntegral.isIntegral t).map j)
      refine ⟨a, hj ?_⟩
      change (algebraMap (Localization.AtPrime p) (FractionRing R)) a = jR t at ha
      simpa only [hcomm] using ha
  let : IsLocalizedModule p.primeCompl
      (↑(IsScalarTower.toAlgHom R S T) : S →ₗ[R] T) :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have hmap :
      (IsLocalizedModule.map p.primeCompl (Algebra.linearMap R (Localization.AtPrime p))
        (IsScalarTower.toAlgHom R S T).toLinearMap) (Algebra.linearMap R S) =
        (Algebra.linearMap (Localization.AtPrime p) T).restrictScalars R := by
    exact IsLocalizedModule.map_linearMap_of_isLocalization (Localization.AtPrime p) T p
  have hf : Function.Bijective
      ((IsLocalizedModule.map p.primeCompl
        (Algebra.linearMap R (Localization.AtPrime p))
        (↑(IsScalarTower.toAlgHom R S T) : S →ₗ[R] T))
        (Algebra.linearMap R S)) := by
    have hfun := congrArg
      (fun f : Localization.AtPrime p →ₗ[R] T => Function.Bijective f) hmap
    exact hfun.mpr hbij
  let : Module.FinitePresentation R S := Module.finitePresentation_of_finite R S
  exact Module.FinitePresentation.exists_notMem_bijective (Algebra.linearMap R S)
    p (Algebra.linearMap R (Localization.AtPrime p))
    (↑(IsScalarTower.toAlgHom R S T) : S →ₗ[R] T) hf

/-- Bijectivity of a localized module map gives bijectivity of the corresponding
localized ring map. -/
private theorem awayMap_bijective_of_localizedModuleMap_bijective
    (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (r : R)
    (h : Function.Bijective
      ((LocalizedModule.map (Submonoid.powers r)) (Algebra.linearMap R S))) :
    Function.Bijective (Localization.awayMap (algebraMap R S) r) := by
  let Q := Localization.Away ((algebraMap R S) r)
  let T := Localization.Away r
  let : Algebra R Q := inferInstance
  let : IsScalarTower R S Q := inferInstance
  let : Algebra T Q := localizationAlgebra (Submonoid.powers r) S
  let : IsScalarTower R T Q := isScalarTower_localizationAlgebra (Submonoid.powers r) S
  let : IsLocalizedModule (Submonoid.powers r)
      (↑(IsScalarTower.toAlgHom R S Q) : S →ₗ[R] Q) :=
    isLocalizedModule_iff_isLocalization.mpr inferInstance
  have hloc :=
    (IsLocalizedModule.map_bijective_iff_localizedModuleMap_bijective
      (Algebra.linearMap R T)
      (↑(IsScalarTower.toAlgHom R S Q) : S →ₗ[R] Q)).mpr h
  have hlin := IsLocalization.map_linearMap_eq_toLinearMap_mapₐ
    (A := S) (Submonoid.powers r) T Q
  have haway : (IsLocalization.mapₐ (Submonoid.powers r) T T Q
      (Algebra.ofId R S)).toRingHom =
      Localization.awayMap (algebraMap R S) r := by
    apply IsLocalization.ringHom_ext (Submonoid.powers r)
    ext x
    simp [IsLocalization.mapₐ, Localization.awayMap, IsLocalization.Away.map]
    rfl
  have hfun := congrArg (fun l : T →ₗ[R] Q => Function.Bijective l) hlin
  have hmap : Function.Bijective
      (IsLocalization.mapₐ (Submonoid.powers r) T T Q (Algebra.ofId R S)) :=
    hfun.mp hloc
  rw [← haway]
  exact hmap

/-- Bijectivity of a principal localization map is independent of the chosen localization
rings. -/
private theorem awayMap_bijective_of_awayMap_bijective
    {R S Rr Sr : Type*} [CommRing R] [CommRing S]
    [CommRing Rr] [CommRing Sr] [Algebra R Rr] [Algebra S Sr]
    (f : R →+* S) (r : R)
    [IsLocalization.Away r Rr] [IsLocalization.Away (f r) Sr]
    (h : Function.Bijective (Localization.awayMap f r)) :
    Function.Bijective (IsLocalization.Away.map Rr Sr f r) := by
  constructor
  · exact (IsLocalization.Away.map_injective_iff Sr f r).mpr
      ((IsLocalization.Away.map_injective_iff
        (Localization.Away (f r)) f r).mp h.1)
  · exact (IsLocalization.Away.map_surjective_iff Rr Sr f r).mpr
      ((IsLocalization.Away.map_surjective_iff
        (Localization.Away r) (Localization.Away (f r)) f r).mp h.2)

/-- A birational morphism of integral schemes maps the generic point to the generic point, with
an isomorphism on the stalk there. -/
private theorem map_genericPoint_of_isBirational {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
    (f : X ⟶ Y) (hf : IsBirational f) :
    f (genericPoint X) = genericPoint Y ∧ IsIso (f.stalkMap (genericPoint X)) := by
  have hη : genericPoint X ∈ genericPoints X := by simp [genericPoints_eq_singleton]
  exact ⟨by simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using
    hf.bijOn.mapsTo hη, hf.isIso_stalkMap _ hη⟩

/-- An affine open on which some germ is injective is integral. -/
private theorem isIntegral_of_germ_injective {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {x : X} {hx : x ∈ U} [IsDomain (X.presheaf.stalk x)]
    (hinj : Function.Injective (X.presheaf.germ U x hx)) : IsIntegral U := by
  let : IsDomain Γ(X, U) := hinj.isDomain _
  have : IsIntegral (Spec Γ(X, U)) := inferInstance
  exact IsIntegral.of_isIso hU.isoSpec.inv

/-- The finite neighbourhood can be chosen affine and integral. -/
private theorem exists_finite_integral_affine_neighbourhood
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsProper f]
    (x : X) (hfinite : (f ⁻¹' {x}).Finite)
    [IsDomain (X.presheaf.stalk x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧ IsIntegral U ∧ IsFinite (f ∣_ U) := by
  obtain ⟨V, hxV, hfiniteV⟩ :=
    exists_isFinite_morphismRestrict_of_finite_preimage_singleton f x hfinite
  obtain ⟨U, hxU, hU, hUV, hinj⟩ := X.exists_le_and_germ_injective x V hxV
  have heq : V.ι ''ᵁ (V.ι ⁻¹ᵁ U) = U := by
    simp [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hUV]
  have hfin : IsFinite (f ∣_ U) := by
    let : IsFinite (f ∣_ V) := hfiniteV
    let : MorphismProperty.RespectsIso (@IsFinite) := by
      apply MorphismProperty.RespectsIso.mk
      · intro A B C e g hg
        let : IsFinite g := hg
        infer_instance
      · intro A B C e g hg
        let : IsFinite g := hg
        infer_instance
    have hfin' : IsFinite ((f ∣_ V) ∣_ (V.ι ⁻¹ᵁ U)) :=
      inferInstance
    exact heq ▸ ((MorphismProperty.arrow_mk_iso_iff (P := @IsFinite)
      (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U))).mp hfin')
  exact ⟨U, hxU, hU, isIntegral_of_germ_injective hU hinj, hfin⟩

/-- The generic stalk of an integral scheme is a fraction field of the sections on an
affine open. -/
private theorem isFractionRing_stalk_of_eq_genericPoint
    (Z : Scheme.{u}) [IsIntegral Z] (W : Z.Opens) (hW : IsAffineOpen W)
    [Nonempty W] (z : Z) (hzW : z ∈ W) (hz : z = genericPoint Z) :
    let : Algebra Γ(Z, W) (Z.presheaf.stalk z) :=
      (Z.presheaf.germ W z hzW).hom.toAlgebra
    IsFractionRing Γ(Z, W) (Z.presheaf.stalk z) := by
  subst z
  exact functionField_isFractionRing_of_isAffineOpen Z W hW

/-- A point with an open neighbourhood over which `f` is an isomorphism belongs to the
greatest open over which `f` is an isomorphism. -/
public theorem mem_maximal_isomorphism_open_of_exists_isIso_restrict
    {X Y : Scheme.{u}} (f : Y ⟶ X) (U : X.Opens)
    (hU : IsGreatest { V : X.Opens | IsIso (f ∣_ V) } U) (x : X)
    (hx : ∃ V : X.Opens, x ∈ V ∧ IsIso (f ∣_ V)) :
    x ∈ U := by
  obtain ⟨V, hxV, hV⟩ := hx
  exact hU.2 hV hxV

/-- **Stacks Project, Tag 0BFP (finite fibre, normal local ring).**
Let `f : Y ⟶ X` be a proper birational morphism, where `X` is Noetherian and `Y`
is reduced. The morphism is an isomorphism over a neighbourhood of every point whose fibre
is finite and whose local ring is a normal domain. -/
@[stacks 0BFP "finite_fibre_normal", ega "III 4.4.9" "proper case"]
public theorem exists_isIso_restrict_of_finite_fiber_of_normal
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsProper f] [IsReduced Y]
    (hf : IsBirational f) (x : X) (hfinite : (f ⁻¹' {x}).Finite)
    [IsDomain (X.presheaf.stalk x)] [IsIntegrallyClosed (X.presheaf.stalk x)] :
    ∃ U : X.Opens, x ∈ U ∧ IsIso (f ∣_ U) := by
  obtain ⟨U, hxU, hAffine, hIntegral, hFinite⟩ :=
    exists_finite_integral_affine_neighbourhood f x hfinite
  let g := f ∣_ U
  let : IsIntegral U := hIntegral
  let : IsFinite g := hFinite
  let : IsReduced (f ⁻¹ᵁ U) := inferInstance
  have hbir : IsBirational g := birational_morphismRestrict f hf U
  let : IsIntegral (f ⁻¹ᵁ U) :=
    integral_of_reduced_birational_to_integral g hbir
  let : IsAffine U.toScheme := hAffine
  let T : U.toScheme.Opens := ⊤
  have hT : IsAffineOpen T := isAffineOpen_top U.toScheme
  let xU : U.toScheme := ⟨x, hxU⟩
  have : IsIso (U.ι.stalkMap xU) := inferInstance
  let eStalk : (X.presheaf.stalk x) ≃+* (U.toScheme.presheaf.stalk xU) :=
    (asIso (U.ι.stalkMap xU)).commRingCatIsoToRingEquiv
  let : IsIntegrallyClosed (U.toScheme.presheaf.stalk xU) :=
    IsIntegrallyClosed.of_equiv eStalk
  let p : Ideal Γ(U.toScheme, T) :=
    (hT.primeIdealOf ⟨xU, by simp [T]⟩).asIdeal
  let : p.IsPrime := inferInstance
  let : Algebra Γ(U.toScheme, T) (U.toScheme.presheaf.stalk xU) :=
    (U.toScheme.presheaf.germ T xU (by simp [T])).hom.toAlgebra
  let : IsLocalization.AtPrime (U.toScheme.presheaf.stalk xU) p :=
    hT.isLocalization_stalk ⟨xU, by simp [T]⟩
  let : IsIntegrallyClosed (Localization.AtPrime p) :=
    IsIntegrallyClosed.of_equiv
      (IsLocalization.algEquiv p.primeCompl (U.toScheme.presheaf.stalk xU)
        (Localization.AtPrime p)).toRingEquiv
  let : IsLocallyNoetherian U.toScheme := inferInstance
  let : IsNoetherianRing Γ(U.toScheme, T) :=
    IsLocallyNoetherian.component_noetherian ⟨T, hT⟩
  let V : (f ⁻¹ᵁ U).toScheme.Opens := g ⁻¹ᵁ T
  have hV : IsAffineOpen V := hT.preimage g
  have : Nonempty V := by
    simp [V, T]
  let A := Γ(U.toScheme, T)
  let B := Γ((f ⁻¹ᵁ U).toScheme, V)
  let : IsDomain A := inferInstance
  let : IsDomain B := inferInstance
  let : Algebra A B := (g.app T).hom.toAlgebra
  let : Module.Finite A B := g.finite_app T hT
  obtain ⟨heq, _⟩ := map_genericPoint_of_isBirational g hbir
  have hηT : g (genericPoint (f ⁻¹ᵁ U).toScheme) ∈ T := by simp [T]
  let KY := U.toScheme.presheaf.stalk (g (genericPoint (f ⁻¹ᵁ U).toScheme))
  let KZ := (f ⁻¹ᵁ U).toScheme.functionField
  let : Nonempty T := by simp [T]
  let : Algebra A KY :=
    (U.toScheme.presheaf.germ T (g (genericPoint (f ⁻¹ᵁ U).toScheme)) hηT).hom.toAlgebra
  let : IsFractionRing A KY :=
    isFractionRing_stalk_of_eq_genericPoint U.toScheme T hT _ hηT heq
  let : Algebra A KZ :=
    ((g.app T) ≫ (f ⁻¹ᵁ U).toScheme.germToFunctionField V).hom.toAlgebra
  let : IsScalarTower A B KZ := IsScalarTower.of_algebraMap_eq' rfl
  let eRing : KY ≃+* KZ :=
    (asIso (g.stalkMap (genericPoint (f ⁻¹ᵁ U).toScheme))).commRingCatIsoToRingEquiv
  let e : KY ≃ₐ[A] KZ :=
    { eRing with
      commutes' := fun a => by
        change g.stalkMap (genericPoint (f ⁻¹ᵁ U).toScheme)
            (U.toScheme.presheaf.germ T
              (g (genericPoint (f ⁻¹ᵁ U).toScheme)) hηT a) =
          (f ⁻¹ᵁ U).toScheme.germToFunctionField V (g.app T a)
        exact g.germ_stalkMap_apply T (genericPoint (f ⁻¹ᵁ U).toScheme) hηT a }
  let : IsFractionRing A KZ := IsFractionRing.of_algEquiv e
  let i : B →ₐ[A] FractionRing A :=
    (FractionRing.algEquiv A KY).symm.toAlgHom.comp
      (e.symm.toAlgHom.comp (IsScalarTower.toAlgHom A B KZ))
  have hi : Function.Injective i := by
    intro a b hab
    apply (f ⁻¹ᵁ U).toScheme.germToFunctionField_injective V
    exact e.symm.injective ((FractionRing.algEquiv A KY).symm.injective hab)
  obtain ⟨r, hr, hrmod⟩ :=
    exists_localizedModuleMap_bijective_of_finite_of_normal_atPrime A B p i hi
  have hring : Function.Bijective (Localization.awayMap (algebraMap A B) r) :=
    awayMap_bijective_of_localizedModuleMap_bijective A B r hrmod
  let W : U.toScheme.Opens := U.toScheme.basicOpen r
  have hxW : xU ∈ W := by
    change xU ∈ U.toScheme.basicOpen r
    rw [U.toScheme.mem_basicOpen r xU (by simp [T])]
    exact (IsLocalization.AtPrime.isUnit_to_map_iff
      (U.toScheme.presheaf.stalk xU) p r).mpr (by simpa using hr)
  have hW : IsAffineOpen W := hT.basicOpen r
  let : IsLocalization.Away r Γ(U.toScheme, W) := hT.isLocalization_basicOpen r
  let : IsLocalization.Away (g.app T r)
      Γ((f ⁻¹ᵁ U).toScheme, (f ⁻¹ᵁ U).toScheme.basicOpen (g.app T r)) :=
    hV.isLocalization_basicOpen (g.app T r)
  have hring' : Function.Bijective
      (IsLocalization.Away.map Γ(U.toScheme, W)
        Γ((f ⁻¹ᵁ U).toScheme, (f ⁻¹ᵁ U).toScheme.basicOpen (g.app T r))
        (g.app T).hom r) :=
    awayMap_bijective_of_awayMap_bijective (g.app T).hom r hring
  have hApp : IsIso (g.app W) := by
    rw [hT.app_basicOpen_eq_away_map g hV r]
    have : IsIso (CommRingCat.ofHom
        (IsLocalization.Away.map Γ(U.toScheme, W)
          Γ((f ⁻¹ᵁ U).toScheme, (f ⁻¹ᵁ U).toScheme.basicOpen (g.app T r))
          (g.app T).hom r)) :=
      (ConcreteCategory.isIso_iff_bijective _).mpr hring'
    infer_instance
  have hIsoRestr : IsIso (g ∣_ W) :=
    (isIso_morphismRestrict_iff_isIso_app g hW).mpr hApp
  let W' : X.Opens := U.ι ''ᵁ W
  have hxW' : x ∈ W' := by
    change x ∈ U.ι ''ᵁ W
    exact ⟨xU, hxW, rfl⟩
  have hIsoFinal : IsIso (f ∣_ W') :=
    (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
      (morphismRestrictRestrict f U W)).mp hIsoRestr
  exact ⟨W', hxW', hIsoFinal⟩


/-- A point with normal local ring on a Noetherian scheme has an integral affine open
neighbourhood. -/
@[ega "IV 6.13.1" "special case"]
private lemma exists_integral_affineOpen_of_isNormal_stalk
    {X : Scheme.{u}} [IsNoetherian X] (x : X)
    (hnormal : IsNormalRing (X.presheaf.stalk x)) :
    ∃ (U : X.Opens) (_hx : x ∈ U), IsAffineOpen U ∧ IsIntegral U.toScheme := by
  let : IsDomain (X.presheaf.stalk x) :=
    hnormal.of_isLocalRing.1
  obtain ⟨U, hx, hU, hinj⟩ :=
    exists_affineOpen_germ_injective_of_isLocallyNoetherian X x
  exact ⟨U, hx, hU, isIntegral_of_germ_injective hU hinj⟩

/-- A local homomorphism of essentially finite type out of a normal local domain, with finite
residue field extension and zero-dimensional closed fibre, is an isomorphism once both rings
embed compatibly into the fraction field of the source. -/
private theorem isIso_localHom_of_normal_essFiniteType
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    {K : Type u} [CommRing K] [Algebra R K] [IsFractionRing R K]
    (f : R →+* S) [IsLocalHom f] [IsDomain R] [IsDomain S] [IsIntegrallyClosed R]
    (hft : f.EssFiniteType)
    (hres : @Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S)
      _ _ (Stacks.LocalizationOfFiniteAlgebra.residueAlgebra f).toModule)
    (hdim : ringKrullDim (Stacks.LocalizationOfFiniteAlgebra.closedFiber f) = 0)
    (i : S →+* K) (hi : Function.Injective i)
    (hRinj : Function.Injective (algebraMap R K))
    (hicomm : ∀ r, i (f r) = algebraMap R K r) :
    IsIso (CommRingCat.ofHom f) := by
  classical
  let : Algebra R S := f.toAlgebra
  obtain ⟨T, hcommT, g, h, M, hg, hcomp, hloc⟩ :=
    Stacks.LocalizationOfFiniteAlgebra.essFiniteType_localization_finite f hft hres hdim
  let : CommRing T := hcommT
  let : Algebra R T := g.toAlgebra
  let : Algebra T S := h.toAlgebra
  let : IsScalarTower R T S := IsScalarTower.of_algebraMap_eq' (by
    ext r
    exact congrArg (fun k : R →+* S => k r) hcomp.symm)
  let j : T →+* K := i.comp h
  let jA : T →ₐ[R] K :=
    { toRingHom := j
      commutes' := fun r => by
        calc
          i (h (g r)) = i (f r) :=
            congrArg i (congrArg (fun k : R →+* S => k r) hcomp)
          _ = algebraMap R K r := hicomm r }
  have hgInt (b : T) : _root_.IsIntegral R b := by
    change g.IsIntegralElem b
    exact hg.to_isIntegral b
  have hImage : ∀ b : T, ∃ r : R, h b = f r := by
    intro b
    have hb : _root_.IsIntegral R (jA b) :=
      (hgInt b).map jA
    obtain ⟨r, hr⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hb
    refine ⟨r, ?_⟩
    apply hi
    calc
      i (h b) = jA b := rfl
      _ = algebraMap R K r := hr.symm
      _ = i (f r) := by
        exact (hicomm r).symm
  have hsurj : Function.Surjective f := by
    intro s
    obtain ⟨b, t, hst⟩ := IsLocalization.exists_mk'_eq M s
    obtain ⟨r₁, hr₁⟩ := hImage b
    obtain ⟨r₂, hr₂⟩ := hImage t
    have hden : IsUnit (f r₂) := by
      rw [← hr₂]
      exact IsLocalization.map_units S t
    have hr₂unit : IsUnit r₂ := IsLocalHom.map_nonunit r₂ hden
    let u : Rˣ := hr₂unit.unit
    have huval : (u : R) = r₂ := hr₂unit.unit_spec
    have hmulInv : f ((u⁻¹ : Rˣ) : R) * f r₂ = 1 := by
      rw [← huval, ← map_mul]
      simp
    have hstmul : s * f r₂ = f r₁ := by
      calc
        s * f r₂ = IsLocalization.mk' S b t * h t := by rw [hst, hr₂]
        _ = h b := IsLocalization.mk'_spec S b t
        _ = f r₁ := hr₁
    have hfmul : f (r₁ * ((u⁻¹ : Rˣ) : R)) * f r₂ = f r₁ := by
      rw [map_mul]
      calc
        f r₁ * f ((u⁻¹ : Rˣ) : R) * f r₂ =
            f r₁ * (f ((u⁻¹ : Rˣ) : R) * f r₂) := by ac_rfl
        _ = f r₁ := by rw [hmulInv, mul_one]
    refine ⟨r₁ * ((u⁻¹ : Rˣ) : R), ?_⟩
    exact (hden.mul_left_inj).mp (hstmul.trans hfmul.symm) |>.symm
  have hinj : Function.Injective f := by
    intro a b hab
    apply hRinj
    calc
      algebraMap R K a = i (f a) := (hicomm a).symm
      _ = i (f b) := congrArg i hab
      _ = algebraMap R K b := hicomm b
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ⟨hinj, hsurj⟩

/-- A quasi-finite local homomorphism has a finite residue field extension. -/
private theorem quasiFinite_local_residueField_finite
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hqf : f.QuasiFinite) :
    @Module.Finite (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) _ _
      (Stacks.LocalizationOfFiniteAlgebra.residueAlgebra f).toModule := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.QuasiFinite R S := hqf
  let p : Ideal R := IsLocalRing.maximalIdeal R
  let q : Ideal S := IsLocalRing.maximalIdeal S
  have : p.IsPrime := IsLocalRing.maximalIdeal.isMaximal R |>.isPrime
  have : q.IsPrime := IsLocalRing.maximalIdeal.isMaximal S |>.isPrime
  have hqp : q.comap (algebraMap R S) = p := by
    change q.comap f = p
    exact IsLocalRing.maximalIdeal_comap f
  have : q.LiesOver p := ⟨hqp.symm⟩
  let := Localization.AtPrime.algebraOfLiesOver p q
  have : Localization.AtPrime.IsLiesOverAlgebra p q := by
    exact ⟨rfl⟩
  have : IsScalarTower R (Localization.AtPrime p) (Localization.AtPrime q) :=
    inferInstance
  have : Algebra.QuasiFiniteAt R q := inferInstance
  let ψ : Localization.AtPrime p →+* Localization.AtPrime q :=
    Localization.localRingHom p q (algebraMap R S) hqp.symm
  have hfinite : Module.Finite p.ResidueField q.ResidueField := by infer_instance
  have hfiniteψ : (IsLocalRing.ResidueField.map ψ).Finite :=
    RingHom.finite_algebraMap.mpr hfinite
  let ep : R ≃ₐ[R] Localization.AtPrime p := IsLocalization.atUnits R p.primeCompl
    (fun r hr ↦ IsLocalRing.notMem_maximalIdeal.mp hr)
  let eq : S ≃ₐ[S] Localization.AtPrime q := IsLocalization.atUnits S q.primeCompl
    (fun r hr ↦ IsLocalRing.notMem_maximalIdeal.mp hr)
  have : IsLocalHom ep.toRingEquiv.toRingHom :=
    IsLocalHom.of_surjective _ ep.surjective
  have : IsLocalHom eq.toRingEquiv.toRingHom :=
    IsLocalHom.of_surjective _ eq.surjective
  let epr := IsLocalRing.ResidueField.mapEquiv ep.toRingEquiv
  let eqr := IsLocalRing.ResidueField.mapEquiv eq.toRingEquiv
  have hring : ψ.comp ep.toRingEquiv.toRingHom = eq.toRingEquiv.toRingHom.comp f := by
    apply RingHom.ext
    intro r
    change ψ (algebraMap R (Localization.AtPrime p) r) =
      algebraMap S (Localization.AtPrime q) (f r)
    exact Localization.localRingHom_to_map p q (algebraMap R S) hqp.symm r
  have : IsLocalHom (ψ.comp ep.toRingEquiv.toRingHom) :=
    RingHom.isLocalHom_comp ψ ep.toRingEquiv.toRingHom
  have : IsLocalHom (eq.toRingEquiv.toRingHom.comp f) :=
    RingHom.isLocalHom_comp (eq.toRingEquiv.toRingHom) f
  have hrescomp :
      (IsLocalRing.ResidueField.map ψ).comp epr.toRingHom =
        eqr.toRingHom.comp (IsLocalRing.ResidueField.map f) := by
    apply RingHom.ext
    intro z
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
    simp only [RingHom.comp_apply, epr, eqr, IsLocalRing.ResidueField.map_residue]
    exact congrArg (IsLocalRing.residue (Localization.AtPrime q))
      (congrArg (fun k : R →+* Localization.AtPrime q ↦ k r) hring)
  have hfinComp :
      (eqr.symm.toRingHom.comp
        ((IsLocalRing.ResidueField.map ψ).comp epr.toRingHom)).Finite :=
    RingHom.Finite.comp (RingHom.Finite.of_surjective _ eqr.symm.surjective)
      (RingHom.Finite.comp hfiniteψ (RingHom.Finite.of_surjective _ epr.surjective))
  have hEq :
      eqr.symm.toRingHom.comp
        ((IsLocalRing.ResidueField.map ψ).comp epr.toRingHom) =
          IsLocalRing.ResidueField.map f := by
    apply RingHom.ext
    intro z
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective z
    apply eqr.injective
    have hz := congrArg
      (fun k : IsLocalRing.ResidueField R →+* IsLocalRing.ResidueField (Localization.AtPrime q) ↦
        k (IsLocalRing.residue R r)) hrescomp
    simpa [RingHom.comp_apply, epr, eqr, IsLocalRing.ResidueField.mapEquiv,
      IsLocalRing.ResidueField.map_residue] using hz
  have hfinitef : (IsLocalRing.ResidueField.map f).Finite := hEq ▸ hfinComp
  let : Algebra (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    Stacks.LocalizationOfFiniteAlgebra.residueAlgebra f
  let : Module (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField S) :=
    (Stacks.LocalizationOfFiniteAlgebra.residueAlgebra f).toModule
  exact RingHom.finite_algebraMap.mp hfinitef

/-- The closed fibre of a quasi-finite local homomorphism is zero-dimensional. -/
@[ega "0 7.4.4" "(i)"]
private theorem quasiFinite_local_closedFiber_dimension_zero
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] (hqf : f.QuasiFinite) :
    ringKrullDim (Stacks.LocalizationOfFiniteAlgebra.closedFiber f) = 0 := by
  let : Algebra R S := f.toAlgebra
  have : Algebra.QuasiFinite R S := hqf
  let p : Ideal R := IsLocalRing.maximalIdeal R
  have : p.IsPrime := IsLocalRing.maximalIdeal.isMaximal R |>.isPrime
  have : IsArtinianRing (p.Fiber S) := inferInstance
  let ep : R ≃ₐ[R] Localization.AtPrime p := IsLocalization.atUnits R p.primeCompl
    (fun r hr ↦ IsLocalRing.notMem_maximalIdeal.mp hr)
  have : IsLocalHom ep.toRingEquiv.toRingHom :=
    IsLocalHom.of_surjective _ ep.surjective
  let epr := IsLocalRing.ResidueField.mapEquiv ep.toRingEquiv
  let eBase : IsLocalRing.ResidueField R ≃ₐ[R] p.ResidueField :=
    { toRingEquiv := epr
      commutes' := by
        intro r
        change IsLocalRing.ResidueField.map ep.toRingEquiv.toRingHom
          (IsLocalRing.residue R r) = algebraMap R p.ResidueField r
        rw [IsLocalRing.ResidueField.map_residue]
        calc
          IsLocalRing.residue (Localization.AtPrime p) (ep r) =
              IsLocalRing.residue (Localization.AtPrime p)
                (algebraMap R (Localization.AtPrime p) r) := by
                  congr 1
          _ = algebraMap R p.ResidueField r := by
            rw [IsScalarTower.algebraMap_apply R (Localization.AtPrime p) p.ResidueField]
            rfl }
  let eFiber : (IsLocalRing.ResidueField R ⊗[R] S) ≃ₐ[R] p.Fiber S :=
    Algebra.TensorProduct.congr eBase (AlgEquiv.refl (R := R) (A₁ := S))
  have : IsArtinianRing (IsLocalRing.ResidueField R ⊗[R] S) :=
    RingEquiv.isArtinianRing eFiber.symm.toRingEquiv
  have hJle : Ideal.map f (IsLocalRing.maximalIdeal R) ≤ IsLocalRing.maximalIdeal S :=
    IsLocalRing.map_maximalIdeal_le f
  have hJne : Ideal.map f (IsLocalRing.maximalIdeal R) ≠ ⊤ :=
    ne_top_of_le_ne_top (IsLocalRing.maximalIdeal.isMaximal S).ne_top hJle
  let : Nontrivial (S ⧸ Ideal.map f (IsLocalRing.maximalIdeal R)) :=
    Ideal.Quotient.nontrivial_iff.mpr hJne
  have : IsArtinianRing (Stacks.LocalizationOfFiniteAlgebra.closedFiber f) := by
    let eClosed : (IsLocalRing.ResidueField R ⊗[R] S) ≃ₐ[R]
      Stacks.LocalizationOfFiniteAlgebra.closedFiber f :=
      (Algebra.TensorProduct.comm R (IsLocalRing.ResidueField R) S).trans
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot S
          (IsLocalRing.maximalIdeal R)).symm.restrictScalars R)
    exact RingEquiv.isArtinianRing eClosed.toRingEquiv
  have hdimLE : Ring.KrullDimLE 0 (Stacks.LocalizationOfFiniteAlgebra.closedFiber f) :=
    (isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mp inferInstance).2
  exact ringKrullDimZero_iff_ringKrullDim_eq_zero.mp hdimLE

/-- A morphism that becomes an isomorphism both after precomposition and after
postcomposition is itself an isomorphism. -/
lemma isIso_of_isIso_comp_left_and_right {C : Type*} [Category C]
    {A B D E : C} (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E)
    [IsIso (a ≫ b)] [IsIso (b ≫ c)] : IsIso b := by
  let : IsSplitEpi b := IsSplitEpi.mk' ⟨inv (a ≫ b) ≫ a, by
    rw [Category.assoc, IsIso.inv_hom_id]⟩
  let : IsSplitMono b := IsSplitMono.mk' ⟨c ≫ inv (b ≫ c), by
    rw [← Category.assoc, IsIso.hom_inv_id]⟩
  exact isIso_of_mono_of_isSplitEpi b

/-- **Stacks Project, Tag 0BFP (quasi-finite point over a normal point).** The maximal open
over which a proper birational morphism with reduced source is an isomorphism contains every
normal point admitting a preimage at which the morphism is quasi-finite. -/
@[stacks 0BFP "quasi_finite_point_normal", ega "III 4.4.9" "proper case"]
public theorem mem_maximal_isomorphism_open_of_quasiFiniteAt_of_isNormal
    {X Y : Scheme.{u}} [IsNoetherian X] (f : Y ⟶ X) [IsProper f] [IsReduced Y]
    (hf : IsBirational f) (U : X.Opens)
    (hU : IsGreatest { V : X.Opens | IsIso (f ∣_ V) } U) (x : X)
    (hnormal : IsNormalRing (X.presheaf.stalk x)) (y : Y) (hy : f y = x)
    (hqf : quasiFiniteAt f y) :
    x ∈ U := by
  classical
  obtain ⟨W, hxW, hWaff, hWint⟩ := exists_integral_affineOpen_of_isNormal_stalk x hnormal
  let X' := W.toScheme
  let V := f ⁻¹ᵁ W
  let Y' := V.toScheme
  let g := f ∣_ W
  have hyV : y ∈ V := by
    change f y ∈ W
    simpa [hy] using hxW
  let y' : Y' := ⟨y, hyV⟩
  let x' : X' := g y'
  have hbir : IsBirational g := birational_morphismRestrict f hf W
  let : IsIntegral X' := hWint
  let : IsReduced Y' := inferInstance
  let : IsIntegral Y' := integral_of_reduced_birational_to_integral g hbir
  have : IsIso (W.ι.stalkMap x') := inferInstance
  have : IsIso (V.ι.stalkMap y') := inferInstance
  let : IsLocalHom (f.stalkMap y).hom := inferInstance
  let : IsLocalHom (g.stalkMap y').hom := inferInstance
  let R := X.presheaf.stalk (f (V.ι y'))
  let S := Y.presheaf.stalk (V.ι y')
  let R' := X'.presheaf.stalk x'
  let S' := Y'.presheaf.stalk y'
  let K := X'.functionField
  let KY := Y'.functionField
  obtain ⟨hgen, _⟩ := map_genericPoint_of_isBirational g hbir
  let eGen : X'.presheaf.stalk (genericPoint X') ≅
      X'.presheaf.stalk (g (genericPoint Y')) :=
    X'.presheaf.stalkCongr (.of_eq hgen.symm)
  let gηforward : CommRingCat.of K ⟶ CommRingCat.of KY :=
    eGen.hom ≫ g.stalkMap (genericPoint Y')
  have : IsIso gηforward := by infer_instance
  let gη : KY →+* K := (asIso gηforward).inv.hom
  let eη : KY ≃+* K := (asIso gηforward).symm.commRingCatIsoToRingEquiv
  let spX := (X'.presheaf.stalkSpecializes (genericPoint_specializes x')).hom
  let spY := (Y'.presheaf.stalkSpecializes (genericPoint_specializes y')).hom
  have hWpt : W.ι x' = x := by
    change ((f ∣_ W) y').1 = x
    rw [morphismRestrict_base_coe]
    change f y = x
    exact hy
  have hVpt : V.ι y' = y := rfl
  have hmorph : V.ι ≫ f = g ≫ W.ι := by
    rw [morphismRestrict_ι f W]
  have hXeq : (V.ι ≫ f) y' = (g ≫ W.ι) y' :=
    congrArg (fun k : Y' ⟶ X => k y') hmorph
  have hgy : g y' = x' := by
    rfl
  let iWmap : CommRingCat.of R ⟶ CommRingCat.of R' :=
    (X.presheaf.stalkCongr (.of_eq hXeq)).hom ≫
      W.ι.stalkMap (g y') ≫
      eqToHom (congrArg (fun z : X' => X'.presheaf.stalk z) hgy)
  have : IsIso ((X.presheaf.stalkCongr (.of_eq hXeq)).hom) := by infer_instance
  have : IsIso (eqToHom (congrArg (fun z : X' => X'.presheaf.stalk z) hgy)) := by
    infer_instance
  have : IsIso (W.ι.stalkMap (g y')) := inferInstance
  have : IsIso iWmap := by
    exact IsIso.comp_isIso'
      (inferInstance : IsIso ((X.presheaf.stalkCongr (.of_eq hXeq)).hom))
      (IsIso.comp_isIso'
        (inferInstance : IsIso (W.ι.stalkMap (g y')))
        (inferInstance : IsIso
          (eqToHom (congrArg (fun z : X' => X'.presheaf.stalk z) hgy))))
  let iW : R →+* R' := iWmap.hom
  let iVmap : CommRingCat.of S ⟶ CommRingCat.of S' := V.ι.stalkMap y'
  have : IsIso iVmap := by infer_instance
  let iV : S →+* S' := iVmap.hom
  let fxy := (f.stalkMap (V.ι y')).hom
  let gxy : R' →+* S' := (g.stalkMap y').hom
  let b : R →+* K := spX.comp iW
  let i : S →+* K := gη.comp (spY.comp iV)
  let : Algebra R' K := spX.toAlgebra
  let : Algebra R K := b.toAlgebra
  have : IsFractionRing R' K := inferInstance
  let eW : R ≃+* R' := (asIso iWmap).commRingCatIsoToRingEquiv
  have : IsFractionRing R K :=
    IsFractionRing.of_ringEquiv_left eW (fun _ => rfl)
  have hRinj : Function.Injective (algebraMap R K) := by
    change Function.Injective b
    intro a a' haa
    apply eW.injective
    apply IsFractionRing.injective R' K
    exact haa
  have hnormalR : IsNormalRing R := by
    change IsNormalRing (X.presheaf.stalk (f (V.ι y')))
    have hpt : f (V.ι y') = x := by rw [hVpt, hy]
    rw [hpt]
    exact hnormal
  let : IsDomain R := hnormalR.of_isLocalRing.1
  let eV : S ≃+* S' := (asIso iVmap).commRingCatIsoToRingEquiv
  let : IsDomain S := eV.isDomain_iff.mpr inferInstance
  let : IsIntegrallyClosed R :=
    hnormalR.of_isLocalRing.2
  have hft : fxy.EssFiniteType := by
    let : LocallyOfFiniteType f := inferInstance
    exact LocallyOfFiniteType.stalkMap f (V.ι y')
  have hqf' : fxy.QuasiFinite := by
    change (f.stalkMap (V.ι y')).hom.QuasiFinite
    rw [hVpt]
    exact hqf.2
  have hres := quasiFinite_local_residueField_finite fxy hqf'
  have hdim := quasiFinite_local_closedFiber_dimension_zero fxy hqf'
  have hi : Function.Injective i := by
    intro a a' haa
    apply eV.injective
    apply IsFractionRing.injective S' KY
    apply eη.injective
    exact haa
  have hresMap := Scheme.Hom.stalkMap_congr_hom (V.ι ≫ f) (g ≫ W.ι) hmorph y'
  rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at hresMap
  have hmap : iV.comp fxy = gxy.comp iW := by
    dsimp [fxy, iV, iW, iVmap, iWmap, gxy, hgy]
    simpa [hVpt, hgy, ← CommRingCat.hom_comp] using
      congrArg CommRingCat.Hom.hom hresMap
  have hcomm : ∀ r, i (fxy r) = algebraMap R K r := by
    intro r
    let hmapSpec := (genericPoint_specializes y').map g.continuous
    have hn := Scheme.Hom.stalkSpecializes_stalkMap g (genericPoint Y') y'
      (genericPoint_specializes y')
    let hgenRel := specializes_of_eq hgen
    let hleft := hgenRel.trans (genericPoint_specializes x')
    let hright := hmapSpec
    have hrel : hleft = hright := Subsingleton.elim _ _
    have hpoint :
        X'.presheaf.stalkSpecializes (genericPoint_specializes x') ≫
            X'.presheaf.stalkSpecializes hgenRel =
          X'.presheaf.stalkSpecializes hmapSpec := by
      calc
        _ = X'.presheaf.stalkSpecializes hleft := by
          rw [← TopCat.Presheaf.stalkSpecializes_comp
            (F := X'.presheaf) hgenRel (genericPoint_specializes x')]
        _ = X'.presheaf.stalkSpecializes hright := by rw [hrel]
        _ = _ := rfl
    have hcat : CommRingCat.ofHom spX ≫ gηforward =
        CommRingCat.ofHom gxy ≫ CommRingCat.ofHom spY := by
      calc
        _ = (X'.presheaf.stalkSpecializes (genericPoint_specializes x') ≫
            X'.presheaf.stalkSpecializes hgenRel) ≫ g.stalkMap (genericPoint Y') := by
          dsimp [spX, gηforward, hgenRel, eGen]
          simp only [TopCat.Presheaf.stalkCongr_hom]
          rfl
        _ = X'.presheaf.stalkSpecializes hmapSpec ≫
            g.stalkMap (genericPoint Y') := by
          rw [hpoint]
        _ = g.stalkMap y' ≫
            Y'.presheaf.stalkSpecializes (genericPoint_specializes y') := hn
        _ = CommRingCat.ofHom gxy ≫ CommRingCat.ofHom spY := by
          dsimp [gxy, spY]
    have hn' := congrArg CommRingCat.Hom.hom hcat
    change gηforward.hom.comp spX = spY.comp gxy at hn'
    have hmap' := congrArg (fun q : R →+* S' => q r)
      hmap
    have hmapValue : iV (fxy r) = gxy (iW r) := by
      simpa only [RingHom.comp_apply] using hmap'
    have hn'' := congrArg (fun q : R' →+* KY => q (iW r)) hn'
    change gηforward.hom (spX (iW r)) = spY (gxy (iW r)) at hn''
    change gη (spY (iV (fxy r))) = spX (iW r)
    rw [hmapValue]
    rw [← hn'']
    simp [gη]
  have hlocalIso : IsIso (CommRingCat.ofHom fxy) :=
    isIso_localHom_of_normal_essFiniteType fxy hft hres hdim i hi hRinj hcomm
  have : IsIso (CommRingCat.ofHom fxy) := hlocalIso
  have hmapCat : CommRingCat.ofHom fxy ≫ iVmap = iWmap ≫ CommRingCat.ofHom gxy := by
    ext r
    exact congrArg (fun q : R →+* S' => q r) hmap
  have hgxyEq : CommRingCat.ofHom gxy =
      (asIso iWmap).inv ≫ CommRingCat.ofHom fxy ≫ iVmap := by
    apply (cancel_epi iWmap).mp
    calc
      iWmap ≫ CommRingCat.ofHom gxy = CommRingCat.ofHom fxy ≫ iVmap := hmapCat.symm
      _ = iWmap ≫ ((asIso iWmap).inv ≫ CommRingCat.ofHom fxy ≫ iVmap) := by
        simp
  have : IsIso (CommRingCat.ofHom gxy) := by
    rw [hgxyEq]
    infer_instance
  let phi : S' →+* R' := (asIso (CommRingCat.ofHom gxy)).inv.hom
  have hphiS : phi.comp gxy = RingHom.id _ := by
    rw [← CommRingCat.hom_comp]
    change ((asIso (CommRingCat.ofHom gxy)).hom ≫
      (asIso (CommRingCat.ofHom gxy)).inv).hom = _
    rw [(asIso (CommRingCat.ofHom gxy)).hom_inv_id]
    rfl
  have hphi : IsLocalHom phi := IsLocalHom.of_surjective _ (by
    intro r
    refine ⟨gxy r, ?_⟩
    have hh := congrArg (fun q : R' →+* R' => q r) hphiS
    simpa [RingHom.comp_apply] using hh)
  have : LocallyOfFiniteType g := inferInstance
  obtain ⟨O, hxO, s, hs, hsy, hphiEq⟩ :=
    exists_open_morphism_inducing_localHom_of_isReduced
      (𝟙 X') g x' x' y' (by simp) hgy phi hphi
      (by
        convert hphiS using 1 <;> simp [gxy, -CommRingCat.hom_comp]
        rfl) inferInstance
      (show IsReduced X' from inferInstance)
      (by rw [irreducibleComponents_eq_singleton]; exact Set.finite_singleton _)
  have hs' : s ≫ g = O.ι := by simpa using hs
  have hsu (u : O.toScheme) : g (s u) = O.ι u := congrArg (fun t : O.toScheme ⟶ X' => t u) hs'
  let D := g ⁻¹ᵁ O
  let : Nonempty D.toScheme :=
    ⟨⟨y', by change g y' ∈ O; simpa [hgy] using hxO⟩⟩
  let : IsIntegral D.toScheme := isIntegral_of_isOpenImmersion D.ι
  let : IsReduced D.toScheme := inferInstance
  let z : D.toScheme := ⟨y', by change g y' ∈ O; simpa [hgy] using hxO⟩
  let a := g.resLE O D le_rfl
  let j := D.ι
  let k := a ≫ s
  have hbase : j ≫ g = j ≫ g := rfl
  have hkbase : k ≫ g = j ≫ g := by
    calc
      k ≫ g = a ≫ (s ≫ g) := by simp [k, Category.assoc]
      _ = a ≫ O.ι := by rw [hs]; simp
      _ = j ≫ g := by
        simp [a, j]
  have hzbase : (j ≫ g) z = x' := by
    change g y' = x'
    exact hgy
  have hzY : g y' = x' := hgy
  have hjz : j z = y' := rfl
  have hkz : k z = y' := by
    change s (a z) = y'
    have haz : a z = ⟨x', hxO⟩ := by
      apply Subtype.ext
      change (g.resLE O D le_rfl z).1 = x'
      rw [Scheme.Hom.coe_resLE_apply]
    rw [haz, hsy]
  let eX : CommRingCat.of R' ⟶ CommRingCat.of (X'.presheaf.stalk (g y')) :=
    eqToHom (congrArg (fun t : X' => X'.presheaf.stalk t) hgy).symm
  have : IsIso eX := inferInstance
  have hcompG : eX ≫ g.stalkMap y' = CommRingCat.ofHom gxy := by
    simp [eX, gxy]
  have : IsIso (g.stalkMap y') := by
    have : IsIso (eX ≫ g.stalkMap y') := by rw [hcompG]; infer_instance
    exact IsIso.of_isIso_comp_left eX (g.stalkMap y')
  have hfg : j.stalkMap z =
      Y'.presheaf.stalkSpecializes
        (Inseparable.of_eq (hjz.trans hkz.symm).symm).specializes ≫ k.stalkMap z := by
    have hpt : j z = k z := hjz.trans hkz.symm
    have hs0 := Scheme.Hom.stalkMap_congr (j ≫ g) (k ≫ g) hkbase.symm z z rfl
    rw [Scheme.Hom.stalkMap_comp, Scheme.Hom.stalkMap_comp] at hs0
    have hcompPt : (j ≫ g) z = (k ≫ g) z := hkbase.symm ▸ rfl
    have hptMapped : g (j z) = g (k z) := congrArg g hpt
    have hs' : g.stalkMap (j z) ≫ j.stalkMap z =
        (X'.presheaf.stalkCongr (.of_eq hcompPt)).hom ≫
          g.stalkMap (k z) ≫ k.stalkMap z := by simpa using hs0
    have hcongrEq :
        (X'.presheaf.stalkCongr (.of_eq hcompPt)).hom =
          (X'.presheaf.stalkCongr (.of_eq hptMapped)).hom := by congr 1
    have hfgpt := g.stalkMap_congr_point (j z) (k z) hpt
    have hspec : Y'.presheaf.stalkSpecializes
        (Inseparable.of_eq hpt.symm).specializes =
          (Y'.presheaf.stalkCongr (.of_eq hpt)).hom := by rfl
    have : IsIso (g.stalkMap (j z)) := by rw [hjz]; infer_instance
    apply (cancel_epi (g.stalkMap (j z))).mp
    rw [hspec]
    have hreplace :
        ((X'.presheaf.stalkCongr (.of_eq hcompPt)).hom ≫
          g.stalkMap (k z)) ≫ k.stalkMap z =
        (g.stalkMap (j z) ≫
          (Y'.presheaf.stalkCongr (.of_eq hpt)).hom) ≫ k.stalkMap z := by
      rw [hcongrEq]
      exact congrArg (fun q => q ≫ k.stalkMap z) hfgpt.symm
    exact hs'.trans hreplace
  have : LocallyOfFiniteType g := inferInstance
  obtain ⟨Z, hzZ, hZ⟩ :=
    exists_open_eq_of_stalkMap_eq
      (j ≫ g) g j k hbase hkbase x' z y' hzbase hzY hjz hkz hfg
      (Or.inl inferInstance)
  let q := Z.ι ≫ a
  let j' := Z.ι ≫ D.ι
  have hj : j' = q ≫ s := by
    dsimp [j', q, k] at hZ ⊢
    simpa only [Category.assoc] using hZ
  have hjq : j' ≫ g = q ≫ O.ι := by
    calc
      j' ≫ g = (q ≫ s) ≫ g := by rw [hj]
      _ = q ≫ O.ι := by
        rw [Category.assoc, hs]
        simp
  have hjOpen : IsOpenImmersion j' := by
    dsimp [j']
    infer_instance
  have hqInj : Function.Injective q := by
    intro v w hvw
    apply j'.isOpenEmbedding.injective
    have : j' v = j' w := by simpa [hj, Scheme.Hom.comp_apply] using congrArg s hvw
    exact this
  have hqOpen : IsOpenMap q := by
    intro T hT
    have himage : q '' T = s ⁻¹' (j' '' T) := by
      ext u
      constructor
      · rintro ⟨v, hvT, rfl⟩
        exact ⟨v, hvT, by simp [hj]⟩
      · rintro ⟨v, hvT, hgv⟩
        refine ⟨v, hvT, ?_⟩
        apply O.ι.isOpenEmbedding.injective
        calc
          O.ι (q v) = g (j' v) := by
            have hv := congrArg (fun t : Z.toScheme ⟶ X' => t v) hjq
            simpa only [Scheme.Hom.comp_apply] using hv.symm
          _ = g (s u) := congrArg g hgv
          _ = O.ι u := hsu u
    rw [himage]
    exact (j'.isOpenEmbedding.isOpenMap T hT).preimage s.continuous
  have hqEmbedding : IsOpenEmbedding q :=
    IsOpenEmbedding.of_continuous_injective_isOpenMap q.continuous hqInj hqOpen
  have hqStalk (v : Z.toScheme) : IsIso (q.stalkMap v) := by
    let u : O.toScheme := q v
    have hleft : IsIso (g.stalkMap (s u) ≫ s.stalkMap u) := by
      have hi : IsIso ((s ≫ g).stalkMap u) := by rw [hs]; infer_instance
      rw [Scheme.Hom.stalkMap_comp] at hi
      exact hi
    have hright : IsIso (s.stalkMap u ≫ q.stalkMap v) := by
      have hi : IsIso (j'.stalkMap v) := by infer_instance
      rw [hj, Scheme.Hom.stalkMap_comp] at hi
      exact hi
    let : IsIso (s.stalkMap u) :=
      isIso_of_isIso_comp_left_and_right (g.stalkMap (s u)) (s.stalkMap u)
        (q.stalkMap v)
    exact IsIso.of_isIso_comp_left (s.stalkMap u) (q.stalkMap v)
  have : IsOpenImmersion q :=
    IsOpenImmersion.iff_isIso_stalkMap.mpr ⟨hqEmbedding, hqStalk⟩
  let sD : O.toScheme ⟶ D.toScheme := O.toScheme.topIso.inv ≫ s.resLE D ⊤ (by
    intro u _
    change s u ∈ D
    change g (s u) ∈ O
    exact hsu u ▸ u.2)
  have hsDfac : sD ≫ D.ι = s := by
    dsimp [sD]
    simp [Category.assoc, Scheme.Hom.resLE_comp_ι]
  have hsDsec : sD ≫ a = 𝟙 O.toScheme := by
    apply (cancel_mono O.ι).mp
    calc
      (sD ≫ a) ≫ O.ι = sD ≫ D.ι ≫ g := by
        simp [Category.assoc, a, Scheme.Hom.resLE_comp_ι]
      _ = s ≫ g := by
        simpa only [Category.assoc] using
          congrArg (fun t : O.toScheme ⟶ Y' => t ≫ g) hsDfac
      _ = 𝟙 O.toScheme ≫ O.ι := by simp [hs']
      _ = (𝟙 O.toScheme) ≫ O.ι := by simp
  have : IsSeparated a := inferInstance
  have : IsClosedImmersion sD := by
    have : IsClosedImmersion (sD ≫ a) := by rw [hsDsec]; infer_instance
    exact .of_comp sD a
  have hsDcontains : Set.range Z.ι ⊆ Set.range sD := by
    rintro d ⟨w, rfl⟩
    refine ⟨q w, ?_⟩
    apply D.ι.isOpenEmbedding.injective
    calc
      D.ι (sD (q w)) = s (q w) := by rw [← hsDfac]; rfl
      _ = j' w := by
        have hWpoint := congrArg (fun t : Z.toScheme ⟶ Y' => t w) hj
        simpa only [Scheme.Hom.comp_apply] using hWpoint.symm
  have hZdense : Dense (Set.range Z.ι) :=
    Z.ι.isOpenEmbedding.isOpen_range.dense ⟨z, ⟨⟨z, hzZ⟩, rfl⟩⟩
  have hsDsurj : Surjective sD := by
    rw [surjective_iff]
    intro d
    have hclosed := (IsClosedImmersion.isClosedEmbedding sD).isClosed_range
    have hclosedRange : closure (Set.range sD) = Set.range sD := hclosed.closure_eq
    have hd : d ∈ closure (Set.range sD) := by
      rw [(hZdense.mono hsDcontains).closure_eq]
      simp
    rw [hclosedRange] at hd
    exact hd
  have : IsIso sD := isIso_of_isClosedImmersion_of_surjective sD
  have : IsIso (sD ≫ a) := by rw [hsDsec]; infer_instance
  have : IsIso a := IsIso.of_isIso_comp_left sD a
  have hIsoLocal : IsIso (g.resLE O D le_rfl) := by simpa [a] using (inferInstance : IsIso a)
  let T : X.Opens := W.ι ''ᵁ O
  have hxT : x ∈ T := by
    change x ∈ W.ι ''ᵁ O
    exact ⟨x', hxO, hWpt⟩
  have hIsoRestrict : IsIso (f ∣_ T) := by
    have hIsoTwice : IsIso ((f ∣_ W) ∣_ O) := by
      simpa [g, ← Scheme.Hom.resLE_eq_morphismRestrict] using hIsoLocal
    exact (MorphismProperty.arrow_mk_iso_iff (P := .isomorphisms _)
      (morphismRestrictRestrict f W O)).mp hIsoTwice
  exact hU.2 hIsoRestrict hxT


end AlgebraicGeometry
