module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.RestrictionBaseRingLinear
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.SupportedDerivedModules
public import StacksFrontier.CategoryTheory.Center.Shift

/-!
# Support of a derived module killed by a scalar

Let `X` be a scheme, `a ∈ Γ(X, 𝒪_X)` and `E` an object of `D(𝒪_X)` on which `a` acts as zero,
that is `a • 𝟙 E = 0` for the `Γ(X, 𝒪_X)`-linear structure
`AlgebraicGeometry.Scheme.linearOfRingHom` of the identity ring map. Then the cohomology of `E`
is supported on the zero locus of `a`: outside that zero locus, on the basic open `X_a`, the
section `a` has become invertible, so it acts invertibly on the restriction of `E`, and an
object on which zero acts invertibly is a zero object.

Taking the hypothesis for each member of a family `(g_i)` of global sections gives the support
condition on the zero locus of the family, which is how the condition is produced in
[Stacks, Tag 08EK]: the iterated cone `C_{i+1} = cone(g_i · 1_{C_i})` is killed by `g_i ^ 2`
([Stacks, Tag 05QP]), so `C_s` is killed by a power of each `g_i` and is therefore supported on
`V(g_1, …, g_s)`.

## Main results

* `CategoryTheory.CatCenter.isZero_of_isUnit_algebraMap`: an object of a linear category on
  which a scalar acts both as zero and invertibly is a zero object.
* `CategoryTheory.CatCenter.isUnit_algebraMap_derivedCategory`: a scalar acting invertibly on an
  abelian category acts invertibly on its derived category.
* `Stacks.DerivedQCoh.cohomologySupportedOn_compl_basicOpen_of_smul_id_eq_zero`: the support
  statement for one global section.
* `Stacks.DerivedQCoh.cohomologySupportedOn_zeroLocus_of_smul_id_eq_zero`: the support statement
  on the zero locus of a set of global sections, each of which has a power killing `E`.

## Implementation notes

*Why the centre of the category appears.* The scalar `a` is not a unit of `Γ(X, 𝒪_X)`, so the
elementary argument "`a` invertible, hence `a • 𝟙 = 0` forces `𝟙 = 0`" is unavailable at the
base ring. What is invertible is the *endomorphism* `a` defines, and the ring that endomorphism
lives in is `CategoryTheory.CatCenter`, the centre `End (𝟭 C)` of the category: an `R`-linear
structure is a ring map `R →+* CatCenter C` (`CategoryTheory.Linear.ofRingMorphism` and its
inverse `CategoryTheory.Linear.toCatCenter`, which is the `algebraMap` of
`CategoryTheory.CatCenter.instAlgebra`), and invertibility travels along a ring map. So the
restriction of `a` to `X_a`, a unit of `Γ(X_a, 𝒪_X)` by
`AlgebraicGeometry.RingedSpace.isUnit_of_isUnit_germ`, gives a unit of the centre of the
`𝒪_{X_a}`-modules, hence -- `CategoryTheory.CatCenter.homologicalComplexAlgHom` and
`CategoryTheory.CatCenter.localization_algebraMap` passing an `algebraMap` to an `algebraMap` --
a unit of the centre of `D(𝒪_{X_a})`.

*Carrying one base ring across the restriction.* The scalar is kept in `Γ(X, 𝒪_X)` on both
sides of the restriction, the ring map into the sections over the open changing instead; that is
the arrangement `Stacks.DerivedQCoh.derivedRestrict_linear` is stated in, and it is what makes
`a • 𝟙 E = 0` restrict to `a • 𝟙 (E|_{X_a}) = 0` with the same scalar.

`CategoryTheory.CatCenter.algebraMap_ofRingMorphism` below is the `algebraMap` reading of
`CategoryTheory.Linear.toCatCenter_ofRingMorphism_id` of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/DerivedCompletionRinged/Pushforward.lean`, which
is its case `R = CatCenter C` with `φ` the identity; the two should be collapsed onto the
general statement when that file is next touched.

## References

* [Stacks Project, Tag 08DA](https://stacks.math.columbia.edu/tag/08DA)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Duality.OpenImmersion (derivedRestrict)

universe w v u

namespace CategoryTheory.CatCenter

/-- **For the linear structure attached to a ring map into the centre, the central element a
scalar defines is its image.** -/
theorem algebraMap_ofRingMorphism {R : Type*} [CommRing R] {C : Type u} [Category.{v} C]
    [Preadditive C] (φ : R →+* CatCenter C) (r : R) :
    letI := Linear.ofRingMorphism φ
    algebraMap R (CatCenter C) r = φ r := by
  let := Linear.ofRingMorphism φ
  refine CatCenter.ext _ _ fun X => ?_
  exact Category.comp_id _

/-- **An object on which a scalar acts both as zero and invertibly is a zero object.** The
scalar acts on `Y` by the component at `Y` of the central element it defines; if that central
element is a unit of the centre, composing with the component of its inverse turns the vanishing
of that component into the vanishing of the identity of `Y`. -/
theorem isZero_of_isUnit_algebraMap {R : Type*} [CommRing R] {C : Type u} [Category.{v} C]
    [Preadditive C] [Linear R C] {Y : C} {r : R}
    (hr : IsUnit (algebraMap R (CatCenter C) r)) (hzero : r • 𝟙 Y = 0) : IsZero Y := by
  obtain ⟨u, hu⟩ := hr
  have happ : (algebraMap R (CatCenter C) r).app Y = 0 := by
    rw [algebraMap_app]
    exact hzero
  have hmul : (((u⁻¹ : (CatCenter C)ˣ) : CatCenter C) *
      ((u : (CatCenter C)ˣ) : CatCenter C)).app Y = 0 := by
    rw [mul_app, hu, happ, Limits.comp_zero]
  rw [u.inv_mul] at hmul
  exact (IsZero.iff_id_eq_zero Y).2 hmul

/-- **A scalar acting invertibly on an abelian category acts invertibly on its derived
category.** The central element the scalar defines acts degreewise on cochain complexes and
descends to the localization; both operations take the central element of a scalar to the
central element of the same scalar, and both are ring maps, so they carry a unit to a unit. -/
theorem isUnit_algebraMap_derivedCategory {R : Type*} [CommRing R] {C : Type u}
    [Category.{v} C] [Abelian C] [Linear R C] [HasDerivedCategory.{w} C] {r : R}
    (hr : IsUnit (algebraMap R (CatCenter C) r)) :
    IsUnit (algebraMap R (CatCenter (DerivedCategory C)) r) := by
  have hcx : IsUnit (algebraMap R (CatCenter (CochainComplex C ℤ)) r) := by
    rw [← (homologicalComplexAlgHom (C := C) (ComplexShape.up ℤ) R).commutes r]
    exact hr.map (homologicalComplexAlgHom (C := C) (ComplexShape.up ℤ) R).toRingHom
  have hloc := hcx.map (localizationRingHom (DerivedCategory.Q (C := C))
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)))
  rwa [show localizationRingHom (DerivedCategory.Q (C := C))
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (algebraMap R (CatCenter (CochainComplex C ℤ)) r) =
      algebraMap R (CatCenter (DerivedCategory C)) r from
    localization_algebraMap _ _ R r] at hloc

end CategoryTheory.CatCenter

namespace Stacks.DerivedQCoh

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A section of the structure sheaf whose image in the global sections is a unit gives a unit
of the centre of the category of modules.** -/
theorem isUnit_algebraMap_catCenter_modules (Y : Scheme.{u}) (A : Type u) [CommRing A]
    (φ : A →+* Γ(Y, ⊤)) {a : A} (ha : IsUnit (φ a)) :
    letI : Linear A Y.Modules := Scheme.linearOfRingHom Y A φ
    IsUnit (algebraMap A (CatCenter Y.Modules) a) := by
  let : Linear A Y.Modules := Scheme.linearOfRingHom Y A φ
  let T : Γ(Y, ⊤) →+* CatCenter Y.Modules :=
    Stacks.SheafOfModules.terminalSectionRingHom Y.ringCatSheaf ⊤ isTerminalTop
  have hT : algebraMap A (CatCenter Y.Modules) a = T (φ a) :=
    CatCenter.ext _ _ fun _ => Category.comp_id _
  rw [hT]
  exact ha.map T

/-- **The restriction of a global section to its own basic open is a unit.** The basic open of
the restricted section is the preimage of the basic open, which is the whole of the open
subscheme, so every germ of the restricted section is a unit. -/
theorem isUnit_ι_appTop_basicOpen {X : Scheme.{u}} (a : Γ(X, ⊤)) :
    IsUnit ((X.basicOpen a).ι.appTop.hom a) := by
  have hpre := (X.basicOpen a).ι.preimage_basicOpen_top a
  rw [Scheme.Opens.ι_preimage_self] at hpre
  refine (X.basicOpen a).toScheme.toRingedSpace.isUnit_of_isUnit_germ ⊤ _ fun x hx => ?_
  have hmem : x ∈ (X.basicOpen a).toScheme.basicOpen ((X.basicOpen a).ι.appTop.hom a) := by
    rw [← hpre]
    exact hx
  exact (RingedSpace.mem_basicOpen _ _ x hx).1 hmem

/-- **A derived module killed by a global section restricts to zero on the basic open of that
section.** Restriction to the basic open is `Γ(X, 𝒪_X)`-linear
(`Stacks.DerivedQCoh.derivedRestrict_linear`), so the scalar still kills the restriction; and
over the basic open the scalar has become a unit, so it acts invertibly. -/
theorem isZero_derivedRestrict_basicOpen_of_smul_id_eq_zero {X : Scheme.{u}} (a : Γ(X, ⊤))
    (E : DerivedCategory X.Modules)
    (h : letI : Linear Γ(X, ⊤) X.Modules :=
        Scheme.linearOfRingHom X Γ(X, ⊤) (RingHom.id Γ(X, ⊤))
      a • 𝟙 E = 0) :
    IsZero ((Scheme.Modules.restrictFunctor (X.basicOpen a).ι).mapDerivedCategory.obj E) := by
  let : Linear Γ(X, ⊤) X.Modules := Scheme.linearOfRingHom X Γ(X, ⊤) (RingHom.id Γ(X, ⊤))
  let : Linear Γ(X, ⊤) (X.basicOpen a).toScheme.Modules :=
    Scheme.linearOfRingHom (X.basicOpen a).toScheme Γ(X, ⊤)
      (((X.basicOpen a).ι.appTop).hom.comp (RingHom.id Γ(X, ⊤)))
  let : Functor.Linear Γ(X, ⊤) (derivedRestrict (X.basicOpen a).ι) :=
    derivedRestrict_linear (X.basicOpen a).ι (RingHom.id Γ(X, ⊤))
  have hzero : a • 𝟙 ((derivedRestrict (X.basicOpen a).ι).obj E) = 0 := by
    have hmap : (derivedRestrict (X.basicOpen a).ι).map (a • 𝟙 E) =
        a • 𝟙 ((derivedRestrict (X.basicOpen a).ι).obj E) := by
      rw [Functor.Linear.map_smul, CategoryTheory.Functor.map_id]
    rw [← hmap, h, CategoryTheory.Functor.map_zero]
  have hunit : IsUnit (algebraMap Γ(X, ⊤)
      (CatCenter (X.basicOpen a).toScheme.Modules) a) :=
    isUnit_algebraMap_catCenter_modules (X.basicOpen a).toScheme Γ(X, ⊤)
      (((X.basicOpen a).ι.appTop).hom.comp (RingHom.id Γ(X, ⊤)))
      (isUnit_ι_appTop_basicOpen a)
  exact CatCenter.isZero_of_isUnit_algebraMap
    (CatCenter.isUnit_algebraMap_derivedCategory hunit) hzero

/-- **A derived module killed by a global section has its cohomology supported on the zero locus
of that section.** -/
theorem cohomologySupportedOn_compl_basicOpen_of_smul_id_eq_zero {X : Scheme.{u}} (a : Γ(X, ⊤))
    (E : DerivedCategory X.Modules)
    (h : letI : Linear Γ(X, ⊤) X.Modules :=
        Scheme.linearOfRingHom X Γ(X, ⊤) (RingHom.id Γ(X, ⊤))
      a • 𝟙 E = 0) :
    CohomologySupportedOn X.ringCatSheaf ((X.basicOpen a : Set X)ᶜ) E :=
  cohomologySupportedOn_compl_opens_of_isZero_derivedRestrict (X.basicOpen a) E
    (isZero_derivedRestrict_basicOpen_of_smul_id_eq_zero a E h)

/-- **A derived module on which every member of a set of global sections has a power acting as
zero has its cohomology supported on the zero locus of that set.** This is the form in which the
support hypothesis of [Stacks, Tag 08EK] is produced: the closed set there is cut out by
finitely many global sections, and the iterated cone built from them is killed by a power of
each. -/
theorem cohomologySupportedOn_zeroLocus_of_smul_id_eq_zero {X : Scheme.{u}}
    (s : Set Γ(X, ⊤)) (E : DerivedCategory X.Modules)
    (h : letI : Linear Γ(X, ⊤) X.Modules :=
        Scheme.linearOfRingHom X Γ(X, ⊤) (RingHom.id Γ(X, ⊤))
      ∀ f ∈ s, ∃ k : ℕ, f ^ k • 𝟙 E = 0) :
    CohomologySupportedOn X.ringCatSheaf (X.zeroLocus (U := ⊤) s) E := by
  let : Linear Γ(X, ⊤) X.Modules := Scheme.linearOfRingHom X Γ(X, ⊤) (RingHom.id Γ(X, ⊤))
  intro n x hx
  obtain ⟨f, hfs, hxf⟩ : ∃ f ∈ s, x ∈ X.basicOpen f := by
    by_contra hcon
    exact hx ((X.mem_zeroLocus_iff s x).2 fun f hf hmem => hcon ⟨f, hf, hmem⟩)
  obtain ⟨k, hk⟩ := h f hfs
  have hk1 : f ^ (k + 1) • 𝟙 E = 0 := by
    have hpow : f ^ (k + 1) = f * f ^ k := by ring
    rw [hpow, mul_smul, hk, smul_zero]
  refine cohomologySupportedOn_compl_basicOpen_of_smul_id_eq_zero (f ^ (k + 1)) E hk1 n x ?_
  have hmem : x ∈ X.basicOpen (f ^ (k + 1)) := by
    rw [X.basicOpen_pow f (Nat.succ_pos k)]
    exact hxf
  exact fun hc => hc hmem

end Stacks.DerivedQCoh

end
