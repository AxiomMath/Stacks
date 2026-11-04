module

public import StacksFrontier.AlgebraicGeometry.Blowup.AffineModelTwistBridge
public import StacksFrontier.AlgebraicGeometry.Blowup.ExceptionalTwistNegativeOne
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceNegativeTwistSections
public import StacksFrontier.AlgebraicGeometry.Blowup.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.TwistedPullbackTerms
public import StacksFrontier.AlgebraicGeometry.AmpleGlobalGeneration.Twist
public import StacksFrontier.AlgebraicGeometry.AmpleWire.UnitStalk
public import StacksFrontier.AlgebraicGeometry.Surfaces.ExceptionalCurveTwistGenerators
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.ClosedPointTrivialization
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.Main
public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.StalkAtCentre
public import StacksFrontier.AlgebraicGeometry.Modules.SectionsTransportAlongIso
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# `𝒪_X ⟶ b_*𝒪_{X'}(E)` is invertible for the blowup of a regular local surface

Let `(A, 𝔪)` be a regular local ring of dimension two, let `X = Spec A` and let
`b : X' ⟶ X` be the blowing up of `X` in `𝔪`, with exceptional divisor `E`. Multiplication by the
canonical section of `𝒪_{X'}(E)` gives, by adjunction, a map

`α : 𝒪_X ⟶ b_*𝒪_{X'}(E)`

and this file proves that `α` is invertible, with no hypothesis beyond regularity and the
dimension. It is the assembly of the four steps the argument is split into.

## The four steps

1. *Away from the centre* `α` is invertible with no arithmetic input at all: the blowup is an
   isomorphism over the complement of the centre and the canonical section is invertible there.
   This is `Stacks.BlowupTwistUnit.isIso_pullback_exceptionalTwistUnitComparison` together with
   `Stacks.BlowupTwistUnit.isIso_pullback_canonicalSectionHom_exceptionalIdeal`.
2. *At the centre* the question is one stalk, and
   `Stacks.BlowupTwistUnit.isIso_of_isIso_restrict_of_stalk_free` reduces it to the freeness of
   rank one of the two stalks there.
3. *The rank-one trivializations.* The stalk of `𝒪_X` at any point is the local ring there,
   `Stacks.Ample.unitStalkEquiv`, and the stalk of `b_*𝒪_{X'}(E)` at the closed point is `A`
   because its global sections are: that is part (4) of
   [Stacks, Tag 0AGS] in degree `-1`, where the exponent `max(0, n)` is `0` and the answer is
   `𝔪⁰ = A`. The passage from sections to stalk is
   `Stacks.BlowupTwistUnit.stalkTrivializationOfSections`, the closed point of the spectrum of a
   local ring having no proper open neighbourhood.
4. *The arithmetic* that turns the two trivializations into invertibility of the stalk is
   `Stacks.BlowupTwistUnit.bijective_of_forall_notMem_isPrime`, through
   `Stacks.BlowupTwistUnit.isIso_stalk_of_forall_ne`.

The centre is the single closed point of `Spec A` — `Stacks.BlowupTwistUnit.support_centre` —
which is what makes step 2 applicable with the open taken to be the complement of the centre.

## Main definitions

The elided prefix is `Stacks.BlowupTwistUnit`.

* `centre`: the ideal sheaf on `Spec A` cut out by the maximal ideal.
* `exceptionalTwistPushforward` and `exceptionalTwistComparison`: `b_*𝒪_{X'}(E)` and the
  comparison `α`.
* `exceptionalSectionsEquivOfRegular`: **`Γ(X', 𝒪_{X'}(E)) ≅ A` as `A`-modules**, part (4) of
  [Stacks, Tag 0AGS] in degree `-1` read through the two identifications of the twisting sheaves.
* `exceptionalSectionsTrivializationOfRegular`: the same over `Γ(X, ⊤)`.

## Main results

* `Stacks.BlowupTwistUnit.support_centre`: **the centre is the closed point.**
* `Stacks.BlowupTwistUnit.isIso_exceptionalTwistComparison_of_stalk_free`: **`α` is invertible**
  for an arbitrary centre supported at one point with no proper open neighbourhood, given a
  rank-one trivialization of the global sections of `b_*𝒪_{X'}(E)`.
* `Stacks.BlowupTwistUnit.isIso_exceptionalTwistComparison_regularLocal`: **`α` is invertible for
  the blowup of a regular local ring of dimension two in its maximal ideal**, with nothing
  assumed.

## Implementation notes

**No `@[stacks]` attribute is attached to anything here.** The statement proved is `𝒪_X = b_*
𝒪_{X'}(E)`, which the Stacks Project does not state as a lemma of its own: it is part (4) of
[Stacks, Tag 0AGS] at `n = -1` combined with part (3) of [Stacks, Tag 02OS] identifying
`𝒪_{X'}(-1)` with `𝒪_{X'}(E)`, and part (4) is already registered, on
`Stacks.Blowup.bijective_maxSections_maximalIdeal`, which is the input used here. Nothing here is
[Stacks, Tag 0B4T], whose statement is the existence of a map
`(Ω^r_{X/Spec A₀})^{**} ⟶ ω_X` along a sequence of blowups in closed points; see the module
docstring of
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Boundedness/TopDifferentialsToDualizing.lean`
for the shape that statement takes and for the inputs it still carries.

**The namespace is `Stacks.BlowupTwistUnit`.** Inside `Stacks.Blowup` the names
`exceptionalIdeal`, `blowUpToBase` and `blowUp` resolve to `Stacks.Blowup`'s own affine-model
versions, which are *different* schemes from the `AlgebraicGeometry` ones this file is about, so
every such name is written out fully qualified.

## References

* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction Stacks.RingedSpace
open Stacks.ModuleStalkSpecialization

universe u

namespace Stacks.BlowupTwistUnit

-- An invertible `𝒪_X`-module is quasi-coherent.  Registered for instance search here so that
-- quasi-coherence of `𝒪_{X'}(E)`, and through [Stacks, Tag 01LC] of its direct image, is found
-- rather than assumed: `isQuasicoherent_of_isInvertibleModule` is a theorem, so without this the
-- chain does not run.
attribute [local instance] Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule

/-! ### The comparison map of the exceptional twist, named -/

variable {X : Scheme.{u}} (M : X.IdealSheafData)

/-- The direct image `b_*𝒪_{X'}(E)` of the exceptional twist of a blowing up, as an
`𝒪_X`-module. -/
abbrev exceptionalTwistPushforward : X.Modules :=
  (Scheme.Modules.pushforward (AlgebraicGeometry.blowUpToBase M)).obj
    (Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal M))

/-- The comparison map `α : 𝒪_X ⟶ b_*𝒪_{X'}(E)`, the adjoint transpose of multiplication by the
canonical section of `𝒪_{X'}(E)`. -/
abbrev exceptionalTwistComparison :
    Stacks.Ample.unitModule X ⟶ exceptionalTwistPushforward M :=
  Stacks.DeRham.BlowupTwist.twistUnitComparison (AlgebraicGeometry.blowUpToBase M)
    (Stacks.Divisors.invertibleSheaf' (AlgebraicGeometry.exceptionalIdeal M))
    (Stacks.Divisors.canonicalSectionHom (AlgebraicGeometry.exceptionalIdeal M))

/-! ### Invertibility from a trivialization of the global sections -/

/-- **A morphism of quasi-coherent modules invertible outside one point is invertible**, as soon
as the target's module of global sections is free of rank one over `Γ(X, ⊤)`, the source's stalk
is free of rank one over the local ring, and that point has no proper open neighbourhood, the
local ring there being Noetherian of Krull dimension at least two.

This is `Stacks.BlowupTwistUnit.isIso_of_isIso_restrict_of_stalk_free` with the target's rank-one
trivialization of the stalk supplied from the global sections by
`Stacks.BlowupTwistUnit.stalkTrivializationOfSections`. The point of stating it is that a theorem
computing `H⁰` delivers that trivialization on sections, over `Γ(X, ⊤)`, while the stalk criterion
asks for it over the local ring. The source's is left at the stalk, because the only case the
development meets is `𝒪_X`, where `Stacks.Ample.unitStalkEquiv` already supplies it. -/
theorem isIso_of_isIso_restrict_of_sections_free {F G : X.Modules} [F.IsQuasicoherent]
    [G.IsQuasicoherent] (φ : F ⟶ G) (w : X) (V : X.Opens)
    (hV : IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ))
    (hVw : ∀ y : X, y ≠ w → y ∈ V)
    (hw : ∀ U : X.Opens, w ∈ U → U = ⊤)
    [IsNoetherianRing (X.presheaf.stalk w)]
    (hdim : 2 ≤ ringKrullDim (X.presheaf.stalk w))
    (d : letI := stalkModule F w
      F.presheaf.stalk w ≃ₗ[X.presheaf.stalk w] X.presheaf.stalk w)
    (e : Γ(G, (⊤ : X.Opens)) ≃ₗ[Γ(X, (⊤ : X.Opens))] Γ(X, (⊤ : X.Opens))) :
    IsIso φ :=
  isIso_of_isIso_restrict_of_stalk_free φ w V hV hVw hdim d
    (stalkTrivializationOfSections G w hw e)

/-- **The comparison map `𝒪_X ⟶ b_*𝒪_{X'}(E)` restricts to an isomorphism over an open of the
base disjoint from the centre over which the blowup is an isomorphism.** Over such an open the
canonical section of `𝒪_{X'}(E)` is invertible
(`Stacks.BlowupTwistUnit.isIso_pullback_canonicalSectionHom_exceptionalIdeal`) and
`Stacks.BlowupTwistUnit.isIso_pullback_exceptionalTwistUnitComparison` applies;
`Stacks.AffineProjectionFormula.isIso_openRestrictHom_iff` passes from the inverse image to the
restriction. -/
theorem isIso_restrictFunctor_exceptionalTwistComparison (V : X.Opens)
    [IsIso (AlgebraicGeometry.blowUpToBase M ∣_ V)]
    (hV : Disjoint ((V : Set X)) ((M.support : Set X))) :
    IsIso ((Scheme.Modules.restrictFunctor V.ι).map (exceptionalTwistComparison M)) :=
  (Stacks.AffineProjectionFormula.isIso_openRestrictHom_iff V _).mpr
    (isIso_pullback_exceptionalTwistUnitComparison M V
      (isIso_pullback_canonicalSectionHom_exceptionalIdeal M V hV))

/-- **The comparison map `𝒪_X ⟶ b_*𝒪_{X'}(E)` is invertible** when the centre is supported at a
single point `w` which has no proper open neighbourhood, the local ring at `w` is Noetherian of
Krull dimension at least two, and the global sections of `b_*𝒪_{X'}(E)` are free of rank one
over `Γ(X, ⊤)`.

Away from the centre the blowup is an isomorphism and the canonical section is invertible, so
`Stacks.BlowupTwistUnit.isIso_restrictFunctor_exceptionalTwistComparison` applies on the
complement of the centre. At `w` the two stalks are free of rank one — the one of `𝒪_X` by
`Stacks.Ample.unitStalkEquiv`, the one of `b_*𝒪_{X'}(E)` from the hypothesis — and
`Stacks.BlowupTwistUnit.isIso_of_isIso_restrict_of_sections_free` concludes.

Quasi-coherence of the direct image is [Stacks, Tag 01LC],
`AlgebraicGeometry.pushforward_isQuasicoherent`, which is why the blowup is asked to be
quasi-compact and quasi-separated; quasi-coherence of `𝒪_{X'}(E)` itself is its invertibility,
the exceptional ideal being an effective Cartier divisor. -/
theorem isIso_exceptionalTwistComparison_of_stalk_free (w : X)
    (hsupp : ∀ x : X, x ∈ M.support → x = w)
    (hw : ∀ V : X.Opens, w ∈ V → V = ⊤)
    [IsNoetherianRing (X.presheaf.stalk w)]
    (hdim : 2 ≤ ringKrullDim (X.presheaf.stalk w))
    [QuasiCompact (AlgebraicGeometry.blowUpToBase M)]
    [QuasiSeparated (AlgebraicGeometry.blowUpToBase M)]
    (e : Γ(exceptionalTwistPushforward M, (⊤ : X.Opens))
      ≃ₗ[Γ(X, (⊤ : X.Opens))] Γ(X, (⊤ : X.Opens))) :
    IsIso (exceptionalTwistComparison M) := by
  have : Stacks.Divisors.IsEffectiveCartierDivisor (AlgebraicGeometry.exceptionalIdeal M) :=
    Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal M
  have : (Stacks.Ample.unitModule X).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohPushforward.isQuasicoherent_unit X
  have : (show (AlgebraicGeometry.blowUp M).Modules from
      Stacks.Divisors.invertibleSheaf'
        (AlgebraicGeometry.exceptionalIdeal M)).IsQuasicoherent :=
    Stacks.AmpleGlobalGeneration.isQuasicoherent_of_isInvertibleModule _
  have : (exceptionalTwistPushforward M).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent (AlgebraicGeometry.blowUpToBase M) _
  have hdisj : Disjoint (((M.support.compl : X.Opens) : Set X)) ((M.support : Set X)) := by
    rw [show (((M.support.compl : X.Opens)) : Set X) = ((M.support : Set X))ᶜ from rfl]
    exact disjoint_compl_left
  have hVw : ∀ y : X, y ≠ w → y ∈ (M.support.compl : X.Opens) := by
    intro y hy
    have hmem : y ∉ ((M.support : Set X)) := fun hmem ↦ hy (hsupp y hmem)
    exact hmem
  exact isIso_of_isIso_restrict_of_sections_free (exceptionalTwistComparison M) w
    (M.support.compl : X.Opens)
    (isIso_restrictFunctor_exceptionalTwistComparison M (M.support.compl : X.Opens) hdisj)
    hVw hw hdim (Stacks.Ample.unitStalkEquiv X w) e

/-! ### The centre of the blowing up of a local ring in its maximal ideal -/

variable (A : Type u) [CommRing A]

/-- The ideal sheaf on `Spec A` cut out by the maximal ideal of a local ring `A`: the centre of
the blowing up [Stacks, Tag 0AGS] is about. -/
abbrev centre [IsLocalRing A] : (Spec (CommRingCat.of A)).IdealSheafData :=
  Stacks.Blowup.AffineModel.specIdealSheaf (IsLocalRing.maximalIdeal A)

/-- **The support of the ideal sheaf on `Spec A` cut out by an ideal `I ⊆ A` is the zero locus of
`I`.** The ideal sheaf is `Scheme.IdealSheafData.ofIdealTop` at the transport of `I` along the
counit `Γ(Spec A, ⊤) ≅ A`, whose support is the zero locus of that transport by
`Scheme.IdealSheafData.coe_support_ofIdealTop`; the counit being an isomorphism, contracting the
transport returns `I`. -/
theorem coe_support_specIdealSheaf (I : Ideal A) :
    ((Stacks.Blowup.AffineModel.specIdealSheaf I).support :
        Set (Spec (CommRingCat.of A))) = PrimeSpectrum.zeroLocus (I : Set A) := by
  rw [Stacks.Blowup.AffineModel.specIdealSheaf,
    Scheme.IdealSheafData.coe_support_ofIdealTop, AlgebraicGeometry.Spec_zeroLocus]
  show PrimeSpectrum.zeroLocus
    ((Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
      (Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom I) : Ideal A) : Set A) = _
  have hb := ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv
  rw [Ideal.comap_map_of_surjective' _ hb.2 I, (RingHom.injective_iff_ker_eq_bot _).mp hb.1]
  simp

/-- **The centre of the blowing up of a local ring in its maximal ideal is its closed point.**
The support is the zero locus of the maximal ideal by
`Stacks.BlowupTwistUnit.coe_support_specIdealSheaf`, and the zero locus of a maximal ideal is the
single point it names, `PrimeSpectrum.zeroLocus_eq_singleton`. -/
theorem support_centre [IsLocalRing A] :
    (((centre A).support) : Set (Spec (CommRingCat.of A)))
      = {IsLocalRing.closedPoint A} := by
  rw [centre, coe_support_specIdealSheaf A (IsLocalRing.maximalIdeal A),
    PrimeSpectrum.zeroLocus_eq_singleton]
  rfl

/-- Every point of the centre is the closed point, the form
`Stacks.BlowupTwistUnit.isIso_exceptionalTwistComparison_of_stalk_free` consumes. -/
theorem eq_closedPoint_of_mem_support_centre [IsLocalRing A]
    (x : Spec (CommRingCat.of A)) (hx : x ∈ (centre A).support) :
    x = IsLocalRing.closedPoint A := by
  have h : x ∈ (((centre A).support) : Set (Spec (CommRingCat.of A))) := hx
  rw [support_centre A] at h
  exact h

/-! ### The global sections of the exceptional twist over a regular local surface -/

/-- `I^{max(0,-1)} = I⁰ = ⊤`: the exponent part (4) of [Stacks, Tag 0AGS] carries in degree
`-1`. -/
theorem pow_toNat_max_zero_neg_one (I : Ideal A) : I ^ (max 0 (-1 : ℤ)).toNat = ⊤ := by
  rw [show (max 0 (-1 : ℤ)).toNat = 0 from by decide, pow_zero, Ideal.one_eq_top]

/-- **`Γ(X', 𝒪_{X'}(E)) ≅ A` as `A`-modules**, for `X' ⟶ Spec A` the blowing up of a regular
local ring of dimension two in its maximal ideal.

This is part (4) of [Stacks, Tag 0AGS] in degree `-1`,
`Stacks.Blowup.bijective_maxSections_maximalIdeal`, read through two identifications: the
exceptional twist is the degree `-1` twist by
`AlgebraicGeometry.exceptionalInvertibleSheafIsoBlowUpTwistNegOne` (part (3) of
[Stacks, Tag 02OS] and part (1) of [Stacks, Tag 01WX]), and the blowup of `Spec A` in the sheaf
of ideals `𝔪` defines is the affine model `Proj (A[𝔪t])` over `Spec A`, carrying the one twisting
sheaf onto the other, by `Stacks.Blowup.AffineModel.specProjIso` and
`Stacks.Blowup.AffineModel.specProjTwistIso`. The sections are transported along that
isomorphism of schemes over `A` by
`AlgebraicGeometry.globalSectionsOverPullbackIso`. In degree `-1` the exponent of part (4) is
`max(0, -1) = 0`, so the source of the canonical map is `𝔪⁰ = A`. -/
def exceptionalSectionsEquivOfRegular [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    ((AlgebraicGeometry.globalSectionsOver
        (AlgebraicGeometry.blowUpToBase (centre A))).obj
      (Stacks.Divisors.invertibleSheaf'
        (AlgebraicGeometry.exceptionalIdeal (centre A)))) ≃ₗ[A] A :=
  (((AlgebraicGeometry.globalSectionsOver
            (AlgebraicGeometry.blowUpToBase (centre A))).mapIso
          (AlgebraicGeometry.exceptionalInvertibleSheafIsoBlowUpTwistNegOne
            (centre A))).toLinearEquiv.trans
      (AlgebraicGeometry.globalSectionsOverPullbackIso
          (Stacks.Blowup.AffineModel.specProjIso (IsLocalRing.maximalIdeal A))
          (AlgebraicGeometry.blowUpToBase (centre A))
          (Stacks.Blowup.toSpec (IsLocalRing.maximalIdeal A))
          (Stacks.Blowup.AffineModel.specProjIso_hom_blowUpToBase
            (IsLocalRing.maximalIdeal A))
          (Stacks.Blowup.AffineModel.specProjTwistIso
            (IsLocalRing.maximalIdeal A) (-1))).toLinearEquiv).trans
    ((LinearEquiv.ofBijective (Stacks.Blowup.maxSections (IsLocalRing.maximalIdeal A) (-1))
        (Stacks.Blowup.bijective_maxSections_maximalIdeal A hdim (-1))).symm.trans
      ((LinearEquiv.ofEq _ ⊤
          (pow_toNat_max_zero_neg_one A (IsLocalRing.maximalIdeal A))).trans
        Submodule.topEquiv))

/-- `Stacks.BlowupTwistUnit.exceptionalSectionsEquivOfRegular` over `Γ(Spec A, ⊤)` instead of over
`A`: the two rings of scalars are identified by the counit `Γ(Spec A, ⊤) ≅ A`, which is what
`Stacks.BlowupTwistUnit.transportTrivialization` carries the trivialization along. The `A`-action
on the sections of a direct image over `Spec A` is the `Γ(Spec A, ⊤)`-action read through that
counit, by the definition of `AlgebraicGeometry.globalSectionsOver`, so the compatibility is an
identity. -/
def exceptionalSectionsTrivializationOfRegular [IsRegularLocalRing A]
    (hdim : ringKrullDim A = 2) :
    Γ(exceptionalTwistPushforward (centre A), (⊤ : (Spec (CommRingCat.of A)).Opens))
      ≃ₗ[Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens))]
        Γ(Spec (CommRingCat.of A), (⊤ : (Spec (CommRingCat.of A)).Opens)) :=
  letI : Module A Γ(exceptionalTwistPushforward (centre A),
      (⊤ : (Spec (CommRingCat.of A)).Opens)) :=
    inferInstanceAs (Module A ((AlgebraicGeometry.globalSectionsOver
      (AlgebraicGeometry.blowUpToBase (centre A))).obj
        (Stacks.Divisors.invertibleSheaf'
          (AlgebraicGeometry.exceptionalIdeal (centre A)))))
  transportTrivialization
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
    (fun _ _ ↦ rfl) (exceptionalSectionsEquivOfRegular A hdim)

/-! ### The assembly -/

/-- **`𝒪_X ⟶ b_*𝒪_{X'}(E)` is invertible for the blowing up of a regular local ring of dimension
two in its maximal ideal.** Nothing is assumed: the four steps are
`Stacks.BlowupTwistUnit.isIso_pullback_exceptionalTwistUnitComparison` away from the centre,
`Stacks.BlowupTwistUnit.isIso_of_isIso_restrict_of_stalk_free` at it,
`Stacks.BlowupTwistUnit.exceptionalSectionsTrivializationOfRegular` for the rank-one
trivialization there — part (4) of [Stacks, Tag 0AGS] in degree `-1` — and
`Stacks.BlowupTwistUnit.bijective_of_forall_notMem_isPrime` for the arithmetic.

The local ring at the closed point is `A` itself,
`AlgebraicGeometry.forall_eq_top_of_mem_of_isLocalRing` making the germ at `⊤` an isomorphism, so
the Noetherian hypothesis and the dimension bound transport from `A`. -/
theorem isIso_exceptionalTwistComparison_regularLocal (A : Type u) [CommRing A]
    [IsRegularLocalRing A] (hdim : ringKrullDim A = 2) :
    IsIso (exceptionalTwistComparison (centre A)) := by
  have hw : ∀ V : (Spec (CommRingCat.of A)).Opens,
      IsLocalRing.closedPoint A ∈ V → V = ⊤ :=
    AlgebraicGeometry.forall_eq_top_of_mem_of_isLocalRing (CommRingCat.of A)
  let σ : A ≃+* (Spec (CommRingCat.of A)).presheaf.stalk (IsLocalRing.closedPoint A) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.trans
      (stalkRingEquivTop (X := Spec (CommRingCat.of A)) (IsLocalRing.closedPoint A) hw)
  have : IsNoetherianRing
      ((Spec (CommRingCat.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) :=
    isNoetherianRing_of_ringEquiv A σ
  have hdim' : 2 ≤ ringKrullDim
      ((Spec (CommRingCat.of A)).presheaf.stalk (IsLocalRing.closedPoint A)) := by
    rw [← ringKrullDim_eq_of_ringEquiv σ, hdim]
  exact isIso_exceptionalTwistComparison_of_stalk_free (centre A)
    (IsLocalRing.closedPoint A) (eq_closedPoint_of_mem_support_centre A) hw hdim'
    (exceptionalSectionsTrivializationOfRegular A hdim)

end Stacks.BlowupTwistUnit

end
