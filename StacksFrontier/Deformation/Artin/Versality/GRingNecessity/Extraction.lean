module

public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.Conclusion
public import StacksFrontier.Deformation.Artin.Versality.GRingNecessity.Versal
public import StacksFrontier.RingTheory.Kaehler.SmoothRingMapsInTheNoetherianCase

/-!
# Residue fields, closed points and affine charts for Stacks Example 98.12.8

Let `Λ` be a Noetherian ring, `𝔪 ⊂ Λ` a maximal ideal, `R = Λ_𝔪^∧`, `Λ → C → R` a
factorization, `𝒳 = 𝒮_F` the category fibred in sets of Stacks Example 98.12.8 and `ξ` its
formal object over `R`. This file collects the geometric and ring theoretic facts used to read
off the datum of the Example (a finite type `Λ`-algebra `A`, a maximal ideal `𝔪_A` over `𝔪` with
`κ(𝔪) = κ(𝔪_A)`, smoothness at `𝔪_A` and `C → A`) from the conclusion of Stacks Lemma 98.12.7:
residue fields of points of schemes over `Spec Λ` as quotients of `Λ`, closed points of complete
local bases isomorphic to `Λ_𝔪^∧`, local rings of `Spec Λ`, affine charts around a point over `𝔪`
of a scheme factoring through `S'`, and the maximal ideal `𝔪_A`.

## Main definitions

* `Deformation.Artin.GRingNecessity.residueAlgebraMap`: the map `Λ → κ(x)` for a point `x` of a
  scheme over `Spec Λ`.
* `Deformation.Artin.GRingNecessity.specClosedPoint`: the closed point of the spectrum of a local
  ring, as a point of the scheme.
* `Deformation.Artin.GRingNecessity.stalkLift`: the extension of `Λ → T` to a local ring of
  `Spec Λ`.
* `Deformation.Artin.GRingNecessity.quotientEquivResidueField`,
  `Deformation.Artin.GRingNecessity.quotientEquivResidueFieldOfPoint`: residue fields equal to
  `Λ / 𝔪`.
* `Deformation.Artin.GRingNecessity.chartAlgebra`, `Deformation.Artin.GRingNecessity.chartAlgHom`,
  `Deformation.Artin.GRingNecessity.chartResidue`: the `Λ`-algebra `Γ(X, V)` of an affine open
  `V`, the map `C → Γ(X, V)`, and the map `Γ(X, V) → κ(u₀)`.

## Main results

* `Deformation.Artin.GRingNecessity.baseMap_closedPoint`: morphisms of formal objects preserve
  the closed points of the bases.
* `Deformation.Artin.GRingNecessity.toS_closedPoint_of_isCompletionBase`,
  `Deformation.Artin.GRingNecessity.residueAlgebraMap_surjective_of_isCompletionBase`: the closed
  point of a base isomorphic to `Λ_𝔪^∧` lies over `𝔪`, with residue field a quotient of `Λ`.
* `Deformation.Artin.GRingNecessity.exists_affineOpen_chart`: a factorization `X → S'` sends a
  point over `𝔪` into `Spec C`, inside an affine open `V` with `Spec Γ(X, V) → Spec C` over `S`.
* `Deformation.Artin.GRingNecessity.residueField_map_bijective_of_surjective_comp`: for `𝔪_A` the
  kernel of `A → K` with `Λ → K` surjective with kernel `𝔪`, `κ(𝔪) → κ(𝔪_A)` is bijective.

## Implementation notes

An object of `𝒳` over `X` is a factorization `X → S'` of the structure morphism; a point over `𝔪`
is not in the preimage of `U = S ∖ {𝔪}`, so it lies in the preimage of `Spec C`, and any affine
open neighbourhood `V` inside that preimage gives `A = Γ(X, V)`, of finite type over `Λ` when
`X → S` is locally of finite type, with a `Λ`-algebra map `C → A`. The maximal ideal `𝔪_A` is the
kernel of `A → κ(u₀)`; it lies over `𝔪` and has residue field `Λ / 𝔪` as soon as `Λ → κ(u₀)` is
surjective with kernel `𝔪`. Closed points of spectra are stated through `specClosedPoint`, which
has the type of points of the scheme, so that they can be transported along equations of
morphisms of schemes.

## References

* [Stacks Project, Tag 07XI](https://stacks.math.columbia.edu/tag/07XI)
* [Stacks Project, Tag 07XH](https://stacks.math.columbia.edu/tag/07XH)
* [Stacks Project, Tag 07XF](https://stacks.math.columbia.edu/tag/07XF)
* [Stacks Project, Tag 02HT](https://stacks.math.columbia.edu/tag/02HT)
-/

@[expose] public noncomputable section

namespace Deformation.Artin.GRingNecessity

open AlgebraicGeometry CategoryTheory IsLocalRing

universe u

/-! ### Residue fields of points over `Spec Λ` -/

section Residue

variable {Λ : Type u} [CommRing Λ]

/-- The `Λ`-algebra structure of the residue field of a point of a scheme over `Spec Λ`. -/
def residueAlgebraMap {X : Scheme.{u}} (f : X ⟶ Spec (.of Λ)) (x : X) :
    Λ →+* X.residueField x :=
  (Spec.preimage (X.fromSpecResidueField x ≫ f)).hom

/-- The spectrum of `Λ → κ(x)` is `Spec κ(x) → X → Spec Λ`. -/
theorem specMap_residueAlgebraMap {X : Scheme.{u}} (f : X ⟶ Spec (.of Λ)) (x : X) :
    Spec.map (CommRingCat.ofHom (residueAlgebraMap f x)) = X.fromSpecResidueField x ≫ f := by
  simp [residueAlgebraMap]

/-- The kernel of `Λ → κ(x)` is the prime of `Λ` below `x`. -/
theorem ker_residueAlgebraMap {X : Scheme.{u}} (f : X ⟶ Spec (.of Λ)) (x : X) :
    RingHom.ker (residueAlgebraMap f x) = (f x).asIdeal := by
  have h : (Spec.map (CommRingCat.ofHom (residueAlgebraMap f x)))
      (closedPoint (X.residueField x)) = f x :=
    (congrArg (fun φ => φ (closedPoint (X.residueField x)))
      (specMap_residueAlgebraMap f x)).trans
      ((Scheme.Hom.comp_apply _ _ _).trans (congrArg f (Scheme.fromSpecResidueField_apply x _)))
  refine Eq.trans ?_ (congrArg PrimeSpectrum.asIdeal h)
  change RingHom.ker (residueAlgebraMap f x) =
    Ideal.comap (residueAlgebraMap f x) (maximalIdeal (X.residueField x))
  rw [IsLocalRing.maximalIdeal_eq_bot, RingHom.ker_eq_comap_bot]

/-- Ring maps are determined by their spectra: if `Spec g ≫ Spec f = Spec h` then
`g ∘ f = h`. -/
private theorem hom_comp_eq_of_specMap_comp_eq {R S T : CommRingCat.{u}} (f : R ⟶ S) (g : S ⟶ T)
    (h : R ⟶ T) (H : Spec.map g ≫ Spec.map f = Spec.map h) : g.hom.comp f.hom = h.hom :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp f g).trans H))

/-- The residue field maps of a morphism over `Spec Λ` are `Λ`-algebra maps. -/
theorem residueFieldMap_comp_residueAlgebraMap {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (fY : Y ⟶ Spec (.of Λ)) (x : X) :
    (φ.residueFieldMap x).hom.comp (residueAlgebraMap fY (φ x)) =
      residueAlgebraMap (φ ≫ fY) x := by
  refine hom_comp_eq_of_specMap_comp_eq (CommRingCat.ofHom (residueAlgebraMap fY (φ x)))
    (φ.residueFieldMap x) (CommRingCat.ofHom (residueAlgebraMap (φ ≫ fY) x)) ?_
  rw [specMap_residueAlgebraMap, ← Category.assoc,
    Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField, Category.assoc]
  exact (specMap_residueAlgebraMap _ _).symm

/-- If `Λ → κ(x)` is surjective, so is `Λ → κ(φ x)`. -/
theorem residueAlgebraMap_surjective_of_comp {X Y : Scheme.{u}} (φ : X ⟶ Y)
    (fY : Y ⟶ Spec (.of Λ)) (x : X)
    (h : Function.Surjective (residueAlgebraMap (φ ≫ fY) x)) :
    Function.Surjective (residueAlgebraMap fY (φ x)) := by
  intro w
  obtain ⟨l, hl⟩ := h ((φ.residueFieldMap x).hom w)
  refine ⟨l, (φ.residueFieldMap x).hom.injective ?_⟩
  rw [← RingHom.comp_apply, residueFieldMap_comp_residueAlgebraMap, hl]

end Residue

/-! ### Closed points of complete local bases -/

section ClosedPoint

/-- The closed point of the spectrum of a local ring, as a point of the scheme. -/
def specClosedPoint (R : Type u) [CommRing R] [IsLocalRing R] : Spec (.of R) := closedPoint R

/-- Every point of an infinitesimal thickening of the closed point maps to the closed point. -/
theorem adicThickeningι_apply {R : Type u} [CommRing R] [IsLocalRing R] (n : ℕ)
    (y : adicThickening R (maximalIdeal R) n) :
    adicThickeningι R (maximalIdeal R) n y = closedPoint R := by
  apply PrimeSpectrum.ext
  change Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1))) (PrimeSpectrum.asIdeal y) =
    maximalIdeal R
  have : (PrimeSpectrum.asIdeal y).IsPrime := PrimeSpectrum.isPrime y
  have hprime : (Ideal.comap (Ideal.Quotient.mk (maximalIdeal R ^ (n + 1)))
      (PrimeSpectrum.asIdeal y)).IsPrime := Ideal.comap_isPrime _ _
  exact ((maximalIdeal.isMaximal R).eq_of_le hprime.ne_top ((hprime.pow_le_iff n.succ_ne_zero).mp
    (Ideal.mk_ker.symm.trans_le (Ideal.comap_mono bot_le)))).symm

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {F : Type*} [Category F]
  {p : F ⥤ BigFppfOver B S hS}

/-- The induced map of complete local bases of a morphism of formal objects preserves the
closed points. -/
theorem baseMap_closedPoint {X Y : FormalObject B S hS p} (h : X ⟶ Y) :
    FormalObject.Hom.baseMap h (specClosedPoint X.base.R) = specClosedPoint Y.base.R := by
  have hb := (FormalObject.Hom.baseMap_spec h).2 0
  have : Nontrivial (X.base.R ⧸ maximalIdeal X.base.R ^ (0 + 1)) :=
    Ideal.Quotient.nontrivial_iff.mpr (by simpa using (maximalIdeal.isMaximal X.base.R).ne_top)
  obtain ⟨pt⟩ : Nonempty (adicThickening X.base.R (maximalIdeal X.base.R) 0) :=
    inferInstanceAs (Nonempty (PrimeSpectrum (X.base.R ⧸ maximalIdeal X.base.R ^ (0 + 1))))
  have e1 := (Scheme.Hom.comp_apply (eqToHom (X.level_eq 0).symm ≫ p.map (h.app 0) ≫
      eqToHom (Y.level_eq 0)).left.hom (adicThickeningι Y.base.R (maximalIdeal Y.base.R) 0)
    pt).trans (adicThickeningι_apply 0 _)
  have e2 := (Scheme.Hom.comp_apply (adicThickeningι X.base.R (maximalIdeal X.base.R) 0)
    (FormalObject.Hom.baseMap h) pt).trans
    (congrArg (FormalObject.Hom.baseMap h) (adicThickeningι_apply 0 pt))
  exact e2.symm.trans ((congrArg (fun φ => φ pt) hb).symm.trans e1)

/-- If `Λ → R → κ(R)` is surjective, so is `Λ → κ` at the closed point of `Spec R`. -/
theorem residueAlgebraMap_specMap_surjective {Λ R : Type u} [CommRing Λ] [CommRing R]
    [IsLocalRing R] (φ : Λ →+* R) (hφ : Function.Surjective ((residue R).comp φ)) :
    Function.Surjective
      (residueAlgebraMap (Spec.map (CommRingCat.ofHom φ)) (specClosedPoint R)) := by
  change Function.Surjective (residueAlgebraMap (Spec.map (CommRingCat.ofHom φ)) (closedPoint R))
  have hmax : (closedPoint R).asIdeal.IsMaximal := maximalIdeal.isMaximal R
  set e := Scheme.Spec.residueFieldIso (.of R) (closedPoint R)
  have key' : residueAlgebraMap (Spec.map (CommRingCat.ofHom φ)) (closedPoint R) =
      e.inv.hom.comp ((algebraMap R (closedPoint R).asIdeal.ResidueField).comp φ) :=
    (hom_comp_eq_of_specMap_comp_eq
      (CommRingCat.ofHom ((algebraMap R (closedPoint R).asIdeal.ResidueField).comp φ)) e.inv
      (CommRingCat.ofHom (residueAlgebraMap (Spec.map (CommRingCat.ofHom φ)) (closedPoint R)))
      (by
        refine Eq.trans ?_ (specMap_residueAlgebraMap _ _).symm
        rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of R) (closedPoint R),
          Category.assoc]
        exact congrArg (Spec.map e.inv ≫ ·)
          ((congrArg Spec.map (CommRingCat.ofHom_comp _ _)).trans (Spec.map_comp _ _)))).symm
  intro z
  obtain ⟨r, hr⟩ := Ideal.algebraMap_residueField_surjective (closedPoint R).asIdeal (e.hom z)
  obtain ⟨l, hl⟩ := hφ (residue R r)
  have h1 : algebraMap R (closedPoint R).asIdeal.ResidueField (φ l) =
      algebraMap R (closedPoint R).asIdeal.ResidueField r := by
    rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, Ideal.ker_algebraMap_residueField]
    change φ l - r ∈ maximalIdeal R
    rwa [← residue_eq_zero_iff, map_sub, sub_eq_zero]
  refine ⟨l, ?_⟩
  rw [key', RingHom.comp_apply, RingHom.comp_apply, h1, hr]
  simp

end ClosedPoint

/-! ### Local rings of `Spec Λ` and residue fields equal to `κ(𝔪)` -/

section Stalk

variable {Λ : Type u} [CommRing Λ]

/-- The extension of `Λ → T` to the local ring `𝒪_{S,s}` of `S = Spec Λ` at `s`, for a
`Λ`-algebra `T` in which the elements outside `s` become units. -/
def stalkLift (s : Spec (.of Λ)) {T : Type*} [CommRing T] [Algebra Λ T]
    (hT : ∀ y : Λ, y ∉ PrimeSpectrum.asIdeal s → IsUnit (algebraMap Λ T y)) :
    (Spec (.of Λ)).presheaf.stalk s →+* T :=
  letI := (toStalkHom s).toAlgebra
  haveI : (PrimeSpectrum.asIdeal s).IsPrime := PrimeSpectrum.isPrime s
  haveI : IsLocalization.AtPrime ((Spec (.of Λ)).presheaf.stalk s) (PrimeSpectrum.asIdeal s) :=
    StructureSheaf.IsLocalization.to_stalk Λ s
  IsLocalization.lift (M := (PrimeSpectrum.asIdeal s).primeCompl)
    (S := (Spec (.of Λ)).presheaf.stalk s) (fun y => hT y y.2)

/-- `stalkLift` extends `Λ → T`. -/
theorem stalkLift_comp_toStalkHom (s : Spec (.of Λ)) {T : Type*} [CommRing T] [Algebra Λ T]
    (hT : ∀ y : Λ, y ∉ PrimeSpectrum.asIdeal s → IsUnit (algebraMap Λ T y)) :
    (stalkLift s hT).comp (toStalkHom s) = algebraMap Λ T := by
  let := (toStalkHom s).toAlgebra
  have : (PrimeSpectrum.asIdeal s).IsPrime := PrimeSpectrum.isPrime s
  have : IsLocalization.AtPrime ((Spec (.of Λ)).presheaf.stalk s) (PrimeSpectrum.asIdeal s) :=
    StructureSheaf.IsLocalization.to_stalk Λ s
  ext l
  exact IsLocalization.lift_eq (M := (PrimeSpectrum.asIdeal s).primeCompl)
    (S := (Spec (.of Λ)).presheaf.stalk s) _ l

/-- The map on local rings induced by a morphism from the spectrum of a local ring to `Spec Λ`
restricts on `Λ` to the corresponding ring map. -/
theorem stalkClosedPointTo_comp_toStalkHom {K : Type u} [CommRing K] [IsLocalRing K]
    (g : Spec (.of K) ⟶ Spec (.of Λ)) :
    (Scheme.stalkClosedPointTo g).hom.comp (toStalkHom (g (closedPoint K))) =
      (Spec.preimage g).hom := by
  exact hom_comp_eq_of_specMap_comp_eq (CommRingCat.ofHom (toStalkHom (g (closedPoint K))))
    (Scheme.stalkClosedPointTo g) (Spec.preimage g)
    ((congrArg (Spec.map (Scheme.stalkClosedPointTo g) ≫ ·)
      (fromSpecStalk_eq_toStalkHom _).symm).trans
      ((Scheme.Spec_stalkClosedPointTo_fromSpecStalk g).trans (Spec.map_preimage g).symm))

variable (𝔪 : Ideal Λ) [𝔪.IsMaximal]

/-- The residue field of a local `Λ`-algebra lying over `𝔪` whose residue field is generated by
the image of `Λ` is `Λ / 𝔪`. -/
def quotientEquivResidueField (T : Type*) [CommRing T] [IsLocalRing T] [Algebra Λ T]
    (hT : (maximalIdeal T).comap (algebraMap Λ T) = 𝔪)
    (hs : ∀ t : T, ∃ l : Λ, t - algebraMap Λ T l ∈ maximalIdeal T) :
    (Λ ⧸ 𝔪) ≃+* ResidueField T :=
  letI := Ideal.Quotient.field 𝔪
  RingEquiv.ofBijective (Ideal.Quotient.lift 𝔪 ((residue T).comp (algebraMap Λ T))
      (fun a ha => by
        rw [RingHom.comp_apply, residue_eq_zero_iff, ← Ideal.mem_comap, hT]
        exact ha))
    ⟨RingHom.injective _, fun z => by
      obtain ⟨t, rfl⟩ := residue_surjective z
      obtain ⟨l, hl⟩ := hs t
      refine ⟨Ideal.Quotient.mk 𝔪 l, ?_⟩
      rw [Ideal.Quotient.lift_mk, RingHom.comp_apply, eq_comm, ← sub_eq_zero, ← map_sub,
        residue_eq_zero_iff]
      exact hl⟩

/-- `quotientEquivResidueField` sends the class of `l` to the residue of its image. -/
theorem quotientEquivResidueField_mk (T : Type*) [CommRing T] [IsLocalRing T] [Algebra Λ T]
    (hT : (maximalIdeal T).comap (algebraMap Λ T) = 𝔪)
    (hs : ∀ t : T, ∃ l : Λ, t - algebraMap Λ T l ∈ maximalIdeal T) (l : Λ) :
    quotientEquivResidueField 𝔪 T hT hs (Ideal.Quotient.mk 𝔪 l) =
      residue T (algebraMap Λ T l) :=
  rfl

/-- The residue field of a point of a scheme over `Spec Λ` lying over `𝔪`, with residue field a
quotient of `Λ`, is `Λ / 𝔪`. -/
def quotientEquivResidueFieldOfPoint {X : Scheme.{u}} (f : X ⟶ Spec (.of Λ)) (x : X)
    (hker : RingHom.ker (residueAlgebraMap f x) = 𝔪)
    (hsurj : Function.Surjective (residueAlgebraMap f x)) :
    (Λ ⧸ 𝔪) ≃+* X.residueField x :=
  (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hsurj)

omit [𝔪.IsMaximal] in
/-- `quotientEquivResidueFieldOfPoint` sends the class of `l` to its image in `κ(x)`. -/
theorem quotientEquivResidueFieldOfPoint_mk {X : Scheme.{u}} (f : X ⟶ Spec (.of Λ)) (x : X)
    (hker : RingHom.ker (residueAlgebraMap f x) = 𝔪)
    (hsurj : Function.Surjective (residueAlgebraMap f x)) (l : Λ) :
    quotientEquivResidueFieldOfPoint 𝔪 f x hker hsurj (Ideal.Quotient.mk 𝔪 l) =
      residueAlgebraMap f x l :=
  rfl

end Stalk

/-! ### Bases isomorphic to `Λ_𝔪^∧` and completions of local rings -/

section CompletionBase

variable {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ] {𝔪 : Ideal Λ} [𝔪.IsMaximal]

/-- The closed point of a base isomorphic to `Λ_𝔪^∧` lies over `𝔪`. -/
theorem toS_closedPoint_of_isCompletionBase {A : FormalBase (Spec (.of Λ))}
    (h : IsCompletionBase 𝔪 A) : A.toS (specClosedPoint A.R) = closedPointOf 𝔪 := by
  change A.toS (closedPoint A.R) = closedPointOf 𝔪
  obtain ⟨σ, hσ⟩ := h
  refine (congrArg (fun φ => φ (closedPoint A.R)) hσ.symm).trans ?_
  apply PrimeSpectrum.ext
  change Ideal.comap ((σ : Completion 𝔪 →+* A.R).comp (algebraMap Λ (Completion 𝔪)))
    (maximalIdeal A.R) = 𝔪
  rw [← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap, comap_maximalIdeal_completion]

/-- The residue field at the closed point of a base isomorphic to `Λ_𝔪^∧` is a quotient of
`Λ`. -/
theorem residueAlgebraMap_surjective_of_isCompletionBase {A : FormalBase (Spec (.of Λ))}
    (h : IsCompletionBase 𝔪 A) :
    Function.Surjective (residueAlgebraMap A.toS (specClosedPoint A.R)) := by
  obtain ⟨σ, hσ⟩ := h
  have hs : Function.Surjective ((residue A.R).comp
      ((σ : Completion 𝔪 →+* A.R).comp (algebraMap Λ (Completion 𝔪)))) := by
    intro z
    obtain ⟨r, rfl⟩ := residue_surjective z
    obtain ⟨l, hl⟩ := exists_sub_mem_pow_completion 𝔪 1 (σ.symm r)
    rw [pow_one] at hl
    refine ⟨l, ?_⟩
    rw [RingHom.comp_apply, RingHom.comp_apply, eq_comm, ← sub_eq_zero, ← map_sub,
      residue_eq_zero_iff]
    simpa using ringEquiv_map_maximalIdeal_le σ (Ideal.mem_map_of_mem _ hl)
  exact hσ ▸ residueAlgebraMap_specMap_surjective _ hs

end CompletionBase

/-! ### An affine chart of `U` around `u₀` -/

section Chart

variable {Λ : Type u} [CommRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal] (C : Type u) [CommRing C]
  [Algebra Λ C] {X : Scheme.{u}} (f : X ⟶ Spec (.of Λ))

/-- A factorization of `X → S` through `S'` sends every point over `𝔪` into `Spec C`, and an
affine open neighbourhood of such a point inside the preimage of `Spec C` gives a
`Spec Γ(X, V) → Spec C` over `S`. -/
theorem exists_affineOpen_chart (g : X ⟶ puncturedCoprod 𝔪 C)
    (hg : g ≫ puncturedCoprodMap 𝔪 C = f) (u₀ : X) (hu₀ : f u₀ = closedPointOf 𝔪) :
    ∃ (V : X.Opens) (hV : IsAffineOpen V), u₀ ∈ V ∧
      ∃ gC : Spec Γ(X, V) ⟶ Spec (.of C),
        gC ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ C)) = hV.fromSpec ≫ f := by
  have hinr : g u₀ ∈ Set.range (Limits.coprod.inr : Spec (.of C) ⟶ puncturedCoprod 𝔪 C) := by
    have hmem : g u₀ ∈ Set.range (Limits.coprod.inl : (puncturedSpec 𝔪).toScheme ⟶ _) ⊔
        Set.range (Limits.coprod.inr : Spec (.of C) ⟶ _) :=
      (isCompl_range_inl_inr (puncturedSpec 𝔪).toScheme (Spec (.of C))).sup_eq_top.symm ▸
        Set.mem_univ _
    refine hmem.resolve_left ?_
    rintro ⟨v, hv⟩
    have h1 : f u₀ = (puncturedSpec 𝔪).ι v := by
      rw [← hg, Scheme.Hom.comp_apply, ← hv, ← Scheme.Hom.comp_apply, inl_puncturedCoprodMap]
    exact v.2 (h1.symm.trans hu₀)
  obtain ⟨_, ⟨V, hV, rfl⟩, hu₀V, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (u := g ⁻¹ᵁ (Limits.coprod.inr : Spec (.of C) ⟶ puncturedCoprod 𝔪 C).opensRange) hinr
    (TopologicalSpace.Opens.isOpen _)
  change IsAffineOpen V at hV
  have hrange : Set.range (hV.fromSpec ≫ g) ⊆
      Set.range (Limits.coprod.inr : Spec (.of C) ⟶ puncturedCoprod 𝔪 C) := by
    rintro _ ⟨z, rfl⟩
    have hz : hV.fromSpec z ∈ (V : Set X) := hV.range_fromSpec ▸ Set.mem_range_self z
    rw [Scheme.Hom.comp_apply]
    exact hVW hz
  refine ⟨V, hV, hu₀V, IsOpenImmersion.lift Limits.coprod.inr (hV.fromSpec ≫ g) hrange, ?_⟩
  rw [← inr_puncturedCoprodMap 𝔪 C, ← Category.assoc, IsOpenImmersion.lift_fac,
    Category.assoc, hg]

variable {V : X.Opens} (hV : IsAffineOpen V)

/-- The `Λ`-algebra structure on `Γ(X, V)` for an affine open `V` of a scheme over `Spec Λ`. -/
@[instance_reducible]
def chartAlgebra : Algebra Λ Γ(X, V) :=
  (Spec.preimage (hV.fromSpec ≫ f)).hom.toAlgebra

/-- The spectrum of `Λ → Γ(X, V)` is `Spec Γ(X, V) → X → Spec Λ`. -/
theorem specMap_chartAlgebra :
    letI := chartAlgebra f hV
    Spec.map (CommRingCat.ofHom (algebraMap Λ Γ(X, V))) = hV.fromSpec ≫ f := by
  change Spec.map (CommRingCat.ofHom (Spec.preimage (hV.fromSpec ≫ f)).hom) = _
  rw [CommRingCat.ofHom_hom, Spec.map_preimage]

/-- If `X → Spec Λ` is locally of finite type, then `Γ(X, V)` is of finite type over `Λ`. -/
theorem finiteType_chartAlgebra [LocallyOfFiniteType f] :
    letI := chartAlgebra f hV
    Algebra.FiniteType Λ Γ(X, V) := by
  let := chartAlgebra f hV
  have h : LocallyOfFiniteType (Spec.map (CommRingCat.ofHom (algebraMap Λ Γ(X, V)))) := by
    rw [specMap_chartAlgebra]
    infer_instance
  exact HasRingHomProperty.Spec_iff.mp h

/-- The `Λ`-algebra map `C → Γ(X, V)` given by a morphism `Spec Γ(X, V) → Spec C` over `S`. -/
def chartAlgHom (gC : Spec Γ(X, V) ⟶ Spec (.of C))
    (hgC : gC ≫ Spec.map (CommRingCat.ofHom (algebraMap Λ C)) = hV.fromSpec ≫ f) :
    letI := chartAlgebra f hV
    C →ₐ[Λ] Γ(X, V) :=
  letI := chartAlgebra f hV
  { (Spec.preimage gC).hom with
    commutes' := fun l => by
      have h : CommRingCat.ofHom (algebraMap Λ C) ≫ Spec.preimage gC =
          CommRingCat.ofHom (algebraMap Λ Γ(X, V)) := by
        apply Spec.map_injective
        rw [Spec.map_comp, Spec.map_preimage, hgC, specMap_chartAlgebra]
      exact congrArg (fun φ => φ.hom l) h }

variable {u₀ : X} (hu₀ : u₀ ∈ V)

/-- The ring map `Γ(X, V) → κ(u₀)` at a point of the affine open `V`. -/
def chartResidue : Γ(X, V) →+* X.residueField u₀ :=
  (Spec.preimage (IsOpenImmersion.lift hV.fromSpec (X.fromSpecResidueField u₀) (by
    rw [Scheme.range_fromSpecResidueField, hV.range_fromSpec, Set.singleton_subset_iff]
    exact hu₀))).hom

/-- The spectrum of `Γ(X, V) → κ(u₀)`, followed by `Spec Γ(X, V) → X`, is the canonical
morphism `Spec κ(u₀) → X`. -/
theorem specMap_chartResidue :
    Spec.map (CommRingCat.ofHom (chartResidue hV hu₀)) ≫ hV.fromSpec =
      X.fromSpecResidueField u₀ := by
  rw [chartResidue, CommRingCat.ofHom_hom, Spec.map_preimage, IsOpenImmersion.lift_fac]

/-- The map `Γ(X, V) → κ(u₀)` restricts on `Λ` to `Λ → κ(u₀)`. -/
theorem chartResidue_comp_algebraMap :
    letI := chartAlgebra f hV
    (chartResidue hV hu₀).comp (algebraMap Λ Γ(X, V)) = residueAlgebraMap f u₀ := by
  let := chartAlgebra f hV
  refine hom_comp_eq_of_specMap_comp_eq (CommRingCat.ofHom (algebraMap Λ Γ(X, V)))
    (CommRingCat.ofHom (chartResidue hV hu₀)) (CommRingCat.ofHom (residueAlgebraMap f u₀)) ?_
  rw [specMap_chartAlgebra, ← Category.assoc, specMap_chartResidue, specMap_residueAlgebraMap]

end Chart

/-! ### The maximal ideal `𝔪_A` -/

section KernelResidue

variable {Λ : Type u} [CommRing Λ] (𝔪 : Ideal Λ) [𝔪.IsMaximal] {A : Type u} [CommRing A]
  [Algebra Λ A] {K : Type u} [Field K] (ψ : A →+* K)
  (hsurj : Function.Surjective (ψ.comp (algebraMap Λ A)))
  (hker : RingHom.ker (ψ.comp (algebraMap Λ A)) = 𝔪)

include hsurj in
/-- The kernel of a map to a field which is surjective on `Λ` is maximal. -/
theorem ker_isMaximal_of_surjective_comp : (RingHom.ker ψ).IsMaximal := by
  refine RingHom.ker_isMaximal_of_surjective ψ fun z => ?_
  obtain ⟨l, rfl⟩ := hsurj z
  exact ⟨algebraMap Λ A l, rfl⟩

omit [𝔪.IsMaximal] in
include hker in
/-- The kernel lies over `𝔪`. -/
theorem eq_comap_ker : 𝔪 = (RingHom.ker ψ).comap (algebraMap Λ A) := by
  rw [← hker, RingHom.comap_ker]

include hsurj in
/-- Every element is congruent to an element of `Λ` modulo the kernel. -/
theorem exists_sub_mem_ker (a : A) : ∃ l : Λ, a - algebraMap Λ A l ∈ RingHom.ker ψ := by
  obtain ⟨l, hl⟩ := hsurj (ψ a)
  refine ⟨l, ?_⟩
  rw [RingHom.mem_ker, map_sub, ← RingHom.comp_apply, hl, sub_self]

include hsurj in
/-- `κ(𝔪) → κ(𝔪_A)` is bijective. -/
theorem residueField_map_bijective_of_surjective_comp [(RingHom.ker ψ).IsMaximal] :
    Function.Bijective (Ideal.ResidueField.map 𝔪 (RingHom.ker ψ) (algebraMap Λ A)
      (eq_comap_ker 𝔪 ψ hker)) := by
  refine ⟨RingHom.injective _, fun z => ?_⟩
  obtain ⟨a, rfl⟩ := Ideal.algebraMap_residueField_surjective (RingHom.ker ψ) z
  obtain ⟨l, hl⟩ := exists_sub_mem_ker ψ hsurj a
  refine ⟨algebraMap Λ 𝔪.ResidueField l, ?_⟩
  rwa [Ideal.ResidueField.map_algebraMap, eq_comm, ← sub_eq_zero, ← map_sub,
    Ideal.algebraMap_residueField_eq_zero]

end KernelResidue

/-- The completion map of a local ring is a local ring map. -/
theorem isLocalHom_algebraMap_adicCompletion (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalHom (algebraMap R (AdicCompletion (maximalIdeal R) R)) := by
  refine ⟨fun o ho => ?_⟩
  by_contra hno
  have h1 := ho.map (AdicCompletion.evalₐ (maximalIdeal R) 1)
  rw [AdicCompletion.algebraMap_apply, AdicCompletion.evalₐ_of, Algebra.algebraMap_self,
    RingHom.id_apply, Ideal.Quotient.eq_zero_iff_mem.mpr (by simpa using hno)] at h1
  have : Nontrivial (R ⧸ maximalIdeal R ^ 1) :=
    Ideal.Quotient.nontrivial_iff.mpr (by simpa using (maximalIdeal.isMaximal R).ne_top)
  exact not_isUnit_zero h1

end Deformation.Artin.GRingNecessity

end
