module

public import StacksFrontier.AlgebraicGeometry.Curves.Models.RegularProperModel
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SpecialFiberPrincipal
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.NormalBase
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.ProperGeomConnected.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Regular
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The structure sheaf and the special fibre of a regular proper model

In the situation of [Stacks, Tag 0C61] the model `f : X ⟶ Spec(R)` satisfies the hypotheses of
[Stacks, Tag 0AY8]: it is proper, `Spec(R)` is integral and normal because `R` is a discrete
valuation ring, `X` is reduced because it is regular, every generic point of an irreducible
component of `X` lies over the generic point `ξ` of `Spec(R)` because `f` is flat, and the
generic fibre `X_ξ` is the curve `C`, whose only global functions are the constants.  The first
conclusion of Tag 0AY8 therefore holds unconditionally here: `f_*𝒪_X = 𝒪_{Spec(R)}`, equivalently
`Γ(X, 𝒪_X) = R`.

The second conclusion of Tag 0AY8 holds here just as unconditionally: `f` has geometrically
connected fibres.  Read at the closed point of `Spec(R)`, where the fibre is `X_k` and the base
is the one-point scheme `Spec(k)`, it gives [Stacks, Tag 0C62]: the special fibre `X_k` is
connected.  That is the whole of Tag 0C62, and it is proved here with nothing assumed beyond
Situation 0C61.

## Main results

* `Stacks.Models.RegularProperModelSituation.isIso_c`: `f_*𝒪_X = 𝒪_{Spec(R)}`.
* `Stacks.Models.RegularProperModelSituation.isIso_globalSections_model`: `Γ(X, 𝒪_X) = R`.
* `Stacks.Models.RegularProperModelSituation.surjective_X_to_R`: the model is surjective onto
  `Spec(R)`, so the special fibre is nonempty.
* `Stacks.Models.RegularProperModelSituation.isIso_globalSections_specialFiber_of_surjective`:
  if every function on `X_k` extends to `X`, then `Γ(X_k, 𝒪_{X_k}) = k`.
* `Stacks.Models.RegularProperModelSituation.geometricallyConnected_X_to_R`: the model has
  geometrically connected fibres.
* `Stacks.Models.RegularProperModelSituation.connectedSpace_specialFiber`: **[Stacks, Tag 0C62]**,
  the special fibre `X_k` is connected.
* `Stacks.Models.RegularProperModelSituation.isConnected_univ_specialFiber`: the same statement
  read as `IsConnected (Set.univ : Set X_k)`.
* `Stacks.Models.RegularProperModelSituation.connectedSpace_subscheme_radical_specialFiberIdeal`:
  the same statement read on the reduced special fibre, the closed subscheme of `X` cut out by
  the radical of the ideal of `X_k`.

## Implementation notes

`f_*𝒪_X = 𝒪_S` is expressed by invertibility of `AlgebraicGeometry.Scheme.Hom.c`, and
`Γ(Y, 𝒪_Y) = A` by invertibility of the canonical ring map `A ⟶ Γ(Y, 𝒪_Y)`, exactly as in the
situation's own hypothesis `isIso_globalSections` on the curve.  The special fibre is the
pullback `RegularModelSituation.specialFiber`, and `specialFiberι`, `specialFiberToSpec` name its
two projections.

**How Tag 0C62 is reached.**  The second conclusion of Tag 0AY8 is
`Stacks.SteinFactorization.geometricallyConnected_of_isNormal`, which the source deduces from
clause (1) of [Stacks, Tag 03H2];  that clause rests on [Stacks, Tag 0G7X] — an idempotent of
`Γ(X_s, 𝒪_{X_s})` lifts to a neighbourhood of `s` — and Tag 0G7X is
`Stacks.AlgebraicGeometry.Fibres.extendsOverNeighbourhood_of_isProper`, with no restriction on
the base.  So the specialization to Situation 0C61 needs no extra input, and the step from
geometric connectedness of the fibres to connectedness of `X_k` is just
`AlgebraicGeometry.GeometricallyConnected.connectedSpace_of_subsingleton` applied to
`specialFiberToSpec`, the base `Spec(k)` of the special fibre being a one-point scheme.

Over a discrete valuation ring the idempotent-lifting input of Tag 0G7X is the concrete
assertion that `Γ(X, 𝒪_X) ⟶ Γ(X_k, 𝒪_{X_k})` hits the idempotents, the only open
neighbourhood of the closed point of `Spec(R)` being `Spec(R)` itself.  Tag 0G7X holds for
every proper morphism, so the connectedness statement below needs no hypothesis at all.

The results of this file do not carry a `0AY8` attribute, which belongs to the two general lemmas
in `StacksFrontier.AlgebraicGeometry.MoreMorphisms.SteinFactorization.NormalBase`; they are their
specialization to Situation 0C61, which Section 55.9 does not state separately.

The identity `Γ(X_k, 𝒪_{X_k}) = k` is a different matter and is false in general, the special
fibre of a regular model being allowed to be non-reduced;  accordingly
`isIso_globalSections_specialFiber_of_surjective` keeps surjectivity of the restriction as a
hypothesis, and Section 55.9 never asserts the identity.

## References

* [Stacks Project, Tag 0C62](https://stacks.math.columbia.edu/tag/0C62)
* [Stacks Project, Tag 0C61](https://stacks.math.columbia.edu/tag/0C61)
* [Stacks Project, Tag 0AY8](https://stacks.math.columbia.edu/tag/0AY8)
* [Stacks Project, Tag 03H2](https://stacks.math.columbia.edu/tag/03H2)
* [Stacks Project, Tag 0G7X](https://stacks.math.columbia.edu/tag/0G7X)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ProperGeomConnected

universe u

namespace Stacks.Models

namespace RegularModelSituation

/-- The closed immersion of the special fibre `X_k` into the total space of the model. -/
public noncomputable abbrev specialFiberι (S : RegularModelSituation.{u}) :
    S.specialFiber ⟶ S.X :=
  pullback.fst S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))

/-- The structure morphism of the special fibre `X_k` over the residue field `k`. -/
public noncomputable abbrev specialFiberToSpec (S : RegularModelSituation.{u}) :
    S.specialFiber ⟶ Spec (.of S.k) :=
  pullback.snd S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k)))

end RegularModelSituation

/-- A discrete valuation ring is a normal ring: it is an integrally closed domain, and both
properties pass to its localizations at primes, which are localizations at sets of
nonzerodivisors. -/
private lemma isNormalRing_of_isDiscreteValuationRing (R : Type u) [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] : IsNormalRing R := by
  intro p hp
  have hle : p.primeCompl ≤ nonZeroDivisors R := p.primeCompl_le_nonZeroDivisors
  exact ⟨IsLocalization.isDomain_of_le_nonZeroDivisors _ hle,
    isIntegrallyClosed_of_isLocalization _ _ hle⟩

namespace RegularProperModelSituation

variable (S : RegularProperModelSituation.{u})

/-- The base of a regular model is a normal integral scheme, being the spectrum of a discrete
valuation ring. -/
private lemma isNormal_spec : AlgebraicGeometry.IsNormal (Spec (.of S.R)) :=
  AlgebraicGeometry.isNormal_spec_of_isNormalRing
    (isNormalRing_of_isDiscreteValuationRing S.R)

/-- The total space of a regular model is reduced, because a regular scheme is normal. -/
private lemma isReduced_X : IsReduced S.X :=
  have : AlgebraicGeometry.IsNormal S.X := AlgebraicGeometry.isNormal_of_isRegular S.X S.regular
  inferInstance

/-- Every generic point of an irreducible component of the total space of a regular model lies
over the generic point of `Spec(R)`, because a flat morphism takes generic points to generic
points and `Spec(R)` is irreducible. -/
@[sga "6 X 7.7" "partial"]
private lemma maps_genericPoints (x : S.X) (hx : x ∈ genericPoints S.X) :
    S.X_to_R x = genericPoint (Spec (.of S.R)) := by
  have h := AlgebraicGeometry.mem_genericPoints_of_generalizingMap
    (Flat.generalizingMap S.X_to_R) hx
  rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at h

/-- The generic fibre of a regular model has no global functions beyond the constants: it is the
curve `C`, whose structure morphism is an isomorphism on global sections by hypothesis, and the
residue field of `Spec(R)` at its generic point is the fraction field `K`. -/
private lemma isIso_appTop_fiberToSpecResidueField_genericPoint :
    IsIso ((Scheme.ΓSpecIso
        (.of ((Spec (.of S.R)).residueField (genericPoint (Spec (.of S.R)))))).inv ≫
      (S.X_to_R.fiberToSpecResidueField (genericPoint (Spec (.of S.R)))).appTop) := by
  rw [genericPoint_eq_bot_of_affine]
  set f : S.X ⟶ Spec (.of S.R) := S.X_to_R with hf
  set qK : Spec (.of S.K) ⟶ Spec (.of S.R) :=
    Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)) with hqK
  set ξ : Spec (.of S.R) := (⊥ : PrimeSpectrum (CommRingCat.of S.R)) with hξ
  let qξ : Spec (.of ((Spec (.of S.R)).residueField ξ)) ⟶ Spec (.of S.R) :=
    (Spec (.of S.R)).fromSpecResidueField ξ
  let e₁ : (Spec (.of S.R)).residueField ξ ≅ CommRingCat.of ξ.asIdeal.ResidueField :=
    Scheme.Spec.residueFieldIso (.of S.R) ξ
  let e₂ : ξ.asIdeal.ResidueField ≃+* S.K := by
    show (⊥ : Ideal S.R).ResidueField ≃+* S.K
    exact IsFractionRing.ringEquivOfRingEquiv (RingEquiv.quotientBot S.R)
  let e : (Spec (.of S.R)).residueField ξ ≃+* S.K :=
    e₁.commRingCatIsoToRingEquiv.trans e₂
  let eSpec : Spec (.of S.K) ≅ Spec (.of ((Spec (.of S.R)).residueField ξ)) :=
    Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso e).op
  -- the two descriptions `Spec K` and `Spec κ(ξ)` of the generic point agree over `Spec(R)`
  have hq : eSpec.hom ≫ qξ = qK := by
    show eSpec.hom ≫ (Spec (.of S.R)).fromSpecResidueField ξ = qK
    rw [← Scheme.Spec.map_residueFieldIso_inv_eq_fromSpecResidueField (.of S.R) ξ]
    dsimp [eSpec, e, e₁]
    simp only [← Spec.map_comp]
    apply Spec.map_inj.2
    apply CommRingCat.hom_ext
    apply RingHom.ext
    intro r
    show e₂ (e₁.commRingCatIsoToRingEquiv
      (e₁.inv.hom (algebraMap S.R ξ.asIdeal.ResidueField r))) = _
    have he : e₁.hom.hom (e₁.inv.hom (algebraMap S.R ξ.asIdeal.ResidueField r)) =
        algebraMap S.R ξ.asIdeal.ResidueField r := by simp
    show e₂ (e₁.hom.hom (e₁.inv.hom (algebraMap S.R ξ.asIdeal.ResidueField r))) = _
    rw [he, ← Ideal.algebraMap_quotient_residueField_mk]
    show IsFractionRing.ringEquivOfRingEquiv (RingEquiv.quotientBot S.R)
      (algebraMap (S.R ⧸ (⊥ : Ideal S.R)) ξ.asIdeal.ResidueField (Ideal.Quotient.mk ⊥ r)) =
      algebraMap S.R S.K r
    exact (IsFractionRing.ringEquivOfRingEquiv_algebraMap
        (A := S.R ⧸ (⊥ : Ideal S.R)) (K := ξ.asIdeal.ResidueField)
        (B := S.R) (L := S.K) (RingEquiv.quotientBot S.R) (Ideal.Quotient.mk ⊥ r))
  -- hence the fibre over `ξ` is the generic fibre, compatibly with the global sections
  let gK : S.genericFiber ⟶ Spec (.of S.K) := pullback.snd f qK
  let gξ : pullback f qξ ⟶ Spec (.of ((Spec (.of S.R)).residueField ξ)) := pullback.snd f qξ
  have hq' : qξ = eSpec.inv ≫ qK := by
    calc
      qξ = (𝟙 _) ≫ qξ := by simp
      _ = (eSpec.inv ≫ eSpec.hom) ≫ qξ := by simp
      _ = eSpec.inv ≫ qK := by rw [Category.assoc, hq]
  let pToGen : pullback f qξ ⟶ S.genericFiber :=
    pullback.map f qξ f qK (𝟙 S.X) eSpec.inv (𝟙 (Spec (.of S.R))) (by simp) hq'
  have : IsIso pToGen :=
    pullback.map_isIso f qξ f qK (𝟙 S.X) eSpec.inv (𝟙 (Spec (.of S.R))) (by simp) hq'
  let eFiber : pullback f qξ ≅ S.genericFiber := asIso pToGen
  have hbase : eFiber.hom ≫ gK = gξ ≫ eSpec.inv := by
    show pullback.map f qξ f qK (𝟙 S.X) eSpec.inv (𝟙 (Spec (.of S.R))) (by simp) hq' ≫
      pullback.snd f qK = pullback.snd f qξ ≫ eSpec.inv
    dsimp [pullback.map]
    rw [pullback.lift_snd]
  have : IsIso eFiber.hom.appTop := by
    show IsIso (eFiber.hom.app ⊤)
    infer_instance
  have : IsIso S.genericFiberIso.hom.appTop := by
    show IsIso (S.genericFiberIso.hom.app ⊤)
    infer_instance
  have hcurve : gK.appTop ≫ S.genericFiberIso.hom.appTop = S.C_to_K.appTop := by
    simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop S.genericFiberIso_over_K
  have hcurveIso : IsIso (((Scheme.ΓSpecIso (.of S.K)).inv ≫ gK.appTop) ≫
      S.genericFiberIso.hom.appTop) := by
    rw [Category.assoc, hcurve]
    exact S.isIso_globalSections
  have hgenIso : IsIso ((Scheme.ΓSpecIso (.of S.K)).inv ≫ gK.appTop) :=
    (isIso_comp_right_iff _ _).mp hcurveIso
  have hnat : CommRingCat.ofHom e.toRingHom ≫ (Scheme.ΓSpecIso (.of S.K)).inv =
      (Scheme.ΓSpecIso (.of ((Spec (.of S.R)).residueField ξ))).inv ≫ eSpec.hom.appTop := by
    simp [eSpec]
  have hbaseΓ : gK.appTop ≫ eFiber.hom.appTop = eSpec.inv.appTop ≫ gξ.appTop := by
    simpa only [Scheme.Hom.comp_appTop] using congrArg Scheme.Hom.appTop hbase
  have hcompSpec : eSpec.hom.appTop ≫ eSpec.inv.appTop = 𝟙 _ := by
    simpa only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop] using
      congrArg Scheme.Hom.appTop eSpec.inv_hom_id
  have hsections :
      CommRingCat.ofHom e.toRingHom ≫ (Scheme.ΓSpecIso (.of S.K)).inv ≫
        gK.appTop ≫ eFiber.hom.appTop =
      (Scheme.ΓSpecIso (.of ((Spec (.of S.R)).residueField ξ))).inv ≫ gξ.appTop := by
    calc
      _ = (CommRingCat.ofHom e.toRingHom ≫ (Scheme.ΓSpecIso (.of S.K)).inv) ≫
          gK.appTop ≫ eFiber.hom.appTop := by simp [Category.assoc]
      _ = ((Scheme.ΓSpecIso (.of ((Spec (.of S.R)).residueField ξ))).inv ≫
          eSpec.hom.appTop) ≫ gK.appTop ≫ eFiber.hom.appTop := by rw [hnat]
      _ = (Scheme.ΓSpecIso (.of ((Spec (.of S.R)).residueField ξ))).inv ≫
          (eSpec.hom.appTop ≫ (gK.appTop ≫ eFiber.hom.appTop)) := by simp [Category.assoc]
      _ = (Scheme.ΓSpecIso (.of ((Spec (.of S.R)).residueField ξ))).inv ≫
          (eSpec.hom.appTop ≫ (eSpec.inv.appTop ≫ gξ.appTop)) := by rw [hbaseΓ]
      _ = (Scheme.ΓSpecIso (.of ((Spec (.of S.R)).residueField ξ))).inv ≫ gξ.appTop := by
        congr 1
        calc
          eSpec.hom.appTop ≫ (eSpec.inv.appTop ≫ gξ.appTop) =
              (eSpec.hom.appTop ≫ eSpec.inv.appTop) ≫ gξ.appTop := by rw [Category.assoc]
          _ = gξ.appTop := by rw [hcompSpec, Category.id_comp]
  have : IsIso (CommRingCat.ofHom e.toRingHom) :=
    (ConcreteCategory.isIso_iff_bijective _).2 e.bijective
  have : IsIso ((Scheme.ΓSpecIso (.of S.K)).inv ≫ gK.appTop) := hgenIso
  have : IsIso gK.appTop :=
    IsIso.of_isIso_comp_left ((Scheme.ΓSpecIso (.of S.K)).inv) gK.appTop
  show IsIso ((Scheme.ΓSpecIso (.of ((Spec (.of S.R)).residueField ξ))).inv ≫ gξ.appTop)
  rw [← hsections]
  infer_instance

/-- **The first conclusion of [Stacks, Tag 0AY8] in Situation 0C61.**  For a regular proper model
`f : X ⟶ Spec(R)` of a smooth projective curve with `H⁰(C, 𝒪_C) = K`, one has
`f_*𝒪_X = 𝒪_{Spec(R)}`. -/
public theorem isIso_c : IsIso S.X_to_R.c := by
  have := S.isNormal_spec
  have := S.isReduced_X
  exact Stacks.SteinFactorization.isIso_c_of_isNormal S.X_to_R S.maps_genericPoints
    S.isIso_appTop_fiberToSpecResidueField_genericPoint

/-- The restriction of `RegularProperModelSituation.isIso_c` to global sections. -/
private lemma isIso_appTop_X_to_R : IsIso S.X_to_R.appTop := by
  have := S.isIso_c
  show IsIso (S.X_to_R.c.app (Opposite.op ⊤))
  infer_instance

/-- **`Γ(X, 𝒪_X) = R` for a regular proper model.**  The canonical map from the discrete
valuation ring to the global functions on the model is an isomorphism; this is the degree-zero
reading of `RegularProperModelSituation.isIso_c`. -/
public theorem isIso_globalSections_model :
    IsIso ((Scheme.ΓSpecIso (.of S.R)).inv ≫ S.X_to_R.appTop) :=
  have := S.isIso_appTop_X_to_R
  inferInstance

/-- The total space of a regular model is nonempty, since it contains the generic fibre, which is
the curve `C` and hence an integral scheme. -/
public theorem nonempty_X : Nonempty S.X :=
  have : Nonempty S.genericFiber := ⟨S.genericFiberIso.hom (Classical.arbitrary S.C)⟩
  ⟨pullback.fst S.X_to_R (Spec.map (CommRingCat.ofHom (algebraMap S.R S.K)))
    (Classical.arbitrary _)⟩

/-- A regular proper model is surjective onto `Spec(R)`: its image is closed because the model is
proper, and it contains the generic point of `Spec(R)` because `X` is nonempty and its generic
points lie over `ξ`. -/
public theorem surjective_X_to_R : Function.Surjective S.X_to_R.base := by
  obtain ⟨x⟩ := S.nonempty_X
  have hclosed : IsClosed (Set.range S.X_to_R.base) := by
    simpa using S.X_to_R.isClosedMap _ isClosed_univ
  have hmem : genericPoint (Spec (.of S.R)) ∈ Set.range S.X_to_R.base := by
    refine ⟨genericPoints.ofComponent
      (⟨irreducibleComponent x, irreducibleComponent_mem_irreducibleComponents x⟩ :
        irreducibleComponents S.X), ?_⟩
    exact S.maps_genericPoints _ (genericPoints.ofComponent _).2
  rw [← Set.range_eq_univ]
  refine Set.eq_univ_of_univ_subset ?_
  calc (Set.univ : Set (Spec (.of S.R)))
      = closure {genericPoint (Spec (.of S.R))} :=
        (genericPoint_spec (Spec (.of S.R))).symm
    _ ⊆ Set.range S.X_to_R.base :=
        hclosed.closure_subset_iff.mpr (Set.singleton_subset_iff.mpr hmem)

/-- The special fibre of a regular proper model is nonempty, the model being surjective. -/
public theorem nonempty_specialFiber : Nonempty S.specialFiber := by
  have hrange : Set.range S.specialFiberToSpec.base = Set.univ := by
    rw [Scheme.Pullback.range_snd, Set.range_eq_univ.mpr S.surjective_X_to_R,
      Set.preimage_univ]
  obtain ⟨y, -⟩ := Set.eq_univ_iff_forall.mp hrange
    (IsLocalRing.closedPoint (CommRingCat.of S.k))
  exact ⟨y⟩

/-- The ring of global functions on the special fibre is nontrivial, the special fibre being
nonempty. -/
private lemma nontrivial_globalSections_specialFiber : Nontrivial Γ(S.specialFiber, ⊤) :=
  have : Nonempty S.specialFiber := S.nonempty_specialFiber
  have : Nonempty ((⊤ : S.specialFiber.Opens)) := ⟨⟨Classical.arbitrary _, trivial⟩⟩
  Scheme.component_nontrivial _ ⊤

/-- A function on the special fibre which is the restriction of a function on the model already
comes from the residue field.

The restriction `Γ(X, 𝒪_X) ⟶ Γ(X_k, 𝒪_{X_k})` factors through `k` by the defining cartesian
square of the special fibre, and `Γ(X, 𝒪_X) = R` by
`RegularProperModelSituation.isIso_globalSections_model`. -/
private lemma exists_globalSections_specialFiber_eq {e : Γ(S.specialFiber, ⊤)}
    (he : ∃ a, S.specialFiberι.appTop a = e) :
    ∃ c, ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop) c = e := by
  have hsq : S.X_to_R.appTop ≫ S.specialFiberι.appTop =
      (Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))).appTop ≫
        S.specialFiberToSpec.appTop := by
    simpa only [Scheme.Hom.comp_appTop] using
      congrArg Scheme.Hom.appTop (pullback.condition (f := S.X_to_R)
        (g := Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))))
  have hX := S.isIso_appTop_X_to_R
  have hXsurj : Function.Surjective S.X_to_R.appTop :=
    (ConcreteCategory.bijective_of_isIso S.X_to_R.appTop).2
  obtain ⟨a, ha⟩ := he
  obtain ⟨b, hb⟩ := hXsurj a
  refine ⟨(Scheme.ΓSpecIso (.of S.k)).hom
    ((Spec.map (CommRingCat.ofHom (algebraMap S.R S.k))).appTop b), ?_⟩
  have hfac := congrArg (fun φ ↦ (CommRingCat.Hom.hom φ) b) hsq
  simp only [CommRingCat.comp_apply] at hfac
  simpa [← hfac, hb] using ha

/-- **`Γ(X_k, 𝒪_{X_k}) = k`, conditionally.**  If every function on the special fibre of a
regular proper model is the restriction of a function on the model, then the canonical map from
the residue field to the global functions on the special fibre is an isomorphism.

It is surjective by the hypothesis together with
`RegularProperModelSituation.exists_globalSections_specialFiber_eq`, and injective because `k`
is a field and `X_k` is nonempty. -/
public theorem isIso_globalSections_specialFiber_of_surjective
    (hres : Function.Surjective S.specialFiberι.appTop) :
    IsIso ((Scheme.ΓSpecIso (.of S.k)).inv ≫ S.specialFiberToSpec.appTop) := by
  have hnt := S.nontrivial_globalSections_specialFiber
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨RingHom.injective _, fun e ↦ S.exists_globalSections_specialFiber_eq (hres e)⟩

/-- **The second conclusion of [Stacks, Tag 0AY8] in Situation 0C61.**  A regular proper model
`f : X ⟶ Spec(R)` of a smooth projective curve with `H⁰(C, 𝒪_C) = K` has geometrically connected
fibres.

The hypotheses of Tag 0AY8 are the ones already verified for
`RegularProperModelSituation.isIso_c`, and the conclusion is
`Stacks.SteinFactorization.geometricallyConnected_of_isNormal`. -/
@[ega "III 4.3.4" "special case"]
public theorem geometricallyConnected_X_to_R : GeometricallyConnected S.X_to_R :=
  have := S.isNormal_spec
  have := S.isReduced_X
  Stacks.SteinFactorization.geometricallyConnected_of_isNormal S.X_to_R S.maps_genericPoints
    S.isIso_appTop_fiberToSpecResidueField_genericPoint

/-- **[Stacks, Tag 0C62].**  In Situation [Stacks, Tag 0C61] the special fibre `X_k` of the
regular proper model is connected.

This is the second conclusion of [Stacks, Tag 0AY8] — geometric connectedness of the fibres,
`RegularProperModelSituation.geometricallyConnected_X_to_R` — read at the closed point of
`Spec(R)`:  the special fibre is the base change of the model along `Spec(k) ⟶ Spec(R)`, whose
source is a one-point scheme, and a scheme geometrically connected over a one-point base is
connected. -/
@[stacks 0C62 "the special fibre X_k of a regular proper model is connected",
  sga "2 XIII 2.2" "special case",
  sga "6 X 7.12" "special case"]
public theorem connectedSpace_specialFiber : ConnectedSpace S.specialFiber :=
  have := S.geometricallyConnected_X_to_R
  GeometricallyConnected.connectedSpace_of_subsingleton S.specialFiberToSpec

/-- The special fibre of a regular proper model is a connected set: the reading of
`RegularProperModelSituation.connectedSpace_specialFiber` as nonemptiness together with
preconnectedness of `Set.univ`, which is the form the intersection theory of the special fibre
uses. -/
public theorem isConnected_univ_specialFiber :
    _root_.IsConnected (Set.univ : Set S.specialFiber) :=
  have := connectedSpace_specialFiber S
  isConnected_univ

/-- **[Stacks, Tag 0C62] read on the reduced special fibre.**  The closed subscheme of the model
cut out by the radical of the ideal of the special fibre is connected.

Taking the radical does not change the support of a sheaf of ideals, and the support of the ideal
of the special fibre is the closure of the image of `X_k ⟶ X`;  so the underlying space here is a
closed subspace of `X` homeomorphic to a space whose connectedness is
`RegularProperModelSituation.connectedSpace_specialFiber`. -/
public theorem connectedSpace_subscheme_radical_specialFiberIdeal :
    ConnectedSpace S.specialFiberIdeal.radical.subscheme := by
  have hconn := connectedSpace_specialFiber S
  have hsupp : (S.specialFiberIdeal.radical.support : Set S.X) =
      closure (Set.range S.specialFiberι) :=
    Scheme.Hom.support_ker S.specialFiberι
  have hrange : Set.range S.specialFiberIdeal.radical.subschemeι =
      closure (Set.range S.specialFiberι) := by
    rw [← hsupp]
    exact Scheme.IdealSheafData.range_subschemeι _
  have hc : _root_.IsConnected (closure (Set.range S.specialFiberι)) :=
    (isConnected_range S.specialFiberι.continuous).closure
  have hemb : Topology.IsEmbedding S.specialFiberIdeal.radical.subschemeι :=
    S.specialFiberIdeal.radical.subschemeι.isEmbedding
  rw [connectedSpace_iff_univ]
  refine ⟨?_, ?_⟩
  · obtain ⟨x, hx⟩ := hc.nonempty
    rw [← hrange] at hx
    obtain ⟨y, -⟩ := hx
    exact ⟨y, trivial⟩
  · rw [← hemb.isInducing.isPreconnected_image, Set.image_univ, hrange]
    exact hc.isPreconnected

end RegularProperModelSituation

end Stacks.Models

end
