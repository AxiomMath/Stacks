module

public import StacksFrontier.AlgebraicGeometry.Quot.StableReduction.Glueing.FibreTransport
public import StacksFrontier.AlgebraicGeometry.Quot.ContractionUniquenessComplete
public import StacksFrontier.AlgebraicGeometry.Curves.Models.SemistableReduction.NodalSpecialFibre
public import StacksFrontier.AlgebraicGeometry.Scheme.SpecQuotientInSite

/-!
# The fibres of a stable family of curves over a discrete valuation ring

Let `p : X ⟶ S` be a stable family of curves given by a morphism of schemes
(`AlgebraicGeometry.IsStableFamilyOfSchemes`). For every field `k` with `Spec k` in the site and
every morphism `t : Spec k ⟶ S`, the fibre product `X ×_S Spec k` over `k` has genus at least
two, no rational tail and no rational bridge, and `H⁰(X ×_S Spec k, 𝒪) = k`: these are the fibre
conditions of stability and the universal bijectivity of global functions of prestability,
read at the field-valued point `t`, transported along the isomorphism of the fibre presented in
the site with the chosen fibre product.

Over a discrete valuation ring `R` with fraction field `K` this applies to the closed point
`Spec κ ⟶ Spec R` and to the generic point `Spec K ⟶ Spec R`, whose spectra lie in the site.

For a proper morphism `p : X ⟶ Spec R` which is at-worst-nodal of relative dimension one — with
no regularity assumption on `X` — the special fibre is proper of dimension one over `κ` with
at-worst-nodal singularities, as soon as it is nonempty.

## Main results

* `AlgebraicGeometry.IsStableFamilyOfSchemes.fibre`: the fibre conditions at a field-valued
  point.
* `AlgebraicGeometry.IsStableFamilyOfSchemesOfGenus.specialFibre` and
  `AlgebraicGeometry.IsStableFamilyOfSchemesOfGenus.genericFibre`: the special and generic fibres
  over a discrete valuation ring.
* `Stacks.Models.specialFibre_standing_of_isAtWorstNodal`: the special fibre of a proper
  at-worst-nodal family over a discrete valuation ring, and
  `Stacks.Models.specialFibre_standing_of_isStableFamilyOfSchemesOfGenus` for a stable family.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

/-- A cartesian square of representable presheaves on the big fppf site gives a cartesian square
of schemes. -/
theorem exists_isPullback_toScheme_of_isPullback_yoneda {T U V W : BigFppfOver B integerBase hZ}
    {q : yoneda.obj V ⟶ yoneda.obj T} {v : V ⟶ W} {g : T ⟶ U} {a : W ⟶ U}
    (h : IsPullback q (yoneda.map v) (yoneda.map g) (yoneda.map a)) :
    ∃ q' : V ⟶ T, IsPullback ((BigFppfOver.toScheme B integerBase hZ).map q')
      ((BigFppfOver.toScheme B integerBase hZ).map v)
      ((BigFppfOver.toScheme B integerBase hZ).map g)
      ((BigFppfOver.toScheme B integerBase hZ).map a) := by
  obtain ⟨q', rfl⟩ : ∃ q' : V ⟶ T, yoneda.map q' = q :=
    ⟨Yoneda.fullyFaithful.preimage q, Yoneda.fullyFaithful.map_preimage _⟩
  have hw : q' ≫ g = v ≫ a := yoneda.map_injective ((yoneda.map_comp _ _).trans
    (h.w.trans (yoneda.map_comp _ _).symm))
  have := Space.preservesLimitsOfShape_walkingCospan_toScheme B integerBase hZ
  exact ⟨q', (IsPullback.of_map yoneda hw h).map (BigFppfOver.toScheme B integerBase hZ)⟩

/-- The field-valued point of a scheme `S` of the site given by a morphism `Spec k ⟶ S`. -/
def fieldValuedPointOfHom {S : Scheme.{u}} (hS : B.Contains S) (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) (t : Spec (.of k) ⟶ S) :
    Space.FieldValuedPoint B integerBase hZ (schemeSpace (integerSiteObject B hZ hS)).obj where
  carrier := k
  contained := hk
  toBase := specULiftZIsTerminal.from _
  value := integerSiteMap B hZ hk hS t

/-- **The fibre conditions of a stable family at a field-valued point.** Let `p : X ⟶ S` be a
stable family of curves given by a morphism of schemes, `k` a field with `Spec k` in the site and
`t : Spec k ⟶ S`. Then `X ×_S Spec k` over `k` has genus at least two, no rational tail and no
rational bridge, and its global functions are `k`. -/
theorem IsStableFamilyOfSchemes.fibre {X S : Scheme.{u}} {p : X ⟶ S} {hS : B.Contains S}
    (hst : IsStableFamilyOfSchemes B hZ p hS) (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) (t : Spec (.of k) ⟶ S) :
    HasGenusTwoNoRationalTailNoRationalBridge k (pullback.snd p t) ∧
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (pullback.snd p t).appTop) := by
  obtain ⟨hflat, hproper, hlfp, hfib, hF⟩ := hst
  have hX := Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact p hS
  set F := curveFamilyOfFiberDimensionLE B hZ (integerSiteMap B hZ hX hS p) hflat hproper hlfp
    hfib
  let pt : Space.FieldValuedPoint B integerBase hZ (schemeSpace F.base).obj :=
    fieldValuedPointOfHom hS k hk t
  -- a presentation of the fibre in the site gives the fibre product of schemes
  have key : ∀ (V : BigFppfOver B integerBase hZ) (v : V ⟶ integerSiteObject B hZ hk)
      (q : yoneda.obj V ⟶ yoneda.obj (integerSiteObject B hZ hX)),
      IsPullback q (yoneda.map v) (yoneda.map (integerSiteMap B hZ hX hS p))
        (yoneda.map (integerSiteMap B hZ hk hS t)) →
      ∃ ψ : (BigFppfOver.toScheme B integerBase hZ).obj V ⟶ pullback p t, IsIso ψ ∧
        ψ ≫ pullback.snd p t = (BigFppfOver.toScheme B integerBase hZ).map v ≫ Spec.map (𝟙 _) := by
    intro V v q hsq
    obtain ⟨q', hsq'⟩ := exists_isPullback_toScheme_of_isPullback_yoneda hsq
    have hsq'' : IsPullback ((BigFppfOver.toScheme B integerBase hZ).map q')
        ((BigFppfOver.toScheme B integerBase hZ).map v) p t := hsq'
    refine ⟨hsq''.isoPullback.hom, Iso.isIso_hom _, ?_⟩
    rw [Spec.map_id]
    exact hsq''.isoPullback_hom_snd.trans (Category.comp_id _).symm
  constructor
  · obtain ⟨V, v, q, hsq, hcond⟩ := hF.2 pt
    obtain ⟨ψ, hψ, hw⟩ := key V v q hsq
    exact HasGenusTwoNoRationalTailNoRationalBridge.of_iso (𝟙 _) _ _ ψ hw hcond
  · obtain ⟨V, v, q, hsq⟩ := CurveFamily.exists_isPullback_fieldValuedPoint B hZ F pt
    have hglob := CurveFamily.isIso_appTop_of_isPullback_fieldValuedPoint hF.1.2 hsq
    obtain ⟨ψ, hψ, hw⟩ := key V v q.hom (AlgebraicSpaces.isPullback_hom B integerBase hZ hsq)
    exact isIso_ΓSpecIso_inv_comp_appTop_of_iso (𝟙 _) _ _ ψ hw hglob

/-- **The fibre conditions of a stable family of genus `g` at a field-valued point.** -/
theorem IsStableFamilyOfSchemesOfGenus.fibre {g : ℕ} {X S : Scheme.{u}} {p : X ⟶ S}
    {hS : B.Contains S} (hst : IsStableFamilyOfSchemesOfGenus B hZ g p hS) (k : Type u) [Field k]
    (hk : B.Contains (Spec (.of k))) (t : Spec (.of k) ⟶ S) :
    HasGenusTwoNoRationalTailNoRationalBridge k (pullback.snd p t) ∧
      IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (pullback.snd p t).appTop) :=
  hst.isStableFamilyOfSchemes.fibre k hk t

section DVR

variable (R : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  (K : Type u) [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDomain R] [IsDiscreteValuationRing R] in
/-- The spectrum of the residue field of a local ring whose spectrum lies in the site lies in the
site. -/
theorem contains_spec_residueField_of_contains [IsLocalRing R] (hR : B.Contains (Spec (.of R))) :
    B.Contains (Spec (.of (ResidueField R))) :=
  BigFppfSite.contains_specQuotient B hR (maximalIdeal R)

/-- The spectrum of the fraction field of a discrete valuation ring whose spectrum lies in the site
lies in the site: `Spec K ⟶ Spec R` is an open immersion, hence a quasi-compact monomorphism. -/
theorem contains_spec_fractionRing_of_contains (hR : B.Contains (Spec (.of R))) :
    B.Contains (Spec (.of K)) := by
  have := Stacks.Models.genericFiberSpec_isOpenImmersion (R := R) (K := K)
  exact (Scheme.size_le_of_mono_quasiCompact
    (Spec.map (CommRingCat.ofHom (algebraMap R K)))).trans_lt hR

variable {R K}

/-- **The special fibre of a stable family of genus `g` over a discrete valuation ring** has
genus at least two, no rational tail and no rational bridge, and `H⁰ = κ`. -/
theorem IsStableFamilyOfSchemesOfGenus.specialFibre {g : ℕ} {X : Scheme.{u}}
    {p : X ⟶ Spec (.of R)} {hR : B.Contains (Spec (.of R))}
    (hst : IsStableFamilyOfSchemesOfGenus B hZ g p hR) :
    HasGenusTwoNoRationalTailNoRationalBridge (ResidueField R)
        (pullback.snd p (ContractionUniquenessComplete.closedPoint R)) ∧
      IsIso ((Scheme.ΓSpecIso (.of (ResidueField R))).inv ≫
        (pullback.snd p (ContractionUniquenessComplete.closedPoint R)).appTop) :=
  hst.fibre _ (contains_spec_residueField_of_contains R hR) _

/-- **The generic fibre of a stable family of genus `g` over a discrete valuation ring** has
genus at least two, no rational tail and no rational bridge, and `H⁰ = K`. -/
theorem IsStableFamilyOfSchemesOfGenus.genericFibre {g : ℕ} {X : Scheme.{u}}
    {p : X ⟶ Spec (.of R)} {hR : B.Contains (Spec (.of R))}
    (hst : IsStableFamilyOfSchemesOfGenus B hZ g p hR) :
    HasGenusTwoNoRationalTailNoRationalBridge K
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K)))) ∧
      IsIso ((Scheme.ΓSpecIso (.of K)).inv ≫
        (pullback.snd p (Spec.map (CommRingCat.ofHom (algebraMap R K)))).appTop) :=
  hst.fibre _ (contains_spec_fractionRing_of_contains R K hR) _

end DVR

/-! ### Fibres of an at-worst-nodal family over field points -/

/-- **The fibre of an at-worst-nodal family over a field point.** Let `p : X ⟶ S` be at-worst-nodal
of relative dimension one and `t : Spec F ⟶ S` a morphism from the spectrum of a field inducing an
isomorphism `κ(t) ≅ F` of residue fields. If the fibre product `X ×_S Spec F` is nonempty, it has
dimension one and at-worst-nodal singularities over `F` ([Stacks, Tag 0C59]). -/
theorem topologicalKrullDim_pullback_eq_one_and_hasAtWorstNodalSingularities {X S : Scheme.{u}}
    (p : X ⟶ S) (hnod : IsAtWorstNodalOfRelativeDimensionOne p) {F : Type u} [Field F]
    (t : Spec (.of F) ⟶ S) [IsIso (S.descResidueField (Scheme.stalkClosedPointTo t))]
    [Nonempty (pullback p t : Scheme.{u})] :
    topologicalKrullDim (pullback p t : Scheme.{u}) = 1 ∧
      (letI : (pullback p t).Over (Spec (.of F)) := ⟨pullback.snd p t⟩;
        Stacks.Curves.HasAtWorstNodalSingularities F (pullback p t)) := by
  obtain ⟨-, hlfp, h⟩ := (Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff p).mpr hnod
  obtain ⟨E, -, hE⟩ := exists_iso_fiber_pullback_of_isIso_descResidueField p t
  obtain ⟨-, hdim, hnodal⟩ := h _ ⟨E.inv (Classical.arbitrary _)⟩
  have hdim' : topologicalKrullDim (pullback p t : Scheme.{u}) = 1 :=
    (IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso E).isHomeomorph).symm.trans hdim
  refine ⟨hdim', ?_⟩
  let φ : CommRingCat.of F ⟶ CommRingCat.of (S.residueField (t (IsLocalRing.closedPoint F))) :=
    inv (S.descResidueField (Scheme.stalkClosedPointTo t))
  have : IsIso φ := IsIso.inv_isIso
  have : LocallyOfFiniteType (p.fiberToSpecResidueField (t (IsLocalRing.closedPoint F))) :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd _ _))
  refine Stacks.Curves.hasAtWorstNodalSingularities_of_isIso _ (pullback.snd p t) hdim E.inv
    φ ?_ hnodal
  rw [← hE]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, φ, ← Spec.map_comp, IsIso.inv_hom_id,
    Spec.map_id, Category.comp_id]

/-- A scheme over a field with `H⁰ = k` is nonempty. -/
theorem nonempty_of_isIso_globalSections (k : Type u) [Field k] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of k)) (h : IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop)) : Nonempty V :=
  have := connectedSpace_of_isIso_globalSections k f
  inferInstance

end AlgebraicGeometry

namespace Stacks.Models

open _root_.AlgebraicGeometry

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- **The special fibre of a proper at-worst-nodal family over a discrete valuation ring.** Let
`p : X ⟶ Spec R` be proper and at-worst-nodal of relative dimension one, with nonempty special
fibre; no regularity of `X` is assumed. Then the special fibre is proper over the residue field
`κ`, of dimension one, with at-worst-nodal singularities, and `X` is quasi-compact. -/
theorem specialFibre_standing_of_isAtWorstNodal {X : Scheme.{u}} (p : X ⟶ Spec (.of R))
    [IsProper p] (hnod : IsAtWorstNodalOfRelativeDimensionOne p)
    [Nonempty (pullback p (ContractionUniquenessComplete.closedPoint R) : Scheme.{u})] :
    IsProper (pullback.snd p (ContractionUniquenessComplete.closedPoint R)) ∧
      topologicalKrullDim
        (pullback p (ContractionUniquenessComplete.closedPoint R) : Scheme.{u}) = 1 ∧
      (letI : (pullback p (ContractionUniquenessComplete.closedPoint R)).Over
          (Spec (.of (IsLocalRing.ResidueField R))) :=
        ⟨pullback.snd p (ContractionUniquenessComplete.closedPoint R)⟩;
        Stacks.Curves.HasAtWorstNodalSingularities (IsLocalRing.ResidueField R)
          (pullback p (ContractionUniquenessComplete.closedPoint R))) ∧
      CompactSpace X := by
  have := isIso_descResidueField_of_surjective (IsLocalRing.residue R)
    IsLocalRing.residue_surjective
  obtain ⟨hdim, hnodal⟩ := topologicalKrullDim_pullback_eq_one_and_hasAtWorstNodalSingularities p
    hnod (ContractionUniquenessComplete.closedPoint R)
  exact ⟨inferInstance, hdim, hnodal, QuasiCompact.compactSpace_of_compactSpace p⟩

/-- **The special fibre of a stable family over a discrete valuation ring** is proper of dimension
one over the residue field with at-worst-nodal singularities; it is nonempty since its global
functions are the residue field. -/
theorem specialFibre_standing_of_isStableFamilyOfSchemesOfGenus {B : BigFppfSite.{u}}
    {hZ : B.Contains integerBase} {hR : B.Contains (Spec (.of R))} {g : ℕ} {X : Scheme.{u}}
    {p : X ⟶ Spec (.of R)} (hst : IsStableFamilyOfSchemesOfGenus B hZ g p hR) :
    IsProper (pullback.snd p (ContractionUniquenessComplete.closedPoint R)) ∧
      topologicalKrullDim
        (pullback p (ContractionUniquenessComplete.closedPoint R) : Scheme.{u}) = 1 ∧
      (letI : (pullback p (ContractionUniquenessComplete.closedPoint R)).Over
          (Spec (.of (IsLocalRing.ResidueField R))) :=
        ⟨pullback.snd p (ContractionUniquenessComplete.closedPoint R)⟩;
        Stacks.Curves.HasAtWorstNodalSingularities (IsLocalRing.ResidueField R)
          (pullback p (ContractionUniquenessComplete.closedPoint R))) ∧
      CompactSpace X := by
  have : IsProper p := hst.isProper
  have := nonempty_of_isIso_globalSections _ _ hst.specialFibre.2
  exact specialFibre_standing_of_isAtWorstNodal p
    (hst.isAtWorstNodalOfRelativeDimensionOne fun _ hF => hF.1.1)

end Stacks.Models

end
