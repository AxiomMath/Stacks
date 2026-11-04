module

public import StacksFrontier.AlgebraicGeometry.Limits.ChowLemmaNoetherian0200
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.Properness
public import StacksFrontier.AlgebraicGeometry.Limits.NoetherianValuativeCriterion.Separatedness
public import StacksFrontier.AlgebraicGeometry.Limits.ProperCheckSquare
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.Morphisms.Valuative.ImmersionClosedness
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianValuativeSeparatedness
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.OpenImmersionCriterion
public import StacksFrontier.RingTheory.GeometricallyIntegral.NowhereDenseFibreAux
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The valuative criterion for properness at the generic points of the source

For a morphism of finite type to a locally Noetherian scheme it is enough to test the valuative
criterion for properness on the discrete valuation subrings of the residue fields at the generic
points of the irreducible components of the source, with the generic arrow the canonical one.
This is condition (4) of [Stacks, Tag 0208], and this file proves that it implies properness.

## Main results

* `AlgebraicGeometry.isProper_of_genericDiscreteValuativeCriterion`: **condition (4) of
  [Stacks, Tag 0208] implies condition (1)**, that is, properness.

## Implementation notes

The source deduces this implication from Chow's lemma over a Noetherian base, and so does the
proof here.  Chow's lemma in that form is `AlgebraicGeometry.hasDenseChowModification`, which
carries `@[stacks 0200]` unconditionally; documentation elsewhere in this repository describing
Chow's lemma over a Noetherian base as unavailable or available only conditionally predates that
result.

The uniqueness half of the criterion gives separatedness at once, by condition (4) of
[Stacks, Tag 0207] — `AlgebraicGeometry.isSeparated_tfae_of_locallyOfFiniteType` — so Chow's
lemma applies.  Properness is Zariski-local at the target, so the base may be taken affine and
hence Noetherian; the criterion itself is *not* restricted to the open subscheme, which would
mean transporting a discrete valuation subring of a residue field along an open immersion.
Instead the Chow modification is taken of the restricted morphism while the criterion is still
applied to the original morphism, and the lift it produces is descended to the open subscheme.

The argument is then the one of the source.  If the immersion into the projective space is not a
closed immersion, some point lies in the closure of its image but not in the image; that point lies
in the closure of the image of a single irreducible component, so the specialization is realized by
a discrete valuation subring of the residue field at the generic point of that component
(`AlgebraicGeometry.exists_isDiscreteValuationRing_subring_of_specializes_of_isImmersion`, which
packages the geometric inputs of the proof of [Stacks, Tag 0207]).  The criterion lifts the
resulting arrow to the target, properness of the modification lifts it to the source of the
immersion, and separatedness of the projective space over the base identifies the two arrows out of
the spectrum of the subring — exhibiting the point in the image after all.

## References

* [Stacks Project, Tag 0208](https://stacks.math.columbia.edu/tag/0208)
* [Stacks Project, Tag 0207](https://stacks.math.columbia.edu/tag/0207)
* [Stacks Project, Tag 0200](https://stacks.math.columbia.edu/tag/0200)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

private theorem exists_genericPoint_specializes_of_mem_closure_range
    {Yc P : Scheme.{u}} [IsNoetherian Yc] (i : Yc ⟶ P) {y : P}
    (hy : y ∈ closure (Set.range i.base)) :
    ∃ η ∈ genericPoints (Yc : Type u), i η ⤳ y := by
  have hfin : (genericPoints (Yc : Type u)).Finite :=
    genericPoints.finite NoetherianSpace.finite_irreducibleComponents
  have h1 : Set.range i.base ⊆ closure (i.base '' genericPoints (Yc : Type u)) := by
    rintro _ ⟨x, rfl⟩
    have hx : x ∈ closure (genericPoints (Yc : Type u)) := by
      rw [genericPoints.closure]; trivial
    exact image_closure_subset_closure_image i.continuous ⟨x, hx, rfl⟩
  have h2 := closure_minimal h1 (isClosed_closure (s := i.base '' genericPoints (Yc : Type u)))
  have h3 : i.base '' genericPoints (Yc : Type u) =
      ⋃ η ∈ genericPoints (Yc : Type u), ({i.base η} : Set P) := by
    ext z; simp [eq_comm]
  rw [h3, hfin.closure_biUnion] at h2
  obtain ⟨η, hη, hz⟩ := Set.mem_iUnion₂.mp (h2 hy)
  exact ⟨η, hη, specializes_iff_mem_closure.mpr hz⟩

/-- The source of a quasi-compact morphism of finite type to a Noetherian scheme is Noetherian. -/
private theorem isNoetherian_of_locallyOfFiniteType_of_quasiCompact {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsNoetherian Y] [LocallyOfFiniteType f] [QuasiCompact f] : IsNoetherian X :=
  have := LocallyOfFiniteType.isLocallyNoetherian f
  have := QuasiCompact.compactSpace_of_compactSpace f
  ⟨⟩

variable {V W : Scheme.{u}}

/-- **Chow's lemma with the modification pinned to the dense open.** Over a Noetherian base a
separated morphism of finite type has a dense Chow modification whose source is the closure of
the locus over the dense open, so that every generic point of that source lies over a generic
point of the target and the modification identifies the residue fields there.

Chow's lemma itself gives a modification which is an isomorphism over a dense open subscheme of
the target but says nothing about the locus over it being dense in the source; replacing the
source with the scheme-theoretic image of that locus makes it so, and costs neither properness
nor surjectivity nor the projective immersion. -/
@[ega "II 5.6.1" "Clause (i), special case"]
private theorem exists_chowModification_genericPoints (p : V ⟶ W)
    [IsNoetherian W] [IsSeparated p] [LocallyOfFiniteType p] [QuasiCompact p] :
    ∃ (n : ℕ) (Y : Scheme.{u}) (π : Y ⟶ V) (i : Y ⟶ ProjectiveSpace n W),
      IsProper π ∧ Surjective π ∧ IsImmersion i ∧
        π ≫ p = i ≫ (ProjectiveSpace n W ↘ W) ∧
        ∀ η ∈ genericPoints Y, π η ∈ genericPoints V ∧ IsIso (π.residueFieldMap η) := by
  have : IsNoetherian V := isNoetherian_of_locallyOfFiniteType_of_quasiCompact p
  obtain ⟨n, X', π, i, U, hπ, hsurj, himm, hcomm, hUdense, hUiso⟩ := hasDenseChowModification p
  have : IsProper π := hπ
  have : IsImmersion i := himm
  have : IsNoetherian X' := isNoetherian_of_locallyOfFiniteType_of_quasiCompact π
  set O : X'.Opens := π ⁻¹ᵁ U with hOdef
  have hqcO : QuasiCompact O.ι := inferInstance
  have hiso : IsIso (π ∣_ U) := hUiso
  have htO : IsOpenImmersion O.ι.toImage := isOpenImmersion_toImage O.ι (Or.inl hqcO)
  have hdomtO : IsDominant O.ι.toImage := isDominant_toImage O.ι (Or.inl hqcO)
  have hOopen : IsOpenImmersion (O.ι ≫ π) := by
    rw [← morphismRestrict_ι π U]; infer_instance
  have hfac : O.ι.toImage ≫ (O.ι.imageι ≫ π) = O.ι ≫ π := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι]
  refine ⟨n, O.ι.image, O.ι.imageι ≫ π, O.ι.imageι ≫ i, inferInstance, ?_, inferInstance, ?_, ?_⟩
  · refine surjective_of_isProper_of_dense _ U (inv (π ∣_ U) ≫ O.ι.toImage) ?_ hUdense
    rw [Category.assoc, hfac, ← morphismRestrict_ι π U, IsIso.inv_hom_id_assoc]
  · rw [Category.assoc, Category.assoc, hcomm]
  · intro η hη
    have hNoethY : IsLocallyNoetherian O.ι.image :=
      LocallyOfFiniteType.isLocallyNoetherian (O.ι.imageι ≫ π)
    have hopen : IsOpen (Set.range O.ι.toImage.base) := O.ι.toImage.isOpenEmbedding.isOpen_range
    have hdense : Dense (Set.range O.ι.toImage.base) := hdomtO.denseRange
    obtain ⟨o, rfl⟩ : η ∈ Set.range O.ι.toImage.base :=
      Scheme.mem_of_mem_genericPoints_of_dense _ hopen hdense hη
    have ho : o ∈ genericPoints O.toScheme :=
      mem_genericPoints_of_isOpenImmersion_apply O.ι.toImage hη
    have hpt : (O.ι.imageι ≫ π) (O.ι.toImage.base o) = (O.ι ≫ π) o := by
      rw [← Scheme.Hom.comp_apply, hfac]
    refine ⟨by rw [hpt]; exact genericPoints_map_of_openImmersion (O.ι ≫ π) ho, ?_⟩
    have he : ((O.ι.imageι ≫ π).residueFieldMap (O.ι.toImage.base o)) ≫
        O.ι.toImage.residueFieldMap o =
        (V.residueFieldCongr (by rw [← hpt])).hom ≫ (O.ι ≫ π).residueFieldMap o := by
      rw [← Scheme.residueFieldMap_comp, Scheme.Hom.residueFieldMap_congr hfac o]
      rfl
    have : IsIso (((O.ι.imageι ≫ π).residueFieldMap (O.ι.toImage.base o)) ≫
        O.ι.toImage.residueFieldMap o) := by rw [he]; infer_instance
    exact IsIso.of_isIso_comp_right _ (O.ι.toImage.residueFieldMap o)


/-- The projective immersion of a Chow modification of `p` over an open subscheme `Wo` of the
base is a closed immersion, granted condition (4) of Stacks 0208 for `p` itself.

A point in the closure of the image of the immersion lies in the closure of the image of some
irreducible component of the source, so a discrete valuation subring of the residue field at the
generic point of that component realizes the specialization inside the projective space.  The
assumed criterion lifts the induced arrow to `V`, properness of the modification lifts it
further to the source of the immersion, and separatedness of the projective space over the base
identifies the two resulting arrows: the lifted one passes through the image, and its closed
point is the given point. -/
private theorem isClosedImmersion_of_genericDiscreteValuativeCriterion
    {n : ℕ} {Yc : Scheme.{u}} (p : V ⟶ W) (Wo : W.Opens)
    (π : Yc ⟶ (p ⁻¹ᵁ Wo).toScheme) (i : Yc ⟶ ProjectiveSpace n Wo.toScheme)
    [IsLocallyNoetherian W] [IsProper π] [IsImmersion i] [IsNoetherian Yc]
    (hcomm : (π ≫ (p ⁻¹ᵁ Wo).ι) ≫ p =
      i ≫ (ProjectiveSpace n Wo.toScheme ↘ Wo.toScheme) ≫ Wo.ι)
    (hgen : ∀ η ∈ genericPoints (Yc : Type u),
      (π ≫ (p ⁻¹ᵁ Wo).ι) η ∈ genericPoints (V : Type u) ∧
        IsIso ((π ≫ (p ⁻¹ᵁ Wo).ι).residueFieldMap η))
    (h : GenericDiscreteValuativeCriterion p) :
    IsClosedImmersion i := by
  classical
  set ι₀ : (p ⁻¹ᵁ Wo).toScheme ⟶ V := (p ⁻¹ᵁ Wo).ι with hι₀
  set q : Yc ⟶ V := π ≫ ι₀ with hq
  set prW : ProjectiveSpace n Wo.toScheme ⟶ W :=
    (ProjectiveSpace n Wo.toScheme ↘ Wo.toScheme) ≫ Wo.ι with hprW
  have hqp : q ≫ p = i ≫ prW := by rw [hq, hprW, ← Category.assoc]; exact hcomm
  rw [isClosedImmersion_iff_isClosed_range]
  apply isClosed_of_closure_subset
  intro y hy
  obtain ⟨η, hη, hspec⟩ := exists_genericPoint_specializes_of_mem_closure_range i hy
  by_cases hyeq : i η = y
  · exact ⟨η, hyeq⟩
  obtain ⟨hqη, hρiso⟩ := hgen η hη
  have hPN : IsLocallyNoetherian (ProjectiveSpace n Wo.toScheme) :=
    LocallyOfFiniteType.isLocallyNoetherian (ProjectiveSpace n Wo.toScheme ↘ Wo.toScheme)
  set ρ : V.residueField (q η) ⟶ Yc.residueField η := q.residueFieldMap η with hρdef
  have hρ : IsIso ρ := hρiso
  set τ : (Yc.residueField η : Type u) ≃+* (V.residueField (q η) : Type u) :=
    (asIso ρ).commRingCatIsoToRingEquiv.symm with hτdef
  have hinv : CommRingCat.ofHom τ.toRingHom = inv ρ := rfl
  have hτρ : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ Spec.map ρ = 𝟙 _ := by
    rw [← Spec.map_comp, hinv, IsIso.hom_inv_id, Spec.map_id]; rfl
  have hfrom : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ Yc.fromSpecResidueField η ≫ q =
      V.fromSpecResidueField (q η) := by
    rw [← q.SpecMap_residueFieldMap_fromSpecResidueField η, ← hρdef, ← Category.assoc, hτρ,
      Category.id_comp]
  have hfromp : Spec.map (CommRingCat.ofHom τ.toRingHom) ≫
      Yc.fromSpecResidueField η ≫ q ≫ p = V.fromSpecResidueField (q η) ≫ p := by
    rw [← hfrom]; simp only [Category.assoc]
  obtain ⟨B, hB, hBfrac, m, hm, hmy⟩ :=
    exists_isDiscreteValuationRing_subring_of_specializes_of_isImmersion i η hspec hyeq τ
  have hBsub : Spec.map (CommRingCat.ofHom B.subtype) ≫ m ≫ prW =
      V.fromSpecResidueField (q η) ≫ p := by
    have h1 := congrArg (fun k => k ≫ prW) hm
    simp only [Category.assoc] at h1
    rw [h1, ← hqp]
    exact hfromp
  set i₂ : Spec (.of B) ⟶ W := m ≫ prW with hi₂
  have sq : CommSq (V.fromSpecResidueField (q η))
      (Spec.map (CommRingCat.ofHom B.subtype)) p i₂ := ⟨hBsub.symm⟩
  obtain ⟨⟨l, hl₁, hl₂⟩⟩ := (h (q η) hqη B hB hBfrac i₂ sq).1
  -- descend the lift to the open subscheme over `Wo`
  have hlrange : Set.range l.base ⊆ Set.range ι₀.base := by
    rintro _ ⟨x, rfl⟩
    rw [hι₀, Scheme.Opens.range_ι]
    show p (l.base x) ∈ Wo
    have hkey : l ≫ p = m ≫ (ProjectiveSpace n Wo.toScheme ↘ Wo.toScheme) ≫ Wo.ι := by
      rw [hl₂, hi₂, hprW]
    have hpt := congrArg (fun k : Spec (.of B) ⟶ W => k.base x) hkey
    simp only [Scheme.Hom.comp_apply] at hpt
    have hmem : p.base (l.base x) ∈ Set.range Wo.ι.base := by
      rw [hpt]; exact Set.mem_range_self _
    rw [Scheme.Opens.range_ι] at hmem
    exact hmem
  set l₀ : Spec (.of B) ⟶ (p ⁻¹ᵁ Wo).toScheme := IsOpenImmersion.lift ι₀ l hlrange with hl₀def
  have hl₀ : l₀ ≫ ι₀ = l := IsOpenImmersion.lift_fac _ _ _
  have hvc : ValuativeCriterion π := by
    have hg : IsProper π := inferInstance
    rw [IsProper.eq_valuativeCriterion] at hg
    exact hg.1.1.1
  set b₁ : Spec (.of (V.residueField (q η) : Type u)) ⟶ Yc :=
    Spec.map (CommRingCat.ofHom τ.toRingHom) ≫ Yc.fromSpecResidueField η with hb₁def
  have hb₁q : b₁ ≫ q = V.fromSpecResidueField (q η) := by
    rw [hb₁def, Category.assoc]; exact hfrom
  have hb₁π : b₁ ≫ π = Spec.map (CommRingCat.ofHom B.subtype) ≫ l₀ := by
    apply (cancel_mono ι₀).1
    rw [Category.assoc, ← hq, hb₁q, Category.assoc, hl₀]
    exact hl₁.symm
  let D : ValuativeCommSq π :=
    { R := B
      K := (V.residueField (q η) : Type u)
      i₁ := b₁
      i₂ := l₀
      commSq := ⟨by rw [hb₁π]; rfl⟩ }
  have hb₁' : Spec.map (CommRingCat.ofHom B.subtype) ≫ (hvc D).some.default.l = b₁ :=
    (hvc D).some.default.fac_left
  have hb₂' : (hvc D).some.default.l ≫ π = l₀ := (hvc D).some.default.fac_right
  set b := (hvc D).some.default.l with hbdef
  have hsepW : IsSeparated prW := by rw [hprW]; infer_instance
  have hb₁i : Spec.map (CommRingCat.ofHom B.subtype) ≫ (b ≫ i) = b₁ ≫ i := by
    rw [← Category.assoc, hb₁']
  have hbipr : (b ≫ i) ≫ prW = i₂ := by
    simp only [Category.assoc]
    rw [← hqp, hq]
    simp only [← Category.assoc]
    rw [hb₂', hl₀, hl₂]
  have hmE : Spec.map (CommRingCat.ofHom B.subtype) ≫ m = b₁ ≫ i := by
    rw [hm, hb₁def]; simp only [Category.assoc]
  have hEsq : (b₁ ≫ i) ≫ prW = Spec.map (CommRingCat.ofHom B.subtype) ≫ i₂ := by
    rw [← hbipr, ← hb₁i]; simp only [Category.assoc]
  let E : ValuativeCommSq prW :=
    { R := B
      K := (V.residueField (q η) : Type u)
      i₁ := b₁ ≫ i
      i₂ := i₂
      commSq := ⟨hEsq⟩ }
  have hbi : b ≫ i = m :=
    congrArg CommSq.LiftStruct.l
      (@Subsingleton.elim _ (IsSeparated.valuativeCriterion prW E)
        (⟨b ≫ i, hb₁i, hbipr⟩ : E.commSq.LiftStruct)
        (⟨m, hmE, hi₂.symm⟩ : E.commSq.LiftStruct))
  refine ⟨b (@IsLocalRing.closedPoint B _
    (@IsDiscreteValuationRing.toIsLocalRing B _ _ hB)), ?_⟩
  rw [← hmy, ← hbi]
  rfl

/-- **[Stacks, Tag 0208], condition (4) implies condition (1).** A morphism of finite type to a
locally Noetherian scheme is proper as soon as every valuative diagram whose valuation ring is a
discrete valuation subring of the residue field at a generic point of an irreducible component
of the source, with that residue field as its fraction field, and whose generic arrow is the
canonical one, has exactly one dotted arrow. -/
@[stacks 0208 "condition (4) implies condition (1)",
  ega "II 7.3.8" "(b)⇒(a)",
  ega "IV 15.7.5" "c⇒a",
  ega "IV 18.10.20" "partial"]
theorem isProper_of_genericDiscreteValuativeCriterion (p : V ⟶ W)
    [IsLocallyNoetherian W] [LocallyOfFiniteType p] [QuasiCompact p]
    (h : GenericDiscreteValuativeCriterion p) : IsProper p := by
  have hsep : IsSeparated p :=
    ((isSeparated_tfae_of_locallyOfFiniteType p).out 4 1).mp
      fun η hη A hA hAK i₂ sq => (h η hη A hA hAK i₂ sq).2
  apply IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) (f := p)
    (fun j : W.affineCover.I₀ => (W.affineCover.f j).opensRange)
    W.affineCover.iSup_opensRange
  intro j
  set Wo : W.Opens := (W.affineCover.f j).opensRange with hWo
  have hWoAff : IsAffine Wo.toScheme := isAffineOpen_opensRange (W.affineCover.f j)
  have : IsNoetherian Wo.toScheme := ⟨⟩
  obtain ⟨n, Yc, π, i, hπ, hsurj, himm, hcomm0, hgen0⟩ :=
    exists_chowModification_genericPoints (p ∣_ Wo)
  have : IsProper π := hπ
  have : Surjective π := hsurj
  have : IsImmersion i := himm
  have : IsNoetherian (p ⁻¹ᵁ Wo).toScheme :=
    isNoetherian_of_locallyOfFiniteType_of_quasiCompact (p ∣_ Wo)
  have : IsNoetherian Yc := isNoetherian_of_locallyOfFiniteType_of_quasiCompact π
  have hcomm : (π ≫ (p ⁻¹ᵁ Wo).ι) ≫ p =
      i ≫ (ProjectiveSpace n Wo.toScheme ↘ Wo.toScheme) ≫ Wo.ι := by
    rw [Category.assoc, ← morphismRestrict_ι p Wo, ← Category.assoc, hcomm0, Category.assoc]
  have hgen : ∀ η ∈ genericPoints (Yc : Type u),
      (π ≫ (p ⁻¹ᵁ Wo).ι) η ∈ genericPoints (V : Type u) ∧
        IsIso ((π ≫ (p ⁻¹ᵁ Wo).ι).residueFieldMap η) := by
    intro η hη
    obtain ⟨hmem, hiso⟩ := hgen0 η hη
    refine ⟨genericPoints_map_of_openImmersion (p ⁻¹ᵁ Wo).ι hmem, ?_⟩
    rw [Scheme.residueFieldMap_comp]
    exact CategoryTheory.IsIso.comp_isIso'
      (inferInstanceAs (IsIso ((p ⁻¹ᵁ Wo).ι.residueFieldMap (π η)))) hiso
  have hci : IsClosedImmersion i :=
    isClosedImmersion_of_genericDiscreteValuativeCriterion p Wo π i hcomm hgen h
  exact isProper_of_surjective_of_isClosedImmersion_projectiveSpace (p ∣_ Wo) π i hcomm0

/-- **[Stacks, Tag 0208].** Let `S` be locally Noetherian and `f : X ⟶ S` of finite type. The
following are equivalent:

1. `f` is proper;
2. every valuative diagram for `f` has exactly one dotted arrow;
3. every valuative diagram for `f` whose valuation ring is a discrete valuation ring has exactly
   one dotted arrow;
4. for every generic point `η` of an irreducible component of `X` and every discrete valuation
   subring `A` of `κ(η)` with fraction field `κ(η)`, every valuative diagram whose generic arrow
   is the canonical `Spec κ(η) ⟶ X` has exactly one dotted arrow, that is,
   `AlgebraicGeometry.GenericDiscreteValuativeCriterion f`.

Conditions (1) to (3) are `AlgebraicGeometry.isProper_tfae_of_isFiniteType`; (3) implies (4)
because such a diagram is a valuative diagram over a discrete valuation ring, and (4) implies (1)
is `AlgebraicGeometry.isProper_of_genericDiscreteValuativeCriterion`. -/
@[stacks 0208, ega "II 7.3.8", ega "IV 15.7.5" "a⇔c"]
theorem isProper_tfae_genericDiscreteValuativeCriterion {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f] :
    List.TFAE
      [ IsProper f,
        ValuativeCriterion f,
        ∀ D : ValuativeCommSq f,
          IsDiscreteValuationRing D.R → Nonempty (Unique D.commSq.LiftStruct),
        GenericDiscreteValuativeCriterion f ] := by
  tfae_have 1 ↔ 2 := (isProper_tfae_of_isFiniteType f).out 1 2
  tfae_have 2 ↔ 3 := (isProper_tfae_of_isFiniteType f).out 2 3
  tfae_have 3 → 4 := by
    intro h η _ A hA _ i₂ sq
    exact (unique_iff_subsingleton_and_nonempty _).mp
      (h { R := A, K := X.residueField η, i₁ := X.fromSpecResidueField η, i₂ := i₂,
           commSq := sq } hA) |>.symm
  tfae_have 4 → 1 := isProper_of_genericDiscreteValuativeCriterion f
  tfae_finish

end AlgebraicGeometry

end
