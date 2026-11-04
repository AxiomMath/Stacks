module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.LipmanEquivalencePort
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DominateByNormalizedBlowUps.Basic

/-!
# Dominating a modification by normalized blowups centred outside an open

Let `X` be a Noetherian normal Nagata scheme of dimension at most two and let `f : Y ⟶ X` be a
proper birational morphism which is an isomorphism over an open `V` of `X`. Then `Y` is
dominated by a finite sequence of normalized blowups of `X` at closed points, each lying over a
point of `X` outside `V`, every stage of which is proper over `X`. This refines
`Stacks.ResolutionOfSurfaces.exists_normalizedBlowUpChain_dominating`: since `X` is normal the
sequence starts at `X` itself, and the centres avoid the locus over which `f` is already an
isomorphism.

The proof is that of [Stacks, Tag 0BBT], keeping track of the open `V`. After replacing `Y` by
its normalization, which changes nothing over the normal open `f⁻¹ V ≅ V`, every centre chosen
by the induction is the image `f y` of a non-closed point `y` of `Y` with closed image. Such an
image lies outside `V`, for `f` is injective over `V`, so that `{y} = f⁻¹ {f y}` would be closed.
Moreover the common normal modification `T'` of `Y` and of the normalized blowup `X'` of `X` at
`f y` constructed in the induction is finite over `Y ×_X X'`, which is isomorphic to `X'` over
the inverse image of `V`; so `T' ⟶ X'` has finite fibres over that inverse image, and being
proper and birational onto a normal scheme it is an isomorphism there. The induction therefore
continues with the inverse image of `V` in place of `V`.

## Main results

* `AlgebraicGeometry.reflTransGen_isProperNormalizedBlowUpOutside_map`: a sequence of proper
  normalized blowups over `X'` centred outside the inverse image of an open `V` of `X` is, via
  a proper morphism `X' ⟶ X`, a sequence over `X` centred outside `V`.
* `Stacks.ResolutionOfSurfaces.exists_reflTransGen_isProperNormalizedBlowUpOutside_dominating`:
  a proper birational morphism to a Noetherian normal Nagata scheme of dimension at most two
  which is an isomorphism over an open `V` is dominated by a sequence of proper normalized
  blowups at closed points lying over the complement of `V`.

## References

* [Stacks Project, Tag 0BBT](https://stacks.math.columbia.edu/tag/0BBT)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A proper normalized blowup over `X'` centred outside the inverse image of an open `V` of `X`
is, via a proper morphism `q : X' ⟶ X`, a proper normalized blowup over `X` centred outside
`V`. -/
theorem IsProperNormalizedBlowUpOutside.map {X X' : Scheme.{u}} (q : X' ⟶ X) [IsProper q]
    {V : X.Opens} {A B : Over X'} (h : IsProperNormalizedBlowUpOutside (q ⁻¹ᵁ V) A B) :
    IsProperNormalizedBlowUpOutside V ((Over.map q).obj A) ((Over.map q).obj B) := by
  obtain ⟨⟨hA, x, hx, hout, e, he⟩, hB⟩ := h
  refine ⟨⟨hA, x, hx, hout, e, ?_⟩, ?_⟩
  · change e.hom ≫ Stacks.Blowup.normalizedBlowUp A.left hA x hx ≫ A.hom ≫ q = B.hom ≫ q
    rw [← he]
    simp only [Category.assoc]
  · have : IsProper B.hom := hB
    exact (inferInstance : IsProper (B.hom ≫ q))

/-- A sequence of proper normalized blowups over `X'` centred outside the inverse image of an
open `V` of `X` is, via a proper morphism `q : X' ⟶ X`, a sequence of proper normalized blowups
over `X` centred outside `V`. -/
theorem reflTransGen_isProperNormalizedBlowUpOutside_map {X X' : Scheme.{u}} (q : X' ⟶ X)
    [IsProper q] {V : X.Opens} {A B : Over X'}
    (h : Relation.ReflTransGen (IsProperNormalizedBlowUpOutside (q ⁻¹ᵁ V)) A B) :
    Relation.ReflTransGen (IsProperNormalizedBlowUpOutside V) ((Over.map q).obj A)
      ((Over.map q).obj B) := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih => exact ih.tail (hstep.map q)

end AlgebraicGeometry

open AlgebraicGeometry

namespace Stacks.ResolutionOfSurfaces

attribute [local instance] isLocalHom_ringEquiv

/-- A normal scheme is reduced. -/
private instance isReduced_of_isNormal' (X : Scheme.{u}) [IsNormal X] : IsReduced X :=
  isReduced_of_isReduced_stalk X

/-- A Noetherian normal scheme is covered by integral opens. -/
private lemma exists_integral_open_of_isNormal {X : Scheme.{u}} [IsNoetherian X] [IsNormal X]
    (x : X) : ∃ U : X.Opens, x ∈ U ∧ IsIntegral U.toScheme := by
  let hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompactOpen_of_isNoetherian
  have : IsIso (Scheme.normalization X hX) :=
    (Scheme.isIso_normalization_iff_isNormal X hX).2 inferInstance
  let k := inv (Scheme.normalization X hX)
  obtain ⟨U', hxU', hU'⟩ := exists_integral_open_normalization hX (k x)
  refine ⟨k ⁻¹ᵁ U', hxU', ?_⟩
  have : Nonempty (k ⁻¹ᵁ U').toScheme := ⟨⟨x, hxU'⟩⟩
  exact isIntegral_of_isOpenImmersion (k ∣_ U')

/-- If `l` is an isomorphism over `V`, a non-closed point with closed image maps outside `V`. -/
private lemma apply_not_mem_of_isIso_morphismRestrict {S T : Scheme.{u}} (l : T ⟶ S)
    (V : S.Opens) (hV : IsIso (l ∣_ V)) (y : T) (hy : ¬ IsClosed ({y} : Set T))
    (hly : IsClosed ({l y} : Set S)) : l y ∉ V := fun hmem =>
  hy (isClosed_singleton_of_isIso_restrict l V y hmem hly)

/-- In a commutative square `p ≫ l = g ≫ q` whose comparison morphism to `T ×_S S'` is finite,
with `g` proper and birational onto a Noetherian normal scheme, `g` is an isomorphism over the
inverse image of every open over which `l` is an isomorphism: there `T ×_S S' ⟶ S'` is an
isomorphism, so `g` has finite fibres. -/
private lemma isIso_morphismRestrict_preimage_of_finite_comparison
    {S T S' T' : Scheme.{u}} [IsNoetherian S'] [IsNormal S'] [IsReduced T']
    (l : T ⟶ S) (q : S' ⟶ S) (p : T' ⟶ T) (g : T' ⟶ S') (h : p ≫ l = g ≫ q)
    [IsProper g] (hg : IsBirational g) [IsFinite (Limits.pullback.lift p g h)]
    (V : S.Opens) (hV : IsIso (l ∣_ V)) : IsIso (g ∣_ (q ⁻¹ᵁ V)) := by
  obtain ⟨M, hM⟩ := exists_maximal_isomorphism_open g
  refine isIso_morphismRestrict_of_le g M _ ?_ hM.1
  intro x hx
  let c := Limits.pullback.lift p g h
  let s := Limits.pullback.snd l q
  have hsV : IsIso (s ∣_ (q ⁻¹ᵁ V)) := isIso_pullback_snd_over_open l q V hV
  have hsub : (s ⁻¹' {x}).Subsingleton := by
    intro w (hw : s w = x) w' (hw' : s w' = x)
    have hwV : w ∈ s ⁻¹ᵁ (q ⁻¹ᵁ V) := show s w ∈ q ⁻¹ᵁ V from hw ▸ hx
    have hw'V : w' ∈ s ⁻¹ᵁ (q ⁻¹ᵁ V) := show s w' ∈ q ⁻¹ᵁ V from hw' ▸ hx
    have heq : (s ∣_ (q ⁻¹ᵁ V)) ⟨w, hwV⟩ = (s ∣_ (q ⁻¹ᵁ V)) ⟨w', hw'V⟩ :=
      Subtype.ext <| (morphismRestrict_base_coe s _ ⟨w, hwV⟩).trans
        ((hw.trans hw'.symm).trans (morphismRestrict_base_coe s _ ⟨w', hw'V⟩).symm)
    exact congrArg Subtype.val ((s ∣_ (q ⁻¹ᵁ V)).homeomorph.injective heq)
  have hfin : (g ⁻¹' {x}).Finite := by
    have hpre : g ⁻¹' {x} = c ⁻¹' (s ⁻¹' {x}) := by
      ext z
      change g z = x ↔ s (c z) = x
      rw [show g = c ≫ s from (Limits.pullback.lift_snd p g h).symm, Scheme.Hom.comp_apply]
    rw [hpre]
    exact hsub.finite.preimage' fun w _ => c.finite_preimage_singleton w
  have := IsNormal.stalk_normal x
  obtain ⟨W, hxW, hW⟩ := exists_isIso_restrict_of_finite_fiber_of_normal g hg x hfin
  exact hM.2 hW hxW

/-- `l` is dominated by a sequence of proper normalized blowups of its target at closed points
lying over the complement of `V`. -/
private abbrev HasCentredDominatingTail {S T : Scheme.{u}} (V : S.Opens) (l : T ⟶ S) : Prop :=
  ∃ Z : Over S, Relation.ReflTransGen (IsProperNormalizedBlowUpOutside V) (Over.mk (𝟙 S)) Z ∧
    ∃ h : Z.left ⟶ T, h ≫ l = Z.hom

private lemma hasCentredDominatingTail_of_square
    {S T S' T' : Scheme.{u}} {l : T ⟶ S} {q : S' ⟶ S} [IsProper q]
    {p : T' ⟶ T} {g : T' ⟶ S'} {V : S.Opens}
    (hq : IsProperNormalizedBlowUpOutside V (Over.mk (𝟙 S)) (Over.mk q))
    (hcomm : p ≫ l = g ≫ q) (hg : HasCentredDominatingTail (q ⁻¹ᵁ V) g) :
    HasCentredDominatingTail V l := by
  obtain ⟨Z, hZ, h, hh⟩ := hg
  refine ⟨(Over.map q).obj Z, ?_, h ≫ p, ?_⟩
  · have h0 : (Over.map q).obj (Over.mk (𝟙 S')) = Over.mk q :=
      congrArg Over.mk (Category.id_comp q)
    exact .head hq (h0 ▸ reflTransGen_isProperNormalizedBlowUpOutside_map q hZ)
  · change (h ≫ p) ≫ l = Z.hom ≫ q
    rw [Category.assoc, hcomm, ← Category.assoc, hh]

/-- The normalized blowup of a normal Noetherian Nagata scheme of dimension at most two at a
closed non-generic point outside an open `W` inherits these hypotheses, is a proper normalized
blowup centred outside `W`, and has principal pulled-back maximal ideals over the centre. -/
private lemma exists_normalizedBlowUpOutside_at_closed_point
    {S : Scheme.{u}} [IsNoetherian S] [IsNormal S]
    (hNagata : IsNagataScheme S) (hdim : topologicalKrullDim S ≤ 2)
    (hlocal : ∀ x : S, ∃ U : S.Opens, x ∈ U ∧ IsIntegral U.toScheme)
    (x : S) (hx : IsClosed ({x} : Set S)) (hgen : x ∉ genericPoints S) (W : S.Opens)
    (hxW : x ∉ W) :
    ∃ (S' : Scheme.{u}) (q : S' ⟶ S), IsProper q ∧ IsNoetherian S' ∧ IsNormal S' ∧
      IsNagataScheme S' ∧ (∀ x : S', ∃ U : S'.Opens, x ∈ U ∧ IsIntegral U.toScheme) ∧
      IsBirational q ∧ topologicalKrullDim S' ≤ 2 ∧
      IsProperNormalizedBlowUpOutside W (Over.mk (𝟙 S)) (Over.mk q) ∧
      ∀ w : S', q w = x → ∃ d : S'.presheaf.stalk w,
        (IsLocalRing.maximalIdeal (S.presheaf.stalk (q w))).map (q.stalkMap w).hom =
          Ideal.span {d} := by
  let hS : ∀ U : S.Opens, IsCompact (U : Set S) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompactOpen_of_isNoetherian
  let S' := Stacks.Blowup.normalizedBlowUpScheme S hS x hx
  let q : S' ⟶ S := Stacks.Blowup.normalizedBlowUp S hS x hx
  have : IsProper q := Stacks.Blowup.isProper_normalizedBlowUp hS x hx hNagata
  have : IsNoetherian S' := isNoetherian_of_isProper_over_noetherian q
  have : IsNormal S' := Stacks.Blowup.isNormal_normalizedBlowUpScheme hS x hx
  have hqbir : IsBirational q :=
    isBirational_normalizedBlowUp_of_genericPoints_disjoint_center hS x hx
      (Set.disjoint_singleton_right.mpr hgen)
  refine ⟨S', q, inferInstance, inferInstance, inferInstance,
    Stacks.Blowup.isNagataScheme_normalizedBlowUpScheme hS x hx hNagata,
    exists_integral_open_normalization
      (Stacks.Blowup.finite_irreducibleComponents_blowUp
        (Scheme.IdealSheafData.vanishingIdeal ⟨{x}, hx⟩) hS), hqbir,
    (topologicalKrullDim_le_of_birational_of_locally_integral q hqbir hlocal).trans hdim,
    ⟨⟨hS, x, hx, hxW, Iso.refl _, ?_⟩, ‹IsProper q›⟩,
    exists_principal_maximalIdeal_normalizedBlowUp hS x hx⟩
  simp only [Iso.refl_hom, Over.mk_hom, Category.id_comp]
  rfl

/-- The inner induction of `hasCentredDominatingTail_of_normal`, on the valuation of the
denominator of a fraction whose residue is transcendental. -/
private lemma hasCentredDominatingTail_of_transcendental_residue (n : ℕ)
    {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (u : R)
    (ih : ∀ {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T] [IsNormal S] [IsNormal T],
      IsNagataScheme S → topologicalKrullDim S ≤ 2 →
      (∀ x : S, ∃ U : S.Opens, x ∈ U ∧ IsIntegral U.toScheme) →
      ∀ (l : T ⟶ S) [IsProper l], IsBirational l → topologicalKrullDim T ≤ 2 →
      ∀ W : S.Opens, IsIso (l ∣_ W) →
      (contractedPoints l).ncard < n → HasCentredDominatingTail W l) :
    ∀ m {S T : Scheme.{u}} [IsNoetherian S] [IsNoetherian T] [IsNormal S] [IsNormal T]
      (hNagataS : IsNagataScheme S) (hdimS : topologicalKrullDim S ≤ 2)
      (hlocalS : ∀ x : S, ∃ U : S.Opens, x ∈ U ∧ IsIntegral U.toScheme)
      (l : T ⟶ S) [IsProper l] (hl : IsBirational l)
      (hdimT : topologicalKrullDim T ≤ 2) (W : S.Opens) (hW : IsIso (l ∣_ W))
      (y : T) (hy : ¬ IsClosed ({y} : Set T)) (hly : IsClosed ({l y} : Set S))
      (e : T.presheaf.stalk y ≃+* R) (a b : S.presheaf.stalk (l y))
      (hb : e ((l.stalkMap y).hom b) ≠ 0)
      (hab : e ((l.stalkMap y).hom a) = u * e ((l.stalkMap y).hom b))
      (hu : letI := (IsLocalRing.ResidueField.map
        (e.toRingHom.comp (l.stalkMap y).hom)).toAlgebra;
        Transcendental (IsLocalRing.ResidueField (S.presheaf.stalk (l y)))
          (IsLocalRing.residue R u)),
      (IsDiscreteValuationRing.addVal R (e ((l.stalkMap y).hom b))).toNat = m →
      (contractedPoints l).ncard ≤ n → HasCentredDominatingTail W l := by
  intro m
  induction m using Nat.strong_induction_on with
  | h m ihm =>
    intro S T _ _ _ _ hNagataS hdimS hlocalS l _ hl hdimT W hW y hy hly e a b hb hab hu hm hcard
    obtain ⟨S', q, _, _, _, hNagataS', hlocalS', hqbir, hdimS', hs, hprincipal⟩ :=
      exists_normalizedBlowUpOutside_at_closed_point hNagataS hdimS hlocalS (l y) hly
        (not_generic_image_of_contracted_nonclosed_point l hl y hy hly) W
        (apply_not_mem_of_isIso_morphismRestrict l W hW y hy hly)
    obtain ⟨T', p, g, hcomm, _, _, _, _, hpbir, hgbir⟩ :=
      exists_common_normal_modification hNagataS hdimS l q hl hqbir
    have : IsNoetherian T' := isNoetherian_of_isProper_over_noetherian p
    have hdimT' : topologicalKrullDim T' ≤ 2 :=
      (topologicalKrullDim_le_of_birational_of_locally_integral g hgbir hlocalS').trans hdimS'
    have hgW : IsIso (g ∣_ (q ⁻¹ᵁ W)) :=
      isIso_morphismRestrict_preimage_of_finite_comparison l q p g hcomm hgbir W hW
    have hbadFinite := finite_contracted_nonclosed_points l hl hdimT
    obtain ⟨hfinite', hbound⟩ :=
      finite_contracted_points_of_finite_comparison l g p q hcomm hpbir hdimT hbadFinite
    apply hasCentredDominatingTail_of_square hs hcomm
    by_cases hsmall : (contractedPoints g).ncard < n
    · exact ih hNagataS' hdimS' hlocalS' g hgbir hdimT' (q ⁻¹ᵁ W) hgW hsmall
    · have hmem : y ∈ p '' contractedPoints g := by
        by_contra hmissing
        have hdrop := ncard_lt_of_injOn_with_missing_image hbadFinite p
          (mapsTo_contracted_points_of_finite_comparison l g p q hcomm)
          (injOn_contracted_points_of_finite_comparison l g p q hcomm hpbir hdimT)
          y ⟨hy, hly⟩ hmissing
        exact hsmall (hdrop.trans_le hcard)
      obtain ⟨z, hz, hpz⟩ := hmem
      subst y
      have : IsIso (p.stalkMap z) := isIso_stalkMap_over_nonclosed_point p hpbir hdimT z hy
      have hqz : q (g z) = l (p z) := (congrArg (fun k : T' ⟶ S => k z) hcomm).symm
      obtain ⟨e', a', b', hb', hab', hu', hlt⟩ := exists_fraction_descent_in_square l q p g
        hcomm z hz.2 (hprincipal (g z) hqz) e u a b hb hab hu
      exact ihm _ (hlt.trans_le (by omega)) hNagataS' hdimS' hlocalS' g hgbir hdimT'
        (q ⁻¹ᵁ W) hgW z hz.1 hz.2 e' a' b' hb' hab' hu' rfl (hbound.trans hcard)

private theorem hasCentredDominatingTail_of_normal
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNoetherian Y]
    [IsNormal X] [IsNormal Y]
    (hNagata : IsNagataScheme X) (hdim : topologicalKrullDim X ≤ 2)
    (hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIntegral U.toScheme)
    (f : Y ⟶ X) [IsProper f] (hf : IsBirational f)
    (hdimY : topologicalKrullDim Y ≤ 2) (V : X.Opens) (hV : IsIso (f ∣_ V)) :
    HasCentredDominatingTail V f := by
  classical
  generalize hn : (contractedPoints f).ncard = n
  induction n using Nat.strong_induction_on generalizing X Y with
  | h n ih =>
    by_cases hbad : (contractedPoints f).Nonempty
    · obtain ⟨y, hy, hfy⟩ := hbad
      have hycodim := codimension_eq_one_of_nonclosed_of_not_generic hdimY y hy
        (not_generic_of_contracted_nonclosed_point f hf y hy hfy)
      obtain ⟨_, _⟩ := isDiscreteValuationRing_stalk_of_codimension_eq_one y hycodim
      let R : Type u := Y.presheaf.stalk y
      obtain ⟨u, hu⟩ := exists_transcendental_residue_of_nonclosed f y hy hfy
      obtain ⟨a, b, hb, hab⟩ := exists_stalk_numerator_denominator_of_locally_integral
        f hf hlocal y u
      refine hasCentredDominatingTail_of_transcendental_residue n u ?_ _ hNagata hdim hlocal f hf
        hdimY V hV y hy hfy (RingEquiv.refl R) a b hb hab hu rfl hn.le
      intro S T _ _ _ _ hNagataS hdimS hlocalS l _ hl hdimT W hW hlt
      exact ih _ hlt hNagataS hdimS hlocalS l hl hdimT W hW rfl
    · have : IsIso f := isIso_of_no_contracted_nonclosed_points f hf hdim fun y hy =>
        Classical.byContradiction fun h => hbad ⟨y, h, hy⟩
      exact ⟨Over.mk (𝟙 X), .refl, inv f, by simp⟩

/-- **Domination by normalized blowups centred outside an open** (a refinement of
[Stacks, Tag 0BBT]). Let `X` be a Noetherian normal Nagata scheme of dimension at most two and
let `f : Y ⟶ X` be a proper birational morphism which is an isomorphism over an open `V` of `X`.
Then there is a finite sequence of normalized blowups of `X` at closed points, each lying over a
point of `X` outside `V` and each stage proper over `X`, whose last stage `Z` dominates `Y` over
`X`. -/
theorem exists_reflTransGen_isProperNormalizedBlowUpOutside_dominating
    {X Y : Scheme.{u}} [IsNoetherian X] [IsNormal X] (hNagata : IsNagataScheme X)
    (hdim : topologicalKrullDim X ≤ 2) (f : Y ⟶ X) [IsProper f] (hf : IsBirational f)
    (V : X.Opens) (hV : IsIso (f ∣_ V)) :
    ∃ Z : Over X, Relation.ReflTransGen (IsProperNormalizedBlowUpOutside V) (Over.mk (𝟙 X)) Z ∧
      ∃ h : Z.left ⟶ Y, h ≫ f = Z.hom := by
  classical
  let hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_isCompactOpen_of_isNoetherian
  let hY := finite_irreducibleComponents_of_isProper f
  let Y' := Scheme.normalizationScheme Y hY
  let ν : Y' ⟶ Y := Scheme.normalization Y hY
  have : IsFinite ν :=
    Scheme.isFinite_normalization (isNagataScheme_of_locallyOfFiniteType f hNagata) hY
  have : IsProper ν := isProper_normalization_of_isProper_to_nagata hNagata f hY
  have : IsNormal Y' := isNormal_normalizationScheme hY
  have : IsFinite (Scheme.normalization X hX) := Scheme.isFinite_normalization hNagata hX
  have : IsReduced (Scheme.normalizationScheme X hX) := isReduced_of_isReduced_stalk _
  obtain ⟨l, -, hl⟩ := exists_lift_normalization_of_proper_birational hX hNagata f hf hY
  have hbir : IsBirational (ν ≫ f) := by
    rw [← hl]
    exact isBirational_comp _ _ (isBirational_lift_normalizations hX hY f hf l hl)
      (Scheme.isBirational_normalization X hX)
  have : IsNoetherian Y' := isNoetherian_of_isProper_over_noetherian (ν ≫ f)
  have hlocal : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ IsIntegral U.toScheme :=
    exists_integral_open_of_isNormal
  have hdimY' : topologicalKrullDim Y' ≤ 2 :=
    (topologicalKrullDim_le_of_birational_of_locally_integral (ν ≫ f) hbir hlocal).trans hdim
  have hV' : IsIso ((ν ≫ f) ∣_ V) := by
    rw [morphismRestrict_comp]
    exact IsIso.comp_isIso' (normalization_restrict_isIso_of_isNormal hY (f ⁻¹ᵁ V)
      (isNormal_of_iso (asIso (f ∣_ V)).symm (isNormal_open V inferInstance))) hV
  obtain ⟨Z, hZ, h, hh⟩ :=
    hasCentredDominatingTail_of_normal hNagata hdim hlocal (ν ≫ f) hbir hdimY' V hV'
  exact ⟨Z, hZ, h ≫ ν, (Category.assoc _ _ _).trans hh⟩

end Stacks.ResolutionOfSurfaces

end
