module

public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.NormalizedBlowUp
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Reduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.EtaleBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.LocalizationBaseChange
public import StacksFrontier.AlgebraicGeometry.NormalProperModel.Basic
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.Pullback.StalkFromSpecStalk
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.ModifyingLocalRings.PointBlowupSequence

/-!
# Sequences of normalized blowups at closed points

Let `X` be a scheme and `T` a set of points of `X`. A *normalized point blowup chain* over `T` is
a finite composition `Xₘ → Xₘ₋₁ → … → X₀ = X` in which each `Xⱼ₊₁ → Xⱼ` is the normalized blowing
up of `Xⱼ` at a closed point whose image in `X` lies in `T`, that is, the normalization of the
blowup of `Xⱼ` in the reduced closed subscheme supported at that point. This is the object whose
existence is asserted on both sides of [Stacks, Tag 0BFZ], the normalized-blowup analogue of the
point blowup chains of [Stacks, Tag 0BFY].

Over a normal base every scheme of such a chain is normal, being a normalization, and then each
step is an isomorphism away from its centre: the blowup is an isomorphism away from the centre
and the normalization of a scheme is an isomorphism over a normal open.

## Main definitions

* `Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain` is a finite sequence of normalized
  blowups at closed points lying over a given set of points, indexed by its composite morphism.
* `Stacks.ResolutionOfSurfaces.FactorsAsNormalizedPointBlowups` says that a morphism is, up to an
  isomorphism of its source, the composite of such a chain. Unlike the chain itself, which names
  the blown-up schemes, this is invariant under isomorphism.

## Main results

* `AlgebraicGeometry.exists_normalizationScheme_iso_of_iso`: an isomorphism of schemes lifts to
  an isomorphism of their normalizations, compatibly with the normalization morphisms.
* `Stacks.ResolutionOfSurfaces.FactorsAsNormalizedPointBlowups.step` extends a factorization by
  the normalized blowup at a closed point lying over the given set.
* `Stacks.ResolutionOfSurfaces.NormalizedPointBlowupChain.isNormal`: every scheme of a normalized
  point blowup chain over a normal base is normal.
* `AlgebraicGeometry.isIso_normalizedBlowUp_restrict_compl_singleton`: the normalized blowing up
  of a normal scheme at a closed point is an isomorphism over the complement of that point.
* `AlgebraicGeometry.exists_isPullback_normalizedBlowUp_comap`: the normalized blowing up at a
  closed point commutes with a base change which is flat and a preimmersion and under which the
  reduced point pulls back to a reduced point.
* `AlgebraicGeometry.factorsAsNormalizedPointBlowups_pullback_fromSpecStalk` is one direction of
  [Stacks, Tag 0BFZ] over a normal base: a sequence of normalized blowups at closed points over
  the distinguished points localizes to such a sequence over the closed point of
  `Spec 𝒪_{S, s i}`. The variant
  `AlgebraicGeometry.factorsAsNormalizedPointBlowups_pullback_fromSpecStalk_of_factors` assumes
  only that the morphism factors as such a sequence, and
  `factorsAsNormalizedPointBlowups_of_corresponds` in the namespace
  `AlgebraicGeometry.FinitePresentationAwayPointsSituation` restates that for the local
  modifications corresponding to a global one under a base-change functor of Tag 0BFU.
* `factorsAsNormalizedPointBlowups_of_baseChange_iso` in the namespace
  `AlgebraicGeometry.FinitePresentationAwayPointsSituation` is the step of the converse direction
  supplied by [Stacks, Tag 0BFV]: a global modification
  supported at the distinguished points whose localizations agree with those of a sequence of
  normalized blowups at closed points over the distinguished points is itself such a sequence.
  It needs neither normality of the base nor a glueing theorem.

## Implementation notes

Finiteness of the irreducible components of the quasi-compact opens of the current scheme is what
makes its normalization, and hence its normalized blowing up, available; it is carried as data by
the inductive step, exactly as in `AlgebraicGeometry.NormalizedBlowUpSeq`, rather than being
propagated from the base. It is a proposition, so the scheme produced by a step does not depend on
which witness is supplied.

This file proves the necessity direction of Tag 0BFZ over a normal base. Both directions over a
normal base are
`AlgebraicGeometry.FinitePresentationAwayPointsSituation.factorsAsNormalizedPointBlowups_iff`,
and the failure of the statement without normality is
`AlgebraicGeometry.not_factorsAsNormalizedPointBlowups_iff`.

The localization of one step of a chain is the normalized blowing up at the unique point above
its centre because both halves of that identification commute with the base change
`q : W ×_S Spec 𝒪_{S,s} ⟶ W`, which is flat and a preimmersion: the blowup half is Tag 0805,
`AlgebraicGeometry.exists_isPullback_blowUpToBase_comap`, and the normalization half is
`AlgebraicGeometry.isPullback_normalizationSchemeMap_of_flat_preimmersion`, the form of Tag 0307
that applies to a morphism which is not locally of finite type. The two cartesian squares are
pasted along the comparison morphism of the blowups, so the normalized blowing up of the base
change is the base change of the normalized blowing up with no comparison isomorphism left to
transport. A step whose centre lies over another distinguished point disappears instead: the
normalized blowing up is an isomorphism over the complement of its centre, which the base change
factors through, and an isomorphism over an open stays an isomorphism after base change along a
morphism landing in that open.

The finiteness hypothesis of Tag 0BFZ, that every quasi-compact open of `S` has finitely many
irreducible components, is not assumed: `NormalizedPointBlowupChain` carries at each step the
finiteness needed to normalize at that step, so the statement proved here is the one the source's
hypothesis is there to make meaningful, without the hypothesis.

Normality of the base is not a hypothesis of Tag 0BFZ, but it is needed: a scheme `S` of dimension
two which is normal away from two closed points `s₁, s₂` and not normal at `s₂` has
`X = ` the normalized blowing up of `S` at `s₁` finitely presented and an isomorphism over
`S \ {s₁, s₂}`, so an object of the category of Tag 0BFU factoring as a one-step chain, while its
base change to `Spec 𝒪_{S, s₂}` is the normalization of that local scheme, a finite non-trivial
morphism, and no chain of normalized blowings up at closed points of a two-dimensional scheme is
finite and non-trivial. Hence the results here about chains over a normal base.

The normalization of a scheme is defined by a construction, not by a universal property, so
transporting a chain along an isomorphism of its base needs the induced isomorphism of
normalizations. That isomorphism is obtained from the cartesian square of
`AlgebraicGeometry.isPullback_normalizationSchemeMap_of_etale`, an isomorphism being étale: the
induced morphism of normalizations is then a base change of an isomorphism.

## References

* [Stacks Project, Tag 0BFZ](https://stacks.math.columbia.edu/tag/0BFZ)
* [Stacks Project, Tag 0BFY](https://stacks.math.columbia.edu/tag/0BFY)
* [Stacks Project, Tag 0BFX](https://stacks.math.columbia.edu/tag/0BFX)
* [Stacks Project, Tag 0BFV](https://stacks.math.columbia.edu/tag/0BFV)
* [Stacks Project, Tag 0BFU](https://stacks.math.columbia.edu/tag/0BFU)
* [Stacks Project, Tag 0BBS](https://stacks.math.columbia.edu/tag/0BBS)
* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
* [Stacks Project, Tag 0307](https://stacks.math.columbia.edu/tag/0307)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Normalization along an isomorphism -/

/-- An isomorphism of schemes whose quasi-compact opens have finitely many irreducible components
lifts to an isomorphism of their normalizations, compatibly with the normalization morphisms. -/
theorem exists_normalizationScheme_iso_of_iso {A B : Scheme.{u}} (d : A ≅ B)
    (hA : ∀ U : A.Opens, IsCompact (U : Set A) → (irreducibleComponents U).Finite)
    (hB : ∀ U : B.Opens, IsCompact (U : Set B) → (irreducibleComponents U).Finite) :
    ∃ e : A.normalizationScheme hA ≅ B.normalizationScheme hB,
      e.hom ≫ B.normalization hB = A.normalization hA ≫ d.hom := by
  have hsq := isPullback_normalizationSchemeMap_of_etale d.hom hB
  have hiso : IsIso (normalizationSchemeMap d.hom
      (finite_irreducibleComponents_of_smooth d.hom hB) hB) := hsq.flip.isIso_snd_of_isIso
  exact ⟨asIso (normalizationSchemeMap d.hom
      (finite_irreducibleComponents_of_smooth d.hom hB) hB),
    normalizationSchemeMap_normalization d.hom _ hB⟩

end AlgebraicGeometry

namespace Stacks.ResolutionOfSurfaces

/-! ### Normalized point blowup chains -/

/-- A finite sequence of normalized blowups at closed points lying over `T ⊆ X`, indexed by the
composite morphism to `X`: either the identity of `X`, or the normalized blowing up of such a
sequence at a closed point of its source whose image in `X` belongs to `T`. -/
inductive NormalizedPointBlowupChain (X : Scheme.{u}) (T : Set X) :
    ∀ Y : Scheme.{u}, (Y ⟶ X) → Prop
  | refl : NormalizedPointBlowupChain X T X (𝟙 X)
  | step {W : Scheme.{u}} {h : W ⟶ X} (hh : NormalizedPointBlowupChain X T W h)
      (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite)
      (w : W) (hw : IsClosed ({w} : Set W)) (hwT : h.base w ∈ T) :
      NormalizedPointBlowupChain X T
        (Stacks.Blowup.normalizedBlowUpScheme W hW w hw)
        (Stacks.Blowup.normalizedBlowUp W hW w hw ≫ h)

/-- A morphism `p : Z ⟶ X` factors as a finite sequence of normalized blowups at closed points
lying over `T ⊆ X` if some `NormalizedPointBlowupChain` over `T` has source isomorphic to `Z`
over `X`. -/
def FactorsAsNormalizedPointBlowups (X : Scheme.{u}) (T : Set X) (Z : Scheme.{u}) (p : Z ⟶ X) :
    Prop :=
  ∃ (Y : Scheme.{u}) (f : Y ⟶ X), NormalizedPointBlowupChain X T Y f ∧ ∃ e : Z ≅ Y, e.hom ≫ f = p

/-- The identity factors as the empty sequence of normalized blowups. -/
theorem FactorsAsNormalizedPointBlowups.refl {X : Scheme.{u}} (T : Set X) :
    FactorsAsNormalizedPointBlowups X T X (𝟙 X) :=
  ⟨X, 𝟙 X, NormalizedPointBlowupChain.refl, Iso.refl X, by simp⟩

/-- Factoring as a sequence of normalized blowups is invariant under precomposition with an
isomorphism. -/
theorem FactorsAsNormalizedPointBlowups.of_iso {X : Scheme.{u}} {T : Set X} {Z Z' : Scheme.{u}}
    {p : Z ⟶ X} (h : FactorsAsNormalizedPointBlowups X T Z p) (e : Z' ≅ Z) :
    FactorsAsNormalizedPointBlowups X T Z' (e.hom ≫ p) := by
  obtain ⟨Y, f, hchain, d, hd⟩ := h
  exact ⟨Y, f, hchain, e ≪≫ d, by rw [Iso.trans_hom, Category.assoc, hd]⟩

/-- Factoring as a sequence of normalized blowups depends only on the morphism. -/
theorem FactorsAsNormalizedPointBlowups.congr {X : Scheme.{u}} {T : Set X} {Z : Scheme.{u}}
    {p p' : Z ⟶ X} (h : FactorsAsNormalizedPointBlowups X T Z p) (hp : p = p') :
    FactorsAsNormalizedPointBlowups X T Z p' := hp ▸ h

/-- Blowing up a closed point lying over `T` and normalizing extends a factorization as a
sequence of normalized blowups: the normalized blowing up at the point is identified with the
normalized blowing up at its image in the chain, the inverse image of the reduced closed
subscheme at the point being the reduced closed subscheme at its image. -/
theorem FactorsAsNormalizedPointBlowups.step {X : Scheme.{u}} {T : Set X} {Z : Scheme.{u}}
    {p : Z ⟶ X} (h : FactorsAsNormalizedPointBlowups X T Z p)
    (hZ : ∀ U : Z.Opens, IsCompact (U : Set Z) → (irreducibleComponents U).Finite)
    (z : Z) (hz : IsClosed ({z} : Set Z)) (hzT : p.base z ∈ T) :
    FactorsAsNormalizedPointBlowups X T
      (Stacks.Blowup.normalizedBlowUpScheme Z hZ z hz)
      (Stacks.Blowup.normalizedBlowUp Z hZ z hz ≫ p) := by
  obtain ⟨Y, f, hchain, e, he⟩ := h
  have hY : ∀ U : Y.Opens, IsCompact (U : Set Y) → (irreducibleComponents U).Finite :=
    finite_irreducibleComponents_of_smooth e.inv hZ
  have hz' : IsClosed ({e.hom z} : Set Y) := by
    have hset : ({e.hom z} : Set Y) = e.inv ⁻¹' ({z} : Set Z) := by
      ext y
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      refine ⟨fun hy => by subst hy; simp, fun hy => ?_⟩
      rw [← show e.hom (e.inv y) = y from by simp, hy]
    rw [hset]
    exact hz.preimage e.inv.continuous
  have hfz : f.base (e.hom z) ∈ T := by
    have hpz : f.base (e.hom z) = p.base z := by
      have := congrArg (fun k : Z ⟶ X => k.base z) he
      simpa using this
    rw [hpz]
    exact hzT
  set J : Y.IdealSheafData :=
    Scheme.IdealSheafData.vanishingIdeal (⟨{e.hom z}, hz'⟩ : Closeds Y) with hJ
  obtain ⟨_, hideal⟩ :=
    AlgebraicGeometry.vanishingIdeal_singleton_comap_of_isIso e.hom (e.hom z) hz' z rfl
  have key : ∀ K : Z.IdealSheafData, K = J.comap e.hom →
      ∃ d : blowUp K ≅ blowUp J, d.hom ≫ blowUpToBase J = blowUpToBase K ≫ e.hom := by
    intro K hK
    cases hK
    exact AlgebraicGeometry.exists_blowUp_iso_comap_of_isIso e.hom J
  obtain ⟨d, hd⟩ := key (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z))
    hideal.symm
  obtain ⟨m, hm⟩ := AlgebraicGeometry.exists_normalizationScheme_iso_of_iso d
    (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hZ)
    (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hY)
  have hstep : m.hom ≫ Stacks.Blowup.normalizedBlowUp Y hY (e.hom z) hz' =
      Stacks.Blowup.normalizedBlowUp Z hZ z hz ≫ e.hom := by
    change m.hom ≫ Scheme.normalization (blowUp J)
        (Stacks.Blowup.finite_irreducibleComponents_blowUp J hY) ≫ blowUpToBase J =
      (Scheme.normalization (blowUp (Scheme.IdealSheafData.vanishingIdeal
            (⟨{z}, hz⟩ : Closeds Z)))
          (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hZ) ≫
        blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds Z))) ≫ e.hom
    rw [← Category.assoc, hm, Category.assoc, hd, Category.assoc]
  refine ⟨_, _, hchain.step hY (e.hom z) hz' hfz, m, ?_⟩
  rw [← Category.assoc, hstep, Category.assoc, he]

/-! ### Normality along a chain -/

/-- Every scheme of a normalized point blowup chain over a normal base is normal: a normalization
is normal, and the base is the only scheme of the chain which is not one. -/
theorem NormalizedPointBlowupChain.isNormal {X : Scheme.{u}} [IsNormal X] {T : Set X}
    {Y : Scheme.{u}} {f : Y ⟶ X} (h : NormalizedPointBlowupChain X T Y f) : IsNormal Y := by
  induction h with
  | refl => infer_instance
  | step hh hW w hw hwT ih =>
    exact Scheme.isNormal_normalizationScheme _
      (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hW)

end Stacks.ResolutionOfSurfaces

namespace AlgebraicGeometry

/-! ### The normalized blowup away from its centre -/

/-- The normalized blowing up of a normal scheme at a closed point is an isomorphism over the
complement of that point: the blowup is an isomorphism there, and the normalization morphism of a
scheme is an isomorphism over a normal open, the complement of the exceptional locus being
isomorphic to the complement of the centre. -/
theorem isIso_normalizedBlowUp_restrict_compl_singleton {X : Scheme.{u}} [IsNormal X]
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (x : X) (hx : IsClosed ({x} : Set X)) :
    IsIso (Stacks.Blowup.normalizedBlowUp X hX x hx ∣_
      (⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ : X.Opens)) := by
  have hcoe : ((Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X)).support : Set X)
      = {x} := Scheme.IdealSheafData.coe_support_vanishingIdeal _
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{x}, hx⟩ : Closeds X) with hI
  set U : X.Opens := ⟨({x} : Set X)ᶜ, hx.isOpen_compl⟩ with hU
  have hsupp : (⟨(I.support : Set X)ᶜ, I.support.isClosed.isOpen_compl⟩ : X.Opens) = U := by
    refine TopologicalSpace.Opens.ext ?_
    change (I.support : Set X)ᶜ = ({x} : Set X)ᶜ
    rw [hcoe]
  have hb : IsIso (blowUpToBase I ∣_ U) := hsupp ▸ isIso_blowUp_restrict_compl_support I
  have hVn : IsNormal (blowUpToBase I ⁻¹ᵁ U).toScheme :=
    isNormal_of_iso (asIso (blowUpToBase I ∣_ U))
  have hn : IsIso (Scheme.normalization (blowUp I)
      (Stacks.Blowup.finite_irreducibleComponents_blowUp I hX) ∣_ (blowUpToBase I ⁻¹ᵁ U)) :=
    Scheme.isIso_normalization_restrict_of_isNormal _ _ _ hVn
  have hcmp : Stacks.Blowup.normalizedBlowUp X hX x hx =
      Scheme.normalization (blowUp I)
        (Stacks.Blowup.finite_irreducibleComponents_blowUp I hX) ≫ blowUpToBase I := rfl
  rw [hcmp, morphismRestrict_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hn hb

/-! ### Base change along a morphism landing in an open of isomorphism -/

/-- A morphism which is an isomorphism over an open subset of its target becomes an isomorphism
after base change along any morphism whose image lies in that open: such a morphism factors
through the open, and the base change along the inclusion of the open is the restriction. -/
theorem isIso_pullback_snd_of_isIso_morphismRestrict {X Y Z : Scheme.{u}} (f : X ⟶ Y)
    (q : Z ⟶ Y) (U : Y.Opens) (hf : IsIso (f ∣_ U)) (hq : ∀ z : Z, q.base z ∈ U) :
    IsIso (pullback.snd f q) := by
  have hrange : Set.range q.base ⊆ Set.range U.ι.base := by
    rintro y ⟨z, rfl⟩
    exact ⟨⟨q.base z, hq z⟩, rfl⟩
  have hfac : IsOpenImmersion.lift U.ι q hrange ≫ U.ι = q :=
    IsOpenImmersion.lift_fac U.ι q hrange
  have hbig : IsPullback (pullback.fst f q) (pullback.snd f q) f
      (IsOpenImmersion.lift U.ι q hrange ≫ U.ι) := by
    rw [hfac]
    exact IsPullback.of_hasPullback f q
  exact (hbig.of_right' (isPullback_morphismRestrict f U).flip).isIso_snd_of_isIso

/-! ### The normalized blowup under a flat preimmersive base change -/

/-- Blowing up and then normalizing commutes with a base change which is flat and a
preimmersion, in the form in which the inverse image of the blown-up ideal has already been
identified: the blowup of `W'` in `J` normalizes to the base change along `q` of the
normalization of the blowup of `W` in `I`.

The blowup half of the square is [Stacks, Tag 0805] and the normalization half is the form of
[Stacks, Tag 0307] carried by
`AlgebraicGeometry.isPullback_normalizationSchemeMap_of_flat_preimmersion`; the two are pasted
along the comparison morphism of the blowups. -/
theorem exists_isPullback_normalization_blowUpToBase_comap {W W' : Scheme.{u}} (q : W' ⟶ W)
    [Flat q] [IsPreimmersion q] (I : W.IdealSheafData)
    (hB : ∀ U : (blowUp I).Opens, IsCompact (U : Set ↥(blowUp I)) →
      (irreducibleComponents U).Finite)
    (J : W'.IdealSheafData) (hJ : I.comap q = J)
    (hB' : ∀ U : (blowUp J).Opens, IsCompact (U : Set ↥(blowUp J)) →
      (irreducibleComponents U).Finite) :
    ∃ m : Scheme.normalizationScheme (blowUp J) hB' ⟶ Scheme.normalizationScheme (blowUp I) hB,
      IsPullback m (Scheme.normalization (blowUp J) hB' ≫ blowUpToBase J)
        (Scheme.normalization (blowUp I) hB ≫ blowUpToBase I) q := by
  subst hJ
  obtain ⟨ψ, hψ⟩ := exists_isPullback_blowUpToBase_comap q I
  have hflat : Flat ψ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) hψ inferInstance
  have hpre : IsPreimmersion ψ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsPreimmersion) hψ inferInstance
  have hν : IsNormal (Scheme.normalizationScheme (blowUp I) hB) :=
    Scheme.isNormal_normalizationScheme _ hB
  have hnormal : IsNormal (pullback (Scheme.normalization (blowUp I) hB) ψ) :=
    isNormal_of_flat_preimmersion (pullback.fst (Scheme.normalization (blowUp I) hB) ψ)
  exact ⟨_, (isPullback_normalizationSchemeMap_of_flat_preimmersion ψ hB hnormal).paste_vert
    hψ.flip⟩

/-- The normalized blowing up at a closed point commutes with a base change which is flat and a
preimmersion and under which the reduced point at `w` pulls back to the reduced point at `z`:
the normalized blowing up of `W'` at `z` is the base change along `q` of the normalized blowing
up of `W` at `w`. -/
theorem exists_isPullback_normalizedBlowUp_comap {W W' : Scheme.{u}} (q : W' ⟶ W)
    [Flat q] [IsPreimmersion q]
    (hW : ∀ U : W.Opens, IsCompact (U : Set W) → (irreducibleComponents U).Finite)
    (hW' : ∀ U : W'.Opens, IsCompact (U : Set W') → (irreducibleComponents U).Finite)
    (w : W) (hw : IsClosed ({w} : Set W)) (z : W') (hz : IsClosed ({z} : Set W'))
    (hideal : (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap q =
      Scheme.IdealSheafData.vanishingIdeal (⟨{z}, hz⟩ : Closeds W')) :
    ∃ m : Stacks.Blowup.normalizedBlowUpScheme W' hW' z hz ⟶
        Stacks.Blowup.normalizedBlowUpScheme W hW w hw,
      IsPullback m (Stacks.Blowup.normalizedBlowUp W' hW' z hz)
        (Stacks.Blowup.normalizedBlowUp W hW w hw) q :=
  exists_isPullback_normalization_blowUpToBase_comap q _
    (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hW) _ hideal
    (Stacks.Blowup.finite_irreducibleComponents_blowUp _ hW')

/-! ### Localizing a sequence of normalized blowups -/

open Stacks.ResolutionOfSurfaces

/-- **Stacks Project, Tag 0BFZ**, necessity, for a normal base. Let `s` be an injective family
of closed points of a normal scheme `S` and fix an index `i`. A morphism to `S` which is the
composite of a finite sequence of normalized blowups at closed points lying over the `s j`
becomes, after base change to `Spec 𝒪_{S, s i}`, a finite sequence of normalized blowups at
closed points lying over the closed point: a step whose centre lies over `s i` is the normalized
blowing up at the unique point above that centre, and a step whose centre lies over another `s j`
becomes an isomorphism. -/
theorem factorsAsNormalizedPointBlowups_pullback_fromSpecStalk {S : Scheme.{u}} [IsNormal S]
    {n : ℕ} (s : Fin n → S) (hinj : Function.Injective s)
    (hclosed : ∀ j, IsClosed ({s j} : Set S)) (i : Fin n)
    {Z : Scheme.{u}} {p : Z ⟶ S}
    (h : NormalizedPointBlowupChain S (Set.range s) Z p) :
    FactorsAsNormalizedPointBlowups (Spec (S.presheaf.stalk (s i)))
      {IsLocalRing.closedPoint (S.presheaf.stalk (s i))}
      (pullback p (S.fromSpecStalk (s i))) (pullback.snd p (S.fromSpecStalk (s i))) := by
  have hflat : Flat (S.fromSpecStalk (s i)) := flat_fromSpecStalk S (s i)
  induction h with
  | refl =>
    refine ((FactorsAsNormalizedPointBlowups.refl
      ({IsLocalRing.closedPoint (S.presheaf.stalk (s i))} :
        Set (Spec (S.presheaf.stalk (s i))))).of_iso
      (asIso (pullback.snd (𝟙 S) (S.fromSpecStalk (s i))))).congr ?_
    simp
  | @step W pW hh hW w hw hwT ih =>
    obtain ⟨j, hj⟩ := hwT
    have hqflat : Flat (pullback.fst pW (S.fromSpecStalk (s i))) :=
      flat_pullbackFst_fromSpecStalk pW (s i)
    have hAsnd := pullbackRightPullbackFstIso_hom_snd pW (S.fromSpecStalk (s i))
      (Stacks.Blowup.normalizedBlowUp W hW w hw)
    suffices hgoal : FactorsAsNormalizedPointBlowups (Spec (S.presheaf.stalk (s i)))
        {IsLocalRing.closedPoint (S.presheaf.stalk (s i))}
        (pullback (Stacks.Blowup.normalizedBlowUp W hW w hw)
          (pullback.fst pW (S.fromSpecStalk (s i))))
        (pullback.snd (Stacks.Blowup.normalizedBlowUp W hW w hw)
            (pullback.fst pW (S.fromSpecStalk (s i))) ≫
          pullback.snd pW (S.fromSpecStalk (s i))) by
      refine (hgoal.of_iso (pullbackRightPullbackFstIso pW (S.fromSpecStalk (s i))
        (Stacks.Blowup.normalizedBlowUp W hW w hw)).symm).congr ?_
      rw [Iso.symm_hom, Iso.inv_comp_eq]
      exact hAsnd.symm
    by_cases hji : j = i
    · subst hji
      have hwi : pW.base w = s j := hj.symm
      have hc : pW.base w = (S.fromSpecStalk (s j)).base
          (IsLocalRing.closedPoint (S.presheaf.stalk (s j))) := by
        rw [hwi, Scheme.fromSpecStalk_closedPoint]
      obtain ⟨z, hzfst, hzsnd⟩ := Scheme.Pullback.exists_preimage_pullback
        (f := pW) (g := S.fromSpecStalk (s j)) w
        (IsLocalRing.closedPoint (S.presheaf.stalk (s j))) hc
      obtain ⟨hz, hideal⟩ := vanishingIdeal_singleton_comap_pullbackFst pW
        (S.fromSpecStalk (s j)) w hw (pointToSpecStalk pW w hwi)
        (pointToSpecStalk_comp_fromSpecStalk pW w hwi) z hzfst
      have hW' := finite_irreducibleComponents_pullbackFst_fromSpecStalk pW (s j) hW
      obtain ⟨m, hm⟩ := exists_isPullback_normalizedBlowUp_comap
        (pullback.fst pW (S.fromSpecStalk (s j))) hW hW' w hw z hz hideal
      have hinv : hm.isoPullback.inv ≫ Stacks.Blowup.normalizedBlowUp
            (pullback pW (S.fromSpecStalk (s j))) hW' z hz =
          pullback.snd (Stacks.Blowup.normalizedBlowUp W hW w hw)
            (pullback.fst pW (S.fromSpecStalk (s j))) := by
        rw [Iso.inv_comp_eq]
        exact hm.isoPullback_hom_snd.symm
      refine ((ih.step hW' z hz (by rw [hzsnd]; exact rfl)).of_iso
        hm.isoPullback.symm).congr ?_
      rw [Iso.symm_hom, ← Category.assoc, hinv]
    · have hmiss : ∀ y : ↥(pullback pW (S.fromSpecStalk (s i))),
          pullback.fst pW (S.fromSpecStalk (s i)) y ≠ w := by
        intro y hy
        have hcond : pW (pullback.fst pW (S.fromSpecStalk (s i)) y) =
            (S.fromSpecStalk (s i)) (pullback.snd pW (S.fromSpecStalk (s i)) y) := by
          have hcc := pullback.condition (f := pW) (g := S.fromSpecStalk (s i))
          exact congrArg (fun m : (pullback pW (S.fromSpecStalk (s i)) ⟶ S) => m.base y) hcc
        have hrange : s j ∈ Set.range (S.fromSpecStalk (s i)) := by
          refine ⟨pullback.snd pW (S.fromSpecStalk (s i)) y, ?_⟩
          rw [← hcond, hy, ← hj]
        rw [Scheme.range_fromSpecStalk] at hrange
        have hmem : s i ∈ ({s j} : Set S) :=
          specializes_iff_forall_closed.mp hrange _ (hclosed j) (by simp)
        exact hji (hinj (Set.mem_singleton_iff.mp hmem).symm)
      have hWnormal : IsNormal W := hh.isNormal
      have hiso : IsIso (pullback.snd (Stacks.Blowup.normalizedBlowUp W hW w hw)
          (pullback.fst pW (S.fromSpecStalk (s i)))) :=
        isIso_pullback_snd_of_isIso_morphismRestrict _ _
          (⟨({w} : Set W)ᶜ, hw.isOpen_compl⟩ : W.Opens)
          (isIso_normalizedBlowUp_restrict_compl_singleton hW w hw) hmiss
      exact ih.of_iso (asIso (pullback.snd (Stacks.Blowup.normalizedBlowUp W hW w hw)
        (pullback.fst pW (S.fromSpecStalk (s i)))))

/-- An isomorphism over the base transports a factorization as a sequence of normalized
blowups. -/
theorem factorsAsNormalizedPointBlowups_of_overIso {L : Scheme.{u}} {T : Set L} {A B : Over L}
    (e : A ≅ B) (h : FactorsAsNormalizedPointBlowups L T B.left B.hom) :
    FactorsAsNormalizedPointBlowups L T A.left A.hom :=
  (h.of_iso ((Over.forget L).mapIso e)).congr (Over.w e.hom)

/-- **Stacks Project, Tag 0BFZ**, necessity, for a normal base. If a morphism to a normal scheme
`S` factors as a finite sequence of normalized blowups at closed points lying over an injective
family of closed points `s`, then so does its base change to `Spec 𝒪_{S, s i}`, over the closed
point there. -/
theorem factorsAsNormalizedPointBlowups_pullback_fromSpecStalk_of_factors {S : Scheme.{u}}
    [IsNormal S] {n : ℕ} (s : Fin n → S) (hinj : Function.Injective s)
    (hclosed : ∀ j, IsClosed ({s j} : Set S)) (i : Fin n) {Z : Scheme.{u}} {p : Z ⟶ S}
    (h : FactorsAsNormalizedPointBlowups S (Set.range s) Z p) :
    FactorsAsNormalizedPointBlowups (Spec (S.presheaf.stalk (s i)))
      {IsLocalRing.closedPoint (S.presheaf.stalk (s i))}
      (pullback p (S.fromSpecStalk (s i))) (pullback.snd p (S.fromSpecStalk (s i))) := by
  obtain ⟨Y, f, hchain, e, he⟩ := h
  exact factorsAsNormalizedPointBlowups_of_overIso
    ((Over.pullback (S.fromSpecStalk (s i))).mapIso
      (Over.isoMk e he : Over.mk p ≅ Over.mk f))
    (factorsAsNormalizedPointBlowups_pullback_fromSpecStalk s hinj hclosed i hchain)

namespace FinitePresentationAwayPointsSituation

/-- **Stacks Project, Tag 0BFZ**, necessity, for a normal base. If `f : X ⟶ S` factors as a
finite sequence of normalized blowups at closed points lying over the distinguished points, then
so does its base change to the spectrum of the local ring at `s i`, over the closed point
there. -/
theorem factorsAsNormalizedPointBlowups_pullback (D : FinitePresentationAwayPointsSituation.{u})
    [IsNormal D.S] (X : D.globalCategory) (i : Fin D.n)
    (h : FactorsAsNormalizedPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom) :
    FactorsAsNormalizedPointBlowups (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))}
      (pullback X.obj.hom (D.S.fromSpecStalk (D.points i)))
      (pullback.snd X.obj.hom (D.S.fromSpecStalk (D.points i))) :=
  factorsAsNormalizedPointBlowups_pullback_fromSpecStalk_of_factors D.points
    D.points_injective D.points_closed i h

/-- **Stacks Project, Tag 0BFZ**, necessity, for a normal base, in the language of Tag 0BFU. If
`f : X ⟶ S` factors as a finite sequence of normalized blowups at closed points lying over the
distinguished points, then every local modification `g i : Y i ⟶ Spec 𝒪_{S, s i}` corresponding
to it under a base-change functor factors as a finite sequence of normalized blowups at closed
points lying over the closed point.

Both directions are
`AlgebraicGeometry.FinitePresentationAwayPointsSituation.factorsAsNormalizedPointBlowups_iff`. -/
@[stacks 0BFZ "necessity only; corrected: S normal added, the statement being false without it"]
theorem factorsAsNormalizedPointBlowups_of_corresponds
    (D : FinitePresentationAwayPointsSituation.{u}) [IsNormal D.S] (BC : BaseChangeFunctor D)
    (X : D.globalCategory) (i : Fin D.n) (Y : D.localCategory i)
    (hY : BC.functor.obj X i ≅ Y)
    (h : FactorsAsNormalizedPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom) :
    FactorsAsNormalizedPointBlowups (D.localScheme i)
      {IsLocalRing.closedPoint (D.S.presheaf.stalk (D.points i))} Y.obj.left Y.obj.hom :=
  factorsAsNormalizedPointBlowups_of_overIso
    ((ObjectProperty.ι (IsFinitePresentationAway (D.puncturedLocalScheme i))).mapIso hY.symm ≪≫
      (BC.pullbackIso i).app X)
    (D.factorsAsNormalizedPointBlowups_pullback X i h)

/-- **Stacks Project, Tag 0BFZ**, sufficiency, the step supplied by Tag 0BFV. A modification of
`S` supported at the distinguished points is determined by its family of localizations: if the
localizations of `Z` and of `X` agree and `Z` factors as a finite sequence of normalized blowups
at closed points lying over the distinguished points, then so does `X`.

Normality of `S` is not needed here, and neither is the glueing theorem of [Stacks, Tag 0E8Q]:
the base-change functor of Tag 0BFU is fully faithful unconditionally,
`AlgebraicGeometry.BaseChangeFunctor.fullyFaithful`, so it carries the given isomorphism of
families of localizations to an isomorphism over `S`, and factoring as a sequence of normalized
blowups is invariant under isomorphism over `S`.

The full converse is
`AlgebraicGeometry.FinitePresentationAwayPointsSituation.factorsAsNormalizedPointBlowups_iff`,
whose global sequence need not be finitely presented over `S` and is therefore compared with `X` by
descent rather than through this functor. -/
theorem factorsAsNormalizedPointBlowups_of_baseChange_iso
    (D : FinitePresentationAwayPointsSituation.{u}) (BC : BaseChangeFunctor D)
    {X Z : D.globalCategory} (hXZ : BC.functor.obj Z ≅ BC.functor.obj X)
    (hZ : FactorsAsNormalizedPointBlowups D.S (Set.range D.points) Z.obj.left Z.obj.hom) :
    FactorsAsNormalizedPointBlowups D.S (Set.range D.points) X.obj.left X.obj.hom :=
  factorsAsNormalizedPointBlowups_of_overIso
    ((ObjectProperty.ι (IsFinitePresentationAway D.complement)).mapIso
      (BC.fullyFaithful.preimageIso hXZ).symm) hZ

end FinitePresentationAwayPointsSituation

end AlgebraicGeometry

end
