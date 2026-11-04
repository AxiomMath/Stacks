module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleComposition
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleExtension
public import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.DominatingBlowupFromFlattening
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Blowup.SectionExtension
public import StacksFrontier.AlgebraicGeometry.Blowup.Separation
public import StacksFrontier.AlgebraicGeometry.BlowupAmpleFamily.Noetherian
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GraphConstruction
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.NagataInputs

/-!
# Tag 0F3W: a blowup making the strict transform an isomorphism near a closure

Let `f : X ⟶ Y` be a proper morphism of quasi-compact, quasi-separated schemes, let `V ⊆ Y` be a
quasi-compact open and let `T ⊆ V` be closed in `V`. If `f` is an isomorphism over an open
neighbourhood of `T` inside `V`, then there is a `V`-admissible blowup of `Y` along which the
strict transform of `f` becomes an isomorphism over an open neighbourhood of the closure of the
inverse image of `T`.

## Main results

* `AlgebraicGeometry.exists_centre_isIso_strictTransform_near_closure_of_dominating`: the tag,
  with the two results of the source's Divisors chapter it uses carried as hypotheses —
  [Stacks, Tag 081T] and the admissibility of a composite of admissible blowups,
  [Stacks, Tag 080L].
* `AlgebraicGeometry.exists_centre_isIso_strictTransform_near_closure_of_affineCharts`: the
  tag, with [Stacks, Tag 080L] discharged outright and [Stacks, Tag 081T] carried only as far as
  `AlgebraicGeometry.AffineChartFlatteningCentre` allows — that predicate being the affine
  case of tag 0815 with tag 0815's hypotheses (2)-(5) deleted, which by
  `AlgebraicGeometry.affineChartFlatteningCentre_top_iff` amounts at `U = ⊤` to flatness of
  the module itself, so it is not a sound stand-in.

The tag itself, under exactly the source's hypotheses, is
`AlgebraicGeometry.exists_isAdmissibleBlowup_strictTransform_isIso_near_closure`.

Along the way, and of independent use:

* `AlgebraicGeometry.exists_disjoint_isConstructible_isClosed_superset`: two disjoint closed
  subsets of a quasi-compact, quasi-separated prespectral space sit inside disjoint
  *constructible* closed subsets. This is what feeds [Stacks, Tag 0F3V], which separates
  closures of constructible closed sets only.
* `AlgebraicGeometry.isIso_strictTransformToBlowUp_morphismRestrict_of_section`: over an open of
  the blowup across which the blowdown factors through `f`, the strict transform of `f` is an
  isomorphism. This is what turns the conclusion of [Stacks, Tag 081T] — a dominating blowup —
  into the conclusion this tag asks for.
* `AlgebraicGeometry.exists_centre_support_eq_compl_dominating`: every `V`-admissible blowup is
  dominated by the blowup of a centre supported on *exactly* the complement of `V`, by
  multiplying its centre with one supported there ([Stacks, Tag 080A]).

## Implementation notes

The source's proof: let `T'` be the complement in `V` of the largest open over which `f` is an
isomorphism, so `T` and `T'` are disjoint closed subsets of the spectral space `V`; enlarge them
to disjoint *constructible* closed subsets; separate their closures by a `V`-admissible blowup
`b₁ : Y₁ ⟶ Y` ([Stacks, Tag 0F3V]); over `Y₀ = Y₁ ∖ closure T'` the morphism is an isomorphism
on the part lying over `V`, so [Stacks, Tag 081S] — here used through [Stacks, Tag 081T], which
packages its conclusion as a dominating blowup — gives a blowup of a quasi-compact open `K` of
`Y₁` squeezed between the closure of the inverse image of `T` and `Y₀`; [Stacks, Tag 080M]
extends that blowup of `K` to one of `Y₁`; and [Stacks, Tag 080L] composes it with `b₁`.

Where the source says "after replacing `Y` by a `V`-admissible blowup", the Lean proof keeps
`Y₁` and `Y` apart and composes at the end, which is what makes [Stacks, Tag 080L] an explicit
input here.

## References

* [Stacks Project, Tag 0F3W](https://stacks.math.columbia.edu/tag/0F3W)
* [Stacks Project, Tag 0F3V](https://stacks.math.columbia.edu/tag/0F3V)
* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
* [Stacks Project, Tag 080M](https://stacks.math.columbia.edu/tag/080M)
* [Stacks Project, Tag 080L](https://stacks.math.columbia.edu/tag/080L)
* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 07ZU](https://stacks.math.columbia.edu/tag/07ZU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Two disjoint closed subsets of a quasi-compact, quasi-separated prespectral space are
contained in disjoint constructible closed subsets.** Take a quasi-compact open `K` with
`B ⊆ K ⊆ Aᶜ`; then `A' = Kᶜ` is a constructible closed superset of `A` disjoint from `B`. Repeat
with the roles exchanged to get `B'`. -/
theorem exists_disjoint_isConstructible_isClosed_superset {Z : Type u} [TopologicalSpace Z]
    [CompactSpace Z] [PrespectralSpace Z] [QuasiSeparatedSpace Z] (A B : Set Z)
    (hA : IsClosed A) (hB : IsClosed B) (hdisj : Disjoint A B) :
    ∃ A' B' : Set Z, A ⊆ A' ∧ B ⊆ B' ∧ IsClosed A' ∧ IsClosed B' ∧
      Topology.IsConstructible A' ∧ Topology.IsConstructible B' ∧ Disjoint A' B' := by
  obtain ⟨K, hKcompact, hKopen, hBK, hKA⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hB.isCompact hA.isOpen_compl
      fun x hxB hxA ↦ Set.disjoint_left.mp hdisj hxA hxB
  have hKcl : IsClosed Kᶜ := hKopen.isClosed_compl
  obtain ⟨K', hK'compact, hK'open, hK'sub, hK'B⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between hKcl.isCompact hB.isOpen_compl
      fun x hx hxB ↦ hx (hBK hxB)
  exact ⟨Kᶜ, K'ᶜ, fun x hx hxK ↦ hKA hxK hx, fun x hxB hxK' ↦ hK'B hxK' hxB, hKcl,
    hK'open.isClosed_compl, (hKcompact.isConstructible hKopen).compl,
    (hK'compact.isConstructible hK'open).compl,
    Set.disjoint_left.mpr fun x hx hx' ↦ hx' (hK'sub hx)⟩

/-! ### The strict transform over an open the blowup is dominated over -/

/-- The kernel of an open immersion is unchanged by pulling the open back along another open
immersion: both sides have the same ideal over every affine open, by
`AlgebraicGeometry.Scheme.ker_ideal_of_isPullback_of_isOpenImmersion` applied to the cartesian
square of the restriction. -/
theorem ker_comap_opens_ι {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f] (U : Y.Opens)
    [QuasiCompact U.ι] : U.ι.ker.comap f = (f ⁻¹ᵁ U).ι.ker := by
  ext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion U.ι (f ⁻¹ᵁ U).ι (f ∣_ U) f
      (isPullback_morphismRestrict f U).flip]

/-- **A section of `p` identifies the scheme-theoretic closure of the inverse image of a
scheme-theoretically dense open with the closed subscheme cut out by the section.** Over such an
open `U` the morphism `p` is an isomorphism, so the inverse image of `U` factors as `U` followed
by the section; the kernel of that composite is the kernel of the section. -/
theorem ker_preimage_eq_ker_of_section {X Y : Scheme.{u}} (p : X ⟶ Y) (j : Y ⟶ X)
    (hj : j ≫ p = 𝟙 Y) (U : Y.Opens) [IsIso (p ∣_ U)] (hU : U.ι.ker = ⊥) :
    (p ⁻¹ᵁ U).ι.ker = j.ker := by
  have H := isPullback_morphismRestrict p U
  have hw : (𝟙 U.toScheme) ≫ U.ι = (U.ι ≫ j) ≫ p := by
    rw [Category.assoc, hj, Category.comp_id, Category.id_comp]
  have hq₁ : H.lift (𝟙 U.toScheme) (U.ι ≫ j) hw ≫ (p ∣_ U) = 𝟙 U.toScheme := H.lift_fst _ _ _
  have hq₂ : H.lift (𝟙 U.toScheme) (U.ι ≫ j) hw ≫ (p ⁻¹ᵁ U).ι = U.ι ≫ j := H.lift_snd _ _ _
  have hq : (p ∣_ U) ≫ H.lift (𝟙 U.toScheme) (U.ι ≫ j) hw = 𝟙 _ := by
    rw [← cancel_mono (p ∣_ U), Category.assoc, hq₁, Category.id_comp, Category.comp_id]
  have heq : (p ∣_ U) ≫ U.ι ≫ j = (p ⁻¹ᵁ U).ι := by
    rw [← hq₂, ← Category.assoc, hq, Category.id_comp]
  rw [← heq, Scheme.Hom.ker_comp_of_isIso, Scheme.Hom.ker_comp, hU,
    Scheme.IdealSheafData.map_bot]

/-- **The closed subscheme cut out by the inverse image of a scheme-theoretically dense open maps
isomorphically to the base when `p` has a section there.** Its ideal is the kernel of the
section, which is a closed immersion, so the two closed subschemes agree. -/
theorem isIso_subschemeι_comp_of_section {X Y : Scheme.{u}} (p : X ⟶ Y) (j : Y ⟶ X)
    [IsClosedImmersion j] (hj : j ≫ p = 𝟙 Y) (U : Y.Opens) [IsIso (p ∣_ U)]
    (hU : U.ι.ker = ⊥) : IsIso ((p ⁻¹ᵁ U).ι.ker.subschemeι ≫ p) := by
  have hJ : (p ⁻¹ᵁ U).ι.ker = j.ker := ker_preimage_eq_ker_of_section p j hj U hU
  have hker : (p ⁻¹ᵁ U).ι.ker.subschemeι.ker = j.ker := by
    rw [Scheme.IdealSheafData.ker_subschemeι, hJ]
  have hle : j.ker ≤ (p ⁻¹ᵁ U).ι.ker.subschemeι.ker := hker.ge
  have hfac : IsClosedImmersion.lift j (p ⁻¹ᵁ U).ι.ker.subschemeι hle ≫ j =
      (p ⁻¹ᵁ U).ι.ker.subschemeι := IsClosedImmersion.lift_fac _ _ _
  have _ : IsIso (IsClosedImmersion.lift j (p ⁻¹ᵁ U).ι.ker.subschemeι hle) :=
    IsClosedImmersion.isIso_of_ker_eq _ j _ hfac hker
  rw [← hfac, Category.assoc, hj, Category.comp_id]
  infer_instance

/-- A morphism which has an isomorphism as a base change along an open immersion is an
isomorphism over that open. -/
theorem isIso_morphismRestrict_of_isPullback {X Y Z : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (g : Z ⟶ V.toScheme) (j : Z ⟶ X) (H : IsPullback g j V.ι f) [IsIso g] : IsIso (f ∣_ V) := by
  have h : IsIso (pullback.snd f V.ι) := by
    refine (isIso_comp_left_iff H.flip.isoPullback.hom _).mp ?_
    simpa only [IsPullback.isoPullback_hom_snd] using (inferInstance : IsIso g)
  refine (isIso_comp_left_iff (pullbackRestrictIsoRestrict f V).hom _).mp ?_
  rwa [pullbackRestrictIsoRestrict_hom_morphismRestrict]

/-- **The closed subscheme cut out by the inverse image of an open `U` is an isomorphism over an
open `V` that `p` is dominated over.** A morphism `g : V ⟶ X` with `g ≫ p = V.ι` is a section of
`p ∣_ V`, hence a closed immersion because `p` is separated; the previous lemma applies over `V`,
and the two closed subschemes form a cartesian square over the one downstairs. -/
theorem isIso_subschemeι_comp_morphismRestrict_of_section {X Y : Scheme.{u}} (p : X ⟶ Y)
    [IsSeparated p] (U V : Y.Opens) [QuasiCompact (p ⁻¹ᵁ U).ι] (g : V.toScheme ⟶ X)
    (hg : g ≫ p = V.ι) [IsIso ((p ∣_ V) ∣_ (V.ι ⁻¹ᵁ U))] (hU : (V.ι ⁻¹ᵁ U).ι.ker = ⊥) :
    IsIso (((p ⁻¹ᵁ U).ι.ker.subschemeι ≫ p) ∣_ V) := by
  have H := isPullback_morphismRestrict p V
  obtain ⟨s, hj⟩ : ∃ s : V.toScheme ⟶ (p ⁻¹ᵁ V).toScheme, s ≫ (p ∣_ V) = 𝟙 _ :=
    ⟨H.lift (𝟙 V.toScheme) g (by rw [Category.id_comp, hg]), H.lift_fst _ _ _⟩
  have _ : IsClosedImmersion (s ≫ (p ∣_ V)) := by
    rw [hj]
    infer_instance
  have _ : IsClosedImmersion s := IsClosedImmersion.of_comp s (p ∣_ V)
  -- the two kernels, downstairs on `X` and upstairs on the inverse image of `V`
  have hpre : (p ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U) = (p ⁻¹ᵁ V).ι ⁻¹ᵁ (p ⁻¹ᵁ U) := by
    rw [← Scheme.Hom.comp_preimage, morphismRestrict_ι, Scheme.Hom.comp_preimage]
  have hJ : (p ⁻¹ᵁ U).ι.ker.comap (p ⁻¹ᵁ V).ι = ((p ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)).ι.ker := by
    rw [ker_comap_opens_ι, hpre]
  have hle : (p ⁻¹ᵁ U).ι.ker ≤ ((p ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)).ι.ker.map (p ⁻¹ᵁ V).ι :=
    Scheme.IdealSheafData.le_map_iff_comap_le.mpr hJ.le
  have H' : IsPullback ((p ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)).ι.ker.subschemeι
      (Scheme.IdealSheafData.subschemeMap _ _ (p ⁻¹ᵁ V).ι hle) (p ⁻¹ᵁ V).ι
      (p ⁻¹ᵁ U).ι.ker.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _
      (Scheme.IdealSheafData.subschemeMap_subschemeι _ _ _ hle).symm
      (by simpa only [Scheme.IdealSheafData.ker_subschemeι] using hJ)
  have _ : IsIso (((p ∣_ V) ⁻¹ᵁ (V.ι ⁻¹ᵁ U)).ι.ker.subschemeι ≫ (p ∣_ V)) :=
    isIso_subschemeι_comp_of_section (p ∣_ V) s hj (V.ι ⁻¹ᵁ U) hU
  exact isIso_morphismRestrict_of_isPullback _ V _ _ (H'.paste_horiz H)

/-- The complement of the exceptional divisor of a blowup is scheme-theoretically dense, so the
kernel of its inclusion is zero: the blowup is the scheme-theoretic closure of that open. -/
theorem ker_ι_compl_support_exceptionalIdeal_eq_bot {S : Scheme.{u}} (I : S.IdealSheafData) :
    (Scheme.Opens.ι (exceptionalIdeal I).support.compl).ker = ⊥ :=
  ((Scheme.Opens.isSchemeTheoreticallyDense_iff_isSchemeTheoreticallyDominant
      (exceptionalIdeal I).support.compl).mp
    (Stacks.Divisors.isSchemeTheoreticallyDense_compl_of_isEffectiveCartierDivisor
      (exceptionalIdeal I) inferInstance)).ker_eq_bot

/-- **The strict transform is an isomorphism over an open of the blowup that `f` is dominated
over.** If `W ⊆ Bl_ℐ(S)` carries a morphism `g : W ⟶ X` with `g ≫ f` the blowdown of `W`, and if
the base change of `f` is an isomorphism over the part of `W` off the exceptional divisor, then
the strict transform of `f` is an isomorphism over `W`.

This is what turns the conclusion of [Stacks, Tag 081T] — a blowup dominating `f` — into the
conclusion of [Stacks, Tag 0F3W], an isomorphic strict transform. -/
theorem isIso_strictTransformToBlowUp_morphismRestrict_of_section {X S : Scheme.{u}} (f : X ⟶ S)
    [IsSeparated f] (I : S.IdealSheafData) (W : (blowUp I).Opens) (g : W.toScheme ⟶ X)
    (hg : g ≫ f = W.ι ≫ blowUpToBase I)
    [IsIso ((pullback.snd f (blowUpToBase I) ∣_ W) ∣_
      (W.ι ⁻¹ᵁ (exceptionalIdeal I).support.compl))] :
    IsIso (strictTransformToBlowUp f I ∣_ W) := by
  have hker : (W.ι ⁻¹ᵁ (exceptionalIdeal I).support.compl).ι.ker = ⊥ := by
    rw [← ker_comap_opens_ι W.ι (exceptionalIdeal I).support.compl,
      ker_ι_compl_support_exceptionalIdeal_eq_bot, Scheme.IdealSheafData.comap_bot]
  have hw : pullback.lift g W.ι hg ≫ pullback.snd f (blowUpToBase I) = W.ι :=
    pullback.lift_snd _ _ _
  have _ : IsSeparated (pullback.snd f (blowUpToBase I)) := inferInstance
  show IsIso (((Stacks.StrictTransform.ideal f (blowUpToBase I)
    (exceptionalIdeal I)).subschemeι ≫ pullback.snd f (blowUpToBase I)) ∣_ W)
  rw [Stacks.StrictTransform.ideal_eq_ker_ι f (blowUpToBase I) (exceptionalIdeal I)]
  exact isIso_subschemeι_comp_morphismRestrict_of_section (pullback.snd f (blowUpToBase I))
    (exceptionalIdeal I).support.compl W (pullback.lift g W.ι hg) hw hker

/-! ### Admissible blowups: the centre with full support -/

/-- **A `V`-admissible blowup is dominated by the blowup of a centre supported on exactly the
complement of `V`.** Multiply the centre `J` exhibiting the given blowup by a finite-type centre
`K` supported on all of `V ᶜ`: the product is finitely presented with support the union, which is
`Vᶜ`, and by [Stacks, Tag 080A] its blowup factors through the blowup in `J`.

The conclusion of [Stacks, Tag 0F3W] asks for a centre, and the proof needs its support to be
exactly `Vᶜ` so that the inverse image of `V` is precisely the complement of the exceptional
divisor. -/
theorem exists_centre_support_eq_compl_dominating {X Y : Scheme.{u}} [CompactSpace X]
    [QuasiSeparatedSpace X] (V : X.Opens) (hV : IsCompact (V : Set X)) (b : Y ⟶ X)
    (hb : Stacks.Blowup.IsAdmissibleBlowup V b) :
    ∃ I : X.IdealSheafData, FinitePresentation I.subschemeι ∧
      (I.support : Set X) = (V : Set X)ᶜ ∧
        ∃ g : blowUp I ⟶ Y, g ≫ b = blowUpToBase I := by
  obtain ⟨J, hJ, hJV, e, he⟩ := (Stacks.Blowup.isAdmissibleBlowup_iff V b).mp hb
  obtain ⟨K, hK, hKV⟩ := exists_isFiniteType_support_eq_compl X V hV
  refine ⟨J * K, finitePresentation_mul_subschemeι J K hJ hK, ?_, ?_⟩
  · rw [Scheme.IdealSheafData.support_mul, TopologicalSpace.Closeds.coe_sup, hKV]
    exact Set.union_eq_right.mpr fun x hx hVx ↦ Set.disjoint_left.mp hJV hVx hx
  · have he' : e.inv ≫ b = blowUpToBase J := by rw [← he, Iso.inv_hom_id_assoc]
    have hw : (blowUpMulIso J K).inv.left ≫
        blowUpToBase (K.comap (blowUpToBase J)) ≫ blowUpToBase J = blowUpToBase (J * K) := by
      simpa only [Over.mk_hom, Category.assoc] using Over.w (blowUpMulIso J K).inv
    refine ⟨(blowUpMulIso J K).inv.left ≫
      blowUpToBase (K.comap (blowUpToBase J)) ≫ e.inv, ?_⟩
    simpa only [Category.assoc, he'] using hw

/-! ### Tag 0F3W -/

/-- Restricting to `V` and then to the part of `V` lying over `U` is an isomorphism as soon as
the morphism is one over an open containing `V ⊓ U`: the double restriction is isomorphic, as an
arrow, to the single restriction to `V ⊓ U`. -/
theorem isIso_morphismRestrict_morphismRestrict_of_inf_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    (U V W : Y.Opens) (h : V ⊓ U ≤ W) (hW : IsIso (f ∣_ W)) :
    IsIso ((f ∣_ V) ∣_ (V.ι ⁻¹ᵁ U)) := by
  refine (Arrow.isIso_iff_isIso_of_isIso (morphismRestrictRestrict f V (V.ι ⁻¹ᵁ U)).hom).mpr ?_
  refine isIso_morphismRestrict_of_le f (V := W) ?_ hW
  rintro y ⟨x, hx, rfl⟩
  exact h ⟨x.2, hx⟩

/-- **Stacks Project, Tag 0F3W**, with the two results of the source's Divisors chapter it uses
carried as hypotheses: `h081T` is [Stacks, Tag 081T] and `h080L` is the statement that a
`V`-admissible blowup of a `V`-admissible blowup is again one, [Stacks, Tag 080L], which is the
source's licence to replace `Y` by a blowup of it.

Let `f : X ⟶ Y` be a proper morphism of quasi-compact, quasi-separated schemes, let `V ⊆ Y` be a
quasi-compact open, and let `T ⊆ V` be closed in `V` with `f` an isomorphism over some open
neighbourhood of `T` inside `V`. Then there is a `V`-admissible centre `I` on `Y` such that the
strict transform of `f` along the blowup of `Y` in `I` is an isomorphism over an open
neighbourhood of the closure of the inverse image of `T`. -/
theorem exists_centre_isIso_strictTransform_near_closure_of_dominating {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (V : Y.Opens) (hV : IsCompact (V : Set Y)) (T : Set Y)
    (hTV : T ⊆ (V : Set Y)) (hT : IsClosed (V.ι.base ⁻¹' T))
    (hiso : ∃ W : Y.Opens, W ≤ V ∧ T ⊆ (W : Set Y) ∧ IsIso (f ∣_ W))
    (h081T : ∀ (A B : Scheme.{u}) (q : A ⟶ B) (U : B.Opens), IsProper q → CompactSpace B →
      QuasiSeparatedSpace B → IsCompact (U : Set B) → IsIso (q ∣_ U) →
      ∃ (B' : Scheme.{u}) (c : B' ⟶ B), Stacks.Blowup.IsAdmissibleBlowup U c ∧
        ∃ g : B' ⟶ A, g ≫ q = c)
    (h080L : ∀ (Z Z' Z'' : Scheme.{u}) (U : Z.Opens) (c : Z' ⟶ Z) (c' : Z'' ⟶ Z'),
      CompactSpace Z → QuasiSeparatedSpace Z → Stacks.Blowup.IsAdmissibleBlowup U c →
      Stacks.Blowup.IsAdmissibleBlowup (c ⁻¹ᵁ U) c' →
        Stacks.Blowup.IsAdmissibleBlowup U (c' ≫ c)) :
    ∃ I : Y.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (V : Set Y) (I.support : Set Y) ∧
        ∃ W : (blowUp I).Opens,
          closure ((blowUpToBase I).base ⁻¹' T) ⊆ (W : Set (blowUp I)) ∧
            IsIso (strictTransformToBlowUp f I ∣_ W) := by
  classical
  obtain ⟨W, -, hTW, _⟩ := hiso
  have _ : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  have _ : QuasiSeparatedSpace V.toScheme := V.ι.isOpenEmbedding.quasiSeparatedSpace
  -- step 1: enlarge `T` and the complement of `W` in `V` to disjoint constructible closed sets
  obtain ⟨A', B', hAA', hBB', hA'closed, hB'closed, hA'c, hB'c, hdisj'⟩ :=
    exists_disjoint_isConstructible_isClosed_superset (V.ι.base ⁻¹' T)
      ((V.ι.base ⁻¹' (W : Set Y))ᶜ) hT (W.2.preimage V.ι.continuous).isClosed_compl
      (Set.disjoint_left.mpr fun x hxA hxB ↦ hxB (hTW hxA))
  -- step 2: [Stacks, Tag 0F3V] separates their closures after a `V`-admissible blowup
  obtain ⟨Y₁, b₁, hb₁, hclosures⟩ :=
    exists_isAdmissibleBlowup_disjoint_closures V hV A' B' hA'closed hB'closed hA'c hB'c hdisj'
  have _ : IsIso (b₁ ∣_ V) :=
    Stacks.BlowupAmpleFamily.isIso_morphismRestrict_of_isAdmissibleBlowup hb₁
  have _ : IsProper b₁ := isProper_of_isAdmissibleBlowup V b₁ hb₁
  have _ : CompactSpace Y₁ := QuasiCompact.compactSpace_of_compactSpace b₁
  have _ : QuasiSeparatedSpace Y₁ := quasiSeparatedSpace_of_quasiSeparated b₁
  have hV₁ : IsCompact ((b₁ ⁻¹ᵁ V : Y₁.Opens) : Set Y₁) := b₁.isCompact_preimage hV
  -- the open `Y₀` of `Y₁` away from the closure of the enlarged complement
  have hTY₀ : closure (b₁.base ⁻¹' T) ⊆ (closure (b₁.base ⁻¹' (V.ι.base '' B')))ᶜ := by
    have hsub := closure_mono (Set.preimage_mono
      (show T ⊆ V.ι.base '' A' from fun y hy ↦ ⟨⟨y, hTV hy⟩, hAA' hy, rfl⟩) (f := b₁.base))
    exact fun _ hx hy ↦ Set.disjoint_left.mp hclosures (hsub hx) hy
  have hY₀good : (b₁ ⁻¹ᵁ V : Y₁.Opens) ⊓
      ⟨(closure (b₁.base ⁻¹' (V.ι.base '' B')))ᶜ, isClosed_closure.isOpen_compl⟩ ≤
      b₁ ⁻¹ᵁ W := by
    intro x hx
    by_contra hxW
    exact hx.2 (subset_closure ⟨⟨b₁.base x, hx.1⟩, hBB' hxW, rfl⟩)
  -- step 3: a quasi-compact open `K` between the closure of the inverse image of `T` and `Y₀`
  obtain ⟨Kset, hKcompact, hKopen, hTK, hKY₀⟩ :=
    PrespectralSpace.exists_isCompact_and_isOpen_between
      (show IsCompact (closure (b₁.base ⁻¹' T)) from isClosed_closure.isCompact)
      isClosed_closure.isOpen_compl hTY₀
  set K : Y₁.Opens := ⟨Kset, hKopen⟩ with hKdef
  have _ : CompactSpace K.toScheme := isCompact_iff_compactSpace.mp hKcompact
  have _ : QuasiSeparatedSpace K.toScheme := K.ι.isOpenEmbedding.quasiSeparatedSpace
  have hV₀ : IsCompact ((K.ι ⁻¹ᵁ (b₁ ⁻¹ᵁ V) : K.toScheme.Opens) : Set K.toScheme) :=
    K.ι.isCompact_preimage hV₁
  -- step 4: [Stacks, Tag 081T] dominates the base change of `f` to `K` by a blowup of `K`
  have _ : IsProper (pullback.snd f (K.ι ≫ b₁)) := inferInstance
  have hf₀ : IsIso (pullback.snd f (K.ι ≫ b₁) ∣_ (K.ι ⁻¹ᵁ (b₁ ⁻¹ᵁ V))) := by
    refine isIso_morphismRestrict_of_le _ (V := (K.ι ≫ b₁) ⁻¹ᵁ W) ?_
      (isIso_morphismRestrict_pullback_snd_preimage f (K.ι ≫ b₁) W)
    exact fun x hx ↦ hY₀good ⟨hx, hKY₀ x.2⟩
  obtain ⟨Z₀, c₀, hc₀, g₀, hg₀⟩ :=
    h081T _ _ (pullback.snd f (K.ι ≫ b₁)) (K.ι ⁻¹ᵁ (b₁ ⁻¹ᵁ V)) inferInstance inferInstance
      inferInstance hV₀ hf₀
  -- step 5: [Stacks, Tag 080M] extends it to a blowup of `Y₁`, and [Stacks, Tag 080L] composes
  obtain ⟨Y₂, b₂, hb₂, j₀, H⟩ :=
    Stacks.Blowup.exists_admissibleBlowup_isPullback (b₁ ⁻¹ᵁ V) K hV₁ hKcompact c₀ hc₀
  have hb : Stacks.Blowup.IsAdmissibleBlowup V (b₂ ≫ b₁) :=
    h080L Y Y₁ Y₂ V b₁ b₂ inferInstance inferInstance hb₁ hb₂
  -- step 6: the composite is dominated by the blowup of a centre supported on exactly `Vᶜ`
  obtain ⟨I, hI, hIV, a, ha⟩ := exists_centre_support_eq_compl_dominating V hV _ hb
  have hdisj : Disjoint (V : Set Y) (I.support : Set Y) := by
    rw [hIV]
    exact disjoint_compl_right
  have hab : (a ≫ b₂) ≫ b₁ = blowUpToBase I := by rw [Category.assoc, ha]
  set W' : (blowUp I).Opens := (a ≫ b₂) ⁻¹ᵁ K with hW'
  -- the lift of `W'` into `X`
  have hw : ((a ≫ b₂) ∣_ K) ≫ K.ι = (W'.ι ≫ a) ≫ b₂ := by
    rw [morphismRestrict_ι, Category.assoc]
  have hq : H.lift ((a ≫ b₂) ∣_ K) (W'.ι ≫ a) hw ≫ c₀ = (a ≫ b₂) ∣_ K := H.lift_fst _ _ _
  have hg : (H.lift ((a ≫ b₂) ∣_ K) (W'.ι ≫ a) hw ≫ g₀ ≫ pullback.fst f (K.ι ≫ b₁)) ≫ f =
      W'.ι ≫ blowUpToBase I := by
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc g₀, hg₀,
      ← Category.assoc _ c₀, hq, ← Category.assoc, morphismRestrict_ι, Category.assoc,
      Category.assoc, ha]
  refine ⟨I, hI, hdisj, W', ?_, ?_⟩
  · have hpre : (blowUpToBase I).base ⁻¹' T = (a ≫ b₂).base ⁻¹' (b₁.base ⁻¹' T) := by
      rw [← hab]
      rfl
    rw [hpre]
    exact fun x hx ↦ hTK ((a ≫ b₂).continuous.closure_preimage_subset _ hx)
  · have hEV : (blowUpToBase I ⁻¹ᵁ V : (blowUp I).Opens) = (exceptionalIdeal I).support.compl :=
      preimage_eq_compl_support_exceptionalIdeal I V hIV
    have _ : IsIso ((pullback.snd f (blowUpToBase I) ∣_ W') ∣_
        (W'.ι ⁻¹ᵁ (exceptionalIdeal I).support.compl)) := by
      refine isIso_morphismRestrict_morphismRestrict_of_inf_le _ _ W'
        (blowUpToBase I ⁻¹ᵁ W) ?_
        (isIso_morphismRestrict_pullback_snd_preimage f (blowUpToBase I) W)
      rw [← hEV]
      intro x hx
      have hxmap : b₁.base ((a ≫ b₂).base x) = (blowUpToBase I).base x :=
        congrArg (fun k : blowUp I ⟶ Y ↦ k.base x) hab
      have hxV : b₁.base ((a ≫ b₂).base x) ∈ (V : Set Y) := by
        rw [hxmap]
        exact hx.2
      show (blowUpToBase I).base x ∈ (W : Set Y)
      rw [← hxmap]
      exact hY₀good (show (a ≫ b₂).base x ∈ _ from ⟨hxV, hKY₀ hx.1⟩)
    exact isIso_strictTransformToBlowUp_morphismRestrict_of_section f I W' _ hg

/-- **Stacks Project, Tag 0F3W.** Let `f : X ⟶ Y` be a proper morphism of quasi-compact,
quasi-separated schemes, let `V ⊆ Y` be a quasi-compact open and let `T ⊆ V` be closed in `V`.
Suppose `f` is an isomorphism over some open neighbourhood of `T` inside `V`. Then there is a
`V`-admissible centre `I` on `Y` — finitely presented and supported away from `V` — such that
the strict transform of `f` along the blowup of `Y` in `I` is an isomorphism over an open
neighbourhood of the closure of the inverse image of `T`.

The two results of the source's Divisors chapter that the proof uses are discharged as far as
the development allows: [Stacks, Tag 081T] by
`AlgebraicGeometry.exists_isAdmissibleBlowup_dominating_of_affineCharts`, which carries only
`AlgebraicGeometry.AffineChartFlatteningCentre`, and [Stacks, Tag 080L] by
`Stacks.Blowup.IsAdmissibleBlowup.comp`, which is proved outright and carries nothing.

This tag is NOT registered on this declaration. The statement is faithful, but the proof still
carries one hypothesis this development has not proved: `AffineChartFlatteningCentre`, whose
only producer `AffineChartFlatteningCentre.of_isFlatOver` assumes the module already flat
over the base. A tag counts only on a declaration proved under the source's own hypotheses, so
the attribute waits on that one.
-/
theorem exists_centre_isIso_strictTransform_near_closure_of_affineCharts {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsProper f] [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y]
    [QuasiSeparatedSpace Y] (V : Y.Opens) (hV : IsCompact (V : Set Y)) (T : Set Y)
    (hTV : T ⊆ (V : Set Y)) (hT : IsClosed (V.ι.base ⁻¹' T))
    (hiso : ∃ W : Y.Opens, W ≤ V ∧ T ⊆ (W : Set Y) ∧ IsIso (f ∣_ W))
    (H : ∀ (A B : Scheme.{u}) (q : A ⟶ B) (U : B.Opens),
      AffineChartFlatteningCentre q A.unitModule U) :
    ∃ I : Y.IdealSheafData, FinitePresentation I.subschemeι ∧
      Disjoint (V : Set Y) (I.support : Set Y) ∧
        ∃ W : (blowUp I).Opens,
          closure ((blowUpToBase I).base ⁻¹' T) ⊆ (W : Set (blowUp I)) ∧
            IsIso (strictTransformToBlowUp f I ∣_ W) :=
  exists_centre_isIso_strictTransform_near_closure_of_dominating f V hV T hTV hT hiso
    (fun A B q U _ _ _ hU _ ↦ exists_isAdmissibleBlowup_dominating_of_affineCharts q U hU
      (H A B q U))
    (fun _ _ _ U c c' _ _ hc hc' ↦ Stacks.Blowup.IsAdmissibleBlowup.comp U c c' hc hc')

end AlgebraicGeometry

end
