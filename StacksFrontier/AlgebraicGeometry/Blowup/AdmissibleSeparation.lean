module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import StacksFrontier.AlgebraicGeometry.Properties.FiniteTypeIdealSheafOfOpen
public import StacksFrontier.AlgebraicGeometry.Blowup.Admissible
public import StacksFrontier.AlgebraicGeometry.Blowup.AffineChart
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesRestrictDegOne
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendIdealSheaf

/-!
# Separating two disjoint quasi-compact opens by a blowup

Let `X` be a quasi-compact and quasi-separated scheme and let `U, V ⊆ X` be disjoint
quasi-compact open subschemes. There is a `U ∪ V`-admissible blowup `b : X' ⟶ X` whose source
splits as a disjoint union of two open subschemes `X' = X'₁ ⨿ X'₂` with `b⁻¹(U) ⊆ X'₁` and
`b⁻¹(V) ⊆ X'₂`.

The construction follows the source. Choose quasi-coherent sheaves of ideals `ℐ`, `𝒥` of finite
type with `X ∖ U = V(ℐ)` and `X ∖ V = V(𝒥)`. Since `U` and `V` are disjoint, `V(ℐ𝒥) = X` as a
set, so `ℐ𝒥` is contained in the nilradical. Blow up in `ℐ + 𝒥`: this is `U ∪ V`-admissible,
because `V(ℐ + 𝒥) = X ∖ (U ∪ V)`. Over an affine open `W` the blowup is covered by the spectra of
the affine blowup algebras `Γ(X, W)[(ℐ + 𝒥)(W)/c]`, `c ∈ (ℐ + 𝒥)(W)`
(`Stacks.Blowup.iSup_opensRange_blowUpAffineChart`, Stacks tag 0804), and it suffices to take the
charts with `c ∈ ℐ(W)` and those with `c ∈ 𝒥(W)`: writing `c = a + b` shows the two families
still cover, and for `a ∈ ℐ(W)`, `b ∈ 𝒥(W)` the two charts are disjoint, because `a⁽¹⁾b⁽¹⁾` is a
nilpotent element of the Rees algebra and so cuts out the empty basic open of its `Proj`.

Comparing charts over two *different* affine opens is done by restricting both to a common affine
open inside the intersection, along the transition morphism of the relative `Proj` the blowup is
glued from.

## Main results

* `Stacks.Blowup.exists_admissibleBlowup_disjoint_open_cover`: **Tag 080P**, the separation
  statement above.
* `Stacks.Blowup.exists_disjoint_open_cover_blowUp_sup`: the splitting of the blowup in `ℐ + 𝒥`
  for a *given* pair of ideal sheaves with nilpotent product, which is the step of the argument
  that survives a base change of the blowup.
* `Stacks.Blowup.exists_admissibleBlowup_pairwise_disjoint_open_cover`: the same statement for a
  finite family of pairwise disjoint quasi-compact opens, which is the form in which the source
  uses Tag 080P to separate the finitely many loci where a locally constant invariant on `U`
  takes a fixed value. The construction is the same with `∑ ℐ_i` in place of `ℐ + 𝒥`: the two
  facts about the charts that the proof needs — that charts attached to ideal sheaves with
  nilpotent product are disjoint, and that the preimage of an open away from the support of `ℐ`
  is covered by the charts of `ℐ` — are already proved for an arbitrary centre dominating the
  ideal sheaf, so only the covering statement has to be redone, by induction over the index
  set.

## Implementation notes

"`X'` is the disjoint union of `X'₁` and `X'₂`" is recorded as two disjoint opens of `X'` whose
supremum is `⊤`, rather than as an isomorphism with a coproduct: an open subscheme of `X'` *is*
the data of an open of `X'`, and the two conditions say exactly that the two open subschemes are
disjoint and jointly cover.

The half of Stacks tag 01PH that the proof consumes — a quasi-compact open of a quasi-compact and
quasi-separated scheme is the complement of the support of a quasi-coherent sheaf of ideals of
finite type — is not available in the library, so it is proved here as
`AlgebraicGeometry.exists_isFiniteType_support_eq_compl`: the vanishing ideal of the complement is
everything on the affine opens inside the open, and `Stacks.IdealSheaf.exists_fg_le_of_mem`
(Stacks tag 01PF for sheaves of ideals) shrinks it to a finite type subsheaf retaining a unit
section on each member of a finite affine cover of the open.

## References

* [Stacks Project, Tag 080P](https://stacks.math.columbia.edu/tag/080P)
* [Stacks Project, Tag 0804](https://stacks.math.columbia.edu/tag/0804)
* [Stacks Project, Tag 01PF](https://stacks.math.columbia.edu/tag/01PF)
* [Stacks Project, Tag 01PH](https://stacks.math.columbia.edu/tag/01PH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Polynomial TopologicalSpace
open AlgebraicGeometry.Scheme.IdealSheafData

universe u

namespace Stacks.Blowup

/-! ### Basic opens of `Proj` -/

/-- A basic open of `Proj` attached to a sum is covered by the two basic opens of the summands:
if a homogeneous prime contains both summands it contains the sum. -/
private theorem projBasicOpen_add_le_sup {R : Type*} [CommRing R] {σ : Type*} [SetLike σ R]
    [AddSubgroupClass σ R] (A : ℕ → σ) [GradedRing A] (a b : R) :
    Proj.basicOpen A (a + b) ≤ Proj.basicOpen A a ⊔ Proj.basicOpen A b := by
  intro x hx
  show x ∈ (Proj.basicOpen A a : Set (Proj A)) ∪ (Proj.basicOpen A b : Set (Proj A))
  by_cases ha : a ∈ x.asHomogeneousIdeal
  · by_cases hb : b ∈ x.asHomogeneousIdeal
    · exact absurd (add_mem ha hb) ((Proj.mem_basicOpen A (a + b) x).1 hx)
    · exact Or.inr ((Proj.mem_basicOpen A b x).2 hb)
  · exact Or.inl ((Proj.mem_basicOpen A a x).2 ha)

/-- A nilpotent element cuts out the empty basic open of `Proj`. -/
private theorem projBasicOpen_eq_bot_of_isNilpotent {R : Type*} [CommRing R] {σ : Type*}
    [SetLike σ R] [AddSubgroupClass σ R] (A : ℕ → σ) [GradedRing A] {a : R}
    (ha : IsNilpotent a) : Proj.basicOpen A a = ⊥ := by
  obtain ⟨n, hn⟩ := ha
  rw [← Proj.basicOpen_pow A a (n + 1) n.succ_pos, pow_succ, hn, zero_mul,
    Proj.basicOpen_zero]

/-! ### Degree-one elements of the Rees algebra -/

/-- The degree-one element attached to a sum of two sections of the ideal is the sum of the two
degree-one elements. -/
private theorem reesDegOne_add {R : Type u} [CommRing R] (I : Ideal R) (a b : I) :
    reesDegOne I (a + b).2 = reesDegOne I a.2 + reesDegOne I b.2 :=
  Subtype.ext (by
    show monomial 1 ((a : R) + (b : R)) = monomial 1 (a : R) + monomial 1 (b : R)
    rw [map_add])

/-- If the product of two sections of the ideal is nilpotent, so is the product of the two
degree-one elements of the Rees algebra: that product is the monomial `(ab)·t²`. -/
private theorem isNilpotent_reesDegOne_mul {R : Type u} [CommRing R] (I : Ideal R) (a b : I)
    (hab : IsNilpotent ((a : R) * b)) :
    IsNilpotent (reesDegOne I a.2 * reesDegOne I b.2) := by
  obtain ⟨n, hn⟩ := hab
  refine ⟨n + 1, Subtype.ext ?_⟩
  show (monomial 1 (a : R) * monomial 1 (b : R)) ^ (n + 1) = 0
  rw [monomial_mul_monomial, monomial_pow, pow_succ, hn, zero_mul, map_zero]

/-! ### The affine charts of a blowup, as opens of the blowup -/

variable {X : Scheme.{u}}

/-- The affine chart of the blowup of `X` in `ℐ` attached to an affine open `W` of `X` and a
section `a ∈ ℐ(W)`, as an open of the blowup: the image of the basic open `D₊(a⁽¹⁾)` of
`Proj (Γ(X, W)[ℐ(W)t])` under the chart of the blowup over `W`. By Stacks tag 0804 this is the
spectrum of the affine blowup algebra `Γ(X, W)[ℐ(W)/a]`. -/
private def chartOpen (ℐ : X.IdealSheafData) (W : X.affineOpens) (a : ℐ.ideal W) :
    (blowUp ℐ).Opens :=
  blowUpChart ℐ W ''ᵁ Proj.basicOpen (reesGrading (ℐ.ideal W)) (reesDegOne (ℐ.ideal W) a.2)

/-- A point of the blowup lies in a chart exactly when it is the image of a point of the
corresponding basic open of `Proj` of the Rees algebra. -/
private theorem mem_chartOpen (ℐ : X.IdealSheafData) (W : X.affineOpens) (a : ℐ.ideal W)
    (p : blowUp ℐ) :
    p ∈ chartOpen ℐ W a ↔ ∃ q, q ∈ Proj.basicOpen (reesGrading (ℐ.ideal W))
      (reesDegOne (ℐ.ideal W) a.2) ∧ blowUpChart ℐ W q = p :=
  Iff.rfl

/-- The chart attached to `a ∈ ℐ(W)` is the spectrum of the affine blowup algebra
`Γ(X, W)[ℐ(W)/a]`. -/
private theorem chartOpen_eq_opensRange (ℐ : X.IdealSheafData) (W : X.affineOpens)
    (a : ℐ.ideal W) : chartOpen ℐ W a = (blowUpAffineChart ℐ W a.2).opensRange := by
  rw [chartOpen, ← opensRange_specAffineBlowupι (ℐ.ideal W) (a : Γ(X, W.1)) a.2,
    ← Scheme.Hom.opensRange_comp]
  rfl

/-- **Stacks Project, Tag 0804.** The charts attached to the sections of `ℐ(W)` cover the
preimage of `W` in the blowup. -/
private theorem iSup_chartOpen (ℐ : X.IdealSheafData) (W : X.affineOpens) :
    ⨆ a : ℐ.ideal W, chartOpen ℐ W a = blowUpToBase ℐ ⁻¹ᵁ (W : X.Opens) := by
  rw [← iSup_opensRange_blowUpAffineChart ℐ W]
  exact iSup_congr fun a => chartOpen_eq_opensRange ℐ W a

/-- Each chart over `W` lies over `W`. -/
private theorem chartOpen_le_preimage (ℐ : X.IdealSheafData) (W : X.affineOpens)
    (a : ℐ.ideal W) : chartOpen ℐ W a ≤ blowUpToBase ℐ ⁻¹ᵁ (W : X.Opens) :=
  (iSup_chartOpen ℐ W) ▸ le_iSup (fun a : ℐ.ideal W => chartOpen ℐ W a) a

/-- Every point over `W` lies in the chart of some section of `ℐ(W)`. -/
private theorem exists_mem_chartOpen (ℐ : X.IdealSheafData) (W : X.affineOpens) {p : blowUp ℐ}
    (hp : blowUpToBase ℐ p ∈ (W : X.Opens)) : ∃ a : ℐ.ideal W, p ∈ chartOpen ℐ W a := by
  have hmem : p ∈ ⨆ a : ℐ.ideal W, chartOpen ℐ W a := by
    rw [iSup_chartOpen]; exact hp
  exact Opens.mem_iSup.mp hmem

/-- The chart of a sum is covered by the charts of the two summands. -/
private theorem chartOpen_add_le (ℐ : X.IdealSheafData) (W : X.affineOpens)
    (a b : ℐ.ideal W) :
    chartOpen ℐ W (a + b) ≤ chartOpen ℐ W a ⊔ chartOpen ℐ W b := by
  intro p hp
  obtain ⟨q, hq, hqp⟩ := (mem_chartOpen ℐ W (a + b) p).mp hp
  rw [reesDegOne_add] at hq
  rcases projBasicOpen_add_le_sup _ _ _ hq with h | h
  · exact Or.inl ((mem_chartOpen ℐ W a p).mpr ⟨q, h, hqp⟩)
  · exact Or.inr ((mem_chartOpen ℐ W b p).mpr ⟨q, h, hqp⟩)

/-- Two charts over the same affine open are disjoint as soon as the product of the two sections
is nilpotent: the product of the two degree-one elements of the Rees algebra is then nilpotent,
and the basic open it cuts out — the intersection of the two — is empty. -/
private theorem disjoint_chartOpen (ℐ : X.IdealSheafData) (W : X.affineOpens) (a b : ℐ.ideal W)
    (hab : IsNilpotent ((a : Γ(X, W.1)) * b)) :
    Disjoint (chartOpen ℐ W a) (chartOpen ℐ W b) := by
  refine Opens.coe_disjoint.mp (Set.disjoint_left.mpr fun p hpa hpb => ?_)
  obtain ⟨q, hq, hqp⟩ := (mem_chartOpen ℐ W a p).mp hpa
  obtain ⟨r, hr, hrp⟩ := (mem_chartOpen ℐ W b p).mp hpb
  obtain rfl : q = r :=
    (blowUpChart ℐ W).isOpenEmbedding.injective (hqp.trans hrp.symm)
  have hbot := projBasicOpen_eq_bot_of_isNilpotent (reesGrading (ℐ.ideal W))
    (isNilpotent_reesDegOne_mul (ℐ.ideal W) a b hab)
  have hmem : q ∈ Proj.basicOpen (reesGrading (ℐ.ideal W))
      (reesDegOne (ℐ.ideal W) a.2 * reesDegOne (ℐ.ideal W) b.2) := by
    rw [Proj.basicOpen_mul]; exact ⟨hq, hr⟩
  rw [hbot] at hmem
  exact hmem

/-! ### Comparing charts over different affine opens -/

/-- The chart of the blowup over a smaller affine open factors through the chart over a bigger
one, along the transition morphism of the relative `Proj`. -/
private theorem blowUpChart_transition (ℐ : X.IdealSheafData) {T W : X.affineOpens} (h : T ≤ W) :
    Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h) ≫ blowUpChart ℐ W = blowUpChart ℐ T :=
  colimit.w (reesData ℐ).gluingData.functor (homOfLE h)

/-- A point of a chart over `W` which lies over a smaller affine open `T` already lies in the
chart over `T` attached to the restricted section. -/
private theorem mem_chartOpen_of_le (ℐ : X.IdealSheafData) {T W : X.affineOpens} (h : T ≤ W)
    (a : ℐ.ideal W) {p : blowUp ℐ} (hp : p ∈ chartOpen ℐ W a)
    (hT : blowUpToBase ℐ p ∈ (T : X.Opens)) :
    p ∈ chartOpen ℐ T ⟨(sheafRestrict h).hom (a : Γ(X, W.1)), sheafRestrict_mem_ideal ℐ h a⟩ := by
  obtain ⟨q, hq, hqp⟩ := (mem_chartOpen ℐ W a p).mp hp
  have hpre : p ∈ (blowUpChart ℐ T).opensRange := by
    rw [← blowUpToBase_preimage_coe]; exact hT
  obtain ⟨r, hrp⟩ := hpre
  have hfac : blowUpChart ℐ W (Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h) r)
      = blowUpChart ℐ T r :=
    congrArg (fun f : Proj (reesGrading (ℐ.ideal T)) ⟶ blowUp ℐ => f.base r)
      (blowUpChart_transition ℐ h)
  obtain rfl : Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h) r = q :=
    (blowUpChart ℐ W).isOpenEmbedding.injective (hfac.trans (hrp.trans hqp.symm))
  refine (mem_chartOpen ℐ T _ p).mpr ⟨r, ?_, hrp⟩
  have hmem : r ∈ Proj.map (reesRestrict ℐ h) (reesIrrelevant_le ℐ h) ⁻¹ᵁ
      Proj.basicOpen (reesGrading (ℐ.ideal W)) (reesDegOne (ℐ.ideal W) a.2) := hq
  rwa [Proj.map_preimage_basicOpen, reesRestrict_reesDegOne] at hmem

/-! ### The two halves of the blowup -/

/-- The union of all charts of the blowup of `X` in `K` attached to sections of a smaller ideal
sheaf `I ≤ K`. -/
private def chartsFromIdeal (I K : X.IdealSheafData) (hIK : I ≤ K) : (blowUp K).Opens :=
  ⨆ W : X.affineOpens, ⨆ a : I.ideal W, chartOpen K W ⟨a, le_def.mp hIK W a.2⟩

/-- Each chart attached to a section of `I` lies in the union. -/
private theorem chartOpen_le_chartsFromIdeal (I K : X.IdealSheafData) (hIK : I ≤ K)
    (W : X.affineOpens) (a : I.ideal W) :
    chartOpen K W ⟨(a : Γ(X, W.1)), le_def.mp hIK W a.2⟩ ≤ chartsFromIdeal I K hIK :=
  le_iSup_of_le W (le_iSup_of_le a le_rfl)

/-- The charts attached to `I` together with those attached to `J` cover the blowup in `I + J`:
over an affine open every section of `(I + J)(W)` is a sum of a section of `I(W)` and one of
`J(W)`, and the chart of a sum is covered by the charts of the summands. -/
private theorem chartsFromIdeal_sup (I J : X.IdealSheafData) :
    chartsFromIdeal I (I ⊔ J) le_sup_left ⊔ chartsFromIdeal J (I ⊔ J) le_sup_right = ⊤ := by
  refine top_le_iff.mp fun p _ => ?_
  obtain ⟨W, hW, hpW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (Opens.mem_top (blowUpToBase (I ⊔ J) p))
  obtain ⟨c, hc⟩ := exists_mem_chartOpen (I ⊔ J) ⟨W, hW⟩ hpW
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp c.2
  have hc' : c = ⟨a, (le_sup_left : I ≤ I ⊔ J) ⟨W, hW⟩ ha⟩
      + ⟨b, (le_sup_right : J ≤ I ⊔ J) ⟨W, hW⟩ hb⟩ := Subtype.ext hab.symm
  rw [hc'] at hc
  rcases chartOpen_add_le (I ⊔ J) ⟨W, hW⟩ _ _ hc with h | h
  · exact Or.inl (chartOpen_le_chartsFromIdeal I (I ⊔ J) le_sup_left ⟨W, hW⟩ ⟨a, ha⟩ h)
  · exact Or.inr (chartOpen_le_chartsFromIdeal J (I ⊔ J) le_sup_right ⟨W, hW⟩ ⟨b, hb⟩ h)

/-- The charts attached to `I` are disjoint from those attached to `J` as soon as `IJ` is
contained in the nilradical: two such charts both lie over an affine open inside the intersection
of their bases, and there they are disjoint by `Stacks.Blowup.disjoint_chartOpen`. -/
private theorem disjoint_chartsFromIdeal (I J K : X.IdealSheafData) (hIK : I ≤ K) (hJK : J ≤ K)
    (hIJ : I * J ≤ X.nilradical) :
    Disjoint (chartsFromIdeal I K hIK) (chartsFromIdeal J K hJK) := by
  rw [chartsFromIdeal, chartsFromIdeal]
  simp only [iSup_disjoint_iff, disjoint_iSup_iff]
  intro Z b W a
  refine Opens.coe_disjoint.mp (Set.disjoint_left.mpr fun p hpW hpZ => ?_)
  have hW := chartOpen_le_preimage K W ⟨a, le_def.mp hIK W a.2⟩ hpW
  have hZ := chartOpen_le_preimage K Z ⟨b, le_def.mp hJK Z b.2⟩ hpZ
  obtain ⟨T, hT, hpT, hTWZ⟩ :=
    exists_isAffineOpen_mem_and_subset (U := W.1 ⊓ Z.1) ⟨hW, hZ⟩
  have hTsub : T ≤ W.1 ⊓ Z.1 := hTWZ
  have hTW : (⟨T, hT⟩ : X.affineOpens) ≤ W := hTsub.trans inf_le_left
  have hTZ : (⟨T, hT⟩ : X.affineOpens) ≤ Z := hTsub.trans inf_le_right
  have haT := mem_chartOpen_of_le K hTW ⟨a, le_def.mp hIK W a.2⟩ hpW hpT
  have hbT := mem_chartOpen_of_le K hTZ ⟨b, le_def.mp hJK Z b.2⟩ hpZ hpT
  have hnil : IsNilpotent
      ((sheafRestrict hTW).hom (a : Γ(X, W.1)) * (sheafRestrict hTZ).hom (b : Γ(X, Z.1))) :=
    mem_nilradical.mp (hIJ ⟨T, hT⟩ (Ideal.mul_mem_mul (sheafRestrict_mem_ideal I hTW ⟨a, a.2⟩)
      (sheafRestrict_mem_ideal J hTZ ⟨b, b.2⟩)))
  exact Set.disjoint_left.mp
    (Opens.coe_disjoint.mpr (disjoint_chartOpen K ⟨T, hT⟩ _ _ hnil)) haT hbT

/-- The preimage of an open disjoint from the support of `I` is covered by the charts attached to
`I`: on an affine open inside it `I` is everything, so every section of `K` there is a section of
`I`. -/
private theorem preimage_le_chartsFromIdeal (I K : X.IdealSheafData) (hIK : I ≤ K) (U : X.Opens)
    (hU : Disjoint (U : Set X) (I.support : Set X)) :
    blowUpToBase K ⁻¹ᵁ U ≤ chartsFromIdeal I K hIK := by
  intro p hp
  obtain ⟨W, hW, hpW, hWU⟩ := exists_isAffineOpen_mem_and_subset (U := U) hp
  have htop := AlgebraicGeometry.Scheme.IdealSheafData.ideal_eq_top_of_disjoint_support I
    ⟨W, hW⟩ (hU.mono_left hWU)
  obtain ⟨a, ha⟩ := exists_mem_chartOpen K ⟨W, hW⟩ hpW
  exact chartOpen_le_chartsFromIdeal I K hIK ⟨W, hW⟩ ⟨a, htop ▸ Submodule.mem_top⟩ ha

/-- **The blowup in a sum of two ideal sheaves with nilpotent product splits.** Let `X` be a
scheme, let `ℐ` and `𝒥` be quasi-coherent sheaves of ideals whose product is contained in the
nilradical, and let `U, V ⊆ X` be opens disjoint from the support of `ℐ` and from the support of
`𝒥` respectively. Then the blowup of `X` in `ℐ + 𝒥` is the disjoint union of two open
subschemes, the first containing the inverse image of `U` and the second that of `V`.

The two pieces are the unions of the affine charts of Stacks tag 0804 attached to the sections of
`ℐ` and to those of `𝒥`. This is the content of the proof of Stacks tag 080P for a given pair of
ideal sheaves, where `Stacks.Blowup.exists_admissibleBlowup_disjoint_open_cover` asserts it for
the pair that proof chooses; it is the form in which the statement is consumed by a base change
of the blowup, whose centre is the given pair restricted to the base. -/
theorem exists_disjoint_open_cover_blowUp_sup (I J : X.IdealSheafData)
    (hIJ : I * J ≤ X.nilradical) (U V : X.Opens)
    (hU : Disjoint (U : Set X) (I.support : Set X))
    (hV : Disjoint (V : Set X) (J.support : Set X)) :
    ∃ U₁ U₂ : (blowUp (I ⊔ J)).Opens, Disjoint U₁ U₂ ∧ U₁ ⊔ U₂ = ⊤ ∧
      blowUpToBase (I ⊔ J) ⁻¹ᵁ U ≤ U₁ ∧ blowUpToBase (I ⊔ J) ⁻¹ᵁ V ≤ U₂ :=
  ⟨chartsFromIdeal I (I ⊔ J) le_sup_left, chartsFromIdeal J (I ⊔ J) le_sup_right,
    disjoint_chartsFromIdeal I J (I ⊔ J) le_sup_left le_sup_right hIJ,
    chartsFromIdeal_sup I J,
    preimage_le_chartsFromIdeal I (I ⊔ J) le_sup_left U hU,
    preimage_le_chartsFromIdeal J (I ⊔ J) le_sup_right V hV⟩

/-! ### Cutting out a quasi-compact open by an ideal sheaf of finite type -/

/-- The ideal of a supremum of two ideal sheaves on an affine open is the supremum of the two
ideals. -/
private theorem ideal_sup_apply (I J : X.IdealSheafData) (W : X.affineOpens) :
    (I ⊔ J).ideal W = I.ideal W ⊔ J.ideal W := rfl

/-- A quasi-coherent sheaf of ideals which is everything on each member of a finite family of
affine opens has a finite type quasi-coherent subsheaf of ideals with the same property. -/
private theorem exists_isFiniteType_forall_ideal_eq_top [CompactSpace X] [QuasiSeparatedSpace X]
    (K : X.IdealSheafData) {s : Set X.affineOpens} (hs : s.Finite) :
    (∀ W ∈ s, K.ideal W = ⊤) →
      ∃ J : X.IdealSheafData, J ≤ K ∧ J.IsFiniteType ∧ ∀ W ∈ s, J.ideal W = ⊤ := by
  have hbot : (⊥ : X.IdealSheafData).IsFiniteType := fun _ => Submodule.fg_bot
  induction s, hs using Set.Finite.induction_on with
  | empty => exact fun _ => ⟨⊥, bot_le, hbot, by simp⟩
  | @insert W s hW hs ih =>
    intro hKs
    obtain ⟨J, hJK, hJft, hJtop⟩ := ih fun V hV => hKs V (Set.mem_insert_of_mem _ hV)
    obtain ⟨J', hJ'K, hJ'ft, hJ'one⟩ :=
      Stacks.IdealSheaf.exists_fg_le_of_mem K W.2 (a := 1)
        (by rw [hKs W (Set.mem_insert _ _)]; exact Submodule.mem_top)
    refine ⟨J ⊔ J', sup_le hJK hJ'K, hJft.sup hJ'ft, fun V hV => ?_⟩
    rw [ideal_sup_apply]
    rcases Set.mem_insert_iff.mp hV with rfl | hV
    · exact (Ideal.eq_top_iff_one _).mpr (Submodule.mem_sup_right hJ'one)
    · rw [hJtop V hV, top_sup_eq]

/-- The ideal of a supremum of ideal sheaves on an affine open is the supremum of the ideals. -/
private theorem ideal_iSup_apply {ι : Type*} (I : ι → X.IdealSheafData) (W : X.affineOpens) :
    (⨆ i, I i).ideal W = ⨆ i, (I i).ideal W := by
  rw [ideal_iSup, iSup_apply]

/-- If the supports of two ideal sheaves are the complements of disjoint opens, their product is
contained in the nilradical. -/
private theorem mul_le_nilradical_of_support_eq_compl {U V : X.Opens} {I J : X.IdealSheafData}
    (hI : ((I.support : Closeds X) : Set X) = (U : Set X)ᶜ)
    (hJ : ((J.support : Closeds X) : Set X) = (V : Set X)ᶜ) (hUV : Disjoint U V) :
    I * J ≤ X.nilradical := by
  have htop : (⊤ : Closeds X) ≤ (I * J).support := by
    rw [support_mul, ← SetLike.coe_subset_coe, Closeds.coe_sup, hI, hJ, ← Set.compl_inter,
      Set.disjoint_iff_inter_eq_empty.mp (Opens.coe_disjoint.mpr hUV), Set.compl_empty]
    exact Set.subset_univ _
  simpa using le_support_iff_le_vanishingIdeal.mp htop

/-! ### Separating two disjoint quasi-compact opens -/

/-- **Stacks Project, Tag 080P.** Let `X` be a quasi-compact and quasi-separated scheme and let
`U, V` be disjoint quasi-compact open subschemes of `X`. Then there is a `U ∪ V`-admissible
blowup `b : X' ⟶ X` such that `X'` is the disjoint union of two open subschemes `X' = X'₁ ⨿ X'₂`
with `b⁻¹(U) ⊆ X'₁` and `b⁻¹(V) ⊆ X'₂`. -/
@[stacks 080P]
theorem exists_admissibleBlowup_disjoint_open_cover
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    (U V : X.Opens) (hU : IsCompact (U : Set X))
    (hV : IsCompact (V : Set X)) (hUV : Disjoint U V) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X) (U₁ U₂ : X'.Opens),
      IsAdmissibleBlowup (U ⊔ V) b ∧
        Disjoint U₁ U₂ ∧ U₁ ⊔ U₂ = ⊤ ∧
          b ⁻¹ᵁ U ≤ U₁ ∧ b ⁻¹ᵁ V ≤ U₂ := by
  obtain ⟨I, hIft, hIsupp⟩ := AlgebraicGeometry.exists_isFiniteType_support_eq_compl X U hU
  obtain ⟨J, hJft, hJsupp⟩ := AlgebraicGeometry.exists_isFiniteType_support_eq_compl X V hV
  have hIJnil : I * J ≤ X.nilradical :=
    mul_le_nilradical_of_support_eq_compl hIsupp hJsupp hUV
  have hsuppK : (((I ⊔ J).support : Closeds X) : Set X) = ((U ⊔ V : X.Opens) : Set X)ᶜ := by
    rw [support_sup, Closeds.coe_inf, hIsupp, hJsupp, ← Set.compl_union, Opens.coe_sup]
  refine ⟨blowUp (I ⊔ J), blowUpToBase (I ⊔ J), chartsFromIdeal I (I ⊔ J) le_sup_left,
    chartsFromIdeal J (I ⊔ J) le_sup_right,
    isAdmissibleBlowup_blowUpToBase
      ((finitePresentation_subschemeι_iff_isFiniteType _).mpr (hIft.sup hJft))
      (by rw [hsuppK]; exact disjoint_compl_right),
    disjoint_chartsFromIdeal I J (I ⊔ J) le_sup_left le_sup_right hIJnil,
    chartsFromIdeal_sup I J, ?_, ?_⟩
  · exact preimage_le_chartsFromIdeal I (I ⊔ J) le_sup_left U
      (by rw [hIsupp]; exact disjoint_compl_right)
  · exact preimage_le_chartsFromIdeal J (I ⊔ J) le_sup_right V
      (by rw [hJsupp]; exact disjoint_compl_right)

/-! ### Separating finitely many pairwise disjoint quasi-compact opens -/

/-- The chart attached to the zero section of the centre is empty: the degree-one element of the
Rees algebra it cuts out is `0`, and `0` cuts out the empty basic open of `Proj`. -/
private theorem chartOpen_eq_bot_of_eq_zero (ℐ : X.IdealSheafData) (W : X.affineOpens)
    (a : ℐ.ideal W) (ha : (a : Γ(X, W.1)) = 0) : chartOpen ℐ W a = ⊥ := by
  have hz : reesDegOne (ℐ.ideal W) a.2 = 0 := by
    refine Subtype.ext ?_
    show monomial 1 (a : Γ(X, W.1)) = 0
    rw [ha, map_zero]
  rw [chartOpen, hz, Proj.basicOpen_zero]
  exact Opens.ext (by simp)

/-- A section of the centre lying in the sum of the ideal sheaves of a finite subfamily has its
chart covered by the unions of charts attached to the members of that subfamily. The sum is a
sum of finitely many sections, one from each member, and the chart of a sum is covered by the
charts of the summands. -/
private theorem chartOpen_le_iSup_chartsFromIdeal {ι : Type*} (I : ι → X.IdealSheafData)
    (K : X.IdealSheafData) (hIK : ∀ i, I i ≤ K) (W : X.affineOpens) (s : Finset ι) :
    ∀ c : K.ideal W, (c : Γ(X, W.1)) ∈ ⨆ i ∈ s, (I i).ideal W →
      chartOpen K W c ≤ ⨆ i, chartsFromIdeal (I i) K (hIK i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro c hc
    rw [chartOpen_eq_bot_of_eq_zero K W c (by simpa using hc)]
    exact bot_le
  | @insert j s _ ih =>
    intro c hc
    rw [Finset.iSup_insert] at hc
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hc
    have haK : a ∈ K.ideal W := le_def.mp (hIK j) W ha
    have hbK : b ∈ K.ideal W :=
      (iSup_le fun i => iSup_le fun _ => le_def.mp (hIK i) W :
        (⨆ i ∈ s, (I i).ideal W) ≤ K.ideal W) hb
    have hceq : c = (⟨a, haK⟩ : K.ideal W) + ⟨b, hbK⟩ := Subtype.ext hab.symm
    rw [hceq]
    refine le_trans (chartOpen_add_le K W ⟨a, haK⟩ ⟨b, hbK⟩) (sup_le ?_ ?_)
    · exact le_trans (chartOpen_le_chartsFromIdeal (I j) K (hIK j) W ⟨a, ha⟩)
        (le_iSup (fun i => chartsFromIdeal (I i) K (hIK i)) j)
    · exact ih ⟨b, hbK⟩ hb

/-- The charts attached to the members of a finite family of ideal sheaves cover the blowup in
the sum of the family: over an affine open every section of the sum is a finite sum of sections
of the members. -/
private theorem chartsFromIdeal_iSup {ι : Type*} [Finite ι] (I : ι → X.IdealSheafData) :
    ⨆ i, chartsFromIdeal (I i) (⨆ j, I j) (le_iSup I i) = ⊤ := by
  classical
  have : Fintype ι := Fintype.ofFinite ι
  refine top_le_iff.mp fun p _ => ?_
  obtain ⟨W, hW, hpW, -⟩ :=
    exists_isAffineOpen_mem_and_subset (Opens.mem_top (blowUpToBase (⨆ j, I j) p))
  obtain ⟨c, hc⟩ := exists_mem_chartOpen (⨆ j, I j) ⟨W, hW⟩ hpW
  refine chartOpen_le_iSup_chartsFromIdeal I (⨆ j, I j) (le_iSup I) ⟨W, hW⟩ Finset.univ c ?_ hc
  have h2 : (⨆ i, (I i).ideal ⟨W, hW⟩) ≤
      ⨆ i ∈ (Finset.univ : Finset ι), (I i).ideal ⟨W, hW⟩ :=
    iSup_le fun i => le_iSup_of_le i (le_iSup_of_le (Finset.mem_univ i) le_rfl)
  exact h2 (ideal_iSup_apply I ⟨W, hW⟩ ▸ c.2)

/-- **Stacks Project, Tag 080P for a finite family.** Let `X` be a quasi-compact and
quasi-separated scheme and let `U_i`, `i ∈ ι`, be a finite family of pairwise disjoint
quasi-compact open subschemes of `X`. Then there is a `⋃ U_i`-admissible blowup `b : X' ⟶ X`
such that `X'` is the disjoint union of open subschemes `X'_i`, `i ∈ ι`, with
`b⁻¹(U_i) ⊆ X'_i`.

This is the form in which the source iterates Tag 080P: the decomposition of `U` into the
finitely many loci where a locally constant invariant takes a fixed value is separated by a
single blowup. The proof is that of the two-piece case verbatim. Choose quasi-coherent sheaves
of ideals `ℐ_i` of finite type with `X ∖ U_i = V(ℐ_i)` and blow up `∑ ℐ_i`; the piece `X'_i` is
the union of the affine charts of Stacks tag 0804 attached to the sections of `ℐ_i`. Two such
pieces are disjoint because `ℐ_iℐ_j` is contained in the nilradical for `i ≠ j`, and they cover
because over an affine open every section of `(∑ ℐ_i)(W)` is a sum of sections of the
`ℐ_i(W)`. -/
@[stacks 080P "stated for a finite family of pairwise disjoint quasi-compact opens; the \
source's two-piece statement is the case of a two-element index type"]
theorem exists_admissibleBlowup_pairwise_disjoint_open_cover
    (X : Scheme.{u}) [CompactSpace X] [QuasiSeparatedSpace X]
    {ι : Type*} [Finite ι] (U : ι → X.Opens) (hU : ∀ i, IsCompact (U i : Set X))
    (hUd : Pairwise fun i j => Disjoint (U i) (U j)) :
    ∃ (X' : Scheme.{u}) (b : X' ⟶ X) (V : ι → X'.Opens),
      IsAdmissibleBlowup (⨆ i, U i) b ∧
        (Pairwise fun i j => Disjoint (V i) (V j)) ∧ ⨆ i, V i = ⊤ ∧
          ∀ i, b ⁻¹ᵁ U i ≤ V i := by
  classical
  choose I hIft hIsupp using fun i =>
    AlgebraicGeometry.exists_isFiniteType_support_eq_compl X (U i) (hU i)
  have hKft : (⨆ i, I i).IsFiniteType := by
    intro W
    rw [ideal_iSup_apply]
    exact Submodule.fg_iSup _ fun i => hIft i W
  have hsuppK : (((⨆ i, I i).support : Closeds X) : Set X) = ((⨆ i, U i : X.Opens) : Set X)ᶜ := by
    rw [support_iSup, Closeds.coe_iInf, Opens.coe_iSup, Set.compl_iUnion]
    exact Set.iInter_congr fun i => hIsupp i
  have hnil : ∀ i j, i ≠ j → I i * I j ≤ X.nilradical := fun i j hij =>
    mul_le_nilradical_of_support_eq_compl (hIsupp i) (hIsupp j) (hUd hij)
  refine ⟨blowUp (⨆ i, I i), blowUpToBase (⨆ i, I i),
    fun i => chartsFromIdeal (I i) (⨆ j, I j) (le_iSup I i),
    isAdmissibleBlowup_blowUpToBase
      ((finitePresentation_subschemeι_iff_isFiniteType _).mpr hKft)
      (by rw [hsuppK]; exact disjoint_compl_right),
    fun i j hij => disjoint_chartsFromIdeal (I i) (I j) (⨆ k, I k) (le_iSup I i) (le_iSup I j)
      (hnil i j hij),
    chartsFromIdeal_iSup I, fun i => ?_⟩
  exact preimage_le_chartsFromIdeal (I i) (⨆ j, I j) (le_iSup I i) (U i)
    (by rw [hIsupp i]; exact disjoint_compl_right)

end Stacks.Blowup

end
