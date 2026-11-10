module

public import StacksFrontier.AlgebraicGeometry.F6Rank136.ExceptionalCurveContractionReduced
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Contraction.SetTheoreticFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.LocallyPrincipal
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierComplement
public import StacksFrontier.Topology.Dimension.DimensionLEOne
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The classifying morphism is quasi-finite over the exceptional curve

In the Stein case of [Stacks, Tag 0C2L] let `f : X ⟶ Y` contract the exceptional curve `E`
to a closed point `y` whose local ring is regular of dimension two, and let `g : X ⟶ Bl_y Y` be
the morphism to the blowup with `b ∘ g = f`, where `b : Bl_y Y ⟶ Y` is the blowup morphism and
`E' = b⁻¹(y)` its exceptional curve. Over every point `w` of `E'` there is a point at which `g`
is quasi-finite.

## Main results

* `AlgebraicGeometry.specializes_and_isClosed_singleton_of_iso_projectiveLineProj` — on a curve
  presented as `𝐏¹_k`, a point with a proper specialization inside the curve is its generic
  point, and the specialization is a closed point.
* `AlgebraicGeometry.two_le_ringKrullDim_stalk_of_specializes` — a chain of length two of
  generizations bounds the dimension of the local ring from below.
* `AlgebraicGeometry.exists_ne_blowUpToBase_eq_of_ringKrullDim_eq_two` — the exceptional curve of
  the blowup of a point whose local ring has dimension two is not a single point.
* `AlgebraicGeometry.exists_quasiFiniteAt_blowUpClassifying_of_steinSetup` — the classifying
  morphism is quasi-finite at some point over each point of the exceptional curve of the blowup.

## References

* [Stacks Project, Tag 0C2L](https://stacks.math.columbia.edu/tag/0C2L)
* [Stacks Project, Tag 01TH](https://stacks.math.columbia.edu/tag/01TH)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **On a curve presented as the projective line, a proper specialization starts at the generic
point and ends at a closed point.** Let `D` cut out a closed subscheme isomorphic to `𝐏¹_k`, and
let `a ⤳ b` be distinct points of its support. Then `a` specializes to every point of the
support, and `b` is a closed point of `X`. -/
@[ega "II 7.4.3" "special case"]
public theorem specializes_and_isClosed_singleton_of_iso_projectiveLineProj {X : Scheme.{u}}
    (D : X.IdealSheafData) (k : Type u) [Field k] (e : projectiveLineProj k ≅ D.subscheme)
    {a b : X} (ha : a ∈ (D.support : Set X)) (hb : b ∈ (D.support : Set X)) (hab : a ⤳ b)
    (hne : a ≠ b) :
    (∀ z ∈ (D.support : Set X), a ⤳ z) ∧ IsClosed ({b} : Set X) := by
  have : IsIntegral D.subscheme := isIntegral_subscheme_of_iso_projectiveLineProj D k e
  have hdim : topologicalKrullDim D.subscheme ≤ 1 := by
    rw [← IsHomeomorph.topologicalKrullDim_eq _ e.hom.homeomorph.isHomeomorph,
      Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin k (r := 2) two_pos]
    norm_num
  rw [← D.range_subschemeι] at ha hb
  obtain ⟨a', rfl⟩ := ha
  obtain ⟨b', rfl⟩ := hb
  have hι := D.subschemeι.isClosedEmbedding
  have hab' : a' ⤳ b' := hι.isInducing.specializes_iff.mp hab
  have hne' : a' ≠ b' := fun h ↦ hne (h ▸ rfl)
  have hgen : closure ({a'} : Set D.subscheme) = Set.univ := by
    by_contra hne_univ
    have hsub := Stacks.Topology.Dimension.subsingleton_of_isIrreducible_of_ne_univ hdim
      isClosed_closure isIrreducible_singleton.closure hne_univ
    exact hne' (hsub (subset_closure rfl) (specializes_iff_mem_closure.mp hab'))
  have hclosed : IsClosed ({b'} : Set D.subscheme) := by
    refine Stacks.Topology.Dimension.isClosed_singleton_of_mem_of_ne_univ hdim
      (T := closure ({b'} : Set D.subscheme)) isClosed_closure ?_ (subset_closure rfl)
    intro huniv
    have hba : b' ⤳ a' := specializes_iff_mem_closure.mpr (by rw [huniv]; trivial)
    exact hne' (hab'.antisymm hba).eq
  refine ⟨?_, ?_⟩
  · intro z hz
    rw [← D.range_subschemeι] at hz
    obtain ⟨z', rfl⟩ := hz
    exact (specializes_iff_mem_closure.mpr (by rw [hgen]; trivial : z' ∈ _)).map
      D.subschemeι.continuous
  · rw [← Set.image_singleton]
    exact hι.isClosedMap _ hclosed

/-- **A chain of two proper generizations bounds the dimension of the local ring from below.**
If `a ⤳ b ⤳ w` are three distinct points of a scheme, then `dim 𝒪_{X,w} ≥ 2`. -/
public theorem two_le_ringKrullDim_stalk_of_specializes {X : Scheme.{u}} {a b w : X}
    (hab : a ⤳ b) (hbw : b ⤳ w) (hab' : a ≠ b) (hbw' : b ≠ w) :
    2 ≤ ringKrullDim (X.presheaf.stalk w) := by
  have hrange : ∀ z, z ⤳ w → ∃ q, X.fromSpecStalk w q = z := fun z hz ↦ by
    rw [← Set.mem_range, Scheme.range_fromSpecStalk]
    exact hz
  obtain ⟨qa, rfl⟩ := hrange a (hab.trans hbw)
  obtain ⟨qb, rfl⟩ := hrange b hbw
  have hemb := (X.fromSpecStalk w).isEmbedding
  have hqab : @LT.lt (PrimeSpectrum (X.presheaf.stalk w)) _ qa qb := lt_of_le_of_ne
    ((PrimeSpectrum.le_iff_specializes _ _).mpr (hemb.isInducing.specializes_iff.mp hab))
    fun h ↦ hab' (h ▸ rfl)
  have hqb : @LT.lt (PrimeSpectrum (X.presheaf.stalk w)) _ qb
      (IsLocalRing.closedPoint (X.presheaf.stalk w)) := lt_of_le_of_ne
    ((PrimeSpectrum.le_iff_specializes _ _).mpr (IsLocalRing.specializes_closedPoint _))
    fun h ↦ hbw' (by
      rw [show qb = IsLocalRing.closedPoint (X.presheaf.stalk w) from h]
      exact Scheme.fromSpecStalk_closedPoint)
  let p : LTSeries (PrimeSpectrum (X.presheaf.stalk w)) :=
    RelSeries.fromListIsChain [qa, qb, IsLocalRing.closedPoint _] (List.cons_ne_nil _ _)
      (List.IsChain.cons_cons hqab (List.isChain_pair.mpr hqb))
  calc (2 : WithBot ℕ∞) = (p.length : WithBot ℕ∞) := by simp [p]; rfl
    _ ≤ _ := Order.LTSeries.length_le_krullDim p

/-- **The exceptional curve of the blowup of a point of dimension two is not a single point.**
Let `y` be a closed point of a Noetherian scheme `Y` with `dim 𝒪_{Y,y} = 2`, and suppose the
blowup morphism `b` of the reduced point `{y}` is surjective. Then for every point `w` of the
blowup there is a point `w' ≠ w` of the blowup over `y`. -/
public theorem exists_ne_blowUpToBase_eq_of_ringKrullDim_eq_two {Y : Scheme.{u}}
    [IsNoetherian Y] (y : Y) (hy : IsClosed ({y} : Set Y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2)
    (hsurj : Function.Surjective (blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))).base)
    (w : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))) :
    ∃ w' : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)),
      blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) w' = y ∧
        w' ≠ w := by
  set I := Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y) with hI
  have : IsNoetherian (blowUp I) := Stacks.ResolutionOfSurfaces.isNoetherian_blowUp I
  have hsupp : ((exceptionalIdeal I).support : Set (blowUp I)) =
      (blowUpToBase I).base ⁻¹' {y} := by
    rw [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage, hI,
      Scheme.IdealSheafData.coe_support_vanishingIdeal]
    rfl
  obtain ⟨l, hl⟩ : ∃ l : LTSeries (PrimeSpectrum (Y.presheaf.stalk y)), l.length = 2 := by
    apply (Order.le_krullDim_iff (n := 2)).mp
    change ((2 : ℕ) : WithBot ℕ∞) ≤ ringKrullDim (Y.presheaf.stalk y)
    rw [hdim]
    rfl
  have h01 : l 0 < l 1 := l.rel_of_lt (by simp [Fin.lt_def, hl])
  have h1c : l 1 < IsLocalRing.closedPoint (Y.presheaf.stalk y) :=
    lt_of_lt_of_le (l.rel_of_lt (show (1 : Fin (l.length + 1)) < Fin.last _ by
      simp [Fin.lt_def, hl]))
      ((PrimeSpectrum.le_iff_specializes _ _).mpr (IsLocalRing.specializes_closedPoint _))
  have hinj := (Y.fromSpecStalk y).isEmbedding.injective
  have hcont := (Y.fromSpecStalk y).continuous
  have key : ∀ q q' : PrimeSpectrum (Y.presheaf.stalk y), q < q' →
      Y.fromSpecStalk y q ⤳ Y.fromSpecStalk y q' ∧ Y.fromSpecStalk y q ≠ Y.fromSpecStalk y q' :=
    fun q q' h ↦ ⟨((PrimeSpectrum.le_iff_specializes _ _).mp h.le).map hcont,
      fun h' ↦ h.ne (hinj h')⟩
  obtain ⟨hy01, hy01'⟩ := key _ _ h01
  obtain ⟨hy1, hy1'⟩ := key _ _ h1c
  rw [Scheme.fromSpecStalk_closedPoint] at hy1 hy1'
  set y₀ := Y.fromSpecStalk y (l 0)
  set y₁ := Y.fromSpecStalk y (l 1)
  have hspec := (blowUpToBase I).isClosedMap.specializingMap
  obtain ⟨w₀, hw₀⟩ := hsurj y₀
  obtain ⟨w₁, hw01, hw₁⟩ := hspec (show (blowUpToBase I) w₀ ⤳ y₁ from hw₀ ▸ hy01)
  obtain ⟨w₂, hw12, hw₂⟩ := hspec (show (blowUpToBase I) w₁ ⤳ y from hw₁ ▸ hy1)
  have h2 : 2 ≤ ringKrullDim ((blowUp I).presheaf.stalk w₂) :=
    two_le_ringKrullDim_stalk_of_specializes hw01 hw12
      (fun h ↦ hy01' (hw₀.symm.trans ((congrArg _ h).trans hw₁)))
      (fun h ↦ hy1' (hw₁.symm.trans ((congrArg _ h).trans hw₂)))
  by_contra H
  push Not at H
  have hw₂E : w₂ ∈ ((exceptionalIdeal I).support : Set (blowUp I)) := hsupp ▸ hw₂
  have h1 : ringKrullDim ((blowUp I).presheaf.stalk w₂) ≤ 1 :=
    Stacks.Divisors.ringKrullDim_stalk_le_one_of_isLocallyPrincipal
      (Stacks.Divisors.isLocallyPrincipal_of_isEffectiveCartierDivisor _
        (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _)) hw₂E
      fun z hz _ ↦ by
        rw [hsupp] at hz
        exact (H z hz).trans (H w₂ hw₂).symm
  exact absurd (h2.trans h1) (by decide)

/-- **The classifying morphism is quasi-finite over the exceptional curve**, with the centre of
the blowup named. This is
`AlgebraicGeometry.exists_quasiFiniteAt_blowUpClassifying_of_steinSetup` for an ideal sheaf `I`
equal to the vanishing ideal of `{y}`. -/
public theorem exists_quasiFiniteAt_blowUpClassifying_of_steinSetup_of_eq {X Y : Scheme.{u}}
    {D : X.IdealSheafData} {k : Type u} [Field k] (e : projectiveLineProj k ≅ D.subscheme)
    (f : X ⟶ Y) (y : Y) (hsetup : D.IsSteinContractionSetup f y)
    (hy : IsClosed ({y} : Set Y)) (hdim : ringKrullDim (Y.presheaf.stalk y) = 2)
    (I : Y.IdealSheafData)
    (hI : I = Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y))
    (g : X ⟶ blowUp I) (hg : g ≫ blowUpToBase I = f) (w : blowUp I)
    (hw : blowUpToBase I w = y) :
    ∃ x : X, g.base x = w ∧ g.QuasiFiniteAt x := by
  have := hsetup.isNoetherian
  have := hsetup.isProper
  have := hsetup.isIso_c
  have := hsetup.geometricallyConnected
  have : IsProper g := isProper_of_isProper_of_isSeparated g (blowUpToBase I) f hg
  have hsupp : ∀ x ∈ (D.support : Set X), f.base x = y :=
    (D.forall_subschemeι_base_eq_iff_forall_mem_support f y).1 hsetup.base_eq
  have hbg : ∀ x : X, blowUpToBase I (g x) = f x := fun x ↦ by rw [← hg]; rfl
  obtain ⟨W, hWc⟩ : ∃ W : Y.Opens, (W : Set Y) = ({y} : Set Y)ᶜ :=
    ⟨⟨{y}ᶜ, hy.isOpen_compl⟩, rfl⟩
  have hiso : IsIso (g ∣_ (blowUpToBase I ⁻¹ᵁ W)) := by
    subst hI
    exact isIso_morphismRestrict_blowUpClassifying (D := D) f y hy hsupp
      hsetup.quasiFinite_of_notMem g hg W hWc
  have hrange : ((blowUpToBase I ⁻¹ᵁ W : (blowUp I).Opens) : Set (blowUp I)) ⊆
      Set.range g.base := by
    intro v hv
    obtain ⟨x', hx'⟩ := (Scheme.homeoOfIso (asIso (g ∣_ (blowUpToBase I ⁻¹ᵁ W)))).surjective
      ⟨v, hv⟩
    exact ⟨x'.1, (morphismRestrict_base_coe g _ x').symm.trans (congrArg Subtype.val hx')⟩
  have hgenW : genericPoints (blowUp I) ⊆
      ((blowUpToBase I ⁻¹ᵁ W : (blowUp I).Opens) : Set (blowUp I)) := fun v hv ↦ by
    have hv' : blowUpToBase I v ≠ y :=
      base_ne_of_mem_genericPoints_of_isEffectiveCartierDivisor_comap _ _
        (Stacks.Blowup.isEffectiveCartierDivisor_exceptionalIdeal _) y
        (hI ▸ supportSet_vanishingIdeal_singleton hy) hv
    change blowUpToBase I v ∈ (W : Set Y)
    rw [hWc]
    exact hv'
  have hgsurj : Function.Surjective g.base := by
    intro v
    have hv : v ∈ closure (genericPoints (blowUp I)) := by
      rw [genericPoints.closure]
      trivial
    exact closure_minimal (hgenW.trans hrange) g.isClosedMap.isClosed_range hv
  have hfib : ∀ x : X, blowUpToBase I (g x) = y → x ∈ (D.support : Set X) := fun x hx ↦
    preimage_singleton_subset_support_of_steinSetup e f y hsetup
      (show f x = y from (hbg x).symm.trans hx)
  have hbsurj : Function.Surjective (blowUpToBase I).base := fun z ↦ by
    obtain ⟨x, rfl⟩ := f.surjective z
    exact ⟨g x, hbg x⟩
  have hP : ∀ a b : X, g a = w → g b = w → a ⤳ b → a = b := by
    intro a b ha hb hab
    by_contra hne
    have haE := hfib a (by rw [ha]; exact hw)
    have hbE := hfib b (by rw [hb]; exact hw)
    obtain ⟨hgen, hcl⟩ :=
      specializes_and_isClosed_singleton_of_iso_projectiveLineProj D k e haE hbE hab hne
    have hwcl : IsClosed ({w} : Set (blowUp I)) := by
      rw [← hb, ← Set.image_singleton]
      exact g.isClosedMap _ hcl
    obtain ⟨w', hw', hne'⟩ : ∃ w' : blowUp I, blowUpToBase I w' = y ∧ w' ≠ w := by
      subst hI
      exact exists_ne_blowUpToBase_eq_of_ringKrullDim_eq_two y hy hdim hbsurj w
    obtain ⟨x', rfl⟩ := hgsurj w'
    have hsp : g a ⤳ g x' := (hgen x' (hfib x' hw')).map g.continuous
    rw [ha, specializes_iff_mem_closure, hwcl.closure_eq] at hsp
    exact hne' hsp
  obtain ⟨x, hx⟩ := hgsurj w
  refine ⟨x, hx, ?_⟩
  have hι : ∀ p : g.fiber (g x), g (g.fiberι (g x) p) = w := fun p ↦ by
    have : g.fiberι (g x) p ∈ Set.range (g.fiberι (g x)) := ⟨p, rfl⟩
    rw [Scheme.Hom.range_fiberι] at this
    exact this.trans hx
  have hinj : Function.Injective (g.fiberι (g x)) := fun p q h ↦
    (g.fiberHomeo (g x)).injective (Subtype.ext (by
      rw [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberHomeo_apply]
      exact h))
  have key : ∀ p q : g.fiber (g x), p ⤳ q → p = q := fun p q hpq ↦
    hinj (hP _ _ (hι p) (hι q) (hpq.map (g.fiberι (g x)).continuous))
  have hqf : quasiFiniteAt g x := by
    refine ((quasiFiniteAt_tfae g x).out 1 3).mpr (And.intro ?_ ?_)
    · exact closure_subset_iff_isClosed.mp fun q hq ↦
        (key _ _ (specializes_iff_mem_closure.mpr hq)).symm
    · rintro ⟨x', hne, hsp⟩
      exact hne (key _ _ hsp)
  exact hqf.2

/-- **The classifying morphism is quasi-finite over the exceptional curve.** In the Stein case
of [Stacks, Tag 0C2L], with `𝒪_{Y,y}` of dimension two, the morphism `g : X ⟶ Bl_y Y` over `f`
is quasi-finite at some point over each point of the exceptional curve of the blowup. -/
public theorem exists_quasiFiniteAt_blowUpClassifying_of_steinSetup {X Y : Scheme.{u}}
    {D : X.IdealSheafData} {k : Type u} [Field k] (e : projectiveLineProj k ≅ D.subscheme)
    (f : X ⟶ Y) (y : Y) (hsetup : D.IsSteinContractionSetup f y)
    (hy : IsClosed ({y} : Set Y))
    (hdim : ringKrullDim (Y.presheaf.stalk y) = 2)
    (g : X ⟶ AlgebraicGeometry.blowUp
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)))
    (hg : g ≫ AlgebraicGeometry.blowUpToBase
      (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) = f) :
    ∀ w : AlgebraicGeometry.blowUp
        (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)),
      AlgebraicGeometry.blowUpToBase
          (Scheme.IdealSheafData.vanishingIdeal (⟨{y}, hy⟩ : Closeds Y)) w = y →
        ∃ x : X, g.base x = w ∧ g.QuasiFiniteAt x :=
  fun w hw ↦ exists_quasiFiniteAt_blowUpClassifying_of_steinSetup_of_eq e f y hsetup hy hdim _
    rfl g hg w hw

end AlgebraicGeometry

end
