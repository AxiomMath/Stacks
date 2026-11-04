module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleTopos
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SiteAxioms

/-!
# Independence of the small étale topos from the choice of big site

The small étale site of a scheme `S` is cut out of a chosen big étale site containing `S`, so a
priori both the site and its topos depend on that choice. They do not: the comparison functor
from the chosen small étale site to Mathlib's choice-free small étale category of `S` is a dense
subsite inclusion, so the two have the same sheaves. Two choices of big étale site therefore
give canonically equivalent small étale topoi, and the equivalences are coherent when a third
choice is introduced.

## Main definitions

* `AlgebraicGeometry.smallEtaleToCommonEtale` is the comparison functor to the choice-free small
  étale category of `S`.
* `AlgebraicGeometry.smallEtaleToCommonToposEquiv` is the resulting equivalence of topoi.
* `AlgebraicGeometry.smallEtaleToposEquiv` is the canonical equivalence between the small étale
  topoi of two choices of big étale site.

## Main results

* `AlgebraicGeometry.smallEtaleToCommonEtale_isDenseSubsite`: the chosen small étale site is a
  dense subsite of the common one.
* `AlgebraicGeometry.smallEtaleToposEquiv_sections` identifies the restriction of the canonical
  equivalence to affine étale objects represented in both sites, naturally in the sheaf, and
  `AlgebraicGeometry.smallEtaleToposEquiv_sections_natural` makes that identification compatible
  with morphisms of such objects.
* `AlgebraicGeometry.smallEtaleToposEquiv_refl` identifies the self-comparison with the identity
  functor, and `AlgebraicGeometry.smallEtaleToposEquiv_trans` identifies a composite comparison
  with the direct one.

## Implementation notes

Density is proved from its two halves separately: cover-density, because every étale scheme over
`S` is covered by affine opens whose size is bounded by that of `S`, and cocontinuity, because an
étale covering formed in the ambient category of schemes is refined by one internal to the site.
The sheaf-value universe is at least the successor of the scheme universe, so that it contains
the matching-family sets of the small étale sites.

## References

* [Stacks Project, Tag 0958](https://stacks.math.columbia.edu/tag/0958)
-/

@[expose] public noncomputable section

open CategoryTheory Cardinal

universe u v

namespace AlgebraicGeometry

/-- An affine scheme locally of finite type over a scheme of a big étale site is itself below
that site's cardinal cutoff. -/
private theorem affine_locallyOfFiniteType_size_lt
    (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) {T : Scheme.{u}} [IsAffine T]
    (f : T ⟶ S) [LocallyOfFiniteType f] : T.size < B.cutoff := by
  let V : PUnit → T.affineOpens := fun _ => ⟨⊤, isAffineOpen_top _⟩
  have hcov : ⨆ i, (V i).1 = ⊤ := by simp [V]
  have hI : Cardinal.mk PUnit ≤ S.size ^ ℵ₀ := by
    calc
      Cardinal.mk PUnit = 1 := by simp
      _ ≤ S.size := one_le_aleph0.trans (Scheme.aleph0_le_size S)
      _ ≤ S.size ^ ℵ₀ := Cardinal.self_le_power _ one_le_aleph0
  exact Scheme.size_lt_of_locallyOfFiniteType_of_affineCover
    B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit f V hcov hI hS

/-- An étale scheme over `S` whose size is below the cutoff, read as an object of the small
étale site of `S`. -/
private noncomputable def smallEtaleObject
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : Scheme.{u}) (hT : T.size < B.cutoff) (f : T ⟶ S)
    [Etale f] : SmallEtale B S hS := by
  let T₀ := B.obj T hT
  let g : T₀ ⟶ B.obj S hS := B.inclusion.preimage (show
    B.inclusion.obj T₀ ⟶ B.inclusion.obj (B.obj S hS) from f)
  let O : BigEtaleOver B S hS := Over.mk g
  refine ⟨O, ?_⟩
  change Etale (B.inclusion.map g)
  rw [Functor.map_preimage]
  infer_instance

/-- The canonical functor from the small étale site of `S` cut out by a big étale site to
Mathlib's small étale category of `S`, which is independent of that choice. -/
public def smallEtaleToCommonEtale
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    SmallEtale B S hS ⥤ S.Etale where
  obj X := MorphismProperty.Over.mk (P := @Etale) (Q := ⊤)
    (B.inclusion.map X.obj.hom) X.property
  map {X Y} f := MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤)
    ((SmallEtale.toScheme B S hS).map f) (by
      change B.inclusion.map f.hom.left ≫ B.inclusion.map Y.obj.hom =
        B.inclusion.map X.obj.hom
      rw [← B.inclusion.map_comp]
      exact congrArg B.inclusion.map f.hom.w)
  map_id X := by apply MorphismProperty.Over.Hom.ext; rfl
  map_comp f g := by apply MorphismProperty.Over.Hom.ext; rfl

/-- The comparison functor to the common small étale category is full: a morphism over `S` of
the underlying schemes lies in the chosen site because that site is a full subcategory. -/
local instance smallEtaleToCommonEtale_full
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (smallEtaleToCommonEtale B S hS).Full where
  map_surjective := by
    intro X Y f
    let g : X.obj.left ⟶ Y.obj.left := B.inclusion.preimage f.left
    have hg : B.inclusion.map (g ≫ Y.obj.hom) = B.inclusion.map X.obj.hom := by
      rw [Functor.map_comp,
        show B.inclusion.map g = f.left from B.inclusion.map_preimage f.left]
      exact MorphismProperty.Over.w f
    let f₀ : X.obj ⟶ Y.obj := Over.homMk g (B.inclusion.map_injective hg)
    let f₁ : X ⟶ Y := ObjectProperty.homMk f₀
    refine ⟨f₁, ?_⟩
    apply MorphismProperty.Over.Hom.ext
    change B.inclusion.map g = f.left
    exact B.inclusion.map_preimage f.left

/-- The comparison functor to the common small étale category is faithful. -/
local instance smallEtaleToCommonEtale_faithful
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (smallEtaleToCommonEtale B S hS).Faithful where
  map_injective h := (SmallEtale.toScheme B S hS).map_injective (congrArg (·.left) h)

/-- The comparison functor is cover-dense: every étale scheme over `S` is covered by affine
opens, and those are small enough to belong to the chosen site. -/
local instance smallEtaleToCommonEtale_coverDense
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (smallEtaleToCommonEtale B S hS).IsCoverDense (S.smallEtaleTopology) where
  is_cover U := by
    let 𝒜 := U.left.affineCover
    let G := smallEtaleToCommonEtale B S hS
    have hsmall (i : 𝒜.I₀) : (𝒜.X i).size < B.cutoff :=
      affine_locallyOfFiniteType_size_lt B S hS (𝒜.f i ≫ U.hom)
    let A (i : 𝒜.I₀) := smallEtaleObject B S hS (𝒜.X i) (hsmall i)
      (𝒜.f i ≫ U.hom)
    let q (i : 𝒜.I₀) : G.obj (A i) ⟶ U :=
      MorphismProperty.Over.homMk (P := @Etale) (Q := ⊤) (𝒜.f i) (by
        change 𝒜.f i ≫ U.hom =
          B.inclusion.map (B.inclusion.preimage (show
            B.inclusion.obj (B.obj (𝒜.X i) (hsmall i)) ⟶
            B.inclusion.obj (B.obj S hS) from 𝒜.f i ≫ U.hom))
        rw [B.inclusion.map_preimage])
    have hgen : Sieve.generate (Presieve.ofArrows (fun i => G.obj (A i)) q) ∈
        S.smallEtaleTopology U := by
      apply (Scheme.ofArrows_mem_smallEtaleTopology_iff q).2
      change (⋃ i, Set.range (𝒜.f i)) = Set.univ
      ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨𝒜.idx x, 𝒜.covers x⟩
    apply S.smallEtaleTopology.superset_covering ?_ hgen
    rw [Sieve.generate_le_iff]
    rintro Y f ⟨i⟩
    exact Presieve.in_coverByImage G (q i)

universe w w' wH

/-- The precoverage presented by a class of covering families. -/
def sitePrecoverage {C : Type w} [Category.{w'} C]
    (IsCov : Covering.{w, w', wH} C → Prop) : Precoverage C where
  coverings X := {R | ∃ E : PreZeroHypercover.{wH} X,
    R = E.presieve₀ ∧ IsCov ⟨X, E⟩}

/-- A sieve in the topology generated by a class of covering families satisfying the site
axioms contains a covering family of that class. -/
lemma exists_siteCovering_refining_sieve
    {C : Type w} [Category.{w'} C]
    {IsCov : Covering.{w, w', wH} C → Prop}
    (hsite : IsSite IsCov) {X : C} {S : Sieve X}
    (hS : (sitePrecoverage IsCov).Saturate X S) :
    ∃ E : PreZeroHypercover.{wH} X,
      IsCov ⟨X, E⟩ ∧ E.sieve₀ ≤ S := by
  induction hS with
  | of X R hR =>
      obtain ⟨E, rfl, hE⟩ := hR
      exact ⟨E, hE, le_rfl⟩
  | top X =>
      refine ⟨PreZeroHypercover.singleton (𝟙 X), hsite.1 (𝟙 X), ?_⟩
      simp
  | pullback X S hS Y f ih =>
      obtain ⟨E, hE, hES⟩ := ih
      obtain ⟨P, π₁, π₂, hpull, hP⟩ := hsite.2.2 ⟨X, E⟩ hE Y f
      let E' : PreZeroHypercover Y := ⟨E.I₀, P, π₂⟩
      refine ⟨E', hP, ?_⟩
      rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      intro i
      have hmem : S (π₁ i ≫ E.f i) :=
        S.downward_closed (hES _ (Sieve.ofArrows_mk E.X E.f i)) (π₁ i)
      show S (π₂ i ≫ f)
      rwa [(hpull i).w] at hmem
  | transitive X S R hS hlocal ihS ihlocal =>
      obtain ⟨E, hE, hES⟩ := ihS
      have hloc (i : E.I₀) :
          ∃ F : PreZeroHypercover (E.X i),
            IsCov ⟨E.X i, F⟩ ∧ F.sieve₀ ≤ R.pullback (E.f i) := by
        apply ihlocal
        exact hES _ (Sieve.ofArrows_mk E.X E.f i)
      choose F hF hFR using hloc
      have hEF : IsCov ⟨X, E.bind F⟩ := by
        simpa [PreZeroHypercover.pushforward] using hsite.2.1 ⟨X, E⟩ hE
          (fun i => ⟨E.X i, F i⟩) hF (fun _ => rfl)
      refine ⟨E.bind F, hEF, ?_⟩
      rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
      rintro ⟨i, j⟩
      exact hFR i ((F i).f j) (Sieve.ofArrows_mk (F i).X (F i).f j)

/-- The comparison functor carries covering sieves of the chosen small étale site to covering
sieves of the common one. -/
private theorem smallEtaleToCommonEtale_coverPreserving
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    CoverPreserving (SmallEtale.topology B S hS)
      (Scheme.smallEtaleTopology S) (smallEtaleToCommonEtale B S hS) := by
  let G := smallEtaleToCommonEtale B S hS
  let K := Scheme.smallEtaleTopology S
  refine ⟨fun {U R} hR => ?_⟩
  have hsat : (sitePrecoverage (SmallEtale.IsCovering B S hS)).Saturate U R := hR
  obtain ⟨E, hE, hER⟩ := exists_siteCovering_refining_sieve (SmallEtale.isSite B S hS) hsat
  have hBig : B.IsCovering ⟨U.obj.left,
      E.map (SmallEtale.inclusion B S hS ⋙
        BigEtaleOver.forget B S hS)⟩ := hE
  have hEtale := hBig.etale
  change ((E.map (SmallEtale.inclusion B S hS ⋙
    BigEtaleOver.forget B S hS)).map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj U.obj.left) at hEtale
  have hEtale' : (E.map (SmallEtale.toScheme B S hS)).presieve₀ ∈
      Scheme.etalePrecoverage ((SmallEtale.toScheme B S hS).obj U) := by
    simpa [SmallEtale.toScheme, BigEtaleOver.toScheme, PreZeroHypercover.map] using hEtale
  have hpoints := (Scheme.presieve₀_mem_precoverage_iff
    (E.map (SmallEtale.toScheme B S hS))).mp hEtale' |>.1
  have hcover : Sieve.ofArrows (fun i => G.obj (E.X i))
      (fun i => G.map (E.f i)) ∈ K (G.obj U) := by
    apply (Scheme.ofArrows_mem_smallEtaleTopology_iff
      (f := fun i => G.map (E.f i))).2
    ext x
    simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
    obtain ⟨i, y, hy⟩ := hpoints x
    exact ⟨i, y, hy⟩
  refine K.superset_covering (Sieve.functorPushforward_monotone G U hER) ?_
  simpa only [PreZeroHypercover.sieve₀, Sieve.functorPushforward_ofArrows] using hcover

/-- The comparison functor is cocontinuous: a covering sieve of the common small étale
category is refined by the image of one internal to the chosen site. -/
private theorem smallEtaleToCommonEtale_isCocontinuous
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (smallEtaleToCommonEtale B S hS).IsCocontinuous
      (SmallEtale.topology B S hS) (Scheme.smallEtaleTopology S) := by
  classical
  let G := smallEtaleToCommonEtale B S hS
  let J := SmallEtale.topology B S hS
  let : MorphismProperty.RespectsIso (@Etale : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine ⟨?_⟩
  intro U T hT
  change T ∈ S.smallGrothendieckTopology (@Etale) (G.obj U) at hT
  dsimp only [G] at hT
  obtain ⟨𝒰, h𝒰over, h𝒰et, h𝒰T⟩ :=
    (Scheme.mem_smallGrothendieckTopology
      (P := (@Etale : MorphismProperty Scheme.{u})) (S := S)
      (X := (smallEtaleToCommonEtale B S hS).obj U) T).mp hT
  let : Category.{u, u + 1}
      (MorphismProperty.Over (@Etale : MorphismProperty Scheme.{u}) ⊤ S) :=
    (inferInstance : Category.{u, u + 1} S.Etale)
  let (i : 𝒰.I₀) : (𝒰.X i).Over S := h𝒰over.over i
  let (i : 𝒰.I₀) : (𝒰.f i).IsOver S := h𝒰over.isOver_map i
  have hGU : (G.obj U).left = B.inclusion.obj U.obj.left := rfl
  cases hGU
  have h𝒰cov : 𝒰.presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj U.obj.left) :=
    𝒰.mem₀
  let 𝒰' : PreZeroHypercover.{u + 1} (B.inclusion.obj U.obj.left) := {
    I₀ := ULift.{u + 1, u} 𝒰.I₀
    X i := 𝒰.X i.down
    f i := 𝒰.f i.down
  }
  have h𝒰'cov : 𝒰'.presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj U.obj.left) := by
    have hp := (Scheme.presieve₀_mem_precoverage_iff 𝒰.toPreZeroHypercover).mp h𝒰cov
    refine (Scheme.presieve₀_mem_precoverage_iff 𝒰').2 ⟨fun x => ?_, fun i => hp.2 i.down⟩
    obtain ⟨i, y, hy⟩ := hp.1 x
    exact ⟨⟨i⟩, y, hy⟩
  obtain ⟨E, hE, ⟨r⟩⟩ :=
    BigEtaleSite.exists_covering_refining_etale_cover B 𝒰' h𝒰'cov
  have hEtale : (E.map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj U.obj.left) := hE.1
  have hEprops := (Scheme.presieve₀_mem_precoverage_iff (E.map B.inclusion)).mp hEtale
  let F : PreZeroHypercover U := {
    I₀ := E.I₀
    X j := {
      obj := Over.mk (E.f j ≫ U.obj.hom)
      property := by
        show Etale (B.inclusion.map (E.f j ≫ U.obj.hom))
        rw [Functor.map_comp]
        let : Etale (B.inclusion.map (E.f j)) := hEprops.2 j
        infer_instance
    }
    f j := ObjectProperty.homMk (Over.homMk (E.f j) (by simp))
  }
  have hFcover : SmallEtale.IsCovering B S hS ⟨U, F⟩ := by
    show B.IsCovering ⟨U.obj.left,
      F.map (SmallEtale.inclusion B S hS ⋙
        BigEtaleOver.forget B S hS)⟩
    simpa [F, SmallEtale.inclusion, BigEtaleOver.forget, PreZeroHypercover.map] using hE
  have hFpre : F.presieve₀ ∈ SmallEtale.precoverage B S hS U :=
    (SmallEtale.mem_precoverage_iff B S hS).2 ⟨F, rfl, hFcover⟩
  have hFmem : F.sieve₀ ∈ J U := by
    simpa [J, SmallEtale.topology] using
      (Precoverage.generate_mem_toGrothendieck hFpre)
  have hFle : F.sieve₀ ≤ T.functorPullback G := by
    rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
    intro j
    let i := (r.s₀ j).down
    let Wi : S.Etale := by
      let : Etale (𝒰.X i ↘ S) := h𝒰et i
      exact Scheme.Etale.mk (𝒰.X i ↘ S)
    let β : Wi ⟶ G.obj U := by
      let : (𝒰.f i).IsOver S := h𝒰over.isOver_map i
      exact (𝒰.f i).asOverProp S (hX := h𝒰et i) (hY := (G.obj U).prop)
    have hβ : T β := by
      apply h𝒰T
      show Presieve.ofArrows
        (fun k => (𝒰.X k).asOverProp (P := (@Etale : MorphismProperty Scheme.{u}))
          S (h𝒰et k))
        (fun k => (𝒰.f k).asOverProp (P := (@Etale : MorphismProperty Scheme.{u})) S) β
      exact Presieve.ofArrows.mk i
    have hr : r.h₀ j ≫ 𝒰.f i = B.inclusion.map (E.f j) := by
      show r.h₀ j ≫ 𝒰'.f (r.s₀ j) = (E.map B.inclusion).f j
      exact r.w₀ j
    let δ : G.obj (F.X j) ⟶ Wi := MorphismProperty.Over.homMk (r.h₀ j) (by
      show r.h₀ j ≫ (𝒰.X i ↘ S) =
        B.inclusion.map (E.f j ≫ U.obj.hom)
      rw [← (h𝒰over.isOver_map i).comp_over, ← Category.assoc, hr]
      show B.inclusion.map (E.f j) ≫ B.inclusion.map U.obj.hom =
        B.inclusion.map (E.f j ≫ U.obj.hom)
      exact (Functor.map_comp B.inclusion _ _).symm)
    have hfac : G.map (F.f j) = δ ≫ β := by
      apply MorphismProperty.Over.Hom.ext
      show B.inclusion.map (E.f j) = r.h₀ j ≫ 𝒰.f i
      exact hr.symm
    show T (G.map (F.f j))
    rw [hfac]
    exact T.downward_closed hβ δ
  exact J.superset_covering hFle hFmem

/-- The chosen small étale site is a dense subsite of the common small étale category of `S`,
so the two have the same sheaves. -/
public theorem smallEtaleToCommonEtale_isDenseSubsite
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (smallEtaleToCommonEtale B S hS).IsDenseSubsite
      (SmallEtale.topology B S hS) S.smallEtaleTopology := by
  let G := smallEtaleToCommonEtale B S hS
  let J := SmallEtale.topology B S hS
  let K := S.smallEtaleTopology
  let : G.Full := smallEtaleToCommonEtale_full B S hS
  let : G.Faithful := smallEtaleToCommonEtale_faithful B S hS
  let : G.IsCoverDense K := smallEtaleToCommonEtale_coverDense B S hS
  let : G.IsCocontinuous J K := smallEtaleToCommonEtale_isCocontinuous B S hS
  refine {
    isCoverDense' := inferInstance
    isLocallyFull' := inferInstance
    isLocallyFaithful' := inferInstance
    functorPushforward_mem_iff := ?_ }
  intro X R
  refine ⟨fun h => ?_, (smallEtaleToCommonEtale_coverPreserving B S hS).cover_preserve⟩
  have hpull : (R.functorPushforward G).functorPullback G ∈ J X := G.cover_lift J K h
  rwa [Sieve.functorPullback_functorPushforward_eq] at hpull

/-- The small étale topos cut out by a big étale site is equivalent to the category of sheaves
on Mathlib's small étale category of `S`. -/
public noncomputable def smallEtaleToCommonToposEquiv
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    smallEtaleTopos.{u, max (u + 1) v} B S hS ≌
      Sheaf S.smallEtaleTopology (Type (max (u + 1) v)) := by
  letI : (smallEtaleToCommonEtale B S hS).IsDenseSubsite
      (SmallEtale.topology B S hS) S.smallEtaleTopology := by
    exact smallEtaleToCommonEtale_isDenseSubsite B S hS
  exact Functor.IsDenseSubsite.sheafEquiv _ _ (smallEtaleToCommonEtale B S hS) _

/-- The canonical equivalence between the small étale topoi obtained from two
big étale sites containing the same scheme. -/
@[stacks 0958 "equivalence of small étale topoi"]
public noncomputable def smallEtaleToposEquiv
    (B₁ B₂ : BigEtaleSite.{u}) (S : Scheme.{u})
    (h₁ : B₁.Contains S) (h₂ : B₂.Contains S) :
    smallEtaleTopos.{u, max (u + 1) v} B₁ S h₁ ≌
      smallEtaleTopos.{u, max (u + 1) v} B₂ S h₂ := by
  exact (smallEtaleToCommonToposEquiv B₁ S h₁).trans
    (smallEtaleToCommonToposEquiv B₂ S h₂).symm

/-- On affine étale objects represented in both small sites, the comparison
equivalence agrees with restriction along their identification over `S`. This
is a natural isomorphism of evaluation functors, hence is natural in the sheaf. -/
@[stacks 0958 "comparison on common affine étale objects"]
public noncomputable def smallEtaleToposEquiv_sections
    (B₁ B₂ : BigEtaleSite.{u}) (S : Scheme.{u})
    (h₁ : B₁.Contains S) (h₂ : B₂.Contains S)
    (X₁ : SmallAffineEtale B₁ S h₁)
    (X₂ : SmallAffineEtale B₂ S h₂)
    (e : (Over.post B₁.inclusion).obj X₁.obj.obj ≅
      (Over.post B₂.inclusion).obj X₂.obj.obj) :
    (smallEtaleToposEquiv.{u, v} B₁ B₂ S h₁ h₂).functor ⋙
        (sheafSections (SmallEtale.topology B₂ S h₂)
          (Type (max (u + 1) v))).obj
          (Opposite.op X₂.obj) ≅
      (sheafSections (SmallEtale.topology B₁ S h₁)
        (Type (max (u + 1) v))).obj
        (Opposite.op X₁.obj) := by
  let E₁ := smallEtaleToCommonToposEquiv B₁ S h₁
  let e' : (smallEtaleToCommonEtale B₁ S h₁).obj X₁.obj ≅
      (smallEtaleToCommonEtale B₂ S h₂).obj X₂.obj :=
    (Scheme.Etale.forget S).preimageIso e
  exact Functor.isoWhiskerLeft E₁.functor
      ((sheafSections S.smallEtaleTopology (Type (max (u + 1) v))).mapIso e'.op) ≪≫
    Functor.isoWhiskerRight E₁.unitIso.symm
      ((sheafSections (SmallEtale.topology B₁ S h₁) (Type (max (u + 1) v))).obj
        (Opposite.op X₁.obj))

/-- The section comparison commutes with restrictions along a morphism of
common affine étale objects. -/
@[stacks 0958 "naturality on common affine étale objects"]
public theorem smallEtaleToposEquiv_sections_natural
    (B₁ B₂ : BigEtaleSite.{u}) (S : Scheme.{u})
    (h₁ : B₁.Contains S) (h₂ : B₂.Contains S)
    (X₁ Y₁ : SmallAffineEtale B₁ S h₁)
    (X₂ Y₂ : SmallAffineEtale B₂ S h₂)
    (eX : (Over.post B₁.inclusion).obj X₁.obj.obj ≅
      (Over.post B₂.inclusion).obj X₂.obj.obj)
    (eY : (Over.post B₁.inclusion).obj Y₁.obj.obj ≅
      (Over.post B₂.inclusion).obj Y₂.obj.obj)
    (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (hf : (Over.post B₁.inclusion).map
        ((SmallEtale.inclusion B₁ S h₁).map
          ((SmallAffineEtale.inclusion B₁ S h₁).map f₁)) ≫ eY.hom =
      eX.hom ≫ (Over.post B₂.inclusion).map
        ((SmallEtale.inclusion B₂ S h₂).map
          ((SmallAffineEtale.inclusion B₂ S h₂).map f₂)))
    (F : smallEtaleTopos.{u, max (u + 1) v} B₁ S h₁) :
    (smallEtaleToposEquiv_sections.{u, v} B₁ B₂ S h₁ h₂ Y₁ Y₂ eY).hom.app F ≫
        ((sheafSections (SmallEtale.topology B₁ S h₁)
          (Type (max (u + 1) v))).map
          (Opposite.op ((SmallAffineEtale.inclusion B₁ S h₁).map f₁))).app F =
      ((sheafSections (SmallEtale.topology B₂ S h₂)
        (Type (max (u + 1) v))).map
          (Opposite.op ((SmallAffineEtale.inclusion B₂ S h₂).map f₂))).app
            ((smallEtaleToposEquiv.{u, v} B₁ B₂ S h₁ h₂).functor.obj F) ≫
        (smallEtaleToposEquiv_sections.{u, v} B₁ B₂ S h₁ h₂ X₁ X₂ eX).hom.app F := by
  let E₁ := smallEtaleToCommonToposEquiv.{u, v} B₁ S h₁
  let G₁ := smallEtaleToCommonEtale B₁ S h₁
  let G₂ := smallEtaleToCommonEtale B₂ S h₂
  let eX' : G₁.obj X₁.obj ≅ G₂.obj X₂.obj :=
    (Scheme.Etale.forget S).preimageIso eX
  let eY' : G₁.obj Y₁.obj ≅ G₂.obj Y₂.obj :=
    (Scheme.Etale.forget S).preimageIso eY
  let P := (E₁.functor.obj F).obj
  let η : G₁.op ⋙ P ⟶ F.obj := (E₁.unitIso.inv.app F).hom
  show (P.map eY'.hom.op ≫ η.app (Opposite.op Y₁.obj)) ≫
      F.obj.map f₁.hom.op =
    P.map (G₂.map f₂.hom).op ≫ (P.map eX'.hom.op ≫ η.app (Opposite.op X₁.obj))
  rw [Category.assoc, ← η.naturality]
  show P.map eY'.hom.op ≫
      (P.map (G₁.map f₁.hom).op ≫ η.app (Opposite.op X₁.obj)) = _
  rw [← Category.assoc, ← P.map_comp, ← Category.assoc, ← P.map_comp]
  congr 2
  apply Quiver.Hom.unop_inj
  show G₁.map f₁.hom ≫ eY'.hom = eX'.hom ≫ G₂.map f₂.hom
  apply (Scheme.Etale.forget S).map_injective
  rw [Functor.map_comp, Functor.map_comp]
  erw [Functor.map_preimage, Functor.map_preimage]
  apply Over.OverMorphism.ext
  exact congrArg Over.Hom.left hf

/-- Comparing a small étale topos with itself is naturally isomorphic to the
identity functor. -/
@[stacks 0958 "identity comparison"]
public noncomputable def smallEtaleToposEquiv_refl
    (B : BigEtaleSite.{u}) (S : Scheme.{u})
    (h : B.Contains S) :
    (smallEtaleToposEquiv.{u, v} B B S h h).functor ≅
      𝟭 (smallEtaleTopos.{u, max (u + 1) v} B S h) := by
  exact (smallEtaleToCommonToposEquiv B S h).unitIso.symm

/-- The equivalence for two successive changes of big étale site agrees,
naturally in sheaves, with the equivalence for the direct change. -/
@[stacks 0958 "composition of comparisons"]
public noncomputable def smallEtaleToposEquiv_trans
    (B₁ B₂ B₃ : BigEtaleSite.{u}) (S : Scheme.{u})
    (h₁ : B₁.Contains S) (h₂ : B₂.Contains S) (h₃ : B₃.Contains S) :
    (smallEtaleToposEquiv.{u, v} B₁ B₂ S h₁ h₂).functor ⋙
      (smallEtaleToposEquiv.{u, v} B₂ B₃ S h₂ h₃).functor ≅
        (smallEtaleToposEquiv.{u, v} B₁ B₃ S h₁ h₃).functor := by
  let E₁ := smallEtaleToCommonToposEquiv B₁ S h₁
  let E₂ := smallEtaleToCommonToposEquiv B₂ S h₂
  let E₃ := smallEtaleToCommonToposEquiv B₃ S h₃
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft E₁.functor (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerLeft E₁.functor (Functor.isoWhiskerRight E₂.counitIso E₃.inverse) ≪≫
    Functor.isoWhiskerLeft E₁.functor (Functor.leftUnitor E₃.inverse)

end AlgebraicGeometry

end
