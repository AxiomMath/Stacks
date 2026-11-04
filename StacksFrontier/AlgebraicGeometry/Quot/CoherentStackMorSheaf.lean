module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackHomGlue
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCanonical
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackFiberedUnconditional
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackProjection
public import StacksFrontier.AlgebraicGeometry.Quot.RelativeIsom
public import StacksFrontier.AlgebraicGeometry.Spaces.Pushouts.FormalGlueingCovering
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FiniteCoverRefinement
public import StacksFrontier.CategoryTheory.Sites.Stackification.StageTwoMorSheaf

/-!
# The morphism presheaves of `Coh_{X/Y}` are sheaves

Let `D` be the standing datum of Stacks 08KB and `p : Coh_{X/Y} ⟶ (Sch/S)_fppf` the projection.
This file proves condition (2) of Stacks 026F for `p`: for two objects `x`, `y` over a scheme `U`,
the presheaf `Mor(x, y)` on `(Sch/U)_fppf` is a sheaf.  This is the half of Stacks 08KC on the
presheaves `Isom` of the source.

By `CategoryTheory.Functor.isMorSheaf_of_locallyEqual_of_amalgamation` it suffices to show that
two morphisms of `Coh_{X/Y}` which agree locally on the base are equal, and that morphisms into an
object given compatibly over a covering sieve glue.  Both are read on an fpqc covering contained in
the sieve (`AlgebraicGeometry.BigFppfOver.exists_fpqc_family_refining`), along the chosen pullbacks
of the source to its members, where they are
`AlgebraicGeometry.Space.CoherentHom.eq_of_comp_eq` and
`AlgebraicGeometry.Space.CoherentHom.exists_glue`: Stacks 04W8 for morphisms.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.eq_of_locallyEqual`: separation.
* `AlgebraicGeometry.Space.CoherentSituation.exists_amalgamation`: gluing.
* `AlgebraicGeometry.Space.CoherentSituation.isMorSheaf`: **condition (2) of Stacks 026F.**

## References

* [Stacks Project, Tag 08KC](https://stacks.math.columbia.edu/tag/08KC)
* [Stacks Project, Tag 026F](https://stacks.math.columbia.edu/tag/026F)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

attribute [local instance] AlgebraicGeometry.Space.pointTopology

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Two morphisms from the algebraic space of an object of the site to an algebraic space which
agree on the members of a covering family are equal: an algebraic space is a sheaf. -/
theorem schemeSpace_hom_ext {U : BigFppfOver B S hS} {Y : AlgebraicSpaces B S hS} {L : Type*}
    {V : L → BigFppfOver B S hS} (f : ∀ l, V l ⟶ U)
    (hf : Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS U)
    {g₁ g₂ : (schemeSpaceFunctor B S hS).obj U ⟶ Y}
    (h : ∀ l, (schemeSpaceFunctor B S hS).map (f l) ≫ g₁ =
      (schemeSpaceFunctor B S hS).map (f l) ≫ g₂) : g₁ = g₂ := by
  have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) Y.obj :=
    (isSheaf_iff_isSheaf_of_type _ _).1 Y.property.isSheaf
  have hfor : Presieve.IsSheafFor Y.obj (Presieve.ofArrows V f) := by
    rw [Presieve.isSheafFor_iff_generate]
    exact hsh _ hf
  have key : ∀ (l : L) (g : (schemeSpaceFunctor B S hS).obj U ⟶ Y),
      Y.obj.map (f l).op (yonedaEquiv g.hom) =
        yonedaEquiv ((schemeSpaceFunctor B S hS).map (f l) ≫ g).hom :=
    fun l g => yonedaEquiv_naturality _ (f l)
  have ht : yonedaEquiv g₁.hom = yonedaEquiv g₂.hom := by
    refine hfor.isSeparatedFor.ext fun Z k hk => ?_
    obtain ⟨l⟩ := hk
    rw [key l g₁, key l g₂, h l]
  exact ObjectProperty.hom_ext _ (yonedaEquiv.injective ht)

namespace CoherentSituation

variable (D : CoherentSituation B S hS)

/-- The test scheme over `Y` of an arrow into the scheme of an object of `Coh_{X/Y}`. -/
abbrev arrowObject (A : CoherentObject D) {V : BigFppfOver B S hS} (f : V ⟶ A.T.left) :
    SchemesOver D.Y :=
  CostructuredArrow.mk ((schemeSpaceFunctor B S hS).map f ≫ A.T.hom)

/-- The morphism of test schemes over `Y` of an arrow into the scheme of an object. -/
abbrev arrowHom (A : CoherentObject D) {V : BigFppfOver B S hS} (f : V ⟶ A.T.left) :
    D.arrowObject A f ⟶ A.T :=
  CostructuredArrow.homMk f rfl

/-- The chosen pullback of an object of `Coh_{X/Y}` along an arrow into its scheme. -/
abbrev restrictHom (A : CoherentObject D) {V : BigFppfOver B S hS} (f : V ⟶ A.T.left) :
    CoherentHom (pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS) A
      (D.arrowHom A f)) A :=
  pullbackHom' (modulePullbackStabilityOfFinitePresentation B S hS) A (D.arrowHom A f)

/-- The morphisms of base changes of the chosen pullbacks along an fpqc covering of the scheme of
an object form an fpqc covering. -/
theorem isFpqcCovering_restrictHom (A : CoherentObject D) {L : Type*}
    {V : L → BigFppfOver B S hS} (f : ∀ l, V l ⟶ A.T.left)
    (hf : IsFpqcCovering B S hS fun l => ((schemeSpaceFunctor B S hS).map (f l)).hom) :
    IsFpqcCovering B S hS fun l => (D.relativeMap (D.restrictHom A (f l)).base).hom :=
  isFpqcCovering_baseChangeMap D.f (fun l => D.arrowHom A (f l)) hf

/-- A covering sieve of the big fppf site contains a covering family whose members, read on
algebraic spaces, form an fpqc covering. -/
theorem exists_fpqc_family {U : BigFppfOver B S hS} (R : Sieve U)
    (hR : R ∈ BigFppfOver.topology B S hS U) :
    ∃ (L : Type (u + 1)) (V : L → BigFppfOver B S hS) (f : ∀ l, V l ⟶ U),
      (∀ l, R.arrows (f l)) ∧ Sieve.ofArrows V f ∈ BigFppfOver.topology B S hS U ∧
        IsFpqcCovering B S hS fun l => ((schemeSpaceFunctor B S hS).map (f l)).hom := by
  obtain ⟨L, V, f, hfR, hcov, hfpqc⟩ := BigFppfOver.exists_fpqc_family_refining R hR
  exact ⟨L, V, f, hfR, hcov, represented_fpqc_family B S hS L V f hfpqc⟩

/-- **Separation.**  Two morphisms of `Coh_{X/Y}` which are locally equal for the fppf topology
are equal. -/
theorem eq_of_locallyEqual {A A' : CoherentObject D} {m n : CoherentHom A A'}
    (h : letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
      (coherentSiteProjection D.categoryData).LocallyEqual (BigFppfOver.topology B S hS)
        (x := A) (y := A') m n) : m = n := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  have hb : m.base = n.base := CostructuredArrow.hom_ext _ _ h.1
  obtain ⟨R, hR, hloc⟩ := h.2
  obtain ⟨L, V, f, hfR, -, hfpqc⟩ := exists_fpqc_family R hR
  exact CoherentHom.eq_of_comp_eq (fun l => D.restrictHom A (f l))
    (D.isFpqcCovering_restrictHom A f hfpqc) m n hb fun l => hloc (D.restrictHom A (f l)) (hfR l)

/-- The projection of `Coh_{X/Y}` to the site, written out, is fibred in groupoids
(Stacks 08W5). -/
theorem isFiberedInGroupoids_siteProjection :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    (coherentSiteProjection D.categoryData).IsFiberedInGroupoids := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  rw [← coherentSiteProjection_eq D.categoryData]
  exact D.projection_isFiberedInGroupoids

/-- **Fill-ins in `Coh_{X/Y}`.**  A morphism `ψ : Z ⟶ X` whose base map factors as `f` followed
by the base map of `φ : Y ⟶ X` factors through `φ` by a morphism over `f`. -/
theorem exists_fillIn {X Y Z : CoherentObject D} (φ : CoherentHom Y X) (ψ : CoherentHom Z X)
    (f : Z.T.left ⟶ Y.T.left) (h : f ≫ φ.base.left = ψ.base.left) :
    ∃ χ : CoherentHom Z Y, χ.base.left = f ∧ χ.comp φ = ψ := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  obtain ⟨χ, ⟨h₁, h₂⟩, -⟩ := D.isFiberedInGroupoids_siteProjection.unique_lift φ ψ f h
  exact ⟨χ, h₁, h₂⟩

/-- **Gluing.**  Morphisms into an object of `Coh_{X/Y}`, given over a covering sieve of the
scheme of the source, compatibly with precomposition and over a common morphism `u` of schemes,
come from one morphism over `u`. -/
theorem exists_amalgamation {A A' : CoherentObject D} (u : A.T.left ⟶ A'.T.left)
    {R : Sieve A.T.left} (hR : R ∈ BigFppfOver.topology B S hS A.T.left)
    (F : ∀ {W : CoherentObject D} (Φ : CoherentHom W A), R.arrows Φ.base.left →
      CoherentHom W A')
    (hFbase : ∀ {W : CoherentObject D} (Φ : CoherentHom W A) (hΦ : R.arrows Φ.base.left),
      (F Φ hΦ).base.left = Φ.base.left ≫ u)
    (hFcomp : ∀ {W W' : CoherentObject D} (Ψ : CoherentHom W' W) (Φ : CoherentHom W A)
      (hΦ : R.arrows Φ.base.left) (hΨΦ : R.arrows (Ψ.comp Φ).base.left),
      F (Ψ.comp Φ) hΨΦ = Ψ.comp (F Φ hΦ)) :
    ∃ G : CoherentHom A A', G.base.left = u ∧
      ∀ {W : CoherentObject D} (Φ : CoherentHom W A) (hΦ : R.arrows Φ.base.left),
        Φ.comp G = F Φ hΦ := by
  have hFeq : ∀ {W : CoherentObject D} (Φ Φ' : CoherentHom W A) (_ : Φ = Φ')
      (hΦ : R.arrows Φ.base.left) (hΦ' : R.arrows Φ'.base.left), F Φ hΦ = F Φ' hΦ' := by
    rintro W Φ _ rfl _ _
    rfl
  have hFsq : ∀ {W W₁ W₂ : CoherentObject D} (a : CoherentHom W W₁) (b : CoherentHom W W₂)
      (Φ₁ : CoherentHom W₁ A) (Φ₂ : CoherentHom W₂ A) (h₁ : R.arrows Φ₁.base.left)
      (h₂ : R.arrows Φ₂.base.left), a.comp Φ₁ = b.comp Φ₂ →
        a.comp (F Φ₁ h₁) = b.comp (F Φ₂ h₂) := fun a b Φ₁ Φ₂ h₁ h₂ h => by
    rw [← hFcomp a Φ₁ h₁ (R.downward_closed h₁ _), ← hFcomp b Φ₂ h₂ (R.downward_closed h₂ _)]
    exact hFeq _ _ h _ _
  obtain ⟨L, V, f, hfR, hcov, hfpqc⟩ := exists_fpqc_family R hR
  let Φ : ∀ l, CoherentHom _ A := fun l => D.restrictHom A (f l)
  let φ : ∀ l, CoherentHom _ A' := fun l => F (Φ l) (hfR l)
  have hu : (schemeSpaceFunctor B S hS).map u ≫ A'.T.hom = A.T.hom := by
    refine schemeSpace_hom_ext f hcov fun l => ?_
    have hw := CostructuredArrow.w (φ l).base
    rw [hFbase (Φ l) (hfR l)] at hw
    rw [← Category.assoc, ← Functor.map_comp]
    exact hw
  let β : A.T ⟶ A'.T := CostructuredArrow.homMk u hu
  have hφb : ∀ l, (φ l).base = (Φ l).base ≫ β := fun l =>
    CostructuredArrow.hom_ext _ _ (by
      rw [hFbase (Φ l) (hfR l), CostructuredArrow.comp_left]
      rfl)
  let ψ : ∀ l, (modulePullback B S hS (D.relativeMap ((Φ l).base ≫ β))).obj A'.F ⟶
      (pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS) A
        (D.arrowHom A (f l))).F :=
    fun l => eqToHom (congrArg (fun b => (modulePullback B S hS (D.relativeMap b)).obj A'.F)
      (hφb l).symm) ≫ (φ l).fibre
  have hψ : ∀ l, IsIso (ψ l) := fun l => by
    dsimp only [ψ]
    infer_instance
  have hψe : ∀ l, (⟨(Φ l).base ≫ β, ψ l, hψ l⟩ : CoherentHom _ A') = φ l := fun l =>
    (CoherentHom.mk_eq_mk_eqToHom (hφb l).symm (φ l).fibre).symm
  obtain ⟨G, hGb, hGc⟩ := CoherentHom.exists_glue β Φ (D.isFpqcCovering_restrictHom A f hfpqc)
    ψ fun l m => by
      let P := pullbackObject' (modulePullbackStabilityOfFinitePresentation B S hS) A
        (D.arrowHom A (f l))
      let c := D.restrictHom P (pullback.fst (f l) (f m))
      obtain ⟨e, he₁, he₂⟩ := D.exists_fillIn (Φ m) (c.comp (Φ l)) (pullback.snd (f l) (f m))
        pullback.condition.symm
      refine ⟨_, c, e, ?_, he₂.symm, ?_⟩
      · rw [he₁]
        exact IsPullback.of_hasPullback (f l) (f m)
      · rw [hψe l, hψe m]
        exact hFsq _ _ _ _ _ _ he₂.symm
  have hGu : G.base.left = u := by rw [hGb]; rfl
  refine ⟨G, hGu, fun {W} Φ' hΦ' => ?_⟩
  obtain ⟨K, Y, g, hgS, -, hgfpqc⟩ := exists_fpqc_family
    ((Sieve.ofArrows V f).pullback Φ'.base.left)
    ((BigFppfOver.topology B S hS).pullback_stable _ hcov)
  refine CoherentHom.eq_of_comp_eq (fun j => D.restrictHom W (g j))
    (D.isFpqcCovering_restrictHom W g hgfpqc) _ _ ?_ fun j => ?_
  · refine CostructuredArrow.hom_ext _ _ ?_
    show Φ'.base.left ≫ G.base.left = (F Φ' hΦ').base.left
    rw [hFbase Φ' hΦ', hGu]
  · obtain ⟨l, a, ha⟩ := Functor.exists_factorization_of_ofArrows (hgS j)
    let χ := D.restrictHom W (g j)
    obtain ⟨θ, -, hθ⟩ := D.exists_fillIn (Φ l) (χ.comp Φ') a ha
    calc χ.comp (Φ'.comp G) = (χ.comp Φ').comp G :=
          (CoherentHom.assoc (modulePushforwardCoherence B S hS) χ Φ' G).symm
      _ = (θ.comp (Φ l)).comp G := by rw [hθ]
      _ = θ.comp ((Φ l).comp G) := CoherentHom.assoc (modulePushforwardCoherence B S hS) _ _ _
      _ = θ.comp (φ l) := by rw [hGc l, hψe l]
      _ = χ.comp (F Φ' hΦ') := hFsq _ _ _ _ _ _ hθ

/-- **Condition (2) of Stacks 026F for `Coh_{X/Y}`**: the morphism presheaves are sheaves for the
fppf topology. -/
theorem isMorSheaf :
    letI : Category.{u + 1} (CoherentObject D) := D.categoryData.category
    haveI : (coherentSiteProjection D.categoryData).IsFibered :=
      D.isFiberedInGroupoids_siteProjection.isFibered
    ∀ (U : BigFppfOver B S hS) (x y : (coherentSiteProjection D.categoryData).Fiber U),
      (coherentSiteProjection D.categoryData).IsMorSheaf (BigFppfOver.topology B S hS) U x y := by
  let : Category.{u + 1} (CoherentObject D) := D.categoryData.category
  have : (coherentSiteProjection D.categoryData).IsFibered :=
    D.isFiberedInGroupoids_siteProjection.isFibered
  exact Functor.isMorSheaf_of_locallyEqual_of_amalgamation (fun h => D.eq_of_locallyEqual h)
    (fun u _ hS' F hFbase hFcomp => D.exists_amalgamation u hS' F hFbase hFcomp)

end CoherentSituation

end AlgebraicGeometry.Space

end
