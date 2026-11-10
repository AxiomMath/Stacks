module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleComparison
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.FibreProducts
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp

/-!
# Affine charts are a dense subsite of the small étale site of an algebraic space

Let `F` be an algebraic space over a scheme `S`. The inclusion of its affine étale charts into
all its étale charts is a special cocontinuous functor, and therefore induces an equivalence
between the topoi of sheaves on the affine étale site and on the small étale site of `F`.

## Main results

* `AlgebraicGeometry.Space.exists_etaleCovering_tautologicallyEquivalent`: every étale
  covering family of an object of a big fppf site whose members meet the site's size bound is
  tautologically equivalent to a chosen étale covering family with the same target.
* `AlgebraicGeometry.Space.exists_finite_affine_pullback_refinement`: a covering family of an
  étale chart, pulled back to an affine chart over it, is refined by a covering family of the
  affine étale site.
* `AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`: the inclusion of the
  affine étale charts of `F` into all its étale charts is a special cocontinuous functor, hence
  a dense subsite inclusion inducing an equivalence of sheaf categories.

## References

* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Finite affine refinements -/

/-- Every member of an étale covering family of a big fppf site is an étale morphism of
schemes. -/
private theorem etale_map_of_etaleCovering
    {B : BigFppfSite.{u}} {T : B.Schemes} {E : PreZeroHypercover T}
    (hE : IsEtaleCovering ⟨T, E⟩) (i : E.I₀) : Etale (B.inclusion.map (E.f i)) :=
  ((Scheme.presieve₀_mem_precoverage_iff (E.map B.inclusion)).mp hE).2 i

/-- An étale covering family of a big fppf site is an fppf covering family. -/
private theorem isFppfCovering_of_etaleCovering
    {B : BigFppfSite.{u}} {T : B.Schemes} {E : PreZeroHypercover T}
    (hE : IsEtaleCovering ⟨T, E⟩) : IsFppfCovering ⟨T, E⟩ := by
  change E.presieve₀ ∈ Scheme.fppfPrecoverage.comap B.inclusion T
  rw [Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
  refine (Scheme.presieve₀_mem_precoverage_iff (E.map B.inclusion)).mpr
    ⟨((Scheme.presieve₀_mem_precoverage_iff (E.map B.inclusion)).mp hE).1, fun i => ?_⟩
  have hprops := Etale.iff_flat_and_formallyUnramified.mp (etale_map_of_etaleCovering hE i)
  exact ⟨hprops.1, hprops.2.2⟩

/-- Every chosen étale covering family of an affine object of a big fppf site is refined by a
finite chosen étale covering family whose members are affine. -/
private theorem finite_standard_refinement
    (B : BigFppfSite.{u}) (T : B.Schemes)
    [IsAffine (B.inclusion.obj T)]
    (E : PreZeroHypercover T)
    (hE : B.etaleCovering ⟨T, E⟩) :
    ∃ F : PreZeroHypercover T,
      B.etaleCovering ⟨T, F⟩ ∧ Finite F.I₀ ∧
        (∀ i, IsAffine (B.inclusion.obj (F.X i))) ∧
        ∀ i, ∃ j, ∃ g : F.X i ⟶ E.X j, g ≫ E.f j = F.f i := by
  let T' := B.inclusion.obj T
  let U : Scheme.Cover Scheme.etalePrecoverage T' := {
    I₀ := E.I₀
    X i := B.inclusion.obj (E.X i)
    f i := B.inclusion.map (E.f i)
    mem₀ := by
      change (E.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage T'
      exact hE.2 }
  obtain ⟨V, q, hfin, hopen⟩ := finite_affine_refinement_etaleCover U
  let Q : PreZeroHypercover T := {
    I₀ := V.cover.I₀
    X i := by
      let : AlgebraicGeometry.IsOpenImmersion (q.h₀ i) := hopen i
      exact B.obj (X := V.cover.X i)
        (Scheme.size_lt_of_isOpenImmersion (q.h₀ i) (E.X (q.s₀ i)).property)
    f i := by
      let : AlgebraicGeometry.IsOpenImmersion (q.h₀ i) := hopen i
      exact B.inclusion.preimage (show
        B.inclusion.obj (B.obj (X := V.cover.X i)
          (Scheme.size_lt_of_isOpenImmersion (q.h₀ i) (E.X (q.s₀ i)).property)) ⟶
          B.inclusion.obj T from V.f i) }
  have hQ : IsEtaleCovering ⟨T, Q⟩ := by
    change (Q.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj T)
    rw [show Q.map B.inclusion = V.cover.toPreZeroHypercover from
      PreZeroHypercover.ext (x := _) (y := _) rfl (by rfl) (heq_of_eq (by
        funext i
        change B.inclusion.map (B.inclusion.preimage (show
          B.inclusion.obj (Q.X i) ⟶ B.inclusion.obj T from V.f i)) = V.f i
        rw [Functor.map_preimage]))]
    simpa [T', Scheme.etalePrecoverage] using V.cover.mem₀
  obtain ⟨R, hR, hcomb⟩ :=
    B.fppf_has_representative ⟨T, Q⟩ (isFppfCovering_of_etaleCovering hQ)
  rcases R with ⟨Rtarget, Rfam⟩
  have htarget : T = Rtarget := hcomb.1
  cases htarget
  have hcomb' : PreZeroHypercover.CombinatoriallyEquivalent Q Rfam := hcomb.2
  let F := deduplicateFamily Q
  have hFet : IsEtaleCovering ⟨T, F⟩ := by
    change (F.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj T)
    rw [PreZeroHypercover.presieve₀_map, deduplicateFamily_presieve₀,
      ← PreZeroHypercover.presieve₀_map]
    exact hQ
  have hFcard : Cardinal.mk F.I₀ ≤ B.coveringBound :=
    (deduplicateFamily_card_le hcomb').trans hR.2
  have hF : B.IsCovering ⟨T, F⟩ := ⟨isFppfCovering_of_etaleCovering hFet, hFcard⟩
  have : Finite Q.I₀ := by
    simpa [Q, Scheme.AffineCover.cover] using hfin
  have hFfinite : Finite F.I₀ := deduplicateFamily_finite Q
  have hFaff : ∀ i, IsAffine (B.inclusion.obj (F.X i)) := by
    intro i
    obtain ⟨k, hk⟩ := i.property
    have hi : i = ⟨(⟨Q.X k, Q.f k⟩ : Σ Y : B.Schemes, Y ⟶ T), ⟨k, rfl⟩⟩ :=
      Subtype.ext hk.symm
    subst i
    exact isAffine_Spec (V.X k)
  have hFrefine : ∀ i, ∃ j, ∃ g : F.X i ⟶ E.X j,
      g ≫ E.f j = F.f i := by
    intro i
    obtain ⟨k, hk⟩ := i.property
    have hi : i = ⟨(⟨Q.X k, Q.f k⟩ : Σ Y : B.Schemes, Y ⟶ T), ⟨k, rfl⟩⟩ :=
      Subtype.ext hk.symm
    subst i
    let g := B.inclusion.preimage (show
      B.inclusion.obj (Q.X k) ⟶ B.inclusion.obj (E.X (q.s₀ k)) from q.h₀ k)
    have htri : g ≫ E.f (q.s₀ k) = Q.f k := by
      apply B.inclusion.map_injective
      change B.inclusion.map (g ≫ E.f (q.s₀ k)) =
        B.inclusion.map (B.inclusion.preimage (show
          B.inclusion.obj (Q.X k) ⟶ B.inclusion.obj T from V.f k))
      rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
      simpa [Q, T', U, Scheme.AffineCover.cover] using q.w₀ k
    exact ⟨q.s₀ k, g, by simpa [F, deduplicateFamily] using htri⟩
  exact ⟨F, ⟨hF, hFet⟩, hFfinite, hFaff, hFrefine⟩

/-! ### Refining a pulled-back covering by affine charts -/

/-- **A covering family of an étale chart, pulled back to an affine chart over it, is refined
by a finite affine one.**  Let `E` be a covering family of an étale chart `U` of `F`, let `X` be
an affine étale chart and let `a : X ⟶ U` be a morphism of charts.  Then there is a covering
family of `X` in the affine étale site — so finite, with affine members — each of whose arrows
composed with `a` lies in the sieve generated by `E`. -/
theorem exists_finite_affine_pullback_refinement
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (X : AffineEtale B S hS F)
    {U : SmallEtale B S hS F}
    (a : (AffineEtale.inclusion B S hS F).obj X ⟶ U)
    (E : PreZeroHypercover U)
    (hE : SmallEtale.IsCovering B S hS F ⟨U, E⟩) :
    ∃ F' : PreZeroHypercover.{u + 1} X,
      F'.presieve₀ ∈ AffineEtale.precoverage B S hS F X ∧
      ∀ i, Sieve.generate E.presieve₀
        ((AffineEtale.inclusion B S hS F).map (F'.f i) ≫ a) := by
  let G := AffineEtale.inclusion B S hS F
  let H := SmallEtale.inclusion B S hS F
  let L := SmallEtale.toSchemes B S hS F
  let K := BigFppfOver.toScheme B S hS
  let X₀ := L.obj (G.obj X)
  let U₀ := L.obj U
  let E₀ := E.map L
  change B.etaleCovering ⟨U₀, E₀⟩ at hE
  obtain ⟨P, π₁, π₂, hpb, hcov⟩ := B.coverings_isSite.2.2
    ⟨U₀, E₀⟩ hE.1 X₀ (L.map a)
  let P₀ : PreZeroHypercover X₀ := {
    I₀ := E₀.I₀
    X i := P i
    f i := π₂ i
  }
  have hP₀ : B.IsCovering ⟨X₀, P₀⟩ := hcov
  have hP₀et : IsEtaleCovering ⟨X₀, P₀⟩ := by
    change (P₀.map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj X₀)
    apply (Scheme.presieve₀_mem_precoverage_iff
      (P₀.map B.inclusion)).mpr
    have hfp : IsFppfCovering ⟨X₀, P₀⟩ :=
      B.isFppfCovering_of_isCovering hP₀
    have hfp' : (P₀.map B.inclusion).presieve₀ ∈
        Scheme.fppfPrecoverage (B.inclusion.obj X₀) := by
      simpa [IsFppfCovering, PreZeroHypercover.presieve₀_map] using hfp
    have hjoint := (Scheme.presieve₀_mem_precoverage_iff
      (P₀.map B.inclusion)).mp hfp'
    refine ⟨hjoint.1, fun i => ?_⟩
    have hpb' : IsPullback (B.inclusion.map (π₁ i)) (B.inclusion.map (π₂ i))
        (B.inclusion.map (E₀.f i)) (B.inclusion.map (L.map a)) :=
      Functor.map_isPullback B.inclusion (hpb i)
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback hpb'
      (etale_map_of_etaleCovering hE.2 i)
  have : IsAffine (B.inclusion.obj X₀) := by
    change IsAffine ((AffineEtale.toScheme B S hS F).obj X)
    exact X.property
  obtain ⟨F₁, hF₁, hfinite, hFaff, hrefine⟩ :=
    finite_standard_refinement B X₀ P₀ ⟨hP₀, hP₀et⟩
  let Xc := H.obj (G.obj X)
  let Y (i : F₁.I₀) : BigFppfOver B S hS :=
    Over.mk (F₁.f i ≫ Xc.left.hom)
  let ei (i : F₁.I₀) : Y i ⟶ Xc.left := Over.homMk (F₁.f i) (by rfl)
  let ci (i : F₁.I₀) : CostructuredArrow yoneda F :=
    CostructuredArrow.mk (yoneda.map (ei i) ≫ Xc.hom)
  have hci (i : F₁.I₀) : IsEtaleChart B S hS F (ci i) :=
    etale_comp_of_scheme B S hS (ei i) Xc.hom (etale_map_of_etaleCovering hF₁.2 i)
      (G.obj X).property
  have hAffineChart (i : F₁.I₀) :
      IsAffineChart B S hS F ⟨ci i, hci i⟩ :=
    hFaff i
  let F' : PreZeroHypercover X := {
    I₀ := F₁.I₀
    X i := ⟨⟨ci i, hci i⟩, hAffineChart i⟩
    f i := ObjectProperty.homMk (ObjectProperty.homMk
      (CostructuredArrow.homMk (ei i) (by rfl)))}
  have hmap : (F'.map G).map L = F₁ := by
    ext <;> simp [F', G, H, L, Y, ei, ci, Xc, PreZeroHypercover.map]
  have hFcover : AffineEtale.IsCovering B S hS F ⟨X, F'⟩ := by
    change SmallEtale.IsCovering B S hS F
        ⟨G.obj X, F'.map G⟩ ∧ Finite F'.I₀
    constructor
    · change B.etaleCovering ⟨X₀, (F'.map G).map L⟩
      rw [hmap]
      exact hF₁
    · simpa [F'] using hfinite
  have hmem : F'.presieve₀ ∈ AffineEtale.precoverage B S hS F X := by
    rw [AffineEtale.mem_precoverage_iff]
    exact ⟨F', rfl, hFcover⟩
  refine ⟨F', hmem, fun i => ?_⟩
  obtain ⟨j, g, hg⟩ := hrefine i
  let Uc := H.obj U
  let Ec := H.obj (E.X j)
  have hfactor : (g ≫ π₁ j) ≫ E₀.f j = F₁.f i ≫ L.map a := by
    rw [Category.assoc, (hpb j).w, ← Category.assoc, ← hg]
  have hEw : E₀.f j ≫ Uc.left.hom = Ec.left.hom := by
    change (L.map (E.f j)) ≫ Uc.left.hom = Ec.left.hom
    exact Over.w (H.map (E.f j)).left
  have haw : L.map a ≫ Uc.left.hom = Xc.left.hom := Over.w (H.map a).left
  have heOver : (g ≫ π₁ j) ≫ Ec.left.hom = (Y i).hom := by
    rw [← hEw, ← Category.assoc, hfactor, Category.assoc, haw]
    rfl
  let e : Y i ⟶ Ec.left := Over.homMk (g ≫ π₁ j) heOver
  have heFactor : e ≫ (H.map (E.f j)).left = (ei i) ≫ (H.map a).left :=
    Over.OverMorphism.ext hfactor
  have hEcost : yoneda.map ((H.map (E.f j)).left) ≫ Uc.hom = Ec.hom :=
    CostructuredArrow.w (H.map (E.f j))
  have hacost : yoneda.map ((H.map a).left) ≫ Uc.hom = Xc.hom :=
    CostructuredArrow.w (H.map a)
  have hCost : yoneda.map e ≫ Ec.hom = (ci i).hom := by
    rw [← hEcost, ← Category.assoc, ← Functor.map_comp, heFactor, Functor.map_comp,
      Category.assoc, hacost]
    rfl
  let l₀ : ci i ⟶ Ec := CostructuredArrow.homMk e hCost
  let l : G.obj (F'.X i) ⟶ E.X j := ObjectProperty.homMk l₀
  have hl : l ≫ E.f j = G.map (F'.f i) ≫ a := by
    apply Functor.map_injective H
    apply CostructuredArrow.hom_ext
    exact heFactor
  refine ⟨E.X j, l, E.f j, ⟨j⟩, hl⟩

/-! ### Cocontinuity and cover density -/

private theorem affine_inclusion_lifts_saturate
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    ∀ {U : SmallEtale B S hS F} {R : Sieve U},
      (SmallEtale.precoverage B S hS F).Saturate U R →
      ∀ {X : AffineEtale B S hS F}
        (a : (AffineEtale.inclusion B S hS F).obj X ⟶ U),
        (R.pullback a).functorPullback
          (AffineEtale.inclusion B S hS F) ∈
            AffineEtale.topology B S hS F X := by
  intro U R hR
  induction hR with
  | of U P hP =>
      intro X a
      obtain ⟨E, hEq, hE⟩ :=
        (SmallEtale.mem_precoverage_iff B S hS F).mp hP
      subst P
      obtain ⟨F', hF, hfactor⟩ :=
        exists_finite_affine_pullback_refinement B S hS F X a E hE
      have hgen : Sieve.generate F'.presieve₀ ∈
          AffineEtale.topology B S hS F X := .of X F'.presieve₀ hF
      refine (AffineEtale.topology B S hS F).superset_covering ?_ hgen
      rw [Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      simpa [Sieve.pullback_apply, Category.assoc] using hfactor i
  | top U =>
      intro X a
      simpa only [Sieve.pullback_top, Sieve.functorPullback_top] using
        (AffineEtale.topology B S hS F).top_mem X
  | pullback U R hR Y f ih =>
      intro X a
      simpa [Sieve.pullback_comp, Category.assoc] using
        ih (X := X) (a := a ≫ f)
  | transitive U R T hR hlocal ih ihlocal =>
      intro X a
      refine (AffineEtale.topology B S hS F).transitive (ih a)
        ((T.pullback a).functorPullback
          (AffineEtale.inclusion B S hS F)) ?_
      intro Z k hk
      have hk' : R ((AffineEtale.inclusion B S hS F).map k ≫ a) := hk
      have hsat := ihlocal hk' (X := Z) (a := 𝟙 _)
      rw [← Sieve.functorPullback_pullback]
      simpa [Sieve.pullback_comp, Category.assoc] using hsat

private theorem affine_inclusion_topology_eq_restricted
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hDense : (AffineEtale.inclusion B S hS F).IsCoverDense
      (SmallEtale.topology B S hS F)) :
    AffineEtale.topology B S hS F =
      (AffineEtale.inclusion B S hS F).restrictedTopology
        (SmallEtale.topology B S hS F) := by
  let G := AffineEtale.inclusion B S hS F
  let P := AffineEtale.precoverage B S hS F
  let Q := SmallEtale.precoverage B S hS F
  let K := SmallEtale.topology B S hS F
  have : G.IsCoverDense K := hDense
  have hpre : P ≤ Q.comap G := by
    intro X R hR
    obtain ⟨E, hEq, hE⟩ :=
      (AffineEtale.mem_precoverage_iff B S hS F).mp hR
    rw [Precoverage.mem_comap_iff, hEq, ← PreZeroHypercover.presieve₀_map,
      SmallEtale.mem_precoverage_iff]
    exact ⟨E.map G, rfl, hE.1⟩
  have hcomp : Q.comap G ≤ K.toPrecoverage.comap G := fun _ _ hR =>
    Precoverage.mem_comap_iff.mpr
      (Q.le_toPrecoverage_toGrothendieck _ (Precoverage.mem_comap_iff.mp hR))
  have hle : P.toGrothendieck ≤ G.restrictedTopology K := by
    change P.toGrothendieck ≤ (K.toPrecoverage.comap G).toGrothendieck
    exact (Precoverage.toGrothendieck_monotone hpre).trans
      (Precoverage.toGrothendieck_monotone hcomp)
  have hge : G.restrictedTopology K ≤ P.toGrothendieck := by
    intro X R hR
    rw [Functor.mem_restrictedTopology_iff] at hR
    have hsat : Q.Saturate (G.obj X) (R.functorPushforward G) := hR
    have hlift := affine_inclusion_lifts_saturate B S hS F hsat (𝟙 _)
    rwa [Sieve.pullback_id, Sieve.functorPullback_functorPushforward_eq G] at hlift
  exact le_antisymm hle hge

/-- **Chosen representatives of étale covering families, with a fixed target.** Every étale
covering family of an object `T` of a big fppf site whose members satisfy the site's size
bound is tautologically equivalent to a chosen étale covering family *of `T` itself*. -/
public theorem exists_etaleCovering_tautologicallyEquivalent
    (B : BigFppfSite.{u}) (T : B.Schemes)
    (U : PreZeroHypercover.{u + 1} (B.inclusion.obj T))
    (hU : U.presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj T))
    (hsize : ∀ i, B.Contains (U.X i)) :
    ∃ V : PreZeroHypercover.{u + 1} T,
      B.etaleCovering ⟨T, V⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent U (V.map B.inclusion) := by
  let W : Covering B.Schemes := ⟨T, {
    I₀ := U.I₀
    X i := B.obj (X := U.X i) (hsize i)
    f i := B.inclusion.preimage (show
      B.inclusion.obj (B.obj (X := U.X i) (hsize i)) ⟶ B.inclusion.obj T from U.f i)
  }⟩
  have hmap : W.2.map B.inclusion = U :=
    PreZeroHypercover.ext (x := _) (y := _) rfl (by rfl) (heq_of_eq (by
      funext i
      change B.inclusion.map (B.inclusion.preimage (show
        B.inclusion.obj (W.2.X i) ⟶ B.inclusion.obj T from U.f i)) = U.f i
      rw [Functor.map_preimage]))
  have hW : IsEtaleCovering W := by
    change (W.2.map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj T)
    rwa [hmap]
  obtain ⟨W', hW', hcomb⟩ := exists_chosen_etaleCovering B W hW
  rcases W' with ⟨Wtarget, Wfam⟩
  have htarget : T = Wtarget := hcomb.1
  cases htarget
  have hcomb' : PreZeroHypercover.CombinatoriallyEquivalent W.2 Wfam := hcomb.2
  refine ⟨Wfam, hW', ?_⟩
  have hfirst : PreZeroHypercover.TautologicallyEquivalent U
      (W.2.map B.inclusion) := by
    rw [← hmap]
    exact PreZeroHypercover.tautologicallyEquivalent_refl _
  have hcomb'' : PreZeroHypercover.CombinatoriallyEquivalent
        (W.2.map B.inclusion) (Wfam.map B.inclusion) := by
    change PreZeroHypercover.CombinatoriallyEquivalent W.2 Wfam at hcomb'
    rcases hcomb' with ⟨h₁, h₂⟩
    constructor
    · rcases h₁ with ⟨α, hX, hf⟩
      exact ⟨α, fun i => congrArg (fun X : B.Schemes => B.inclusion.obj X) (hX i), by
        intro i
        simpa [PreZeroHypercover.map] using
          congrArg (fun f => B.inclusion.map f) (hf i)⟩
    · rcases h₂ with ⟨β, hX, hf⟩
      exact ⟨β, fun j => congrArg (fun X : B.Schemes => B.inclusion.obj X) (hX j), by
        intro j
        simpa [PreZeroHypercover.map] using
          congrArg (fun f => B.inclusion.map f) (hf j)⟩
  exact PreZeroHypercover.tautologicallyEquivalent_trans _ _ _ hfirst
    (PreZeroHypercover.tautologicallyEquivalent_of_combinatoriallyEquivalent
      _ _ hcomb'')

private theorem affineEtale_inclusion_isCoverDense
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :
    (AffineEtale.inclusion B S hS F).IsCoverDense
      (SmallEtale.topology B S hS F) := by
  let G := AffineEtale.inclusion B S hS F
  let H := SmallEtale.inclusion B S hS F
  let L := SmallEtale.toSchemes B S hS F
  let K := SmallEtale.topology B S hS F
  constructor
  intro X
  let T := L.obj X
  let A := (B.inclusion.obj T).affineOpenCover
  let U : (B.inclusion.obj T).OpenCover.{u + 1} := {
    I₀ := ULift.{u + 1, u} A.I₀
    X i := A.openCover.X i.down
    f i := A.openCover.f i.down
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨?_, ?_⟩
      · intro x
        obtain ⟨i, y, hy⟩ := A.openCover.exists_eq x
        exact ⟨ULift.up i, y, hy⟩
      · intro i
        exact A.openCover.map_prop i.down }
  obtain ⟨V, hV, hEq⟩ :=
    exists_etaleCovering_tautologicallyEquivalent B T U.toPreZeroHypercover
      (Scheme.precoverage_mono (P := @AlgebraicGeometry.IsOpenImmersion) (Q := @Etale)
        (fun _ _ f _ => inferInstance) (B.inclusion.obj T) U.mem₀)
      (fun i => Scheme.size_lt_of_isOpenImmersion (U.f i) T.property)
  let Uc := H.obj X
  let Y (i : V.I₀) : BigFppfOver B S hS :=
    Over.mk (V.f i ≫ Uc.left.hom)
  let ei (i : V.I₀) : Y i ⟶ Uc.left := Over.homMk (V.f i) (by rfl)
  let ci (i : V.I₀) : CostructuredArrow yoneda F :=
    CostructuredArrow.mk (yoneda.map (ei i) ≫ Uc.hom)
  have hci (i : V.I₀) : IsEtaleChart B S hS F (ci i) :=
    etale_comp_of_scheme B S hS (ei i) Uc.hom (etale_map_of_etaleCovering hV.2 i)
      X.property
  have hAffine (i : V.I₀) : IsAffine (B.inclusion.obj (V.X i)) := by
    obtain ⟨β, hβ⟩ := hEq.2
    obtain ⟨e, he⟩ := hβ i
    have : IsAffine (U.X (β i)) := by
      change IsAffine (A.openCover.X (β i).down)
      infer_instance
    exact @IsAffine.of_isIso (B.inclusion.obj (V.X i)) (U.X (β i))
      e.hom e.isIso_hom (inferInstance : IsAffine (U.X (β i)))
  let E : PreZeroHypercover X := {
    I₀ := V.I₀
    X i := ⟨ci i, hci i⟩
    f i := ObjectProperty.homMk (CostructuredArrow.homMk (ei i) (by rfl))
  }
  have hmap : E.map L = V := by
    ext <;> simp [E, L, H, Y, ei, ci, Uc, PreZeroHypercover.map]
  have hE : SmallEtale.IsCovering B S hS F ⟨X, E⟩ := by
    change B.etaleCovering ⟨T, E.map L⟩
    rw [hmap]
    exact hV
  have hpre : E.presieve₀ ∈ SmallEtale.precoverage B S hS F X :=
    ⟨E, rfl, hE⟩
  have hgen : Sieve.generate E.presieve₀ ∈ K X := .of X E.presieve₀ hpre
  apply K.superset_covering ?_ hgen
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  exact ⟨⟨⟨E.X i, hAffine i⟩, eqToHom rfl, E.f i, by simp⟩⟩

/-- The inclusion of the affine étale charts of an algebraic space into all its étale charts is
a special cocontinuous functor; in particular it is a dense subsite inclusion, and so induces an
equivalence between the affine étale topos and the small étale topos. -/
@[stacks 04JS]
theorem AffineEtale.inclusion_isSpecialCocontinuous
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (_hF : IsAlgebraicSpace B S hS F) :
    IsSpecialCocontinuous
      (AffineEtale.topology B S hS F)
      (SmallEtale.topology B S hS F)
      (AffineEtale.inclusion B S hS F) := by
  let G := AffineEtale.inclusion B S hS F
  let J := AffineEtale.topology B S hS F
  let K := SmallEtale.topology B S hS F
  have hDense := affineEtale_inclusion_isCoverDense B S hS F
  have hCocont : G.IsCocontinuous J K := by
    constructor
    intro X R hR
    change (SmallEtale.precoverage B S hS F).Saturate (G.obj X) R at hR
    exact affine_inclusion_lifts_saturate B S hS F hR (𝟙 _)
  have : G.IsCoverDense K := hDense
  have hTopo := affine_inclusion_topology_eq_restricted B S hS F hDense
  have hSub : G.IsDenseSubsite J K := by
    refine {
      isCoverDense' := hDense
      isLocallyFull' := inferInstance
      isLocallyFaithful' := inferInstance
      functorPushforward_mem_iff := ?_ }
    intro X R
    change R.functorPushforward G ∈ K (G.obj X) ↔
      R ∈ AffineEtale.topology B S hS F X
    rw [hTopo]
    exact (Functor.mem_restrictedTopology_iff (G := G)).symm
  exact ⟨hCocont, hSub⟩

end AlgebraicGeometry.Space
