module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.IsConnected
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CoverPreserving
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.StandardRefinement
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs

/-!
# Affine objects form a dense subsite of the big smooth site

Let `B` be a big smooth site containing a scheme `S`. The inclusion of the big affine smooth
site over `S` into the big smooth site over `S` is a special cocontinuous functor, and therefore
induces an equivalence between their topoi of sheaves.

## Main results

* `AlgebraicGeometry.BigAffineSmooth.inclusion_isSpecialCocontinuous` — the inclusion of affine
  objects is a special cocontinuous functor, hence a dense subsite inclusion inducing an
  equivalence of sheaf categories.

## Implementation notes

`IsSpecialCocontinuous` records cocontinuity together with the dense-subsite property; the latter
canonically supplies the induced equivalence of sheaf categories, so the single assertion
carries both conclusions of the source.

## References

* [Stacks Project, Tag 06VC](https://stacks.math.columbia.edu/tag/06VC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Every covering sieve of a big smooth site contains a chosen covering family. -/
private theorem exists_covering_refining_sieve (B : BigSmoothSite.{u})
    {X : B.category} {R : Sieve X}
    (hR : R ∈ B.grothendieckTopology X) :
    ∃ E : PreZeroHypercover X, B.IsCovering ⟨X, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [BigSmoothSite.grothendieckTopology, Precoverage.mem_toGrothendieck_iff] at hR
  induction hR with
  | of X P hP =>
      obtain ⟨E, hE, rfl⟩ := hP
      exact ⟨E, hE, Sieve.le_generate _⟩
  | top X =>
      exact ⟨PreZeroHypercover.singleton (𝟙 X), B.covering_isSite.1 (𝟙 X), fun _ _ _ ↦ trivial⟩
  | pullback X R hR Y f ih =>
      obtain ⟨E, hE, hle⟩ := ih
      obtain ⟨P, p₁, p₂, hpb, hP⟩ := B.covering_isSite.2.2 ⟨X, E⟩ hE Y f
      let F : PreZeroHypercover Y := ⟨E.I₀, P, p₂⟩
      refine ⟨F, hP, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      intro i
      rw [Sieve.pullback_apply, ← (hpb i).w]
      exact R.downward_closed (hle _ _ ⟨i⟩) (p₁ i)
  | transitive X R Q hR hRQ ihR ihRQ =>
      obtain ⟨E, hE, hle⟩ := ihR
      have hlocal (i : E.I₀) := ihRQ (hle _ _ ⟨i⟩)
      choose F hF hFle using hlocal
      let EF := E.bind F
      have hEF : B.IsCovering ⟨X, EF⟩ :=
        B.covering_isSite.2.1 ⟨X, E⟩ hE (fun i ↦ ⟨E.X i, F i⟩) hF (fun _ ↦ rfl)
      refine ⟨EF, hEF, ?_⟩
      rw [Presieve.ofArrows_le_iff]
      rintro ⟨i, j⟩
      change Q ((F i).f j ≫ E.f i)
      exact hFle i _ _ ⟨j⟩

/-- Over an affine object of a big smooth site, every covering sieve contains a finite chosen
covering family whose members are affine and standard smooth over the target. -/
private theorem exists_affine_covering_refining_sieve (B : BigSmoothSite.{u})
    {T : B.category} [IsAffine ((ObjectProperty.ι _).obj T)] {R : Sieve T}
    (hR : R ∈ B.grothendieckTopology T) :
    ∃ P : PreZeroHypercover T, Finite P.I₀ ∧
      ∃ hPaff : ∀ i, IsAffine ((ObjectProperty.ι _).obj (P.X i)),
      ∃ _hPstandard : ∀ i, letI := hPaff i
        IsStandardSmooth ((ObjectProperty.ι _).map (P.f i)),
      B.IsCovering ⟨T, P⟩ ∧ P.presieve₀ ≤ R := by
  obtain ⟨E, hE, hER⟩ := exists_covering_refining_sieve B hR
  let U : ((ObjectProperty.ι _).obj T).Cover (Scheme.precoverage (@Smooth)) :=
    ⟨E.map (ObjectProperty.ι _), hE.1⟩
  obtain ⟨V, hVref, hVfinite, hVstandard, _⟩ :=
    exists_finite_affine_standardSmooth_refinement U
  let Q := V.cover.toPreZeroHypercover
  have : Finite Q.I₀ := hVfinite
  have : ∀ i, IsAffine (Q.X i) := fun i ↦ isAffine_Spec (V.X i)
  have hQstandard : IsStandardSmoothCovering Q.X Q.f :=
    ⟨hVstandard, Set.iUnion_eq_univ_iff.mpr
      ((Scheme.presieve₀_mem_precoverage_iff Q).mp V.cover.mem₀).1⟩
  obtain ⟨W, hW, hWQ⟩ :=
    exists_covering_tautologicallyEquivalent_standardSmoothCover B Q hQstandard
  rcases hWQ with ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
  let α' : Q.I₀ → W.I₀ := α
  let β' : W.I₀ → Q.I₀ := β
  have hα' (i : Q.I₀) : ∃ e : Q.X i ≅ (ObjectProperty.ι _).obj (W.X (α' i)),
      e.hom ≫ (ObjectProperty.ι _).map (W.f (α' i)) = Q.f i := by
    simpa [α', PreZeroHypercover.map] using hα i
  have hβ' (i : W.I₀) : ∃ e : (ObjectProperty.ι _).obj (W.X i) ≅ Q.X (β' i),
      e.hom ≫ Q.f (β' i) = (ObjectProperty.ι _).map (W.f i) := by
    simpa [β', PreZeroHypercover.map] using hβ i
  let I := Set.range α'
  have : Finite I := Finite.of_surjective (fun i : Q.I₀ => (⟨α' i, ⟨i, rfl⟩⟩ : I))
    fun i ↦ ⟨i.2.choose, Subtype.ext i.2.choose_spec⟩
  let P : PreZeroHypercover T :=
    { I₀ := I
      X := fun i => W.X i.1
      f := fun i => W.f i.1 }
  have hPaff : ∀ i, IsAffine ((ObjectProperty.ι _).obj (P.X i)) := by
    intro i
    obtain ⟨e, _⟩ := hβ' i.1
    have : IsAffine (Q.X (β' i.1)) := isAffine_Spec _
    exact IsAffine.of_isIso e.hom
  have hPstandard : ∀ i, IsStandardSmooth ((ObjectProperty.ι _).map (P.f i)) := by
    intro i
    obtain ⟨e, he⟩ := hβ' i.1
    have : IsAffine ((ObjectProperty.ι _).obj (P.X i)) := hPaff i
    let e' : Arrow.mk ((ObjectProperty.ι _).map (P.f i)) ≅
        Arrow.mk (Q.f (β' i.1)) := Arrow.isoMk e (Iso.refl _) he
    exact (isStandardSmooth_iff_of_arrow_iso _ _ e').2 (hVstandard (β' i.1))
  have hPcover : B.IsCovering ⟨T, P⟩ := by
    change SmoothCovering B.cutoff ⟨T, P⟩ ∧ Cardinal.mk P.I₀ ≤ B.coveringBound
    constructor
    · change (P.map (ObjectProperty.ι _)).presieve₀ ∈
        Scheme.precoverage (@Smooth.{u}) ((ObjectProperty.ι _).obj T)
      apply (Scheme.presieve₀_mem_precoverage_iff (P.map (ObjectProperty.ι _))).2
      constructor
      · intro x
        obtain ⟨i, y, hy⟩ :=
          ((Scheme.presieve₀_mem_precoverage_iff Q).mp V.cover.mem₀).1 x
        obtain ⟨e, he⟩ := hα' i
        let j : I := ⟨α' i, ⟨i, rfl⟩⟩
        refine ⟨j, e.hom y, ?_⟩
        change (e.hom ≫ (ObjectProperty.ι _).map (P.f j)) y = x
        rwa [he]
      · intro j
        obtain ⟨e, he⟩ := hβ' j.1
        have : Smooth (Q.f (β' j.1)) := V.cover.map_prop (β' j.1)
        change Smooth ((ObjectProperty.ι _).map (W.f j.1))
        rw [← he]
        infer_instance
    · exact (Cardinal.mk_le_of_injective (f := fun i : I => (i.1 : W.I₀))
        Subtype.val_injective).trans hW.2
  have hPR : P.presieve₀ ≤ R := by
    rw [Presieve.ofArrows_le_iff]
    intro j
    obtain ⟨e, he⟩ := hβ' j.1
    let k := β' j.1
    let g : P.X j ⟶ E.X (hVref.s₀ k) :=
      ObjectProperty.homMk (e.hom ≫ hVref.h₀ k)
    have hg : g ≫ E.f (hVref.s₀ k) = P.f j := by
      apply (ObjectProperty.ι _).map_injective
      change (e.hom ≫ hVref.h₀ k) ≫
          (ObjectProperty.ι _).map (E.f (hVref.s₀ k)) =
        (ObjectProperty.ι _).map (W.f j.1)
      calc
        (e.hom ≫ hVref.h₀ k) ≫
            (ObjectProperty.ι _).map (E.f (hVref.s₀ k)) =
          e.hom ≫ (hVref.h₀ k ≫ U.f (hVref.s₀ k)) := by cat_disch
        _ = e.hom ≫ Q.f k := by rw [hVref.w₀]
        _ = (ObjectProperty.ι _).map (W.f j.1) := he
    rw [← hg]
    exact R.downward_closed (hER _ _ ⟨hVref.s₀ k⟩) g
  exact ⟨P, inferInstance, hPaff, hPstandard, hPcover, hPR⟩

private theorem inclusion_isCoverDense (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) :
    (BigAffineSmooth.inclusion B S hS).IsCoverDense
      (BigSmoothOver.topology B S hS) := by
  classical
  constructor
  intro X
  let T : B.category := X.left
  let O := (ObjectProperty.ι _).obj T
  let U := O.affineOpenCover.openCover
  obtain ⟨W, hW, hWU⟩ :=
    exists_covering_tautologicallyEquivalent_openCover B T U
  rcases hWU with ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
  have hWaff : ∀ j, IsAffine ((ObjectProperty.ι _).obj (W.X j)) := by
    intro j
    obtain ⟨e, _⟩ := hβ j
    have : IsAffine (U.X (β j)) := by
      change IsAffine (Spec (O.affineOpenCover.X (β j)))
      exact isAffine_Spec _
    exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance
  let Vobj (j : W.I₀) : BigAffineSmooth B S hS :=
    { obj := Over.mk (W.f j ≫ X.hom), property := hWaff j }
  let vmap (j : W.I₀) :
      (BigAffineSmooth.inclusion B S hS).obj (Vobj j) ⟶ X :=
    Over.homMk (W.f j)
  have hBcover : Sieve.ofArrows (fun j => (BigAffineSmooth.inclusion B S hS).obj
      (Vobj j)) vmap ∈ BigSmoothOver.topology B S hS X := by
    rw [BigSmoothOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows W.X W.f ∈ B.grothendieckTopology T
    simpa [PreZeroHypercover.presieve₀] using
      Precoverage.generate_mem_toGrothendieck (⟨W, hW, rfl⟩ : W.presieve₀ ∈ B.precoverage T)
  apply (BigSmoothOver.topology B S hS).superset_covering _ hBcover
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro j
  exact Presieve.in_coverByImage (BigAffineSmooth.inclusion B S hS) (vmap j)

private theorem inclusion_isCocontinuous (B : BigSmoothSite.{u}) (S : Scheme.{u})
    (hS : S.size < B.cutoff) :
    (BigAffineSmooth.inclusion B S hS).IsCocontinuous
      (BigAffineSmooth.topology B S hS)
      (BigSmoothOver.topology B S hS) := by
  classical
  constructor
  intro X R hR
  let u := BigAffineSmooth.inclusion B S hS
  let Y := u.obj X
  let T : B.category := Y.left
  have : IsAffine ((ObjectProperty.ι _).obj T) := X.2
  have hRB : (Sieve.overEquiv Y) R ∈ B.grothendieckTopology T := by
    rwa [BigSmoothOver.topology, GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨P, hPfinite, hPaff, hPstandard, hPcover, hPR⟩ :=
    exists_affine_covering_refining_sieve B hRB
  have hTscheme : (ObjectProperty.ι _).obj T =
      (BigAffineSmooth.toScheme B S hS).obj X := rfl
  let F : PreZeroHypercover X :=
    { I₀ := P.I₀
      X := fun i =>
        { obj := Over.mk (P.f i ≫ Y.hom)
          property := hPaff i }
      f := fun i => ObjectProperty.homMk (Over.homMk (P.f i)) }
  have hFcover : BigAffineSmooth.IsCovering B S hS ⟨X, F⟩ := by
    constructor
    · exact hPcover
    · refine ⟨hPfinite, ?_⟩
      have : ∀ i, IsAffine ((ObjectProperty.ι _).obj (P.X i)) := hPaff
      refine ⟨hPstandard, ?_⟩
      change (⋃ i : P.I₀, Set.range ((ObjectProperty.ι _).map (P.f i))) = Set.univ
      refine Set.eq_univ_iff_forall.mpr fun x => ?_
      have hmem : (P.map (ObjectProperty.ι _)).presieve₀ ∈
          Scheme.precoverage (@Smooth.{u}) ((ObjectProperty.ι _).obj T) := hPcover.1
      obtain ⟨hsurj, _⟩ := (Scheme.presieve₀_mem_precoverage_iff
        (P.map (ObjectProperty.ι _))).mp hmem
      obtain ⟨i, y, hy⟩ := hsurj x
      change ((ObjectProperty.ι _).map (P.f i)) y = x at hy
      have hy' : (P.f i).hom y = x := by
        simpa only [ObjectProperty.ι_map] using hy
      exact Set.mem_iUnion.mpr ⟨i, Set.mem_range.mpr ⟨y, by
        simpa [F, BigAffineSmooth.toScheme, BigSmoothOver.toScheme,
          BigSmoothOver.forget, ObjectProperty.ι_map, hTscheme] using hy'⟩⟩
  have hgen : Sieve.generate F.presieve₀ ∈ BigAffineSmooth.topology B S hS X :=
    Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hFcover⟩
  apply (BigAffineSmooth.topology B S hS).superset_covering _ hgen
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  change R (u.map (F.f i))
  rw [show u.map (F.f i) = Over.homMk (P.f i) by rfl]
  apply (Sieve.overEquiv_iff R (P.f i)).mp
  exact hPR _ _ ⟨i⟩

private theorem inclusion_isCoverPreserving (B : BigSmoothSite.{u})
    (S : Scheme.{u}) (hS : S.size < B.cutoff) :
    CoverPreserving (BigAffineSmooth.topology B S hS)
      (BigSmoothOver.topology B S hS)
      (BigAffineSmooth.inclusion B S hS) := by
  let u := BigAffineSmooth.inclusion B S hS
  let K := BigSmoothOver.topology B S hS
  have : HasPullbacks B.category := inferInstance
  have : HasLimitsOfShape WalkingCospan B.category := inferInstance
  let hterm : IsTerminal WalkingCospan.one :=
    IsTerminal.ofUniqueHom
      (fun j => by
        cases j with
        | none => exact 𝟙 _
        | some j =>
          cases j with
          | left => exact WalkingCospan.Hom.inl
          | right => exact WalkingCospan.Hom.inr)
      (fun _ _ => Subsingleton.elim _ _)
  have : IsConnected WalkingCospan :=
    CategoryTheory.isConnected_of_isTerminal WalkingCospan hterm
  have : PreservesLimitsOfShape WalkingCospan (ObjectProperty.ι
      (fun X : Scheme ↦ X.size < B.cutoff)) := inferInstance
  have : PreservesLimitsOfShape WalkingCospan (Over.forget (B.base S hS)) :=
    inferInstance
  have : PreservesLimitsOfShape WalkingCospan (BigSmoothOver.toScheme B S hS) :=
    inferInstance
  let P := BigSmoothOver.IsAffineOver B S hS
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h => by
    change IsAffine ((BigSmoothOver.toScheme B S hS).obj _) at h ⊢
    exact IsAffine.of_isIso ((BigSmoothOver.toScheme B S hS).map e.inv)⟩
  have : P.IsClosedUnderLimitsOfShape WalkingCospan := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro X ⟨F, hF⟩
    let G := F ⋙ BigSmoothOver.toScheme B S hS
    have : IsAffine (G.obj WalkingCospan.left) := hF WalkingCospan.left
    have : IsAffine (G.obj WalkingCospan.right) := hF WalkingCospan.right
    have : IsAffine (G.obj WalkingCospan.one) := hF WalkingCospan.one
    have : IsAffine (limit G) :=
      IsAffine.of_isIso (HasLimit.isoOfNatIso (diagramIsoCospan G)).hom
    exact IsAffine.of_isIso (preservesLimitIso
      (BigSmoothOver.toScheme B S hS) F).hom
  have : HasPullbacks (BigAffineSmooth B S hS) := inferInstance
  have : PreservesLimitsOfShape WalkingCospan u := inferInstance
  apply coverPreserving_of_generators u
    (BigAffineSmooth.precoverage B S hS) K
  intro X R hR
  obtain ⟨E, hEeq, hE⟩ := hR
  subst R
  rw [← Sieve.generate_map_eq_functorPushforward]
  dsimp [K]
  rw [BigSmoothOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
  have hbase : Presieve.map (BigSmoothOver.forget B S hS)
      ((E.map u).presieve₀) ∈ B.precoverage ((u.obj X).left) := by
    refine ⟨(E.map u).map (BigSmoothOver.forget B S hS), hE.1, ?_⟩
    simp [PreZeroHypercover.presieve₀_map]
  apply B.grothendieckTopology.superset_covering _
    (Precoverage.generate_mem_toGrothendieck hbase)
  rw [Sieve.generate_le_iff, PreZeroHypercover.presieve₀_map]
  exact le_trans
    (Presieve.map_le_functorPushforward (F := BigSmoothOver.forget B S hS)
      (Presieve.map u E.presieve₀))
    (Sieve.le_generate _)

/-- **Stacks 06VC.** The inclusion of the big affine smooth site over a scheme
into its big smooth site is special cocontinuous. Its dense-subsite component
is precisely the datum which gives the induced equivalence of topoi. -/
@[stacks 06VC]
public theorem BigAffineSmooth.inclusion_isSpecialCocontinuous
    (B : BigSmoothSite.{u}) (S : Scheme.{u}) (hS : S.size < B.cutoff) :
    IsSpecialCocontinuous
      (BigAffineSmooth.topology B S hS)
      (BigSmoothOver.topology B S hS)
      (BigAffineSmooth.inclusion B S hS) := by
  change Functor.IsCocontinuous _ _ _ ∧ _
  refine ⟨inclusion_isCocontinuous B S hS, ?_⟩
  let u := BigAffineSmooth.inclusion B S hS
  let J := BigAffineSmooth.topology B S hS
  let K := BigSmoothOver.topology B S hS
  have hcover := inclusion_isCoverPreserving B S hS
  have hfaithful : ∀ ⦃U' U : BigAffineSmooth B S hS⦄
      (a b : U' ⟶ U), u.map a = u.map b → Sieve.equalizer a b ∈ J U' := by
    intro U' U a b hab
    obtain rfl := u.map_injective hab
    simp
  have hfull : ∀ ⦃U' U : BigAffineSmooth B S hS⦄
      (c : u.obj U' ⟶ u.obj U), u.imageSieve c ∈ J U' := by
    intro U' U c; rw [← u.map_preimage c, Functor.imageSieve_map]
    exact J.top_mem U'
  have : u.IsCocontinuous J K := inclusion_isCocontinuous B S hS
  have : u.IsCoverDense K := inclusion_isCoverDense B S hS
  exact Functor.isDenseSubsite_of_isCocontinuous u J K hcover hfaithful hfull

end AlgebraicGeometry
