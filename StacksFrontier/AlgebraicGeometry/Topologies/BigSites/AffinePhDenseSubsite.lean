module

public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CoveringRefinesSieve
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.PhSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CoverPreserving
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.Composition
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs

/-!
# Affine objects form a dense subsite of the big ph site

Let `B` be a big ph site containing a scheme `S`. The inclusion of the big affine ph site over
`S` into the big ph site over `S` is cocontinuous and a dense subsite, so it induces an
equivalence between their topoi of sheaves.

## Main results

* `AlgebraicGeometry.BigAffinePH.inclusion_isCocontinuous` — the inclusion is cocontinuous.
* `AlgebraicGeometry.BigAffinePH.inclusion_isDenseSubsite` — the inclusion is a dense subsite,
  so the induced inverse-image and direct-image functors on sheaves are equivalences.

## Implementation notes

Cocontinuity rests on `exists_finite_affine_ph_refinement`: a covering sieve of an object of
the site whose underlying scheme is affine contains a finite covering family by affine
objects. That is proved by taking any covering family of the site inside the sieve, which is a
ph covering, restricting it to the whole of the affine target to get a *standard* ph covering
refining it, realizing that standard covering inside the site (Stacks 0DBK part 2), and
cutting the index type down to the image of the realization so that the family stays within
the site's bound on index types. Transporting the ph property across the resulting
isomorphisms of sources is `ph_of_surjective_iso_map`.

Cover density is the affine open cover of the underlying scheme, realized in the site by
Stacks 0DBK part 3.

## References

* [Stacks Project, Tag 0DBP](https://stacks.math.columbia.edu/tag/0DBP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w

namespace AlgebraicGeometry

/-- A covering sieve of a big ph site contains one of the site's own covering families. -/
private theorem bigPHSite_exists_covering_refining_sieve (B : BigPHSite.{u})
    {X : B.Schemes} {R : Sieve X} (hR : R ∈ B.topology X) :
    ∃ E : PreZeroHypercover X, B.IsCovering ⟨X, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [BigPHSite.topology] at hR
  exact CategoryTheory.exists_covering_refining_sieve B.IsCovering B.precoverage
    (fun h => ⟨h.choose, h.choose_spec.2, h.choose_spec.1⟩) B.coverings_isSite hR

/-- A scheme isomorphic to an affine scheme is affine. -/
private theorem isAffine_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) [IsAffine Y] : IsAffine X :=
  IsAffine.of_isIso e.hom

private theorem inclusion_isCoverDense (B : BigPHSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (BigAffinePH.inclusion B S hS).IsCoverDense
      (BigPHOver.topology B S hS) := by
  classical
  refine ⟨fun X => ?_⟩
  let T : B.Schemes := X.left
  let O := B.inclusion.obj T
  let U := O.affineOpenCover.openCover
  obtain ⟨W, hW, hWU⟩ := openCover_tautologicallyEquivalent B T U
  rcases hWU with ⟨_, ⟨β, hβ⟩⟩
  have hWaff : ∀ j, IsAffine (B.inclusion.obj (W.X j)) := by
    intro j
    obtain ⟨e, _⟩ := hβ j
    have : IsAffine (U.X (β j)) := isAffine_Spec (O.affineOpenCover.X (β j))
    exact isAffine_of_iso e
  let Vobj (j : W.I₀) : BigAffinePH B S hS :=
    { obj := Over.mk (W.f j ≫ X.hom)
      property := hWaff j }
  let vf (j : W.I₀) :
      (BigAffinePH.inclusion B S hS).obj (Vobj j) ⟶ X :=
    Over.homMk (W.f j)
  have hBcover : Sieve.ofArrows
      (fun j => (BigAffinePH.inclusion B S hS).obj (Vobj j)) vf ∈
      BigPHOver.topology B S hS X := by
    rw [BigPHOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows W.X W.f ∈ B.topology T
    simpa [PreZeroHypercover.presieve₀] using
      Precoverage.generate_mem_toGrothendieck (⟨W, rfl, hW⟩ : W.presieve₀ ∈ B.precoverage T)
  refine (BigPHOver.topology B S hS).superset_covering ?_ hBcover
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  exact fun j => Presieve.in_coverByImage (BigAffinePH.inclusion B S hS) (vf j)

private theorem ph_of_surjective_iso_map {T : Scheme.{u}} {I : Type v} {J : Type w}
    {X : I → Scheme.{u}} {Y : J → Scheme.{u}} {f : ∀ i, X i ⟶ T}
    {g : ∀ j, Y j ⟶ T} (a : I → J) (ha : ∀ j, ∃ i, a i = j)
    (e : ∀ i, X i ≅ Y (a i)) (he : ∀ i, (e i).hom ≫ g (a i) = f i)
    (hX : IsPHCovering X f) : IsPHCovering Y g := by
  rw [isPHCovering_iff] at hX ⊢
  constructor
  · intro j
    obtain ⟨i, rfl⟩ := ha j
    have := hX.1 i
    have hEq : (e i).inv ≫ f i = g (a i) := by simp [← he i]
    rw [← hEq]
    infer_instance
  · intro V hV
    obtain ⟨P, hP, hφ⟩ := hX.2 V hV
    let E : PreZeroHypercover T := ⟨I, X, f⟩
    let φ : P.Hom (E.pullback₂ V.ι) :=
      Classical.choice hφ
    let F : PreZeroHypercover T := { I₀ := J, X := Y, f := g }
    let : ∀ j, HasPullback (g j) V.ι := fun _ => inferInstance
    have hidx : (E.pullback₂ V.ι).I₀ = I := PreZeroHypercover.pullback₂_I₀ V.ι E
    have hidxF : (F.pullback₂ V.ι).I₀ = J := PreZeroHypercover.pullback₂_I₀ V.ι F
    let s : P.I₀ → I := fun k => hidx ▸ φ.s₀ k
    let fstLeg (k : P.I₀) := φ.h₀ k ≫ pullback.fst (f (s k)) V.ι ≫ (e (s k)).hom
    let sndLeg (k : P.I₀) := φ.h₀ k ≫ pullback.snd (f (s k)) V.ι
    have hcond (k : P.I₀) : fstLeg k ≫ g (a (s k)) = sndLeg k ≫ V.ι := by
      dsimp [fstLeg, sndLeg]
      calc
        _ = φ.h₀ k ≫ (pullback.fst (f (s k)) V.ι ≫
            ((e (s k)).hom ≫ g (a (s k)))) := by cat_disch
        _ = φ.h₀ k ≫ (pullback.fst (f (s k)) V.ι ≫ f (s k)) := by rw [he]
        _ = φ.h₀ k ≫ (pullback.snd (f (s k)) V.ι ≫ V.ι) :=
          congrArg (φ.h₀ k ≫ ·) pullback.condition
        _ = _ := by cat_disch
    let ψ : P.Hom (F.pullback₂ V.ι) := by
      cases hidx
      cases hidxF
      dsimp [E, F, PreZeroHypercover.pullback₂] at φ ⊢
      exact
        { s₀ := fun k => a (s k)
          h₀ := fun k => pullback.lift (fstLeg k) (sndLeg k) (hcond k)
          w₀ := by
            intro k
            change pullback.lift (fstLeg k) (sndLeg k) (hcond k) ≫
              pullback.snd (g (a (s k))) V.ι = P.f k
            exact (pullback.lift_snd (fstLeg k) (sndLeg k) (hcond k)).trans (φ.w₀ k) }
    exact ⟨P, hP, ⟨ψ⟩⟩

private theorem exists_finite_affine_ph_refinement (B : BigPHSite.{u})
    {T : B.Schemes} [IsAffine (B.inclusion.obj T)] {R : Sieve T}
    (hR : R ∈ B.topology T) :
    ∃ Q : PreZeroHypercover T, B.IsCovering ⟨T, Q⟩ ∧ Finite Q.I₀ ∧
      (∀ i, IsAffine (B.inclusion.obj (Q.X i))) ∧ Q.presieve₀ ≤ R := by
  classical
  obtain ⟨E, hE, hER⟩ := bigPHSite_exists_covering_refining_sieve B hR
  have hEph : IsPHCovering (E.map B.inclusion).X (E.map B.inclusion).f := hE.ph
  let V : (B.inclusion.obj T).Opens := ⊤
  let eTop := (B.inclusion.obj T).topIso
  have hV : IsAffine V.toScheme := isAffineOpen_top (B.inclusion.obj T)
  obtain ⟨P, hPstd, ⟨φ⟩⟩ := ((isPHCovering_iff _ _).mp hEph).2 V hV
  let P' : PreZeroHypercover (B.inclusion.obj T) :=
    ⟨P.I₀, P.X, fun i => P.f i ≫ eTop.hom⟩
  have hP'std : StandardPHCovering P'.f := by
    obtain ⟨hfin, hX, U, g, j, hg, hsurj, hj, hcover, hcomp⟩ := hPstd
    have : Finite P'.I₀ := hfin
    have : IsProper g := hg
    refine StandardPHCovering.of_presentation P'.f hX
      (g ≫ eTop.hom) j (by infer_instance) (by infer_instance) hj hcover fun i => ?_
    change (j i ≫ g) ≫ eTop.hom = P.f i ≫ eTop.hom
    rw [hcomp i]
  have : Finite P'.I₀ := hP'std.finite
  have : IsAffine T.1 := ‹IsAffine (B.inclusion.obj T)›
  obtain ⟨W, hW, ⟨α, hα⟩, β, hβ⟩ := standardPHCovering_tautologicallyEquivalent B T P' hP'std
  let I := Set.range α
  let Q : PreZeroHypercover T := ⟨I, fun i => W.X i.1, fun i => W.f i.1⟩
  have hQaff (i : I) : IsAffine (B.inclusion.obj (Q.X i)) := by
    obtain ⟨_, k, rfl⟩ := i
    have := hP'std.isAffine k
    exact isAffine_of_iso (hα k).choose.symm
  let aQ (i : P'.I₀) : (Q.map B.inclusion).I₀ := ⟨α i, ⟨i, rfl⟩⟩
  have hQcov : B.IsCovering ⟨T, Q⟩ := ⟨
    ph_of_surjective_iso_map aQ (fun j => ⟨j.2.choose, Subtype.ext j.2.choose_spec⟩)
      (fun i => (hα i).choose) (fun i => (hα i).choose_spec)
      (standardPHCovering_isPHCovering hP'std),
    (Cardinal.mk_le_of_injective (f := fun i : I => (i.1 : W.I₀))
      Subtype.val_injective).trans hW.2⟩
  refine ⟨Q, hQcov, inferInstance, hQaff, ?_⟩
  rw [Presieve.ofArrows_le_iff]
  intro i
  let k := β i.1
  obtain ⟨e, he⟩ := hβ i.1
  replace he : e.hom ≫ P.f k ≫ V.ι = B.inclusion.map (Q.f i) := he
  let g : Q.X i ⟶ E.X (φ.s₀ k) := B.inclusion.preimage
    (e.hom ≫ φ.h₀ k ≫ pullback.fst ((E.map B.inclusion).f (φ.s₀ k)) V.ι)
  have hmapg : B.inclusion.map g = _ := B.inclusion.map_preimage _
  have hg : g ≫ E.f (φ.s₀ k) = Q.f i := B.inclusion.map_injective <| by
    rw [Functor.map_comp, hmapg, ← he, ← φ.w₀ k]
    simp only [Category.assoc]
    exact congrArg (e.hom ≫ φ.h₀ k ≫ ·) pullback.condition
  rw [← hg]
  exact R.downward_closed (hER _ _ ⟨_⟩) g

/-- **Stacks 0DBP, cocontinuity.** The inclusion of affine objects over `S`
in a chosen big ph site is cocontinuous. -/
@[stacks 0DBP "cocontinuity"]
public instance BigAffinePH.inclusion_isCocontinuous
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (BigAffinePH.inclusion B S hS).IsCocontinuous
      (BigAffinePH.topology B S hS)
      (BigPHOver.topology B S hS) where
  cover_lift := by
    intro X R hR
    let u := BigAffinePH.inclusion B S hS
    let J := BigAffinePH.topology B S hS
    let T : B.Schemes := (BigPHOver.forget B S hS).obj (u.obj X)
    have hRbase : (Sieve.overEquiv (u.obj X)) R ∈ B.topology T :=
      (GrothendieckTopology.mem_over_iff B.topology R).mp hR
    have hTaff : IsAffine (B.inclusion.obj T) := by
      change IsAffine ((BigPHOver.toScheme B S hS).obj (u.obj X))
      exact BigAffinePH.isAffine_toScheme_obj B S hS X
    obtain ⟨Q, hQcover, hQfinite, hQaffine, hQle⟩ :=
      exists_finite_affine_ph_refinement B (T := T)
        (R := Sieve.overEquiv (u.obj X) R) hRbase
    let Vobj (i : Q.I₀) : BigAffinePH B S hS :=
      { obj := Over.mk (Q.f i ≫ (u.obj X).hom)
        property := hQaffine i }
    let vf (i : Q.I₀) : Vobj i ⟶ X :=
      ObjectProperty.homMk
        (Over.homMk (X := B.obj S hS) (U := (Vobj i).obj) (V := X.obj)
          (Q.f i) rfl)
    let V : PreZeroHypercover X := ⟨Q.I₀, Vobj, vf⟩
    have hVcover : BigAffinePH.IsCovering B S hS ⟨X, V⟩ := by
      change BigPHOver.IsCovering B S hS _ ∧ Finite V.I₀
      refine ⟨?_, hQfinite⟩
      have hmap : (V.map u).map (BigPHOver.forget B S hS) = Q := by ext <;> rfl
      change B.IsCovering ⟨T, (V.map u).map (BigPHOver.forget B S hS)⟩
      rwa [hmap]
    have hVmem : Sieve.generate V.presieve₀ ∈ J X :=
      Precoverage.generate_mem_toGrothendieck ⟨V, rfl, hVcover⟩
    have hVle : V.presieve₀ ≤ R.functorPullback u := by
      rw [Presieve.ofArrows_le_iff]
      intro i
      change R (Over.homMk (X := B.obj S hS)
        (U := Over.mk (Q.f i ≫ X.obj.hom)) (V := X.obj) (Q.f i) rfl)
      exact (Sieve.overEquiv_iff R (Q.f i)).mp (hQle _ _ ⟨i⟩)
    exact J.superset_covering ((Sieve.generate_le_iff ..).mpr hVle) hVmem

/-- The inclusion of affine objects over `S` in a chosen big ph site is cover preserving. -/
theorem BigAffinePH.inclusion_coverPreserving
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    CoverPreserving (BigAffinePH.topology B S hS) (BigPHOver.topology B S hS)
      (BigAffinePH.inclusion B S hS) := by
  let u := BigAffinePH.inclusion B S hS
  let K := BigPHOver.topology B S hS
  have := schemeSizeBelow_isClosedUnderLimitsOfShape_walkingCospan B.cutoff
  have : PreservesLimitsOfShape WalkingCospan (BigPHOver.toScheme B S hS) := by infer_instance
  let P := BigPHOver.IsAffineOver B S hS
  have : P.IsClosedUnderIsomorphisms := ⟨fun e h => by
    change IsAffine ((BigPHOver.toScheme B S hS).obj _) at h ⊢
    exact IsAffine.of_isIso ((BigPHOver.toScheme B S hS).map e.inv)⟩
  have : P.IsClosedUnderLimitsOfShape WalkingCospan := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro X ⟨F, hF⟩
    let G := F ⋙ BigPHOver.toScheme B S hS
    have : IsAffine (G.obj WalkingCospan.left) := hF WalkingCospan.left
    have : IsAffine (G.obj WalkingCospan.right) := hF WalkingCospan.right
    have : IsAffine (G.obj WalkingCospan.one) := hF WalkingCospan.one
    have : IsAffine (pullback (G.map WalkingCospan.Hom.inl) (G.map WalkingCospan.Hom.inr)) :=
      inferInstance
    have : IsAffine (limit G) :=
      IsAffine.of_isIso (HasLimit.isoOfNatIso (diagramIsoCospan G)).hom
    exact IsAffine.of_isIso (preservesLimitIso (BigPHOver.toScheme B S hS) F).hom
  have : PreservesLimitsOfShape WalkingCospan u := by infer_instance
  apply coverPreserving_of_generators u (BigAffinePH.precoverage B S hS) K
  intro X R hR
  obtain ⟨E, rfl, hE⟩ := hR
  rw [← Sieve.generate_map_eq_functorPushforward]
  dsimp [K]
  rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
  have hbase : Presieve.map (BigPHOver.forget B S hS)
      ((E.map u).presieve₀) ∈ B.precoverage ((u.obj X).left) :=
    ⟨(E.map u).map (BigPHOver.forget B S hS), by simp [PreZeroHypercover.presieve₀_map], hE.1⟩
  refine B.topology.superset_covering ?_ (Precoverage.generate_mem_toGrothendieck hbase)
  rw [Sieve.generate_le_iff, PreZeroHypercover.presieve₀_map]
  exact le_trans
    (Presieve.map_le_functorPushforward
      (F := BigPHOver.forget B S hS) (Presieve.map u E.presieve₀))
    (Sieve.le_generate _)

/-- **Stacks 0DBP, equivalence of topoi.** The inclusion of affine objects
is a dense subsite, hence its induced morphism of sheaf topoi is an equivalence. -/
@[stacks 0DBP "equivalence of topoi"]
public instance BigAffinePH.inclusion_isDenseSubsite
    (B : BigPHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (BigAffinePH.inclusion B S hS).IsDenseSubsite
      (BigAffinePH.topology B S hS)
      (BigPHOver.topology B S hS) := by
  let u := BigAffinePH.inclusion B S hS
  let J := BigAffinePH.topology B S hS
  let K := BigPHOver.topology B S hS
  have hfaithful : ∀ ⦃U' U : BigAffinePH B S hS⦄
      (a b : U' ⟶ U), u.map a = u.map b → Sieve.equalizer a b ∈ J U' := by
    intro U' U a b hab
    obtain rfl := u.map_injective hab
    simp
  have hfull : ∀ ⦃U' U : BigAffinePH B S hS⦄
      (c : u.obj U' ⟶ u.obj U), u.imageSieve c ∈ J U' := by
    intro U' U c
    rw [← u.map_preimage c, Functor.imageSieve_map]
    exact J.top_mem U'
  have : u.IsCocontinuous J K := BigAffinePH.inclusion_isCocontinuous B S hS
  have : u.IsCoverDense K := inclusion_isCoverDense B S hS
  exact Functor.isDenseSubsite_of_isCocontinuous u J K
    (BigAffinePH.inclusion_coverPreserving B S hS) hfaithful hfull

end AlgebraicGeometry
