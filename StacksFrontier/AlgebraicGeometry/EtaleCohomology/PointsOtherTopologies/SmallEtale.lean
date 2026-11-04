module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import Mathlib.CategoryTheory.Sites.Point.Map
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.FiniteRefinement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallAffineEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp
public import StacksCore.Tactic.StacksAttribute

/-!
# Enough points for the small étale site

The small étale site of a scheme has enough points, because the small affine étale site is a
dense subsite of it and has enough points.

## Main results

* `AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous` states that the
  inclusion of the small affine étale site into the small étale site is special cocontinuous,
  hence induces an equivalence of topoi.
* `AlgebraicGeometry.SmallEtale.hasConservativeFamily` states that the small étale site has
  enough points.

## References

* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 06VX](https://stacks.math.columbia.edu/tag/06VX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v w u₁ v₁ w₁

namespace AlgebraicGeometry

private theorem smallAffineEtale_isCoverDense
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (AlgebraicGeometry.SmallAffineEtale.inclusion B S hS).IsCoverDense
      (AlgebraicGeometry.SmallEtale.topology B S hS) := by
  let K := AlgebraicGeometry.SmallEtale.topology B S hS
  constructor
  intro X
  let T := B.inclusion.obj X.obj.left
  let A := T.affineOpenCover
  let U : T.OpenCover.{u + 1} := {
    I₀ := ULift.{u + 1, u} A.I₀
    X i := A.openCover.X i.down
    f i := A.openCover.f i.down
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      constructor
      · intro x
        obtain ⟨i, y, hy⟩ := A.openCover.exists_eq x
        exact ⟨ULift.up i, y, hy⟩
      · intro i
        exact A.openCover.map_prop i.down }
  obtain ⟨V, hV, hEq⟩ :=
    AlgebraicGeometry.BigEtaleSite.exists_isCovering_tautologicallyEquivalent_openCover
      B X.obj.left U
  obtain ⟨β, hβ⟩ := hEq.2
  let e (i : V.I₀) := Classical.choose (hβ i)
  have he (i : V.I₀) : (e i).hom ≫ U.f (β i) = (V.map B.inclusion).f i :=
    Classical.choose_spec (hβ i)
  let E : PreZeroHypercover X := {
    I₀ := V.I₀
    X i := ⟨Over.mk (V.f i ≫ X.obj.hom), by
      show Etale (B.inclusion.map (V.f i) ≫ B.inclusion.map X.obj.hom)
      have : Etale (B.inclusion.map (V.f i)) := by
        rw [← show (e i).hom ≫ U.f (β i) = B.inclusion.map (V.f i) by
          simpa [PreZeroHypercover.map] using he i]
        have : IsOpenImmersion (U.f (β i)) := U.map_prop (β i)
        exact Etale.etale_comp (e i).hom (U.f (β i))
      have : Etale (B.inclusion.map X.obj.hom) := X.property
      exact Etale.etale_comp _ _⟩
    f i := ObjectProperty.homMk (Over.homMk (V.f i) (by simp))
  }
  have hmap : E.map (AlgebraicGeometry.SmallEtale.inclusion B S hS ⋙
      AlgebraicGeometry.BigEtaleOver.forget B S hS) = V := by
    ext <;> rfl
  have hE : AlgebraicGeometry.SmallEtale.IsCovering B S hS ⟨X, E⟩ := by
    show B.IsCovering ⟨X.obj.left, E.map
      (AlgebraicGeometry.SmallEtale.inclusion B S hS ⋙
        AlgebraicGeometry.BigEtaleOver.forget B S hS)⟩
    rwa [hmap]
  have hgen : Sieve.generate E.presieve₀ ∈ K X := by
    exact Precoverage.generate_mem_toGrothendieck
      (J := AlgebraicGeometry.SmallEtale.precoverage B S hS) ⟨E, rfl, hE⟩
  apply K.superset_covering ?_ hgen
  rw [Sieve.generate_le_iff]
  rintro Y f ⟨i⟩
  let Aobj : AlgebraicGeometry.SmallAffineEtale B S hS :=
    ⟨E.X i, by
      show IsAffine ((V.map B.inclusion).X i)
      have : IsAffine (U.X (β i)) := by
        show IsAffine (A.openCover.X (β i).down)
        infer_instance
      exact IsAffine.of_isIso (e i).hom⟩
  exact ⟨⟨Aobj, 𝟙 _, E.f i, by simp [Aobj]⟩⟩

private theorem finite_standard_refinement
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (T : B.Scheme)
    [IsAffine (B.inclusion.obj T)]
    (E : PreZeroHypercover T) (hE : B.IsCovering ⟨T, E⟩) :
    ∃ F : PreZeroHypercover T,
      B.IsCovering ⟨T, F⟩ ∧ Finite F.I₀ ∧
        (∀ i, IsAffine (B.inclusion.obj (F.X i))) ∧
        (∀ i, ∃ j, ∃ g : F.X i ⟶ E.X j, g ≫ E.f j = F.f i) ∧
        (∀ i, Etale (B.inclusion.map (F.f i))) := by
  let T' := B.inclusion.obj T
  let U : Scheme.Cover Scheme.etalePrecoverage T' := {
    I₀ := E.I₀
    X i := B.inclusion.obj (E.X i)
    f i := B.inclusion.map (E.f i)
    mem₀ := by
      show (E.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage T'
      exact hE.1 }
  obtain ⟨V, q, hfin, hopen⟩ := finite_affine_refinement_etaleCover U
  let Q : PreZeroHypercover T := {
    I₀ := V.cover.I₀
    X i := by
      have : IsOpenImmersion (q.h₀ i) := hopen i
      exact B.obj (V.cover.X i)
        (Scheme.size_lt_of_isOpenImmersion (q.h₀ i) (E.X (q.s₀ i)).property)
    f i := by
      have : IsOpenImmersion (q.h₀ i) := hopen i
      exact B.inclusion.preimage (show
        B.inclusion.obj (B.obj (V.cover.X i)
          (Scheme.size_lt_of_isOpenImmersion (q.h₀ i) (E.X (q.s₀ i)).property)) ⟶
          B.inclusion.obj T from V.f i) }
  have hQf (i : Q.I₀) : B.inclusion.map (Q.f i) = V.f i := Functor.map_preimage _ _
  have hQ : AlgebraicGeometry.IsEtaleCovering ⟨T, Q⟩ := by
    show (Q.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj T)
    rw [show Q.map B.inclusion = V.cover.toPreZeroHypercover by
      ext
      case f =>
        simp only [Q, Scheme.AffineCover.cover, PreZeroHypercover.map, ObjectProperty.ι_obj]
        refine heq_of_eq (funext fun i => ?_)
        exact hQf i
      all_goals simp [Q, Scheme.AffineCover.cover, PreZeroHypercover.map]]
    simpa [T', Scheme.etalePrecoverage] using V.cover.mem₀
  obtain ⟨R, hR, hcomb⟩ := B.exists_covering_rep ⟨T, Q⟩ hQ
  rcases R with ⟨Rtarget, Rfam⟩
  have htarget : T = Rtarget := hcomb.1
  cases htarget
  have hcomb' : PreZeroHypercover.CombinatoriallyEquivalent Q Rfam := hcomb.2
  let F := deduplicateFamily Q
  have hFet : AlgebraicGeometry.IsEtaleCovering ⟨T, F⟩ := by
    show (F.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj T)
    rw [PreZeroHypercover.presieve₀_map, deduplicateFamily_presieve₀,
      ← PreZeroHypercover.presieve₀_map]
    exact hQ
  have hF : B.IsCovering ⟨T, F⟩ :=
    ⟨hFet, (deduplicateFamily_card_le hcomb').trans hR.2⟩
  have : Finite Q.I₀ := by
    simpa [Q, Scheme.AffineCover.cover] using hfin
  have hFaff : ∀ i, IsAffine (B.inclusion.obj (F.X i)) := by
    intro i
    obtain ⟨k, rfl⟩ := deduplicateFamily_index Q i
    exact isAffine_Spec (V.X k)
  have hFrefine : ∀ i, ∃ j, ∃ g : F.X i ⟶ E.X j,
      g ≫ E.f j = F.f i := by
    intro i
    obtain ⟨k, rfl⟩ := deduplicateFamily_index Q i
    let g := B.inclusion.preimage (show
      B.inclusion.obj (Q.X k) ⟶ B.inclusion.obj (E.X (q.s₀ k)) from q.h₀ k)
    have htri : g ≫ E.f (q.s₀ k) = Q.f k := by
      apply B.inclusion.map_injective
      rw [Functor.map_comp, Functor.map_preimage, hQf k]
      simpa [Q, T', U, Scheme.AffineCover.cover] using q.w₀ k
    exact ⟨q.s₀ k, g, by simpa [F, deduplicateFamily] using htri⟩
  have hQetale : ∀ i, Etale (B.inclusion.map (Q.f i)) := by
    intro i
    have hEtale : ∀ j, Etale (B.inclusion.map (E.f j)) :=
      (Scheme.presieve₀_mem_precoverage_iff (E.map B.inclusion)).mp hE.1 |>.2
    have : IsOpenImmersion (q.h₀ i) := hopen i
    have : Etale (U.f (q.s₀ i)) := hEtale (q.s₀ i)
    have h : Etale (q.h₀ i ≫ U.f (q.s₀ i)) := by infer_instance
    rw [q.w₀ i] at h
    rwa [hQf i]
  have hFetale : ∀ i, Etale (B.inclusion.map (F.f i)) := by
    intro i
    obtain ⟨k, rfl⟩ := deduplicateFamily_index Q i
    simpa [F, deduplicateFamily] using hQetale k
  exact ⟨F, hF, deduplicateFamily_finite Q, hFaff, hFrefine, hFetale⟩

private theorem finite_affine_pullback_refinement
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : AlgebraicGeometry.BigAffineEtale B S hS)
    (hXet : Etale (B.inclusion.map (X.obj.hom)))
    {U : AlgebraicGeometry.BigEtaleOver B S hS}
    (a : (AlgebraicGeometry.BigAffineEtale.inclusion B S hS).obj X ⟶ U)
    (E : PreZeroHypercover U)
    (hE : B.IsCovering ⟨U.left, E.map (AlgebraicGeometry.BigEtaleOver.forget B S hS)⟩) :
    ∃ F : PreZeroHypercover.{u + 1} X,
      AlgebraicGeometry.BigAffineEtale.IsCovering B S hS ⟨X, F⟩ ∧
      (∀ i, Sieve.generate E.presieve₀
        ((AlgebraicGeometry.BigAffineEtale.inclusion B S hS).map (F.f i) ≫ a)) ∧
      (∀ i, Etale (B.inclusion.map
        ((AlgebraicGeometry.BigAffineEtale.inclusion B S hS).obj (F.X i)).hom)) := by
  let G := AlgebraicGeometry.BigAffineEtale.inclusion B S hS
  let forget := AlgebraicGeometry.BigEtaleOver.forget B S hS
  let E₀ := E.map forget
  obtain ⟨P, π₁, π₂, hpb, hcov⟩ := B.coverings_isSite.2.2
    ⟨U.left, E₀⟩ hE (G.obj X).left a.left
  let P₀ : PreZeroHypercover (G.obj X).left := {
    I₀ := E₀.I₀
    X i := P i
    f i := π₂ i
  }
  have hcov₀ : B.IsCovering ⟨(G.obj X).left, P₀⟩ := by
    simpa [P₀, E₀, PreZeroHypercover.map] using hcov
  have : IsAffine (B.inclusion.obj (G.obj X).left) := X.property
  obtain ⟨F, hF, hfinite, hFaff, hrefine, hFetale⟩ :=
    finite_standard_refinement B (G.obj X).left P₀ hcov₀
  let F' : PreZeroHypercover.{u + 1} X := {
    I₀ := F.I₀
    X i := ⟨Over.mk (F.f i ≫ (G.obj X).hom), hFaff i⟩
    f i := ObjectProperty.homMk (Over.homMk (F.f i) (by rfl))
  }
  have hF' : AlgebraicGeometry.BigAffineEtale.IsCovering B S hS ⟨X, F'⟩ := by
    simpa [AlgebraicGeometry.BigAffineEtale.IsCovering,
      AlgebraicGeometry.BigEtaleOver.IsStandardEtaleCovering,
      AlgebraicGeometry.BigEtaleOver.IsCovering,
      F', G, forget, PreZeroHypercover.map] using
        (show B.IsCovering ⟨(G.obj X).left, F.map (𝟭 _)⟩ ∧
          IsAffine ((AlgebraicGeometry.BigEtaleOver.toScheme B S hS).obj (G.obj X)) ∧
          Finite F.I₀ ∧ ∀ i, IsAffine (B.inclusion.obj (F.X i)) from
          ⟨hF, X.property, hfinite, hFaff⟩)
  have hFstruct : ∀ i, Etale (B.inclusion.map (F.f i ≫ (G.obj X).hom)) := by
    intro i
    have := hFetale i
    have : Etale (B.inclusion.map (G.obj X).hom) := hXet
    exact Etale.etale_comp (B.inclusion.map (F.f i)) (B.inclusion.map (G.obj X).hom)
  refine ⟨F', hF', ?_, ?_⟩
  · intro i
    obtain ⟨j, g, hg⟩ := hrefine i
    have hpbw : π₁ j ≫ (E.f j).left = π₂ j ≫ a.left := by
      simpa [E₀, PreZeroHypercover.map, forget] using (hpb j).w
    let l : G.obj (F'.X i) ⟶ E.X j := Over.homMk (g ≫ π₁ j) (by
      calc
        (g ≫ π₁ j) ≫ (E.X j).hom =
            (g ≫ π₁ j ≫ (E.f j).left) ≫ U.hom := by
              rw [← (E.f j).w]
              exact (Category.assoc _ _ _).symm
        _ = (g ≫ π₂ j ≫ a.left) ≫ U.hom := by simp only [Category.assoc, hpbw]
        _ = F.f i ≫ (G.obj X).hom := by
          rw [← Category.assoc, hg]
          exact congrArg (fun t => F.f i ≫ t) a.w)
    have hl : l ≫ E.f j = G.map (F'.f i) ≫ a := by
      apply Over.OverMorphism.ext
      show (g ≫ π₁ j) ≫ (E.f j).left = F.f i ≫ a.left
      calc
        (g ≫ π₁ j) ≫ (E.f j).left = g ≫ π₁ j ≫ (E.f j).left := Category.assoc _ _ _
        _ = g ≫ (π₂ j ≫ a.left) := by rw [hpbw]
        _ = F.f i ≫ a.left := by rw [← Category.assoc, hg]
    exact ⟨E.X j, l, E.f j, ⟨j⟩, hl⟩
  · intro i
    simpa [F'] using hFstruct i

/-- The inclusion of the small affine étale site of `S` into its small étale site is
cocontinuous ([Stacks, Tag 04HR]). -/
theorem smallAffineEtale_inclusion_isCocontinuous
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (AlgebraicGeometry.SmallAffineEtale.inclusion B S hS).IsCocontinuous
      (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
      (AlgebraicGeometry.SmallEtale.topology B S hS) := by
  let G := AlgebraicGeometry.SmallAffineEtale.inclusion B S hS
  let J := AlgebraicGeometry.SmallAffineEtale.topology B S hS
  constructor
  have hSat : ∀ {Y : AlgebraicGeometry.SmallEtale B S hS} {R : Sieve Y},
      (AlgebraicGeometry.SmallEtale.precoverage B S hS).Saturate Y R →
      ∀ (X : AlgebraicGeometry.SmallAffineEtale B S hS)
        (a : G.obj X ⟶ Y), (R.pullback a).functorPullback G ∈ J X := by
    intro Y R hR
    induction hR with
    | of Y P hP =>
      intro X a
      obtain ⟨E, hEq, hE⟩ := (AlgebraicGeometry.SmallEtale.mem_precoverage_iff B S hS).mp hP
      subst P
      let Xbig : AlgebraicGeometry.BigAffineEtale B S hS :=
        ⟨(AlgebraicGeometry.SmallEtale.inclusion B S hS).obj (G.obj X), by
          show IsAffine ((AlgebraicGeometry.SmallEtale.toScheme B S hS).obj (G.obj X))
          exact X.property⟩
      let Yover := (AlgebraicGeometry.SmallEtale.inclusion B S hS).obj Y
      let Eover := E.map (AlgebraicGeometry.SmallEtale.inclusion B S hS)
      have hEover : B.IsCovering ⟨Y.obj.left,
          Eover.map (AlgebraicGeometry.BigEtaleOver.forget B S hS)⟩ := by
        simpa [Eover, AlgebraicGeometry.SmallEtale.IsCovering,
          AlgebraicGeometry.BigEtaleOver.IsCovering] using hE
      have hstruct : Etale (B.inclusion.map ((G.obj X).obj.hom)) :=
        (G.obj X).property
      let aover : (AlgebraicGeometry.BigAffineEtale.inclusion B S hS).obj Xbig ⟶ Yover :=
        (AlgebraicGeometry.SmallEtale.inclusion B S hS).map a
      obtain ⟨F, hF, hRef, hEtale⟩ :=
        finite_affine_pullback_refinement B S hS Xbig hstruct aover Eover hEover
      let Fsmall : PreZeroHypercover X := {
        I₀ := F.I₀
        X i := ⟨⟨(F.X i).obj, hEtale i⟩, by
          show IsAffine ((AlgebraicGeometry.BigEtaleOver.toScheme B S hS).obj (F.X i).obj)
          exact (F.X i).property⟩
        f i := ObjectProperty.homMk (ObjectProperty.homMk
          ((AlgebraicGeometry.BigAffineEtale.inclusion B S hS).map (F.f i)))
      }
      have hRefSmall (i : F.I₀) :
          Sieve.generate E.presieve₀
            (((AlgebraicGeometry.SmallAffineEtale.inclusion B S hS).map (Fsmall.f i)) ≫ a) := by
        have hi := hRef i
        simp only [Sieve.generate_apply] at hi ⊢
        obtain ⟨Z, g, t, ht, hcomp⟩ := hi
        obtain ⟨j⟩ := ht
        let gs := (AlgebraicGeometry.SmallEtale.inclusion B S hS).preimage
          (show (AlgebraicGeometry.SmallEtale.inclusion B S hS).obj
            ((AlgebraicGeometry.SmallAffineEtale.inclusion B S hS).obj (Fsmall.X i)) ⟶
              (AlgebraicGeometry.SmallEtale.inclusion B S hS).obj (E.X j) from g)
        refine ⟨E.X j, gs, E.f j, ⟨j⟩, ?_⟩
        apply (AlgebraicGeometry.SmallEtale.inclusion B S hS).map_injective
        rw [Functor.map_comp,
          Functor.map_preimage (AlgebraicGeometry.SmallEtale.inclusion B S hS)]
        simpa [Fsmall, aover, Yover, Eover, PreZeroHypercover.map,
          AlgebraicGeometry.SmallAffineEtale.inclusion,
          AlgebraicGeometry.BigAffineEtale.inclusion,
          AlgebraicGeometry.SmallEtale.inclusion] using hcomp
      have hFmap : Fsmall.map
          (AlgebraicGeometry.SmallAffineEtale.inclusion B S hS ⋙
            AlgebraicGeometry.SmallEtale.inclusion B S hS) =
          F.map (AlgebraicGeometry.BigAffineEtale.inclusion B S hS) := by
        ext <;> rfl
      have hFsmall : AlgebraicGeometry.SmallAffineEtale.IsCovering B S hS ⟨X, Fsmall⟩ := by
        constructor
        · show AlgebraicGeometry.BigEtaleOver.IsCovering B S hS
            ⟨(AlgebraicGeometry.SmallEtale.inclusion B S hS).obj (G.obj X),
              Fsmall.map (AlgebraicGeometry.SmallAffineEtale.inclusion B S hS ⋙
                AlgebraicGeometry.SmallEtale.inclusion B S hS)⟩
          rw [hFmap]
          exact hF.1
        · exact hF.2.2.1
      have hJ : Sieve.generate Fsmall.presieve₀ ∈ J X := by
        exact Precoverage.generate_mem_toGrothendieck
          (J := AlgebraicGeometry.SmallAffineEtale.precoverage B S hS) ⟨Fsmall, rfl, hFsmall⟩
      apply J.superset_covering ?_ hJ
      rw [Sieve.generate_le_iff]
      rintro Z f ⟨i⟩
      exact hRefSmall i
    | top Y =>
      intro X a
      simp
    | pullback Y T hT Z f ih =>
      intro X a
      rw [← Sieve.pullback_comp]
      exact ih X (a ≫ f)
    | transitive Y T Q hT hQ ihT ihQ =>
      intro X a
      apply J.transitive (ihT X a)
      intro X' f hf
      rw [← Sieve.functorPullback_pullback]
      simpa [← Sieve.pullback_comp, Category.assoc] using ihQ hf X' (𝟙 _)
  intro X R hR
  change (AlgebraicGeometry.SmallEtale.precoverage B S hS).Saturate (G.obj X) R at hR
  simpa [G] using hSat hR X (𝟙 _)

/-- The inclusion of the small affine étale site of a scheme into its small étale site is a special
cocontinuous functor. -/
@[stacks 04HR]
public theorem SmallAffineEtale.inclusion_isSpecialCocontinuous
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    IsSpecialCocontinuous
      (AlgebraicGeometry.SmallAffineEtale.topology B S hS)
      (AlgebraicGeometry.SmallEtale.topology B S hS)
      (AlgebraicGeometry.SmallAffineEtale.inclusion B S hS) := by
  let G := AlgebraicGeometry.SmallAffineEtale.inclusion B S hS
  let P := AlgebraicGeometry.SmallAffineEtale.precoverage B S hS
  let J := AlgebraicGeometry.SmallAffineEtale.topology B S hS
  let K := AlgebraicGeometry.SmallEtale.topology B S hS
  have : G.IsCoverDense K := by
    simpa [G, K] using smallAffineEtale_isCoverDense B S hS
  have hco : G.IsCocontinuous J K :=
    smallAffineEtale_inclusion_isCocontinuous B S hS
  have hPmap : P ≤ (K.toPrecoverage).comap G := by
    intro X R hR
    obtain ⟨E, hEq, hCover⟩ :=
      (AlgebraicGeometry.SmallAffineEtale.mem_precoverage_iff B S hS).mp hR
    rw [Precoverage.mem_comap_iff, hEq, ← PreZeroHypercover.presieve₀_map,
      GrothendieckTopology.mem_toPrecoverage_iff]
    exact (AlgebraicGeometry.SmallEtale.precoverage B S hS).generate_mem_toGrothendieck
      ((AlgebraicGeometry.SmallEtale.mem_precoverage_iff B S hS).2
        ⟨E.map G, rfl, hCover.1⟩)
  have hle : J ≤ G.restrictedTopology K := by
    show P.toGrothendieck ≤ ((K.toPrecoverage).comap G).toGrothendieck
    exact Precoverage.toGrothendieck_monotone hPmap
  have hge : G.restrictedTopology K ≤ J := by
    intro X R hR
    have hpush : R.functorPushforward G ∈ K (G.obj X) :=
      (Functor.mem_restrictedTopology_iff (G := G) (K := K)).mp hR
    have hpull := Functor.cover_lift (G := G) (J := J) (K := K) hpush
    rwa [Sieve.functorPullback_functorPushforward_eq] at hpull
  show G.IsCocontinuous J K ∧ G.IsDenseSubsite J K
  refine ⟨hco, ?_⟩
  rw [le_antisymm hle hge]
  infer_instance

namespace SmallEtale

/-- The small étale site of a scheme has enough points. -/
@[stacks 06VX "small_etale"]
public lemma hasConservativeFamily (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (AlgebraicGeometry.SmallEtale.topology B S hS).HasConservativeFamily.{u} := by
  let J := AlgebraicGeometry.SmallAffineEtale.topology B S hS
  let K := AlgebraicGeometry.SmallEtale.topology B S hS
  let G := AlgebraicGeometry.SmallAffineEtale.inclusion B S hS
  have hSpec := AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS
  have : G.IsCocontinuous J K := hSpec.1
  have : G.IsDenseSubsite J K := hSpec.2
  exact CategoryTheory.hasConservativeFamily_of_denseSubsite.{u + 1, u + 1, u} J K G
    (AlgebraicGeometry.smallAffineEtale_hasConservativeFamily B S hS)

end SmallEtale

end AlgebraicGeometry
