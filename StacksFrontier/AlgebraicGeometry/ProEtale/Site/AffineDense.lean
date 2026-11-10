module

public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Slices
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp
public import StacksCore.Tactic.StacksAttribute

/-!
# Affine objects form a dense subsite of the big pro-étale site

Let `B` be a big pro-étale site containing a scheme `S`. The inclusion of affine
objects over `S` into the big pro-étale site over `S` is special cocontinuous
and induces an equivalence of their topoi of sheaves.

## Main results

* `AlgebraicGeometry.ProEtale.inclusion_isSpecialCocontinuous` gives the special cocontinuity
  of the affine inclusion.

## Implementation notes

The predicate `IsSpecialCocontinuous` records cocontinuity and the dense-subsite
property. The latter supplies the equivalence of sheaf categories induced by
the inclusion, hence the equivalence of topoi in the source.

## References

* [Stacks Project, Tag 098N](https://stacks.math.columbia.edu/tag/098N)
-/

@[expose] public section

open CategoryTheory

universe u u₁ v₁

namespace AlgebraicGeometry.ProEtale

/-- Every index of the deduplication of a covering family comes from an index of the family,
with the same source object and the same morphism. -/
private theorem exists_eq_of_mem_shrink
    {C : Type*} [Category C] {T : C} (E : PreZeroHypercover T) (p : E.shrink.I₀) :
    ∃ i, (⟨E.X i, E.f i⟩ : Σ Y : C, Y ⟶ T) = p.1 := by
  obtain ⟨⟨Y, f⟩, hf⟩ := p
  obtain ⟨i⟩ := hf
  exact ⟨i, rfl⟩

/-- Deduplicating a finitely indexed covering family leaves it finitely indexed. -/
private theorem finite_shrink {C : Type*} [Category C] {T : C} (E : PreZeroHypercover T)
    [Finite E.I₀] : Finite E.shrink.I₀ := by
  classical
  refine Finite.of_surjective E.toShrink.s₀ fun p => ?_
  obtain ⟨i, hi⟩ := exists_eq_of_mem_shrink E p
  exact ⟨i, Subtype.ext hi⟩

/-- The deduplication of a covering family has at most as many indices as any family
combinatorially equivalent to it. -/
private theorem mk_shrink_I₀_le {C : Type u₁} [Category.{v₁} C] {T : C}
    {E F : PreZeroHypercover.{max u₁ v₁} T}
    (h : PreZeroHypercover.CombinatoriallyEquivalent E F) :
    Cardinal.mk E.shrink.I₀ ≤ Cardinal.mk F.I₀ := by
  classical
  obtain ⟨α, hX, hf⟩ := h.1
  let rep (p : E.shrink.I₀) : E.I₀ := Classical.choose (exists_eq_of_mem_shrink E p)
  let m (p : E.shrink.I₀) : F.I₀ := α (rep p)
  have hm : Function.Injective m := by
    intro p q hpq
    apply Subtype.ext
    calc
      p.1 = ⟨E.X (rep p), E.f (rep p)⟩ :=
        (Classical.choose_spec (exists_eq_of_mem_shrink E p)).symm
      _ = ⟨E.X (rep q), E.f (rep q)⟩ :=
        pair_eq_of_combIndex_eq α hX hf (rep p) (rep q) hpq
      _ = q.1 := Classical.choose_spec (exists_eq_of_mem_shrink E q)
  exact Cardinal.mk_le_of_injective hm

/-- Transporting a family built from preimages of morphisms under the inclusion of the big site
recovers the original family. -/
private theorem map_inclusion_mk_preimage (B : BigProetaleSite.{u}) {T : B.Scheme}
    {ι : Type (u + 1)} (X : ι → B.Scheme) (g : ∀ i, B.inclusion.obj (X i) ⟶ B.inclusion.obj T) :
    ({ I₀ := ι, X := X, f := fun i => B.inclusion.preimage (g i) } :
      PreZeroHypercover T).map B.inclusion =
      { I₀ := ι, X := fun i => B.inclusion.obj (X i), f := g } := by
  ext
  · rfl
  · exact heq_of_eq rfl
  · exact heq_of_eq (funext fun i => Functor.map_preimage B.inclusion (g i))

/-- A quasi-compact weakly étale covering of an affine scheme is refined by a weakly étale
covering with finitely many affine members, each mapping to a member of the given covering by
an open immersion. -/
private theorem finite_affine_refinement_proetaleCover
    {T : Scheme.{u}} [IsAffine T]
    (U : Scheme.Cover (Scheme.propQCPrecoverage @WeaklyEtale) T) :
    ∃ (V : Scheme.AffineCover @WeaklyEtale T)
      (f : V.cover ⟶ U.weaken Scheme.propQCPrecoverage_le_precoverage),
      Finite V.I₀ ∧ ∀ i, IsOpenImmersion (f.h₀ i) := by
  let : MorphismProperty.RespectsLeft @WeaklyEtale @IsOpenImmersion := by
    constructor
    intro A C D i hi f hf
    exact inferInstance
  let U' : Scheme.Cover (Scheme.precoverage @WeaklyEtale) T :=
    U.weaken Scheme.propQCPrecoverage_le_precoverage
  let : QuasiCompactCover U.toPreZeroHypercover := by
    rw [← Scheme.presieve₀_mem_qcPrecoverage_iff]
    exact U.mem₀.1
  let : QuasiCompactCover U'.toPreZeroHypercover := by
    simpa [U'] using (inferInstance : QuasiCompactCover U.toPreZeroHypercover)
  exact QuasiCompactCover.exists_hom U'

/-- A pro-étale covering of an affine object of the big category is refined by a chosen
covering family with finitely many indices, all of whose source schemes are affine. -/
theorem finite_standard_refinement
    (B : BigProetaleSite.{u}) (T : B.Scheme)
    [IsAffine (B.inclusion.obj T)]
    (E : PreZeroHypercover T) (hE : B.IsProetaleCovering ⟨T, E⟩) :
    ∃ F : PreZeroHypercover T,
      B.covering ⟨T, F⟩ ∧ Finite F.I₀ ∧
        (∀ i, IsAffine (B.inclusion.obj (F.X i))) ∧
        ∀ i, ∃ j, ∃ g : F.X i ⟶ E.X j, g ≫ E.f j = F.f i := by
  let T' := B.inclusion.obj T
  let U : Scheme.Cover (Scheme.propQCPrecoverage @WeaklyEtale) T' := {
    I₀ := E.I₀
    X i := B.inclusion.obj (E.X i)
    f i := B.inclusion.map (E.f i)
    mem₀ := by
      change (E.map B.inclusion).presieve₀ ∈ Scheme.proetalePrecoverage T'
      exact hE }
  obtain ⟨V, q, hfin, hopen⟩ := finite_affine_refinement_proetaleCover U
  let : Scheme.JointlySurjective (Scheme.precoverage @WeaklyEtale) := by
    constructor
    intro X R hR x
    change R ∈ Scheme.jointlySurjectivePrecoverage X ∧ _ at hR
    rw [Scheme.jointlySurjectivePrecoverage,
      Presieve.mem_comap_jointlySurjectivePrecoverage_iff] at hR
    exact hR.1 x
  let Q : PreZeroHypercover T := {
    I₀ := V.cover.I₀
    X i := ⟨Spec (V.X i),
      @Scheme.size_lt_of_isOpenImmersion B.cutoff (Spec (V.X i))
        (B.inclusion.obj (E.X (q.s₀ i))) (q.h₀ i) (hopen i)
        (E.X (q.s₀ i)).property⟩
    f i := B.inclusion.preimage (show
      B.inclusion.obj (⟨Spec (V.X i),
        @Scheme.size_lt_of_isOpenImmersion B.cutoff (Spec (V.X i))
          (B.inclusion.obj (E.X (q.s₀ i))) (q.h₀ i) (hopen i)
          (E.X (q.s₀ i)).property⟩ : B.Scheme) ⟶
        B.inclusion.obj T from V.f i) }
  have hQ : B.IsProetaleCovering ⟨T, Q⟩ := by
    change (Q.map B.inclusion).presieve₀ ∈ Scheme.proetalePrecoverage (B.inclusion.obj T)
    rw [show Q.map B.inclusion = V.cover.toPreZeroHypercover from
      map_inclusion_mk_preimage B _ _]
    change V.cover.presieve₀ ∈ Scheme.propQCPrecoverage @WeaklyEtale (B.inclusion.obj T)
    change V.cover.presieve₀ ∈
      ((Scheme.qcPrecoverage ⊓ Scheme.precoverage @WeaklyEtale) (B.inclusion.obj T))
    refine ⟨?_, V.cover.mem₀⟩
    let : Finite V.cover.I₀ := by simpa [Scheme.AffineCover.cover] using hfin
    let : ∀ i, IsAffine (V.cover.X i) := fun i => isAffine_Spec (V.X i)
    let : ∀ i, IsAffineHom (V.cover.f i) := by
      intro i
      infer_instance
    exact Scheme.presieve₀_mem_qcPrecoverage_iff.mpr QuasiCompactCover.of_finite
  obtain ⟨R, hR, hcomb⟩ := B.covering_representatives ⟨T, Q⟩ hQ
  rcases R with ⟨Rtarget, Rfam⟩
  have htarget : T = Rtarget := hcomb.1
  cases htarget
  have hcomb' : PreZeroHypercover.CombinatoriallyEquivalent Q Rfam := hcomb.2
  have hFpro : B.IsProetaleCovering ⟨T, Q.shrink⟩ := by
    change (Q.shrink.map B.inclusion).presieve₀ ∈
      Scheme.proetalePrecoverage (B.inclusion.obj T)
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀_shrink,
      ← PreZeroHypercover.presieve₀_map]
    exact hQ
  let : Finite Q.I₀ := by simpa [Q, Scheme.AffineCover.cover] using hfin
  have hFdata : ∀ i, IsAffine (B.inclusion.obj (Q.shrink.X i)) ∧
      ∃ j, ∃ g : Q.shrink.X i ⟶ E.X j, g ≫ E.f j = Q.shrink.f i := by
    intro i
    obtain ⟨k, hk⟩ := exists_eq_of_mem_shrink Q i
    have hi : i = Q.toShrink.s₀ k := Subtype.ext hk.symm
    subst i
    constructor
    · change IsAffine (B.inclusion.obj (Q.X k))
      change IsAffine (Spec (V.X k))
      exact isAffine_Spec (V.X k)
    let g := B.inclusion.preimage (show
      B.inclusion.obj (Q.X k) ⟶ B.inclusion.obj (E.X (q.s₀ k)) from q.h₀ k)
    have htri : g ≫ E.f (q.s₀ k) = Q.f k := by
      apply B.inclusion.map_injective
      dsimp [g]
      change B.inclusion.map (g ≫ E.f (q.s₀ k)) =
        B.inclusion.map (B.inclusion.preimage (show
          B.inclusion.obj (Q.X k) ⟶ B.inclusion.obj T from V.f k))
      rw [Functor.map_comp, Functor.map_preimage, Functor.map_preimage]
      exact q.w₀ k
    exact ⟨q.s₀ k, g, htri⟩
  exact ⟨Q.shrink, ⟨hFpro, (mk_shrink_I₀_le hcomb').trans hR.2⟩, finite_shrink Q,
    fun i => (hFdata i).1, fun i => (hFdata i).2⟩

/-- A covering of an object `U` of the big category over `S` pulls back, along a morphism to
`U` from an affine object `X`, to a standard affine covering of `X` each of whose members
factors through the given covering. -/
private theorem finite_affine_pullback_refinement
    (B : BigProetaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : BigAffineProetale B S hS)
    {U : BigProetaleOver B S hS}
    (a : (BigAffineProetale.inclusion B S hS).obj X ⟶ U)
    (E : PreZeroHypercover.{u + 1} U)
    (hE : BigProetaleOver.IsCovering B S hS
      ⟨U, E⟩) :
    ∃ F : PreZeroHypercover.{u + 1} X,
      BigAffineProetale.IsCovering B S hS ⟨X, F⟩ ∧
      ∀ i, Sieve.generate E.presieve₀
        ((BigAffineProetale.inclusion B S hS).map (F.f i) ≫ a) := by
  let G := BigAffineProetale.inclusion B S hS
  let forget := BigProetaleOver.forget B S hS
  let E₀ : PreZeroHypercover.{u + 1} U.left := E.map forget
  have hE₀ : B.covering ⟨U.left, E₀⟩ := hE
  obtain ⟨P, π₁, π₂, hpb, hcov⟩ := B.covering_isSite.2.2
    ⟨U.left, E₀⟩ hE₀ (G.obj X).left a.left
  let P₀ : PreZeroHypercover.{u + 1} (G.obj X).left := {
    I₀ := E₀.I₀
    X i := P i
    f i := π₂ i
  }
  have hcov₀ : B.IsProetaleCovering ⟨(G.obj X).left, P₀⟩ := by
    apply (B.isProetaleCovering_iff ⟨(G.obj X).left, P₀⟩).2
    simpa [P₀, E₀, PreZeroHypercover.map] using hcov.1
  let : IsAffine (B.inclusion.obj (G.obj X).left) := X.property
  obtain ⟨F, hF, hfinite, hFaff, hrefine⟩ :=
    finite_standard_refinement B (G.obj X).left P₀ hcov₀
  let F' : PreZeroHypercover.{u + 1} X := {
    I₀ := F.I₀
    X i := ⟨Over.mk (F.f i ≫ (G.obj X).hom), hFaff i⟩
    f i := ObjectProperty.homMk (Over.homMk (F.f i) (by rfl))
  }
  have hF' : BigAffineProetale.IsCovering B S hS ⟨X, F'⟩ := by
    simpa [BigAffineProetale.IsCovering,
      BigProetaleOver.IsCovering, F', G, forget,
      PreZeroHypercover.map] using
        (show B.covering ⟨(G.obj X).left, F.map (𝟭 _)⟩ ∧ Finite F.I₀ from
          ⟨hF, hfinite⟩)
  refine ⟨F', hF', ?_⟩
  intro i
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
    change (g ≫ π₁ j) ≫ (E.f j).left = F.f i ≫ a.left
    calc
      (g ≫ π₁ j) ≫ (E.f j).left = g ≫ π₁ j ≫ (E.f j).left := Category.assoc _ _ _
      _ = g ≫ (π₂ j ≫ a.left) := by rw [hpbw]
      _ = F.f i ≫ a.left := by rw [← Category.assoc, hg]
  exact ⟨E.X j, l, E.f j, ⟨j⟩, hl⟩

/-- The inclusion of the affine objects over `S` into the big pro-étale category over `S` is
cocontinuous. -/
private theorem affine_inclusion_isCocontinuous
    (B : BigProetaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (BigAffineProetale.inclusion B S hS).IsCocontinuous
      (BigAffineProetale.topology B S hS)
      (BigProetaleOver.topology B S hS) := by
  let G := BigAffineProetale.inclusion B S hS
  let J := BigAffineProetale.topology B S hS
  constructor
  intro X R hR
  rw [CategoryTheory.GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨E, hE, hER⟩ := (B.mem_topology_iff (Sieve.overEquiv (G.obj X) R)).mp hR
  let Eover : PreZeroHypercover.{u + 1} (G.obj X) := {
    I₀ := E.I₀
    X i := Over.mk (E.f i ≫ (G.obj X).hom)
    f i := Over.homMk (E.f i) (by rfl)
  }
  have hEover : BigProetaleOver.IsCovering B S hS ⟨(G.obj X), Eover⟩ := by
    change B.covering ⟨(G.obj X).left, _⟩
    simpa [Eover, PreZeroHypercover.map, BigProetaleOver.forget] using hE
  obtain ⟨F, hF, hrefine⟩ :=
    finite_affine_pullback_refinement B S hS X (𝟙 _) Eover hEover
  have hJ : Sieve.generate F.presieve₀ ∈ J X := by
    change Sieve.generate F.presieve₀ ∈
      (BigAffineProetale.precoverage B S hS).toGrothendieck X
    exact Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hF⟩
  apply J.superset_covering ?_ hJ
  rw [Sieve.generate_le_iff]
  intro Y f hf
  obtain ⟨i⟩ := hf
  change R (G.map (F.f i))
  have hi := hrefine i
  rw [Sieve.generate_apply] at hi
  rcases hi with ⟨Z, l, t, ht, hl⟩
  obtain ⟨j⟩ := ht
  have hRj : R (Eover.f j) := (Sieve.overEquiv_iff R (E.f j)).mp (hER _ _ ⟨j⟩)
  have hcomp : l ≫ Eover.f j = G.map (F.f i) := by
    simpa [G, BigAffineProetale.inclusion] using hl
  have hRfi : R.arrows (G.map (F.f i)) := by
    rw [← hcomp]
    exact R.downward_closed hRj l
  simpa using hRfi

/-- The affine objects over `S` are cover-dense in the big pro-étale category over `S`: every
object of the latter is covered by affine ones. -/
private theorem affine_inclusion_isCoverDense
    (B : BigProetaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (BigAffineProetale.inclusion B S hS).IsCoverDense
      (BigProetaleOver.topology B S hS) := by
  let G := BigAffineProetale.inclusion B S hS
  constructor
  intro X
  let T := B.inclusion.obj X.left
  let A := T.affineOpenCover
  let U : T.OpenCover.{u + 1} := {
    I₀ := ULift.{u + 1, u} A.openCover.I₀
    X i := A.openCover.X i.down
    f i := A.openCover.f i.down
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨?_, ?_⟩
      · intro x
        obtain ⟨i, y, hy⟩ := A.openCover.exists_eq x
        exact ⟨ULift.up i, y, hy⟩
      · intro i
        exact A.openCover.map_prop i.down
  }
  let E : PreZeroHypercover.{u + 1} X.left := {
    I₀ := U.I₀
    X i := ⟨U.X i, Scheme.size_lt_of_isOpenImmersion (U.f i) X.left.property⟩
    f i := B.inclusion.preimage (U.f i)
  }
  have hmap : E.map B.inclusion = U.toPreZeroHypercover :=
    map_inclusion_mk_preimage B _ _
  have hpre : E.presieve₀ ∈ B.precoverage.coverings X.left := by
    rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff,
      ← PreZeroHypercover.presieve₀_map]
    apply Scheme.etalePrecoverage_le_proetalePrecoverage _
    apply Scheme.precoverage_mono (P := @IsOpenImmersion) (Q := @Etale)
      (fun _ _ _ _ ↦ inferInstance)
    rw [hmap]
    exact U.mem₀
  have hgen : Sieve.generate E.presieve₀ ∈ B.topology X.left := by
    change Sieve.generate E.presieve₀ ∈ B.precoverage.toGrothendieck X.left
    exact Precoverage.generate_mem_toGrothendieck hpre
  have hle : Sieve.generate E.presieve₀ ≤
      Sieve.overEquiv X (Sieve.coverByImage G X) := by
    rw [Sieve.generate_le_iff]
    intro Y f hf
    obtain ⟨i⟩ := hf
    let Ti : B.Scheme := E.X i
    let vi : Ti ⟶ X.left := E.f i
    let Ai : BigAffineProetale B S hS :=
      ⟨Over.mk (vi ≫ X.hom), by
        dsimp [Ti, E]
        change IsAffine (B.inclusion.obj (⟨U.X i,
          Scheme.size_lt_of_isOpenImmersion (U.f i) X.left.property⟩ : B.Scheme))
        change IsAffine (Spec (A.X i.down))
        exact isAffine_Spec _⟩
    let ai : G.obj Ai ⟶ X := Over.homMk
      (X := (⟨S, hS⟩ : B.Scheme)) (U := G.obj Ai) (V := X) (f := vi) (by rfl)
    exact (Sieve.overEquiv_iff (Sieve.coverByImage G X) vi).2 (Presieve.in_coverByImage G ai)
  rw [BigProetaleOver.topology, CategoryTheory.GrothendieckTopology.mem_over_iff]
  exact B.topology.superset_covering hle hgen

/-- The affine objects over `S`, with their standard coverings, form a dense subsite of the
big pro-étale site over `S`. -/
private theorem affine_inclusion_isDenseSubsite
    (B : BigProetaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    (BigAffineProetale.inclusion B S hS).IsDenseSubsite
      (BigAffineProetale.topology B S hS)
      (BigProetaleOver.topology B S hS) := by
  let G := BigAffineProetale.inclusion B S hS
  let P := BigAffineProetale.precoverage B S hS
  let J := BigAffineProetale.topology B S hS
  let K := BigProetaleOver.topology B S hS
  let : G.IsCoverDense K := affine_inclusion_isCoverDense B S hS
  have hco : G.IsCocontinuous J K := affine_inclusion_isCocontinuous B S hS
  have hPmap : P ≤ (K.toPrecoverage).comap G := by
    intro X R hR
    obtain ⟨E, hEq, hE⟩ :=
      (BigAffineProetale.mem_precoverage_iff B S hS).mp hR
    rw [Precoverage.mem_comap_iff]
    rw [hEq, ← PreZeroHypercover.presieve₀_map,
      GrothendieckTopology.mem_toPrecoverage_iff]
    have hB : B.covering
        ⟨(G.obj X).left, (E.map G).map
          (BigProetaleOver.forget B S hS)⟩ := hE.1
    have hBase : ((E.map G).map
        (BigProetaleOver.forget B S hS)).presieve₀ ∈
        B.precoverage.coverings (G.obj X).left := by
      rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff]
      rw [← PreZeroHypercover.presieve₀_map]
      simpa only [PreZeroHypercover.presieve₀_map,
        BigProetaleSite.inclusion, ObjectProperty.ι_obj] using
        (B.isProetaleCovering_iff _).mp hB.1
    have hBaseGen : Sieve.generate
        ((E.map G).map (BigProetaleOver.forget B S hS)).presieve₀ ∈
        B.topology (G.obj X).left := by
      change _ ∈ B.precoverage.toGrothendieck _
      exact Precoverage.generate_mem_toGrothendieck hBase
    change Sieve.generate (E.map G).presieve₀ ∈ K (G.obj X)
    change Sieve.generate (E.map G).presieve₀ ∈
      (B.topology.over (⟨S, hS⟩ : B.Scheme)) (G.obj X)
    rw [CategoryTheory.GrothendieckTopology.mem_over_iff]
    simpa [Sieve.overEquiv_ofArrows, PreZeroHypercover.presieve₀_map] using hBaseGen
  have hle : J ≤ G.restrictedTopology K := by
    change P.toGrothendieck ≤ ((K.toPrecoverage).comap G).toGrothendieck
    exact Precoverage.toGrothendieck_monotone hPmap
  have hge : G.restrictedTopology K ≤ J := by
    intro X R hR
    rw [Functor.mem_restrictedTopology_iff] at hR
    simpa only [Sieve.functorPullback_functorPushforward_eq] using G.cover_lift J K hR
  change G.IsDenseSubsite J K
  rw [le_antisymm hle hge]
  infer_instance

/-- **Stacks 098N.** The inclusion of the big affine pro-étale site over a
scheme into its big pro-étale site is special cocontinuous, and induces the
canonical equivalence of their topoi of sheaves. -/
@[stacks 098N]
theorem inclusion_isSpecialCocontinuous
    (B : BigProetaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    IsSpecialCocontinuous
      (BigAffineProetale.topology B S hS)
      (BigProetaleOver.topology B S hS)
      (BigAffineProetale.inclusion B S hS) := by
  change (BigAffineProetale.inclusion B S hS).IsCocontinuous
      (BigAffineProetale.topology B S hS)
      (BigProetaleOver.topology B S hS) ∧
    (BigAffineProetale.inclusion B S hS).IsDenseSubsite
      (BigAffineProetale.topology B S hS)
      (BigProetaleOver.topology B S hS)
  exact ⟨affine_inclusion_isCocontinuous B S hS,
    affine_inclusion_isDenseSubsite B S hS⟩

end AlgebraicGeometry.ProEtale
