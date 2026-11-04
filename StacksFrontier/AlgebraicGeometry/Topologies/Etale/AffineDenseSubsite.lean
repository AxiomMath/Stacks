module

public import Mathlib.AlgebraicGeometry.Cover.MorphismProperty
public import Mathlib.AlgebraicGeometry.Cover.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SiteAxioms
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp

/-!
# Affine objects form a dense subsite of the big étale site

Let `B` be a big étale site containing a scheme `S`. The inclusion of the big affine étale
category over `S` into the big étale category over `S` is a special cocontinuous functor, and
therefore induces an equivalence between their topoi of sheaves.

So the big étale topos over `S` can be computed on affine objects alone. This is the étale
analogue of the statement that a sheaf on a scheme is determined by its sections on affine
opens.

## Main results

* `AlgebraicGeometry.BigAffineEtale.inclusion_isSpecialCocontinuous` — the inclusion of affine
  objects is a special cocontinuous functor, hence a dense subsite inclusion inducing an
  equivalence of sheaf categories.

## Implementation notes

`IsSpecialCocontinuous` records cocontinuity together with the dense-subsite property; the latter
canonically supplies the induced equivalence of sheaf categories, so the single assertion
carries both conclusions of the source.

The proof turns on refining an arbitrary covering by a finite affine one. Over an affine
object, an étale covering admits a finite refinement by affine schemes: the covering is
quasi-compact because its members are open maps onto a compact space, so a finite affine
subcover exists. Transferring that refinement into the size-bounded site needs the index type
to stay small, which is why the refining family is deduplicated — reindexed by the set of
source-and-arrow pairs actually occurring — before its combinatorial representative in the
site is taken. Deduplication is also what keeps the cardinality bound of the representative
available.

Cover density is then checked on the affine open cover of each object, and cocontinuity by
induction over the saturation of the big étale precoverage: the generating case is the finite
affine refinement, and the inductive cases are formal. Identifying the affine topology with
the topology restricted along the inclusion is what upgrades cover density to the dense-subsite
property.

## References

* [Stacks Project, Tag 021E](https://stacks.math.columbia.edu/tag/021E)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

private theorem isCovering_deduplicateFamily
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {T : B.Scheme}
    (Q : PreZeroHypercover.{u + 1} T) (hQ : AlgebraicGeometry.IsEtaleCovering ⟨T, Q⟩) :
    B.IsCovering ⟨T, deduplicateFamily Q⟩ := by
  obtain ⟨R, hR, hcomb⟩ := B.exists_covering_rep ⟨T, Q⟩ hQ
  rcases R with ⟨Rtarget, Rfam⟩
  have htarget : T = Rtarget := hcomb.1
  cases htarget
  have hcomb' : PreZeroHypercover.CombinatoriallyEquivalent Q Rfam := hcomb.2
  refine ⟨?_, (deduplicateFamily_card_le hcomb').trans hR.2⟩
  show ((deduplicateFamily Q).map B.inclusion).presieve₀ ∈
    Scheme.etalePrecoverage (B.inclusion.obj T)
  rw [PreZeroHypercover.presieve₀_map, deduplicateFamily_presieve₀,
    ← PreZeroHypercover.presieve₀_map]
  exact hQ

private theorem exists_finite_affine_covering_of_isEtaleCovering
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {T : B.Scheme} (E : PreZeroHypercover T)
    (Q : PreZeroHypercover.{u + 1} T) (hQ : AlgebraicGeometry.IsEtaleCovering ⟨T, Q⟩)
    [Finite Q.I₀] (haff : ∀ k, IsAffine (B.inclusion.obj (Q.X k)))
    (hrefine : ∀ k, ∃ j, ∃ g : Q.X k ⟶ E.X j, g ≫ E.f j = Q.f k) :
    ∃ F : PreZeroHypercover T,
      B.IsCovering ⟨T, F⟩ ∧ Finite F.I₀ ∧
        (∀ i, IsAffine (B.inclusion.obj (F.X i))) ∧
        ∀ i, ∃ j, ∃ g : F.X i ⟶ E.X j, g ≫ E.f j = F.f i :=
  ⟨deduplicateFamily Q, isCovering_deduplicateFamily B Q hQ, deduplicateFamily_finite Q,
    fun ⟨_, k, hk⟩ => by subst hk; exact haff k,
    fun ⟨_, k, hk⟩ => by subst hk; exact hrefine k⟩

/-- A morphism between images of the inclusion, composed with the image of an arrow, is
determined by its image. -/
private theorem preimage_inclusion_comp_eq
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {X Y Z : B.Scheme}
    (h : B.inclusion.obj X ⟶ B.inclusion.obj Y) (g : Y ⟶ Z) (k : X ⟶ Z)
    (e : h ≫ B.inclusion.map g = B.inclusion.map k) : B.inclusion.preimage h ≫ g = k :=
  B.inclusion.map_injective (by rw [Functor.map_comp, Functor.map_preimage, e])

private theorem finite_standard_refinement
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (T : B.Scheme)
    [IsAffine (B.inclusion.obj T)]
    (E : PreZeroHypercover T) (hE : B.IsCovering ⟨T, E⟩) :
    ∃ F : PreZeroHypercover T,
      B.IsCovering ⟨T, F⟩ ∧ Finite F.I₀ ∧
        (∀ i, IsAffine (B.inclusion.obj (F.X i))) ∧
        ∀ i, ∃ j, ∃ g : F.X i ⟶ E.X j, g ≫ E.f j = F.f i := by
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
  have hQf : ∀ i, B.inclusion.map (Q.f i) = V.f i := fun i => B.inclusion.map_preimage _
  have hQ : AlgebraicGeometry.IsEtaleCovering ⟨T, Q⟩ := by
    show (Q.map B.inclusion).presieve₀ ∈ Scheme.etalePrecoverage (B.inclusion.obj T)
    rw [show Q.map B.inclusion = V.cover.toPreZeroHypercover from
      PreZeroHypercover.ext (x := _) (y := _) rfl (by rfl) (heq_of_eq (funext hQf))]
    simpa [T', Scheme.etalePrecoverage] using V.cover.mem₀
  have : Finite Q.I₀ := by
    simpa [Q, Scheme.AffineCover.cover] using hfin
  refine exists_finite_affine_covering_of_isEtaleCovering B E Q hQ
    (fun k => by
      show IsAffine (Spec (V.X k))
      exact isAffine_Spec _) fun k => ?_
  refine ⟨q.s₀ k, _, preimage_inclusion_comp_eq B (show
    B.inclusion.obj (Q.X k) ⟶ B.inclusion.obj (E.X (q.s₀ k)) from q.h₀ k) _ _ ?_⟩
  rw [hQf]
  simpa [Q, T', U, Scheme.AffineCover.cover] using q.w₀ k

private theorem finite_affine_pullback_refinement
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : BigAffineEtale B S hS)
    {U : BigEtaleOver B S hS}
    (a : (BigAffineEtale.inclusion B S hS).obj X ⟶ U)
    (E : PreZeroHypercover U)
    (hE : B.IsCovering ⟨U.left, E.map (BigEtaleOver.forget B S hS)⟩) :
    ∃ F : PreZeroHypercover.{u + 1} X,
      F.presieve₀ ∈ BigAffineEtale.precoverage B S hS X ∧
      ∀ i, Sieve.generate E.presieve₀
        ((BigAffineEtale.inclusion B S hS).map (F.f i) ≫ a) := by
  let G := BigAffineEtale.inclusion B S hS
  let forget := BigEtaleOver.forget B S hS
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
  obtain ⟨F, hF, hfinite, hFaff, hrefine⟩ :=
    finite_standard_refinement B (G.obj X).left P₀ hcov₀
  let F' : PreZeroHypercover.{u + 1} X := {
    I₀ := F.I₀
    X i := ⟨Over.mk (F.f i ≫ (G.obj X).hom), hFaff i⟩
    f i := ObjectProperty.homMk (Over.homMk (F.f i) rfl)
  }
  have hF' : BigAffineEtale.IsCovering B S hS ⟨X, F'⟩ := by
    simpa [BigAffineEtale.IsCovering,
      BigEtaleOver.IsStandardEtaleCovering, BigEtaleOver.IsCovering,
      F', G, forget, PreZeroHypercover.map] using
        (show B.IsCovering ⟨(G.obj X).left, F.map (𝟭 _)⟩ ∧
          IsAffine ((BigEtaleOver.toScheme B S hS).obj (G.obj X)) ∧
          Finite F.I₀ ∧ ∀ i, IsAffine (B.inclusion.obj (F.X i)) from
          ⟨hF, X.property, hfinite, hFaff⟩)
  refine ⟨F', ⟨F', rfl, hF'⟩, fun i => ?_⟩
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

/-- A sieve containing a covering presieve of `P` is covering for the topology generated by `P`. -/
private theorem mem_toGrothendieck_of_le_arrows {C : Type*} [Category C] (P : Precoverage C)
    {X : C} {R : Presieve X} (hR : R ∈ P X) {S : Sieve X} (h : R ≤ S.arrows) :
    S ∈ P.toGrothendieck X :=
  P.toGrothendieck.superset_covering ((Sieve.generate_le_iff _ _).2 h)
    (Precoverage.generate_mem_toGrothendieck hR)

private theorem bigAffineEtale_isCoverDense (B : AlgebraicGeometry.BigEtaleSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    (BigAffineEtale.inclusion B S hS).IsCoverDense
      (BigEtaleOver.topology B S hS) := by
  let G := BigAffineEtale.inclusion B S hS
  let K := BigEtaleOver.topology B S hS
  constructor
  intro X
  let A := (B.inclusion.obj X.left).affineOpenCover
  let U : (B.inclusion.obj X.left).OpenCover.{u + 1} := {
    I₀ := ULift.{u + 1, u} A.I₀
    X i := A.openCover.X i.down
    f i := A.f i.down
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ?_, fun i => A.openCover.map_prop i.down⟩
      obtain ⟨i, y, hy⟩ := A.openCover.exists_eq x
      exact ⟨ULift.up i, y, hy⟩ }
  obtain ⟨V, hV, hEq⟩ :=
    BigEtaleSite.exists_isCovering_tautologicallyEquivalent_openCover B X.left U
  let E : PreZeroHypercover X := {
    I₀ := V.I₀
    X i := Over.mk (V.f i ≫ X.hom)
    f i := Over.homMk (V.f i) }
  have hE : BigEtaleOver.IsCovering B S hS ⟨X, E⟩ := by
    show B.IsCovering ⟨X.left, E.map (Over.forget (B.obj S hS))⟩
    simpa [E, PreZeroHypercover.map] using hV
  have hpre : E.presieve₀ ∈ BigEtaleOver.precoverage B S hS X := by
    rw [BigEtaleOver.mem_precoverage_iff]
    exact ⟨E, rfl, hE⟩
  refine mem_toGrothendieck_of_le_arrows (BigEtaleOver.precoverage B S hS) hpre ?_
  rintro Y f ⟨i⟩
  rw [Sieve.coverByImage]
  obtain ⟨β, hβ⟩ := hEq.2
  obtain ⟨e, he⟩ := hβ i
  let j := β i
  have : IsOpenImmersion (U.f j) := U.map_prop j
  let Tj : B.Scheme :=
    B.obj (U.X j) (Scheme.size_lt_of_isOpenImmersion (U.f j) X.left.property)
  let tj : Tj ⟶ X.left := ⟨U.f j⟩
  let Aobj : BigAffineEtale B S hS := ⟨Over.mk (tj ≫ X.hom), by
    show IsAffine (A.openCover.X j.down)
    infer_instance⟩
  let eHom : V.X i ⟶ Tj := B.inclusion.preimage (show
      B.inclusion.obj (V.X i) ⟶ B.inclusion.obj Tj from e.hom)
  have hTriangle : eHom ≫ tj = V.f i :=
    preimage_inclusion_comp_eq B _ _ _ (by simpa [PreZeroHypercover.map] using he)
  let lift : E.X i ⟶ G.obj Aobj := Over.homMk eHom (congrArg (· ≫ X.hom) hTriangle)
  let map : G.obj Aobj ⟶ X := Over.homMk tj
  refine ⟨⟨Aobj, lift, map, ?_⟩⟩
  ext
  show (eHom ≫ tj).hom = (V.f i).hom
  exact congrArg (fun f => f.hom) hTriangle

private theorem affine_inclusion_lifts_saturate
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    ∀ {U : BigEtaleOver B S hS} {R : Sieve U},
      (BigEtaleOver.precoverage B S hS).Saturate U R →
      ∀ {X : BigAffineEtale B S hS}
        (a : (BigAffineEtale.inclusion B S hS).obj X ⟶ U),
        (R.pullback a).functorPullback
          (BigAffineEtale.inclusion B S hS) ∈
            BigAffineEtale.topology B S hS X := by
  intro U R hR
  induction hR with
  | of U P hP =>
      intro X a
      obtain ⟨E, hEq, hE⟩ :=
        (BigEtaleOver.mem_precoverage_iff B S hS).mp hP
      subst P
      change B.IsCovering
        ⟨U.left, E.map (BigEtaleOver.forget B S hS)⟩ at hE
      obtain ⟨F, hF, hfactor⟩ :=
        finite_affine_pullback_refinement B S hS X a E hE
      refine mem_toGrothendieck_of_le_arrows (BigAffineEtale.precoverage B S hS) hF ?_
      rintro Y f ⟨i⟩
      show (Sieve.generate E.presieve₀).pullback a
        ((BigAffineEtale.inclusion B S hS).map (F.f i))
      simpa [Sieve.pullback_apply, Category.assoc] using hfactor i
  | top U =>
      intro X a
      simpa only [Sieve.pullback_top, Sieve.functorPullback_top] using
        (BigAffineEtale.topology B S hS).top_mem X
  | pullback U R hR Y f ih =>
      intro X a
      simpa [Sieve.pullback_comp, Category.assoc] using
        ih (X := X) (a := a ≫ f)
  | transitive U R T hR hlocal ih ihlocal =>
      intro X a
      refine (BigAffineEtale.topology B S hS).transitive (ih a)
        ((T.pullback a).functorPullback
          (BigAffineEtale.inclusion B S hS)) ?_
      intro Z k hk
      have hsat := ihlocal (show R ((BigAffineEtale.inclusion B S hS).map k ≫ a) from hk)
        (X := Z) (a := 𝟙 _)
      rw [← Sieve.functorPullback_pullback]
      simpa [Sieve.pullback_comp, Category.assoc] using hsat

private theorem affine_topology_eq_restricted
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    BigAffineEtale.topology B S hS =
      (BigAffineEtale.inclusion B S hS).restrictedTopology
        (BigEtaleOver.topology B S hS) := by
  let G := BigAffineEtale.inclusion B S hS
  let P := BigAffineEtale.precoverage B S hS
  let Q := BigEtaleOver.precoverage B S hS
  let K := BigEtaleOver.topology B S hS
  have : G.Full := inferInstance
  have : G.Faithful := inferInstance
  have hpre : P ≤ Q.comap G := by
    intro X R hR
    obtain ⟨E, hEq, hE⟩ :=
      (BigAffineEtale.mem_precoverage_iff B S hS).mp hR
    rw [Precoverage.mem_comap_iff, hEq, ← PreZeroHypercover.presieve₀_map,
      BigEtaleOver.mem_precoverage_iff]
    have hstd : BigEtaleOver.IsStandardEtaleCovering B S hS
        ⟨G.obj X, E.map G⟩ := by
      simpa [G, BigAffineEtale.IsCovering] using hE
    exact ⟨E.map G, rfl, hstd.1⟩
  have hcomp : Q.comap G ≤ K.toPrecoverage.comap G := by
    intro X R hR
    apply Precoverage.mem_comap_iff.mpr
    apply Q.le_toPrecoverage_toGrothendieck
    exact Precoverage.mem_comap_iff.mp hR
  have : G.IsCoverDense K := bigAffineEtale_isCoverDense B S hS
  have : G.IsLocallyFull K := inferInstance
  have : G.IsLocallyFaithful K := inferInstance
  have hle : P.toGrothendieck ≤ G.restrictedTopology K := by
    show P.toGrothendieck ≤ (K.toPrecoverage.comap G).toGrothendieck
    exact (Precoverage.toGrothendieck_monotone hpre).trans
      (Precoverage.toGrothendieck_monotone hcomp)
  have hge : G.restrictedTopology K ≤ P.toGrothendieck := by
    intro X R hR
    rw [Functor.mem_restrictedTopology_iff] at hR
    have hsat : Q.Saturate (G.obj X) (R.functorPushforward G) := hR
    have hlift := affine_inclusion_lifts_saturate B S hS hsat (𝟙 _)
    rwa [Sieve.pullback_id, Sieve.functorPullback_functorPushforward_eq G] at hlift
  exact le_antisymm hle hge

/-- **Stacks 021E.** The inclusion of the big affine étale site over a scheme
into its big étale site is special cocontinuous. Its dense-subsite component
gives the induced equivalence of topoi. -/
@[stacks 021E]
public theorem BigAffineEtale.inclusion_isSpecialCocontinuous
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    IsSpecialCocontinuous
      (BigAffineEtale.topology B S hS)
      (BigEtaleOver.topology B S hS)
      (BigAffineEtale.inclusion B S hS) := by
  let G := BigAffineEtale.inclusion B S hS
  let J := BigAffineEtale.topology B S hS
  let K := BigEtaleOver.topology B S hS
  have hCocont : G.IsCocontinuous J K := by
    constructor
    intro X R hR
    change (BigEtaleOver.precoverage B S hS).Saturate (G.obj X) R at hR
    exact affine_inclusion_lifts_saturate B S hS hR (𝟙 _)
  have : G.Full := inferInstance
  have : G.Faithful := inferInstance
  have : G.IsCoverDense K := bigAffineEtale_isCoverDense B S hS
  have hSub : G.IsDenseSubsite J K := by
    show G.IsDenseSubsite (BigAffineEtale.topology B S hS) K
    rw [affine_topology_eq_restricted B S hS]
    infer_instance
  exact ⟨hCocont, hSub⟩

end AlgebraicGeometry
