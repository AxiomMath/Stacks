module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Sites.Over
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BigSitesPushforward.SubordinateCoverings
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleToposIndependence
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.BigSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Precoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Smooth.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.SyntomicTopology.SiteRefinement
public import StacksFrontier.CategoryTheory.Sites.Cocontinuous.AlmostCocontinuousDefs
public import StacksFrontier.CategoryTheory.Sites.Pretopology.SmallSubsite

/-!
# Almost cocontinuity of base change by a closed immersion

Base change along a closed immersion is almost cocontinuous on each of the big syntomic,
smooth, and étale sites.

## Main results

* `AlgebraicGeometry.bigSyntomicPullback_isAlmostCocontinuous` gives the syntomic case.
* `AlgebraicGeometry.bigSmoothPullback_isAlmostCocontinuous` gives the smooth case.
* `AlgebraicGeometry.bigEtalePullback_isAlmostCocontinuous` gives the étale case.

## Implementation notes

The three topologies are the localized topologies of chosen big sites. The base-change functor
is the canonical right adjoint `Over.pullback`, and the closed-immersion assumption is imposed
on the underlying morphism of schemes. The three declarations correspond to the three choices of
topology in the source.

Each case runs the same argument. A covering sieve on a base change is refined by a covering
family; that family is made subordinate to the closed immersion, so each of its members either
has empty base change or factors through a member of the original family; and the family is then
refined back inside the chosen big site. The empty alternative is discharged by showing that an
object of the site with empty underlying scheme has the bottom sieve as a covering sieve, which
is what `syntomic_empty_bottom`, `smooth_empty_bottom` and `etale_empty_bottom` record.

## References

* [Stacks Project, Tag 04C3](https://stacks.math.columbia.edu/tag/04C3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u
universe uC vC

namespace AlgebraicGeometry

private lemma bot_mem_of_empty_cover_representative
    {C : Type uC} [Category.{vC} C]
    {τCov IsCov : Covering.{uC, vC, max uC vC} C → Prop}
    (J : Precoverage C) (T : C)
    (hrep : ∀ E : Covering C, τCov E →
      ∃ E', IsCov E' ∧ Covering.CombEquiv E E')
    (hτ : τCov ⟨T, PreZeroHypercover.empty T⟩)
    (hmem : ∀ E : PreZeroHypercover.{max uC vC} T,
      IsCov ⟨T, E⟩ → E.presieve₀ ∈ J T) :
    (⊥ : Sieve T) ∈ J.toGrothendieck T := by
  obtain ⟨E, hE, hT, hce⟩ := hrep ⟨T, PreZeroHypercover.empty T⟩ hτ
  cases hT
  have hEmpty : IsEmpty E.2.I₀ := ⟨fun i => by
    obtain ⟨β, -, -⟩ := hce.2
    exact PEmpty.elim (β i)⟩
  have hpresieve : E.2.presieve₀ = (⊥ : Presieve E.1) := by
    funext Z g
    apply propext
    constructor
    · rintro ⟨i⟩
      exact hEmpty.false i
    · simp
  have hEbot : E.2.sieve₀ = (⊥ : Sieve E.1) := by
    show Sieve.generate E.2.presieve₀ = ⊥
    rw [hpresieve]
    simp
  rw [← hEbot]
  exact J.generate_mem_toGrothendieck (hmem E.2 hE)

private lemma syntomic_empty_bottom
    (B : AlgebraicGeometry.BigSyntomicSite.{u}) (T : B.category)
    (hT : IsEmpty (B.inclusion.obj T)) :
    (⊥ : Sieve T) ∈ B.topology T := by
  have hτ : AlgebraicGeometry.SyntomicCovering B.cutoff
      ⟨T, PreZeroHypercover.empty T⟩ := by
    show AlgebraicGeometry.IsSyntomicCovering _ _
    constructor
    · exact fun i => PEmpty.elim i
    · ext x
      constructor <;> intro _ <;> exact (hT.false x).elim
  show (⊥ : Sieve T) ∈ (B.precoverage).toGrothendieck T
  exact bot_mem_of_empty_cover_representative B.precoverage T
    (fun E hE => B.has_coveringRepresentative E hE) hτ (fun E hE => ⟨E, rfl, hE⟩)

private lemma smooth_empty_bottom
    (B : AlgebraicGeometry.BigSmoothSite.{u}) (T : B.category)
    (hT : IsEmpty ((ObjectProperty.ι
      (fun X : Scheme.{u} => X.size < B.cutoff)).obj T)) :
    (⊥ : Sieve T) ∈ B.grothendieckTopology T := by
  have hτ : AlgebraicGeometry.SmoothCovering B.cutoff
      ⟨T, PreZeroHypercover.empty T⟩ := by
    let I : B.category ⥤ Scheme := ObjectProperty.ι
      (fun X : Scheme.{u} => X.size < B.cutoff)
    let E := (PreZeroHypercover.empty T).map I
    show E.presieve₀ ∈ Scheme.precoverage (@Smooth.{u}) (I.obj T)
    exact (Scheme.presieve₀_mem_precoverage_iff E).2
      ⟨fun x => (hT.false x).elim, fun i => PEmpty.elim i⟩
  show (⊥ : Sieve T) ∈ B.precoverage.toGrothendieck T
  exact bot_mem_of_empty_cover_representative B.precoverage T
    (fun E hE => B.has_coveringRepresentative E hE) hτ (fun E hE => ⟨E, hE, rfl⟩)

private lemma etale_empty_bottom
    (B : AlgebraicGeometry.BigEtaleSite.{u}) (T : B.Scheme)
    (hT : IsEmpty (B.inclusion.obj T)) :
    (⊥ : Sieve T) ∈ B.topology T := by
  have hτ : AlgebraicGeometry.IsEtaleCovering
      ⟨T, PreZeroHypercover.empty T⟩ := by
    show ((PreZeroHypercover.empty T).map B.inclusion).presieve₀ ∈
      Scheme.etalePrecoverage (B.inclusion.obj T)
    exact (Scheme.presieve₀_mem_precoverage_iff
      ((PreZeroHypercover.empty T).map B.inclusion)).2
      ⟨fun x => (hT.false x).elim, fun i => PEmpty.elim i⟩
  show (⊥ : Sieve T) ∈ B.precoverage.toGrothendieck T
  exact bot_mem_of_empty_cover_representative B.precoverage T
    (fun E hE => B.exists_covering_rep E hE) hτ (fun E hE => ⟨E, rfl, hE⟩)

/-- The base change of a closed immersion along any morphism is again a closed immersion after
applying a pullback-preserving functor to schemes. -/
private lemma isClosedImmersion_map_pullback_fst
    {C : Type uC} [Category.{vC} C] (I : C ⥤ Scheme.{u}) {X Y U : C} (g : U ⟶ Y) (f : X ⟶ Y)
    [HasPullback g f] [PreservesLimit (cospan g f) I] [IsClosedImmersion (I.map f)] :
    IsClosedImmersion (I.map (pullback.fst g f)) := by
  rw [← (IsPullback.map I (IsPullback.of_hasPullback g f)).isoPullback_hom_fst]
  infer_instance

/-- The common end of the almost cocontinuity argument: a covering `W` of `U` refining a
subordinate covering of the base change of the covering `E` gives the required covering sieve. -/
private theorem exists_sieve_of_subordinate_refinement
    {C : Type uC} [Category.{vC} C] [HasPullbacks C] (I : C ⥤ Scheme.{u}) [I.Full] [I.Faithful]
    (J : GrothendieckTopology C) {X Y : C} (f : X ⟶ Y)
    (hempty : ∀ T : C, IsEmpty (I.obj T) → (⊥ : Sieve T) ∈ J T)
    (U : Over Y) (S : Sieve ((Over.pullback f).obj U))
    (E : PreZeroHypercover.{max uC vC} ((Over.pullback f).obj U).left)
    (hES : E.sieve₀ ≤ Sieve.overEquiv _ S)
    {K : Type (u + 1)} {Z : K → Scheme.{u}} {q : ∀ k, Z k ⟶ I.obj U.left}
    (hfac : ∀ k, IsEmpty (pullback (q k) (I.map (pullback.fst U.hom f)) : Scheme.{u}) ∨
      ∃ i, ∃ h : pullback (q k) (I.map (pullback.fst U.hom f)) ⟶ I.obj (E.X i),
        h ≫ I.map (E.f i) = pullback.snd _ _)
    (W : PreZeroHypercover.{max uC vC} U.left) (m : (W.map I).Hom ⟨K, Z, q⟩)
    (hW : W.sieve₀ ∈ J U.left) :
    ∃ T : Sieve U, T ∈ (J.over Y) U ∧
      ∀ ⦃V : Over Y⦄ (g : V ⟶ U), T g →
        SheafTheoreticallyEmptySite (J.over X) ((Over.pullback f).obj V) ∨
          S ((Over.pullback f).map g) := by
  let F := Over.pullback f
  let P := F.obj U
  let p : pullback U.hom f ⟶ U.left := pullback.fst U.hom f
  let p' : I.obj P.left ⟶ I.obj U.left := I.map p
  let T : Sieve U := (Sieve.overEquiv U).symm W.sieve₀
  refine ⟨T, (GrothendieckTopology.mem_over_iff (J := J) T).2 (by simpa [T] using hW), ?_⟩
  intro V g hg
  have hgbase : W.sieve₀ (g.left) := by
    simpa [T] using (Sieve.overEquiv_iff T g.left).2 hg
  rw [PreZeroHypercover.sieve₀, Sieve.ofArrows] at hgbase
  obtain ⟨j, k, hk⟩ := (Sieve.mem_ofArrows_iff W.X W.f g.left).mp hgbase
  let Vj : Over Y := Over.mk (W.f j ≫ U.hom)
  let aj : Vj ⟶ U := Over.homMk (W.f j) (by simp [Vj])
  let b₁ := pullback.fst (W.f j ≫ U.hom) f
  let b₂ := pullback.snd (W.f j ≫ U.hom) f
  let tj : (F.obj Vj).left ⟶ P.left :=
    pullback.lift (b₁ ≫ W.f j) b₂ (by
      dsimp [b₁, b₂]
      rw [Category.assoc]
      exact pullback.condition)
  have hmapj : (F.map aj).left = tj := by
    calc
      (F.map aj).left = pullback.lift
          (pullback.fst Vj.hom f ≫ aj.left) (pullback.snd Vj.hom f) _ := by
            exact Over.pullback_map_left f Vj (k := aj)
      _ = tj := by
        apply pullback.hom_ext
        · simp [tj, b₁, b₂, Vj, aj]
        · simp [tj, b₁, b₂, Vj, aj]
  let k₀ : K := m.s₀ j
  let mh : I.obj (W.X j) ⟶ Z k₀ := m.h₀ j
  have hmcomp : mh ≫ q k₀ = I.map (W.f j) := m.w₀ j
  let rj : I.obj (F.obj Vj).left ⟶ pullback (q k₀) p' :=
    pullback.lift (I.map b₁ ≫ mh) (I.map tj) (by
      rw [Category.assoc, hmcomp]
      change _ = I.map tj ≫ I.map p
      simp only [← Functor.map_comp]
      exact congrArg I.map (pullback.lift_fst _ _ _).symm)
  let a : V ⟶ Vj := Over.homMk k (by
    calc
      k ≫ (W.f j ≫ U.hom) = (k ≫ W.f j) ≫ U.hom := by simp
      _ = g.left ≫ U.hom := by rw [hk]
      _ = V.hom := g.w)
  have ha : a ≫ aj = g := by
    apply (Over.forget Y).map_injective
    show k ≫ W.f j = g.left
    exact hk.symm
  cases hfac k₀ with
  | inl hEmpty =>
      have hEmptyJ : IsEmpty (I.obj (F.obj Vj).left) :=
        ⟨fun z => hEmpty.false (rj z)⟩
      have hEmptyV : IsEmpty (I.obj (F.obj V).left) :=
        ⟨fun z => hEmptyJ.false ((I.map (F.map a).left) z)⟩
      left
      apply (GrothendieckTopology.mem_over_iff (J := J)
        (⊥ : Sieve (F.obj V))).2
      simpa using hempty _ hEmptyV
  | inr hfactor =>
      rcases hfactor with ⟨i, h, hcomm⟩
      have hgen : E.sieve₀ ((F.map aj).left) := by
        rw [PreZeroHypercover.sieve₀, Sieve.ofArrows]
        apply (Sieve.mem_ofArrows_iff E.X E.f (F.map aj).left).2
        refine ⟨i, I.preimage (rj ≫ h), I.map_injective ?_⟩
        rw [hmapj, Functor.map_comp, I.map_preimage, Category.assoc, hcomm]
        exact (pullback.lift_snd _ _ _).symm
      have hSgen : S (F.map aj) := by
        have h' := (Sieve.overEquiv_iff S (F.map aj).left).mp (hES _ hgen)
        let U' : Over X := Over.mk ((F.map aj).left ≫ (F.obj U).hom)
        let e : F.obj Vj ≅ U' := Over.isoMk (Iso.refl _) (by simp [U'])
        let a' : U' ⟶ F.obj U := Over.homMk (F.map aj).left
        have hEq : e.hom ≫ a' = F.map aj := by
          apply (Over.forget X).map_injective
          simp [e, a', Over.comp_left]
        have hdown := S.downward_closed h' e.hom
        rw [hEq] at hdown
        exact hdown
      right
      have hdown := S.downward_closed hSgen (F.map a)
      simpa only [← F.map_comp, ha] using hdown

/-- Base change by a closed immersion is almost cocontinuous on big syntomic sites. -/
@[stacks 04C3 "syntomic case"]
public theorem bigSyntomicPullback_isAlmostCocontinuous
    (B : AlgebraicGeometry.BigSyntomicSite.{u}) {X Y : B.category} (f : X ⟶ Y)
    [IsClosedImmersion (B.inclusion.map f)] :
    IsAlmostCocontinuous (Over.pullback f)
      (AlgebraicGeometry.BigSyntomicOver.topology B Y.1 Y.2)
      (AlgebraicGeometry.BigSyntomicOver.topology B X.1 X.2) := by
  let I := B.inclusion
  let UY := B.obj Y.1 Y.2
  let UX := B.obj X.1 X.2
  let J := B.topology
  let F := Over.pullback f
  show ∀ U : Over UY, ∀ {S : Sieve (F.obj U)},
    S ∈ (J.over UX) (F.obj U) →
      ∃ T : Sieve U, T ∈ (J.over UY) U ∧
        ∀ ⦃V : Over UY⦄ (g : V ⟶ U), T g →
          SheafTheoreticallyEmptySite (J.over UX) (F.obj V) ∨ S (F.map g)
  intro U S hS
  have hSbase : Sieve.overEquiv (F.obj U) S ∈ J (F.obj U).left :=
    (GrothendieckTopology.mem_over_iff (J := J) S).mp hS
  obtain ⟨E, hE, hES⟩ := exists_siteCovering_refining_sieve B.covering_isSite hSbase
  have := isClosedImmersion_map_pullback_fst I U.hom f
  obtain ⟨K, V, q, hV, hfac⟩ :=
    AlgebraicGeometry.exists_syntomicCovering_subordinate_to_closedImmersion
      (I.map (pullback.fst U.hom f)) (fun i => I.obj (E.X i)) (fun i => I.map (E.f i)) hE.1
  obtain ⟨W, hW, ⟨m⟩⟩ := AlgebraicGeometry.exists_siteCovering_refining B U.left ⟨K, V, q⟩ hV
  refine exists_sieve_of_subordinate_refinement I J f (syntomic_empty_bottom B) U S E hES hfac
    W m ?_
  simpa [J, AlgebraicGeometry.BigSyntomicSite.topology,
    AlgebraicGeometry.BigSyntomicSite.precoverage, sitePrecoverage] using
    (sitePrecoverage B.IsCovering).generate_mem_toGrothendieck ⟨W, rfl, hW⟩

/-- Base change by a closed immersion is almost cocontinuous on big smooth sites. -/
@[stacks 04C3 "smooth case"]
public theorem bigSmoothPullback_isAlmostCocontinuous
    (B : AlgebraicGeometry.BigSmoothSite.{u}) {X Y : B.category} (f : X ⟶ Y)
    [IsClosedImmersion ((ObjectProperty.ι _).map f)] :
    IsAlmostCocontinuous (Over.pullback f)
      (AlgebraicGeometry.BigSmoothOver.topology B Y.1 Y.2)
      (AlgebraicGeometry.BigSmoothOver.topology B X.1 X.2) := by
  let I : B.category ⥤ Scheme :=
    ObjectProperty.ι (fun X : Scheme.{u} => X.size < B.cutoff)
  let UY : B.category := ⟨Y.1, Y.2⟩
  let UX : B.category := ⟨X.1, X.2⟩
  let J := B.grothendieckTopology
  let F := Over.pullback f
  have hpre : B.precoverage = sitePrecoverage B.IsCovering := by
    ext T R
    constructor
    · rintro ⟨E, hE, rfl⟩
      exact ⟨E, rfl, hE⟩
    · rintro ⟨E, rfl, hE⟩
      exact ⟨E, hE, rfl⟩
  show ∀ U : Over UY, ∀ {S : Sieve (F.obj U)},
    S ∈ (J.over UX) (F.obj U) →
      ∃ T : Sieve U, T ∈ (J.over UY) U ∧
        ∀ ⦃V : Over UY⦄ (g : V ⟶ U), T g →
          SheafTheoreticallyEmptySite (J.over UX) (F.obj V) ∨ S (F.map g)
  intro U S hS
  have hSbase : Sieve.overEquiv (F.obj U) S ∈ (sitePrecoverage B.IsCovering).toGrothendieck
      (F.obj U).left := by
    rw [← hpre]
    exact (GrothendieckTopology.mem_over_iff (J := J) S).mp hS
  obtain ⟨E, hE, hES⟩ := exists_siteCovering_refining_sieve B.covering_isSite hSbase
  have := isClosedImmersion_map_pullback_fst I U.hom f
  obtain ⟨K, V, q, hV, hfac⟩ :=
    AlgebraicGeometry.exists_smoothCovering_subordinate_to_closedImmersion
      (I.map (pullback.fst U.hom f)) (fun i => I.obj (E.X i)) (fun i => I.map (E.f i)) hE.1
  obtain ⟨W, hW, ⟨m⟩⟩ :=
    AlgebraicGeometry.exists_covering_refining_smooth_cover B ⟨K, V, q⟩ hV
  refine exists_sieve_of_subordinate_refinement I J f (smooth_empty_bottom B) U S E hES hfac
    W m ?_
  simpa [J, AlgebraicGeometry.BigSmoothSite.grothendieckTopology] using
    B.precoverage.generate_mem_toGrothendieck ⟨W, hW, rfl⟩

/-- Base change by a closed immersion is almost cocontinuous on big étale sites. -/
@[stacks 04C3 "étale case"]
public theorem bigEtalePullback_isAlmostCocontinuous
    (B : AlgebraicGeometry.BigEtaleSite.{u}) {X Y : B.Scheme} (f : X ⟶ Y)
    [IsClosedImmersion (B.inclusion.map f)] :
    IsAlmostCocontinuous (Over.pullback f)
      (AlgebraicGeometry.BigEtaleOver.topology B Y.1 Y.2)
      (AlgebraicGeometry.BigEtaleOver.topology B X.1 X.2) := by
  let I : B.Scheme ⥤ Scheme := B.inclusion
  let UY := B.obj Y.1 Y.2
  let UX := B.obj X.1 X.2
  let J := B.topology
  let F := Over.pullback f
  have htopY : AlgebraicGeometry.BigEtaleOver.topology B Y.1 Y.2 = J.over UY := by
    calc
      AlgebraicGeometry.BigEtaleOver.topology B Y.1 Y.2 =
          (B.precoverage.comap (Over.forget UY)).toGrothendieck := by
        rw [AlgebraicGeometry.BigEtaleOver.topology, bigEtaleOver_precoverage_eq_comap]
      _ = B.precoverage.toGrothendieck.over UY := by
        rw [← over_toGrothendieck_eq_toGrothendieck_comap_forget B.precoverage UY]
  have htopX : AlgebraicGeometry.BigEtaleOver.topology B X.1 X.2 = J.over UX := by
    calc
      AlgebraicGeometry.BigEtaleOver.topology B X.1 X.2 =
          (B.precoverage.comap (Over.forget UX)).toGrothendieck := by
        rw [AlgebraicGeometry.BigEtaleOver.topology, bigEtaleOver_precoverage_eq_comap]
      _ = B.precoverage.toGrothendieck.over UX := by
        rw [← over_toGrothendieck_eq_toGrothendieck_comap_forget B.precoverage UX]
  rw [htopY, htopX]
  show ∀ U : Over UY, ∀ {S : Sieve (F.obj U)},
    S ∈ (J.over UX) (F.obj U) →
      ∃ T : Sieve U, T ∈ (J.over UY) U ∧
        ∀ ⦃V : Over UY⦄ (g : V ⟶ U), T g →
          SheafTheoreticallyEmptySite (J.over UX) (F.obj V) ∨ S (F.map g)
  intro U S hS
  have hSbase : Sieve.overEquiv (F.obj U) S ∈ J (F.obj U).left :=
    (GrothendieckTopology.mem_over_iff (J := J) S).mp hS
  obtain ⟨E, hE, hES⟩ := exists_siteCovering_refining_sieve B.coverings_isSite hSbase
  have := isClosedImmersion_map_pullback_fst I U.hom f
  obtain ⟨K, V, q, hV, hfac⟩ :=
    AlgebraicGeometry.exists_etaleCovering_subordinate_to_closedImmersion
      (I.map (pullback.fst U.hom f)) (fun i => I.obj (E.X i)) (fun i => I.map (E.f i)) hE.1
  obtain ⟨W, hW, ⟨m⟩⟩ :=
    AlgebraicGeometry.BigEtaleSite.exists_covering_refining_etale_cover B ⟨K, V, q⟩ hV
  refine exists_sieve_of_subordinate_refinement I J f (etale_empty_bottom B) U S E hES hfac
    W m ?_
  simpa [J, AlgebraicGeometry.BigEtaleSite.topology] using
    B.precoverage.generate_mem_toGrothendieck ⟨W, rfl, hW⟩

end AlgebraicGeometry
