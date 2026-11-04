module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.IsConnected
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CoveringRefinesSieve
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CoverPreserving
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.SliceAdjunction
public import StacksFrontier.AlgebraicGeometry.Topologies.Support.SyntomicSiteRepresentatives
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.BigSiteOver
public import StacksFrontier.AlgebraicGeometry.Topologies.Syntomic.StandardRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.SyntomicTopology.Coverings
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs

/-!
# Affine objects form a dense subsite of the big syntomic site

Let `B` be a big syntomic site containing a scheme `S`. The inclusion of the big affine
syntomic site over `S` into the big syntomic site over `S` is a special cocontinuous functor,
so it induces an equivalence between their topoi of sheaves.

## Main results

* `AlgebraicGeometry.BigAffineSyntomic.inclusion_isSpecialCocontinuous` — the inclusion is
  special cocontinuous, hence a dense subsite, hence induces an equivalence of topoi.

## Implementation notes

`IsSpecialCocontinuous` packages cocontinuity with Mathlib's `Functor.IsDenseSubsite`, whose
`Functor.IsDenseSubsite.sheafEquiv` is the induced equivalence of sheaf categories, so the one
statement carries both conclusions of the source.

## References

* [Stacks Project, Tag 06VD](https://stacks.math.columbia.edu/tag/06VD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u v

namespace AlgebraicGeometry

/-- A covering sieve of the big syntomic site contains one of the site's own covering
families. -/
private theorem bigSyntomicSite_exists_covering_refining_sieve (B : BigSyntomicSite.{u})
    {X : B.category} {R : Sieve X} (hR : R ∈ B.topology X) :
    ∃ E : PreZeroHypercover X, B.IsCovering ⟨X, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [BigSyntomicSite.topology] at hR
  exact CategoryTheory.exists_covering_refining_sieve B.IsCovering B.precoverage
    (fun h => ⟨h.choose, h.choose_spec.2, h.choose_spec.1⟩) B.covering_isSite hR

/-- A standard syntomic covering of an object of a big syntomic site is tautologically
equivalent to one of the site's own covering families. -/
private theorem exists_siteCovering_tautologicallyEquivalent_standardSyntomic
    (B : BigSyntomicSite.{u}) (T : B.category) (𝒰 : PreZeroHypercover.{v} T.1)
    (h𝒰 : IsSyntomicCovering 𝒰.X 𝒰.f)
    (hstandard : IsStandardSyntomicCovering 𝒰.X 𝒰.f) :
    ∃ 𝒱 : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, 𝒱⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent 𝒰 (𝒱.map B.inclusion) := by
  apply B.exists_isCovering_tautologicallyEquivalent_of_sources_iso T 𝒰 h𝒰
  intro i
  let : IsAffine (𝒰.X i) := hstandard.affine_source i
  let : IsAffine T.1 := hstandard.affine_target
  let : Algebra Γ(T.1, ⊤) Γ(𝒰.X i, ⊤) := (𝒰.f i).appTop.hom.toAlgebra
  let : Algebra.Syntomic Γ(T.1, ⊤) Γ(𝒰.X i, ⊤) :=
    have : Algebra.IsRelativeGlobalCompleteIntersection _ _ := hstandard.standard_syntomic i
    Algebra.Syntomic.of_isRelativeGlobalCompleteIntersection _ _
  let : LocallyOfFiniteType (𝒰.f i) :=
    (HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFiniteType)).2
      (RingHom.finiteType_algebraMap.mpr inferInstance)
  exact ⟨⟨𝒰.X i, Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact (𝒰.f i) T.2⟩,
    ⟨Iso.refl _⟩⟩

/-- A Zariski covering of an object of a big syntomic site is tautologically equivalent to one
of the site's own covering families. -/
private theorem exists_siteCovering_tautologicallyEquivalent_openCover
    (B : BigSyntomicSite.{u}) (T : B.category) (𝒰 : Scheme.OpenCover.{v} T.1) :
    ∃ 𝒱 : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, 𝒱⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent 𝒰.toPreZeroHypercover
          (𝒱.map B.inclusion) :=
  B.exists_isCovering_tautologicallyEquivalent_of_sources_iso T 𝒰.toPreZeroHypercover
    (isSyntomicCovering_of_mem_zariskiPrecoverage 𝒰.mem₀)
    (fun i ↦ ⟨⟨𝒰.X i, Scheme.size_lt_of_isOpenImmersion (𝒰.f i) T.2⟩, ⟨Iso.refl _⟩⟩)

private theorem exists_affine_covering_refining_sieve (B : BigSyntomicSite.{u})
    {T : B.category} [IsAffine ((ObjectProperty.ι _).obj T)] {R : Sieve T}
    (hR : R ∈ B.topology T) :
    ∃ P : PreZeroHypercover T, Finite P.I₀ ∧
      (∀ i, IsAffine ((ObjectProperty.ι _).obj (P.X i))) ∧
      (∀ i (hPi : IsAffine ((ObjectProperty.ι _).obj (P.X i))),
        @IsStandardSyntomic _ _ hPi _ ((ObjectProperty.ι _).map (P.f i))) ∧
      B.IsCovering ⟨T, P⟩ ∧ P.presieve₀ ≤ R := by
  classical
  obtain ⟨E, hE, hER⟩ := bigSyntomicSite_exists_covering_refining_sieve B hR
  have hEsyn : IsSyntomicCovering
      (fun i ↦ (E.X i).1) (fun i ↦ (ObjectProperty.ι _).map (E.f i)) := by
    simpa [SyntomicCovering] using hE.1
  let U : ((ObjectProperty.ι _).obj T).Cover
      (Scheme.precoverage (@Syntomic)) :=
    ⟨E.map (ObjectProperty.ι _), (Scheme.presieve₀_mem_precoverage_iff
        (E.map (ObjectProperty.ι _))).2 ⟨Set.iUnion_eq_univ_iff.mp hEsyn.2, hEsyn.1⟩⟩
  obtain ⟨V, hVref, hVfinite, hVstandard, _⟩ :=
    exists_finite_affine_standardSyntomic_refinement
      U.toPreZeroHypercover hEsyn
  let Q := V.cover.toPreZeroHypercover
  let : Finite Q.I₀ := hVfinite
  let : ∀ i, IsAffine (Q.X i) := fun i ↦ isAffine_Spec (V.X i)
  have hQsyn : IsSyntomicCovering Q.X Q.f := by
    obtain ⟨hsurj, hmapsyn⟩ :=
      (Scheme.presieve₀_mem_precoverage_iff Q).mp V.cover.mem₀
    exact ⟨hmapsyn, Set.iUnion_eq_univ_iff.mpr hsurj⟩
  have hQstandard : IsStandardSyntomicCovering Q.X Q.f :=
    ⟨hVfinite, inferInstance, fun i ↦ inferInstance, hVstandard, hQsyn.2⟩
  obtain ⟨W, hW, hWQ⟩ :=
    exists_siteCovering_tautologicallyEquivalent_standardSyntomic
      B T Q hQsyn hQstandard
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
  let : Finite I := Finite.of_surjective (fun i : Q.I₀ => (⟨α' i, ⟨i, rfl⟩⟩ : I))
    fun i ↦ ⟨i.2.choose, Subtype.ext i.2.choose_spec⟩
  let P : PreZeroHypercover T :=
    { I₀ := I
      X := fun i => W.X i.1
      f := fun i => W.f i.1 }
  have hPaff : ∀ i, IsAffine ((ObjectProperty.ι _).obj (P.X i)) := by
    intro i
    obtain ⟨e, _⟩ := hβ' i.1
    let : IsAffine (Q.X (β' i.1)) := isAffine_Spec (V.X (β' i.1))
    exact IsAffine.of_isIso e.hom
  have hPstandard : ∀ i (hPi : IsAffine ((ObjectProperty.ι _).obj (P.X i))),
      @IsStandardSyntomic _ _ hPi _ ((ObjectProperty.ι _).map (P.f i)) := by
    intro i hPi
    obtain ⟨e, he⟩ := hβ' i.1
    let : IsAffine ((ObjectProperty.ι _).obj (P.X i)) := hPi
    have he' : e.inv ≫ (ObjectProperty.ι _).map (P.f i) = Q.f (β' i.1) :=
      (Iso.inv_comp_eq e).2 he.symm
    exact standardSyntomic_of_sourceIso (Q.f (β' i.1))
      ((ObjectProperty.ι _).map (P.f i)) e.symm he' (hVstandard (β' i.1))
  have hPsurj : (⋃ i : I, Set.range ((ObjectProperty.ι _).map (P.f i))) = Set.univ := by
    refine Set.eq_univ_iff_forall.mpr fun x => ?_
    have hx : x ∈ (⋃ i, Set.range (Q.f i)) := by rw [hQsyn.2]; trivial
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
    obtain ⟨e, he⟩ := hα' i
    let j : I := ⟨α' i, ⟨i, rfl⟩⟩
    refine Set.mem_iUnion.mpr ⟨j, Set.mem_range.mpr ⟨e.hom y, ?_⟩⟩
    change (e.hom ≫ (ObjectProperty.ι _).map (P.f j)) y = x
    rwa [he]
  have hPsyn : IsSyntomicCovering
      (fun i ↦ (P.X i).1) (fun i ↦ (ObjectProperty.ι _).map (P.f i)) := by
    refine ⟨fun i ↦ ?_, hPsurj⟩
    let : IsAffine ((ObjectProperty.ι _).obj (P.X i)) := hPaff i
    let : IsAffine ((P.X i).1) := hPaff i
    exact syntomic_of_standardSyntomic (hPstandard i (hPaff i))
  have hPcover : B.IsCovering ⟨T, P⟩ := by
    change SyntomicCovering B.cutoff ⟨T, P⟩ ∧
      Cardinal.mk P.I₀ ≤ B.coveringBound
    exact ⟨by simpa [SyntomicCovering] using hPsyn,
      le_trans (Cardinal.mk_le_of_injective (f := fun i : I => (i.1 : W.I₀))
        Subtype.val_injective) hW.2⟩
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
        (e.hom ≫ hVref.h₀ k) ≫ (ObjectProperty.ι _).map (E.f (hVref.s₀ k)) =
            e.hom ≫ Q.f k := by
              have hw := hVref.w₀ k
              change hVref.h₀ k ≫ (ObjectProperty.ι _).map (E.f (hVref.s₀ k)) = Q.f k at hw
              rw [← hw]
              exact Category.assoc _ _ _
        _ = (ObjectProperty.ι _).map (W.f j.1) := he
    simpa only [← hg] using R.downward_closed (hER _ _ ⟨hVref.s₀ k⟩) g
  exact ⟨P, inferInstance, hPaff, (fun i _ ↦ hPstandard i (hPaff i)), hPcover, hPR⟩

private theorem inclusion_isCoverDense (B : BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    (BigAffineSyntomic.inclusion B S hS).IsCoverDense
      (BigSyntomicOver.topology B S hS) := by
  classical
  constructor
  intro X
  let T : B.category := X.left
  let O := (ObjectProperty.ι _).obj T
  let U : Scheme.OpenCover O := O.affineOpenCover.openCover
  obtain ⟨W, hW, hWU⟩ :=
    exists_siteCovering_tautologicallyEquivalent_openCover
      B T U
  rcases hWU with ⟨⟨α, hα⟩, ⟨β, hβ⟩⟩
  have hWaff : ∀ j, IsAffine ((ObjectProperty.ι _).obj (W.X j)) := by
    intro j
    obtain ⟨e, _⟩ := hβ j
    let : IsAffine (U.X (β j)) := by
      change IsAffine (Spec (O.affineOpenCover.X (β j)))
      exact isAffine_Spec _
    exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance
  let Vobj (j : W.I₀) : BigAffineSyntomic B S hS :=
    { obj := Over.mk (W.f j ≫ X.hom), property := hWaff j }
  let vmap (j : W.I₀) :
      (BigAffineSyntomic.inclusion B S hS).obj (Vobj j) ⟶ X :=
    Over.homMk (W.f j)
  have hBcover : Sieve.ofArrows
      (fun j => (BigAffineSyntomic.inclusion B S hS).obj (Vobj j)) vmap ∈
      BigSyntomicOver.topology B S hS X := by
    rw [BigSyntomicOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
    change Sieve.ofArrows W.X W.f ∈ B.topology T
    simpa [BigSyntomicSite.topology, PreZeroHypercover.presieve₀] using
      Precoverage.generate_mem_toGrothendieck (⟨W, rfl, hW⟩ : W.presieve₀ ∈ B.precoverage T)
  apply (BigSyntomicOver.topology B S hS).superset_covering _ hBcover
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro j
  exact Presieve.in_coverByImage (BigAffineSyntomic.inclusion B S hS) (vmap j)

private theorem inclusion_isCocontinuous (B : BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    (BigAffineSyntomic.inclusion B S hS).IsCocontinuous
      (BigAffineSyntomic.topology B S hS)
      (BigSyntomicOver.topology B S hS) := by
  classical
  constructor
  intro X R hR
  let u := BigAffineSyntomic.inclusion B S hS
  let Y := u.obj X
  let T : B.category := Y.left
  let : IsAffine ((ObjectProperty.ι _).obj T) := X.2
  have hRB : (Sieve.overEquiv Y) R ∈ B.topology T := by
    rwa [BigSyntomicOver.topology, GrothendieckTopology.mem_over_iff] at hR
  obtain ⟨P, hPfinite, hPaff, hPstandard, hPcover, hPR⟩ :=
    exists_affine_covering_refining_sieve B hRB
  have hTscheme : (ObjectProperty.ι _).obj T =
      (BigAffineSyntomic.toScheme B S hS).obj X := rfl
  let F : PreZeroHypercover X :=
    { I₀ := P.I₀
      X := fun i =>
        { obj := Over.mk (P.f i ≫ Y.hom)
          property := hPaff i }
      f := fun i => ObjectProperty.homMk (Over.homMk (P.f i)) }
  have hFcover : BigAffineSyntomic.IsCovering B S hS ⟨X, F⟩ := by
    constructor
    · exact hPcover
    · refine ⟨hPfinite, X.property, hPaff, ?_, hPcover.1.2⟩
      exact fun i ↦ hPstandard i (hPaff i)
  have hgen : Sieve.generate F.presieve₀ ∈ BigAffineSyntomic.topology B S hS X :=
    Precoverage.generate_mem_toGrothendieck ⟨F, rfl, hFcover⟩
  apply (BigAffineSyntomic.topology B S hS).superset_covering _ hgen
  rw [Sieve.generate_le_iff, Presieve.ofArrows_le_iff]
  intro i
  change R (u.map (F.f i))
  rw [show u.map (F.f i) = Over.homMk (P.f i) by rfl]
  apply (Sieve.overEquiv_iff R (P.f i)).mp
  exact hPR _ _ ⟨i⟩

private theorem inclusion_isCoverPreserving (B : BigSyntomicSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    CoverPreserving (BigAffineSyntomic.topology B S hS)
      (BigSyntomicOver.topology B S hS)
      (BigAffineSyntomic.inclusion B S hS) := by
  let u := BigAffineSyntomic.inclusion B S hS
  let K := BigSyntomicOver.topology B S hS
  let : ObjectProperty.IsClosedUnderIsomorphisms
      (fun X : Scheme ↦ X.size < B.cutoff) := ⟨fun {X Y} e h => by
        change X.size < B.cutoff at h
        rwa [← Scheme.size_congr e]⟩
  let : ObjectProperty.IsClosedUnderLimitsOfShape
      (fun X : Scheme ↦ X.size < B.cutoff) WalkingCospan :=
    .mk' (by
      rintro _ ⟨F, hF⟩
      rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
      exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right))
  let : Limits.HasPullbacks B.category := inferInstance
  let : Limits.HasLimitsOfShape WalkingCospan B.category := inferInstance
  let hterm : Limits.IsTerminal WalkingCospan.one :=
    Limits.IsTerminal.ofUniqueHom
      (fun j => by
        cases j with
        | none => exact 𝟙 _
        | some j =>
          cases j with
          | left => exact WalkingCospan.Hom.inl
          | right => exact WalkingCospan.Hom.inr)
      (fun _ _ => Subsingleton.elim _ _)
  let : IsConnected WalkingCospan :=
    CategoryTheory.isConnected_of_isTerminal WalkingCospan hterm
  let : Limits.PreservesLimitsOfShape WalkingCospan (ObjectProperty.ι
      (fun X : Scheme ↦ X.size < B.cutoff)) := inferInstance
  let : PreservesLimitsOfShape WalkingCospan
      (Over.forget (BigSyntomicSite.obj B S hS)) := inferInstance
  let : PreservesLimitsOfShape WalkingCospan
      (BigSyntomicOver.toScheme B S hS) := inferInstance
  let P := BigSyntomicOver.IsAffineOver B S hS
  let : P.IsClosedUnderIsomorphisms := ⟨fun e h => by
    change IsAffine ((BigSyntomicOver.toScheme B S hS).obj _) at h ⊢
    exact IsAffine.of_isIso ((BigSyntomicOver.toScheme B S hS).map e.inv)⟩
  let : P.IsClosedUnderLimitsOfShape WalkingCospan := by
    apply ObjectProperty.IsClosedUnderLimitsOfShape.mk'
    rintro X ⟨F, hF⟩
    let G := F ⋙ BigSyntomicOver.toScheme B S hS
    let : IsAffine (G.obj WalkingCospan.left) := hF WalkingCospan.left
    let : IsAffine (G.obj WalkingCospan.right) := hF WalkingCospan.right
    let : IsAffine (G.obj WalkingCospan.one) := hF WalkingCospan.one
    have : IsAffine (limit G) :=
      IsAffine.of_isIso (HasLimit.isoOfNatIso (diagramIsoCospan G)).hom
    exact IsAffine.of_isIso (preservesLimitIso
      (BigSyntomicOver.toScheme B S hS) F).hom
  let : Limits.HasPullbacks (BigAffineSyntomic B S hS) := inferInstance
  let : Limits.PreservesLimitsOfShape WalkingCospan u := inferInstance
  apply coverPreserving_of_generators u
    (BigAffineSyntomic.precoverage B S hS) K
  intro X R hR
  obtain ⟨E, hEeq, hE⟩ := hR
  subst R
  rw [← Sieve.generate_map_eq_functorPushforward]
  dsimp [K]
  rw [BigSyntomicOver.topology, GrothendieckTopology.mem_over_iff, Sieve.overEquiv_generate]
  have hbase : Presieve.map (BigSyntomicOver.forget B S hS)
      ((E.map u).presieve₀) ∈ B.precoverage ((u.obj X).left) := by
    refine ⟨(E.map u).map (BigSyntomicOver.forget B S hS), ?_, ?_⟩
    · simp [PreZeroHypercover.presieve₀_map]
    · simpa [u, BigSyntomicOver.IsCovering] using hE.1
  apply B.topology.superset_covering _ (Precoverage.generate_mem_toGrothendieck hbase)
  rw [Sieve.generate_le_iff, PreZeroHypercover.presieve₀_map]
  exact le_trans
    (Presieve.map_le_functorPushforward (F := BigSyntomicOver.forget B S hS)
      (Presieve.map u E.presieve₀))
    (Sieve.le_generate _)

/-- **Stacks 06VD.** The inclusion of affine objects over `S` into the big
syntomic site over `S` is special cocontinuous. Its dense-subsite component
gives the induced equivalence of topoi. -/
@[stacks 06VD]
public theorem BigAffineSyntomic.inclusion_isSpecialCocontinuous
    (B : BigSyntomicSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    IsSpecialCocontinuous
      (BigAffineSyntomic.topology B S hS)
      (BigSyntomicOver.topology B S hS)
      (BigAffineSyntomic.inclusion B S hS) := by
  change Functor.IsCocontinuous _ _ _ ∧ _
  constructor
  · exact inclusion_isCocontinuous B S hS
  · let u := BigAffineSyntomic.inclusion B S hS
    let J := BigAffineSyntomic.topology B S hS
    let K := BigSyntomicOver.topology B S hS
    have hcover := inclusion_isCoverPreserving B S hS
    have hfaithful : ∀ ⦃U' U : BigAffineSyntomic B S hS⦄
        (a b : U' ⟶ U), u.map a = u.map b → Sieve.equalizer a b ∈ J U' := by
      intro U' U a b hab
      obtain rfl := u.map_injective hab
      simp
    have hfull : ∀ ⦃U' U : BigAffineSyntomic B S hS⦄
        (c : u.obj U' ⟶ u.obj U), u.imageSieve c ∈ J U' := by
      intro U' U c
      rw [← u.map_preimage c, Functor.imageSieve_map]
      exact J.top_mem U'
    let : u.IsCocontinuous J K := inclusion_isCocontinuous B S hS
    let : u.IsCoverDense K := inclusion_isCoverDense B S hS
    exact Functor.isDenseSubsite_of_isCocontinuous u J K hcover hfaithful hfull

end AlgebraicGeometry
