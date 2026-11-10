module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.CoveringRefinesSieve
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiPrecoverage
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiSiteAxioms
public import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.StandardCovering
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismDefs

/-!
# Affine objects form a dense subsite of the big Zariski site

Let `B` be a big Zariski site containing a scheme `S`. The inclusion of the big affine Zariski
site over `S` into the big Zariski site over `S` is a special cocontinuous functor, so it
induces an equivalence between their topoi of sheaves: nothing is lost by working only with
affine objects over `S`.

## Main results

* `AlgebraicGeometry.BigAffineZariski.inclusion_isSpecialCocontinuous` — the inclusion is
  special cocontinuous, hence a dense subsite, hence induces an equivalence of topoi.

## Implementation notes

`IsSpecialCocontinuous` packages cocontinuity with Mathlib's `Functor.IsDenseSubsite`, whose
`Functor.IsDenseSubsite.sheafEquiv` is the induced equivalence of sheaf categories; the one
statement therefore carries both conclusions of the source.

Cocontinuity is the substantial half. Given a covering sieve of an affine object, one has to
produce a *standard* covering family of affine objects refining it, and the covering families
of a big Zariski site are only closed under combinatorial equivalence, not literal
restriction. So the construction goes: refine the sieve by a covering family of the big site,
pass to the induced open covering of schemes, refine that by a finite family of standard opens
(Stacks 020Q), deduplicate the resulting family so that its index type injects into the
original one — which is what keeps it inside the site's cardinal bound on index types — and
finally produce a combinatorially equivalent member of the site by Stacks 03WV.

Local fullness and local faithfulness are immediate from the inclusion being fully faithful,
and cover density holds because every scheme is covered by affine opens.

## References

* [Stacks Project, Tag 020W](https://stacks.math.columbia.edu/tag/020W)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- A covering sieve of the big Zariski site contains one of the site's own covering
families. -/
private theorem bigZariskiSite_exists_covering_refining_sieve
    (B : BigZariskiSite.{u}) {X : B.Schemes} {R : Sieve X}
    (hR : R ∈ B.grothendieckTopology X) :
    ∃ E : PreZeroHypercover X, B.IsCovering ⟨X, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [BigZariskiSite.grothendieckTopology] at hR
  exact CategoryTheory.exists_covering_refining_sieve B.IsCovering B.precoverage
    id B.coverings_isSite hR

private theorem deduplicateFamily_card_le_of_maps
    {C : Type*} [Category C] {T : C}
    {E F : PreZeroHypercover T}
    (α : E.I₀ → F.I₀) (hX : ∀ i, E.X i = F.X (α i))
    (hf : ∀ i, E.f i = eqToHom (hX i) ≫ F.f (α i)) :
    Cardinal.mk (deduplicateFamily E).I₀ ≤ Cardinal.mk F.I₀ := by
  classical
  let rep (p : (deduplicateFamily E).I₀) : E.I₀ := Classical.choose p.property
  let m (p : (deduplicateFamily E).I₀) : F.I₀ := α (rep p)
  have hm : Function.Injective m := by
    intro p q hpq
    apply Subtype.ext
    calc
      p.1 = ⟨E.X (rep p), E.f (rep p)⟩ := (Classical.choose_spec p.property).symm
      _ = ⟨E.X (rep q), E.f (rep q)⟩ :=
        pair_eq_of_combIndex_eq α hX hf (rep p) (rep q) hpq
      _ = q.1 := Classical.choose_spec q.property
  exact Cardinal.mk_le_of_injective hm

private theorem finite_standard_refinement
    (B : BigZariskiSite.{u}) (T : B.Schemes)
    [IsAffine (B.inclusion.obj T)] (E : PreZeroHypercover T)
    (hE : B.IsCovering ⟨T, E⟩) :
    ∃ F : PreZeroHypercover T, B.IsCovering ⟨T, F⟩ ∧ Finite F.I₀ ∧
      (∀ i, IsAffine (B.inclusion.obj (F.X i))) ∧
      (∀ i, ∃ f : Γ(B.inclusion.obj T, ⊤),
        ∃ e : B.inclusion.obj (F.X i) ≅ ((B.inclusion.obj T).basicOpen f).toScheme,
          B.inclusion.map (F.f i) = e.hom ≫ ((B.inclusion.obj T).basicOpen f).ι) ∧
      (∀ i, ∃ j, ∃ g : F.X i ⟶ E.X j, g ≫ E.f j = F.f i) := by
  classical
  let T' := B.inclusion.obj T
  let U : T'.OpenCover.{u + 1} := {
    I₀ := E.I₀
    X i := B.inclusion.obj (E.X i)
    f i := B.inclusion.map (E.f i)
    mem₀ := by
      change (E.map B.inclusion).presieve₀ ∈ Scheme.zariskiPretopology T'
      exact hE.1 }
  obtain ⟨V, q, hfin, hbasic⟩ :=
    Scheme.OpenCover.exists_isStandardZariski_refinement U
  let Q : PreZeroHypercover T := {
    I₀ := V.I₀
    X i := by
      let : IsOpenImmersion (V.f i) := V.map_prop i
      exact ⟨V.X i, Scheme.size_lt_of_isOpenImmersion (V.f i) T.property⟩
    f i := B.inclusion.preimage (show
      B.inclusion.obj ⟨V.X i, by
        let : IsOpenImmersion (V.f i) := V.map_prop i
        exact Scheme.size_lt_of_isOpenImmersion (V.f i) T.property⟩ ⟶ T' from V.f i) }
  have hQ : IsZariskiCovering ⟨T, Q⟩ := by
    change (Q.map B.inclusion).presieve₀ ∈ Scheme.zariskiPretopology T'
    rw [PreZeroHypercover.presieve₀_map]
    have hmap : Q.presieve₀.map B.inclusion = V.presieve₀ := by
      rw [PreZeroHypercover.presieve₀, Presieve.map_ofArrows]
      change Presieve.ofArrows V.X (fun i => B.inclusion.map (Q.f i)) =
        Presieve.ofArrows V.X V.f
      congr 1
      funext i
      rw [Functor.map_preimage]
    rw [hmap]
    exact V.mem_pretopology
  obtain ⟨⟨T₀, G⟩, hG, hT, hcomb⟩ := B.covering_representative ⟨T, Q⟩ hQ
  obtain rfl : T = T₀ := hT
  have hcomb' : PreZeroHypercover.CombinatoriallyEquivalent Q G := hcomb
  let F := deduplicateFamily Q
  have hFz : IsZariskiCovering ⟨T, F⟩ := by
    change (F.map B.inclusion).presieve₀ ∈ Scheme.zariskiPretopology T'
    rw [PreZeroHypercover.presieve₀_map, deduplicateFamily_presieve₀,
      ← PreZeroHypercover.presieve₀_map]
    exact hQ
  have hFbound : Cardinal.mk F.I₀ ≤ B.coveringCardinal := by
    obtain ⟨α, hX, hf⟩ := hcomb'.1
    exact (deduplicateFamily_card_le_of_maps α hX hf).trans hG.2
  have hF : B.IsCovering ⟨T, F⟩ := ⟨hFz, hFbound⟩
  have : Finite Q.I₀ := hfin
  have : Finite F.I₀ := deduplicateFamily_finite Q
  have hrep : ∀ i : F.I₀, ∃ k, i = ⟨(⟨Q.X k, Q.f k⟩ : Σ Y : B.Schemes, Y ⟶ T), ⟨k, rfl⟩⟩ :=
    fun i => by
      obtain ⟨k, hk⟩ := i.property
      exact ⟨k, Subtype.ext hk.symm⟩
  have hFaff : ∀ i, IsAffine (B.inclusion.obj (F.X i)) := by
    intro i
    obtain ⟨j, rfl⟩ := hrep i
    obtain ⟨f, e, _⟩ := hbasic j
    exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance
  have hFrefine : ∀ i, ∃ j, ∃ g : F.X i ⟶ E.X j, g ≫ E.f j = F.f i := by
    intro i
    obtain ⟨k, rfl⟩ := hrep i
    let j := q.s₀ k
    let g : Q.X k ⟶ E.X j := B.inclusion.preimage
      (show B.inclusion.obj (Q.X k) ⟶ B.inclusion.obj (E.X j) from q.h₀ k)
    refine ⟨j, g, ?_⟩
    have hq : B.inclusion.map (g ≫ E.f j) = V.f k := by
      rw [Functor.map_comp, Functor.map_preimage]
      change q.h₀ k ≫ U.f (q.s₀ k) = V.f k
      exact q.w₀ k
    have hQf : B.inclusion.map (Q.f k) = V.f k := Functor.map_preimage _ _
    exact B.inclusion.map_injective (hq.trans hQf.symm)
  have hFbasic : ∀ i, ∃ f : Γ(T', ⊤), ∃ e : B.inclusion.obj (F.X i) ≅
      (T'.basicOpen f).toScheme,
      B.inclusion.map (F.f i) = e.hom ≫ (T'.basicOpen f).ι := by
    intro i
    obtain ⟨k, rfl⟩ := hrep i
    obtain ⟨f, e, he⟩ := hbasic k
    refine ⟨f, e, ?_⟩
    change B.inclusion.map (Q.f k) = e.hom ≫ (T'.basicOpen f).ι
    rw [← he]
    change B.inclusion.map (B.inclusion.preimage _) = _
    rw [Functor.map_preimage]
  exact ⟨F, hF, inferInstance, hFaff, hFbasic, hFrefine⟩

private theorem exists_standard_refining_sieve
    (B : BigZariskiSite.{u}) {T : B.Schemes} {R : Sieve T}
    [IsAffine (B.inclusion.obj T)] (hR : R ∈ B.grothendieckTopology T) :
    ∃ F : PreZeroHypercover T, B.IsCovering ⟨T, F⟩ ∧ Finite F.I₀ ∧
      (∀ i, IsAffine (B.inclusion.obj (F.X i))) ∧
      (∀ i, ∃ f : Γ(B.inclusion.obj T, ⊤),
        ∃ e : B.inclusion.obj (F.X i) ≅ ((B.inclusion.obj T).basicOpen f).toScheme,
          B.inclusion.map (F.f i) = e.hom ≫ ((B.inclusion.obj T).basicOpen f).ι) ∧
      F.presieve₀ ≤ R := by
  obtain ⟨E, hE, hER⟩ := bigZariskiSite_exists_covering_refining_sieve B hR
  obtain ⟨F, hF, hFin, hAff, hBasic, hRef⟩ := finite_standard_refinement B T E hE
  refine ⟨F, hF, hFin, hAff, hBasic, ?_⟩
  rw [Presieve.ofArrows_le_iff]
  intro i
  obtain ⟨j, g, hgj⟩ := hRef i
  rw [← hgj]
  exact R.downward_closed (hER _ _ ⟨j⟩) g

/-- A sieve containing a covering presieve is a covering sieve of the induced topology. -/
private theorem mem_toGrothendieck_of_presieve_le {C : Type*} [Category C] {K : Precoverage C}
    {X : C} {P : Presieve X} {R : Sieve X} (hP : P ∈ K X) (h : P ≤ R.arrows) :
    R ∈ K.toGrothendieck X :=
  K.toGrothendieck.superset_covering ((Sieve.generate_le_iff _ _).2 h)
    (Precoverage.generate_mem_toGrothendieck hP)

private theorem inclusion_isCocontinuous
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (BigAffineZariski.inclusion B S hS).IsCocontinuous
      (BigAffineZariski.topology B S hS)
      (BigZariskiOver.topology B S hS) := by
  classical
  let u := BigAffineZariski.inclusion B S hS
  constructor
  intro X R hR
  let T : B.Schemes := (BigZariskiOver.inclusion B S hS).obj (u.obj X)
  have hR' : R ∈ B.grothendieckTopology.over (⟨S, hS⟩ : B.Schemes) (u.obj X) := by
    rwa [← BigZariskiOver.topology_eq_over B ⟨S, hS⟩]
  have hRbase : (Sieve.overEquiv (u.obj X) R) ∈ B.grothendieckTopology T := by
    rwa [GrothendieckTopology.mem_over_iff] at hR'
  have hTaff : IsAffine (B.inclusion.obj T) := X.property
  obtain ⟨F, hF, hFin, hAff, hBasic, hFR⟩ :=
    exists_standard_refining_sieve B (T := T) (R := Sieve.overEquiv (u.obj X) R) hRbase
  let Vobj (i : F.I₀) : BigAffineZariski B S hS :=
    ⟨Over.mk (F.f i ≫ (u.obj X).hom), hAff i⟩
  let vf (i : F.I₀) : Vobj i ⟶ X :=
    ObjectProperty.homMk (Over.homMk (F.f i) rfl)
  let V : PreZeroHypercover X := ⟨F.I₀, Vobj, vf⟩
  have hpre : (F.map B.inclusion).presieve₀ ∈
      Scheme.zariskiPrecoverage (B.inclusion.obj T) := hF.1
  have : IsAffine ((BigZariskiOver.toScheme B S hS).obj (u.obj X)) := hTaff
  let FCover : ((B.inclusion.obj T).Cover Scheme.zariskiPrecoverage) :=
    ⟨F.map B.inclusion, hpre⟩
  have hstd : IsStandardZariskiCovering FCover := ⟨hFin, hBasic⟩
  have hVcover : BigAffineZariski.IsCovering B S hS ⟨X, V⟩ := by
    change BigZariskiOver.IsStandardZariskiCovering B S hS
      ⟨(BigAffineZariski.inclusion B S hS).obj X,
        (V.map (BigAffineZariski.inclusion B S hS))⟩
    exact ⟨hF, ⟨hpre, hstd⟩⟩
  refine mem_toGrothendieck_of_presieve_le (P := V.presieve₀) ⟨V, rfl, hVcover⟩ ?_
  rw [Presieve.ofArrows_le_iff]
  intro i
  change R (u.map (vf i))
  exact (Sieve.overEquiv_iff R (F.f i)).mp (hFR _ _ ⟨i⟩)

private theorem exists_affine_cover_refining_sieve
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : BigAffineZariski B S hS} {R : Sieve X}
    (hR : R ∈ BigAffineZariski.topology B S hS X) :
    ∃ E : PreZeroHypercover X,
      BigAffineZariski.IsCovering B S hS ⟨X, E⟩ ∧ E.presieve₀ ≤ R := by
  rw [BigAffineZariski.topology] at hR
  exact CategoryTheory.exists_covering_refining_sieve
    (BigAffineZariski.IsCovering B S hS)
    (BigAffineZariski.precoverage B S hS)
    (fun ⟨E, hEq, hE⟩ => ⟨E, hE, hEq⟩)
    (BigAffineZariski.isSite B S hS) hR

private theorem inclusion_coverPreserving
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    CategoryTheory.CoverPreserving
      (BigAffineZariski.topology B S hS)
      (BigZariskiOver.topology B S hS)
      (BigAffineZariski.inclusion B S hS) := by
  classical
  let u := BigAffineZariski.inclusion B S hS
  constructor
  intro X R hR
  obtain ⟨E, hE, hER⟩ := exists_affine_cover_refining_sieve B S hS hR
  let V := E.map u
  have hV : BigZariskiOver.IsCovering B S hS ⟨u.obj X, V⟩ := by
    simpa [V, u, BigAffineZariski.inclusion,
      PreZeroHypercover.map] using hE.1
  refine mem_toGrothendieck_of_presieve_le
    ((BigZariskiOver.mem_precoverage_iff _ _ _).2 ⟨V, rfl, hV⟩) ?_
  rw [Presieve.ofArrows_le_iff]
  intro i
  exact R.image_mem_functorPushforward u (hER _ _ ⟨i⟩)

private theorem inclusion_isCoverDense
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (BigAffineZariski.inclusion B S hS).IsCoverDense
      (BigZariskiOver.topology B S hS) := by
  classical
  let u := BigAffineZariski.inclusion B S hS
  constructor
  intro X
  let T : B.Schemes := (BigZariskiOver.inclusion B S hS).obj X
  let U : (B.inclusion.obj T).OpenCover := (B.inclusion.obj T).affineCover
  obtain ⟨E, hE, hTE⟩ :=
    BigZariskiSite.exists_isCovering_tautologicallyEquivalent_openCover B T U
  have hAff : ∀ i, IsAffine (B.inclusion.obj (E.X i)) := by
    intro i
    rcases hTE.2 with ⟨β, hβ⟩
    obtain ⟨e, he⟩ := hβ i
    let : IsAffine (U.X (β i)) := inferInstance
    exact @IsAffine.of_isIso _ _ e.hom e.isIso_hom inferInstance
  let Vobj (i : E.I₀) : BigAffineZariski B S hS :=
    ⟨Over.mk (E.f i ≫ X.hom), hAff i⟩
  let vf (i : E.I₀) : u.obj (Vobj i) ⟶ X :=
    Over.homMk (E.f i) rfl
  let V : PreZeroHypercover X := ⟨E.I₀, fun i => u.obj (Vobj i), vf⟩
  have hVE : V.map (BigZariskiOver.inclusion B S hS) = E := by
    ext <;> simp [V, vf, Vobj, u, BigZariskiOver.inclusion,
      BigAffineZariski.inclusion, PreZeroHypercover.map]
  have hV : BigZariskiOver.IsCovering B S hS ⟨X, V⟩ := by
    change B.IsCovering ⟨
      (BigZariskiOver.inclusion B S hS).obj X,
      V.map (BigZariskiOver.inclusion B S hS)⟩
    rw [hVE]
    simpa [T, BigZariskiOver.inclusion] using hE
  refine mem_toGrothendieck_of_presieve_le
    ((BigZariskiOver.mem_precoverage_iff _ _ _).2 ⟨V, rfl, hV⟩) ?_
  rw [Presieve.ofArrows_le_iff]
  intro i
  exact Presieve.in_coverByImage u (vf i)

/-- **Stacks 020W.** The inclusion of the big affine Zariski site over a scheme
into its big Zariski site is special cocontinuous. Its dense-subsite component
gives the induced equivalence of topoi. -/
@[stacks 020W]
public theorem BigAffineZariski.inclusion_isSpecialCocontinuous
    (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) :
    IsSpecialCocontinuous
      (BigAffineZariski.topology B S hS)
      (BigZariskiOver.topology B S hS)
      (BigAffineZariski.inclusion B S hS) := by
  let u := BigAffineZariski.inclusion B S hS
  let J := BigAffineZariski.topology B S hS
  let K := BigZariskiOver.topology B S hS
  change Functor.IsCocontinuous u J K ∧ u.IsDenseSubsite J K
  refine ⟨inclusion_isCocontinuous B S hS, ?_⟩
  let : u.IsCocontinuous J K := inclusion_isCocontinuous B S hS
  let : u.IsCoverDense K := inclusion_isCoverDense B S hS
  have hfaithful : ∀ ⦃U' U : BigAffineZariski B S hS⦄
      (a b : U' ⟶ U), u.map a = u.map b → Sieve.equalizer a b ∈ J U' := by
    intro U' U a b hab
    obtain rfl := u.map_injective hab
    rw [Sieve.equalizer_self]
    exact J.top_mem _
  have hfull : ∀ ⦃U' U : BigAffineZariski B S hS⦄
      (c : u.obj U' ⟶ u.obj U), u.imageSieve c ∈ J U' := by
    intro U' U c
    rw [← u.map_preimage c, Functor.imageSieve_map]
    exact J.top_mem _
  exact Functor.isDenseSubsite_of_isCocontinuous u J K
    (inclusion_coverPreserving B S hS) hfaithful hfull

private noncomputable def affineInclusion_sheafEquiv
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Sheaf (BigAffineZariski.topology B S hS) (Type (u + 1)) ≌
      Sheaf (BigZariskiOver.topology B S hS) (Type (u + 1)) := by
  let u := BigAffineZariski.inclusion B S hS
  let J := BigAffineZariski.topology B S hS
  let K := BigZariskiOver.topology B S hS
  letI : u.IsCocontinuous J K := (BigAffineZariski.inclusion_isSpecialCocontinuous B S hS).1
  letI : u.IsDenseSubsite J K := (BigAffineZariski.inclusion_isSpecialCocontinuous B S hS).2
  exact Functor.IsDenseSubsite.sheafEquiv J K u (Type (u + 1))


end AlgebraicGeometry
