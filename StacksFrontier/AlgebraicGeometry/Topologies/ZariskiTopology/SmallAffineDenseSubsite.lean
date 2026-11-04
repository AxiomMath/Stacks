module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.SmallZariskiOpens
public import StacksFrontier.AlgebraicGeometry.Topologies.Zariski.StandardCovering
public import StacksFrontier.AlgebraicGeometry.Topologies.ZariskiTopology.Sites
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp

/-!
# Affine opens form a dense subsite of the small Zariski site

Let `B` be a big Zariski site containing a scheme `S`. The inclusion of the small affine
Zariski site of `S` — the affine open subschemes of `S`, with the standard Zariski coverings —
into the small Zariski site of `S` is a special cocontinuous functor, so it induces an
equivalence between their topoi of sheaves.

## Main results

* `AlgebraicGeometry.SmallAffineZariski.inclusion_isSpecialCocontinuous` — the inclusion is
  special cocontinuous, hence a dense subsite, hence induces an equivalence of topoi.

## Implementation notes

`IsSpecialCocontinuous` packages cocontinuity with Mathlib's `Functor.IsDenseSubsite`, whose
`Functor.IsDenseSubsite.sheafEquiv` is the induced equivalence of sheaf categories; the one
statement therefore carries both conclusions of the source.

Cocontinuity is the substantial half, and is proved by induction over the saturation that
generates the small Zariski topology from its covering families. Given a covering family of an
affine open `U` of `S` and a map `V ⟶ U` from another affine open, one pulls the family back
to `V`, refines the pullback by finitely many basic opens of `V` (Stacks 020Q) and lands the
result inside the site. That last step is where the cardinal bound a big Zariski site puts on
index types has to be respected: a family of open subschemes of `V` is a Zariski covering, so
it is combinatorially equivalent to a selected one, and deduplicating it makes its index type
inject into the selected one's while keeping it finite —
`AlgebraicGeometry.deduplicateFamily` and its lemmas.

Cover density holds because every scheme is covered by affine opens, and an affine open of an
open subscheme of `S` is an affine open of `S`. Local fullness and local faithfulness are
immediate from the inclusion being fully faithful.

Both small categories are essentially small — the small Zariski site is equivalent to the
lattice of opens of `S` by Stacks 020X, and the affine ones form a full subcategory — which is
what makes the right Kan extension along the inclusion exist, hence the induced morphism of
topoi available. Those instances are recorded here.

## References

* [Stacks Project, Tag 0F1B](https://stacks.math.columbia.edu/tag/0F1B)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The small Zariski site of `S` is essentially small: by Stacks 020X it is equivalent to the
lattice of opens of the underlying space of `S`, which is a small category. -/
public instance SmallZariski.essentiallySmall (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : EssentiallySmall.{u} (SmallZariski B S hS) :=
  EssentiallySmall.mk' (smallZariskiSiteEquiv B S hS)

/-- The small affine Zariski site of `S` is essentially small, being a full subcategory of the
small Zariski site. -/
public instance SmallAffineZariski.essentiallySmall (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : EssentiallySmall.{u} (SmallAffineZariski B S hS) :=
  essentiallySmall_of_fully_faithful (SmallAffineZariski.inclusion B S hS)

/-- An open covering of an object of a big Zariski site is refined by a covering family *of
that site*, each of whose members is identified with a member of the given covering over the
base; the refinement is finite whenever the given covering is. The point is the cardinal bound
on index types: a selected representative of the covering supplies the bound, and
deduplicating transports it to a family built out of the given opens themselves. -/
private theorem exists_bounded_openCover_refinement
    (B : BigZariskiSite.{u}) (T : B.Schemes)
    (U : (B.inclusion.obj T).OpenCover.{u + 1}) :
    ∃ F : PreZeroHypercover T, B.IsCovering ⟨T, F⟩ ∧
      (Finite U.I₀ → Finite F.I₀) ∧ (∀ i, IsOpenImmersion (B.inclusion.map (F.f i))) ∧
      ∀ i, ∃ j, ∃ e : B.inclusion.obj (F.X i) ≅ U.X j,
        B.inclusion.map (F.f i) = e.hom ≫ U.f j := by
  classical
  have hsize (i : U.I₀) := by
    have := U.map_prop i
    exact Scheme.size_lt_of_isOpenImmersion (U.f i) T.property
  let Q : PreZeroHypercover T := {
    I₀ := U.I₀
    X i := ⟨U.X i, hsize i⟩
    f i := B.inclusion.preimage (show
      B.inclusion.obj ⟨U.X i, hsize i⟩ ⟶ B.inclusion.obj T from U.f i) }
  have hmap : (Q.map B.inclusion).presieve₀ = U.presieve₀ := by
    rw [PreZeroHypercover.presieve₀_map, PreZeroHypercover.presieve₀,
      Presieve.map_ofArrows]
    show Presieve.ofArrows U.X (fun i => B.inclusion.map (Q.f i)) =
      Presieve.ofArrows U.X U.f
    congr 1
    funext i
    exact B.inclusion.map_preimage _
  have hQ : IsZariskiCovering ⟨T, Q⟩ := by
    show (Q.map B.inclusion).presieve₀ ∈ Scheme.zariskiPretopology _
    rw [hmap]
    exact U.mem_pretopology
  obtain ⟨⟨target, representative⟩, hrepresentative, htarget, hcomb⟩ :=
    B.covering_representative ⟨T, Q⟩ hQ
  cases htarget
  let F := deduplicateFamily Q
  have hF : B.IsCovering ⟨T, F⟩ := by
    refine ⟨?_, (deduplicateFamily_card_le
      (hcomb : Q.CombinatoriallyEquivalent representative)).trans hrepresentative.2⟩
    show (F.map B.inclusion).presieve₀ ∈ Scheme.zariskiPretopology _
    rw [PreZeroHypercover.presieve₀_map, deduplicateFamily_presieve₀,
      ← PreZeroHypercover.presieve₀_map]
    exact hQ
  have hcomparison (i : F.I₀) : ∃ j, ∃ e : B.inclusion.obj (F.X i) ≅ U.X j,
      B.inclusion.map (F.f i) = e.hom ≫ U.f j := by
    obtain ⟨j, rfl⟩ := deduplicateFamily_index Q i
    refine ⟨j, Iso.refl _, ?_⟩
    show B.inclusion.map (Q.f j) = 𝟙 _ ≫ U.f j
    rw [Category.id_comp]
    exact B.inclusion.map_preimage _
  refine ⟨F, hF, fun hfinite => ?_, fun i => ?_, hcomparison⟩
  · let : Finite Q.I₀ := hfinite
    exact deduplicateFamily_finite Q
  · obtain ⟨j, e, h⟩ := hcomparison i
    rw [h]
    let : IsOpenImmersion (U.f j) := U.map_prop j
    infer_instance

/-- The composite of two maps of `B` that are open immersions in `Scheme` is an open immersion. -/
private theorem isOpenImmersion_inclusion_map_comp (B : BigZariskiSite.{u}) {X Y Z : B.Schemes}
    (f : X ⟶ Y) (g : Y ⟶ Z) (hf : IsOpenImmersion (B.inclusion.map f))
    (hg : IsOpenImmersion (B.inclusion.map g)) : IsOpenImmersion (B.inclusion.map (f ≫ g)) := by
  rw [Functor.map_comp]
  infer_instance

/-- The affine objects are cover dense in the small Zariski site: every open subscheme of `S`
is covered by its affine opens, and those are objects of the small affine Zariski site. -/
private theorem smallAffineZariski_isCoverDense
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (SmallAffineZariski.inclusion B S hS).IsCoverDense
      (SmallZariski.topology B S hS) := by
  classical
  let K := SmallZariski.topology B S hS
  constructor
  intro target
  let T := B.inclusion.obj target.obj.left
  let A := T.affineCover
  let U : T.OpenCover.{u + 1} := {
    I₀ := ULift.{u + 1, u} A.I₀
    X i := A.X i.down
    f i := A.f i.down
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x => ?_, fun i => A.map_prop i.down⟩
      obtain ⟨i, y, hy⟩ := A.exists_eq x
      exact ⟨ULift.up i, y, hy⟩ }
  obtain ⟨F, hF, -, hopen, hcomparison⟩ :=
    exists_bounded_openCover_refinement B target.obj.left U
  choose source comparison hcomparison using hcomparison
  let E : PreZeroHypercover target := {
    I₀ := F.I₀
    X i := ⟨Over.mk (F.f i ≫ target.obj.hom),
      isOpenImmersion_inclusion_map_comp B _ _ (hopen i) target.property⟩
    f i := ObjectProperty.homMk (Over.homMk (F.f i) (by simp)) }
  have hmap : E.map (SmallZariski.inclusion B S hS ⋙
      BigZariskiOver.inclusion B S hS) = F := by
    ext <;> rfl
  have hE : SmallZariski.IsCovering B S hS ⟨target, E⟩ := by
    show B.IsCovering ⟨target.obj.left, E.map
      (SmallZariski.inclusion B S hS ⋙ BigZariskiOver.inclusion B S hS)⟩
    rw [hmap]
    exact hF
  have hgen : Sieve.generate E.presieve₀ ∈ K target :=
    (SmallZariski.precoverage B S hS).generate_mem_toGrothendieck ⟨E, rfl, hE⟩
  refine K.superset_covering ?_ hgen
  rw [Sieve.generate_le_iff]
  rintro _ _ ⟨i⟩
  let affine : SmallAffineZariski B S hS := ⟨E.X i, by
    show IsAffine (B.inclusion.obj (F.X i))
    let : IsAffine (U.X (source i)) := by
      show IsAffine (A.X (source i).down)
      infer_instance
    exact IsAffine.of_isIso (comparison i).hom⟩
  exact ⟨⟨affine, 𝟙 _, E.f i, by simp [affine]⟩⟩

/-- Every open covering of an affine open `U` of `S` is refined by a covering family of the
small affine Zariski site, namely by finitely many basic opens of `U`. -/
private theorem smallAffineZariski_standard_refinement
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (target : SmallAffineZariski B S hS)
    (U : ((SmallAffineZariski.toScheme B S hS).obj target).OpenCover.{u + 1}) :
    ∃ E : PreZeroHypercover target,
      SmallAffineZariski.IsCovering B S hS ⟨target, E⟩ ∧
      ∀ i, ∃ j, ∃ lift : (SmallAffineZariski.toScheme B S hS).obj (E.X i) ⟶ U.X j,
        lift ≫ U.f j = (SmallAffineZariski.toScheme B S hS).map (E.f i) := by
  classical
  let T := target.obj.obj.left
  let T' := B.inclusion.obj T
  let : IsAffine T' := target.property
  obtain ⟨V, refinement, hfinite, hbasic⟩ := U.exists_isStandardZariski_refinement
  obtain ⟨F, hF, hFfinite, hopen, hcomparison⟩ := exists_bounded_openCover_refinement B T V
  choose source comparison hcomparison using hcomparison
  have haffine (i : F.I₀) : IsAffine (B.inclusion.obj (F.X i)) := by
    obtain ⟨f, basicComparison, -⟩ := hbasic (source i)
    exact IsAffine.of_isIso ((comparison i).trans basicComparison).hom
  let E : PreZeroHypercover target := {
    I₀ := F.I₀
    X i := ⟨⟨Over.mk (F.f i ≫ target.obj.obj.hom),
      isOpenImmersion_inclusion_map_comp B _ _ (hopen i) target.obj.property⟩, haffine i⟩
    f i := ObjectProperty.homMk
      (ObjectProperty.homMk (Over.homMk (F.f i) (by simp))) }
  have hmap : E.map (SmallAffineZariski.inclusion B S hS ⋙
      SmallZariski.inclusion B S hS ⋙ BigZariskiOver.inclusion B S hS) = F := by
    ext <;> rfl
  have hscheme : E.map (SmallAffineZariski.toScheme B S hS) = F.map B.inclusion := by
    ext <;> rfl
  have hE : SmallAffineZariski.IsCovering B S hS ⟨target, E⟩ := by
    refine ⟨?_, ?_, hFfinite hfinite, ?_⟩
    · show B.IsCovering ⟨T, E.map (SmallAffineZariski.inclusion B S hS ⋙
        SmallZariski.inclusion B S hS ⋙ BigZariskiOver.inclusion B S hS)⟩
      rw [hmap]
      exact hF
    · show (E.map (SmallAffineZariski.toScheme B S hS)).presieve₀ ∈
        Scheme.zariskiPrecoverage T'
      rw [hscheme]
      exact hF.1
    · intro i
      obtain ⟨f, basicComparison, hbasicComparison⟩ := hbasic (source i)
      refine ⟨f, (comparison i).trans basicComparison, ?_⟩
      show B.inclusion.map (F.f i) = _
      rw [hcomparison i, hbasicComparison]
      simp only [Iso.trans_hom]
      rfl
  refine ⟨E, hE, fun i => ?_⟩
  refine ⟨refinement.s₀ (source i), (comparison i).hom ≫ refinement.h₀ (source i), ?_⟩
  rw [Category.assoc, refinement.w₀]
  exact (hcomparison i).symm

/-- The inclusion of the small affine Zariski site into the small Zariski site is
cocontinuous: a covering sieve of an open subscheme of `S` pulls back, along any map from an
affine open, to a covering sieve of that affine open. -/
private theorem smallAffineZariski_inclusion_isCocontinuous
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (SmallAffineZariski.inclusion B S hS).IsCocontinuous
      (SmallAffineZariski.topology B S hS) (SmallZariski.topology B S hS) := by
  classical
  let G := SmallAffineZariski.inclusion B S hS
  let J := SmallAffineZariski.topology B S hS
  let H := SmallZariski.toScheme B S hS
  have hSat : ∀ {target : SmallZariski B S hS} {R : Sieve target},
      (SmallZariski.precoverage B S hS).Saturate target R →
      ∀ (affine : SmallAffineZariski B S hS) (arrow : G.obj affine ⟶ target),
        (R.pullback arrow).functorPullback G ∈ J affine := by
    intro target R hR
    induction hR with
    | of target P hP =>
      intro affine arrow
      obtain ⟨E, rfl, hE⟩ := (SmallZariski.mem_precoverage_iff B S hS).mp hP
      let U : (H.obj target).OpenCover.{u + 1} :=
        { toPreZeroHypercover := E.map H, mem₀ := hE.1 }
      let V := U.pullback₁ (H.map arrow)
      obtain ⟨F, hF, hRefinement⟩ :=
        smallAffineZariski_standard_refinement B S hS affine V
      have hRef (i : F.I₀) : Sieve.generate E.presieve₀ (G.map (F.f i) ≫ arrow) := by
        obtain ⟨j, lift, hlift⟩ := hRefinement i
        let schemeLift := lift ≫ U.pullbackHom (H.map arrow) j
        let schemeArrow := B.inclusion.preimage (show
          B.inclusion.obj (F.X i).obj.obj.left ⟶
            B.inclusion.obj (E.X j).obj.left from schemeLift)
        have hcomp : schemeArrow ≫ (E.f j).hom.left =
            (F.f i).hom.hom.left ≫ arrow.hom.left := by
          apply B.inclusion.map_injective
          rw [Functor.map_comp, Functor.map_preimage, Functor.map_comp]
          show schemeLift ≫ U.f j =
            (SmallAffineZariski.toScheme B S hS).map (F.f i) ≫ H.map arrow
          have hcond : U.pullbackHom (H.map arrow) j ≫ U.f j = V.f j ≫ H.map arrow :=
            pullback.condition.symm
          rw [Category.assoc, hcond, ← Category.assoc, hlift]
        let overArrow : (F.X i).obj.obj ⟶ (E.X j).obj :=
          Over.homMk schemeArrow (by
            rw [← (E.f j).hom.w, ← Category.assoc, hcomp, Category.assoc, arrow.hom.w]
            show (F.f i).hom.hom.left ≫ affine.obj.obj.hom = _
            exact (F.f i).hom.hom.w)
        refine ⟨E.X j, ObjectProperty.homMk overArrow, E.f j, ⟨j⟩, ?_⟩
        apply ObjectProperty.hom_ext
        apply Over.OverMorphism.ext
        exact hcomp
      have hgen : Sieve.generate F.presieve₀ ∈ J affine :=
        (SmallAffineZariski.precoverage B S hS).generate_mem_toGrothendieck ⟨F, rfl, hF⟩
      refine J.superset_covering ?_ hgen
      rw [Sieve.generate_le_iff]
      rintro _ _ ⟨i⟩
      exact hRef i
    | top target =>
      intro affine arrow
      simp
    | pullback target R hR middle arrow ih =>
      intro affine lift
      rw [← Sieve.pullback_comp]
      exact ih affine (lift ≫ arrow)
    | transitive target R Q hR hQ ihR ihQ =>
      intro affine arrow
      apply J.transitive (ihR affine arrow)
      intro smaller lift hlift
      rw [← Sieve.functorPullback_pullback]
      simpa [← Sieve.pullback_comp, Category.assoc] using ihQ hlift smaller (𝟙 _)
  constructor
  intro affine R hR
  change (SmallZariski.precoverage B S hS).Saturate (G.obj affine) R at hR
  simpa using hSat hR affine (𝟙 _)

/-- **Stacks 0F1B.** The inclusion of the small affine Zariski site of a scheme into its small
Zariski site is a special cocontinuous functor. Its dense-subsite component is the induced
equivalence of topoi `Sh(S_{affine, Zar}) ≌ Sh(S_Zar)`, given by
`CategoryTheory.Functor.IsDenseSubsite.sheafEquiv`. -/
@[stacks 0F1B]
public theorem SmallAffineZariski.inclusion_isSpecialCocontinuous
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsSpecialCocontinuous (SmallAffineZariski.topology B S hS)
      (SmallZariski.topology B S hS) (SmallAffineZariski.inclusion B S hS) := by
  let G := SmallAffineZariski.inclusion B S hS
  let P := SmallAffineZariski.precoverage B S hS
  let J := SmallAffineZariski.topology B S hS
  let K := SmallZariski.topology B S hS
  let : G.IsCoverDense K := smallAffineZariski_isCoverDense B S hS
  let : G.IsCocontinuous J K := smallAffineZariski_inclusion_isCocontinuous B S hS
  have hPmap : P ≤ (K.toPrecoverage).comap G := by
    intro affine R hR
    obtain ⟨E, hEq, hCover⟩ := (SmallAffineZariski.mem_precoverage_iff B S hS).mp hR
    rw [Precoverage.mem_comap_iff, hEq, ← PreZeroHypercover.presieve₀_map,
      GrothendieckTopology.mem_toPrecoverage_iff]
    exact (SmallZariski.precoverage B S hS).generate_mem_toGrothendieck
      ⟨E.map G, rfl, hCover.1⟩
  have hle : J ≤ G.restrictedTopology K := Precoverage.toGrothendieck_monotone hPmap
  have hge : G.restrictedTopology K ≤ J := by
    intro affine R hR
    have hpull := Functor.cover_lift (G := G) (J := J) (K := K)
      ((Functor.mem_restrictedTopology_iff (G := G) (K := K)).mp hR)
    rwa [Sieve.functorPullback_functorPushforward_eq] at hpull
  show G.IsCocontinuous J K ∧ G.IsDenseSubsite J K
  refine ⟨inferInstance, ?_⟩
  rw [le_antisymm hle hge]
  infer_instance

end AlgebraicGeometry

end
