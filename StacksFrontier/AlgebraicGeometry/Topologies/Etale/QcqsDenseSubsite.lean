module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PointsOtherTopologies.SmallEtale
public import StacksFrontier.AlgebraicGeometry.Topologies.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.QcqsSite
import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtalePullbackFpqcAmalgamation
public import StacksFrontier.CategoryTheory.Sites.Topos.ToposMorphismComp

/-!
# The quasi-compact quasi-separated subsite is dense in the small étale site

Let `B` be a big étale site containing a scheme `S`. The objects of the small étale site of `S`
whose underlying scheme is quasi-compact and quasi-separated form a site
(`AlgebraicGeometry.SmallQcqsEtale`), and the inclusion of that subsite into the whole small
étale site is a special cocontinuous functor. Consequently restriction along the inclusion is an
equivalence on sheaves: the small étale topos of `S` is computed by the quasi-compact
quasi-separated objects alone.

Together with `AlgebraicGeometry.hasTerminal_smallQcqsEtale` this is what the subsite is for: for
a quasi-compact quasi-separated `S` it has `S / S` as a terminal object and it computes the small
étale topos, so the étale cohomology of `S` is the cohomology over an object of a site whose
objects descend through a limit of schemes. Neither half holds for the small *affine* étale site,
whose terminal object needs `[IsAffine S]`.

Density holds because every object of the small étale site is covered by its affine opens, and an
affine scheme is quasi-compact and quasi-separated. Cocontinuity holds because an object of the
subsite has quasi-compact underlying scheme, so a covering sieve of its image can be refined by a
*finite* family of affine opens of members of that sieve, which is a covering family of the
subsite.

## Main results

* `AlgebraicGeometry.smallQcqsEtale_isCoverDense` — the inclusion of the quasi-compact
  quasi-separated subsite is cover dense.
* `AlgebraicGeometry.smallQcqsEtale_inclusion_isCocontinuous` — the inclusion is cocontinuous.
* `AlgebraicGeometry.SmallQcqsEtale.inclusion_isSpecialCocontinuous` — the inclusion is a
  special cocontinuous functor, hence exhibits the subsite as a dense subsite.
* `AlgebraicGeometry.SmallQcqsEtale.sheafEquiv` and
  `AlgebraicGeometry.SmallQcqsEtale.sheafEquivAddCommGrp` — the induced equivalence between
  sheaves on the quasi-compact quasi-separated subsite and sheaves on the small étale site, for
  general coefficients and for abelian groups.

## Implementation notes

The covering families of the subsite are required to be finite and to have index type bounded by
the ambient site's covering bound. Both constraints are met at once by deduplicating a finite
jointly surjective family — reindexing it by the set of source-and-arrow pairs it uses — and
bounding the resulting index type through a combinatorially equivalent selected representative of
the ambient big étale site, exactly as for the affine subsite. That an arrow of the subsite with
fixed target is determined by its image in the ambient category of schemes is what makes the
bound transfer.

No `@[stacks]` attribute appears in this file. Tag 04HR is the corresponding statement for the
*affine* subsite, already attributed where it is proved, namely at
`AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous`; the quasi-compact
quasi-separated subsite is not considered in the source and carries no tag of its own.

## References

* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry

/-! ### Open subschemes of objects of the small étale site -/

section OpenSubobject

variable (B : AlgebraicGeometry.BigEtaleSite.{u})

variable (S : Scheme.{u}) (hS : B.Contains S)

/-- An open subscheme of an object `X` of the small étale site of `S`, as an object of that site:
the composite of the open immersion with the étale structure morphism of `X` is étale. -/
private def smallEtaleOpenObj (X : SmallEtale B S hS)
    (V : ((SmallEtale.toScheme B S hS).obj X).Opens) : SmallEtale B S hS :=
  ⟨Over.mk (BigEtaleSite.openObjι B V ≫ X.obj.hom), by
    change Etale (B.inclusion.map (BigEtaleSite.openObjι B V ≫ X.obj.hom))
    rw [B.inclusion.map_comp]
    have : IsOpenImmersion (B.inclusion.map (BigEtaleSite.openObjι B V)) :=
      inferInstanceAs (IsOpenImmersion V.ι)
    infer_instance⟩

/-- The inclusion of an open subscheme of `X` as a morphism of the small étale site of `S`. -/
private def smallEtaleOpenObjι (X : SmallEtale B S hS)
    (V : ((SmallEtale.toScheme B S hS).obj X).Opens) :
    smallEtaleOpenObj B S hS X V ⟶ X :=
  ObjectProperty.homMk (Over.homMk (BigEtaleSite.openObjι B V))

/-- On schemes, the inclusion of an open subscheme of `X` is the inclusion of that open. -/
private theorem toScheme_map_smallEtaleOpenObjι (X : SmallEtale B S hS)
    (V : ((SmallEtale.toScheme B S hS).obj X).Opens) :
    (SmallEtale.toScheme B S hS).map (smallEtaleOpenObjι B S hS X V) = V.ι :=
  rfl

/-- An affine open subscheme of an object of the small étale site of `S`, as an object of the
quasi-compact quasi-separated subsite: an affine scheme is quasi-compact and quasi-separated. -/
private def qcqsOpenObj (X : SmallEtale B S hS)
    (V : ((SmallEtale.toScheme B S hS).obj X).Opens) (hV : AlgebraicGeometry.IsAffineOpen V) :
    SmallQcqsEtale B S hS :=
  ⟨smallEtaleOpenObj B S hS X V, by
    have : IsAffine (V : Scheme.{u}) := hV
    exact ⟨inferInstanceAs (CompactSpace (V : Scheme.{u})),
      quasiSeparatedSpace_of_isAffine (V : Scheme.{u})⟩⟩

end OpenSubobject

/-! ### Covering families of the quasi-compact quasi-separated subsite -/

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The functor sending an object of the quasi-compact quasi-separated étale subsite of `S` to
its underlying object of the ambient size-bounded category of schemes. -/
private abbrev qcqsEtaleToBigScheme :=
  SmallQcqsEtale.inclusion B S hS ⋙ SmallEtale.inclusion B S hS ⋙ Over.forget (B.obj S hS)

/-- An arrow of the quasi-compact quasi-separated étale subsite with fixed target is determined
by its image in the ambient category of schemes: the target's structure morphism recovers the
source's. -/
private theorem qcqsEtaleToBigScheme_arrow_injective (X : SmallQcqsEtale B S hS) :
    Function.Injective (fun p : Σ Y : SmallQcqsEtale B S hS, Y ⟶ X =>
      (⟨(qcqsEtaleToBigScheme B S hS).obj p.1, (qcqsEtaleToBigScheme B S hS).map p.2⟩ :
        Σ Y : B.Scheme, Y ⟶ (qcqsEtaleToBigScheme B S hS).obj X)) := by
  rintro ⟨⟨⟨A, hA⟩, ha⟩, f⟩ ⟨⟨⟨A', hA'⟩, ha'⟩, f'⟩ h
  obtain ⟨Y, k, rfl⟩ := Over.mk_surjective A
  obtain ⟨Y', k', rfl⟩ := Over.mk_surjective A'
  obtain rfl : Y = Y' := congrArg Sigma.fst h
  have hf : f.hom.hom.left = f'.hom.hom.left := eq_of_heq (Sigma.mk.inj h).2
  obtain rfl : k = k' :=
    (Over.w f.hom.hom).symm.trans
      ((congrArg (fun z => z ≫ X.obj.obj.hom) hf).trans (Over.w f'.hom.hom))
  refine Sigma.ext rfl (heq_of_eq ?_)
  apply ObjectProperty.hom_ext
  apply ObjectProperty.hom_ext
  exact Over.OverMorphism.ext hf

/-- **A finite jointly surjective family of the quasi-compact quasi-separated étale subsite is a
covering family after deduplication.** Deduplicating keeps the family finite and does not change
the presieve it generates, and its index type is bounded by the ambient site's covering bound
because it injects into the deduplication of the image family, which a selected combinatorially
equivalent representative bounds. -/
private theorem smallQcqsEtale_isCovering_deduplicateFamily
    {X : SmallQcqsEtale B S hS} (E : PreZeroHypercover.{u + 1} X) [Finite E.I₀]
    (hcov : E.presieve₀.map (SmallQcqsEtale.toScheme B S hS) ∈
      Scheme.etalePrecoverage ((SmallQcqsEtale.toScheme B S hS).obj X)) :
    SmallQcqsEtale.IsCovering B S hS ⟨X, deduplicateFamily E⟩ := by
  classical
  let F := qcqsEtaleToBigScheme B S hS
  have he : AlgebraicGeometry.IsEtaleCovering ⟨F.obj X, E.map F⟩ := by
    show (E.map (F ⋙ B.inclusion)).presieve₀ ∈ Scheme.etalePrecoverage _
    rw [PreZeroHypercover.presieve₀_map]
    exact hcov
  obtain ⟨⟨T, Q⟩, hQ, ht, hcomb⟩ := B.exists_covering_rep ⟨F.obj X, E.map F⟩ he
  cases ht
  let m : (deduplicateFamily E).I₀ → (deduplicateFamily (E.map F)).I₀ := fun z =>
    ⟨⟨F.obj z.1.1, F.map z.1.2⟩, by
      obtain ⟨k, hk⟩ := z.2
      exact ⟨k, congrArg (fun p : Σ Y, Y ⟶ X =>
        (⟨F.obj p.1, F.map p.2⟩ : Σ Y, Y ⟶ F.obj X)) hk⟩⟩
  have hm : Function.Injective m := fun z z' hz => Subtype.ext
    (qcqsEtaleToBigScheme_arrow_injective B S hS X (congrArg Subtype.val hz))
  refine ⟨⟨?_, (Cardinal.mk_le_of_injective hm).trans
    ((deduplicateFamily_card_le hcomb).trans hQ.2)⟩, deduplicateFamily_finite E⟩
  show ((deduplicateFamily E).map (F ⋙ B.inclusion)).presieve₀ ∈ Scheme.etalePrecoverage _
  rw [PreZeroHypercover.presieve₀_map, deduplicateFamily_presieve₀]
  exact hcov

/-- **A sieve of the quasi-compact quasi-separated étale subsite whose arrows are jointly
surjective on points is a covering sieve.** The target's underlying scheme is quasi-compact and
the arrows of the subsite are étale, hence open, so finitely many of the chosen arrows already
cover. -/
private theorem smallQcqsEtale_mem_topology_of_jointlySurjective
    {X : SmallQcqsEtale B S hS} {R : Sieve X}
    (hR : ∀ x : (SmallQcqsEtale.toScheme B S hS).obj X,
      ∃ (Y : SmallQcqsEtale B S hS) (g : Y ⟶ X), R g ∧
        x ∈ Set.range ((SmallQcqsEtale.toScheme B S hS).map g)) :
    R ∈ SmallQcqsEtale.topology B S hS X := by
  classical
  choose Y g hg hx using hR
  have hopen : ∀ z : (SmallQcqsEtale.toScheme B S hS).obj X,
      IsOpen (Set.range ((SmallQcqsEtale.toScheme B S hS).map (g z))) := fun z =>
    ((SmallEtale.toScheme B S hS).map
      ((SmallQcqsEtale.inclusion B S hS).map (g z))).isOpenMap.isOpen_range
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun z : (SmallQcqsEtale.toScheme B S hS).obj X =>
      Set.range ((SmallQcqsEtale.toScheme B S hS).map (g z)))
    hopen fun z _ => Set.mem_iUnion.2 ⟨z, hx z⟩
  let E : PreZeroHypercover.{u + 1} X :=
    { I₀ := ULift.{u + 1, u} {z : (SmallQcqsEtale.toScheme B S hS).obj X // z ∈ t}
      X i := Y i.down.1
      f i := g i.down.1 }
  have : Finite E.I₀ := inferInstanceAs (Finite (ULift.{u + 1, u} _))
  have hcovE : E.presieve₀.map (SmallQcqsEtale.toScheme B S hS) ∈
      Scheme.etalePrecoverage ((SmallQcqsEtale.toScheme B S hS).obj X) := by
    rw [← PreZeroHypercover.presieve₀_map]
    refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun z => ?_, fun i => ?_⟩
    · obtain ⟨y, hy, hmem⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ z))
      exact ⟨ULift.up ⟨y, hy⟩, hmem⟩
    · exact SmallEtale.etale_toScheme_map
        ((SmallQcqsEtale.inclusion B S hS).map (g i.down.1))
  have hgen : Sieve.generate (deduplicateFamily E).presieve₀ ∈
      SmallQcqsEtale.topology B S hS X := by
    show Sieve.generate _ ∈ (SmallQcqsEtale.precoverage B S hS).toGrothendieck X
    rw [Precoverage.mem_toGrothendieck_iff]
    exact Precoverage.Saturate.of X _
      ⟨deduplicateFamily E, rfl, smallQcqsEtale_isCovering_deduplicateFamily B S hS E hcovE⟩
  refine (SmallQcqsEtale.topology B S hS).superset_covering ?_ hgen
  rw [Sieve.generate_le_iff, deduplicateFamily_presieve₀]
  rintro Z f ⟨i⟩
  exact hg i.down.1

/-! ### Cover density -/

/-- **The quasi-compact quasi-separated subsite is cover dense in the small étale site.** Every
object of the small étale site of `S` is covered by affine objects, and affine objects are
quasi-compact and quasi-separated. -/
public theorem smallQcqsEtale_isCoverDense :
    (SmallQcqsEtale.inclusion B S hS).IsCoverDense (SmallEtale.topology B S hS) := by
  have := (SmallAffineEtale.inclusion_isSpecialCocontinuous B S hS).2
  have haff : (SmallAffineEtale.inclusion B S hS).IsCoverDense (SmallEtale.topology B S hS) :=
    Functor.IsDenseSubsite.isCoverDense (SmallAffineEtale.topology B S hS)
      (SmallEtale.topology B S hS) (SmallAffineEtale.inclusion B S hS)
  refine ⟨fun U => (SmallEtale.topology B S hS).superset_covering ?_ (haff.is_cover U)⟩
  rintro Z f ⟨⟨A, l, r, w⟩⟩
  exact ⟨⟨(SmallAffineEtale.toQcqsEtale B S hS).obj A, l, r, w⟩⟩

/-! ### Cocontinuity -/

/-- **The inclusion of the quasi-compact quasi-separated subsite is cocontinuous.** Given a
covering sieve of the image of an object `X` of the subsite, every point of `X` is hit by some
arrow of the sieve, hence by an affine open of the source of such an arrow; those affine opens
are objects of the subsite, so the sieve pulled back to the subsite is jointly surjective and
therefore covering. -/
public theorem smallQcqsEtale_inclusion_isCocontinuous :
    (SmallQcqsEtale.inclusion B S hS).IsCocontinuous
      (SmallQcqsEtale.topology B S hS) (SmallEtale.topology B S hS) := by
  classical
  constructor
  intro X R hR
  refine smallQcqsEtale_mem_topology_of_jointlySurjective B S hS fun x => ?_
  obtain ⟨W, h, hhR, y, hy⟩ := SmallEtale.exists_mem_arrows_mem_range B S hS hR x
  obtain ⟨V, hVaff, hyV, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (x := y) trivial
  refine ⟨qcqsOpenObj B S hS W V hVaff,
    ObjectProperty.homMk (smallEtaleOpenObjι B S hS W V ≫ h), R.downward_closed hhR _, ?_⟩
  have hmap : (SmallQcqsEtale.toScheme B S hS).map
      (ObjectProperty.homMk (smallEtaleOpenObjι B S hS W V ≫ h) :
        qcqsOpenObj B S hS W V hVaff ⟶ X) =
      V.ι ≫ (SmallEtale.toScheme B S hS).map h := by
    rw [← toScheme_map_smallEtaleOpenObjι B S hS W V]
    exact (SmallEtale.toScheme B S hS).map_comp (smallEtaleOpenObjι B S hS W V) h
  refine ⟨⟨y, hyV⟩, ?_⟩
  rw [hmap]
  exact (Scheme.Hom.comp_apply V.ι ((SmallEtale.toScheme B S hS).map h) ⟨y, hyV⟩).trans hy

/-! ### The dense subsite and the equivalence on sheaves -/

/-- **The inclusion of the quasi-compact quasi-separated subsite is a special cocontinuous
functor.** It is cocontinuous and exhibits the subsite as a dense subsite of the small étale site
of `S`, so the induced morphism of topoi is an equivalence. This is the analogue, for the
quasi-compact quasi-separated subsite, of the statement proved for the affine subsite at
`AlgebraicGeometry.SmallAffineEtale.inclusion_isSpecialCocontinuous`. -/
public theorem SmallQcqsEtale.inclusion_isSpecialCocontinuous :
    IsSpecialCocontinuous (SmallQcqsEtale.topology B S hS) (SmallEtale.topology B S hS)
      (SmallQcqsEtale.inclusion B S hS) := by
  let G := SmallQcqsEtale.inclusion B S hS
  let P := SmallQcqsEtale.precoverage B S hS
  let J := SmallQcqsEtale.topology B S hS
  let K := SmallEtale.topology B S hS
  have : G.IsCoverDense K := smallQcqsEtale_isCoverDense B S hS
  have hco : G.IsCocontinuous J K := smallQcqsEtale_inclusion_isCocontinuous B S hS
  have hPmap : P ≤ (K.toPrecoverage).comap G := by
    intro X R hR
    obtain ⟨E, hEq, hCover⟩ := (SmallQcqsEtale.mem_precoverage_iff B S hS).mp hR
    rw [Precoverage.mem_comap_iff, hEq, ← PreZeroHypercover.presieve₀_map,
      GrothendieckTopology.mem_toPrecoverage_iff]
    exact (SmallEtale.precoverage B S hS).generate_mem_toGrothendieck
      ((SmallEtale.mem_precoverage_iff B S hS).2 ⟨E.map G, rfl, hCover.1⟩)
  have hge : G.restrictedTopology K ≤ J := by
    intro X R hR
    have hpull := Functor.cover_lift (G := G) (J := J) (K := K)
      ((Functor.mem_restrictedTopology_iff (G := G) (K := K)).mp hR)
    rwa [Sieve.functorPullback_functorPushforward_eq] at hpull
  have htop : J = G.restrictedTopology K :=
    le_antisymm (Precoverage.toGrothendieck_monotone hPmap) hge
  have hdense : G.IsDenseSubsite J K := by
    rw [htop]
    infer_instance
  exact ⟨hco, hdense⟩

/-- **The subsite computes the small étale topos.** Restriction along the inclusion of the
quasi-compact quasi-separated étale subsite of `S` is an equivalence from sheaves on the small
étale site onto sheaves on the subsite; this is that equivalence, written in the direction from
the subsite. -/
public def SmallQcqsEtale.sheafEquiv (A : Type w) [Category.{w'} A]
    [∀ X : (SmallEtale B S hS)ᵒᵖ,
      HasLimitsOfShape (StructuredArrow X (SmallQcqsEtale.inclusion B S hS).op) A] :
    Sheaf (SmallQcqsEtale.topology B S hS) A ≌ Sheaf (SmallEtale.topology B S hS) A :=
  haveI hspec := SmallQcqsEtale.inclusion_isSpecialCocontinuous B S hS
  haveI := hspec.1
  haveI := hspec.2
  Functor.IsDenseSubsite.sheafEquiv (SmallQcqsEtale.topology B S hS)
    (SmallEtale.topology B S hS) (SmallQcqsEtale.inclusion B S hS) A

/-- **Abelian sheaves on the small étale site of `S` are the same as abelian sheaves on its
quasi-compact quasi-separated étale subsite.** This is the instance of
`AlgebraicGeometry.SmallQcqsEtale.sheafEquiv` in which étale cohomology is computed. -/
public def SmallQcqsEtale.sheafEquivAddCommGrp :
    Sheaf (SmallQcqsEtale.topology B S hS) AddCommGrpCat.{u + 1} ≌
      Sheaf (SmallEtale.topology B S hS) AddCommGrpCat.{u + 1} :=
  SmallQcqsEtale.sheafEquiv B S hS AddCommGrpCat.{u + 1}

end AlgebraicGeometry

end
