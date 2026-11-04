module

public import Mathlib.AlgebraicGeometry.Cover.Open
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.Coverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementBind
public import StacksFrontier.AlgebraicGeometry.Topologies.StandardPhRefinement
public import StacksFrontier.CategoryTheory.Sites.Pretopology.CombinatorialEquivalence
public import StacksFrontier.CategoryTheory.Sites.Pretopology.EquivalenceComparison

/-!
# Realizing ph coverings inside a big ph site

A big ph site is cut out of all schemes by a cardinal bound, and only a set-sized collection
of ph covering families is retained. A standard ph covering, and a Zariski covering, of an
object of such a site is nevertheless tautologically equivalent to one of the site's own
covering families: its sources are small enough, and the site's representative axiom then
supplies the family. An *arbitrary* ph covering of an object of the site is refined by one of
the site's families, which follows from those two cases.

## Main results

* `AlgebraicGeometry.exists_isCovering_refinement` — an arbitrary ph covering is refined by a
  covering of the site.
* `AlgebraicGeometry.standardPHCovering_tautologicallyEquivalent` — a standard ph covering is
  tautologically equivalent to a covering of the site.
* `AlgebraicGeometry.openCover_tautologicallyEquivalent` — a Zariski covering is
  tautologically equivalent to a covering of the site.
* `AlgebraicGeometry.standardPHCovering_isPHCovering` — a standard ph covering is a ph
  covering.

## Implementation notes

The smallness of the sources is where the two cases differ. For a Zariski covering the
sources are open subschemes of the target, so
`AlgebraicGeometry.Scheme.size_lt_of_isOpenImmersion` applies directly. For a standard ph
covering the sources are affine and locally of finite type over the target, which bounds their
size because the site's cutoff is a strong prelimit above `ℵ₀`; that is
`size_lt_of_affine_locallyOfFiniteType`.

The site's representative axiom replaces a family only up to *combinatorial* equivalence, a
bijection of index types matching the members on the nose; the conclusion here is
*tautological* equivalence, which only asks for isomorphisms over the target. The passage from
one to the other is `tautologicallyEquivalent_of_combMap`. Both cases also have to reindex the
given family by a type in the site's universe before the axiom applies, which for a standard
ph covering is possible because such a family is finite.

Part (1) composes at the level of the *site*, using its own composition axiom
(`CompositionCond`, the second clause of `IsSite`) on the families produced by parts (2) and
(3). Composing ph coverings of *schemes* instead and realizing the result afterwards would need
the unconditional form of Stacks 0DBF part (2) and hence Chow's lemma (Stacks 0202), which this
development does not have; nothing of the kind is used below.

The refinement datum produced for each member of the realized Zariski covering is flattened by
`exists_standardPHCovering_refinement_of_iso` into the form "each member maps into some member of
the given family, compatibly with the structure morphisms". That is what the site-level
composition consumes, and it avoids carrying the fibre products of
`CategoryTheory.PreZeroHypercover.pullback₂` through the assembly of the final refinement.

## References

* [Stacks Project, Tag 0DBK](https://stacks.math.columbia.edu/tag/0DBK)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal

universe u v w u' v'

namespace AlgebraicGeometry


private theorem standardPHCovering_reindex {T : Scheme.{u}} [IsAffine T]
    {J : Type w} (E : PreZeroHypercover.{v} T) (e : J ≃ E.I₀)
    (hE : StandardPHCovering E.f) :
    @StandardPHCovering J T ‹IsAffine T› (fun j => E.X (e j))
      (fun j => E.f (e j)) := by
  classical
  have : Finite E.I₀ := hE.finite
  have : Finite J := Finite.of_equiv E.I₀ e.symm
  obtain ⟨U, g, j, hg, hsurj, hj, hcover, hcomp⟩ := hE.exists_presentation
  refine StandardPHCovering.of_presentation _ (fun i => hE.isAffine (e i))
    g (fun i => j (e i)) hg hsurj (fun i => hj (e i)) ?_ (fun i => hcomp (e i))
  exact (e.surjective.iUnion_comp fun i => Set.range (j i)).trans hcover

/-- A standard ph covering can be reindexed by a type in any given universe. -/
private theorem exists_reindex_standardPHCovering {T : Scheme.{u}} [IsAffine T]
    (E : PreZeroHypercover.{v} T) (hE : StandardPHCovering E.f) :
    ∃ (e : ULift.{w, 0} (Fin (Nat.card E.I₀)) ≃ E.I₀), StandardPHCovering (E.reindex e).f := by
  have : Finite E.I₀ := hE.finite
  let e : ULift.{w, 0} (Fin (Nat.card E.I₀)) ≃ E.I₀ :=
    Equiv.ulift.trans (Finite.equivFin E.I₀).symm
  exact ⟨e, standardPHCovering_reindex E e hE⟩

/-- A standard ph covering is a ph covering: its members are locally of finite type, and over
an affine open of the target its own base change is the required standard refinement. -/
public theorem standardPHCovering_isPHCovering {T : Scheme.{u}} [IsAffine T]
    {E : PreZeroHypercover.{v} T} (hE : StandardPHCovering E.f) :
    IsPHCovering E.X E.f := by
  rw [isPHCovering_iff]
  constructor
  · intro i
    obtain ⟨U, g, j, hg, -, hj, -, hcomp⟩ := hE.exists_presentation
    have : IsProper g := hg
    have : IsOpenImmersion (j i) := hj i
    have h : LocallyOfFiniteType (j i ≫ g) := by infer_instance
    simpa [hcomp i] using h
  · intro V hV
    have : IsAffine V.toScheme := hV
    obtain ⟨e, he⟩ := exists_reindex_standardPHCovering.{u, v, u} E hE
    exact ⟨(E.reindex e).pullback₂ V.ι, he.pullback V.ι,
      ⟨⟨e, fun _ => 𝟙 _, fun _ => rfl⟩⟩⟩

private theorem size_lt_of_affine_locallyOfFiniteType {κ : Cardinal.{u}}
    (hκ : ℵ₀ < κ) (hsl : Cardinal.IsStrongPrelimit κ)
    {X S : Scheme.{u}} [IsAffine X] (f : X ⟶ S)
    [LocallyOfFiniteType f] (hS : S.size < κ) : X.size < κ := by
  have hcov : (⨆ _ : ULift.{u} Unit,
      (⟨⊤, isAffineOpen_top X⟩ : X.affineOpens).1) = ⊤ := by
    ext x; simp
  have hI : Cardinal.mk (ULift.{u} Unit) ≤ S.size ^ Cardinal.aleph0 := by
    calc
      Cardinal.mk (ULift.{u} Unit) ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0
      _ ≤ S.size := Scheme.aleph0_le_size _
      _ ≤ S.size ^ Cardinal.aleph0 := Cardinal.self_le_power _ (by simp)
  exact Scheme.size_lt_of_locallyOfFiniteType_of_affineCover hκ hsl f
    (fun _ => ⟨⊤, isAffineOpen_top X⟩) hcov hI hS

private theorem tautologicallyEquivalent_shrink {C : Type u} [Category.{v} C] {S : C}
    (E : PreZeroHypercover.{w} S) :
    PreZeroHypercover.TautologicallyEquivalent E E.shrink := by
  constructor
  · exact ⟨E.toShrink.s₀, fun i => ⟨Iso.refl _, E.toShrink.w₀ i⟩⟩
  · refine ⟨E.fromShrink.s₀, fun i => ?_⟩
    refine ⟨eqToIso (show E.shrink.X i = E.X (E.fromShrink.s₀ i) from ?_), ?_⟩
    · exact (Presieve.ofArrows_surj E.f _ i.2).choose_spec.1.symm
    · exact E.fromShrink.w₀ i

private theorem eqToHom_family_arrow {C : Type u} [Category.{v} C] {I : Type w}
    {T : C} (X : I → C) (f : ∀ i, X i ⟶ T) {i j : I} (h : i = j) :
    eqToHom (congrArg X h) ≫ f j = f i := by
  cases h
  simp

private theorem tautologicallyEquivalent_of_combMap
    {C : Type u} [Category.{u'} C] {D : Type v} [Category.{v'} D]
    (F : C ⥤ D) {T : C} {E G : PreZeroHypercover.{w} T}
    (h : PreZeroHypercover.CombinatoriallyEquivalent E G) :
    PreZeroHypercover.TautologicallyEquivalent (E.map F) (G.map F) := by
  rcases h with ⟨⟨α, hX, hf⟩, ⟨β, hY, hg⟩⟩
  constructor
  · refine ⟨α, fun i => ⟨eqToIso (congrArg F.obj (hX i)), ?_⟩⟩
    simpa [PreZeroHypercover.map, eqToHom_map] using congrArg F.map (hf i).symm
  · refine ⟨β, fun j => ⟨eqToIso (congrArg F.obj (hY j)), ?_⟩⟩
    simpa [PreZeroHypercover.map, eqToHom_map] using congrArg F.map (hg j).symm

private theorem exists_isCovering_tautologicallyEquivalent
    (B : BigPHSite.{u}) (T : B.Schemes)
    (E : PreZeroHypercover.{u + 1} T.1)
    (hE : IsPHCovering E.X E.f)
    (hsmall : ∀ i, (E.X i).size < B.cutoff) :
    ∃ F : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, F⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent E (F.map B.inclusion) := by
  let W : PreZeroHypercover.{u + 1} T := {
    I₀ := E.I₀
    X i := ⟨E.X i, hsmall i⟩
    f i := ⟨E.f i⟩ }
  have hW : IsPHCoveringInCutoff ⟨T, W⟩ := hE
  obtain ⟨⟨T', G⟩, hG, hT, hcomb⟩ := B.covering_representative ⟨T, W⟩ hW
  cases hT
  exact ⟨G, hG, tautologicallyEquivalent_of_combMap B.inclusion hcomb⟩

/-- **Stacks 0DBK, part (2).** A standard ph covering is tautologically equivalent to a covering
in the big ph site. -/
@[stacks 0DBK "part (2)"]
public theorem standardPHCovering_tautologicallyEquivalent
    (B : BigPHSite.{u}) (T : B.Schemes) [IsAffine T.1]
    (E : PreZeroHypercover.{v} T.1) (hE : StandardPHCovering E.f) :
    ∃ F : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, F⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent E (F.map B.inclusion) := by
  classical
  obtain ⟨e, hE'⟩ := exists_reindex_standardPHCovering.{u, v, u + 1} E hE
  let E' : PreZeroHypercover.{u + 1} T.1 := E.reindex e
  have hEph : IsPHCovering E'.X E'.f := standardPHCovering_isPHCovering hE'
  have hsmall : ∀ i, (E'.X i).size < B.cutoff := by
    intro i
    have : IsAffine (E'.X i) := hE'.isAffine i
    have : LocallyOfFiniteType (E'.f i) := ((isPHCovering_iff _ _).mp hEph).1 i
    exact size_lt_of_affine_locallyOfFiniteType B.aleph0_lt_cutoff
      B.cutoff_isStrongPrelimit (E'.f i) T.2
  obtain ⟨G, hG, htautWG⟩ :=
    exists_isCovering_tautologicallyEquivalent B T E' hEph hsmall
  have htautE' : PreZeroHypercover.TautologicallyEquivalent E E' := by
    constructor
    · refine ⟨e.symm, fun i => ⟨eqToIso (congrArg E.X (e.apply_symm_apply i).symm), ?_⟩⟩
      exact eqToHom_family_arrow E.X E.f (e.apply_symm_apply i).symm
    · exact ⟨e, fun _ => ⟨Iso.refl _, rfl⟩⟩
  exact ⟨G, hG, PreZeroHypercover.tautologicallyEquivalent_trans E E'
    (G.map B.inclusion) htautE' htautWG⟩

/-- **Stacks 0DBK, part (3).** A Zariski open covering is tautologically equivalent to a covering
in the big ph site. -/
@[stacks 0DBK "part (3)"]
public theorem openCover_tautologicallyEquivalent
    (B : BigPHSite.{u}) (T : B.Schemes) (U : T.1.OpenCover.{v}) :
    ∃ F : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, F⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent U.toPreZeroHypercover
          (F.map B.inclusion) := by
  classical
  let S := B.inclusion.obj T
  let E := U.toPreZeroHypercover
  let E' := E.shrink
  have hopen (i : E'.I₀) : IsOpenImmersion (E'.f i) := by
    obtain ⟨j, hX, hf⟩ := Presieve.ofArrows_surj E.f _ i.2
    show IsOpenImmersion i.1.2
    rw [hf]
    infer_instance
  have hcover : ∀ x : S, ∃ i, x ∈ Set.range (E'.f i) := by
    intro x
    obtain ⟨i, y, hy⟩ := U.exists_eq x
    refine ⟨E.toShrink.s₀ i, ?_⟩
    have hf : (E.toShrink.h₀ i ≫ E'.f (E.toShrink.s₀ i)) y = x :=
      (congrArg (fun f => f y) (E.toShrink.w₀ i)).trans hy
    refine ⟨E.toShrink.h₀ i y, ?_⟩
    simpa only [Scheme.Hom.comp_apply] using hf
  let V : S.OpenCover.{u + 1} := {
    I₀ := E'.I₀
    X := E'.X
    f := E'.f
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      exact ⟨hcover, hopen⟩ }
  obtain ⟨G, hG, htautWG⟩ := exists_isCovering_tautologicallyEquivalent B T V.toPreZeroHypercover
    (IsPHCovering.of_openCover V) fun i => Scheme.size_lt_of_isOpenImmersion (V.f i) T.2
  exact ⟨G, hG, PreZeroHypercover.tautologicallyEquivalent_trans E
    V.toPreZeroHypercover (G.map B.inclusion) (tautologicallyEquivalent_shrink E) htautWG⟩

/-- A standard ph covering of an affine open of the target of a ph covering, transported along
an isomorphism and flattened: each of its members maps into a member of the given family,
compatibly with the structure morphisms. This is the datum the site-level composition consumes. -/
private theorem exists_standardPHCovering_refinement_of_iso {S Y : Scheme.{u}} [IsAffine Y]
    {E : PreZeroHypercover.{v} S} (hE : IsPHCovering E.X E.f) (U : S.affineOpens)
    (g : Y ⟶ S) (e : Y ≅ U.1.toScheme) (he : e.hom ≫ U.1.ι = g) :
    ∃ P : PreZeroHypercover.{u} Y, StandardPHCovering P.f ∧
      ∀ k, ∃ (i : E.I₀) (h : P.X k ⟶ E.X i), h ≫ E.f i = P.f k ≫ g := by
  have : IsAffine U.1.toScheme := U.2
  obtain ⟨P₀, hP₀, ⟨φ⟩⟩ := hE.2 U.1 U.2
  refine ⟨⟨P₀.I₀, P₀.X, fun k ↦ P₀.f k ≫ e.inv⟩,
    _root_.AlgebraicGeometry.StandardPHCovering.comp hP₀ inferInstance inferInstance,
    fun k ↦ ?_⟩
  refine ⟨φ.s₀ k, φ.h₀ k ≫ Limits.pullback.fst (E.f (φ.s₀ k)) U.1.ι, ?_⟩
  have hinv : e.inv ≫ g = U.1.ι := by rw [← he, Iso.inv_hom_id_assoc]
  have hw : φ.h₀ k ≫ Limits.pullback.snd (E.f (φ.s₀ k)) U.1.ι = P₀.f k := φ.w₀ k
  have key : φ.h₀ k ≫ Limits.pullback.fst (E.f (φ.s₀ k)) U.1.ι ≫ E.f (φ.s₀ k)
      = P₀.f k ≫ U.1.ι :=
    (congrArg (φ.h₀ k ≫ ·) Limits.pullback.condition).trans
      ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ U.1.ι) hw))
  simp only [Category.assoc]
  rw [hinv]
  exact key

/-- **Stacks 0DBK, part (1).** Every ph covering of an object of a big ph site is refined by one
of the site's own covering families.

The refinement is assembled from parts (2) and (3) by the site's composition axiom: the affine
opens of the target form a Zariski covering, hence by part (3) are tautologically equivalent to a
covering `G` of the site, and each member of `G` is isomorphic over the target to an affine open,
hence by the definition of a ph covering carries a standard ph covering refining the given family
there, which by part (2) is tautologically equivalent to a covering of the site. -/
@[stacks 0DBK "part (1)"]
public theorem exists_isCovering_refinement
    (B : BigPHSite.{u}) (T : B.Schemes)
    (E : PreZeroHypercover.{v} T.1) (hE : IsPHCovering E.X E.f) :
    ∃ F : PreZeroHypercover.{u + 1} T,
      B.IsCovering ⟨T, F⟩ ∧ Nonempty ((F.map B.inclusion).Hom E) := by
  classical
  let S := B.inclusion.obj T
  let O : S.OpenCover.{u + 1} := {
    I₀ := ULift.{u + 1, u} (↑S.affineOpens : Type u)
    X i := i.down.1.toScheme
    f i := i.down.1.ι
    mem₀ := by
      rw [Scheme.presieve₀_mem_precoverage_iff]
      refine ⟨fun x ↦ ?_, fun i ↦ inferInstance⟩
      have hx : x ∈ (⨆ V : (↑S.affineOpens : Type u), V.1) := by
        rw [iSup_affineOpens_eq_top S]; trivial
      obtain ⟨V, hxV⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
      exact ⟨ULift.up V, ⟨⟨x, hxV⟩, rfl⟩⟩ }
  obtain ⟨G, hG, htaut⟩ := openCover_tautologicallyEquivalent B T O
  obtain ⟨β, hβ⟩ := htaut.2
  choose ε hε using hβ
  have hGaffine (j : G.I₀) : IsAffine (B.inclusion.obj (G.X j)) :=
    @IsAffine.of_isIso _ _ (ε j).hom (CategoryTheory.Iso.isIso_hom (ε j)) (β j).down.2
  have hGaffine' (j : G.I₀) : IsAffine (G.X j).1 := hGaffine j
  have hstd (j : G.I₀) : ∃ P : PreZeroHypercover.{u} (B.inclusion.obj (G.X j)),
      @StandardPHCovering P.I₀ _ (hGaffine j) P.X P.f ∧
        ∀ k, ∃ (i : E.I₀) (h : P.X k ⟶ E.X i),
          h ≫ E.f i = P.f k ≫ B.inclusion.map (G.f j) := by
    have := hGaffine j
    exact exists_standardPHCovering_refinement_of_iso hE (β j).down
      (B.inclusion.map (G.f j)) (ε j) (hε j)
  choose P hP hPref using hstd
  choose idx hom hcomm using fun j ↦ hPref j
  have hreal (j : G.I₀) : ∃ H : PreZeroHypercover.{u + 1} (G.X j),
      B.IsCovering ⟨G.X j, H⟩ ∧
        PreZeroHypercover.TautologicallyEquivalent (P j) (H.map B.inclusion) := by
    have := hGaffine' j
    exact standardPHCovering_tautologicallyEquivalent B (G.X j) (P j) (hP j)
  choose H hH htautH using hreal
  choose γ hγ using fun j ↦ (htautH j).2
  choose δ hδ using fun j ↦ hγ j
  refine ⟨G.bind fun j ↦ (H j).pushforward (eqToHom rfl),
    B.isSite.2.1 ⟨T, G⟩ hG (fun j ↦ ⟨G.X j, H j⟩) hH (fun _ ↦ rfl), ⟨?_⟩⟩
  refine ⟨fun s ↦ idx s.1 (γ s.1 s.2),
    fun s ↦ (δ s.1 s.2).hom ≫ hom s.1 (γ s.1 s.2), fun s ↦ ?_⟩
  have h1 : ((δ s.1 s.2).hom ≫ hom s.1 (γ s.1 s.2)) ≫ E.f (idx s.1 (γ s.1 s.2))
      = B.inclusion.map ((H s.1).f s.2) ≫ B.inclusion.map (G.f s.1) := by
    rw [Category.assoc, hcomm s.1 (γ s.1 s.2), ← Category.assoc, hδ s.1 s.2]
    simp [PreZeroHypercover.map]
  refine h1.trans ?_
  have h2 : ((H s.1).f s.2 ≫ eqToHom (rfl : G.X s.1 = G.X s.1)) ≫ G.f s.1
      = (H s.1).f s.2 ≫ G.f s.1 := by simp
  rw [← Functor.map_comp]
  exact congrArg B.inclusion.map h2.symm

end AlgebraicGeometry
