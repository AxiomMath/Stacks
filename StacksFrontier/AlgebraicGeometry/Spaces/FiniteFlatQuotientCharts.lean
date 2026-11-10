module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.FiniteFlatQuotientAffine
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.InvariantAffineCover
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionQuotientImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.Coproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotientFromPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteFlatQuotientInvariantPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.GroupoidQuotientRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCoverRepresentable
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quotient of a finite locally free groupoid by an invariant affine covering

Let `(U, R, s, t, c)` be a groupoid scheme over `S` with `s` and `t` finite locally free and with
`(t, s)` an equivalence relation, and suppose that `U` is covered by `R`-invariant affine opens.
Then for every big fppf site of `S` containing `S`, `U` and `R` the fppf quotient sheaf `U/R` is
representable, and the representing scheme `M` for that site carries a morphism `f : U ⟶ M` of
`S`-schemes which is finite locally free, surjective, and whose kernel pair is `(t, s)`, that is
`R = U ×_M U`. Since those three properties of `f` are properties of schemes rather than of the
site, one such `M` then represents `U/R` on *every* big fppf site, so the groupoid has a finite
flat quotient in the sense of `Stacks.Groupoids.FiniteFlatQuotient`. This is Tag 07S6.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenImmersion_chart_quotientSheaf_of_isInvariantOpen`: **the
  chart of the quotient sheaf attached to one `R`-invariant affine open.** The quotient of the
  restriction of the groupoid to an `R`-invariant affine open `V` of `U` is representable by an
  object `X` of the site of size at most that of `U`, and the induced morphism `yoneda.obj X ⟶ U/R`
  is a representable open immersion, received from an object `Y` of the site presenting `V` by a
  surjective finite locally free morphism `Y ⟶ X`.
* `AlgebraicGeometry.Space.isRepresentable_quotientSheaf_of_isInvariantOpen_isAffineOpen_cover`:
  **the quotient sheaf of such a groupoid is representable.**
* `AlgebraicGeometry.Space.isFiniteLocallyFree_of_localAffineQuotients`: a morphism whose kernel
  pair is the given relation is finite locally free as soon as each member of a covering of `U` by
  invariant opens maps, by a surjective finite locally free morphism, onto an open subscheme of the
  target compatibly with it.
* `AlgebraicGeometry.Space.exists_quotientMap_isRepresented_of_isInvariantOpen_isAffineOpen_cover`
  and `AlgebraicGeometry.Space.exists_quotientMap_isRepresented_of_affineOrbits`: **the quotient
  scheme and the quotient morphism on a given big fppf site** — a quotient scheme `M`, a finite
  locally free surjective quotient morphism, its kernel-pair square, and the representation of the
  quotient sheaf compatibly with it. The second has the covering replaced by the condition that
  every nonempty closed subset of `U` contains a point whose orbit lies in an affine open.
* `AlgebraicGeometry.Space.nonempty_finiteFlatQuotient_of_affineOrbits_of_bigFppfSite`: the
  resulting term of `Stacks.Groupoids.FiniteFlatQuotient`, whose representation clause holds on
  every big fppf site, produced on one given site.
* `AlgebraicGeometry.Space.nonempty_finiteFlatQuotient_of_affineOrbits`: **finite flat quotients of
  groupoids with affine orbits.** The same conclusion with no site hypothesis.

## Implementation notes

The `represents` field of `Stacks.Groupoids.FiniteFlatQuotient` quantifies over every big fppf site
containing the schemes involved, so the construction produces, on one site, a scheme `M` and a
finite locally free surjective morphism `f : U ⟶ M` with the given kernel pair;
`AlgebraicGeometry.quotientSheaf_isRepresented_of_isPullback` then gives the representation on
every site, and `AlgebraicGeometry.finiteFlatQuotientOfIsPullback` assembles the structure. That
one site is produced from `S`, `U` and `R` by `AlgebraicGeometry.BigFppfSite.exists_containing`.

## References

* [Stacks Project, Tag 000J](https://stacks.math.columbia.edu/tag/000J)
* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
* [Stacks Project, Tag 01JJ](https://stacks.math.columbia.edu/tag/01JJ)
* [Stacks Project, Tag 02WU](https://stacks.math.columbia.edu/tag/02WU)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 03JE](https://stacks.math.columbia.edu/tag/03JE)
* [Stacks Project, Tag 07S6](https://stacks.math.columbia.edu/tag/07S6)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Cardinal Opposite
open Stacks.Groupoids Stacks.Morphisms AlgebraicGeometry.GroupoidScheme

noncomputable section

universe u

namespace AlgebraicGeometry.Space

/-- An open immersion with range `U` is isomorphic to `U` over the ambient scheme. -/
private theorem exists_iso_hom_comp_ι_eq {X Z : Scheme.{u}} (f : Z ⟶ X)
    [AlgebraicGeometry.IsOpenImmersion f] (U : X.Opens) (hf : Set.range f.base = U) :
    ∃ α : Z ≅ U.toScheme, α.hom ≫ U.ι = f :=
  ⟨AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq f U.ι (by rw [hf, U.range_ι]),
    AlgebraicGeometry.IsOpenImmersion.isoOfRangeEq_hom_fac _ _ _⟩

/-- **The chart of the fppf quotient sheaf attached to an invariant affine open.** Let
`(U, R, s, t, c)` be a groupoid scheme over `S` with `s` and `t` finite locally free and with
`(t, s)` an equivalence relation, and let `V` be an `R`-invariant affine open of `U`. Then there
are objects `X` and `Y` of the big fppf site of `S`, with `X` of size at most that of `U`, a
morphism `gS : Y ⟶ U` of `S`-schemes which is an open immersion with image `V`, a surjective finite
locally free morphism `π : Y ⟶ X`, and a representable open immersion `k : yoneda.obj X ⟶ U/R` such
that the chart `k` applied to a point of `Y` composed with `π` is the canonical projection applied
to the corresponding point of `U`, and such that every point of `U` over an object of the site
whose image lies in `V` factors through `gS`. -/
theorem exists_isOpenImmersion_chart_quotientSheaf_of_isInvariantOpen {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source]
    (B : BigFppfSite.{u}) (hS : B.Contains S) (hU : B.Contains G.objects.left)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {V : G.objects.left.Opens} (hVinv : IsInvariantOpen G V) (hVaff : IsAffineOpen V) :
    let F : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
    let J := BigFppfOver.topology B S hS
    ∃ (X Y : BigFppfOver B S hS) (π : Y ⟶ X) (gS : F.obj Y ⟶ G.objects)
      (k : yoneda.obj X ⟶ (quotientSheaf J F (groupoidPreRelation G)).obj),
      IsOpenImmersion B S hS k ∧
      ((BigFppfOver.toScheme B S hS).obj X).size ≤ G.objects.left.size ∧
      AlgebraicGeometry.IsOpenImmersion gS.left ∧
      Set.range gS.left.base = (V : Set G.objects.left) ∧
      Function.Surjective ((BigFppfOver.toScheme B S hS).map π).base ∧
      IsFiniteLocallyFree ((BigFppfOver.toScheme B S hS).map π) ∧
      (∀ (T : BigFppfOver B S hS) (a : T ⟶ Y), k.app (op T) (a ≫ π) =
        (toQuotientSheaf J F (groupoidPreRelation G)).app (op T) (F.map a ≫ gS)) ∧
      (∀ (T : BigFppfOver B S hS) (h : F.obj T ⟶ G.objects),
        Set.range h.left.base ⊆ (V : Set G.objects.left) →
        ∃ a : T ⟶ Y, F.map a ≫ gS = h) := by
  have hfull : (Over.post (X := B.obj hS) B.inclusion).Full := inferInstance
  have hfaith : (Over.post (X := B.obj hS) B.inclusion).Faithful := inferInstance
  let F : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let J := BigFppfOver.topology B S hS
  let Uobj : BigFppfOver B S hS :=
    Over.mk (X := B.obj hS) (Y := (⟨G.objects.left, hU⟩ : B.Schemes))
      (ObjectProperty.homMk G.objects.hom)
  obtain ⟨Y, fY, hoi, hrange, hfac⟩ := exists_restrict_bigFppfOver Uobj V
  let g : F.obj Y ⟶ G.objects := F.map fY
  have _ : AlgebraicGeometry.IsOpenImmersion g.left := hoi
  have hgr : Set.range g.left.base = (V : Set G.objects.left) := hrange
  have _ : IsAffine (F.obj Y).left := by
    obtain ⟨e, -⟩ := exists_iso_hom_comp_ι_eq g.left V hgr
    have _ : IsAffine V.toScheme := hVaff
    exact IsAffine.of_isIso e.hom
  have hinv : ∀ r : G.arrows.left, G.source.left.base r ∈ Set.range g.left.base →
      G.target.left.base r ∈ Set.range g.left.base :=
    forall_mem_range_of_isInvariantOpen G g hVinv hgr
  let Rst := GroupoidScheme.restrict G g
  have hobj : Rst.groupoid.objects = F.obj Y := Rst.objects_eq
  have hobjl : Rst.groupoid.objects.left = (F.obj Y).left := congrArg Over.left hobj
  have _ : IsAffine Rst.groupoid.objects.left := by rw [hobjl]; infer_instance
  have _ : IsAffine Rst.groupoid.arrows.left := restriction_isAffine_arrows G g Rst hinv
  have _ : IsFiniteLocallyFree Rst.groupoid.source.left :=
    restriction_source_isFiniteLocallyFree G g Rst hinv
  have _ : IsFiniteLocallyFree Rst.groupoid.target.left :=
    restriction_target_isFiniteLocallyFree G g Rst hinv
  have _ : IsEquivalenceRelation Rst.groupoid.target Rst.groupoid.source :=
    restriction_isEquivalenceRelation G g Rst
  have hYc : B.Contains Rst.groupoid.objects.left := by rw [hobjl]; exact Y.left.property
  have hMc : B.Contains (quotientOver Rst.groupoid).left :=
    contains_quotientOver Rst.groupoid B hYc
  let Xi : BigFppfOver B S hS :=
    Over.mk (X := B.obj hS) (Y := (⟨(quotientOver Rst.groupoid).left, hMc⟩ : B.Schemes))
      (ObjectProperty.homMk (quotientOver Rst.groupoid).hom)
  obtain ⟨hMsh, q, hq, hqfac⟩ := quotientSheaf_isRepresented Rst.groupoid B hS
  have : IsIso q.hom := (sheafToPresheaf _ _).map_isIso q
  let e := asIso q.hom
  let pr : Rst.groupoid.objects ⟶ quotientOver Rst.groupoid := quotientProjection Rst.groupoid
  let pr' : F.obj Y ⟶ F.obj Xi := eqToHom hobj.symm ≫ pr
  let π : Y ⟶ Xi := F.preimage pr'
  have hFπ : F.map π = pr' := F.map_preimage pr'
  have hπleft : (BigFppfOver.toScheme B S hS).map π =
      (eqToHom hobj.symm).left ≫ objectsToInvariantSpectrum Rst.groupoid := by
    have h1 : (BigFppfOver.toScheme B S hS).map π = (F.map π).left := rfl
    rw [h1, hFπ]
    rfl
  have hisoe : IsIso (eqToHom hobj.symm).left :=
    inferInstanceAs (IsIso ((Over.forget S).map (eqToHom hobj.symm)))
  refine ⟨Xi, Y, π, g, yonedaToPoints F Xi ≫ e.inv ≫ (restrictionQuotientMap J F G g Rst).hom,
    ?_, ?_, hoi, hgr, ?_, ?_, ?_, ?_⟩
  · let Φ : yoneda.obj Xi ≅
        (quotientSheaf J F (PreRelation.restrict (groupoidPreRelation G) g)).obj :=
      (asIso (yonedaToPoints F Xi)).trans (e.symm.trans
        ((sheafToPresheaf J (Type u)).mapIso (groupoidRestrictionQuotientIso J F G g Rst)))
    have hΦ : yonedaToPoints F Xi ≫ e.inv ≫ (restrictionQuotientMap J F G g Rst).hom =
        Φ.hom ≫ (restrictQuotientSheafMap J F (groupoidPreRelation G) g).hom := by
      rw [restrictionQuotientMap_factor]
      rfl
    rw [hΦ]
    exact MorphismProperty.RespectsIso.precomp _ Φ.hom _
      (isOpenImmersion_restrictedQuotientMap_of_groupoid G B hS g)
  · refine le_trans (size_quotientOver_le Rst.groupoid) ?_
    rw [hobjl]
    exact Scheme.size_le_of_isOpenImmersion g.left
  · rw [hπleft]
    exact (MorphismProperty.RespectsIso.precomp @Surjective (eqToHom hobj.symm).left _
      ((surjective_iff _).2 (surjective_objectsToInvariantSpectrum Rst.groupoid))).surj
  · rw [hπleft]
    exact MorphismProperty.RespectsIso.precomp (@IsFiniteLocallyFree) (eqToHom hobj.symm).left _
      (objectsToInvariantSpectrum_isFiniteLocallyFree Rst.groupoid)
  · intro T a
    let z : ToType ((Stacks.Groupoids.points F Rst.groupoid.objects).obj (op T)) :=
      F.map a ≫ eqToHom hobj.symm
    have key1 := ConcreteCategory.congr_hom (NatTrans.congr_app hqfac (op T)) z
    have key2 := ConcreteCategory.congr_hom (NatTrans.congr_app
      (toQuotientSheaf_comp_quotientSheafMap J F (groupoidPreRelation Rst.groupoid)
        (groupoidPreRelation G) Rst.hom.mapArrows Rst.hom.mapObjects
        (by simpa [groupoidPreRelation, PreRelation.source] using Rst.hom.map_source)
        (by simpa [groupoidPreRelation, PreRelation.target] using Rst.hom.map_target)) (op T)) z
    have heinv : ∀ w, e.inv.app (op T) (e.hom.app (op T) w) = w := fun w =>
      ConcreteCategory.congr_hom (NatTrans.congr_app e.hom_inv_id (op T)) w
    have hzmap : z ≫ Rst.hom.mapObjects = F.map a ≫ g := by
      rw [Rst.mapObjects_eq, show z = F.map a ≫ eqToHom hobj.symm from rfl, Category.assoc,
        ← Category.assoc (eqToHom hobj.symm), eqToHom_trans, eqToHom_refl, Category.id_comp]
    have hz' : z ≫ pr = F.map a ≫ pr' := Category.assoc _ _ _
    have hstep : F.map (a ≫ π) = e.hom.app (op T)
        ((toQuotientSheaf J F (groupoidPreRelation Rst.groupoid)).app (op T) z) := by
      rw [F.map_comp, hFπ, ← hz']
      exact key1.symm
    change (restrictionQuotientMap J F G g Rst).hom.app (op T)
      (e.inv.app (op T) (F.map (a ≫ π))) = _
    rw [hstep, heinv, show (restrictionQuotientMap J F G g Rst).hom.app (op T)
        ((toQuotientSheaf J F (groupoidPreRelation Rst.groupoid)).app (op T) z) =
      (toQuotientSheaf J F (groupoidPreRelation G)).app (op T)
        (z ≫ Rst.hom.mapObjects) from key2, hzmap]
  · intro T h hsub
    obtain ⟨h₀, rfl⟩ := F.map_surjective (X := T) (Y := Uobj) h
    obtain ⟨a, ha⟩ := hfac h₀ hsub
    exact ⟨a, (F.map_comp a fY).symm.trans (congrArg F.map ha)⟩

/-- **The fppf quotient sheaf of a finite locally free groupoid covered by invariant affine opens
is representable.** For a groupoid scheme over `S` with finite locally free source and target whose
pre-relation is an equivalence relation, and whose object scheme is covered by `R`-invariant affine
opens indexed by a type below the site's cutoff, the quotient sheaf `U/R` is representable on the
big fppf site of `S`. -/
@[stacks 07S6 "representability of the quotient sheaf",
  sga "3 V 4.1" "(iv), special case",
  sga "3 V 7.1" "(iv), special case"]
theorem isRepresentable_quotientSheaf_of_isInvariantOpen_isAffineOpen_cover {S : Scheme.{u}}
    (G : GroupoidScheme S) [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] [IsEquivalenceRelation G.target G.source]
    (B : BigFppfSite.{u}) (hS : B.Contains S) (hU : B.Contains G.objects.left)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {ι : Type u} (hι : #ι < B.cutoff) (V : ι → G.objects.left.Opens)
    (hVinv : ∀ i, IsInvariantOpen G (V i)) (hVaff : ∀ i, IsAffineOpen (V i))
    (hcov : ⨆ i, V i = ⊤) :
    let F : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
    let J := BigFppfOver.topology B S hS
    (quotientSheaf J F (groupoidPreRelation G)).obj.IsRepresentable := by
  classical
  have hfull : (Over.post (X := B.obj hS) B.inclusion).Full := inferInstance
  have hfaith : (Over.post (X := B.obj hS) B.inclusion).Faithful := inferInstance
  let F : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let J := BigFppfOver.topology B S hS
  let Uobj : BigFppfOver B S hS :=
    Over.mk (X := B.obj hS) (Y := (⟨G.objects.left, hU⟩ : B.Schemes))
      (ObjectProperty.homMk G.objects.hom)
  choose X Y π gS k hk hsize hgoi hgr hπsurj hπflf hπeq hfacY using fun i =>
    exists_isOpenImmersion_chart_quotientSheaf_of_isInvariantOpen G B hS hU (hVinv i) (hVaff i)
  have hfactor : ∀ (i : ι) (T : BigFppfOver B S hS) (h : F.obj T ⟶ G.objects),
      Set.range h.left.base ⊆ (V i : Set G.objects.left) →
      ∃ b : T ⟶ X i, (k i).app (op T) b =
        (toQuotientSheaf J F (groupoidPreRelation G)).app (op T) h := by
    intro i T h hsub
    obtain ⟨a, ha⟩ := hfacY i T h hsub
    exact ⟨a ≫ π i, by rw [hπeq i T a, ha]⟩
  refine isRepresentable_of_isOpenImmersion_cover_of_chart B S hS
    (quotientSheaf J F (groupoidPreRelation G)).property hι hU hsize k hk
    (quotientChart J F Uobj (groupoidPreRelation G))
    (isLocallySurjective_quotientChart J F Uobj (groupoidPreRelation G)) ?_
  rintro y ⟨x, rfl⟩
  obtain ⟨p, rfl⟩ := Quot.exists_rep x
  set T : BigFppfOver B S hS := FieldValuedPoint.siteObject B S hS (yoneda.obj Uobj) p
  have hss : Subsingleton (F.obj T).left :=
    inferInstanceAs (Subsingleton (Spec (CommRingCat.of p.carrier)))
  have hne : Nonempty (F.obj T).left :=
    inferInstanceAs (Nonempty (Spec (CommRingCat.of p.carrier)))
  set h₀ : T ⟶ Uobj := p.value
  set x₀ : G.objects.left := (F.map h₀).left.base (Classical.arbitrary _)
  have hmem : x₀ ∈ ⨆ i, V i := by rw [hcov]; trivial
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hmem
  have hsub : Set.range (F.map h₀).left.base ⊆ (V i : Set G.objects.left) := by
    rintro _ ⟨z, rfl⟩
    rw [Subsingleton.elim z (Classical.arbitrary _)]
    exact hi
  obtain ⟨b, hb⟩ := hfactor i T (F.map h₀) hsub
  refine Set.mem_iUnion.mpr ⟨i, FieldValuedPoint.class B S hS (yoneda.obj (X i))
    { carrier := p.carrier, contained := p.contained, toBase := p.toBase, value := b }, ?_⟩
  refine FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS _
    ⟨_, FieldValuedPoint.dominates_refl B S hS _ _, ⟨𝟙 _, ?_⟩⟩
  change (quotientSheaf J F (groupoidPreRelation G)).obj.map (𝟙 T).op
      ((quotientChart J F Uobj (groupoidPreRelation G)).app (op T) h₀) =
    (k i).app (op T) b
  simp only [op_id, CategoryTheory.Functor.map_id]
  exact hb.symm

/-- **Finite local freeness of a quotient morphism from the local quotients.** Let
`(U, R, s, t, c)` be a groupoid scheme over `S` and `f : U ⟶ M` a surjective morphism of
`S`-schemes whose kernel pair is `(t, s)`. Suppose `U` is covered by `R`-invariant opens `V i` and
that each `V i` admits a surjective finite locally free morphism onto a scheme which is an open
subscheme of `M`, compatibly with `f`. Then `f` is finite locally free. -/
theorem isFiniteLocallyFree_of_localAffineQuotients {S : Scheme.{u}} (G : GroupoidScheme S)
    {M : Over S} (f : G.objects ⟶ M) (hpb : IsPullback G.target G.source f f)
    (hsurj : Surjective f.left)
    {ι : Type*} (V : ι → G.objects.left.Opens) (hVinv : ∀ i, IsInvariantOpen G (V i))
    (hcov : ⨆ i, V i = ⊤)
    (hloc : ∀ i, ∃ (Z : Scheme.{u}) (mi : Z ⟶ M.left) (qi : (V i).toScheme ⟶ Z),
      AlgebraicGeometry.IsOpenImmersion mi ∧ IsFiniteLocallyFree qi ∧
      Function.Surjective qi.base ∧ qi ≫ mi = (V i).ι ≫ f.left) :
    IsFiniteLocallyFree f.left := by
  classical
  choose Z mi qi hmoi hqflf hqsurj hqfac using hloc
  set W : ι → M.left.Opens := fun i => @Scheme.Hom.opensRange _ _ (mi i) (hmoi i)
  have hWcoe : ∀ i, (W i : Set M.left) = Set.range (mi i).base := fun i => rfl
  have hpt : ∀ (i) (y : (V i).toScheme),
      (mi i).base ((qi i).base y) = f.left.base ((V i).ι.base y) := fun i y =>
    congrArg (fun φ : (V i).toScheme ⟶ M.left => φ.base y) (hqfac i)
  have hWset : ∀ i, (W i : Set M.left) = f.left.base '' (V i : Set G.objects.left) := by
    intro i
    rw [hWcoe i]
    refine Set.Subset.antisymm ?_ ?_
    · rintro _ ⟨z, rfl⟩
      obtain ⟨y, rfl⟩ := hqsurj i z
      refine ⟨(V i).ι.base y, ?_, (hpt i y).symm⟩
      rw [← Scheme.Opens.range_ι]
      exact ⟨y, rfl⟩
    · rintro _ ⟨x, hx, rfl⟩
      rw [← Scheme.Opens.range_ι] at hx
      obtain ⟨y, rfl⟩ := hx
      exact ⟨(qi i).base y, hpt i y⟩
  have hWsup : iSup W = ⊤ := by
    refine le_antisymm le_top fun z _ => ?_
    obtain ⟨x, hx⟩ := (surjective_iff f.left).mp hsurj z
    have hxmem : x ∈ ⨆ i, V i := by rw [hcov]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hxmem
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨i, ?_⟩
    rw [← SetLike.mem_coe, hWset i]
    exact ⟨x, hi, hx⟩
  choose α hα using fun i =>
    have := hmoi i
    exists_iso_hom_comp_ι_eq (mi i) (W i) (hWcoe i).symm
  refine isFiniteLocallyFree_of_isInvariantOpen_cover G f hpb V hVinv W hWsup hWset
    (fun i => qi i ≫ (α i).hom) (fun i => ?_) (fun i => ?_)
  · rw [Category.assoc, hα, hqfac i]
  · exact MorphismProperty.RespectsIso.postcomp (@IsFiniteLocallyFree) _ _ (hqflf i)

/-- **The quotient scheme and the quotient morphism, on a given big fppf site.** Under the
hypotheses of
`AlgebraicGeometry.Space.isRepresentable_quotientSheaf_of_isInvariantOpen_isAffineOpen_cover` there
are a scheme `M` over `S` belonging to the big fppf site and a morphism `f : U ⟶ M` of `S`-schemes
which is finite locally free and surjective, whose kernel pair is the given pair `(t, s)` — that is
`R = U ×_M U` — and under which the restricted functor of points of `M` is a sheaf representing the
quotient sheaf `U/R` compatibly with `f`. -/
@[stacks 07S6 "the quotient scheme and the three conclusion clauses, on a given site",
  sga "3 V 4.1" "invariant affine cover"]
theorem exists_quotientMap_isRepresented_of_isInvariantOpen_isAffineOpen_cover
    {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source]
    (B : BigFppfSite.{u}) (hS : B.Contains S) (hU : B.Contains G.objects.left)
    (hR : B.Contains G.arrows.left)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    {ι : Type u} (hι : #ι < B.cutoff) (V : ι → G.objects.left.Opens)
    (hVinv : ∀ i, IsInvariantOpen G (V i)) (hVaff : ∀ i, IsAffineOpen (V i))
    (hcov : ⨆ i, V i = ⊤) :
    let F : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
    let J := BigFppfOver.topology B S hS
    ∃ (M : Over S) (f : G.objects ⟶ M), B.Contains M.left ∧
      IsFiniteLocallyFree f.left ∧ Surjective f.left ∧
      IsPullback G.target G.source f f ∧
      ∃ hM : Presheaf.IsSheaf J (Stacks.Groupoids.points F M),
        ∃ q : quotientSheaf J F (groupoidPreRelation G) ⟶
            (⟨Stacks.Groupoids.points F M, hM⟩ : Sheaf J (Type u)),
          IsIso q ∧ toQuotientSheaf J F (groupoidPreRelation G) ≫ q.hom =
            F.op.whiskerLeft (yoneda.map f) := by
  classical
  have hfull : (Over.post (X := B.obj hS) B.inclusion).Full := inferInstance
  have hfaith : (Over.post (X := B.obj hS) B.inclusion).Faithful := inferInstance
  let F : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
  let J := BigFppfOver.topology B S hS
  let Uobj : BigFppfOver B S hS :=
    Over.mk (X := B.obj hS) (Y := (⟨G.objects.left, hU⟩ : B.Schemes))
      (ObjectProperty.homMk G.objects.hom)
  choose X Y π gS k hk hsize hgoi hgr hπsurj hπflf hπeq hfacY using fun i =>
    exists_isOpenImmersion_chart_quotientSheaf_of_isInvariantOpen G B hS hU (hVinv i) (hVaff i)
  have hchart : Presheaf.IsLocallySurjective J
      (quotientChart J F Uobj (groupoidPreRelation G)) :=
    isLocallySurjective_quotientChart J F Uobj (groupoidPreRelation G)
  have hrepr : (quotientSheaf J F (groupoidPreRelation G)).obj.IsRepresentable :=
    isRepresentable_quotientSheaf_of_isInvariantOpen_isAffineOpen_cover G B hS hU hι V
      hVinv hVaff hcov
  let M₀ : BigFppfOver B S hS :=
    @Functor.reprX _ _ (quotientSheaf J F (groupoidPreRelation G)).obj hrepr
  let ε : yoneda.obj M₀ ≅ (quotientSheaf J F (groupoidPreRelation G)).obj :=
    @Functor.reprW _ _ (quotientSheaf J F (groupoidPreRelation G)).obj hrepr
  obtain ⟨p, hp⟩ : ∃ p : Uobj ⟶ M₀,
      yoneda.map p = quotientChart J F Uobj (groupoidPreRelation G) ≫ ε.inv :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hMsh : Presheaf.IsSheaf J (Stacks.Groupoids.points F (F.obj M₀)) :=
    BigFppfOver.isSheaf_post_inclusion_op_comp_yoneda_obj B S hS (F.obj M₀)
  have hcompat : toQuotientSheaf J F (groupoidPreRelation G) ≫
      (ε.inv ≫ yonedaToPoints F M₀) = F.op.whiskerLeft (yoneda.map (F.map p)) := by
    ext T x
    obtain ⟨y, rfl⟩ := F.map_surjective (X := T.unop) (Y := Uobj) x
    have hpy := ConcreteCategory.congr_hom (NatTrans.congr_app hp T) y
    change (yonedaToPoints F M₀).app T (ε.inv.app T
      ((toQuotientSheaf J F (groupoidPreRelation G)).app T (F.map y))) = F.map y ≫ F.map p
    rw [show (toQuotientSheaf J F (groupoidPreRelation G)).app T (F.map y) =
      (quotientChart J F Uobj (groupoidPreRelation G)).app T y from rfl]
    rw [show (yonedaToPoints F M₀).app T (ε.inv.app T
        ((quotientChart J F Uobj (groupoidPreRelation G)).app T y)) =
      (yonedaToPoints F M₀).app T ((yoneda.map p).app T y) from congrArg _ hpy.symm]
    rw [show (yoneda.map p).app T y = y ≫ p from rfl, yonedaToPoints_app]
    exact F.map_comp y p
  let qq : quotientSheaf J F (groupoidPreRelation G) ⟶
      (⟨Stacks.Groupoids.points F (F.obj M₀), hMsh⟩ : Sheaf J (Type u)) :=
    ⟨ε.inv ≫ yonedaToPoints F M₀⟩
  let qinv : (⟨Stacks.Groupoids.points F (F.obj M₀), hMsh⟩ : Sheaf J (Type u)) ⟶
      quotientSheaf J F (groupoidPreRelation G) := ⟨inv (yonedaToPoints F M₀) ≫ ε.hom⟩
  have hqiso : IsIso qq := by
    refine ⟨qinv, Sheaf.hom_ext ?_, Sheaf.hom_ext ?_⟩
    · change (ε.inv ≫ yonedaToPoints F M₀) ≫ (inv (yonedaToPoints F M₀) ≫ ε.hom) = 𝟙 _
      rw [Category.assoc, ← Category.assoc (yonedaToPoints F M₀), IsIso.hom_inv_id,
        Category.id_comp, ε.inv_hom_id]
    · change (inv (yonedaToPoints F M₀) ≫ ε.hom) ≫ (ε.inv ≫ yonedaToPoints F M₀) = 𝟙 _
      rw [Category.assoc, ← Category.assoc ε.hom, ε.hom_inv_id, Category.id_comp,
        IsIso.inv_hom_id]
  have hsurj : Surjective (F.map p).left := by
    have hlsi : Presheaf.IsLocallySurjective J ε.inv :=
      Presheaf.isLocallySurjective_of_iso J ε.inv
    have hls2 : Presheaf.IsLocallySurjective J
        (quotientChart J F Uobj (groupoidPreRelation G) ≫ ε.inv) :=
      @Presheaf.isLocallySurjective_comp _ _ J _ _ _ _ _ _ _ _ _
        (quotientChart J F Uobj (groupoidPreRelation G)) ε.inv hchart hlsi
    have hsieve := Presheaf.imageSieve_mem J
      (quotientChart J F Uobj (groupoidPreRelation G) ≫ ε.inv) (U := op M₀) (𝟙 M₀)
    refine (surjective_iff (F.map p).left).mpr fun z => ?_
    obtain ⟨W, gW, hgW, w, hw⟩ := BigFppfOver.exists_mem_arrows_mem_range B S hS hsieve z
    obtain ⟨t, ht⟩ := hgW
    have ht' : t ≫ p = gW := by
      have h1 : (yoneda.map p).app (op W) t = (yoneda.obj M₀).map gW.op (𝟙 M₀) := by
        rw [hp]; exact ht
      simpa using h1
    refine ⟨(BigFppfOver.toScheme B S hS).map t w, ?_⟩
    rw [← hw, ← ht', (BigFppfOver.toScheme B S hS).map_comp t p, Scheme.Hom.comp_apply]
    rfl
  have hpb : IsPullback G.target G.source (F.map p) (F.map p) :=
    isPullback_of_quotientSheaf_isRepresented G (F.map p) B hS hU hR
      ⟨hMsh, qq, hqiso, hcompat⟩
  have hloc : ∀ i, ∃ (Z : Scheme.{u}) (mi : Z ⟶ (F.obj M₀).left)
      (qi : (V i).toScheme ⟶ Z),
      AlgebraicGeometry.IsOpenImmersion mi ∧ IsFiniteLocallyFree qi ∧
      Function.Surjective qi.base ∧ qi ≫ mi = (V i).ι ≫ (F.map p).left := by
    intro i
    let mi : X i ⟶ M₀ := yoneda.preimage ((k i) ≫ ε.inv)
    have hmi : yoneda.map mi = (k i) ≫ ε.inv := yoneda.map_preimage _
    have hmoi : AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map mi) := by
      have h0 : IsOpenImmersion B S hS (yoneda.map mi) := by
        rw [hmi]
        exact MorphismProperty.RespectsIso.postcomp _ ε.inv (k i) (hk i)
      exact MorphismProperty.of_relative_map (F := yoneda) (f := mi) h0
    obtain ⟨fYi, hfYi⟩ := F.map_surjective (X := Y i) (Y := Uobj) (gS i)
    have hcomp1 : ∀ c : Y i ⟶ X i,
        ε.inv.app (op (Y i)) ((k i).app (op (Y i)) c) = c ≫ mi := fun c =>
      (ConcreteCategory.congr_hom (NatTrans.congr_app hmi (op (Y i))) c).symm
    have hcomp2 : ∀ c : Y i ⟶ Uobj,
        ε.inv.app (op (Y i)) ((toQuotientSheaf J F (groupoidPreRelation G)).app (op (Y i))
          (F.map c)) = c ≫ p := fun c =>
      (ConcreteCategory.congr_hom (NatTrans.congr_app hp (op (Y i))) c).symm
    have e2 : (k i).app (op (Y i)) (π i) =
        (toQuotientSheaf J F (groupoidPreRelation G)).app (op (Y i)) (gS i) := by
      have e1 := hπeq i (Y i) (𝟙 (Y i))
      rw [Category.id_comp] at e1
      have e3 : F.map (𝟙 (Y i)) ≫ gS i = gS i := by
        rw [CategoryTheory.Functor.map_id]
        exact Category.id_comp (gS i)
      rw [e1, e3]
    have hrel : π i ≫ mi = fYi ≫ p := by
      calc π i ≫ mi = ε.inv.app (op (Y i)) ((k i).app (op (Y i)) (π i)) := (hcomp1 (π i)).symm
        _ = ε.inv.app (op (Y i)) ((toQuotientSheaf J F (groupoidPreRelation G)).app (op (Y i))
              (F.map fYi)) := by rw [e2, hfYi]
        _ = fYi ≫ p := hcomp2 fYi
    have hgSleft : (BigFppfOver.toScheme B S hS).map fYi = (gS i).left :=
      congrArg Over.Hom.left hfYi
    have hrelS : (BigFppfOver.toScheme B S hS).map (π i) ≫
        (BigFppfOver.toScheme B S hS).map mi = (gS i).left ≫ (F.map p).left := by
      have h1 : (BigFppfOver.toScheme B S hS).map (π i ≫ mi) =
          (BigFppfOver.toScheme B S hS).map (fYi ≫ p) :=
        congrArg (BigFppfOver.toScheme B S hS).map hrel
      rw [(BigFppfOver.toScheme B S hS).map_comp,
        (BigFppfOver.toScheme B S hS).map_comp] at h1
      rw [h1, hgSleft]
      rfl
    have hgi : AlgebraicGeometry.IsOpenImmersion (gS i).left := hgoi i
    obtain ⟨α, hα⟩ := exists_iso_hom_comp_ι_eq (gS i).left (V i) (hgr i)
    have step2 : α.inv ≫ (gS i).left = (V i).ι := (α.inv_comp_eq).2 hα.symm
    refine ⟨(BigFppfOver.toScheme B S hS).obj (X i),
      (BigFppfOver.toScheme B S hS).map mi,
      α.inv ≫ (BigFppfOver.toScheme B S hS).map (π i), hmoi, ?_, ?_, ?_⟩
    · exact MorphismProperty.RespectsIso.precomp (@IsFiniteLocallyFree) α.inv _ (hπflf i)
    · exact (MorphismProperty.RespectsIso.precomp @Surjective α.inv _
        ((surjective_iff _).2 (hπsurj i))).surj
    · have h3 : α.inv ≫ ((BigFppfOver.toScheme B S hS).map (π i) ≫
          (BigFppfOver.toScheme B S hS).map mi) =
        α.inv ≫ ((gS i).left ≫ (F.map p).left) :=
        congrArg (fun w : (BigFppfOver.toScheme B S hS).obj (Y i) ⟶
          (BigFppfOver.toScheme B S hS).obj M₀ => α.inv ≫ w) hrelS
      have h4 : (α.inv ≫ (gS i).left) ≫ (F.map p).left = (V i).ι ≫ (F.map p).left :=
        congrArg (fun w : (V i).toScheme ⟶ G.objects.left => w ≫ (F.map p).left) step2
      exact (Category.assoc _ _ _).trans
        (h3.trans ((Category.assoc _ _ _).symm.trans h4))
  exact ⟨F.obj M₀, F.map p, M₀.left.property,
    isFiniteLocallyFree_of_localAffineQuotients G (F.map p) hpb hsurj V hVinv hcov hloc,
    hsurj, hpb, hMsh, qq, hqiso, hcompat⟩

/-- **The quotient scheme and the quotient morphism for a groupoid with affine orbits, on a given
big fppf site.** The same conclusion as
`AlgebraicGeometry.Space.exists_quotientMap_isRepresented_of_isInvariantOpen_isAffineOpen_cover`
with the covering by invariant affine opens replaced by the condition that every nonempty closed
subset of `U` contains a point whose `R`-equivalence class `t(s⁻¹({u}))` lies in an affine open of
`U`. -/
@[stacks 07S6 "the three conclusion clauses from the affine-orbit condition, on a given site",
  sga "3 V 4.1" "(iv)"]
theorem exists_quotientMap_isRepresented_of_affineOrbits {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source]
    (B : BigFppfSite.{u}) (hS : B.Contains S) (hU : B.Contains G.objects.left)
    (hR : B.Contains G.arrows.left)
    [HasSheafify (BigFppfOver.topology B S hS) (Type u)]
    (horbit : ∀ Z : Set G.objects.left, IsClosed Z → Z.Nonempty →
      ∃ u ∈ Z, ∃ W : G.objects.left.Opens, IsAffineOpen W ∧
        G.target.left.base '' (G.source.left.base ⁻¹' {u}) ⊆ (W : Set G.objects.left)) :
    let F : BigFppfOver B S hS ⥤ Over S := Over.post B.inclusion
    let J := BigFppfOver.topology B S hS
    ∃ (M : Over S) (f : G.objects ⟶ M), B.Contains M.left ∧
      IsFiniteLocallyFree f.left ∧ Surjective f.left ∧
      IsPullback G.target G.source f f ∧
      ∃ hM : Presheaf.IsSheaf J (Stacks.Groupoids.points F M),
        ∃ q : quotientSheaf J F (groupoidPreRelation G) ⟶
            (⟨Stacks.Groupoids.points F M, hM⟩ : Sheaf J (Type u)),
          IsIso q ∧ toQuotientSheaf J F (groupoidPreRelation G) ≫ q.hom =
            F.op.whiskerLeft (yoneda.map f) := by
  classical
  choose V hVinv hVaff hVmem using
    GroupoidScheme.forall_exists_isInvariantOpen_isAffineOpen_mem G horbit
  have hcov : ⨆ u : G.objects.left, V u = ⊤ :=
    le_antisymm le_top fun u _ => TopologicalSpace.Opens.mem_iSup.mpr ⟨u, hVmem u⟩
  have hι : #(G.objects.left) < B.cutoff :=
    (Scheme.mk_le_two_pow_size G.objects.left).trans_lt (B.cutoff_isStrongPrelimit hU)
  exact exists_quotientMap_isRepresented_of_isInvariantOpen_isAffineOpen_cover G B hS hU hR hι V
    hVinv hVaff hcov

/-- **A finite flat quotient of a groupoid with affine orbits, given a big fppf site.** Let
`(U, R, s, t, c)` be a groupoid scheme over `S` with `s` and `t` finite locally free and with
`(t, s)` an equivalence relation, such that every nonempty closed subset of `U` contains a point
whose `R`-equivalence class lies in an affine open, and suppose given a big fppf site of `S`
containing `S`, `U` and `R`. Then the groupoid has a finite flat quotient in the sense of
`Stacks.Groupoids.FiniteFlatQuotient`. -/
@[stacks 07S6 "the finite flat quotient, given a big fppf site containing the groupoid",
  sga "3 V 4.1" "more general"]
theorem nonempty_finiteFlatQuotient_of_affineOrbits_of_bigFppfSite {S : Scheme.{u}}
    (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source]
    (B : BigFppfSite.{u}) (hS : B.Contains S) (hU : B.Contains G.objects.left)
    (hR : B.Contains G.arrows.left)
    (horbit : ∀ Z : Set G.objects.left, IsClosed Z → Z.Nonempty →
      ∃ u ∈ Z, ∃ W : G.objects.left.Opens, IsAffineOpen W ∧
        G.target.left.base '' (G.source.left.base ⁻¹' {u}) ⊆ (W : Set G.objects.left)) :
    Nonempty (FiniteFlatQuotient G) := by
  classical
  have _ : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    BigFppfOver.hasSheafify_type B S hS
  obtain ⟨M, f, -, hflf, hsurj, hpb, -⟩ :=
    exists_quotientMap_isRepresented_of_affineOrbits G B hS hU hR horbit
  exact ⟨finiteFlatQuotientOfIsPullback G f hflf hsurj hpb⟩

/-- **Finite flat quotients of groupoids with affine orbits.** Let `(U, R, s, t, c)` be a groupoid
scheme over a scheme `S` such that

1. `s, t : R ⟶ U` are finite locally free,
2. `j = (t, s)` is an equivalence relation, and
3. every nonempty closed subset `Z` of `U` contains a point `u` whose `R`-equivalence class
   `t(s⁻¹({u}))` is contained in an affine open of `U`.

Then there is a finite locally free morphism `U ⟶ M` of schemes over `S` with `R = U ×_M U` and
with `M` representing the quotient sheaf `U/R` in the fppf topology — that is, the groupoid has a
finite flat quotient in the sense of `Stacks.Groupoids.FiniteFlatQuotient`, which also records that
`U ⟶ M` is surjective. -/
@[stacks 07S6, sga "3 V 4.1" "more general", sga "3 V 7.1" "special case"]
theorem nonempty_finiteFlatQuotient_of_affineOrbits {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    [IsEquivalenceRelation G.target G.source]
    (horbit : ∀ Z : Set G.objects.left, IsClosed Z → Z.Nonempty →
      ∃ u ∈ Z, ∃ W : G.objects.left.Opens, IsAffineOpen W ∧
        G.target.left.base '' (G.source.left.base ⁻¹' {u}) ⊆ (W : Set G.objects.left)) :
    Nonempty (FiniteFlatQuotient G) := by
  obtain ⟨B, hB⟩ :=
    BigFppfSite.exists_containing ({S, G.objects.left, G.arrows.left} : Set Scheme.{u})
  exact nonempty_finiteFlatQuotient_of_affineOrbits_of_bigFppfSite G B (hB S (by simp))
    (hB _ (by simp)) (hB _ (by simp)) horbit

end AlgebraicGeometry.Space

end

end
