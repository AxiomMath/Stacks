module

public import StacksFrontier.AlgebraicGeometry.Divisors.RankLocalGenerators
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtalePostcompSlice
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentSiteEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRankLocalOnCover

/-!
# Finite local freeness under an equivalence of ringed sites

Stacks 03DM asserts that each local condition of Stacks 03DL is intrinsic to the ringed topos.
This file proves the finite-local-freeness clause, Stacks 03DL (2), and the rank clause of
Stacks 0409, for an equivalence of ringed topoi presented by an equivalence `e : C' ≌ C` of the
underlying ringed sites: a sheaf of modules on `(C, J, R)` is finite locally free, respectively
of rank `r`, exactly when its reindexing along `e` is, over the transported structure sheaf.

It also reconciles the rank clause of Stacks 0409, which asks for a covering of *every* object
of the site, with the rank condition of Stacks 01C6 (3), which asks for a covering of the
*terminal* object: on a ringed site whose slice topologies admit sheafification the two agree.

Finally, the slice form of Stacks 04M0 — postcomposition with an étale morphism of algebraic
spaces, read on the slices of the two small étale sites at a chart — is an equivalence of sites
in the dense-subsite sense, which is the hypothesis under which the transport above applies to
the small étale site of an algebraic space.

## Main definitions

* `AlgebraicGeometry.RingedSite.reindex` is the ringed site obtained by reindexing along an
  equivalence of sites, its structure sheaf being the direct image of the given one.

## Main results

* `Stacks.SheafOfModules.isFiniteFree_reindex_iff`: finite freeness, Stacks 03DE (2), is
  invariant under reindexing along an equivalence of ringed sites.
* `Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_reindex_iff`: **Stacks 03DM for clause (2) of
  Stacks 03DL, for an equivalence of ringed sites.**
* `AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_reindex_iff`: the same for the rank
  clause of Stacks 0409.
* `AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_iff_sheafOfModules`: on a ringed site
  whose slice topologies admit sheafification, the rank clause of Stacks 0409 agrees with the
  rank condition of Stacks 01C6 (3).
* `AlgebraicGeometry.Space.SmallEtale.isDenseSubsite_postcompOverInverse`: the slice comparison
  of Stacks 04M0 along an étale morphism of algebraic spaces is an equivalence of sites in the
  dense-subsite sense.

## Implementation notes

The reindexing functor is `SheafOfModules.pushforward (𝟙 (reindexRing J' e R))`, as for the
invariance of quasi-coherence, and the equivalence of module categories it belongs to is
`Stacks.SheafOfModules.reindexEquivalence`.  Everything here rests on two facts about that
equivalence, both known from the quasi-coherent case: it carries the unit module of `R` to the
unit module of the transported structure sheaf on the nose, and restriction to an object
commutes with it on the nose (`Stacks.SheafOfModules.over_reindex_eq`).  So a presentation of
a module as a coproduct of copies of the structure sheaf travels across by
`Stacks.SheafOfModules.isColimitCofanTransport` with both comparison isomorphisms taken to be the
identity, and the slice case is the same statement for the localized equivalence
`Stacks.SheafOfModules.overSiteEquivalence`.  The index type of the presentation is arbitrary,
so the unranked and the rank-`r` statements are two instances of one transport.

What is not formal is the transport of the *covering family*: a covering sieve of
`e.functor.obj U` pulls back to one of `U` by cocontinuity, and the members produced are the
images of the original ones under `e.inverse`, which forces the comparison of the restriction
to `e.functor.obj (e.inverse.obj (W i))` with the restriction to `W i` along the counit.  That
is `Stacks.SheafOfModules.isColimitCofanOver`, restriction of a finite presentation along a
morphism of the site.  Both covering transports are stated for an arbitrary predicate on the
objects of the site, since neither uses anything about finite local freeness.

`AlgebraicGeometry.RingedSite.reindex` is an abbreviation rather than a definition because the
hypotheses of the transport are typeclasses stated for the topology of the source site, and
instance search must see the topology of the reindexed site as that topology.

The comparison with Stacks 01C6 (3) goes through
`Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_of_free_iso`, whose covering family is indexed
in the universe of the objects of the site, whereas the covering family supplied by Stacks 0409
is indexed in the maximum of the object and morphism universes.  The family is therefore
replaced by the subtype of objects over which the module is a coproduct of `r` copies of the
structure sheaf, which is indexed in the universe of the objects and still covers the terminal
object because it contains the given family.  In the converse direction the local generators of
Stacks 01C6 (3) give an isomorphism from a free module on an index type equivalent to `Fin r`,
and the isomorphism is formed from the explicit invertibility witness carried by
`SheafOfModules.LocalGeneratorsData.IsLocallyFreeData`.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w t

/-! ### Transport of a free presentation along an equivalence of ringed sites -/

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {C' : Type u} [Category.{v} C']
  {J : GrothendieckTopology C} {J' : GrothendieckTopology C'}

variable (e : C' ≌ C) [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J']
  (R : Sheaf J RingCat.{w})

/-- Reindexing along an equivalence of ringed sites carries a presentation of a sheaf of modules
as a coproduct of copies of the structure sheaf to such a presentation of its reindexing. -/
theorem exists_isColimitCofan_reindex (M : SheafOfModules.{w} R) {B : Type t}
    (h : ∃ ι : B → (SheafOfModules.unit R ⟶ M), Nonempty (IsColimit (Cofan.mk M ι))) :
    ∃ ι : B → (SheafOfModules.unit (reindexRing J' e R) ⟶
        (SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M),
      Nonempty (IsColimit (Cofan.mk
        ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M) ι)) := by
  obtain ⟨ι, ⟨hc⟩⟩ := h
  exact ⟨_, ⟨isColimitCofanTransport (reindexEquivalence.{w, w, u, v, u, v} e R)
    (Iso.refl _) (Iso.refl _) ι hc⟩⟩

/-- Reindexing along an equivalence of ringed sites reflects presentations as a coproduct of
copies of the structure sheaf: the inverse equivalence carries one back, and its unit
isomorphism identifies the round trip with the identity. -/
theorem exists_isColimitCofan_of_reindex (M : SheafOfModules.{w} R) {B : Type t}
    (h : ∃ ι : B → (SheafOfModules.unit (reindexRing J' e R) ⟶
        (SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M),
      Nonempty (IsColimit (Cofan.mk
        ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M) ι))) :
    ∃ ι : B → (SheafOfModules.unit R ⟶ M), Nonempty (IsColimit (Cofan.mk M ι)) := by
  obtain ⟨ι, ⟨hc⟩⟩ := h
  exact ⟨_, ⟨isColimitCofanTransport (reindexEquivalence.{w, w, u, v, u, v} e R).symm
    (((reindexEquivalence.{w, w, u, v, u, v} e R).unitIso.app (SheafOfModules.unit R)).symm)
    (((reindexEquivalence.{w, w, u, v, u, v} e R).unitIso.app M).symm) ι hc⟩⟩

/-- **Finite freeness is invariant under an equivalence of ringed sites.**  A sheaf of modules is
finite free, in the sense of Stacks 03DE (2), exactly when its reindexing along an equivalence of
sites is finite free over the transported structure sheaf. -/
theorem isFiniteFree_reindex_iff (M : SheafOfModules.{w} R) :
    SheafOfModules.IsFiniteFree (reindexRing J' e R)
        ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M) ↔
      SheafOfModules.IsFiniteFree R M := by
  rw [SheafOfModules.isFiniteFree_iff_exists_isColimit,
    SheafOfModules.isFiniteFree_iff_exists_isColimit]
  exact ⟨fun ⟨n, h⟩ => ⟨n, exists_isColimitCofan_of_reindex e R M h⟩,
    fun ⟨n, h⟩ => ⟨n, exists_isColimitCofan_reindex e R M h⟩⟩

/-- A presentation of the restriction of `M` to `Y` as a coproduct of `r` copies of the structure
sheaf restricts, along `h : Z ⟶ Y`, to such a presentation over `Z`. -/
theorem exists_isColimitCofanOfRank_over_of_le (M : SheafOfModules.{w} R) {Z Y : C}
    (h : Z ⟶ Y) {r : ℕ}
    (hM : ∃ ι : ∀ _ : Fin r, SheafOfModules.unit (R.over Y) ⟶ M.over Y,
      Nonempty (IsColimit (Cofan.mk (M.over Y) ι))) :
    ∃ ι : ∀ _ : Fin r, SheafOfModules.unit (R.over Z) ⟶ M.over Z,
      Nonempty (IsColimit (Cofan.mk (M.over Z) ι)) := by
  obtain ⟨ι, ⟨hc⟩⟩ := hM
  exact ⟨_, ⟨isColimitCofanOver M h ι hc⟩⟩

/-- Finite freeness of the restriction of a sheaf of modules to `Y` is inherited by its
restriction to any `Z` over `Y`. -/
theorem isFiniteFree_overMap {M : SheafOfModules.{w} R} {Z Y : C} (h : Z ⟶ Y)
    (hM : SheafOfModules.IsFiniteFree (R.over Y) (M.over Y)) :
    SheafOfModules.IsFiniteFree (R.over Z) (M.over Z) := by
  rw [SheafOfModules.isFiniteFree_iff_exists_isColimit] at hM ⊢
  exact exists_isColimitCofan_over_of_le M h hM

section Slice

variable [e.inverse.IsDenseSubsite J J']

omit [e.inverse.IsContinuous J J'] in
/-- The slice case of `Stacks.SheafOfModules.exists_isColimitCofan_reindex`: a presentation of
the restriction of `M` to `e.functor.obj V` gives one of the restriction of its reindexing
to `V`. -/
theorem exists_isColimitCofan_over_reindex (M : SheafOfModules.{w} R) (V : C') {B : Type t}
    (h : ∃ ι : B → (SheafOfModules.unit (R.over (e.functor.obj V)) ⟶
        M.over (e.functor.obj V)),
      Nonempty (IsColimit (Cofan.mk (M.over (e.functor.obj V)) ι))) :
    ∃ ι : B → (SheafOfModules.unit ((reindexRing J' e R).over V) ⟶
        ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over V),
      Nonempty (IsColimit (Cofan.mk
        (((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over V) ι)) :=
  exists_isColimitCofan_reindex (overSiteEquivalence e V) (R.over (e.functor.obj V))
    (M.over (e.functor.obj V)) h

omit [e.inverse.IsContinuous J J'] in
/-- The slice case of `Stacks.SheafOfModules.exists_isColimitCofan_of_reindex`: a presentation of
the restriction of the reindexing of `M` to `V` comes from one of the restriction of `M` to
`e.functor.obj V`. -/
theorem exists_isColimitCofan_of_over_reindex (M : SheafOfModules.{w} R) (V : C') {B : Type t}
    (h : ∃ ι : B → (SheafOfModules.unit ((reindexRing J' e R).over V) ⟶
        ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over V),
      Nonempty (IsColimit (Cofan.mk
        (((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over V) ι))) :
    ∃ ι : B → (SheafOfModules.unit (R.over (e.functor.obj V)) ⟶
        M.over (e.functor.obj V)),
      Nonempty (IsColimit (Cofan.mk (M.over (e.functor.obj V)) ι)) :=
  exists_isColimitCofan_of_reindex (overSiteEquivalence e V) (R.over (e.functor.obj V))
    (M.over (e.functor.obj V)) h

omit [e.inverse.IsContinuous J J'] in
/-- Finite freeness of the restriction of the reindexing of `M` to `V` is finite freeness of the
restriction of `M` to `e.functor.obj V`. -/
theorem isFiniteFree_over_reindex_iff (M : SheafOfModules.{w} R) (V : C') :
    SheafOfModules.IsFiniteFree ((reindexRing J' e R).over V)
        (((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over V) ↔
      SheafOfModules.IsFiniteFree (R.over (e.functor.obj V)) (M.over (e.functor.obj V)) :=
  isFiniteFree_reindex_iff (overSiteEquivalence e V) (R.over (e.functor.obj V))
    (M.over (e.functor.obj V))

omit [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J'] in
/-- A covering family of `e.functor.obj U` whose members satisfy a property after transport along
`e.inverse` gives a covering family of `U` whose members satisfy it: the members produced are the
images `e.inverse.obj (W i)`, and the sieve they generate is covering because `e.functor` is
cocontinuous. -/
theorem exists_cover_reindex {P : C' → Prop} (U : C')
    {I : Type (max u v)} (W : I → C) (g : ∀ i, W i ⟶ e.functor.obj U)
    (hcov : Sieve.ofArrows W g ∈ J (e.functor.obj U)) (hP : ∀ i, P (e.inverse.obj (W i))) :
    ∃ (I' : Type (max u v)) (V : I' → C') (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J' U ∧ ∀ i, P (V i) := by
  refine ⟨I, fun i => e.inverse.obj (W i),
    fun i => e.inverse.map (g i) ≫ (e.unitIso.app U).inv, ?_, hP⟩
  apply J'.superset_covering _ (e.functor.cover_lift J' J hcov)
  intro Z h hh
  replace hh : (Sieve.ofArrows W g).arrows (e.functor.map h) := hh
  rw [Sieve.mem_ofArrows_iff] at hh ⊢
  obtain ⟨i, a, ha⟩ := hh
  refine ⟨i, (e.unitIso.app Z).hom ≫ e.inverse.map a, ?_⟩
  have hnat := e.unit.naturality h
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hnat
  have key : e.inverse.map a ≫ e.inverse.map (g i) = e.inverse.map (e.functor.map h) := by
    rw [← Functor.map_comp, ha]
  simp only [Category.assoc]
  rw [← Category.assoc (e.inverse.map a), key, ← Category.assoc,
    show (e.unitIso.app Z).hom = e.unit.app Z from rfl, ← hnat]
  simp

omit [e.functor.IsContinuous J' J] [e.inverse.IsContinuous J J'] in
/-- A covering family of `e.inverse.obj U` whose members satisfy a property after transport along
`e.functor` gives a covering family of `U` whose members satisfy it: the members produced are the
images `e.functor.obj (V i)`, and the sieve they generate is covering because `e.inverse` is
cocontinuous. -/
theorem exists_cover_of_reindex {P : C → Prop} (U : C)
    {I : Type (max u v)} (V : I → C') (f : ∀ i, V i ⟶ e.inverse.obj U)
    (hcov : Sieve.ofArrows V f ∈ J' (e.inverse.obj U)) (hP : ∀ i, P (e.functor.obj (V i))) :
    ∃ (I' : Type (max u v)) (W : I' → C) (g : ∀ i, W i ⟶ U),
      Sieve.ofArrows W g ∈ J U ∧ ∀ i, P (W i) := by
  refine ⟨I, fun i => e.functor.obj (V i),
    fun i => e.functor.map (f i) ≫ (e.counitIso.app U).hom, ?_, hP⟩
  apply J.superset_covering _ (e.inverse.cover_lift J J' hcov)
  intro Z h hh
  replace hh : (Sieve.ofArrows V f).arrows (e.inverse.map h) := hh
  rw [Sieve.mem_ofArrows_iff] at hh ⊢
  obtain ⟨i, b, hb⟩ := hh
  refine ⟨i, (e.counitIso.app Z).inv ≫ e.functor.map b, ?_⟩
  have hnat := e.counit.naturality h
  simp only [Functor.id_obj, Functor.id_map, Functor.comp_map] at hnat
  have key : e.functor.map b ≫ e.functor.map (f i) = e.functor.map (e.inverse.map h) := by
    rw [← Functor.map_comp, hb]
  simp only [Category.assoc]
  rw [← Category.assoc (e.functor.map b), key,
    show (e.counitIso.app U).hom = e.counit.app U from rfl, hnat]
  simp

/-- Coverability of every object by a family satisfying a property is invariant under an
equivalence, for properties on `C'` and on `C` matching along `e.functor` and stable under
restriction. -/
private theorem forall_exists_cover_reindex_iff (E : C' ≌ C) [E.inverse.IsDenseSubsite J J']
    {P : C → Prop} {Q : C' → Prop}
    (hQP : ∀ V, Q V → P (E.functor.obj V)) (hPQ : ∀ V, P (E.functor.obj V) → Q V)
    (hmono : ∀ {Z Y : C}, (Z ⟶ Y) → P Y → P Z) :
    (∀ U : C', ∃ (I : Type (max u v)) (V : I → C') (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J' U ∧ ∀ i, Q (V i)) ↔
    (∀ U : C, ∃ (I : Type (max u v)) (W : I → C) (g : ∀ i, W i ⟶ U),
      Sieve.ofArrows W g ∈ J U ∧ ∀ i, P (W i)) := by
  constructor
  · intro hN U
    obtain ⟨I, V, f, hcov, hQ⟩ := hN (E.inverse.obj U)
    exact exists_cover_of_reindex E U V f hcov fun i => hQP _ (hQ i)
  · intro hM U
    obtain ⟨I, W, g, hcov, hP⟩ := hM (E.functor.obj U)
    exact exists_cover_reindex E U W g hcov fun i =>
      hPQ _ (hmono (E.counitIso.app (W i)).hom (hP i))

omit [e.inverse.IsContinuous J J'] in
/-- **Stacks 03DM for clause (2) of Stacks 03DL, for an equivalence of ringed sites.**  A sheaf
of modules is finite locally free exactly when its reindexing along an equivalence of sites, over
the transported structure sheaf, is finite locally free. -/
theorem isFiniteLocallyFreeOnSite_reindex_iff (M : SheafOfModules.{w} R) :
    SheafOfModules.IsFiniteLocallyFreeOnSite
        ((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M) ↔
      SheafOfModules.IsFiniteLocallyFreeOnSite M :=
  forall_exists_cover_reindex_iff e
    (P := fun W => SheafOfModules.IsFiniteFree (R.over W) (M.over W))
    (Q := fun V => SheafOfModules.IsFiniteFree ((reindexRing J' e R).over V)
      (((SheafOfModules.pushforward.{w} (𝟙 (reindexRing J' e R))).obj M).over V))
    (fun V => (isFiniteFree_over_reindex_iff e R M V).1)
    (fun V => (isFiniteFree_over_reindex_iff e R M V).2) (isFiniteFree_overMap R)

end Slice

end Stacks.SheafOfModules

/-! ### The rank clause of Stacks 0409 under an equivalence of ringed sites -/

namespace AlgebraicGeometry.RingedSite

open Stacks.SheafOfModules

/-- The ringed site obtained from `X` by reindexing along an equivalence of sites `e : C' ≌ X.C`:
its underlying site is `(C', J')` and its structure sheaf is the direct image of that of `X`. -/
abbrev reindex (X : RingedSite.{u, v, w}) {C' : Type u} [Category.{v} C']
    (J' : GrothendieckTopology C') (e : C' ≌ X.C) [e.functor.IsContinuous J' X.J] :
    RingedSite.{u, v, w} where
  C := C'
  J := J'
  O := (e.functor.sheafPushforwardContinuous CommRingCat.{w} J' X.J).obj X.O

/-- The sheaf of rings in which the modules on a reindexed ringed site live is the direct image
of the sheaf of rings of the original one. -/
theorem ringSheaf_reindex (X : RingedSite.{u, v, w}) {C' : Type u} [Category.{v} C']
    (J' : GrothendieckTopology C') (e : C' ≌ X.C) [e.functor.IsContinuous J' X.J] :
    (Stacks.SheafOfModules.Tensor.ringSheaf (X.reindex J' e).O) =
      reindexRing J' e (Stacks.SheafOfModules.Tensor.ringSheaf X.O) := rfl

/-- **The rank clause of Stacks 0409 is invariant under an equivalence of ringed sites.**  A
sheaf of modules on a ringed site has rank `r` exactly when its reindexing along an equivalence
of sites has rank `r` on the reindexed ringed site. -/
theorem isFiniteLocallyFreeOfRank_reindex_iff (X : RingedSite.{u, v, w}) {C' : Type u}
    [Category.{v} C'] (J' : GrothendieckTopology C') (e : C' ≌ X.C)
    [e.functor.IsContinuous J' X.J] [e.inverse.IsContinuous X.J J']
    [e.inverse.IsDenseSubsite X.J J']
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (r : ℕ) :
    IsFiniteLocallyFreeOfRank (X.reindex J' e)
        ((SheafOfModules.pushforward.{w}
          (𝟙 (reindexRing J' e (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj F) r ↔
      IsFiniteLocallyFreeOfRank X F r :=
  forall_exists_cover_reindex_iff (J := X.J) e
    (P := fun W => ∃ ι : ∀ _ : Fin r,
        SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) ⟶ F.over W,
      Nonempty (IsColimit (Cofan.mk (F.over W) ι)))
    (Q := fun V => ∃ ι : ∀ _ : Fin r,
        SheafOfModules.unit
            ((reindexRing J' e (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).over V) ⟶
          ((SheafOfModules.pushforward.{w}
            (𝟙 (reindexRing J' e (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj F).over V,
      Nonempty (IsColimit (Cofan.mk
        (((SheafOfModules.pushforward.{w}
          (𝟙 (reindexRing J' e (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))).obj F).over V)
        ι)))
    (fun V => exists_isColimitCofan_of_over_reindex e
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F V)
    (fun V => exists_isColimitCofan_over_reindex e
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F V)
    fun h => exists_isColimitCofanOfRank_over_of_le (Stacks.SheafOfModules.Tensor.ringSheaf X.O) F h

/-! ### The rank clause of Stacks 0409 and the rank condition of Stacks 01C6 -/

variable (X : RingedSite.{u, v, w})
    [∀ U : X.C, HasWeakSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **The rank clause of Stacks 0409 implies the rank condition of Stacks 01C6 (3).**  A sheaf of
modules which, over a covering family of every object, is a coproduct of `r` copies of the
structure sheaf has local generators indexed by a type equivalent to `Fin r` over a covering
family of the terminal object. -/
theorem isFiniteLocallyFreeOfRank_sheafOfModules
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) {r : ℕ}
    (h : IsFiniteLocallyFreeOfRank X F r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r := by
  obtain ⟨I, U, hU, hfree⟩ := (isFiniteLocallyFreeOfRank_iff_exists_cover_isColimit X F r).1 h
  have hsub : X.J.CoversTop (fun i : {W : X.C //
      ∃ ι : ∀ _ : Fin r,
          SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) ⟶ F.over W,
        Nonempty (IsColimit (Cofan.mk (F.over W) ι))} => i.1) := by
    intro Z
    refine X.J.superset_covering ?_ (hU Z)
    intro T g hg
    obtain ⟨i, ⟨a⟩⟩ := hg
    exact ⟨⟨U i, hfree i⟩, ⟨a⟩⟩
  refine Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_of_free_iso r _ hsub fun i => ?_
  exact (coproductIsCoproduct _).coconePointUniqueUpToIso
    (Cofan.isColimitEquivOfEquiv Equiv.ulift (Cofan.mk (F.over i.1) i.2.choose)
      i.2.choose_spec.some)

/-- **The rank condition of Stacks 01C6 (3) implies the rank clause of Stacks 0409.**  Local
generators indexed by a type equivalent to `Fin r` present the module as a coproduct of `r`
copies of the structure sheaf over the members of a covering family of the terminal object. -/
theorem isFiniteLocallyFreeOfRank_of_sheafOfModules
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (r : ℕ)
    (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r) :
    IsFiniteLocallyFreeOfRank X F r := by
  obtain ⟨q, hfree, hrank⟩ := h.exists_isFiniteLocallyFreeOfRankData
  refine (isFiniteLocallyFreeOfRank_iff_exists_cover_isColimit X F r).2
    ⟨ULift.{max u v} q.I, fun j => q.X j.down, ?_, fun j => ?_⟩
  · intro Z
    refine X.J.superset_covering ?_ (q.coversTop Z)
    intro T g hg
    obtain ⟨i, ⟨a⟩⟩ := hg
    exact ⟨⟨i⟩, ⟨a⟩⟩
  · have hj : IsIso (q.generators j.down).π := hfree.isIso j.down
    have hiso : SheafOfModules.free.{w} (ULift.{w} (Fin r)) ≅ F.over (q.X j.down) :=
      ((SheafOfModules.freeFunctor
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).over (q.X j.down))).mapIso
        (((hrank j.down).some.trans Equiv.ulift.symm).toIso)).symm ≪≫
          @asIso _ _ _ _ ((q.generators j.down).π) hj
    have h1 : IsColimit (Cofan.mk (F.over (q.X j.down))
        (fun k : ULift.{w} (Fin r) => Sigma.ι _ k ≫ hiso.hom)) :=
      IsColimit.ofIsoColimit (coproductIsCoproduct _) (Cocone.ext hiso (by rintro ⟨k⟩; rfl))
    exact ⟨_, ⟨Cofan.isColimitEquivOfEquiv Equiv.ulift.symm _ h1⟩⟩

/-- **The two rank conditions agree.**  On a ringed site whose slice topologies admit
sheafification, the rank clause of Stacks 0409 — a covering of every object over whose members
the module is a coproduct of `r` copies of the structure sheaf — is equivalent to the rank
condition of Stacks 01C6 (3), which asks for such a covering of the terminal object only. -/
theorem isFiniteLocallyFreeOfRank_iff_sheafOfModules
    (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (r : ℕ) :
    IsFiniteLocallyFreeOfRank X F r ↔
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank F r :=
  ⟨isFiniteLocallyFreeOfRank_sheafOfModules X F,
    isFiniteLocallyFreeOfRank_of_sheafOfModules X F r⟩

end AlgebraicGeometry.RingedSite

/-! ### The slice comparison of Stacks 04M0 is an equivalence of sites -/

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- The inverse of the slice comparison along an étale morphism of algebraic spaces is
cocontinuous for the localized small étale topologies: it is the functor of an equivalence whose
inverse, postcomposition itself, is cover preserving. -/
theorem isCocontinuous_postcompOverInverse (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS X.1) :
    (postcompOverEquivalence B S hS f hf V).inverse.IsCocontinuous
      ((topology B S hS Y.1).over ((smallEtalePostcomp B S hS f hf).obj V))
      ((topology B S hS X.1).over V) :=
  ((postcompOverEquivalence B S hS f hf V).symm.toAdjunction.isCocontinuous_iff_coverPreserving
    ((topology B S hS Y.1).over ((smallEtalePostcomp B S hS f hf).obj V))
    ((topology B S hS X.1).over V)).2 (coverPreserving_overPostcomp B S hS f hf V)

/-- **The slice comparison of Stacks 04M0 is an equivalence of sites.**  For an étale morphism
`f : X ⟶ Y` of algebraic spaces and an étale chart `V` of `X`, a sieve on the slice of the small
étale site of `Y` at the composite chart is covering exactly when its inverse image on the slice
of the small étale site of `X` at `V` is.

This is the hypothesis under which the reindexing results of this file apply to the small étale
site of an algebraic space; it follows from cocontinuity of the comparison in both directions,
which in turn is cover preservation in both directions. -/
instance isDenseSubsite_postcompOverInverse (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)
    (V : SmallEtale B S hS X.1) :
    (postcompOverEquivalence B S hS f hf V).inverse.IsDenseSubsite
      ((topology B S hS Y.1).over ((smallEtalePostcomp B S hS f hf).obj V))
      ((topology B S hS X.1).over V) :=
  have _ := isCocontinuous_overPostcomp B S hS f hf V
  have _ := isCocontinuous_postcompOverInverse B S hS f hf V
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous
    ((topology B S hS X.1).over V)
    ((topology B S hS Y.1).over ((smallEtalePostcomp B S hS f hf).obj V))
    (postcompOverEquivalence B S hS f hf V)

end AlgebraicGeometry.Space.SmallEtale

end
