module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.PullbackExactDescent
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankPullbackGenerators
public import StacksFrontier.AlgebraicGeometry.Recovery27.PullbackLocallyFree

/-!
# Étale descent of finite local freeness of a given rank

[Stacks, Tag 05B2] says that finite local freeness of a quasi-coherent sheaf of modules descends
along an fpqc — in particular along an étale — covering, and that statement is already available
here as `Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFree_of_etale_cover`. It says nothing
about the rank: a sheaf whose pullback to every member of a covering is free of rank `r` is
finite locally free, but the local bases the descent produces are not the pulled-back ones, so
their index types carry no rank information a priori.

This file supplies the missing step. The rank of a locally free sheaf of modules on a ringed
space with nonzero structure stalks is a *single locally constant function* of the point, Tag
01C9, and that is what identifies the two index types: a member `q.X i` of a presentation of `M`
that contains a point `x`, and a presentation of the pullback to a member of the covering through
a preimage `y` of `x`, both compute the rank of the pullback at `y`. That comparison of two
presentations is
`Stacks.EtaleCohomology.BrauerScheme.mk_generators_eq_of_presentations`, proved on a ringed space;
what is added here is the transport of a presentation through a pullback and the descent itself.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.exists_localGeneratorsData_modulePullback`: a locally free
  presentation of `M` pulls back along a morphism of schemes, with a member through a preimage of
  a given point and the same index type there.
* `Stacks.EtaleCohomology.BrauerScheme.mk_generators_eq_of_isFiniteLocallyFreeOfRank_pullback`
  and `Stacks.EtaleCohomology.BrauerScheme.mk_generators_eq_of_etale_cover`: **a member of a
  locally free presentation of `M` containing the image of a point of `T` has index type of
  cardinality `r`**, as soon as the pullback of `M` to `T` is finite locally free of rank `r`;
  and the same read off an étale covering.
* `Stacks.EtaleCohomology.BrauerScheme.localGeneratorsDataNonempty` and
  `Stacks.EtaleCohomology.BrauerScheme.isLocallyFreeData_localGeneratorsDataNonempty`: the
  members with a point of a local-generator presentation are again a local-generator
  presentation, locally free if the original was.
* `Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFreeOfRank_of_mk_generators_eq`: a sheaf of
  modules with a locally free presentation all of whose *inhabited* members have index type of
  cardinality `r` is finite locally free of rank `r`.
* `Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFreeOfRank_of_etale_cover`: **finite local
  freeness of a given rank, for a quasi-coherent sheaf of modules, descends along an étale
  covering.**

## Implementation notes

**Why the members without a point have to be dropped.** The rank of `M` on a member `q.X i` of
the presentation produced by Tag 05B2 is only pinned down by a point of `q.X i`, since the
argument reads it off the rank function of a pullback at a preimage of such a point. On an empty
member the index type is genuinely unconstrained — the zero sheaf on the empty scheme is free of
every rank at once — so the presentation is first restricted to its inhabited members. This
loses no covering: an open with no points is `⊥`, which contributes nothing to a supremum, so
every point of `S` still lies in an inhabited member, namely in whichever member contains it.
The same device appears in `Stacks.EtaleCohomology.BrauerScheme.coverNonempty` for coverings.
Note that this is a restriction of the *conclusion's witness*, not a hypothesis: the theorem is
stated for an arbitrary rank `r` and an arbitrary étale covering.

**Why the pullback of a presentation lives in another module.** The transport of a locally free
presentation through a pullback, and the comparison of two presentations through a point, are
`Stacks.EtaleCohomology.BrauerScheme.mk_generators_eq_of_pullback_rank` and its inputs in
`StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankPullbackGenerators`, stated on a ringed
space. That is not presentation: at this import closure the instance
`(SheafOfModules.pushforward φ).IsRightAdjoint` carried by `SheafOfModules.pullback φ` is not
synthesized at all, and making it reducible buys the synthesis at the price of definitional
checks that then do not terminate; the two instances
`HasWeakSheafify ((Opens.grothendieckTopology S).over U) AddCommGrpCat` and its
`WEqualsLocallyBijective` companion, which every mention of `LocalGeneratorsData` needs, are
expensive here and cheap there. `modulePullback` by contrast needs no instance at all, which is
why every statement in *this* file is about it, and why each identification of
`modulePullback φ` with `SheafOfModules.pullback φ.toRingCatSheafHom`, or of `ModuleSheaf` with
`LocallyFreeRank.toRingSheaf`-typed modules, happens in exactly one declaration. For the same
reason every mention of `IsFiniteLocallyFreeOfRank` here passes `C` and `J` explicitly, as the
rest of this namespace does, rather than fixing them by universe ascription.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace Stacks.EtaleCohomology.BrauerScheme

variable {S : Scheme.{u}}

/-- **A locally free local-generator presentation of `M` pulls back along a morphism of
schemes**: above the member containing the image of a point `y` of `T` there is a member of a
locally free presentation of `φ^* M` containing `y`, whose generating sections have the same
index type. This is
`AlgebraicGeometry.Grassmannian.exists_localGeneratorsData_pullback`, and it is the one
declaration identifying `modulePullback φ` with `SheafOfModules.pullback φ.toRingCatSheafHom`;
the identification is definitional but not syntactic, and expensive, which is why it is confined
to a declaration whose body is nothing else. -/
theorem exists_localGeneratorsData_modulePullback {T : Scheme.{u}} (φ : T ⟶ S)
    (M : ModuleSheaf S) (q : _root_.SheafOfModules.LocalGeneratorsData.{u} M)
    (hq : q.IsLocallyFreeData) (i : q.I) (y : T) (hy : φ.base y ∈ q.X i) :
    ∃ (q' : _root_.SheafOfModules.LocalGeneratorsData.{u} ((modulePullback φ).obj M))
      (_ : q'.IsLocallyFreeData) (j : q'.I),
      y ∈ q'.X j ∧ Cardinal.mk (q'.generators j).I = Cardinal.mk (q.generators i).I :=
  AlgebraicGeometry.Grassmannian.exists_localGeneratorsData_pullback
    φ.base φ.toRingCatSheafHom M q hq i y hy

/-- **A member of a locally free presentation of a sheaf of `𝒪_S`-modules containing the image of
a point `y` of `T` has index type of cardinality `r`, as soon as the pullback of `M` to `T` is
finite locally free of rank `r`.** The presentation transports to one of the pullback with a
member through `y` and the same index type there
(`Stacks.EtaleCohomology.BrauerScheme.exists_localGeneratorsData_modulePullback`), and
`Stacks.EtaleCohomology.BrauerScheme.mk_generators_eq_of_transported` reads the rank off it. This
is the only declaration in this file identifying `ModuleSheaf` with
`AlgebraicGeometry.Scheme.Modules`; the identification is `rfl` but not cheap, which is why
nothing else happens here. -/
theorem mk_generators_eq_of_isFiniteLocallyFreeOfRank_pullback {T : Scheme.{u}} (φ : T ⟶ S)
    (M : ModuleSheaf S) {r : ℕ}
    (hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens T)
      (J := Opens.grothendieckTopology T) ((modulePullback φ).obj M) r)
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u} M) (hq : q.IsLocallyFreeData)
    (i : q.I) (y : T) (hy : φ.base y ∈ q.X i) :
    Cardinal.mk (q.generators i).I = (r : Cardinal.{u}) :=
  mk_generators_eq_of_transported ((modulePullback φ).obj M) hr q i y
    (exists_localGeneratorsData_modulePullback φ M q hq i y hy)

/-- **The members with a point of a local-generator presentation, as a local-generator
presentation.** A member with no point is `⊥` and contributes nothing to the supremum of the
family, so the restricted family still covers: a point of the space lies in some member, and
that member has a point. -/
def localGeneratorsDataNonempty {M : ModuleSheaf S}
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u} M) :
    _root_.SheafOfModules.LocalGeneratorsData.{u} M where
  I := {i : q.I // Nonempty ↥(q.X i)}
  X i := q.X i.1
  coversTop := by
    refine (Opens.coversTop_iff _ _).2 (top_le_iff.mp fun x _ ↦ ?_)
    obtain ⟨i, hi⟩ := ((Opens.coversTop_iff _ q.X).mp q.coversTop).exists_mem x
    exact Opens.mem_iSup.mpr ⟨⟨i, ⟨⟨x, hi⟩⟩⟩, hi⟩
  generators i := q.generators i.1

/-- Restricting a locally free local-generator presentation to its members with a point leaves
it locally free: the generating sections of a surviving member are those of that member. -/
theorem isLocallyFreeData_localGeneratorsDataNonempty {M : ModuleSheaf S}
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u} M) (hq : q.IsLocallyFreeData) :
    (localGeneratorsDataNonempty q).IsLocallyFreeData :=
  ⟨fun i ↦ hq.isIso i.1⟩

/-- **A sheaf of modules with a locally free presentation whose inhabited members all have index
type of cardinality `r` is finite locally free of rank `r`.** The members with no point are
dropped by `Stacks.EtaleCohomology.BrauerScheme.localGeneratorsDataNonempty`; nothing is required
of them, and nothing could be, an empty open carrying free modules of every rank at once. -/
theorem isFiniteLocallyFreeOfRank_of_mk_generators_eq {M : ModuleSheaf S}
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u} M) (hq : q.IsLocallyFreeData) {r : ℕ}
    (hrk : ∀ (i : q.I) (x : S), x ∈ q.X i →
      Cardinal.mk (q.generators i).I = (r : Cardinal.{u})) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) M r :=
  ⟨localGeneratorsDataNonempty q, isLocallyFreeData_localGeneratorsDataNonempty q hq,
    fun i ↦ Cardinal.mk_eq_nat_iff.mp (hrk i.1 i.2.some.1 i.2.some.2)⟩

/-- **Finite local freeness descends along an étale covering from finite local freeness of a
given rank**: the rank is forgotten member by member, and Tag 05B2 applies in the form
`Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFree_of_etale_cover`. -/
theorem isFiniteLocallyFree_of_etale_cover_of_rank {M : ModuleSheaf S}
    (hM : SheafOfModules.IsQuasicoherent.{u, u, u} M)
    (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S) {r : ℕ}
    (h : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (C := Opens (𝒰.X i)) (J := Opens.grothendieckTopology (𝒰.X i))
      ((modulePullback (𝒰.f i)).obj M) r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M :=
  isFiniteLocallyFree_of_etale_cover hM 𝒰 fun i ↦
    have := h i
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      ((modulePullback (𝒰.f i)).obj M) r

/-- **A point of a member of a local-generator presentation of `M` is the image of a point of
some member of an étale covering of `S`**, by joint surjectivity
(`Stacks.EtaleCohomology.BrauerScheme.etaleCover_spec`), and that image still lies in the member.
Isolated from the rank computation because the membership transport and the covering lookup
together already fill the elaborator's budget at this import closure. -/
theorem exists_mem_map_of_etale_cover {M : ModuleSheaf S}
    (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S)
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u} M) (i : q.I) (x : S) (hx : x ∈ q.X i) :
    ∃ (i' : 𝒰.I₀) (y : 𝒰.X i'), (𝒰.f i').base y ∈ q.X i := by
  obtain ⟨i', y, hy⟩ := (etaleCover_spec 𝒰).1 x
  exact ⟨i', y, Eq.mpr (congrArg (· ∈ q.X i) hy) hx⟩

/-- **A member with a point of a locally free presentation of `M` has index type of cardinality
`r`, when the pullback of `M` to every member of an étale covering is finite locally free of rank
`r`.** The point of the member is the image of a point of some member of the covering
(`Stacks.EtaleCohomology.BrauerScheme.exists_mem_map_of_etale_cover`), and there
`Stacks.EtaleCohomology.BrauerScheme.mk_generators_eq_of_isFiniteLocallyFreeOfRank_pullback`
reads the rank. -/
theorem mk_generators_eq_of_etale_cover {M : ModuleSheaf S}
    (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S) {r : ℕ}
    (h : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (C := Opens (𝒰.X i)) (J := Opens.grothendieckTopology (𝒰.X i))
      ((modulePullback (𝒰.f i)).obj M) r)
    (q : _root_.SheafOfModules.LocalGeneratorsData.{u} M) (hq : q.IsLocallyFreeData)
    (i : q.I) (x : S) (hx : x ∈ q.X i) :
    Cardinal.mk (q.generators i).I = (r : Cardinal.{u}) :=
  (exists_mem_map_of_etale_cover 𝒰 q i x hx).elim fun i' hi' ↦ hi'.elim fun y hy ↦
    mk_generators_eq_of_isFiniteLocallyFreeOfRank_pullback (𝒰.f i') M (h i') q hq i y hy

/-- **Finite local freeness of a given rank descends along an étale covering**, for a
quasi-coherent sheaf of `𝒪_S`-modules: if the pullback of `M` to every member of an étale
covering of `S` is finite locally free of rank `r`, then so is `M`.

Tag 05B2 already gives a locally free presentation of `M`
(`Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFree_of_etale_cover_of_rank`); the rank of
each of its members with a point is read off the covering by
`Stacks.EtaleCohomology.BrauerScheme.mk_generators_eq_of_etale_cover`, and the members with no
point are dropped by
`Stacks.EtaleCohomology.BrauerScheme.isFiniteLocallyFreeOfRank_of_mk_generators_eq`. -/
theorem isFiniteLocallyFreeOfRank_of_etale_cover {M : ModuleSheaf S}
    (hM : SheafOfModules.IsQuasicoherent.{u, u, u} M)
    (𝒰 : Scheme.Cover.{u} Scheme.etalePrecoverage S) {r : ℕ}
    (h : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank
      (C := Opens (𝒰.X i)) (J := Opens.grothendieckTopology (𝒰.X i))
      ((modulePullback (𝒰.f i)).obj M) r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank (C := Opens S)
      (J := Opens.grothendieckTopology S) M r := by
  obtain ⟨q, hq, -⟩ :=
    (isFiniteLocallyFree_of_etale_cover_of_rank hM 𝒰 h).exists_isFiniteLocallyFreeData
  exact isFiniteLocallyFreeOfRank_of_mk_generators_eq q hq
    (mk_generators_eq_of_etale_cover 𝒰 h q hq)

end Stacks.EtaleCohomology.BrauerScheme

end

end
