module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RankLoci
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.SourceChernSetup

/-!
# Reducing a finite locally free module to constant rank

Every result of Stacks Section 45.12 about the class of an arbitrary finite locally free module is
proved there by reducing to the case of constant rank, in one unvarying move:

> let `X = ⋃ X_r` be the decomposition into open and closed subschemes such that `ℰ|_{X_r}` has
> constant rank `r`. Since `X` is quasi-compact, this decomposition is finite. Hence
> `A(X) = ∏ A(X_r)`.

This file performs that move once, in the standing situation
`Stacks.WeilCohomology.SourceChernSetup`,
and in the three forms the source's proofs use it: `A(X)` is *separated by*, *patched from* and
*graded by* its restrictions along the morphisms of `𝒞` along which a finite family of finite
locally free modules acquires constant ranks.

## Main results

* `Stacks.WeilCohomology.SourceChernSetup.exists_clopenConstantRankPieces`: **the reduction to
constant rank, for a finite family of modules.** For an object `X` of `𝒞` and finitely many finite
  locally free `𝒪_X`-modules `ℰ i`, there are finitely many objects `P k` of `𝒞` with flat
  morphisms `p k : P k ⟶ X` such that every `(p k)^*ℰ i` has constant rank and
  `A(X) ⟶ ∏ₖ A(P k)`, `a ↦ ((p k)^*a)ₖ`, is injective and reflects the grading.
* `Stacks.WeilCohomology.SourceChernSetup.exists_clopenRankPieces`: the same for a single module,
which is the form the splitting principle and the Chern character consume.
* `Stacks.WeilCohomology.SourceChernSetup.eq_of_pull_constantRank`,
  `Stacks.WeilCohomology.SourceChernSetup.exists_pull_eq_constantRank` and
  `Stacks.WeilCohomology.SourceChernSetup.mem_grade_of_pull_constantRank`: the separation, patching
  and grading forms of the reduction, stated along *every* morphism of `𝒞` making the ranks
  constant and not only along the pieces. This is what makes the reduction functorial, and it is
  what the rules of Tags 0FI5 and 0FI9 are built from.
* `Stacks.Chow.mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback`: **a morphism along which
  `ℰ` acquires constant rank `r` carries every point into the rank-`r` locus of `ℰ`.** This is
  what turns "making the rank constant" into the hypothesis of the second sentence of clause (2),
  and so what makes the patching and grading forms hold along an arbitrary morphism.

## What the three clauses contribute

The decomposition `X = ⋃ X_r` itself is geometry, not an axiom: the rank of a finite locally free
module is a locally constant function, so its fibres are open and closed, and that is Tag 0ESW,
`Stacks.Chow.rankLocus` with `Stacks.Chow.isClopen_rankLocus` and
`Stacks.Chow.isFiniteLocallyFreeOfRank_pullback_rankLocus`. What the situation supplies is the
rest: clause (1) makes the decomposition finite, clause (2) makes each `X_r` an object of `𝒞` and
each inclusion a morphism of it, the second sentence of clause (2) factors a morphism of `𝒞`
along which the rank is constant through the piece it lands in, and condition (2) is the splitting
`A(X) = ∏ A(X_r)` of graded rings — injectivity for the separation form, surjectivity for the
patching form, and the graded half for the grading form.

## Implementation notes

For a family of modules the pieces are the joint loci `⋂ᵢ X_{i, m i}`, cut out by a whole tuple of
ranks rather than by one; they are open and closed because the family is finite, pairwise disjoint
because two distinct tuples differ somewhere, and they cover because every point has a tuple of
ranks. `Stacks.WeilCohomology.exists_jointRankPieces` is that decomposition, and it is the only
place in this directory where a decomposition is built: everything else is an application of
condition (2) to it.

`Stacks.Chow.rankLocus` is an open subscheme of `S(X)`, whereas clause (2) names an object of `𝒞`
whose scheme is merely isomorphic to it. The constant rank is therefore transported across that
isomorphism, by `AlgebraicGeometry.Scheme.Modules.pullbackComp` to split the pullback along
`iso.hom ≫ ι` into the two steps and
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso` to move the conclusion back.
The rank-preservation of a single pullback is
`AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback`, which is what
`StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic` is imported for.

The finite index type is the subtype of the `Finset` of rank tuples that quasi-compactness
returns, and is not pruned to the tuples that actually occur: a piece that happens to be empty
does no harm, the statement asserting only that the modules have constant ranks on each piece.

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v v₁ w

/-! ### The rank along a morphism -/

/-- Constant rank of a pullback along `g` passes to the pullback along `f ≫ g`. -/
private theorem isFiniteLocallyFreeOfRank_pullback_comp {X Y Z : Scheme.{u}} (E : Z.Modules)
    (f : X ⟶ Y) (g : Y ⟶ Z) (r : ℕ)
    (hg : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj E) r) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (f ≫ g)).obj E) r :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
    ((Scheme.Modules.pullbackComp f g).app E) (AlgebraicGeometry.isFiniteLocallyFreeOfRank_pullback
      f ((Scheme.Modules.pullback g).obj E) r)

/-- **A morphism along which `ℰ` acquires constant rank `r` carries every point into the rank-`r`
locus of `ℰ`.**

Let `s` be the rank of `ℰ` at the image of a point `z`, let `V` be the rank-`s` locus and let
`W = g^{-1}(V)`, which contains `z`. On `W` the module `ℰ` pulls back to a module of rank `s`,
because `g` restricted to `W` factors through `V` where `ℰ` has rank `s`, and also to one of rank
`r`, by restricting the hypothesis; `W` has the point `z`, so `s = r`. -/
theorem Stacks.Chow.mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback {X Z : Scheme.{u}}
    (E : X.Modules) [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (g : Z ⟶ X) (r : ℕ)
    (hg : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback g).obj E) r) (z : Z) :
    g.base z ∈ Stacks.Chow.rankLocus E r := by
  have := hg
  obtain ⟨s, hs⟩ : ∃ s, Stacks.Chow.moduleRank E (g.base z) = s := ⟨_, rfl⟩
  set V : X.Opens := Stacks.Chow.rankLocus E s
  have hzW : z ∈ g ⁻¹ᵁ V := (Stacks.Chow.mem_rankLocus E).2 hs
  have h₁ := isFiniteLocallyFreeOfRank_pullback_comp E (g ⁻¹ᵁ V).ι g r hg
  have h₂ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback ((g ⁻¹ᵁ V).ι ≫ g)).obj E) s := by
    have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback V.ι).obj E) s :=
      Stacks.Chow.isFiniteLocallyFreeOfRank_pullback_rankLocus E s
    have h := isFiniteLocallyFreeOfRank_pullback_comp E (g.resLE V (g ⁻¹ᵁ V) le_rfl) V.ι s this
    rwa [Scheme.Hom.resLE_comp_ι] at h
  have hsr : s = r :=
    AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_unique _ h₂ h₁ ⟨z, hzW⟩
  exact (Stacks.Chow.mem_rankLocus E).2 (hs.trans hsr)

namespace Stacks.WeilCohomology

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-! ### The joint constant-rank decomposition -/

/-- The locus where each member of a finite family of finite locally free modules has a prescribed
rank. It is open because the family is finite, each rank locus being open. -/
def jointRankLocus {X : Scheme.{u}} {ι : Type} [Finite ι] (E : ι → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (E i)] (m : ι → ℕ) :
    X.Opens where
  carrier := ⋂ i, (Stacks.Chow.rankLocus (E i) (m i) : Set X)
  is_open' := isOpen_iInter_of_finite fun i => (Stacks.Chow.rankLocus (E i) (m i)).isOpen

/-- The underlying set of `jointRankLocus E m` is the intersection of the rank loci
`Stacks.Chow.rankLocus (E i) (m i)`. -/
theorem coe_jointRankLocus {X : Scheme.{u}} {ι : Type} [Finite ι] (E : ι → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (E i)] (m : ι → ℕ) :
    (jointRankLocus E m : Set X) = ⋂ i, (Stacks.Chow.rankLocus (E i) (m i) : Set X) := rfl

/-- A point lies in `jointRankLocus E m` if and only if each `E i` has rank `m i` at it. -/
theorem mem_jointRankLocus {X : Scheme.{u}} {ι : Type} [Finite ι] (E : ι → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (E i)] (m : ι → ℕ)
    (x : X) : x ∈ jointRankLocus E m ↔ ∀ i, Stacks.Chow.moduleRank (E i) x = m i := by
  constructor
  · intro hx i
    exact (Stacks.Chow.mem_rankLocus (E i)).1 (Set.mem_iInter.1 hx i)
  · intro hx
    exact Set.mem_iInter.2 fun i => (Stacks.Chow.mem_rankLocus (E i)).2 (hx i)

/-- **The joint constant-rank decomposition of a quasi-compact scheme.** For a finite family of
finite locally free modules there are finitely many open and closed subschemes, pairwise disjoint
and covering, on each of which every member of the family has a constant rank — namely the locus
of one tuple of ranks.

The loci of distinct tuples are disjoint because the tuples differ somewhere, they cover because
every point has its own tuple of ranks, and finitely many of them suffice because the scheme is
quasi-compact. This is the only decomposition built in this file. -/
theorem exists_jointRankPieces {X : Scheme.{u}} {ι : Type} [Finite ι] (E : ι → X.Modules)
    [∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (E i)]
    [CompactSpace X] :
    ∃ (κ : Type) (_ : Finite κ) (m : κ → ι → ℕ) (U : κ → X.Opens),
      (∀ k, IsClopen (U k : Set X)) ∧ (∀ k l, k ≠ l → Disjoint (U k) (U l)) ∧
        (⨆ k, U k) = ⊤ ∧
          ∀ (k : κ) (x : X), x ∈ U k ↔ ∀ i, Stacks.Chow.moduleRank (E i) x = m k i := by
  classical
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun m : ι → ℕ => (jointRankLocus E m : Set X))
    (fun m => (jointRankLocus E m).isOpen)
    fun x _ => Set.mem_iUnion.2
      ⟨fun i => Stacks.Chow.moduleRank (E i) x, (mem_jointRankLocus E _ x).2 fun _ => rfl⟩
  refine ⟨{m : ι → ℕ // m ∈ t}, inferInstance, fun k => (k : ι → ℕ),
    fun k => jointRankLocus E (k : ι → ℕ), fun k => ?_, fun k l hkl => ?_, ?_,
    fun k x => mem_jointRankLocus E (k : ι → ℕ) x⟩
  · rw [coe_jointRankLocus]
    exact ⟨isClosed_iInter fun i => (Stacks.Chow.isClopen_rankLocus (E i) _).1,
      isOpen_iInter_of_finite fun i => (Stacks.Chow.isClopen_rankLocus (E i) _).2⟩
  · refine Opens.coe_disjoint.mp (Set.disjoint_left.mpr fun x hx hy => ?_)
    obtain ⟨i, hi⟩ : ∃ i, (k : ι → ℕ) i ≠ (l : ι → ℕ) i := by
      by_cases h : ∀ i, (k : ι → ℕ) i = (l : ι → ℕ) i
      · exact absurd (Subtype.ext (funext h)) hkl
      · exact not_forall.1 h
    exact hi (((mem_jointRankLocus E _ x).1 hx i).symm.trans ((mem_jointRankLocus E _ x).1 hy i))
  · refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨m, hm, hx⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
    exact Opens.mem_iSup.2 ⟨⟨m, hm⟩, hx⟩

/-! ### The pieces as objects of `𝒞` -/

/-- On the object of `𝒞` indexing an open and closed subscheme of the rank-`r` locus of `ℰ`, the
module `ℰ` pulls back to one of constant rank `r`.

Clause (2) gives an object whose scheme is isomorphic to the subscheme rather than equal to it, so
the constant rank has to travel along that isomorphism: pullback along `iso.hom ≫ ι` splits into
its two steps, each of which preserves the rank. -/
theorem isFiniteLocallyFreeOfRank_pullback_clopenSubobject {X : C}
    (E : (S.obj X).Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] (r : ℕ)
    {V : (S.obj X).Opens} (hV : V ≤ Stacks.Chow.rankLocus E r) (D : ClopenSubobject S X V) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map D.hom)).obj E) r := by
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback V.ι).obj E) r :=
    AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFreeOfRank_pullback_of_fiberRank_eq E V r
      fun x hx => by
        rw [Stacks.Chow.fiberRank_eq_moduleRank E x]
        exact (Stacks.Chow.mem_rankLocus E).1 (hV hx)
  have h := isFiniteLocallyFreeOfRank_pullback_comp E D.iso.hom V.ι r this
  rwa [D.iso_hom_comp_ι] at h

/-- The inclusion of a piece is flat, being an open immersion read through an isomorphism. -/
theorem flat_clopenSubobject {X : C} {V : (S.obj X).Opens} (D : ClopenSubobject S X V) :
    Flat (S.map D.hom) := by
  rw [← D.iso_hom_comp_ι]
  infer_instance

namespace SourceChernSetup

/-- **The reduction of a finite family of finite locally free modules to constant ranks.** Let `X`
be an object of `𝒞` and let `ℰ i` be finitely many finite locally free `𝒪_X`-modules. There are
finitely many objects `P k` of `𝒞`, with morphisms `p k : P k ⟶ X`, such that every `(p k)^*ℰ i`
is finite locally free of a constant rank, `a ↦ ((p k)^*a)ₖ` is injective on `A(X)`, and a class
all of whose restrictions lie in degree `n` lies in degree `n`. Each `p k` is flat, being the
inclusion of an open and closed subscheme read through an isomorphism, so a short exact sequence
of modules on `X` stays short exact on every piece.

This is the source's standing reduction: the `P k` index the joint loci where the family has
constant ranks, finite in number because the objects of `𝒞` are quasi-compact, objects of `𝒞` by
clause (2), and the two last clauses are condition (2), read as the splitting of *graded* rings
that the source's reading of `A` as a functor to graded rings makes it. -/
theorem exists_clopenConstantRankPieces (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) (X : C) (ι : Type)
    [Finite ι] (E : ι → (S.obj X).Modules)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (E i)) :
    ∃ (κ : Type) (_ : Finite κ) (P : κ → C) (p : ∀ k, P k ⟶ X) (m : κ → ι → ℕ),
      (∀ k, Flat (S.map (p k))) ∧
      (∀ k i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map (p k))).obj (E i)) (m k i)) ∧
      (Function.Injective fun a : 𝔄.A X => fun k => 𝔄.pull (p k) a) ∧
        ∀ (a : 𝔄.A X) (n : ℕ), (∀ k, 𝔄.pull (p k) a ∈ 𝔄.grade (P k) n) → a ∈ 𝔄.grade X n := by
  have := 𝔄.compactSpace X
  have : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (E i) := hE
  obtain ⟨κ, hκ, m, U, hclopen, hdisj, hcover, hmem⟩ := exists_jointRankPieces E
  have : Finite κ := hκ
  refine ⟨κ, hκ, fun k => (𝔄.clopenSubobject X (U k) (hclopen k)).obj,
    fun k => (𝔄.clopenSubobject X (U k) (hclopen k)).hom, m,
    fun k => flat_clopenSubobject _, fun k i => ?_,
    𝔄.injective_pull_clopenSubobject X κ U hclopen hdisj hcover,
    fun a n h => 𝔄.mem_grade_of_pull_clopenSubobject X κ U hclopen hdisj hcover a n h⟩
  exact isFiniteLocallyFreeOfRank_pullback_clopenSubobject (E i) (m k i)
    (fun x hx => (Stacks.Chow.mem_rankLocus (E i)).2 ((hmem k x).1 hx i)) _

/-- **The reduction of a finite locally free module to constant rank.** Let `X` be an object of
`𝒞` and let `ℰ` be a finite locally free `𝒪_X`-module. There are finitely many objects `P i` of
`𝒞`, with morphisms `p i : P i ⟶ X`, such that each `(p i)^*ℰ` is finite locally free of constant
rank and `a ↦ ((p i)^*a)ᵢ` is injective on `A(X)`. Each `p i` is flat, being the inclusion of an
open and closed subscheme read through an isomorphism, so a short exact sequence of modules on
`X` stays short exact on every piece.

This is `Stacks.WeilCohomology.SourceChernSetup.exists_clopenConstantRankPieces` for one module.
Two classes of `A(X)` that are attached to `ℰ` compatibly with pullback and that agree whenever the
rank is constant therefore agree outright. -/
theorem exists_clopenRankPieces (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) (X : C)
    (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    ∃ (ι : Type) (_ : Finite ι) (P : ι → C) (p : ∀ i, P i ⟶ X) (r : ι → ℕ),
      (∀ i, Flat (S.map (p i))) ∧
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map (p i))).obj E) (r i)) ∧
        Function.Injective fun a : 𝔄.A X => fun i => 𝔄.pull (p i) a := by
  obtain ⟨κ, hκ, P, p, m, hflat, hrank, hinj, -⟩ :=
    𝔄.exists_clopenConstantRankPieces X Unit (fun _ => E) fun _ => hE
  exact ⟨κ, hκ, P, p, fun k => m k (), hflat, fun k => hrank k (), hinj⟩

/-! ### The three functorial forms of the reduction -/

/-- **Clause (2) and condition (2), separation half.** A class of `A(X)` is determined by its
restrictions along the morphisms of `𝒞` along which a finite family of finite locally free modules
acquires constant ranks: two classes with the same restrictions along all of them are equal.

Phrasing the reduction this way, rather than as the existence of the pieces, is what makes it
functorial: the hypothesis is used along *every* such morphism, not only along the pieces
themselves. -/
theorem eq_of_pull_constantRank (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) (X : C) (ι : Type)
    (hι : Finite ι) (E : ι → (S.obj X).Modules)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) (E i)) (a b : 𝔄.A X)
    (h : ∀ (Z : C) (g : Z ⟶ X), Flat (S.map g) → ∀ m : ι → ℕ,
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map g)).obj (E i)) (m i)) →
      𝔄.pull g a = 𝔄.pull g b) : a = b := by
  have := hι
  obtain ⟨κ, -, P, p, m, hflat, hrank, hinj, -⟩ := 𝔄.exists_clopenConstantRankPieces X ι E hE
  exact hinj (funext fun k => h (P k) (p k) (hflat k) (m k) (hrank k))

/-- **Condition (2) is a splitting of graded algebras.** A class of `A(X)` whose restriction along
every flat morphism of `𝒞` making the rank of `ℰ` constant lies in degree `n` lies in degree `n`
itself. This is the graded half of condition (2), read through the reduction. -/
theorem mem_grade_of_pull_constantRank (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) (X : C)
    (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (a : 𝔄.A X) (n : ℕ)
    (h : ∀ (Z : C) (g : Z ⟶ X), Flat (S.map g) → ∀ m : ℕ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map g)).obj E) m → 𝔄.pull g a ∈ 𝔄.grade Z n) :
    a ∈ 𝔄.grade X n := by
  obtain ⟨κ, -, P, p, m, hflat, hrank, -, hgrade⟩ :=
    𝔄.exists_clopenConstantRankPieces X Unit (fun _ => E) fun _ => hE
  exact hgrade a n fun k => h (P k) (p k) (hflat k) (m k ()) (hrank k ())

/-- **Clause (2) and condition (2), patching half.** A rule assigning a class of `A(Z)` to every
morphism `g : Z ⟶ X` of `𝒞` along which `ℰ` acquires a constant rank, compatible with further
pullback, is the restriction of a single class of `A(X)`.

The class is produced by the surjectivity half of condition (2) applied to the rank loci of `ℰ`,
which gives it along the inclusions of the pieces. That it then agrees with the rule along an
*arbitrary* morphism `g` of `𝒞` making the rank constant is the second sentence of clause (2):
such a `g` carries every point into one rank locus,
`Stacks.Chow.mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback`, so it factors through the piece
of `𝒞` indexing that locus and the compatibility of the rule finishes. A `g` whose rank does not
occur has empty source, where `A` is the zero ring by
`Stacks.WeilCohomology.SourceChernSetup.subsingleton_of_isEmpty`. -/
theorem exists_pull_eq_constantRank (𝔄 : SourceChernSetup.{u, v, v₁, w} C S) (X : C)
    (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E)
    (t : ∀ (Z : C) (g : Z ⟶ X) (m : ℕ),
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map g)).obj E) m → 𝔄.A Z)
    (ht : ∀ (Z Z' : C) (g : Z ⟶ X) (h : Z' ⟶ Z) (m : ℕ)
        (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map g)).obj E) m)
        (hm' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map (h ≫ g))).obj E) m),
      𝔄.pull h (t Z g m hm) = t Z' (h ≫ g) m hm') :
    ∃ a : 𝔄.A X, ∀ (Z : C) (g : Z ⟶ X) (m : ℕ)
      (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map g)).obj E) m), 𝔄.pull g a = t Z g m hm := by
  have := 𝔄.compactSpace X
  have : ∀ _ : Unit, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E :=
    fun _ => hE
  have := hE
  obtain ⟨κ, hκ, m, U, hclopen, hdisj, hcover, hmem⟩ := exists_jointRankPieces (fun _ : Unit => E)
  have : Finite κ := hκ
  have hle : ∀ k, U k ≤ Stacks.Chow.rankLocus E (m k ()) := fun k x hx =>
    (Stacks.Chow.mem_rankLocus E).2 ((hmem k x).1 hx ())
  have hrank : ∀ k, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback (S.map (𝔄.clopenSubobject X (U k) (hclopen k)).hom)).obj E)
      (m k ()) :=
    fun k => isFiniteLocallyFreeOfRank_pullback_clopenSubobject E (m k ()) (hle k) _
  obtain ⟨a, ha⟩ := (𝔄.bijective_pull_clopenSubobject X κ U hclopen hdisj hcover).surjective
    fun k => t (𝔄.clopenSubobject X (U k) (hclopen k)).obj
      (𝔄.clopenSubobject X (U k) (hclopen k)).hom (m k ()) (hrank k)
  refine ⟨a, fun Z g mm hm => ?_⟩
  rcases isEmpty_or_nonempty (S.obj Z) with hZ | hZ
  · exact (𝔄.subsingleton_of_isEmpty Z hZ).elim _ _
  obtain ⟨z₀⟩ := hZ
  have hrk : ∀ z : S.obj Z, Stacks.Chow.moduleRank E ((S.map g).base z) = mm := fun z =>
    (Stacks.Chow.mem_rankLocus E).1
      (Stacks.Chow.mem_rankLocus_of_isFiniteLocallyFreeOfRank_pullback E (S.map g) mm hm z)
  obtain ⟨k, hk⟩ : ∃ k, (S.map g).base z₀ ∈ U k := by
    have hx : (S.map g).base z₀ ∈ (⨆ k, U k) := by
      rw [hcover]
      exact Opens.mem_top _
    exact Opens.mem_iSup.1 hx
  have hmk : m k () = mm := ((hmem k _).1 hk ()).symm.trans (hrk z₀)
  subst hmk
  obtain ⟨h, hh⟩ := (𝔄.clopenSubobject X (U k) (hclopen k)).exists_factor g fun z =>
    (hmem k _).2 fun _ => hrk z
  subst hh
  have hak := congrFun ha k
  dsimp only at hak
  rw [𝔄.pull_comp h (𝔄.clopenSubobject X (U k) (hclopen k)).hom, RingHom.comp_apply, hak]
  exact ht _ _ _ h (m k ()) (hrank k) _

end SourceChernSetup

end Stacks.WeilCohomology

end
