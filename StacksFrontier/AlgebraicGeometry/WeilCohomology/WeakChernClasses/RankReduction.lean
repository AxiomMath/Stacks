module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.RankReduction
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation

/-!
# Reducing a finite locally free module to constant rank, in the weak standing situation

The results of `StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.RankReduction`, stated
for `Stacks.WeilCohomology.Weak.ChernSetup`: the standing situation of Stacks Section 45.12 in
which the projective bundle formula, condition (4), is only asked to be injective and to resolve
the top power `c₁^A(𝒪_P(1))^{r+1}` of the twist class (see
`StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation`, which explains why Tag
0FIE needs this generality); condition (4) is used only through these two properties.

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0ESW](https://stacks.math.columbia.edu/tag/0ESW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u v v₁ w

/-! ### The rank along a morphism -/

namespace Stacks.WeilCohomology.Weak

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}

/-! ### The joint constant-rank decomposition -/

namespace ChernSetup

/-- The joint rank pieces of a finite family of finite locally free modules, together with the
constant ranks of the pullbacks to the clopen subobjects they cut out. -/
private theorem exists_jointRankPieces_clopenSubobject (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (ι : Type) [Finite ι] (E : ι → (S.obj X).Modules)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (E i)) :
    ∃ (κ : Type) (_ : Finite κ) (m : κ → ι → ℕ) (U : κ → (S.obj X).Opens)
      (hclopen : ∀ k, IsClopen (U k : Set (S.obj X))),
      (∀ k l, k ≠ l → Disjoint (U k) (U l)) ∧ (⨆ k, U k) = ⊤ ∧
      (∀ (k : κ) (x : S.obj X), x ∈ U k ↔ ∀ i, Stacks.Chow.moduleRank (E i) x = m k i) ∧
      ∀ k i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map (𝔚.clopenSubobject X (U k) (hclopen k)).hom)).obj (E i))
        (m k i) := by
  have := 𝔚.compactSpace X
  obtain ⟨κ, hκ, m, U, hclopen, hdisj, hcover, hmem⟩ := exists_jointRankPieces E
  exact ⟨κ, hκ, m, U, hclopen, hdisj, hcover, hmem, fun k i =>
    isFiniteLocallyFreeOfRank_pullback_clopenSubobject (E i) (m k i)
      (fun x hx => (Stacks.Chow.mem_rankLocus (E i)).2 ((hmem k x).1 hx i)) _⟩

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
theorem exists_clopenConstantRankPieces (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C) (ι : Type)
    [Finite ι] (E : ι → (S.obj X).Modules)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (E i)) :
    ∃ (κ : Type) (_ : Finite κ) (P : κ → C) (p : ∀ k, P k ⟶ X) (m : κ → ι → ℕ),
      (∀ k, Flat (S.map (p k))) ∧
      (∀ k i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map (p k))).obj (E i)) (m k i)) ∧
      (Function.Injective fun a : 𝔚.A X => fun k => 𝔚.pull (p k) a) ∧
        ∀ (a : 𝔚.A X) (n : ℕ), (∀ k, 𝔚.pull (p k) a ∈ 𝔚.grade (P k) n) → a ∈ 𝔚.grade X n := by
  obtain ⟨κ, hκ, m, U, hclopen, hdisj, hcover, -, hrank⟩ :=
    𝔚.exists_jointRankPieces_clopenSubobject X ι E hE
  exact ⟨κ, hκ, fun k => (𝔚.clopenSubobject X (U k) (hclopen k)).obj,
    fun k => (𝔚.clopenSubobject X (U k) (hclopen k)).hom, m,
    fun k => flat_clopenSubobject _, hrank,
    𝔚.injective_pull_clopenSubobject X κ U hclopen hdisj hcover,
    fun a n h => 𝔚.mem_grade_of_pull_clopenSubobject X κ U hclopen hdisj hcover a n h⟩

/-- **The reduction of a finite locally free module to constant rank.** Let `X` be an object of
`𝒞` and let `ℰ` be a finite locally free `𝒪_X`-module. There are finitely many objects `P i` of
`𝒞`, with morphisms `p i : P i ⟶ X`, such that each `(p i)^*ℰ` is finite locally free of constant
rank and `a ↦ ((p i)^*a)ᵢ` is injective on `A(X)`. Each `p i` is flat, being the inclusion of an
open and closed subscheme read through an isomorphism, so a short exact sequence of modules on
`X` stays short exact on every piece.

This is `Stacks.WeilCohomology.Weak.ChernSetup.exists_clopenConstantRankPieces` for one module. Two
classes of `A(X)` that are attached to `ℰ` compatibly with pullback and that agree whenever the
rank is constant therefore agree outright. -/
theorem exists_clopenRankPieces (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E) :
    ∃ (ι : Type) (_ : Finite ι) (P : ι → C) (p : ∀ i, P i ⟶ X) (r : ι → ℕ),
      (∀ i, Flat (S.map (p i))) ∧
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map (p i))).obj E) (r i)) ∧
        Function.Injective fun a : 𝔚.A X => fun i => 𝔚.pull (p i) a := by
  obtain ⟨κ, hκ, P, p, m, hflat, hrank, hinj, -⟩ :=
    𝔚.exists_clopenConstantRankPieces X Unit (fun _ => E) fun _ => hE
  exact ⟨κ, hκ, P, p, fun k => m k (), hflat, fun k => hrank k (), hinj⟩

/-! ### The three functorial forms of the reduction -/

/-- **Clause (2) and condition (2), separation half.** A class of `A(X)` is determined by its
restrictions along the morphisms of `𝒞` along which a finite family of finite locally free modules
acquires constant ranks: two classes with the same restrictions along all of them are equal.

Phrasing the reduction this way, rather than as the existence of the pieces, is what makes it
functorial: the hypothesis is used along *every* such morphism, not only along the pieces
themselves. -/
theorem eq_of_pull_constantRank (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C) (ι : Type)
    (hι : Finite ι) (E : ι → (S.obj X).Modules)
    (hE : ∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) (E i)) (a b : 𝔚.A X)
    (h : ∀ (Z : C) (g : Z ⟶ X), Flat (S.map g) → ∀ m : ι → ℕ,
      (∀ i, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map g)).obj (E i)) (m i)) →
      𝔚.pull g a = 𝔚.pull g b) : a = b := by
  have := hι
  obtain ⟨κ, -, P, p, m, hflat, hrank, hinj, -⟩ := 𝔚.exists_clopenConstantRankPieces X ι E hE
  exact hinj (funext fun k => h (P k) (p k) (hflat k) (m k) (hrank k))

/-- **Condition (2) is a splitting of graded algebras.** A class of `A(X)` whose restriction along
every flat morphism of `𝒞` making the rank of `ℰ` constant lies in degree `n` lies in degree `n`
itself. This is the graded half of condition (2), read through the reduction. -/
theorem mem_grade_of_pull_constantRank (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E) (a : 𝔚.A X) (n : ℕ)
    (h : ∀ (Z : C) (g : Z ⟶ X), Flat (S.map g) → ∀ m : ℕ,
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map g)).obj E) m → 𝔚.pull g a ∈ 𝔚.grade Z n) :
    a ∈ 𝔚.grade X n := by
  obtain ⟨κ, -, P, p, m, hflat, hrank, -, hgrade⟩ :=
    𝔚.exists_clopenConstantRankPieces X Unit (fun _ => E) fun _ => hE
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
`Stacks.WeilCohomology.Weak.ChernSetup.subsingleton_of_isEmpty`. -/
theorem exists_pull_eq_constantRank (𝔚 : ChernSetup.{u, v, v₁, w} C S) (X : C)
    (E : (S.obj X).Modules)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (R := (S.obj X).ringCatSheaf) E)
    (t : ∀ (Z : C) (g : Z ⟶ X) (m : ℕ),
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map g)).obj E) m → 𝔚.A Z)
    (ht : ∀ (Z Z' : C) (g : Z ⟶ X) (h : Z' ⟶ Z) (m : ℕ)
        (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map g)).obj E) m)
        (hm' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
          ((Scheme.Modules.pullback (S.map (h ≫ g))).obj E) m),
      𝔚.pull h (t Z g m hm) = t Z' (h ≫ g) m hm') :
    ∃ a : 𝔚.A X, ∀ (Z : C) (g : Z ⟶ X) (m : ℕ)
      (hm : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
        ((Scheme.Modules.pullback (S.map g)).obj E) m), 𝔚.pull g a = t Z g m hm := by
  obtain ⟨κ, hκ, m, U, hclopen, hdisj, hcover, hmem, hrank⟩ :=
    𝔚.exists_jointRankPieces_clopenSubobject X Unit (fun _ => E) fun _ => hE
  have : Finite κ := hκ
  obtain ⟨a, ha⟩ := (𝔚.bijective_pull_clopenSubobject X κ U hclopen hdisj hcover).surjective
    fun k => t (𝔚.clopenSubobject X (U k) (hclopen k)).obj
      (𝔚.clopenSubobject X (U k) (hclopen k)).hom (m k ()) (hrank k ())
  refine ⟨a, fun Z g mm hm => ?_⟩
  rcases isEmpty_or_nonempty (S.obj Z) with hZ | hZ
  · exact (𝔚.subsingleton_of_isEmpty Z hZ).elim _ _
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
  obtain ⟨h, hh⟩ := (𝔚.clopenSubobject X (U k) (hclopen k)).exists_factor g fun z =>
    (hmem k _).2 fun _ => hrk z
  subst hh
  have hak := congrFun ha k
  dsimp only at hak
  rw [𝔚.pull_comp h (𝔚.clopenSubobject X (U k) (hclopen k)).hom, RingHom.comp_apply, hak]
  exact ht _ _ _ h (m k ()) (hrank k ()) _

end ChernSetup

end Stacks.WeilCohomology.Weak

end
