module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.BundleObject
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.Situation
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The standing situation of Section 45.12 with the source's clauses on `𝒞`

`Stacks.WeilCohomology.ChernSetup` transcribes the graded invariant `A`, the first Chern class and
the projective bundle formula, with the tautological datum of each projective bundle carried as
the field `bundleDatum`. `Stacks.WeilCohomology.SourceChernSetup` extends it by the source's
clauses on the category `𝒞` and by condition (2):

* clause (1): every object of `𝒞` is quasi-compact (`compactSpace`);
* the grading of `A(X)` is a direct sum decomposition (`isInternal_grade`);
* clause (3)(a): the projective bundle of a finite locally free module of constant rank is an
  object of `𝒞` (`bundleObject`), and the datum `bundleDatum` is the one constructed from it by
  `Stacks.WeilCohomology.BundleObject.toBundleDatum` (`bundleDatum_eq`), so that the tautological
  sequence, its exactness, the rank of its kernel and the flatness of the projection are not
  assumed;
* clause (2) and condition (2): an open and closed subscheme of an object is an object, and `A`
  splits along a finite decomposition into open and closed subschemes, as graded rings
  (`clopenSubobject`, `bijective_pull_clopenSubobject`, `mem_grade_of_pull_clopenSubobject`).

## Main definitions

* `Stacks.WeilCohomology.BundleObject.toBundleDatum`: the tautological datum of a clause-(3)(a)
  object.
* `Stacks.WeilCohomology.ClopenSubobject`: an open and closed subscheme as an object of `𝒞`.
* `Stacks.WeilCohomology.SourceChernSetup`: the standing situation with those clauses.

## References

* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v v₁ w

namespace Stacks.WeilCohomology

/-- **Two invertible modules with the same isomorphism class have the same class in `Pic(X)`.**
`Stacks.WeilCohomology.picardClassOf` is a function of the module, and this is the only thing
read off it beyond its value: `AlgebraicGeometry.Scheme.picardClass_eq_iff` says equality in
`Pic(X)` *is* isomorphism. -/
theorem picardClassOf_eq_of_iso (X : Scheme.{u}) (L L' : X.Modules)
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L)
    (hL' : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L')
    (e : L ≅ L') : picardClassOf X L hL = picardClassOf X L' hL' :=
  (Scheme.picardClass_eq_iff X L L' _ _).mpr ⟨e⟩

/-! ### The tautological datum of a clause-(3)(a) object -/

namespace BundleObject

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} {X : C}
  {E : (S.obj X).Modules} {r : ℕ}

/-- **The class of `𝒪_{𝐏(ℰ)}(1)` in `Pic` of the object of `𝒞`.** -/
def twistClass (B : BundleObject S X E r) : (S.obj B.bundle).picardGroup :=
  picardClassOf (S.obj B.bundle) B.twist B.twist_isInvertible

/-- **The whole tautological datum of `𝐏(ℰ)`, constructed from clause (3)(a).** Each piece is
derived in `StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.BundleObject`, whose module
documentation attributes it; short exactness is
`CategoryTheory.ShortComplex.exact_kernel` for the categorical kernel of the tautological
surjection, and the rank of that kernel is
`Stacks.WeilCohomology.BundleObject.isFiniteLocallyFreeOfRank_kernel_quot`. -/
@[ega "IV 19.4.11", sga "6 VII 1.8" "partial"]
def toBundleDatum (B : BundleObject S X E r) : BundleDatum S X E r :=
  haveI hepi : Epi B.quot := B.epi_quot
  { bundle := B.bundle
    proj := B.proj
    flat := B.flat_map_proj
    twist := B.twist
    twist_isInvertible := B.twist_isInvertible
    sub := kernel B.quot
    incl := kernel.ι B.quot
    quot := B.quot
    incl_comp_quot := kernel.condition B.quot
    shortExact := { exact := ShortComplex.exact_kernel B.quot }
    sub_rank := B.isFiniteLocallyFreeOfRank_kernel_quot }

/-- The bundle of `B.toBundleDatum` is the projective bundle `B.bundle`. -/
@[simp]
theorem toBundleDatum_bundle (B : BundleObject S X E r) :
    B.toBundleDatum.bundle = B.bundle := rfl

/-- The projection of `B.toBundleDatum` is the projection `B.proj`. -/
@[simp]
theorem toBundleDatum_proj (B : BundleObject S X E r) :
    B.toBundleDatum.proj = B.proj := rfl

/-- The twist `𝒪(1)` of `B.toBundleDatum` is the module `B.twist`. -/
@[simp]
theorem toBundleDatum_twist (B : BundleObject S X E r) :
    B.toBundleDatum.twist = B.twist := rfl

/-- The tautological surjection of `B.toBundleDatum` is `B.quot`. -/
@[simp]
theorem toBundleDatum_quot (B : BundleObject S X E r) :
    B.toBundleDatum.quot = B.quot := rfl

/-- The class of the twist of `B.toBundleDatum` in `Pic` is `B.twistClass`. -/
@[simp]
theorem toBundleDatum_twistClass (B : BundleObject S X E r) :
    B.toBundleDatum.twistClass = B.twistClass := rfl

end BundleObject

/-! ### An open and closed subscheme as an object of `𝒞` -/

/-- **Clause (2) of the source's category: an open and closed subscheme is an object of `𝒞`.**
For an object `X` of `𝒞` and an open and closed `U ⊆ X`, this is an object of `𝒞` whose scheme is
`U`, together with its inclusion into `X` as a morphism of `𝒞`.

Because `𝒞` is presented as an indexing functor `S : 𝒞 ⥤ Scheme` rather than as a subcategory of
schemes, "whose scheme is `U`" is an isomorphism `S(u) ≅ U` and not an equality; `hom` is required
to be the open immersion of `U` read through it.

The clause has a second sentence — a morphism of `𝒞` which factors through `U` is a morphism of
`𝒞` into `U` — and that is `exists_factor`. -/
structure ClopenSubobject {C : Type w} [Category.{v₁} C] (S : C ⥤ Scheme.{u}) (X : C)
    (U : (S.obj X).Opens) where
  /-- The subscheme `U`, as an object of `𝒞`. -/
  obj : C
  /-- Its inclusion `U ⟶ X`, a morphism of `𝒞`. -/
  hom : obj ⟶ X
  /-- Its scheme is `U`. -/
  iso : S.obj obj ≅ (U : Scheme.{u})
  /-- The inclusion is the open immersion of `U`, read through that identification. -/
  iso_hom_comp_ι : iso.hom ≫ U.ι = S.map hom
  /-- **The second sentence of clause (2).** A morphism `h : Z ⟶ X` of `𝒞` which factors through
  `U` — that is, every point of `Z` is carried into `U` — is a morphism of `𝒞` into `U`: there is
  a morphism `Z ⟶ U` of `𝒞` over `h`. -/
  exists_factor : ∀ {Z : C} (h : Z ⟶ X), (∀ z : S.obj Z, (S.map h).base z ∈ U) →
    ∃ h' : Z ⟶ obj, h' ≫ hom = h

/-! ### The standing situation with the source's clauses on `𝒞` -/

/-- **The standing situation of Stacks Section 45.12 with the source's clauses on `𝒞`.** A
`Stacks.WeilCohomology.ChernSetup` on a category `𝒞` of quasi-compact schemes in which the
projective bundles of finite locally free modules of constant rank and the open and closed
subschemes of objects are objects, the tautological datum of each projective bundle is the
constructed one, and `A` splits along finite decompositions into open and closed subschemes. -/
structure SourceChernSetup (C : Type w) [Category.{v₁} C] (S : C ⥤ Scheme.{u})
    extends ChernSetup.{u, v, v₁, w} C S where
  /-- **Clause (1).** Every object of `𝒞` is quasi-compact. -/
  compactSpace : ∀ X : C, CompactSpace (S.obj X)
  /-- **The grading is a direct sum decomposition**, `A(X) = ⨁_{i ≥ 0} A^i(X)`.

  This is the source's own reading of `A` as a functor to *graded* rings: its graded algebra is
  "a unital, associative, not necessarily commutative `𝐙`-algebra with a grading
  `A = ⨁_{i ≥ 0} A^i`". `DirectSum.IsInternal` is that, at the Mathlib spelling: the map
  `⨁_i A^i(X) ⟶ A(X)` is bijective.

  What it buys is the refinement of condition (4) that the target `∏_{i ≥ 0} A^i(X)` of Tag 0FI5
  needs — `Stacks.WeilCohomology.SourceChernSetup.mem_grade_of_bundleFormula`, that the tuple the
  projective bundle formula resolves a class of `A^n(P)` into is homogeneous of the complementary
  degrees. That was a hypothesis of the standing situation until this field was transcribed. -/
  isInternal_grade : ∀ X : C, DirectSum.IsInternal (grade X)
  /-- **Clause (3)(a).** The projective bundle of a finite locally free module of rank `r + 1` is
  an object of `𝒞`, and its projection is a morphism of `𝒞`.

  This is the *closure property* the source states, and nothing else: the bundle, its twist, its
  tautological sequence, the rank of the kernel of that sequence and the flatness of the
  projection are all constructed from it, by `Stacks.WeilCohomology.BundleObject.toBundleDatum`;
  `bundleDatum_eq` says that the datum `bundleDatum` of the underlying
  `Stacks.WeilCohomology.ChernSetup` is that construction. -/
  bundleObject : ∀ (X : C) (E : (S.obj X).Modules) (r : ℕ),
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1) →
      BundleObject S X E r
  /-- **The tautological datum is the constructed one.** The datum `bundleDatum` of the
  underlying `Stacks.WeilCohomology.ChernSetup` is
  `Stacks.WeilCohomology.BundleObject.toBundleDatum` of the clause-(3)(a) object. -/
  bundleDatum_eq : ∀ (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)),
    bundleDatum X E r hE = (bundleObject X E r hE).toBundleDatum
  /-- **Clause (2).** An open and closed subscheme of an object of `𝒞` is again an object of `𝒞`,
  and its inclusion is a morphism of `𝒞`. -/
  clopenSubobject : ∀ (X : C) (U : (S.obj X).Opens), IsClopen (U : Set (S.obj X)) →
    ClopenSubobject S X U
  /-- **Condition (2), for a finite decomposition.** If `X` is the disjoint union of finitely many
  open and closed subschemes `U i`, then `A(X) = ∏ᵢ A(U i)` through restriction along their
  inclusions. The source states the two-piece case `A(U ⨿ V) = A(U) × A(V)`; this is its
  iteration, which is the form the source's proofs use — `A(X) = ∏ A(X_r)` for the rank
  decomposition — the decomposition being finite by clause (1). -/
  bijective_pull_clopenSubobject : ∀ (X : C) (ι : Type) [Finite ι] (U : ι → (S.obj X).Opens)
    (hU : ∀ i, IsClopen (U i : Set (S.obj X))), (∀ i j, i ≠ j → Disjoint (U i) (U j)) →
      (⨆ i, U i) = ⊤ →
      Function.Bijective fun a : A X => fun i => pull (clopenSubobject X (U i) (hU i)).hom a
  /-- **Condition (2) is a splitting of graded rings.** `A` takes values in graded rings, so the
  splitting `A(X) = ∏ᵢ A(U i)` of condition (2) is one of graded rings: a class whose restriction
  to every piece lies in degree `n` lies in degree `n`. The other direction, that a class of
  degree `n` restricts to classes of degree `n`, is `pull_grade`. -/
  mem_grade_of_pull_clopenSubobject : ∀ (X : C) (ι : Type) [Finite ι] (U : ι → (S.obj X).Opens)
    (hU : ∀ i, IsClopen (U i : Set (S.obj X))), (∀ i j, i ≠ j → Disjoint (U i) (U j)) →
      (⨆ i, U i) = ⊤ → ∀ (a : A X) (n : ℕ),
      (∀ i, pull (clopenSubobject X (U i) (hU i)).hom a ∈
          grade (clopenSubobject X (U i) (hU i)).obj n) →
        a ∈ grade X n


namespace ChernSetup

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}} (𝔄 : ChernSetup.{u, v, v₁, w} C S)

/-- A natural number lies in degree zero: the unit does, by `one_mem`, and `A^0(X)` is an additive
subgroup. -/
theorem natCast_mem_grade_zero (X : C) (n : ℕ) : (n : 𝔄.A X) ∈ 𝔄.grade X 0 := by
  induction n with
  | zero => simpa using (𝔄.grade X 0).zero_mem
  | succ k ih => rw [Nat.cast_succ]; exact (𝔄.grade X 0).add_mem ih (𝔄.one_mem X)

end ChernSetup

namespace SourceChernSetup

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}
  (𝔄 : SourceChernSetup.{u, v, v₁, w} C S)

/-- **Restriction to the pieces of a finite decomposition into open and closed subschemes is
injective on `A`.**

This is the half of condition (2) that the reduction of an arbitrary finite locally free module to
one of constant rank consumes, and it is a consequence of that condition rather than a further
assumption, exactly as `Stacks.WeilCohomology.ChernSetup.injective_pull_proj` is a consequence of
condition (4). -/
theorem injective_pull_clopenSubobject (X : C) (ι : Type) [Finite ι]
    (U : ι → (S.obj X).Opens) (hU : ∀ i, IsClopen (U i : Set (S.obj X)))
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcover : (⨆ i, U i) = ⊤) :
    Function.Injective fun a : 𝔄.A X => fun i => 𝔄.pull (𝔄.clopenSubobject X (U i) (hU i)).hom a :=
  (𝔄.bijective_pull_clopenSubobject X ι U hU hdisj hcover).injective

/-- **`A(X)` is the zero ring when `X` has no points.**

An object with no points is the disjoint union of the empty family of open and closed subschemes,
so condition (2) identifies `A(X)` with the empty product. This is a consequence of condition (2)
rather than a further assumption. -/
theorem subsingleton_of_isEmpty (X : C) (hX : IsEmpty (S.obj X)) : Subsingleton (𝔄.A X) := by
  have hbot : (⊥ : (S.obj X).Opens) = ⊤ :=
    TopologicalSpace.Opens.ext (by simpa using (Set.univ_eq_empty_iff.2 hX).symm)
  refine ⟨fun a b => (𝔄.bijective_pull_clopenSubobject X Empty (fun i => i.elim)
    (fun i => i.elim) (fun i => i.elim) ?_).injective (funext fun i => i.elim)⟩
  rw [iSup_of_empty]
  exact hbot

/-- **Axiom (4), the projective bundle formula, read at the clause-(3)(a) object.** The field
`bijective_bundleFormula` of `Stacks.WeilCohomology.ChernSetup` is stated at `bundleDatum`, which
`bundleDatum_eq` identifies with the datum constructed from `bundleObject`. -/
theorem bijective_bundleFormula_bundleObject (X : C) (E : (S.obj X).Modules) (r : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E (r + 1)) :
    Function.Bijective fun a : Fin (r + 1) → 𝔄.A X =>
      ∑ i : Fin (r + 1),
        𝔄.c₁ (𝔄.bundleObject X E r hE).bundle (𝔄.bundleObject X E r hE).twistClass ^ (i : ℕ) *
          𝔄.pull (𝔄.bundleObject X E r hE).proj (a i) := by
  have h := 𝔄.bijective_bundleFormula X E r hE
  rw [𝔄.bundleDatum_eq X E r hE] at h
  exact h

end SourceChernSetup

end Stacks.WeilCohomology

end
