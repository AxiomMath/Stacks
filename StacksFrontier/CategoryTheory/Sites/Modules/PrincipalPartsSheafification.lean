module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsSectionwise
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialOperators
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.Differentials
import StacksCore.Tactic.StacksAttribute

/-!
# Sheafification of the modules of principal parts

Let `φ : O₁ ⟶ O₂` be a morphism of presheaves of commutative rings on a site and let `F` be
a presheaf of `O₂`-modules. Stacks Tag 0G3U asserts that the sheaf of principal parts of
order `k` of `F^#` relative to `O₂^# / O₁^#` is the sheaf associated to the presheaf
`X ↦ Pᵏ_{O₂(X)/O₁(X)}(F X)` of sectionwise modules of principal parts. That presheaf is
`Stacks.Sheaves.PrincipalParts.sectionwisePrincipalParts`, which carries the sectionwise
half of the statement; this file proves the comparison, which is the step the source
omits.

## Main definitions

* `Stacks.Sheaves.PrincipalParts.iterBracket`: the iterated commutator of a map with a
  *list* of scalars.
* `Stacks.Sheaves.PrincipalParts.IsSectionwiseOrderLE` and
  `Stacks.Sheaves.PrincipalParts.IsSectionwiseUniversal`: a morphism of the underlying
  presheaves of abelian groups is, at every object, a differential operator of order at most
  `k` relative to `O₁(X) → O₂(X)`, respectively a universal such operator.
* `Stacks.Sheaves.PrincipalParts.globalOpHom`: a global differential operator, regarded as a
  morphism of the underlying presheaves of abelian groups.

## Main results

* `Stacks.Sheaves.PrincipalParts.isDifferentialOperatorOfOrderLE_iff_iterBracket`: the
  *bracket characterisation* of the order of a differential operator — `D` has order at most
  `k` if and only if `iterBracket D rs` vanishes for every list `rs` of `k + 1` scalars.
* `Stacks.Sheaves.PrincipalParts.exists_list_lifting_cover`: along a locally surjective
  morphism of presheaves of rings, a whole list of sections of the target lifts on a single
  covering sieve.
* `Stacks.Sheaves.PrincipalParts.transfer_zero`: a naturally-defined expression vanishing on
  sections in the image of locally surjective maps vanishes on all sections of a separated
  target.
* `Stacks.Sheaves.PrincipalParts.isGlobalDiffOpOfOrder_of_isSectionwiseOrderLE` and
  `Stacks.Sheaves.PrincipalParts.isSectionwiseOrderLE_of_isGlobalDiffOpOfOrder`: the two
  directions between sectionwise order and `DiffOp.IsGlobalDiffOpOfOrder`.
* `Stacks.Sheaves.PrincipalParts.principalPartsComparison`: the sheafification of a
  sectionwise module of principal parts corepresents the functor of differential operators
  of bounded order out of the sheafification.
* `Stacks.Sheaves.PrincipalParts.principalPartsSheafification`: Tag 0G3U, which read as a
  statement about the sheaf of principal parts is Tag 09CV.

## Implementation notes

The order of a differential operator is handled through the *bracket characterisation*
`isDifferentialOperatorOfOrderLE_iff_iterBracket`, a single vanishing statement
`∀ rs, rs.length = k + 1 → iterBracket D rs = 0` in place of the recursive definition of
`LinearMap.IsDifferentialOperatorOfOrderLE`, so that a locality argument refines its covering
sieve once, in `exists_list_lifting_cover`, rather than once per order.

## References

* [Stacks Project, Tag 0G3U](https://stacks.math.columbia.edu/tag/0G3U)
* [Stacks Project, Tag 09CV](https://stacks.math.columbia.edu/tag/09CV)
* [Stacks Project, Tag 09CI](https://stacks.math.columbia.edu/tag/09CI), differential
  operators of bounded order, and [Tag 09CL](https://stacks.math.columbia.edu/tag/09CL),
  the universal property of the module of principal parts.
* [Stacks Project, Tag 0G3S](https://stacks.math.columbia.edu/tag/0G3S) and
  [Tag 09CT](https://stacks.math.columbia.edu/tag/09CT), the sheaf of principal parts.
-/

@[expose] public section

open CategoryTheory Opposite

universe v v₁ u u₁

namespace Stacks.Sheaves.PrincipalParts

/-- The iterated commutator of a map `D : M → N` of `S`-sets with a list of scalars:
`iterBracket D [] = D` and `iterBracket D (r :: rs)` is the iterated commutator of
`x ↦ D (r • x) - r • D x` with `rs`. -/
def iterBracket {S M N : Type*} [SMul S M] [SMul S N] [Sub N] (D : M → N) :
    List S → M → N
  | [] => D
  | r :: rs => iterBracket (fun x => D (r • x) - r • D x) rs

/-- The iterated commutator commutes with a map of the ambient data: if `f` and `g` are
compatible with the scalar action along `a`, and `g ∘ D = E ∘ f`, then
`iterBracket E (rs.map a) ∘ f = g ∘ iterBracket D rs`. -/
lemma iterBracket_map {S T M N M' N' : Type*} [SMul S M] [SMul S N] [SMul T M'] [SMul T N']
    [AddGroup N] [AddGroup N'] (a : S → T) (f : M → M') (g : N →+ N')
    (hf : ∀ r x, f (r • x) = a r • f x) (hg : ∀ r x, g (r • x) = a r • g x)
    (D : M → N) (E : M' → N') (h : ∀ x, E (f x) = g (D x)) (rs : List S) (x : M) :
    iterBracket E (rs.map a) (f x) = g (iterBracket D rs x) := by
  induction rs generalizing D E with
  | nil => exact h x
  | cons r rs ih => exact ih _ _ fun x => by rw [← hf, h, h, ← hg, map_sub]

/-- `iterBracket` depends on its operator only through the values of that operator. -/
lemma iterBracket_congr_fun {S M N : Type*} [SMul S M] [SMul S N] [Sub N] {D E : M → N}
    (h : ∀ x, D x = E x) (rs : List S) : iterBracket D rs = iterBracket E rs :=
  congrArg (fun F => iterBracket F rs) (funext h)

/-- The commutator of an iterated commutator with one further scalar is compatible with a
map of the ambient data, under the hypotheses of `iterBracket_map`. -/
lemma iterBracket_commutator_map {S T M N M' N' : Type*} [SMul S M] [SMul S N] [SMul T M']
    [SMul T N'] [AddGroup N] [AddGroup N'] (a : S → T) (f : M → M') (g : N →+ N')
    (hf : ∀ r x, f (r • x) = a r • f x) (hg : ∀ r x, g (r • x) = a r • g x)
    (D : M → N) (E : M' → N') (h : ∀ x, E (f x) = g (D x)) (rs : List S) (r : S) (x : M) :
    iterBracket E (rs.map a) (a r • f x) - a r • iterBracket E (rs.map a) (f x) =
      g (iterBracket D rs (r • x) - r • iterBracket D rs x) := by
  rw [← hf, iterBracket_map a f g hf hg D E h, iterBracket_map a f g hf hg D E h, ← hg,
    map_sub]

/-- Vanishing of an iterated commutator transported along a map of the ambient data. -/
lemma iterBracket_eq_zero_of_map {S T M N M' N' : Type*} [SMul S M] [SMul S N] [SMul T M']
    [SMul T N'] [AddGroup N] [AddGroup N'] (a : S → T) (f : M → M') (g : N →+ N')
    (hf : ∀ r x, f (r • x) = a r • f x) (hg : ∀ r x, g (r • x) = a r • g x)
    (D : M → N) (E : M' → N') (h : ∀ x, E (f x) = g (D x)) (rs : List S) (x : M)
    (hz : iterBracket D rs x = 0) : iterBracket E (rs.map a) (f x) = 0 := by
  rw [iterBracket_map a f g hf hg D E h, hz, map_zero]

/-- Commutation of an iterated commutator with a scalar, transported along a map of the
ambient data. -/
lemma iterBracket_smul_of_map {S T M N M' N' : Type*} [SMul S M] [SMul S N] [SMul T M']
    [SMul T N'] [AddGroup N] [AddGroup N'] (a : S → T) (f : M → M') (g : N →+ N')
    (hf : ∀ r x, f (r • x) = a r • f x) (hg : ∀ r x, g (r • x) = a r • g x)
    (D : M → N) (E : M' → N') (h : ∀ x, E (f x) = g (D x)) (rs : List S) (r : S) (x : M)
    (hsm : iterBracket D rs (r • x) = r • iterBracket D rs x) :
    iterBracket E (rs.map a) (a r • f x) = a r • iterBracket E (rs.map a) (f x) := by
  rw [← hf, iterBracket_map a f g hf hg D E h, iterBracket_map a f g hf hg D E h, hsm, hg]

section Linear

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- `diffBracket` is the commutator in the spelling in which
`LinearMap.IsDifferentialOperatorOfOrderLE` unfolds at a successor. -/
lemma diffBracket_eq (g : S) (D : M →ₗ[R] N) :
    diffBracket g D =
      D ∘ₗ Algebra.lsmul R R M g - Algebra.lsmul R R N g ∘ₗ D := rfl

/-- Being a differential operator of order at most `k + 1` means that every commutator
`diffBracket g D` is one of order at most `k`. -/
lemma isDifferentialOperatorOfOrderLE_succ_iff (k : ℕ) (D : M →ₗ[R] N) :
    D.IsDifferentialOperatorOfOrderLE S (k + 1) ↔
      ∀ g : S, (diffBracket g D).IsDifferentialOperatorOfOrderLE S k := by
  simp only [LinearMap.IsDifferentialOperatorOfOrderLE, diffBracket_eq]

/-- The iterated commutator of an `R`-linear map along a list of scalars is again given by
an `R`-linear map. -/
lemma iterBracket_linear (D : M →ₗ[R] N) (rs : List S) :
    ∃ E : M →ₗ[R] N, ∀ x, E x = iterBracket D rs x := by
  induction rs generalizing D with
  | nil => exact ⟨D, fun _ => rfl⟩
  | cons r rs ih => exact ih (diffBracket r D)

/-- The iterated commutator of an `R`-linear map is again `R`-linear, hence commutes with
the scalars in the image of `R → S`. -/
lemma iterBracket_smul_algebraMap (D : M →ₗ[R] N) (rs : List S) (r : R) (x : M) :
    iterBracket D rs (algebraMap R S r • x) = algebraMap R S r • iterBracket D rs x := by
  obtain ⟨E, hE⟩ := iterBracket_linear D rs
  rw [← hE, ← hE, IsScalarTower.algebraMap_smul, IsScalarTower.algebraMap_smul, E.map_smul]

/-- **The bracket characterisation of the order of a differential operator.** An `R`-linear
map `D : M → N` is a differential operator of order at most `k` relative to `R → S` if and
only if its iterated commutator along every list of `k + 1` scalars vanishes. -/
theorem isDifferentialOperatorOfOrderLE_iff_iterBracket (k : ℕ) (D : M →ₗ[R] N) :
    D.IsDifferentialOperatorOfOrderLE S k ↔
      ∀ rs : List S, rs.length = k + 1 → ∀ x, iterBracket D rs x = 0 := by
  induction k generalizing D with
  | zero =>
    constructor
    · intro h rs hr x
      match rs with
      | [r] => exact sub_eq_zero.mpr (h r x)
      | [] => simp at hr
      | r :: s :: rs => simp at hr
    · intro h r x
      exact sub_eq_zero.mp (h [r] rfl x)
  | succ k ih =>
    rw [isDifferentialOperatorOfOrderLE_succ_iff]
    constructor
    · intro h rs hr x
      cases rs with
      | nil => simp at hr
      | cons r rs => exact (ih (diffBracket r D)).mp (h r) rs (by simpa using hr) x
    · intro h r
      exact (ih (diffBracket r D)).mpr fun rs hr x => h (r :: rs) (by simpa using hr) x

end Linear

section Presheaf

variable {C : Type u₁} [Category.{v₁} C]

/-- The iterated commutator of a morphism of the underlying presheaves of abelian groups of
two presheaves of modules commutes with restriction. -/
lemma iterBracket_naturality {R : Cᵒᵖ ⥤ RingCat.{u}} {F G : PresheafOfModules.{v} R}
    (D : F.presheaf ⟶ G.presheaf) {X Y : Cᵒᵖ} (f : X ⟶ Y) (rs : List (R.obj X))
    (x : F.obj X) :
    iterBracket (D.app Y) (rs.map (R.map f)) (F.map f x) =
      G.map f (iterBracket (D.app X) rs x) :=
  iterBracket_map (R.map f) (F.map f) (G.map f).hom.toAddMonoidHom (F.map_smul f)
    (G.map_smul f) _ _ (fun x => NatTrans.naturality_apply D f x) rs x

/-- A differential operator of order at most `k` over a base object has vanishing iterated
commutator along every list of `k + 1` ring sections. -/
lemma iterBracket_eq_zero_of_isDiffOpOfOrder {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (φ : R ⟶ S) {F G : SheafOfModules.{v} S} (k : ℕ) {U : C}
    (D : DiffOp.RawOp F G U) (hD : DiffOp.IsDiffOpOfOrder φ k D) (Y : Over U)
    (rs : List (S.obj.obj (op Y.left))) (hr : rs.length = k + 1)
    (x : F.val.obj (op Y.left)) : iterBracket (D Y) rs x = 0 := by
  induction k generalizing U with
  | zero =>
    match rs with
    | [r] => exact sub_eq_zero.mpr (hD.2 Y r x)
    | [] => simp at hr
    | r :: s :: rs => simp at hr
  | succ k ih =>
    cases rs with
    | nil => simp at hr
    | cons r rs =>
      have h := ih (DiffOp.RawOp.commutator r (D.slice Y)) (hD.2.2 Y r)
        (Over.mk (𝟙 Y.left)) rs (by simpa using hr) x
      have he : (fun s =>
          D (Over.mk (𝟙 Y.left ≫ Y.hom)) (S.obj.map (𝟙 (op Y.left)) r • s) -
            S.obj.map (𝟙 (op Y.left)) r • D (Over.mk (𝟙 Y.left ≫ Y.hom)) s) =
          (fun s => D Y (r • s) - r • D Y s) := by
        funext s
        rw [S.obj.map_id, Category.id_comp]
        rfl
      change iterBracket (fun s =>
        D (Over.mk (𝟙 Y.left ≫ Y.hom)) (S.obj.map (𝟙 (op Y.left)) r • s) -
          S.obj.map (𝟙 (op Y.left)) r • D (Over.mk (𝟙 Y.left ≫ Y.hom)) s) rs x = 0 at h
      rwa [he] at h

/-- Conversely, a natural, `O₁`-linear raw operator whose iterated commutators along lists
of `k + 1` ring sections vanish is a differential operator of order at most `k`. -/
lemma isDiffOpOfOrder_of_iterBracket {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u}} (φ : R ⟶ S) {F G : SheafOfModules.{v} S} (k : ℕ) {U : C}
    (D : DiffOp.RawOp F G U) (hn : D.IsNatural)
    (hl : ∀ (Y : Over U) (rs : List (S.obj.obj (op Y.left)))
      (a : R.obj.obj (op Y.left)) (x : F.val.obj (op Y.left)),
      iterBracket (D Y) rs (DiffOp.sectionRingHom φ _ a • x) =
        DiffOp.sectionRingHom φ _ a • iterBracket (D Y) rs x)
    (hz : ∀ (Y : Over U) (rs : List (S.obj.obj (op Y.left))),
      rs.length = k + 1 → ∀ x, iterBracket (D Y) rs x = 0) :
    DiffOp.IsDiffOpOfOrder φ k D := by
  induction k generalizing U with
  | zero => exact ⟨hn, fun Y r x => sub_eq_zero.mp (hz Y [r] rfl x)⟩
  | succ k ih =>
    refine ⟨hn, fun Y a x => hl Y [] a x, fun Y r => ?_⟩
    apply ih
    · intro Z Z' f x
      change D (Over.mk (Z.hom ≫ Y.hom)) (S.obj.map Z.hom.op r • F.val.map f.left.op x) -
          S.obj.map Z.hom.op r • D (Over.mk (Z.hom ≫ Y.hom)) (F.val.map f.left.op x) =
        G.val.map f.left.op
          (D (Over.mk (Z'.hom ≫ Y.hom)) (S.obj.map Z'.hom.op r • x) -
            S.obj.map Z'.hom.op r • D (Over.mk (Z'.hom ≫ Y.hom)) x)
      have he : S.obj.map f.left.op (S.obj.map Z'.hom.op r) = S.obj.map Z.hom.op r := by
        rw [← RingCat.comp_apply, ← S.obj.map_comp, ← op_comp, Over.w f]
      rw [map_sub, G.val.map_smul, he, ← he, ← F.val.map_smul]
      let h : Over.mk (Z.hom ≫ Y.hom) ⟶ Over.mk (Z'.hom ≫ Y.hom) :=
        Over.homMk f.left (show f.left ≫ Z'.hom ≫ Y.hom = Z.hom ≫ Y.hom by
          rw [← Category.assoc, Over.w f])
      exact congrArg₂ (· - ·) (hn _ _ h _)
        (congrArg (S.obj.map f.left.op (S.obj.map Z'.hom.op r) • ·) (hn _ _ h x))
    · exact fun Z rs a x => hl (Over.mk (Z.hom ≫ Y.hom)) (S.obj.map Z.hom.op r :: rs) a x
    · exact fun Z rs hrs x =>
        hz (Over.mk (Z.hom ≫ Y.hom)) (S.obj.map Z.hom.op r :: rs) (by simpa using hrs) x

/-- **List lifting on a cover.** For a locally surjective morphism of presheaves of rings
and a finite *list* of sections of the target, there is a single covering sieve on which
every member of the list lifts simultaneously. -/
lemma exists_list_lifting_cover (J : GrothendieckTopology C) {R S : Cᵒᵖ ⥤ RingCat.{u}}
    (α : R ⟶ S) [Presheaf.IsLocallySurjective J α] {X : C} (rs : List (S.obj (op X))) :
    ∃ T : Sieve X, T ∈ J X ∧ ∀ ⦃Y⦄ (f : Y ⟶ X), T f →
      ∃ ss : List (R.obj (op Y)), ss.map (α.app _) = rs.map (S.map f.op) := by
  induction rs with
  | nil => exact ⟨⊤, J.top_mem X, fun _ _ _ => ⟨[], rfl⟩⟩
  | cons r rs ih =>
    obtain ⟨T, hT, ht⟩ := ih
    refine ⟨Presheaf.imageSieve α r ⊓ T,
      J.intersection_covering (Presheaf.imageSieve_mem J α r) hT, ?_⟩
    rintro Y f ⟨⟨s, hs⟩, hf⟩
    obtain ⟨ss, hss⟩ := ht f hf
    exact ⟨s :: ss, by simp [hs, hss]⟩

/-- **Transfer of a vanishing statement to sheafified sections.** An expression `e` natural
in restriction, which vanishes whenever its ring arguments and its module argument come from
the sources of locally surjective maps, vanishes on arbitrary sections of a separated
target. -/
lemma transfer_zero (J : GrothendieckTopology C) {R₁ R₂ S₁ S₂ : Cᵒᵖ ⥤ RingCat.{u}}
    (α₁ : R₁ ⟶ S₁) (α₂ : R₂ ⟶ S₂) [Presheaf.IsLocallySurjective J α₁]
    [Presheaf.IsLocallySurjective J α₂] {M A B : Cᵒᵖ ⥤ AddCommGrpCat.{v}} (q : M ⟶ A)
    [Presheaf.IsLocallySurjective J q] (hB : Presheaf.IsSheaf J B)
    (e : ∀ X, S₁.obj X → List (S₂.obj X) → A.obj X → B.obj X)
    (hn : ∀ {X Y} (f : X ⟶ Y) a (rs : List (S₂.obj X)) x,
      e Y (S₁.map f a) (rs.map (S₂.map f)) (A.map f x) = B.map f (e X a rs x))
    (n : ℕ)
    (he : ∀ X a (rs : List (R₂.obj X)) x, rs.length = n →
      e X (α₁.app X a) (rs.map (α₂.app X)) (q.app X x) = 0)
    (X : Cᵒᵖ) (a : S₁.obj X) (rs : List (S₂.obj X)) (x : A.obj X) (hr : rs.length = n) :
    e X a rs x = 0 := by
  obtain ⟨T, hT, ht⟩ := exists_list_lifting_cover J α₂ rs
  apply hB.isSeparated _ (Presheaf.imageSieve α₁ a ⊓ T ⊓ Presheaf.imageSieve q x)
    (J.intersection_covering (J.intersection_covering
      (Presheaf.imageSieve_mem J α₁ a) hT) (Presheaf.imageSieve_mem J q x))
  rintro Y f ⟨⟨⟨a₀, ha₀⟩, hf⟩, ⟨x₀, hx₀⟩⟩
  obtain ⟨rs₀, hrs₀⟩ := ht f hf
  have hlen : rs₀.length = n := by simpa [hr] using congrArg List.length hrs₀
  rw [← hn f.op, ← ha₀, ← hx₀, ← hrs₀, he _ _ _ _ hlen, map_zero]

/-- **Order from the order on images.** If a morphism `E` of the underlying presheaves of
abelian groups of two sheaves of modules has, on sections coming from a locally surjective
`q`, the `O₁`-linearity and the vanishing of iterated commutators along lists of ring
sections coming from locally surjective `α₂`, then `E` is a global differential operator of
order at most `k`. -/
lemma isGlobalDiffOpOfOrder_of_images {J : GrothendieckTopology C}
    {R₁ R₂ : Cᵒᵖ ⥤ RingCat.{u}} {S₁ S₂ : Sheaf J RingCat.{u}} (α₁ : R₁ ⟶ S₁.obj)
    (α₂ : R₂ ⟶ S₂.obj) [Presheaf.IsLocallySurjective J α₁]
    [Presheaf.IsLocallySurjective J α₂] (φ : S₁ ⟶ S₂) {M : Cᵒᵖ ⥤ AddCommGrpCat.{v}}
    {A B : SheafOfModules.{v} S₂} (q : M ⟶ A.val.presheaf)
    (hq : Presheaf.IsLocallySurjective J q) (E : A.val.presheaf ⟶ B.val.presheaf) (k : ℕ)
    (hl : ∀ X a (rs : List (R₂.obj X)) x,
      iterBracket (E.app X) (rs.map (α₂.app X))
          (DiffOp.sectionRingHom φ X (α₁.app X a) • q.app X x) =
        DiffOp.sectionRingHom φ X (α₁.app X a) •
          iterBracket (E.app X) (rs.map (α₂.app X)) (q.app X x))
    (hz : ∀ X (rs : List (R₂.obj X)), rs.length = k + 1 → ∀ x,
      iterBracket (E.app X) (rs.map (α₂.app X)) (q.app X x) = 0) :
    DiffOp.IsGlobalDiffOpOfOrder φ k (fun X => (E.app X).hom) := by
  have := hq
  intro U
  apply isDiffOpOfOrder_of_iterBracket
  · exact fun Y Y' f x => NatTrans.naturality_apply E f.left.op x
  · intro Y rs a x
    apply sub_eq_zero.mp
    apply transfer_zero J α₁ α₂ q B.isSheaf
      (fun X a rs x => iterBracket (E.app X) rs (DiffOp.sectionRingHom φ X a • x) -
        DiffOp.sectionRingHom φ X a • iterBracket (E.app X) rs x)
      _ rs.length _ (op Y.left) a rs x rfl
    · intro X Y f a rs x
      have hφ := NatTrans.naturality_apply φ.hom f a
      change DiffOp.sectionRingHom φ Y (S₁.obj.map f a) =
        S₂.obj.map f (DiffOp.sectionRingHom φ X a) at hφ
      rw [hφ]
      exact iterBracket_commutator_map (S₂.obj.map f) (A.val.map f)
        (B.val.map f).hom.toAddMonoidHom (A.val.map_smul f) (B.val.map_smul f) _ _
        (fun x => NatTrans.naturality_apply E f x) rs (DiffOp.sectionRingHom φ X a) x
    · exact fun X a rs x _ => sub_eq_zero.mpr (hl X a rs x)
  · intro Y rs hrs x
    apply transfer_zero J α₁ α₂ q B.isSheaf (fun X _ rs x => iterBracket (E.app X) rs x)
      _ (k + 1) _ (op Y.left) 0 rs x hrs
    · exact fun f a rs x => iterBracket_naturality E f rs x
    · exact fun X a rs x hrs => hz X rs hrs x

end Presheaf

section Comparison

variable {C : Type u₁} [Category.{v₁} C]

/-- `IsSectionwiseOrderLE φ D k` says that at every object the morphism `D` of underlying
presheaves of abelian groups is given by a differential operator of order at most `k`
relative to the ring map `O₁(X) → O₂(X)`. -/
abbrev IsSectionwiseOrderLE {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : R ⟶ S)
    {F P : PresheafOfModules.{v} (S ⋙ forget₂ CommRingCat RingCat)}
    (D : F.presheaf ⟶ P.presheaf) (k : ℕ) : Prop :=
  ∀ X : Cᵒᵖ,
    letI : Algebra (R.obj X) (S.obj X) := (φ.app X).hom.toAlgebra
    letI : Module (R.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
    letI : Module (R.obj X) (P.obj X) := Module.compHom (P.obj X) (φ.app X).hom
    letI : IsScalarTower (R.obj X) (S.obj X) (F.obj X) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    letI : IsScalarTower (R.obj X) (S.obj X) (P.obj X) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∃ d : F.obj X →ₗ[R.obj X] P.obj X,
      (∀ x, d x = D.app X x) ∧ d.IsDifferentialOperatorOfOrderLE (S.obj X) k

/-- `IsSectionwiseUniversal φ D k` says that at every object the morphism `D` of underlying
presheaves of abelian groups is given by a *universal* differential operator of order at
most `k`, i.e. exhibits the sections of the target as a module of principal parts. -/
abbrev IsSectionwiseUniversal {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : R ⟶ S)
    {F P : PresheafOfModules.{v} (S ⋙ forget₂ CommRingCat RingCat)}
    (D : F.presheaf ⟶ P.presheaf) (k : ℕ) : Prop :=
  ∀ X : Cᵒᵖ,
    letI : Algebra (R.obj X) (S.obj X) := (φ.app X).hom.toAlgebra
    letI : Module (R.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
    letI : Module (R.obj X) (P.obj X) := Module.compHom (P.obj X) (φ.app X).hom
    letI : IsScalarTower (R.obj X) (S.obj X) (F.obj X) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    letI : IsScalarTower (R.obj X) (S.obj X) (P.obj X) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    ∃ d : F.obj X →ₗ[R.obj X] P.obj X,
      (∀ x, d x = D.app X x) ∧ d.IsUniversalDifferentialOperatorOfOrderLE (S.obj X) k

/-- **Sectionwise order implies sheaf-level order.** If `D` has sectionwise order at most
`k` and `E` is a morphism of sheaves of modules compatible with `D` along locally surjective
comparison maps, then `E` is a global differential operator of order at most `k`. -/
lemma isGlobalDiffOpOfOrder_of_isSectionwiseOrderLE {J : GrothendieckTopology C}
    {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : R ⟶ S) {R' S' : Sheaf J RingCat.{u}}
    (α : R ⋙ forget₂ CommRingCat RingCat ⟶ R'.obj)
    (β : S ⋙ forget₂ CommRingCat RingCat ⟶ S'.obj) [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallySurjective J β] (φ' : R' ⟶ S')
    (hφ : ∀ X a, DiffOp.sectionRingHom φ' X (α.app X a) = β.app X (φ.app X a))
    {F P : PresheafOfModules.{v} (S ⋙ forget₂ CommRingCat RingCat)}
    (D : F.presheaf ⟶ P.presheaf) (k : ℕ) (hD : IsSectionwiseOrderLE φ D k)
    {A B : SheafOfModules.{v} S'}
    (q : F ⟶ (PresheafOfModules.restrictScalars β).obj A.val)
    (t : P ⟶ (PresheafOfModules.restrictScalars β).obj B.val)
    (hq : Presheaf.IsLocallySurjective J ((PresheafOfModules.toPresheaf _).map q))
    (E : A.val.presheaf ⟶ B.val.presheaf)
    (hE : ∀ X x, E.app X (q.app X x) = t.app X (D.app X x)) :
    DiffOp.IsGlobalDiffOpOfOrder φ' k (fun X => (E.app X).hom) := by
  have key (X : Cᵒᵖ) :
      (∀ (a : R.obj X) (rs : List (S.obj X)) x,
        iterBracket (E.app X) (rs.map (β.app X))
            (β.app X (φ.app X a) • (show A.val.obj X from q.app X x)) =
          β.app X (φ.app X a) • iterBracket (E.app X) (rs.map (β.app X)) (q.app X x)) ∧
      ∀ rs : List (S.obj X), rs.length = k + 1 → ∀ x,
        iterBracket (E.app X) (rs.map (β.app X)) (q.app X x) = 0 := by
    let : Algebra (R.obj X) (S.obj X) := (φ.app X).hom.toAlgebra
    let : Module (R.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
    let : Module (R.obj X) (P.obj X) := Module.compHom (P.obj X) (φ.app X).hom
    let : IsScalarTower (R.obj X) (S.obj X) (F.obj X) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let : IsScalarTower (R.obj X) (S.obj X) (P.obj X) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    obtain ⟨d, hd, hdorder⟩ := hD X
    have hdE : ∀ y, E.app X (q.app X y) = (t.app X).hom.toAddMonoidHom (d y) :=
      fun y => (hE X y).trans (congrArg (t.app X) (hd y)).symm
    exact ⟨fun a rs x => iterBracket_smul_of_map (M := F.obj X) (N := P.obj X)
      (M' := A.val.obj X) (N' := B.val.obj X) (β.app X) (q.app X)
      (t.app X).hom.toAddMonoidHom (fun r y => (q.app X).hom.map_smul r y)
      (fun r y => (t.app X).hom.map_smul r y) d (E.app X) hdE rs (φ.app X a) x
      (iterBracket_smul_algebraMap (S := S.obj X) d rs a x),
      fun rs hrs x => iterBracket_eq_zero_of_map (M := F.obj X) (N := P.obj X)
      (M' := A.val.obj X) (N' := B.val.obj X) (β.app X) (q.app X)
      (t.app X).hom.toAddMonoidHom (fun r y => (q.app X).hom.map_smul r y)
      (fun r y => (t.app X).hom.map_smul r y) d (E.app X) hdE rs x
      ((isDifferentialOperatorOfOrderLE_iff_iterBracket k d).mp hdorder rs hrs x)⟩
  exact isGlobalDiffOpOfOrder_of_images α β φ'
    (show F.presheaf ⟶ A.val.presheaf from
      (PresheafOfModules.toPresheaf (S ⋙ forget₂ CommRingCat RingCat)).map q) hq E k
    (fun X a rs x => by rw [hφ]; exact (key X).1 a rs x) fun X rs hrs x => (key X).2 rs hrs x

/-- A global differential operator of order at most `k`, regarded as a morphism of the
underlying presheaves of abelian groups. -/
def globalOpHom {J : GrothendieckTopology C} {R S : Sheaf J RingCat.{u}} {φ : R ⟶ S}
    {F G : SheafOfModules.{v} S} {k : ℕ} (D : DiffOp.GlobalOp F G)
    (hD : DiffOp.IsGlobalDiffOpOfOrder φ k D) : F.val.presheaf ⟶ G.val.presheaf where
  app X := AddCommGrpCat.ofHom (D X)
  naturality {X Y} f := by
    ext x
    exact DiffOp.RawOp.isNatural_of_isDiffOpOfOrder φ k (D.restrict X.unop) (hD X.unop)
      (Over.mk f.unop) (Over.mk (𝟙 X.unop)) (Over.homMk f.unop (by simp)) x

/-- **Sheaf-level order implies sectionwise order.** Restricting a global differential
operator of order at most `k` along a comparison map of presheaves of modules gives a
morphism of sectionwise order at most `k`. -/
lemma isSectionwiseOrderLE_of_isGlobalDiffOpOfOrder {J : GrothendieckTopology C}
    {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : R ⟶ S) {R' S' : Sheaf J RingCat.{u}}
    (α : R ⋙ forget₂ CommRingCat RingCat ⟶ R'.obj)
    (β : S ⋙ forget₂ CommRingCat RingCat ⟶ S'.obj) (φ' : R' ⟶ S')
    (hφ : ∀ X a, DiffOp.sectionRingHom φ' X (α.app X a) = β.app X (φ.app X a))
    {F : PresheafOfModules.{v} (S ⋙ forget₂ CommRingCat RingCat)}
    {A B : SheafOfModules.{v} S'}
    (q : F ⟶ (PresheafOfModules.restrictScalars β).obj A.val) (E : DiffOp.GlobalOp A B)
    (k : ℕ) (hE : DiffOp.IsGlobalDiffOpOfOrder φ' k E) :
    IsSectionwiseOrderLE φ (P := (PresheafOfModules.restrictScalars β).obj B.val)
      ((PresheafOfModules.toPresheaf _).map q ≫ globalOpHom E hE) k := by
  intro X
  let : Algebra (R.obj X) (S.obj X) := (φ.app X).hom.toAlgebra
  let : Module (R.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  let B₀ := (PresheafOfModules.restrictScalars β).obj B.val
  let : Module (R.obj X) (B₀.obj X) := Module.compHom (B₀.obj X) (φ.app X).hom
  let : IsScalarTower (R.obj X) (S.obj X) (F.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower (R.obj X) (S.obj X) (B₀.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let d : F.obj X →ₗ[R.obj X] B₀.obj X :=
    { __ := (E X).comp (q.app X).hom.toAddMonoidHom
      map_smul' := fun a x => by
        change E X (q.app X (φ.app X a • x)) = β.app X (φ.app X a) • E X (q.app X x)
        rw [(q.app X).hom.map_smul]
        change E X (β.app X (φ.app X a) • (show A.val.obj X from q.app X x)) =
          β.app X (φ.app X a) • E X (q.app X x)
        rw [← hφ X a]
        exact DiffOp.RawOp.isO1Linear_of_isDiffOpOfOrder φ' k (E.restrict X.unop)
          (hE X.unop) (Over.mk (𝟙 X.unop)) (α.app X a) (q.app X x) }
  refine ⟨d, fun _ => rfl, (isDifferentialOperatorOfOrderLE_iff_iterBracket k d).mpr ?_⟩
  intro rs hrs x
  have hi := iterBracket_map (S := S.obj X) (T := S'.obj.obj X) (M := F.obj X)
    (M' := A.val.obj X) (N := B₀.obj X) (N' := B.val.obj X) (β.app X) (q.app X)
    (AddMonoidHom.id _) (fun r y => (q.app X).hom.map_smul r y) (fun _ _ => rfl) d (E X)
    (fun _ => rfl) rs x
  exact hi.symm.trans (iterBracket_eq_zero_of_isDiffOpOfOrder φ' k (E.restrict X.unop)
    (hE X.unop) (Over.mk (𝟙 X.unop)) (rs.map (β.app X)) (by simpa using hrs) (q.app X x))

section Universal

variable {R S : Type u} {M P N : Type (max u v)} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup M] [Module R M] [Module S M] [IsScalarTower R S M]
  [AddCommGroup P] [Module R P] [Module S P] [IsScalarTower R S P]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Postcomposing a differential operator of order at most `k` with an `S`-linear map gives
again a differential operator of order at most `k`. -/
lemma isDifferentialOperatorOfOrderLE_comp {k : ℕ} (d : M →ₗ[R] P)
    (hd : d.IsDifferentialOperatorOfOrderLE S k) (f : P →ₗ[S] N) :
    (f.restrictScalars R ∘ₗ d).IsDifferentialOperatorOfOrderLE S k := by
  apply (isDifferentialOperatorOfOrderLE_iff_iterBracket k _).mpr
  intro rs hrs x
  have h := iterBracket_map (id : S → S) (id : M → M) f.toAddMonoidHom (fun _ _ => rfl)
    f.map_smul d (f.restrictScalars R ∘ₗ d) (fun _ => rfl) rs x
  simpa only [List.map_id_fun, id_eq,
    (isDifferentialOperatorOfOrderLE_iff_iterBracket k d).mp hd rs hrs x, map_zero] using h

/-- Two `S`-linear maps out of a module of principal parts that agree on the image of the
universal operator are equal. -/
lemma hom_ext_of_isUniversal {k : ℕ} (d : M →ₗ[R] P)
    (hd : d.IsUniversalDifferentialOperatorOfOrderLE S k) (f g : P →ₗ[S] N)
    (h : ∀ x, f (d x) = g (d x)) : f = g := by
  obtain ⟨l, hl, hu⟩ := hd.2 (f.restrictScalars R ∘ₗ d)
    (isDifferentialOperatorOfOrderLE_comp d hd.1 f)
  exact (hu f fun _ => rfl).trans (hu g fun x => (h x).symm).symm

end Universal

/-- Two morphisms of modules out of a sectionwise module of principal parts at `X` that agree on
the image of the universal operator are equal. -/
private lemma hom_ext_of_isSectionwiseUniversal_app {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : R ⟶ S)
    {F P : PresheafOfModules.{max u v} (S ⋙ forget₂ CommRingCat RingCat)}
    (D : F.presheaf ⟶ P.presheaf) {k : ℕ} (hD : IsSectionwiseUniversal φ D k) (X : Cᵒᵖ)
    {N : ModuleCat.{max u v} ((S ⋙ forget₂ CommRingCat RingCat).obj X)} (f g : P.obj X ⟶ N)
    (h : ∀ x, f (D.app X x) = g (D.app X x)) : f = g := by
  let : Algebra (R.obj X) (S.obj X) := (φ.app X).hom.toAlgebra
  let : Module (R.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
  let : Module (R.obj X) (P.obj X) := Module.compHom (P.obj X) (φ.app X).hom
  let : Module (R.obj X) N := Module.compHom N (φ.app X).hom
  let : IsScalarTower (R.obj X) (S.obj X) (F.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower (R.obj X) (S.obj X) (P.obj X) :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower (R.obj X) (S.obj X) N :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨d, hd, hu⟩ := hD X
  apply ModuleCat.hom_ext
  apply hom_ext_of_isUniversal d hu
  intro x
  rw [hd]
  exact h x

/-- Two morphisms of presheaves of modules out of a sectionwise module of principal parts
that agree on the image of the universal operator are equal. -/
lemma hom_ext_of_isSectionwiseUniversal {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : R ⟶ S)
    {F P Q : PresheafOfModules.{max u v} (S ⋙ forget₂ CommRingCat RingCat)}
    (D : F.presheaf ⟶ P.presheaf) {k : ℕ} (hD : IsSectionwiseUniversal φ D k) (f g : P ⟶ Q)
    (h : ∀ X x, f.app X (D.app X x) = g.app X (D.app X x)) : f = g :=
  PresheafOfModules.hom_ext fun X =>
    hom_ext_of_isSectionwiseUniversal_app φ D hD X _ _ (h X)

/-- A morphism of presheaves of modules of sectionwise order at most `k` out of `F` factors
through a sectionwise module of principal parts of order `k`. -/
lemma exists_lift_of_isSectionwiseUniversal {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : R ⟶ S)
    {F P Q : PresheafOfModules.{max u v} (S ⋙ forget₂ CommRingCat RingCat)}
    (D : F.presheaf ⟶ P.presheaf) {k : ℕ} (hD : IsSectionwiseUniversal φ D k)
    (E : F.presheaf ⟶ Q.presheaf) (hE : IsSectionwiseOrderLE φ E k) :
    ∃ f : P ⟶ Q, ∀ X x, f.app X (D.app X x) = E.app X x := by
  classical
  have h (X : Cᵒᵖ) : ∃ f : P.obj X ⟶ Q.obj X, ∀ x, f (D.app X x) = E.app X x := by
    let : Algebra (R.obj X) (S.obj X) := (φ.app X).hom.toAlgebra
    let : Module (R.obj X) (F.obj X) := Module.compHom (F.obj X) (φ.app X).hom
    let : Module (R.obj X) (P.obj X) := Module.compHom (P.obj X) (φ.app X).hom
    let : Module (R.obj X) (Q.obj X) := Module.compHom (Q.obj X) (φ.app X).hom
    let : IsScalarTower (R.obj X) (S.obj X) (F.obj X) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let : IsScalarTower (R.obj X) (S.obj X) (P.obj X) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    let : IsScalarTower (R.obj X) (S.obj X) (Q.obj X) :=
      IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    obtain ⟨d, hd, hu⟩ := hD X
    obtain ⟨e, he, heorder⟩ := hE X
    obtain ⟨f, hf, _⟩ := hu.2 e heorder
    refine ⟨ModuleCat.ofHom f, ?_⟩
    intro x
    change f (D.app X x) = E.app X x
    exact (congrArg (fun z => f z) (hd x)).symm.trans ((hf x).trans (he x))
  choose f hf using h
  refine ⟨{ app := f, naturality := ?_ }, hf⟩
  intro X Y a
  apply hom_ext_of_isSectionwiseUniversal_app φ D hD X
  intro x
  change (f Y) (P.map a (D.app X x)) = Q.map a ((f X) (D.app X x))
  have hDn := NatTrans.naturality_apply D a x
  change D.app Y (F.map a x) = P.map a (D.app X x) at hDn
  exact (congrArg (fun z => (f Y) z) hDn).symm.trans
    (((hf Y (F.map a x)).trans (NatTrans.naturality_apply E a x)).trans
      (congrArg (fun z => Q.map a z) (hf X x)).symm)

end Comparison

end Stacks.Sheaves.PrincipalParts

namespace Stacks.Sheaves.PrincipalParts

open Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C]

/-- **The comparison isomorphism.** If `D : F.presheaf ⟶ P.presheaf` exhibits `P` as the
presheaf of sectionwise modules of principal parts of order `k`, then the sheafification of
`P` corepresents the functor of differential operators of order at most `k` out of the
sheafification of `F`, i.e. is the sheaf of principal parts of `F^#`. -/
noncomputable def principalPartsComparison {J : GrothendieckTopology C}
    {R S : Cᵒᵖ ⥤ CommRingCat.{u}} (φ : R ⟶ S) {R' S' : Sheaf J RingCat.{u}}
    (α : R ⋙ forget₂ CommRingCat RingCat ⟶ R'.obj)
    (β : S ⋙ forget₂ CommRingCat RingCat ⟶ S'.obj) [Presheaf.IsLocallySurjective J α]
    [Presheaf.IsLocallyInjective J β] [Presheaf.IsLocallySurjective J β]
    [HasWeakSheafify J AddCommGrpCat.{max u u₁ v₁ v}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u u₁ v₁ v}] (φ' : R' ⟶ S')
    (hφ : ∀ X a, DiffOp.sectionRingHom φ' X (α.app X a) = β.app X (φ.app X a))
    {F P : PresheafOfModules.{max u u₁ v₁ v} (S ⋙ forget₂ CommRingCat RingCat)}
    (D : F.presheaf ⟶ P.presheaf) (k : ℕ) (hD : IsSectionwiseUniversal φ D k) :
    (AlgebraicGeometry.SheafOfModules.differentialOperatorsFunctor.{v₁, u₁, u,
        max u u₁ v₁ v} φ' ((PresheafOfModules.sheafification β).obj F) k).coreprX ≅
      (PresheafOfModules.sheafification β).obj P := by
  classical
  let A := (PresheafOfModules.sheafification β).obj F
  let B := (PresheafOfModules.sheafification β).obj P
  let q := (PresheafOfModules.sheafificationAdjunction β).unit.app F
  let t := (PresheafOfModules.sheafificationAdjunction β).unit.app P
  let E : A.val.presheaf ⟶ B.val.presheaf := sheafifyMap J D
  have hE (X) (x : F.obj X) : E.app X (q.app X x) = t.app X (D.app X x) :=
    (congrArg (fun f : F.presheaf ⟶ B.val.presheaf => f.app X x)
      (toSheafify_naturality J D)).symm
  have hDO : IsSectionwiseOrderLE φ D k := fun X => (hD X).imp fun _ h => ⟨h.1, h.2.1⟩
  have hq : Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf (S ⋙ forget₂ CommRingCat RingCat)).map q) := by
    change Presheaf.IsLocallySurjective J (toSheafify J F.presheaf)
    infer_instance
  have horder :=
    isGlobalDiffOpOfOrder_of_isSectionwiseOrderLE φ α β φ' hφ D k hDO q t hq E hE
  let U : DiffOp.GlobalOp A B := fun X => (E.app X).hom
  let H := AlgebraicGeometry.SheafOfModules.differentialOperatorsFunctor.{v₁, u₁, u,
    max u u₁ v₁ v} φ' A k
  let ev (G : SheafOfModules.{max u u₁ v₁ v} S') (f : B ⟶ G) : H.obj G :=
    ⟨AlgebraicGeometry.SheafOfModules.postcomp U f,
      AlgebraicGeometry.SheafOfModules.postcomp_isDiffOpOfOrder φ' k U horder f⟩
  have bij (G : SheafOfModules.{max u u₁ v₁ v} S') : Function.Bijective (ev G) := by
    constructor
    · intro f g hfg
      apply (PresheafOfModules.sheafificationHomEquiv β).injective
      apply hom_ext_of_isSectionwiseUniversal.{max u u₁ v₁ v, v₁, u, u₁} φ D hD
      intro X x
      have h := congrArg (fun z : H.obj G => z.val X (q.app X x)) hfg
      change (f.val.app X) (E.app X (q.app X x)) =
        (g.val.app X) (E.app X (q.app X x)) at h
      exact (congrArg (fun z => (f.val.app X) z) (hE X x)).symm.trans
        (h.trans (congrArg (fun z => (g.val.app X) z) (hE X x)))
    · intro δ
      let δ₀ : F.presheaf ⟶ ((PresheafOfModules.restrictScalars β).obj G.val).presheaf :=
        (PresheafOfModules.toPresheaf _).map q ≫ globalOpHom δ.val δ.property
      have hδ₀ : IsSectionwiseOrderLE φ δ₀ k :=
        isSectionwiseOrderLE_of_isGlobalDiffOpOfOrder φ α β φ' hφ q δ.val k δ.property
      obtain ⟨l, hl⟩ :=
        exists_lift_of_isSectionwiseUniversal.{max u u₁ v₁ v, v₁, u, u₁} φ D hD δ₀ hδ₀
      let f : B ⟶ G := (PresheafOfModules.sheafificationHomEquiv β).symm l
      refine ⟨f, ?_⟩
      have hfac := (PresheafOfModules.sheafificationHomEquiv β).apply_symm_apply l
      have heq : E ≫ (PresheafOfModules.toPresheaf S'.obj).map f.val =
          globalOpHom δ.val δ.property := by
        apply sheafify_hom_ext J _ _ G.isSheaf
        ext X x
        change f.val.app X (E.app X (q.app X x)) = δ.val X (q.app X x)
        exact (congrArg (fun z => f.val.app X z) (hE X x)).trans
          ((congrArg (fun z => (PresheafOfModules.Hom.app z X) (D.app X x)) hfac).trans
            (hl X x))
      exact Subtype.ext <| funext fun X => AddMonoidHom.ext fun x =>
        congrArg (fun z : A.val.presheaf ⟶ G.val.presheaf => z.app X x) heq
  exact H.corepresentableBy.uniqueUpToIso
    { homEquiv := Equiv.ofBijective _ (bij _)
      homEquiv_comp _ _ := rfl }

variable (J : GrothendieckTopology C)

/-- **Stacks Project, Tag 0G3U**, which read as a statement about the sheaf of principal parts
is **Tag 09CV**. Let `φ : O₁ ⟶ O₂` be a morphism of presheaves of
commutative rings on a site and let `F` be a presheaf of `O₂`-modules. Then the sheaf of
principal parts of order `k` of `F^#` relative to `O₂^# / O₁^#` is the sheaf associated to
the presheaf `X ↦ Pᵏ_{O₂(X)/O₁(X)}(F X)` of sectionwise modules of principal parts, and the
sectionwise universal operators are compatible with restriction. -/
@[stacks 0G3U, stacks 09CV, ega "IV 16.4.24" "(ii)"]
noncomputable def principalPartsSheafification [HasWeakSheafify J CommRingCat.{u}]
    [J.WEqualsLocallyBijective CommRingCat.{u}]
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u u₁ v₁ v}]
    [HasWeakSheafify J AddCommGrpCat.{max u u₁ v₁ v}] {O₁ O₂ : Cᵒᵖ ⥤ CommRingCat.{u}}
    (φ : O₁ ⟶ O₂)
    (F : PresheafOfModules.{max u u₁ v₁ v} (O₂ ⋙ forget₂ CommRingCat.{u} RingCat.{u}))
    (k : ℕ) :
    Σ' P : PresheafOfModules.{max u u₁ v₁ v}
        (O₂ ⋙ forget₂ CommRingCat.{u} RingCat.{u}),
      Σ' D : F.presheaf ⟶ P.presheaf,
        Σ' _e : (AlgebraicGeometry.SheafOfModules.differentialOperatorsFunctor.{v₁, u₁, u,
            max u u₁ v₁ v}
            ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
              (associatedCommRingSheafMap J φ))
            ((PresheafOfModules.sheafification (toAssociatedRingSheaf J O₂)).obj F)
            k).coreprX (hF :=
              AlgebraicGeometry.SheafOfModules.differentialOperatorsFunctor_isCorepresentable
                ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
                  (associatedCommRingSheafMap J φ))
                ((PresheafOfModules.sheafification (toAssociatedRingSheaf J O₂)).obj F) k) ≅
          (PresheafOfModules.sheafification (toAssociatedRingSheaf J O₂)).obj P,
        ∀ X : Cᵒᵖ,
          letI : Algebra (O₁.obj X) (O₂.obj X) := (φ.app X).hom.toAlgebra
          letI : Module (O₁.obj X) (F.obj X) :=
            Module.compHom (F.obj X) (φ.app X).hom
          letI : Module (O₁.obj X) (P.obj X) :=
            Module.compHom (P.obj X) (φ.app X).hom
          letI : IsScalarTower (O₁.obj X) (O₂.obj X) (F.obj X) :=
            IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
          letI : IsScalarTower (O₁.obj X) (O₂.obj X) (P.obj X) :=
            IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
          ∃ d : F.obj X →ₗ[O₁.obj X] P.obj X,
            (∀ x, d x = (D.app X).hom x) ∧
              d.IsUniversalDifferentialOperatorOfOrderLE (O₂.obj X) k := by
  classical
  exact Classical.choice (by
    obtain ⟨P, D, hD⟩ := sectionwisePrincipalPartsData.{v, v₁, u, u₁} φ F k
    refine ⟨⟨P, D, ?_, hD⟩⟩
    apply principalPartsComparison.{v, v₁, u, u₁} φ (toAssociatedRingSheaf J O₁)
      (toAssociatedRingSheaf J O₂)
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).map
        (associatedCommRingSheafMap J φ))
      _ D k hD
    intro X a
    exact (congrArg (fun f : O₁ ⟶ sheafify J O₂ => f.app X a)
      (toSheafify_naturality J φ)).symm)

end Stacks.Sheaves.PrincipalParts
