module

public import Mathlib.CategoryTheory.ObjectProperty.Small
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleEssentiallySmall

/-!
# A cardinality encoding of the invertible sheaves of modules on a ringed site

[Stacks, Tag 040B](https://stacks.math.columbia.edu/tag/040B) asserts that on a ringed site the
isomorphism classes of invertible sheaves of modules form a set. This file gives a cardinality
encoding of the invertible sheaves of modules: a code in a fixed type, such that two invertible
modules with the same code are isomorphic.

The encoding is the following. By `Stacks.SheafOfModules.exists_cover_injective_finFree` (the
uniform local bound extracted from [Tag 0B8N (b)](https://stacks.math.columbia.edu/tag/0B8N) in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/InvertibleEssentiallySmall.lean`), every object `U`
of the site has a covering on whose members an invertible sheaf of modules `L` embeds linearly
into a finite free module of sections of the structure sheaf. Choosing, at every object `W` where
one exists at all, an injective linear map `ι W : L(W) → (ℕ → O(W))`, the *code* of `L` at `U` is
the range of

`L(U) → ∏ (p : Σ W : Cᵒᵖ, (U ⟶ W)), (ℕ → O(W))`, `s ↦ (p ↦ ι p.1 (L.map p.2 s))`.

Separatedness of `L` makes this map injective for *every* `U`, because the covering of `U`
supplies, among the `p`, enough objects at which `ι` is injective. The family of ranges is a
single element of a type in `Type (max u v w)`, and two invertible modules with the same code are
isomorphic, since two injective linear maps with the same range differ by a linear equivalence
and the comparison is natural. Picking one representative per code gives the small property that
`ObjectProperty.EssentiallySmall` asks for.

## Main definitions

* `CategoryTheory.ObjectProperty.essentiallySmall_of_invariant`: a property of objects with a
  complete invariant valued in a `w`-small type is essentially small at `w`.
* `Stacks.PresheafOfModules.chosenEmbedding`: at each object, an injective linear map from the
  sections of a presheaf of modules into `ℕ → R(W)`, whenever one exists.
* `Stacks.PresheafOfModules.Code`: the type of codes of presheaves of modules over `R`.
* `Stacks.PresheafOfModules.encode`, `Stacks.PresheafOfModules.code`: the encoding map on
  sections, and the resulting family of ranges.
* `Stacks.PresheafOfModules.transfer`: the comparison map on sections between two presheaves of
  modules with the same code.

## Main results

* `Stacks.PresheafOfModules.injective_encode`: for a separated presheaf of modules all of whose
  objects have a covering sieve factoring through objects with injective chosen embeddings, the
  encoding map is injective at every object.
* `Stacks.PresheafOfModules.isoOfCodeEq`: two presheaves of modules with injective encodings and
  the same code are isomorphic.
* `Stacks.SheafOfModules.injective_encode_of_isInvertible`: the encoding map of an invertible
  sheaf of modules is injective at every object.
* `Stacks.SheafOfModules.isoOfCodeEq`: two invertible sheaves of modules with the same code are
  isomorphic.

## Implementation notes

*What is forced.* The common target `∏ (p : Σ W : Cᵒᵖ, (U ⟶ W)), (ℕ → R(W))` of the family of
semilinear injections is an object of `PresheafOfModules.{max u v w}`, *not* of
`PresheafOfModules.{w}`, so it is not an object of the ambient category and Mathlib has no
`PresheafOfModules.uliftFunctor` to bring it back. This is not an obstruction, and the file never
forms that object: only the family of maps `encode M U` and the single naturality identity
`encode_restrictₛₗ` are used, so the `map_id`/`map_comp` coherence of a big presheaf of modules is
never needed. For the same reason no extension-by-zero functor `j_{U!}`, no gluing (Tag 00AK) and
no abelian structure appear.

The bound `max u v w` is forced: the code of `M` lives in
`Code R = ∀ U : Cᵒᵖ, Set (∀ p : Σ W : Cᵒᵖ, (U ⟶ W), ℕ → R.obj p.1)`, whose universe is
`max u v w` since `Cᵒᵖ : Type u`, the morphisms live in `Type v` and the sections in `Type w`.
Note that no local smallness of `SheafOfModules.{w} R` is required: Mathlib's
`ObjectProperty.EssentiallySmall.{w} P` is literally
`∃ Q, ObjectProperty.Small.{w} Q ∧ P ≤ Q.isoClosure`.

*What is chosen.* `ℕ → R.obj W` rather than `Fin n → R.obj W` is the target of `chosenEmbedding`,
so that the target does not depend on the rank occurring in the covering;
`exists_injective_pi_nat` performs the (injective, linear) extension by zero. The encoding is
indexed by `Σ W : Cᵒᵖ, (U ⟶ W)`, i.e. by *all* arrows out of `U` in `Cᵒᵖ`, rather than by a
covering of `U`: a covering depends on `M`, whereas the code of `M` has to be an element of a type
fixed in advance.

`encode` and its lemmas are phrased with `PresheafOfModules.restrictₛₗ`, the bundled semilinear
restriction map, rather than with `M.map`. The two are related by a `rfl`-lemma, but `M.map f s`
has type `(ModuleCat.restrictScalars (R.map f).hom).obj (M.obj Y)` and not `M.obj Y`, so a
statement written with `M.map` is not even well-formed where the result is fed back into `encode`,
and `rw`/`simp` do not match across the two spellings. Accordingly `transfer_naturality` is proved
in the `restrictₛₗ` spelling and then `exact`-ed into the categorical naturality square of
`PresheafOfModules.isoMk`, `exact` being defeq-tolerant.

*Hypotheses on the site.* The results on invertible sheaves of modules go through Tag 0B8N (b),
which needs `HasWeakSheafify J AddCommGrpCat.{w}`, `J.WEqualsLocallyBijective AddCommGrpCat.{w}`
and `(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}` for every object `V`, the tensor
product named by Tag 0B8N (b) being the sheaf one. The Stacks Project assumes these throughout its
chapter on modules on sites.

## References

* [Stacks Project, Tag 040B](https://stacks.math.columbia.edu/tag/040B)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
-/

@[expose] public section

open CategoryTheory Limits Opposite

namespace CategoryTheory.ObjectProperty

universe w v u

/-- A property of objects is essentially small relative to `w` as soon as it has a *complete
invariant* valued in a `w`-small type: a function `κ` on the objects satisfying the property such
that two objects with the same value of `κ` are isomorphic. -/
theorem essentiallySmall_of_invariant {C : Type u} [Category.{v} C] (P : ObjectProperty C)
    {α : Type*} [Small.{w} α] (κ : Subtype P → α)
    (h : ∀ L L' : Subtype P, κ L = κ L' → Nonempty (L.1 ≅ L'.1)) :
    ObjectProperty.EssentiallySmall.{w} P := by
  have hrep : ∀ c : Set.range κ, ∃ L : Subtype P, κ L = c.1 := fun c => c.2
  choose rep hrep using hrep
  refine ⟨⟨fun X => ∃ c, (rep c).1 = X, ?_, fun X hX => ?_⟩⟩
  · exact small_of_surjective
      (f := fun c => (⟨(rep c).1, c, rfl⟩ : Subtype (fun X => ∃ c, (rep c).1 = X)))
      (by rintro ⟨X, c, rfl⟩; exact ⟨c, rfl⟩)
  · have hc : κ ⟨X, hX⟩ ∈ Set.range κ := ⟨⟨X, hX⟩, rfl⟩
    exact ⟨(rep ⟨_, hc⟩).1, ⟨⟨_, hc⟩, rfl⟩, h ⟨X, hX⟩ (rep ⟨_, hc⟩) (hrep ⟨_, hc⟩).symm⟩

end CategoryTheory.ObjectProperty

namespace Stacks.PresheafOfModules

universe v u w

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{w}}

/-- An injective linear map into a finite free module extends, injectively and linearly, to the
free module on `ℕ`. -/
lemma exists_injective_pi_nat {A : Type*} [Semiring A] {M : Type*} [AddCommMonoid M]
    [Module A M] {n : ℕ} (φ : M →ₗ[A] (Fin n → A)) (hφ : Function.Injective φ) :
    ∃ ψ : M →ₗ[A] (ℕ → A), Function.Injective ψ := by
  refine ⟨(LinearMap.pi fun k : ℕ =>
    if h : k < n then LinearMap.proj (⟨k, h⟩ : Fin n) else 0).comp φ, fun x y hxy => ?_⟩
  refine hφ (funext fun j => ?_)
  have h := congrFun hxy j.1
  simpa [LinearMap.pi_apply, j.isLt] using h

/-- For every presheaf of modules `M` and every object `W` there is a linear map
`M.obj W → (ℕ → R.obj W)` which is injective as soon as some injective linear map
`M.obj W → (ℕ → R.obj W)` exists at all. -/
lemma exists_chosenEmbedding (M : PresheafOfModules.{w} R) (W : Cᵒᵖ) :
    ∃ φ : M.obj W →ₗ[R.obj W] (ℕ → R.obj W),
      (∃ ψ : M.obj W →ₗ[R.obj W] (ℕ → R.obj W), Function.Injective ψ) →
        Function.Injective φ := by
  by_cases h : ∃ ψ : M.obj W →ₗ[R.obj W] (ℕ → R.obj W), Function.Injective ψ
  · exact ⟨h.choose, fun _ => h.choose_spec⟩
  · exact ⟨0, fun h' => absurd h' h⟩

/-- The chosen linear map `M.obj W → (ℕ → R.obj W)`, injective whenever an injective one
exists. -/
noncomputable def chosenEmbedding (M : PresheafOfModules.{w} R) (W : Cᵒᵖ) :
    M.obj W →ₗ[R.obj W] (ℕ → R.obj W) :=
  (exists_chosenEmbedding M W).choose

/-- `chosenEmbedding M W` is injective as soon as some injective linear map
`M.obj W → (ℕ → R.obj W)` exists. -/
lemma injective_chosenEmbedding {M : PresheafOfModules.{w} R} {W : Cᵒᵖ}
    (h : ∃ ψ : M.obj W →ₗ[R.obj W] (ℕ → R.obj W), Function.Injective ψ) :
    Function.Injective (chosenEmbedding M W) :=
  (exists_chosenEmbedding M W).choose_spec h

/-- The type of codes of presheaves of modules over `R`: for each object `U` of the site, a set of
families indexed by the arrows out of `U` in `Cᵒᵖ`. -/
abbrev Code (R : Cᵒᵖ ⥤ RingCat.{w}) : Type max u v w :=
  ∀ U : Cᵒᵖ, Set (∀ p : Σ W : Cᵒᵖ, (U ⟶ W), ℕ → R.obj p.1)

/-- The encoding map on sections: a section `s` over `U` is sent to the family of its chosen
embeddings after restriction along each arrow out of `U`. -/
noncomputable def encode (M : PresheafOfModules.{w} R) (U : Cᵒᵖ) (s : M.obj U) :
    ∀ p : Σ W : Cᵒᵖ, (U ⟶ W), ℕ → R.obj p.1 :=
  fun p => chosenEmbedding M p.1 (M.restrictₛₗ p.2 s)

/-- The value of `encode M U s` at an arrow `p : U ⟶ W` is the chosen embedding at `W` of the
restriction of `s` along `p`. -/
lemma encode_apply (M : PresheafOfModules.{w} R) (U : Cᵒᵖ) (s : M.obj U)
    (p : Σ W : Cᵒᵖ, (U ⟶ W)) :
    encode M U s p = chosenEmbedding M p.1 (M.restrictₛₗ p.2 s) := rfl

/-- The code of a presheaf of modules: the family of the ranges of its encoding maps. -/
noncomputable def code (M : PresheafOfModules.{w} R) : Code R :=
  fun U => Set.range (encode M U)

/-- The code of `M` at `U` is the range of `encode M U`. -/
lemma code_apply (M : PresheafOfModules.{w} R) (U : Cᵒᵖ) :
    code M U = Set.range (encode M U) := rfl

/-- The encoding map is additive. -/
lemma encode_add (M : PresheafOfModules.{w} R) (U : Cᵒᵖ) (s t : M.obj U)
    (p : Σ W : Cᵒᵖ, (U ⟶ W)) :
    encode M U (s + t) p = encode M U s p + encode M U t p := by
  simp only [encode_apply, map_add]

/-- The encoding map is semilinear: at an arrow `p : U ⟶ W` the scalar `r` acts through
`R.map p`. -/
lemma encode_smul (M : PresheafOfModules.{w} R) (U : Cᵒᵖ) (r : R.obj U) (s : M.obj U)
    (p : Σ W : Cᵒᵖ, (U ⟶ W)) :
    encode M U (r • s) p = (R.map p.2).hom r • encode M U s p := by
  simp only [encode_apply, map_smulₛₗ, RingHom.id_apply]

/-- Naturality of the encoding: encoding the restriction of a section along `g` is reindexing its
encoding along `g`. -/
lemma encode_restrictₛₗ (M : PresheafOfModules.{w} R) {U U' : Cᵒᵖ} (g : U ⟶ U') (s : M.obj U)
    (q : Σ W : Cᵒᵖ, (U' ⟶ W)) :
    encode M U' (M.restrictₛₗ g s) q = encode M U s ⟨q.1, g ≫ q.2⟩ := by
  have h : M.restrictₛₗ q.2 (M.restrictₛₗ g s) = M.restrictₛₗ (g ≫ q.2) s :=
    (M.map_comp_apply g q.2 s).symm
  rw [encode_apply, encode_apply, h]

section Injective

variable {J : GrothendieckTopology C}

/-- If `M` is separated and every object of the site has a covering sieve all of whose arrows
factor through an object at which `chosenEmbedding M` is injective, then `encode M U` is injective
for every `U`. -/
theorem injective_encode (M : PresheafOfModules.{w} R)
    (hM : Presheaf.IsSeparated J M.presheaf)
    (hcov : ∀ X : C, ∃ S : Sieve X, S ∈ J X ∧ ∀ ⦃Y : C⦄ (g : Y ⟶ X), S g →
      ∃ (Z : C) (a : Y ⟶ Z) (b : Z ⟶ X), a ≫ b = g ∧
        Function.Injective (chosenEmbedding M (op Z)))
    (U : Cᵒᵖ) : Function.Injective (encode M U) := by
  intro s t hst
  obtain ⟨S, hS, hfac⟩ := hcov U.unop
  refine hM U.unop S hS s t fun Y g hg => ?_
  obtain ⟨Z, a, b, hab, hZ⟩ := hfac g hg
  have hb := congrFun hst ⟨op Z, b.op⟩
  rw [encode_apply, encode_apply] at hb
  have hb' : M.map b.op s = M.map b.op t := hZ hb
  subst hab
  exact (M.map_comp_apply b.op a.op s).trans
    ((congrArg (fun z : M.obj (op Z) => M.map a.op z) hb').trans
      (M.map_comp_apply b.op a.op t).symm)

end Injective

section Transfer

variable {M₁ M₂ : PresheafOfModules.{w} R} (hcode : code M₁ = code M₂)

include hcode

/-- If `M₁` and `M₂` have the same code, every section of `M₁` over `U` has the same encoding as
some section of `M₂` over `U`. -/
lemma exists_encode_eq (U : Cᵒᵖ) (s : M₁.obj U) :
    ∃ t : M₂.obj U, encode M₂ U t = encode M₁ U s := by
  have h : encode M₁ U s ∈ code M₂ U := by
    rw [← congrFun hcode U, code_apply]
    exact Set.mem_range_self s
  rw [code_apply] at h
  exact h

/-- The comparison map on sections between two presheaves of modules with the same code: the
section of `M₂` with the same encoding as the given section of `M₁`. -/
noncomputable def transfer (U : Cᵒᵖ) (s : M₁.obj U) : M₂.obj U :=
  (exists_encode_eq hcode U s).choose

/-- `transfer hcode U s` has the same encoding as `s`. -/
lemma encode_transfer (U : Cᵒᵖ) (s : M₁.obj U) :
    encode M₂ U (transfer hcode U s) = encode M₁ U s :=
  (exists_encode_eq hcode U s).choose_spec

variable (h₁ : ∀ U, Function.Injective (encode M₁ U))
  (h₂ : ∀ U, Function.Injective (encode M₂ U))

include h₂ in
/-- If the encoding maps of `M₂` are injective, `transfer` is additive. -/
lemma transfer_add (U : Cᵒᵖ) (s t : M₁.obj U) :
    transfer hcode U (s + t) = transfer hcode U s + transfer hcode U t :=
  h₂ U (funext fun _ => by simp only [encode_transfer, encode_add])

include h₂ in
/-- If the encoding maps of `M₂` are injective, `transfer` commutes with scalar
multiplication. -/
lemma transfer_smul (U : Cᵒᵖ) (r : R.obj U) (s : M₁.obj U) :
    transfer hcode U (r • s) = r • transfer hcode U s :=
  h₂ U (funext fun _ => by simp only [encode_transfer, encode_smul])

include h₂ in
/-- The comparison map on sections, as a linear map. -/
noncomputable def transferLinearMap (U : Cᵒᵖ) : M₁.obj U →ₗ[R.obj U] M₂.obj U where
  toFun := transfer hcode U
  map_add' := transfer_add hcode h₂ U
  map_smul' r s := transfer_smul hcode h₂ U r s

include h₁ in
/-- If the encoding maps of `M₁` are injective, `transfer hcode U` is injective. -/
lemma injective_transfer (U : Cᵒᵖ) : Function.Injective (transfer hcode U) := by
  intro s s' h
  refine h₁ U ?_
  rw [← encode_transfer hcode U s, ← encode_transfer hcode U s', h]

include h₂ in
/-- If the encoding maps of `M₂` are injective, `transfer hcode U` is surjective. -/
lemma surjective_transfer (U : Cᵒᵖ) : Function.Surjective (transfer hcode U) := by
  intro t
  obtain ⟨s, hs⟩ := exists_encode_eq hcode.symm U t
  exact ⟨s, h₂ U (by rw [encode_transfer, hs])⟩

include h₁ h₂ in
/-- The comparison equivalence on sections, between two presheaves of modules with injective
encodings and the same code. -/
noncomputable def transferLinearEquiv (U : Cᵒᵖ) : M₁.obj U ≃ₗ[R.obj U] M₂.obj U :=
  LinearEquiv.ofBijective (transferLinearMap hcode h₂ U)
    ⟨injective_transfer hcode h₁ U, surjective_transfer hcode h₂ U⟩

include h₂ in
/-- The comparison maps on sections are natural. -/
lemma transfer_naturality {U U' : Cᵒᵖ} (f : U ⟶ U') (s : M₁.obj U) :
    transfer hcode U' (M₁.restrictₛₗ f s) = M₂.restrictₛₗ f (transfer hcode U s) :=
  h₂ U' (funext fun _ => by simp only [encode_transfer, encode_restrictₛₗ])

include h₁ h₂ in
/-- Two presheaves of modules with injective encodings and the same code are isomorphic: the
comparison maps on sections are bijective and natural. -/
noncomputable def isoOfCodeEq : M₁ ≅ M₂ :=
  PresheafOfModules.isoMk
    (fun U =>
      { hom := ModuleCat.ofHom (transferLinearEquiv hcode h₁ h₂ U).toLinearMap
        inv := ModuleCat.ofHom (transferLinearEquiv hcode h₁ h₂ U).symm.toLinearMap
        hom_inv_id := by
          ext x
          exact (transferLinearEquiv hcode h₁ h₂ U).symm_apply_apply x
        inv_hom_id := by
          ext x
          exact (transferLinearEquiv hcode h₁ h₂ U).apply_symm_apply x })
    (by
      intro U U' f
      ext x
      exact transfer_naturality hcode h₂ f x)

end Transfer

end Stacks.PresheafOfModules

namespace Stacks.SheafOfModules

universe v u w

open Stacks.PresheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ V : C, (J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- The encoding map of an invertible sheaf of modules is injective at every object: the covering
of Tag 0B8N (b) supplies the objects at which the chosen embedding is injective, and separatedness
turns that into injectivity over every object. -/
theorem injective_encode_of_isInvertible
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
      [IsInvertible O hO L] (U : Cᵒᵖ) :
    Function.Injective (encode L.val U) := by
  refine injective_encode L.val L.isSheaf.isSeparated (fun X => ?_) U
  obtain ⟨I, V, f, hJ, hinj⟩ := exists_cover_injective_finFree hO L X
  refine ⟨Sieve.generate (Presieve.ofArrows V f), hJ, ?_⟩
  rintro Y g ⟨Z, a, b, ⟨i⟩, hab⟩
  obtain ⟨n, φ, hφ⟩ := hinj i
  exact ⟨V i, a, f i, hab, injective_chosenEmbedding (exists_injective_pi_nat φ hφ)⟩

/-- Two invertible sheaves of modules with the same code are isomorphic. -/
noncomputable def isoOfCodeEq
    (hO : Presheaf.IsSheaf J (Stacks.SheafOfModules.TensorSheafification.structureRingPresheaf O))
    (L₁ L₂ : SheafOfModules.{w} (Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L₁] [IsInvertible O hO L₂] (h : code L₁.val = code L₂.val) :
    L₁ ≅ L₂ :=
  (SheafOfModules.fullyFaithfulForget _).preimageIso
    (Stacks.PresheafOfModules.isoOfCodeEq h
      (injective_encode_of_isInvertible hO L₁) (injective_encode_of_isInvertible hO L₂))

end Stacks.SheafOfModules
