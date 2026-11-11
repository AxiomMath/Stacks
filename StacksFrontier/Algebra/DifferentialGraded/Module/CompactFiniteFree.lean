module

public import StacksFrontier.Algebra.DifferentialGraded.Module.CompactFiniteCellFiltration
public import StacksFrontier.Algebra.DifferentialGraded.Module.CompactFiniteProjective
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryHom
public import StacksFrontier.Algebra.DifferentialGraded.Module.LeftOrthogonalAcyclic
public import StacksCore.Tactic.StacksAttribute

/-!
# Compact objects are direct summands of finite free models

Let `(A, d)` be a differential graded algebra over a commutative ring `R`. [Stacks, Tag 09RB]
asserts that, when `A` lives in only finitely many degrees, a compact object `E` of `D(A, d)` can
be *represented by* a differential graded `A`-module `P` which is *finite projective* as a graded
`A`-module and satisfies `Hom_{K(A, d)}(P, M) = Hom_{D(A, d)}(P, M)` for every differential graded
`A`-module `M`. That implication, (1) ⟹ (2) of the tag, is **false**: it is contradicted by the
source's own [Stacks, Tag 09R5], and the refutation is machine-checked in
`StacksFrontier/Examples/Algebra/CompactObjectNoFiniteProjectiveModel.lean`.

This file proves the statement the source's proof does establish, unconditionally, and registers the
tag on the resulting corrected equivalence: a compact object is a **direct summand** in `D(A, d)` of
the image of a differential graded `A`-module `P` which is **finite free** as a graded `A`-module
and satisfies the condition of [Stacks, Tag 09R0]. The two differences from the literal statement —
direct summand rather than representative, finite free rather than finite projective — are exactly
what the argument of [Stacks, Tag 09R3] delivers, and the counterexample is consistent with them:
its compact object `Ker(x)` is a direct summand of the regular module, which is finite free.

## Errata: Tag 09RB's implication (1) ⟹ (2)

The literal implication (1) ⟹ (2) of [Stacks, Tag 09RB] is **a mistake in the Stacks Project,
pending review**, and it is **contradicted by the source's own [Stacks, Tag 09R5]**. A reader who
arrives at `DifferentialGradedModule.exists_retract_isFiniteFreeAsGradedModule_of_isCompactObject`
below and wonders why it is weaker than the sentence the tag states is seeing the consequence of
that: the tag's sentence is false, and what is registered is the statement the source's own proof
establishes.

*What 09RB says.* Let `(A, d)` be a differential graded algebra with `A^n = 0` for `|n| ≫ 0` and
let `E` be an object of `D(A, d)`. The tag asserts the equivalence of (1) `E` is a compact object,
and (2) `E` can be represented by a differential graded `A`-module `P` which is finite projective
as a graded `A`-module and satisfies `Hom_{K(A, d)}(P, M) = Hom_{D(A, d)}(P, M)` for every
differential graded `A`-module `M`.

*What refutes the literal reading.* The algebra of [Stacks, Tag 09R4] is `A = k[x, y]/(y²)` over a
field `k` of characteristic `2` — here `k = ZMod 2` — with `x` of degree `0`, `y` of degree `-1`,
`d x = 0` and `d y = x² + x`. It is concentrated in degrees `0` and `-1`, so it satisfies 09RB's
boundedness hypothesis with `c = 2`, and its compact object `Ker(x)` has no finite
graded-projective model at all; that is [Stacks, Tag 09R5]. Over that algebra, 09RB's (1) ⟹ (2)
asserts precisely the model 09R5 denies. The machine-checked refutation is
`Stacks.Examples.not_forall_exists_finite_gradedProjective_of_isCompactObject`
(`StacksFrontier/Examples/Algebra/CompactObjectNoFiniteProjectiveModel.lean`), whose
compactness hypothesis is `IsCompactObject.{w}` for a universe `w` that is a parameter of the
theorem, together with the universe-free variant
`Stacks.Examples.not_forall_exists_finite_gradedProjective_of_retract_regularModule` (same file),
whose hypothesis is that `E` is a retract of the image of the regular module and
so implies compactness under every reading of the word.

*What is actually true.* The equivalence is restored once condition (2) is read as the source's own
proof delivers it — a *direct summand* in `D(A, d)` of the image of a module which is *finite free*
as a graded module and satisfies `Hom_K = Hom_D` — and in that form it is closed in both
directions in this file:

* (1) ⟹ (2), corrected:
  `DifferentialGradedModule.exists_retract_isFiniteFreeAsGradedModule_of_isCompactObject`
  (this file), with no boundedness hypothesis of any kind;
* (2) ⟹ (1), corrected:
  `DifferentialGradedModule.isCompactObject_of_retract_isFiniteFreeAsGradedModule` (this file);
* the equivalence, corrected:
  `DifferentialGradedModule.isCompactObject_tfae_exists_retract`
  (this file), which carries the registration of the tag; its third condition is the source's
  condition (2) with "represented by" corrected to "a direct summand of".

The source's own spelling of (2) ⟹ (1) — with finite projective, and a representative rather than
a summand — is true as it stands, and is proved separately at
`DifferentialGradedModule.isCompactObject_of_exists_finite_projective_representative`
(`StacksFrontier/Algebra/DifferentialGraded/Module/CompactFiniteProjective.lean`), without a tag.

*Where the source's error must lie.* The corrected form is what 09RB's proof has in hand once it
has applied Proposition 22.36.4 ([Stacks, Tag 09R3]) and Lemma 22.22.3: `E` is a direct summand of
a `P` with a finite cell filtration, and that `P` computes its derived morphisms. The source does
not stop there — it goes on to build, by a cone construction, a finite graded free `P` representing
`E ⊕ E[n]`, and then to split `0 → P₁ ∩ P₂ → P₁ ⊕ P₂ → P → 0` so as to cut `E` out of `P` as an
honest representative. It is that remainder, which is *not* formalized here, that the
counterexample shows cannot be right.

*Registration.* The tag is registered once, on the corrected equivalence
`DifferentialGradedModule.isCompactObject_tfae_exists_retract`, with
the departure from the source's sentence written into the attribute's note string. No attribute
anywhere in the library claims the literal (1) ⟹ (2).

The engine is [Stacks, Tag 09R3],
`DifferentialGradedModule.isCompactObject_iff_exists_retract_hasFiniteCellFiltration`: a compact
object is a retract of the image of a module `P` with a finite cell filtration. Two properties of
such a `P` are proved here. It is finite free as a graded module: the filtration starts at zero,
each of its finitely many steps is an admissible monomorphism whose quotient is a finite direct
sum of shifts of the algebra, and a graded splitting of such a step adds the generators of the
quotient to those of the stage below. And it computes its derived morphisms: each step being
admissible with a quotient orthogonal on the left to the acyclic modules, `P` is orthogonal on
the left to them, and morphisms out of a left-orthogonal object are not changed by localization
([Stacks, Tag 09KY]).

## Main definitions

* `DifferentialGradedModule.IsFiniteFreeAsGradedModule`: the underlying graded right `A`-module is
  isomorphic to a finite direct sum of shifts of the algebra.

## Main results

* `DifferentialGradedModule.isFiniteFreeAsGradedModule_of_hasFiniteCellFiltration`: a module with
  a finite cell filtration is finite free as a graded module.
* `DifferentialGradedModule.leftOrthogonal_acyclic_of_hasFiniteCellFiltration` and
  `DifferentialGradedModule.bijective_q_map_of_hasFiniteCellFiltration`: such a module is
  orthogonal on the left to the acyclic modules, hence satisfies the condition of
  [Stacks, Tag 09R0].
* `DifferentialGradedModule.isFinite_of_isFiniteFreeAsGradedModule`: a module finite free as a
  graded module is finitely generated as a right `A`-module.
* `DifferentialGradedModule.exists_retract_isFiniteFreeAsGradedModule_of_isCompactObject`:
  the implication (1) ⟹ (2) of [Stacks, Tag 09RB] in its corrected form.
* `DifferentialGradedModule.isCompactObject_of_retract_isFiniteFreeAsGradedModule`: the converse.
* `DifferentialGradedModule.isCompactObject_iff_exists_retract_isFiniteFreeAsGradedModule`: the
  equivalence of the two.
* `DifferentialGradedModule.isProjectiveAsGradedModule_of_isFiniteFreeAsGradedModule`: a module
  finite free as a graded module is projective as a graded module ([Stacks, Tag 09K0]).
* `DifferentialGradedModule.isCompactObject_tfae_exists_retract`: **[Stacks, Tag 09RB],
  corrected**: compact objects are the direct summands of finite free, equivalently of finite
  graded-projective, modules computing their derived morphisms.

## Implementation notes

*What "finite free as a graded module" says.* A map of graded modules is a
`DifferentialGradedModule.GradedHom`: degree-preserving and right `A`-linear, with no
compatibility with the differentials. Finite freeness is a pair of mutually inverse such maps
between `P` and `∐_{j ∈ J} A[k_j]` with `J` finite — equivalently, a basis of `P` as a right
`A`-module consisting of finitely many homogeneous elements, of degrees `-k_j`. The differentials
are deliberately absent: the filtration of a cell-filtered module splits only after they are
forgotten, which is the whole content of admissibility ([Stacks, Tag 09JT]).

*Why the splitting has to be corrected.* An admissible short exact sequence `K ⟶ L ⟶ M` carries a
graded retraction `π` of the first map and a graded section `s` of the second, but nothing forces
`π ∘ s = 0`, and without that the four maps do not exhibit `L` as `K ⊕ M`. Replacing `π` by
`π ∘ (1 - s ∘ g)` makes all four identities hold on the nose, which is
`DifferentialGradedModule.exists_gradedSplitting`.

*No boundedness.* The boundedness hypothesis of the source, "`A^n = 0` for `|n| ≫ 0`", is not
assumed and is not used: Tag 09R3 does not need it, the graded splitting does not need it, and
neither does the orthogonality. That is part of why the literal statement of (1) ⟹ (2) cannot be
rescued by it — its counterexample satisfies it.

*Universes.* Single-universe, as in the rest of this chapter's differential graded interface
(Tag 09JJ): the base ring, the algebra and the modules live in one universe `u`, the index type of
a direct sum is in `Type u`, and compactness is `IsCompactObject.{u}`, tested against the direct
sums that `D(A, d)` has.

## References

* [Stacks Project, Tag 09RB](https://stacks.math.columbia.edu/tag/09RB), whose implication
  (1) ⟹ (2) is corrected here and refuted, in its literal form, in
  `StacksFrontier/Examples/Algebra/CompactObjectNoFiniteProjectiveModel.lean`.
* [Stacks Project, Tag 09R3](https://stacks.math.columbia.edu/tag/09R3), the compact objects as
  the retracts of the cell-filtered modules.
* [Stacks Project, Tag 09R5](https://stacks.math.columbia.edu/tag/09R5), the compact object with
  no finite graded-projective model.
* [Stacks Project, Tag 09R0](https://stacks.math.columbia.edu/tag/09R0), the modules whose
  homotopy morphisms compute their derived morphisms.
* [Stacks Project, Tag 09KY](https://stacks.math.columbia.edu/tag/09KY), morphisms out of a
  left-orthogonal object.
* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT), admissible short exact
  sequences and their graded splittings.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-! ### Maps of graded modules -/

/-- The composite of two maps of graded right `A`-modules. -/
private def gradedComp {X Y Z : DifferentialGradedModule.{u, u, u} A}
    (f : GradedHom X Y) (g : GradedHom Y Z) : GradedHom X Z where
  toFun := g.toFun.comp f.toFun
  map_smul x a := by simp only [LinearMap.comp_apply, f.map_smul, g.map_smul]
  map_grading n x hx := g.map_grading n _ (f.map_grading n x hx)

/-- The identity map of graded right `A`-modules. -/
private def gradedId (X : DifferentialGradedModule.{u, u, u} A) : GradedHom X X where
  toFun := LinearMap.id
  map_smul _ _ := rfl
  map_grading _ _ hx := hx

/-- The zero map of graded right `A`-modules. -/
private def gradedZero (X Y : DifferentialGradedModule.{u, u, u} A) : GradedHom X Y where
  toFun := 0
  map_smul _ _ := (smul_zero _).symm
  map_grading n _ _ := (Y.grading n).zero_mem

/-- Every element of a zero differential graded module vanishes. -/
private theorem eq_zero_of_isZero {M : DifferentialGradedModule.{u, u, u} A} (hM : IsZero M)
    (x : M.M) : x = 0 := by
  have h : (𝟙 M : M ⟶ M) = 0 := hM.eq_of_src _ _
  calc x = (𝟙 M : M ⟶ M).toFun x := rfl
    _ = (0 : M ⟶ M).toFun x := by rw [h]
    _ = 0 := by rw [Hom.hom_zero_toFun]; rfl

/-- A direct sum over an empty index type is a zero object. -/
private theorem isZero_coproduct_of_isEmpty {J : Type u} [IsEmpty J]
    (G : J → DifferentialGradedModule.{u, u, u} A) : IsZero (∐ G) :=
  (IsZero.iff_id_eq_zero _).mpr (Sigma.hom_ext _ _ fun i => isEmptyElim i)

/-- The composite of the two maps of an admissible short exact sequence vanishes elementwise. -/
private theorem toFun_comp_eq_zero {K L M : DifferentialGradedModule.{u, u, u} A}
    (f : K ⟶ L) (g : L ⟶ M) (h : IsAdmissibleShortExact f g) (x : K.M) :
    g.toFun (f.toFun x) = 0 := by
  have hmem : f.toFun x ∈ LinearMap.ker g.toFun := by
    rw [← h.exact]; exact ⟨x, rfl⟩
  exact hmem

/-- **The graded splitting carried by an admissible short exact sequence.** The retraction is
corrected by the section, `π' = π ∘ (1 - s ∘ g)`, so that the four identities of a splitting hold
on the nose: `π' ∘ f = 1`, `g ∘ s = 1`, `π' ∘ s = 0` and `f ∘ π' + s ∘ g = 1`. -/
private theorem exists_gradedSplitting {K L M : DifferentialGradedModule.{u, u, u} A}
    (f : K ⟶ L) (g : L ⟶ M) (h : IsAdmissibleShortExact f g) :
    ∃ (π : GradedHom L K) (s : GradedHom M L),
      (∀ x, π.toFun (f.toFun x) = x) ∧ (∀ z, g.toFun (s.toFun z) = z) ∧
        (∀ z, π.toFun (s.toFun z) = 0) ∧
          ∀ y, f.toFun (π.toFun y) + s.toFun (g.toFun y) = y := by
  obtain ⟨π₀, hπ₀⟩ := h.admissibleMono
  obtain ⟨s, hs⟩ := h.admissibleEpi
  have hgf := toFun_comp_eq_zero f g h
  refine ⟨{ toFun := π₀.toFun.comp (LinearMap.id - s.toFun.comp g.toFun)
            map_smul := fun y a => ?_
            map_grading := fun n y hy => ?_ }, s, fun x => ?_, hs, fun z => ?_, fun y => ?_⟩
  · simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, g.map_smul,
      s.map_smul, ← smul_sub, π₀.map_smul]
  · refine π₀.map_grading n _ (Submodule.sub_mem _ hy ?_)
    exact s.map_grading n _ (g.map_grading n y hy)
  · change π₀.toFun (f.toFun x - s.toFun (g.toFun (f.toFun x))) = x
    rw [hgf x, map_zero, sub_zero, hπ₀]
  · change π₀.toFun (s.toFun z - s.toFun (g.toFun (s.toFun z))) = 0
    rw [hs z, sub_self, map_zero]
  · obtain ⟨w, hw⟩ : y - s.toFun (g.toFun y) ∈ LinearMap.range f.toFun := by
      rw [h.exact]
      change g.toFun (y - s.toFun (g.toFun y)) = 0
      rw [map_sub, hs (g.toFun y), sub_self]
    have hπ : π₀.toFun (y - s.toFun (g.toFun y)) = w := by rw [← hw, hπ₀]
    change f.toFun (π₀.toFun (y - s.toFun (g.toFun y))) + s.toFun (g.toFun y) = y
    rw [hπ, hw, sub_add_cancel]

/-! ### Modules which are finite free as graded modules -/

/-- A differential graded `A`-module `P` is **finite free as a graded `A`-module** when its
underlying graded right `A`-module is isomorphic to a finite direct sum `⨁_{j ∈ J} A[k_j]` of
shifts of the algebra: the two maps of the isomorphism are maps of *graded* modules
(`DifferentialGradedModule.GradedHom`, degree-preserving and right `A`-linear), with no
compatibility with the differentials, which is what "free as a graded module on finitely many
homogeneous generators" means. -/
def IsFiniteFreeAsGradedModule (P : DifferentialGradedModule.{u, u, u} A) : Prop :=
  ∃ (J : Type u) (_ : Finite J) (k : J → ℤ)
    (φ : GradedHom P (∐ fun j => shift (regularModule A) (k j)))
    (ψ : GradedHom (∐ fun j => shift (regularModule A) (k j)) P),
    (∀ x, ψ.toFun (φ.toFun x) = x) ∧ ∀ y, φ.toFun (ψ.toFun y) = y

/-- Being finite free as a graded module transfers along an isomorphism of differential graded
modules. -/
theorem IsFiniteFreeAsGradedModule.of_iso {M N : DifferentialGradedModule.{u, u, u} A} (e : M ≅ N)
    (h : IsFiniteFreeAsGradedModule M) : IsFiniteFreeAsGradedModule N := by
  obtain ⟨J, hJ, k, φ, ψ, hψφ, hφψ⟩ := h
  refine ⟨J, hJ, k, gradedComp e.inv.toGradedHom φ, gradedComp ψ e.hom.toGradedHom,
    fun x => ?_, fun y => ?_⟩
  · change e.hom.toFun (ψ.toFun (φ.toFun (e.inv.toFun x))) = x
    rw [hψφ, ← Hom.comp_toFun_apply e.inv e.hom x, e.inv_hom_id]
    rfl
  · change φ.toFun (e.inv.toFun (e.hom.toFun (ψ.toFun y))) = y
    rw [← Hom.comp_toFun_apply e.hom e.inv (ψ.toFun y), e.hom_inv_id]
    exact hφψ y

/-- A finite direct sum of shifts of the algebra is finite free as a graded module. -/
theorem isFiniteFreeAsGradedModule_coproduct_shifts {J : Type u} [Finite J] (k : J → ℤ) :
    IsFiniteFreeAsGradedModule (∐ fun j => shift (regularModule A) (k j)) :=
  ⟨J, inferInstance, k, gradedId _, gradedId _, fun _ => rfl, fun _ => rfl⟩

/-- A zero differential graded module is finite free as a graded module, on no generators. -/
theorem isFiniteFreeAsGradedModule_of_isZero {M : DifferentialGradedModule.{u, u, u} A}
    (hM : IsZero M) : IsFiniteFreeAsGradedModule M := by
  refine ⟨PEmpty.{u + 1}, inferInstance, fun _ => 0, gradedZero _ _, gradedZero _ _,
    fun x => ?_, fun y => ?_⟩
  · change (0 : M.M) = x
    exact (eq_zero_of_isZero hM x).symm
  · change (0 : (∐ fun _ : PEmpty.{u + 1} => shift (regularModule A) (0 : ℤ)).M) = y
    exact (eq_zero_of_isZero (isZero_coproduct_of_isEmpty _) y).symm

/-! ### Extensions -/

/-- The inclusion of the first half of a direct sum indexed by a sum type. -/
private def coproductInl {J₁ J₂ : Type u} (k₁ : J₁ → ℤ) (k₂ : J₂ → ℤ) :
    (∐ fun j => shift (regularModule A) (k₁ j)) ⟶
      ∐ fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t) :=
  Sigma.desc fun j =>
    Sigma.ι (fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t)) (Sum.inl j)

/-- The inclusion of the second half of a direct sum indexed by a sum type. -/
private def coproductInr {J₁ J₂ : Type u} (k₁ : J₁ → ℤ) (k₂ : J₂ → ℤ) :
    (∐ fun j => shift (regularModule A) (k₂ j)) ⟶
      ∐ fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t) :=
  Sigma.desc fun j =>
    Sigma.ι (fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t)) (Sum.inr j)

private theorem coproductInl_ι {J₁ J₂ : Type u} (k₁ : J₁ → ℤ) (k₂ : J₂ → ℤ) (j : J₁)
    (x : (shift (regularModule A) (k₁ j)).M) :
    (coproductInl k₁ k₂).toFun
        ((Sigma.ι (fun j => shift (regularModule A) (k₁ j)) j).toFun x) =
      (Sigma.ι (fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t))
        (Sum.inl j)).toFun x := by
  have hdesc : Sigma.ι (fun j => shift (regularModule A) (k₁ j)) j ≫ coproductInl k₁ k₂ =
      Sigma.ι (fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t)) (Sum.inl j) :=
    Sigma.ι_desc _ _
  rw [← Hom.comp_toFun_apply, hdesc]

private theorem coproductInr_ι {J₁ J₂ : Type u} (k₁ : J₁ → ℤ) (k₂ : J₂ → ℤ) (j : J₂)
    (x : (shift (regularModule A) (k₂ j)).M) :
    (coproductInr k₁ k₂).toFun
        ((Sigma.ι (fun j => shift (regularModule A) (k₂ j)) j).toFun x) =
      (Sigma.ι (fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t))
        (Sum.inr j)).toFun x := by
  have hdesc : Sigma.ι (fun j => shift (regularModule A) (k₂ j)) j ≫ coproductInr k₁ k₂ =
      Sigma.ι (fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t)) (Sum.inr j) :=
    Sigma.ι_desc _ _
  rw [← Hom.comp_toFun_apply, hdesc]

/-- The map into a direct sum indexed by a sum type attached to a pair of maps of graded modules
into the two halves. -/
private def coproductSumLift {L : DifferentialGradedModule.{u, u, u} A} {J₁ J₂ : Type u}
    (k₁ : J₁ → ℤ) (k₂ : J₂ → ℤ)
    (α : GradedHom L (∐ fun j => shift (regularModule A) (k₁ j)))
    (β : GradedHom L (∐ fun j => shift (regularModule A) (k₂ j))) :
    GradedHom L (∐ fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t)) where
  toFun := (coproductInl k₁ k₂).toFun.comp α.toFun + (coproductInr k₁ k₂).toFun.comp β.toFun
  map_smul y a := by
    simp only [LinearMap.add_apply, LinearMap.comp_apply, α.map_smul, β.map_smul,
      (coproductInl k₁ k₂).map_smul, (coproductInr k₁ k₂).map_smul, smul_add]
  map_grading n y hy :=
    Submodule.add_mem _ ((coproductInl k₁ k₂).map_grading n _ (α.map_grading n y hy))
      ((coproductInr k₁ k₂).map_grading n _ (β.map_grading n y hy))

/-- The summandwise components of the map out of a direct sum indexed by a sum type attached to a
pair of maps of graded modules out of the two halves: on a summand of the first half, the
coprojection into that half followed by the first map, and symmetrically. -/
private def coproductSumComponent {L : DifferentialGradedModule.{u, u, u} A} {J₁ J₂ : Type u}
    (k₁ : J₁ → ℤ) (k₂ : J₂ → ℤ)
    (a : GradedHom (∐ fun j => shift (regularModule A) (k₁ j)) L)
    (b : GradedHom (∐ fun j => shift (regularModule A) (k₂ j)) L) :
    ∀ t : J₁ ⊕ J₂, GradedHom (shift (regularModule A) (Sum.elim k₁ k₂ t)) L
  | Sum.inl j => gradedComp (Sigma.ι (fun j => shift (regularModule A) (k₁ j)) j).toGradedHom a
  | Sum.inr j => gradedComp (Sigma.ι (fun j => shift (regularModule A) (k₂ j)) j).toGradedHom b

/-- The map out of a direct sum indexed by a sum type attached to a pair of maps of graded
modules out of the two halves. -/
private def coproductSumDesc {L : DifferentialGradedModule.{u, u, u} A} {J₁ J₂ : Type u}
    (k₁ : J₁ → ℤ) (k₂ : J₂ → ℤ)
    (a : GradedHom (∐ fun j => shift (regularModule A) (k₁ j)) L)
    (b : GradedHom (∐ fun j => shift (regularModule A) (k₂ j)) L) :
    GradedHom (∐ fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t)) L :=
  gradedCoproductDesc _ (coproductSumComponent k₁ k₂ a b)

private theorem coproductSumDesc_ι_inl {L : DifferentialGradedModule.{u, u, u} A}
    {J₁ J₂ : Type u} (k₁ : J₁ → ℤ) (k₂ : J₂ → ℤ)
    (a : GradedHom (∐ fun j => shift (regularModule A) (k₁ j)) L)
    (b : GradedHom (∐ fun j => shift (regularModule A) (k₂ j)) L) (j : J₁)
    (x : (shift (regularModule A) (k₁ j)).M) :
    (coproductSumDesc k₁ k₂ a b).toFun
        ((Sigma.ι (fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t))
          (Sum.inl j)).toFun x) =
      a.toFun ((Sigma.ι (fun j => shift (regularModule A) (k₁ j)) j).toFun x) :=
  gradedCoproductDesc_ι _ (coproductSumComponent k₁ k₂ a b) (Sum.inl j) x

private theorem coproductSumDesc_ι_inr {L : DifferentialGradedModule.{u, u, u} A}
    {J₁ J₂ : Type u} (k₁ : J₁ → ℤ) (k₂ : J₂ → ℤ)
    (a : GradedHom (∐ fun j => shift (regularModule A) (k₁ j)) L)
    (b : GradedHom (∐ fun j => shift (regularModule A) (k₂ j)) L) (j : J₂)
    (x : (shift (regularModule A) (k₂ j)).M) :
    (coproductSumDesc k₁ k₂ a b).toFun
        ((Sigma.ι (fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t))
          (Sum.inr j)).toFun x) =
      b.toFun ((Sigma.ι (fun j => shift (regularModule A) (k₂ j)) j).toFun x) :=
  gradedCoproductDesc_ι _ (coproductSumComponent k₁ k₂ a b) (Sum.inr j) x

/-- The descent along a sum type restricted to the first half is the first of the two maps. -/
private theorem coproductSumDesc_inl {L : DifferentialGradedModule.{u, u, u} A}
    {J₁ J₂ : Type u} (k₁ : J₁ → ℤ) (k₂ : J₂ → ℤ)
    (a : GradedHom (∐ fun j => shift (regularModule A) (k₁ j)) L)
    (b : GradedHom (∐ fun j => shift (regularModule A) (k₂ j)) L)
    (x : (∐ fun j => shift (regularModule A) (k₁ j)).M) :
    (coproductSumDesc k₁ k₂ a b).toFun ((coproductInl k₁ k₂).toFun x) = a.toFun x :=
  LinearMap.congr_fun (coproduct_linearMap_ext (fun j => shift (regularModule A) (k₁ j))
    (f := (coproductSumDesc k₁ k₂ a b).toFun.comp (coproductInl k₁ k₂).toFun) (g := a.toFun)
    fun j y => by
      simp only [LinearMap.comp_apply]
      rw [coproductInl_ι, coproductSumDesc_ι_inl]) x

/-- The descent along a sum type restricted to the second half is the second of the two maps. -/
private theorem coproductSumDesc_inr {L : DifferentialGradedModule.{u, u, u} A}
    {J₁ J₂ : Type u} (k₁ : J₁ → ℤ) (k₂ : J₂ → ℤ)
    (a : GradedHom (∐ fun j => shift (regularModule A) (k₁ j)) L)
    (b : GradedHom (∐ fun j => shift (regularModule A) (k₂ j)) L)
    (x : (∐ fun j => shift (regularModule A) (k₂ j)).M) :
    (coproductSumDesc k₁ k₂ a b).toFun ((coproductInr k₁ k₂).toFun x) = b.toFun x :=
  LinearMap.congr_fun (coproduct_linearMap_ext (fun j => shift (regularModule A) (k₂ j))
    (f := (coproductSumDesc k₁ k₂ a b).toFun.comp (coproductInr k₁ k₂).toFun) (g := b.toFun)
    fun j y => by
      simp only [LinearMap.comp_apply]
      rw [coproductInr_ι, coproductSumDesc_ι_inr]) x

/-- **A graded module split into two finite free graded pieces is finite free.** The two
coordinates `α`, `β` and the two inclusions `a`, `b` of a direct sum decomposition
`L = ⨁ⱼ A[k₁ j] ⊕ ⨁ⱼ A[k₂ j]` of graded modules assemble into an isomorphism of `L` with the
direct sum indexed by the disjoint union of the two index types. -/
private theorem isFiniteFreeAsGradedModule_of_gradedSplitting
    {L : DifferentialGradedModule.{u, u, u} A} {J₁ J₂ : Type u} [Finite J₁] [Finite J₂]
    (k₁ : J₁ → ℤ) (k₂ : J₂ → ℤ)
    (α : GradedHom L (∐ fun j => shift (regularModule A) (k₁ j)))
    (β : GradedHom L (∐ fun j => shift (regularModule A) (k₂ j)))
    (a : GradedHom (∐ fun j => shift (regularModule A) (k₁ j)) L)
    (b : GradedHom (∐ fun j => shift (regularModule A) (k₂ j)) L)
    (hαa : ∀ x, α.toFun (a.toFun x) = x) (hβb : ∀ x, β.toFun (b.toFun x) = x)
    (hαb : ∀ x, α.toFun (b.toFun x) = 0) (hβa : ∀ x, β.toFun (a.toFun x) = 0)
    (hdec : ∀ y, a.toFun (α.toFun y) + b.toFun (β.toFun y) = y) :
    IsFiniteFreeAsGradedModule L := by
  refine ⟨J₁ ⊕ J₂, inferInstance, Sum.elim k₁ k₂, coproductSumLift k₁ k₂ α β,
    coproductSumDesc k₁ k₂ a b, fun y => ?_, fun z => ?_⟩
  · change (coproductSumDesc k₁ k₂ a b).toFun
      ((coproductInl k₁ k₂).toFun (α.toFun y) + (coproductInr k₁ k₂).toFun (β.toFun y)) = y
    rw [map_add, coproductSumDesc_inl, coproductSumDesc_inr, hdec]
  · refine LinearMap.congr_fun (coproduct_linearMap_ext
      (fun t : J₁ ⊕ J₂ => shift (regularModule A) (Sum.elim k₁ k₂ t))
      (f := (coproductSumLift k₁ k₂ α β).toFun.comp (coproductSumDesc k₁ k₂ a b).toFun)
      (g := LinearMap.id) fun t y => ?_) z
    simp only [LinearMap.comp_apply, LinearMap.id_apply]
    match t with
    | Sum.inl j =>
      rw [coproductSumDesc_ι_inl]
      change (coproductInl k₁ k₂).toFun (α.toFun (a.toFun _)) +
        (coproductInr k₁ k₂).toFun (β.toFun (a.toFun _)) = _
      rw [hαa, hβa, map_zero, add_zero, coproductInl_ι]
    | Sum.inr j =>
      rw [coproductSumDesc_ι_inr]
      change (coproductInl k₁ k₂).toFun (α.toFun (b.toFun _)) +
        (coproductInr k₁ k₂).toFun (β.toFun (b.toFun _)) = _
      rw [hβb, hαb, map_zero, zero_add, coproductInr_ι]

/-- **An extension of finite free graded modules, split as graded modules, is finite free.** The
graded splitting of an admissible short exact sequence `K ⟶ L ⟶ M`
(`DifferentialGradedModule.exists_gradedSplitting`) identifies `L` with `K ⊕ M` as graded
modules, so the generators of the two ends together generate `L` freely. -/
private theorem isFiniteFreeAsGradedModule_of_isAdmissibleShortExact
    {K L M : DifferentialGradedModule.{u, u, u} A} (f : K ⟶ L) (g : L ⟶ M)
    (h : IsAdmissibleShortExact f g) (hK : IsFiniteFreeAsGradedModule K)
    (hM : IsFiniteFreeAsGradedModule M) : IsFiniteFreeAsGradedModule L := by
  obtain ⟨J₁, hJ₁, k₁, φ₁, ψ₁, hψφ₁, hφψ₁⟩ := hK
  obtain ⟨J₂, hJ₂, k₂, φ₂, ψ₂, hψφ₂, hφψ₂⟩ := hM
  obtain ⟨π, s, hπf, hgs, hπs, hdec⟩ := exists_gradedSplitting f g h
  have hgf := toFun_comp_eq_zero f g h
  refine isFiniteFreeAsGradedModule_of_gradedSplitting k₁ k₂ (gradedComp π φ₁)
    (gradedComp g.toGradedHom φ₂) (gradedComp ψ₁ f.toGradedHom) (gradedComp ψ₂ s)
    (fun x => ?_) (fun x => ?_) (fun x => ?_) (fun x => ?_) fun y => ?_
  · change φ₁.toFun (π.toFun (f.toFun (ψ₁.toFun x))) = x
    rw [hπf, hφψ₁]
  · change φ₂.toFun (g.toFun (s.toFun (ψ₂.toFun x))) = x
    rw [hgs, hφψ₂]
  · change φ₁.toFun (π.toFun (s.toFun (ψ₂.toFun x))) = 0
    rw [hπs, map_zero]
  · change φ₂.toFun (g.toFun (f.toFun (ψ₁.toFun x))) = 0
    rw [hgf, map_zero]
  · change f.toFun (ψ₁.toFun (φ₁.toFun (π.toFun y))) + s.toFun (ψ₂.toFun (φ₂.toFun (g.toFun y))) = y
    rw [hψφ₁, hψφ₂, hdec]

/-! ### A module with a finite cell filtration is finite free as a graded module -/

/-- A property of modules holding for zero modules, finite direct sums of shifts of the algebra,
isomorphic copies and middle terms of admissible short exact sequences holds for every module with
a finite cell filtration. -/
private theorem of_hasFiniteCellFiltration {Q : DifferentialGradedModule.{u, u, u} A → Prop}
    (hzero : ∀ {M}, IsZero M → Q M) (hiso : ∀ {M N}, (M ≅ N) → Q M → Q N)
    (hcoprod : ∀ (J : Type u) [Finite J] (k : J → ℤ),
      Q (∐ fun j => shift (regularModule A) (k j)))
    (hext : ∀ {K L M : DifferentialGradedModule.{u, u, u} A} (f : K ⟶ L) (g : L ⟶ M),
      IsAdmissibleShortExact f g → Q K → Q M → Q L)
    {P : DifferentialGradedModule.{u, u, u} A} (hP : HasFiniteCellFiltration P) : Q P := by
  obtain ⟨n, F, hzero', htop, hquot⟩ := hP
  have key : ∀ i : ℕ, i ≤ n + 1 → Q (F.obj i) := by
    intro i hi
    induction i with
    | zero => exact hzero hzero'
    | succ i ih =>
      obtain ⟨J, hJ, k, ⟨e⟩⟩ := hquot ⟨i, by omega⟩
      have hfin : Finite J := hJ
      exact hext _ _
        (isAdmissibleShortExact_cokernelπ (F.diagram.map (homOfLE (Nat.le_succ i))) k e)
        (ih (by omega)) (hiso e.symm (hcoprod J k))
  exact hiso (asIso (F.ι.app (n + 1))) (key (n + 1) le_rfl)

/-- **A module with a finite cell filtration is finite free as a graded module.** Each step of the
filtration sits in an admissible short exact sequence whose quotient is a finite direct sum of
shifts of the algebra (`DifferentialGradedModule.isAdmissibleShortExact_cokernelπ`), so the
graded generators accumulate up the filtration, starting from none at the zero bottom stage. -/
theorem isFiniteFreeAsGradedModule_of_hasFiniteCellFiltration
    {P : DifferentialGradedModule.{u, u, u} A} (hP : HasFiniteCellFiltration P) :
    IsFiniteFreeAsGradedModule P := by
  exact of_hasFiniteCellFiltration isFiniteFreeAsGradedModule_of_isZero
    (fun e => IsFiniteFreeAsGradedModule.of_iso e)
    (fun _ _ => isFiniteFreeAsGradedModule_coproduct_shifts)
    isFiniteFreeAsGradedModule_of_isAdmissibleShortExact hP

/-! ### A module with a finite cell filtration computes its derived morphisms -/

/-- The direct sum of shifts of the algebra formed as a coproduct of the category is the explicit
one, `DifferentialGradedModule.directSumShifts`: both are colimits of the same family. -/
private def coproductShiftsIsoDirectSumShifts {J : Type u} [DecidableEq J] (k : J → ℤ) :
    (∐ fun j => shift (regularModule A) (k j)) ≅ directSumShifts A k :=
  (colimit.isoColimitCocone ⟨Cofan.mk _ (directSumInj _), isColimit_directSumObj _⟩).trans
    (directSumObjIsoDirectSumShifts A k)

/-- A direct sum of shifts of the algebra is orthogonal on the left to the acyclic modules
(Tag 09KM for the one-step filtration), whatever the index type. -/
private theorem leftOrthogonal_acyclic_coproduct_shifts {J : Type u} (k : J → ℤ) :
    (acyclic' A).leftOrthogonal
      ((toHomotopyCategory A).obj (∐ fun j => shift (regularModule A) (k j))) := by
  classical
  exact leftOrthogonal_acyclic_of_iso A (coproductShiftsIsoDirectSumShifts k).symm
    (leftOrthogonal_acyclic_directSumShifts A k)

/-- A zero module is orthogonal on the left to the acyclic modules: every morphism out of it
vanishes. -/
private theorem leftOrthogonal_acyclic_of_isZero {M : DifferentialGradedModule.{u, u, u} A}
    (hM : IsZero M) : (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj M) := by
  intro Y f _
  exact ((toHomotopyCategory A).map_isZero hM).eq_of_src f 0

/-- **A module with a finite cell filtration is orthogonal on the left to the acyclic modules.**
The steps of the filtration are admissible monomorphisms with quotients direct sums of shifts of
the algebra, both of which are orthogonal on the left to the acyclic modules, and orthogonality
is inherited by the middle term of an admissible short exact sequence (Tag 0149). -/
theorem leftOrthogonal_acyclic_of_hasFiniteCellFiltration
    {P : DifferentialGradedModule.{u, u, u} A} (hP : HasFiniteCellFiltration P) :
    (acyclic' A).leftOrthogonal ((toHomotopyCategory A).obj P) := by
  exact of_hasFiniteCellFiltration leftOrthogonal_acyclic_of_isZero
    (fun e => leftOrthogonal_acyclic_of_iso A e)
    (fun _ _ => leftOrthogonal_acyclic_coproduct_shifts)
    (fun f g h => leftOrthogonal_acyclic_of_isAdmissibleShortExact A f g h) hP

/-- **A module with a finite cell filtration satisfies the condition of [Stacks, Tag 09R0]**: the
localization functor is bijective on morphisms out of it into every differential graded module,
that is `Hom_{K(A, d)}(P, M) = Hom_{D(A, d)}(P, M)` for every `M`. It is orthogonal on the left to
the acyclic modules, and morphisms out of such an object are not changed by localization
(Tag 09KY, `DifferentialGradedModule.bijective_q_map_of_leftOrthogonal`). -/
theorem bijective_q_map_of_hasFiniteCellFiltration
    {P : DifferentialGradedModule.{u, u, u} A} (hP : HasFiniteCellFiltration P)
    (M : DifferentialGradedModule.{u, u, u} A) :
    Function.Bijective (((quasiIsomorphisms' A).Q).map :
      ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj M) → _) :=
  bijective_q_map_of_leftOrthogonal (leftOrthogonal_acyclic_of_hasFiniteCellFiltration hP) _

/-! ### Finite freeness implies finiteness -/

/-- **A module which is finite free as a graded module is finite**, that is finitely generated as
a right `A`-module (`DifferentialGradedModule.IsFinite`, Tag 09R1): a finite direct sum of shifts
of the algebra is finitely generated, and the module is a quotient of one. -/
theorem isFinite_of_isFiniteFreeAsGradedModule {P : DifferentialGradedModule.{u, u, u} A}
    (hP : IsFiniteFreeAsGradedModule P) : IsFinite P := by
  obtain ⟨J, hJ, k, φ, ψ, hψφ, _⟩ := hP
  have hfin : Finite J := hJ
  have hsum : Module.Finite (MulOpposite A.A)
      (∐ fun j => shift (regularModule A) (k j)).M := finite_coproduct_shifts k
  exact Module.Finite.of_surjective ψ.opLinearMap fun x => ⟨φ.toFun x, hψφ x⟩

/-- **The converse of the corrected implication of [Stacks, Tag 09RB].** A direct summand in
`D(A, d)` of the image of a module which is finite free as a graded module and computes its
derived morphisms is a compact object. This is the source's own (2) ⟹ (1), with condition (2)
read in the corrected form: finite freeness enters only through the finiteness it implies
(`DifferentialGradedModule.isCompactObject_q_of_isFinite`, Tag 09R1), and a retract of a compact
object is compact (Tag 09QH). It is one half of
`DifferentialGradedModule.isCompactObject_iff_exists_retract_isFiniteFreeAsGradedModule`, and
enters the registered `DifferentialGradedModule.isCompactObject_tfae_exists_retract`. -/
theorem isCompactObject_of_retract_isFiniteFreeAsGradedModule
    (A : DifferentialGradedAlgebra.{u, u} R) (E : derivedCategory' A)
    (P : DifferentialGradedModule.{u, u, u} A) (hP : IsFiniteFreeAsGradedModule P)
    (hD : ∀ M : DifferentialGradedModule.{u, u, u} A, Function.Bijective
      (((quasiIsomorphisms' A).Q).map :
        ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj M) → _))
    (i : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P)
    (r : (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P ⟶ E) (hir : i ≫ r = 𝟙 E) :
    IsCompactObject.{u} E :=
  isCompactObject_of_retract
    (isCompactObject_q_of_isFinite A (isFinite_of_isFiniteFreeAsGradedModule hP) hD) i r hir

/-! ### Tag 09RB, the corrected implication from compactness to a finite free model -/

/-- **The implication (1) ⟹ (2) of [Stacks, Tag 09RB], in the corrected form that the source's own
proof establishes.** A compact object `E` of `D(A, d)` is a *direct summand* in `D(A, d)` of the
image of a differential graded `A`-module `P` which is *finite free* as a graded `A`-module and
satisfies `Hom_{K(A, d)}(P, M) = Hom_{D(A, d)}(P, M)` for every differential graded `A`-module
`M`.

The literal statement of the source — that `E` can be *represented by* such a `P`, with *finite
projective* in place of finite free — is **false**, and is **a mistake in the Stacks Project,
pending review**: it is contradicted by the source's own [Stacks, Tag 09R5], whose compact object
over the bounded algebra `A = k[x, y]/(y²)` of Tag 09R4 has no finite graded-projective
representative at all. That refutation is
`Stacks.Examples.not_forall_exists_finite_gradedProjective_of_isCompactObject`, in
`StacksFrontier/Examples/Algebra/CompactObjectNoFiniteProjectiveModel.lean`. The two differences
below are exactly what the argument of Tag 09R3 delivers, and the counterexample is consistent
with them: there `E = Ker(x)` *is* a direct summand of the regular module, which is finite free.

The statement is **unconditional**: the boundedness hypothesis "`A^n = 0` for `|n| ≫ 0`" of the
source is not assumed and is not used anywhere in the proof, which is part of why the literal
statement cannot be rescued by it.

The proof composes the two implications the chapter already has. [Stacks, Tag 09R3],
`DifferentialGradedModule.isCompactObject_iff_exists_retract_hasFiniteCellFiltration`, makes `E` a
retract of the image of a module `P` with a finite cell filtration; such a `P` is finite free as a
graded module, because its filtration is built out of finitely many finite direct sums of shifts
of the algebra and splits as a filtration of graded modules
(`DifferentialGradedModule.isFiniteFreeAsGradedModule_of_hasFiniteCellFiltration`); and it is
orthogonal on the left to the acyclic modules, so morphisms out of it are not changed by
localization (`DifferentialGradedModule.bijective_q_map_of_hasFiniteCellFiltration`, Tag 09KY),
which is the condition of [Stacks, Tag 09R0].

The converse holds too, as
`DifferentialGradedModule.isCompactObject_of_retract_isFiniteFreeAsGradedModule`, and the two are
assembled into the tag's corrected equivalence,
`DifferentialGradedModule.isCompactObject_tfae_exists_retract`, which carries the registration of
[Stacks, Tag 09RB]. -/
theorem exists_retract_isFiniteFreeAsGradedModule_of_isCompactObject
    (A : DifferentialGradedAlgebra.{u, u} R) (E : derivedCategory' A)
    (hE : IsCompactObject.{u} E) :
    ∃ P : DifferentialGradedModule.{u, u, u} A, IsFiniteFreeAsGradedModule P ∧
      (∀ M : DifferentialGradedModule.{u, u, u} A, Function.Bijective
        (((quasiIsomorphisms' A).Q).map :
          ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj M) → _)) ∧
      ∃ (i : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P)
        (r : (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P ⟶ E), i ≫ r = 𝟙 E := by
  obtain ⟨P, hP, i, r, hir⟩ :=
    (isCompactObject_iff_exists_retract_hasFiniteCellFiltration A E).1 hE
  exact ⟨P, isFiniteFreeAsGradedModule_of_hasFiniteCellFiltration hP,
    fun M => bijective_q_map_of_hasFiniteCellFiltration hP M, i, r, hir⟩

/-! ### Finite freeness implies graded projectivity -/

/-- A surjective map of lawful graded modules is surjective on each homogeneous piece: the
homogeneous component of degree `n` of a preimage of a homogeneous element of degree `n` is again
a preimage. -/
private theorem exists_mem_grading_apply_eq_of_surjective
    {M N : Stacks.DifferentialGraded.DGModule.{u, u, u} (Unbundled.algebra A)}
    (hM : M.IsGradedLawful) (hN : N.IsGradedLawful)
    (f : Stacks.DifferentialGraded.DGModule.GradedHom M N) (hf : Function.Surjective f.toFun)
    {n : ℤ} {y : N.carrier} (hy : y ∈ N.grading n) :
    ∃ x : M.carrier, x ∈ M.grading n ∧ f.toFun x = y := by
  classical
  let := hM.isInternal.chooseDecomposition
  let := hN.isInternal.chooseDecomposition
  obtain ⟨x, rfl⟩ := hf y
  refine ⟨DirectSum.decompose M.grading x n, (DirectSum.decompose M.grading x n).2, ?_⟩
  have hsum := DirectSum.sum_support_decompose M.grading x
  rw [← DirectSum.decompose_of_mem_same N.grading hy,
    ← DirectSum.decompose_of_mem_same N.grading
      (f.map_grading n _ (DirectSum.decompose M.grading x n).2)]
  conv_rhs => rw [← hsum]
  rw [map_sum, DirectSum.decompose_sum, DFinsupp.finsetSum_apply, AddSubgroup.val_finsetSum]
  symm
  refine Finset.sum_eq_single n (fun i _ hin => ?_) (fun hn => ?_)
  · exact DirectSum.decompose_of_mem_ne N.grading
      (f.map_grading i _ (DirectSum.decompose M.grading x i).2) hin
  · rw [DFinsupp.notMem_support_iff.1 hn]
    simp

/-- The image of `a` in a summand of a direct sum of shifts of the regular module is `a` acting on
the image of `1`. -/
private theorem coproduct_shifts_ι_eq_op_smul {J : Type u} (k : J → ℤ) (j : J) (a : A.A) :
    (Sigma.ι (fun j => shift (regularModule A) (k j)) j).toFun a =
      MulOpposite.op a • (Sigma.ι (fun j => shift (regularModule A) (k j)) j).toFun (1 : A.A) := by
  rw [← (Sigma.ι (fun j => shift (regularModule A) (k j)) j).map_smul]
  congr 1
  exact (one_mul a).symm

/-- A point of a finite direct sum of differential graded modules is the sum of its components. -/
private theorem sum_ι_π_apply {J : Type u} [Fintype J] [DecidableEq J]
    (G : J → DifferentialGradedModule.{u, u, u} A) (y : (∐ G).M) :
    ∑ j, (Sigma.ι G j).toFun ((Sigma.π G j).toFun y) = y := by
  have h : (∑ j, (Sigma.ι G j).toFun ∘ₗ (Sigma.π G j).toFun) = LinearMap.id := by
    refine coproduct_linearMap_ext G fun i x => ?_
    rw [LinearMap.sum_apply, LinearMap.id_apply,
      Finset.sum_eq_single i (fun j _ hji => ?_) (fun h => absurd (Finset.mem_univ i) h)]
    · have h := congrArg (fun f : G i ⟶ G i => f.toFun x) (Sigma.ι_π_eq_id G i)
      change (Sigma.π G i).toFun ((Sigma.ι G i).toFun x) = x at h
      rw [LinearMap.comp_apply, h]
    · have h := congrArg (fun f : G i ⟶ G j => f.toFun x) (Sigma.ι_π_of_ne G (Ne.symm hji))
      change (Sigma.π G j).toFun ((Sigma.ι G i).toFun x) = 0 at h
      rw [LinearMap.comp_apply, h, map_zero]
  simpa using LinearMap.congr_fun h y

/-- **A finite direct sum of shifts of the algebra is projective as a graded module** ([Stacks,
Tag 09K0], `Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule`): a surjection of
graded modules onto it is split by sending the generator `1` of each summand to a homogeneous
preimage of the same degree. -/
theorem isProjectiveAsGradedModule_coproduct_shifts {J : Type u} [Finite J] (k : J → ℤ) :
    Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule.{u, u, u, u}
      (Unbundled.module (∐ fun j => shift (regularModule A) (k j))) := by
  classical
  let _ := Fintype.ofFinite J
  let G := fun j => shift (regularModule A) (k j)
  have hlaw := Unbundled.module_isLawful (∐ G)
  refine ⟨⟨hlaw.isInternal, hlaw.grading_smul⟩, fun M hM f hf => ?_⟩
  have hgen (j : J) : (Sigma.ι G j).toFun (1 : A.A) ∈ (∐ G).grading (-k j) := by
    apply (Sigma.ι G j).map_grading
    change (1 : A.A) ∈ A.grading (-k j + k j)
    simpa using SetLike.one_mem_graded A.grading
  choose m hm hfm using fun j => exists_mem_grading_apply_eq_of_surjective hM
    ⟨hlaw.isInternal, hlaw.grading_smul⟩ f hf (y := (Sigma.ι G j).toFun (1 : A.A)) (hgen j)
  let c (j : J) (y : (∐ G).M) : A.A := (Sigma.π G j).toFun y
  have hc_smul (j : J) (y : (∐ G).M) (a : A.A) :
      c j (MulOpposite.op a • y) = c j y * a :=
    (Sigma.π G j).map_smul y a
  let σ : (∐ G).M →ₗ[(Unbundled.algebra A).carrierᵐᵒᵖ] M.carrier :=
    { toFun := fun y => ∑ j, MulOpposite.op (c j y) • m j
      map_add' := fun y z => by
        simp only [c, map_add, MulOpposite.op_add, add_smul, Finset.sum_add_distrib]
      map_smul' := fun a y => by
        rw [← MulOpposite.op_unop a, Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hc_smul, MulOpposite.op_mul, mul_smul]
        rfl }
  refine ⟨⟨σ, fun n y hy => ?_⟩, fun y => ?_⟩
  · refine AddSubgroup.sum_mem _ fun j _ => ?_
    have hcj : c j y ∈ A.grading (n + k j) := (Sigma.π G j).map_grading n y hy
    have := hM.grading_smul (-k j) (n + k j) (m j) (c j y) (hm j) hcj
    rwa [show -k j + (n + k j) = n by ring] at this
  · change f.toFun (∑ j, MulOpposite.op (c j y) • m j) = y
    rw [map_sum]
    conv_rhs => rw [← sum_ι_π_apply G y]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [f.toFun.map_smul, hfm j]
    exact (coproduct_shifts_ι_eq_op_smul k j (c j y)).symm

/-- **A module which is finite free as a graded module is projective as a graded module**
([Stacks, Tag 09K0]): graded projectivity of the direct sum of shifts
(`DifferentialGradedModule.isProjectiveAsGradedModule_coproduct_shifts`) transfers along the
graded isomorphism. -/
theorem isProjectiveAsGradedModule_of_isFiniteFreeAsGradedModule
    {P : DifferentialGradedModule.{u, u, u} A} (hP : IsFiniteFreeAsGradedModule P) :
    Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule.{u, u, u, u}
      (Unbundled.module P) := by
  obtain ⟨J, hJ, k, φ, ψ, hψφ, hφψ⟩ := hP
  have hproj := isProjectiveAsGradedModule_coproduct_shifts (A := A) k
  have hlaw := Unbundled.module_isLawful P
  refine ⟨⟨hlaw.isInternal, hlaw.grading_smul⟩, fun M hM f hf => ?_⟩
  obtain ⟨σ, hσ⟩ := hproj.2 M hM
    { toFun := φ.opLinearMap ∘ₗ f.toFun
      map_grading := fun n x hx => φ.map_grading n _ (f.map_grading n x hx) }
    (fun y => by
      obtain ⟨x, hx⟩ := hf (ψ.toFun y)
      exact ⟨x, by simp [hx, hφψ]⟩)
  refine ⟨{ toFun := σ.toFun ∘ₗ φ.opLinearMap
            map_grading := fun n x hx => σ.map_grading n _ (φ.map_grading n x hx) }, fun y => ?_⟩
  have h := congrArg ψ.toFun (hσ (φ.toFun y))
  simp only [LinearMap.comp_apply, GradedHom.opLinearMap_apply, hψφ] at h
  simpa using h

/-! ### Tag 09RB, the corrected equivalence -/

/-- **Compact objects of `D(A, d)` are the direct summands of finite free models.** An object `E`
of `D(A, d)` is compact if and only if it is a direct summand in `D(A, d)` of the image of a
differential graded `A`-module `P` which is finite free as a graded `A`-module and satisfies
`Hom_{K(A, d)}(P, M) = Hom_{D(A, d)}(P, M)` for every differential graded `A`-module `M`. This
assembles `DifferentialGradedModule.exists_retract_isFiniteFreeAsGradedModule_of_isCompactObject`
and `DifferentialGradedModule.isCompactObject_of_retract_isFiniteFreeAsGradedModule`; it is part
of `DifferentialGradedModule.isCompactObject_tfae_exists_retract`, [Stacks, Tag 09RB]. -/
theorem isCompactObject_iff_exists_retract_isFiniteFreeAsGradedModule
    (A : DifferentialGradedAlgebra.{u, u} R) (E : derivedCategory' A) :
    IsCompactObject.{u} E ↔
      ∃ P : DifferentialGradedModule.{u, u, u} A, IsFiniteFreeAsGradedModule P ∧
        (∀ M : DifferentialGradedModule.{u, u, u} A, Function.Bijective
          (((quasiIsomorphisms' A).Q).map :
            ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj M) → _)) ∧
        ∃ (i : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P)
          (r : (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P ⟶ E), i ≫ r = 𝟙 E := by
  refine ⟨exists_retract_isFiniteFreeAsGradedModule_of_isCompactObject A E, ?_⟩
  rintro ⟨P, hP, hD, i, r, hir⟩
  exact isCompactObject_of_retract_isFiniteFreeAsGradedModule A E P hP hD i r hir

/-- **[Stacks, Tag 09RB], corrected.** *"Let `(A, d)` be a differential graded algebra. Assume
that `A^n = 0` for `|n| ≫ 0`. Let `E` be an object of `D(A, d)`. The following are equivalent:
(1) `E` is a compact object, and (2) `E` can be represented by a differential graded `A`-module
`P` which is finite projective as a graded `A`-module and satisfies
`Hom_{K(A, d)}(P, M) = Hom_{D(A, d)}(P, M)` for every differential graded `A`-module `M`."*

As printed, (1) ⟹ (2) is false: it is contradicted by the source's own [Stacks, Tag 09R5], over
the bounded algebra `A = k[x, y]/(y²)` of Tag 09R4, and the refutation is
`Stacks.Examples.not_forall_exists_finite_gradedProjective_of_isCompactObject` in
`StacksFrontier/Examples/Algebra/CompactObjectNoFiniteProjectiveModel.lean` (recorded in
`errata.md`, entry 09RB). The correction is to replace "can be represented by" in (2) by "is a
direct summand in `D(A, d)` of (the image of)". With that change the statement holds, and the
graded module may moreover be taken finite free. So the following are equivalent, for every
differential graded algebra (the boundedness of `A` is not needed in any direction, and is
dropped, which makes the statement more general):

1. `E` is a compact object;
2. `E` is a direct summand in `D(A, d)` of the image of a differential graded `A`-module `P` which
   is finite free as a graded `A`-module (`DifferentialGradedModule.IsFiniteFreeAsGradedModule`)
   and satisfies `Hom_{K(A, d)}(P, M) = Hom_{D(A, d)}(P, M)` for every `M`;
3. `E` is a direct summand in `D(A, d)` of the image of a differential graded `A`-module `P` which
   is finite (`DifferentialGradedModule.IsFinite`, Tag 09R1) and projective as a graded `A`-module
   (`Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule`, Tag 09K0) and satisfies
   `Hom_{K(A, d)}(P, M) = Hom_{D(A, d)}(P, M)` for every `M`.

The condition `Hom_{K(A, d)}(P, M) = Hom_{D(A, d)}(P, M)` is read as: the localization functor is
bijective on morphisms from the class of `P` to the class of `M` (Tag 09R0). Condition (3) is the
source's condition (2) with "represented by" corrected to "a direct summand of"; the second
conjunct is the source's implication (2) ⟹ (1) as printed, which is true.

Proof: (1) ⟹ (2) is
`DifferentialGradedModule.exists_retract_isFiniteFreeAsGradedModule_of_isCompactObject`
(Tag 09R3 and Tag 09KY); (2) ⟹ (3) holds because a finite free graded module is finite
(`DifferentialGradedModule.isFinite_of_isFiniteFreeAsGradedModule`) and graded projective
(`DifferentialGradedModule.isProjectiveAsGradedModule_of_isFiniteFreeAsGradedModule`); and
(3) ⟹ (1) because the image of a finite `P` with `Hom_K = Hom_D` is compact
(`DifferentialGradedModule.isCompactObject_q_of_isFinite`, Tag 09R1) and a direct summand of a
compact object is compact (Tag 09QH). -/
@[stacks 09RB "Corrected form. As printed, (1) ⟹ (2) is false (refuted by the source's own Tag \
09R5; see errata.md and Examples/Algebra/CompactObjectNoFiniteProjectiveModel.lean). The \
correction replaces 'E can be represented by P' with 'E is a direct summand in D(A, d) of the \
image of P'. Proved: (1) compact ⟺ (2) summand of a finite FREE graded P with Hom_K(P, -) = \
Hom_D(P, -) ⟺ (3) summand of a finite graded-projective P with Hom_K(P, -) = Hom_D(P, -); and \
the source's (2) as printed ⟹ (1). The boundedness of A is not needed and is dropped."]
theorem isCompactObject_tfae_exists_retract
    (A : DifferentialGradedAlgebra.{u, u} R) (E : derivedCategory' A) :
    List.TFAE
      [IsCompactObject.{u} E,
        ∃ P : DifferentialGradedModule.{u, u, u} A, IsFiniteFreeAsGradedModule P ∧
          (∀ M : DifferentialGradedModule.{u, u, u} A, Function.Bijective
            (((quasiIsomorphisms' A).Q).map :
              ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj M) → _)) ∧
          ∃ (i : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P)
            (r : (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P ⟶ E), i ≫ r = 𝟙 E,
        ∃ P : DifferentialGradedModule.{u, u, u} A, IsFinite P ∧
          Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule.{u, u, u, u}
            (Unbundled.module P) ∧
          (∀ M : DifferentialGradedModule.{u, u, u} A, Function.Bijective
            (((quasiIsomorphisms' A).Q).map :
              ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj M) → _)) ∧
          ∃ (i : E ⟶ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P)
            (r : (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P ⟶ E), i ≫ r = 𝟙 E] ∧
      ((∃ P : DifferentialGradedModule.{u, u, u} A, IsFinite P ∧
          Stacks.DifferentialGraded.DGModule.IsProjectiveAsGradedModule.{u, u, u, u}
            (Unbundled.module P) ∧
          (∀ M : DifferentialGradedModule.{u, u, u} A, Function.Bijective
            (((quasiIsomorphisms' A).Q).map :
              ((toHomotopyCategory A).obj P ⟶ (toHomotopyCategory A).obj M) → _)) ∧
          Nonempty (E ≅ (toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj P)) →
        IsCompactObject.{u} E) := by
  refine ⟨?_, fun ⟨P, hP, _, hD, ⟨e⟩⟩ => isCompactObject_of_iso e
    (isCompactObject_q_of_isFinite A hP hD)⟩
  tfae_have 1 → 2 := (isCompactObject_iff_exists_retract_isFiniteFreeAsGradedModule A E).1
  tfae_have 2 → 3 := fun ⟨P, hP, hD, i, r, hir⟩ =>
    ⟨P, isFinite_of_isFiniteFreeAsGradedModule hP,
      isProjectiveAsGradedModule_of_isFiniteFreeAsGradedModule hP, hD, i, r, hir⟩
  tfae_have 3 → 1 := fun ⟨P, hP, _, hD, i, r, hir⟩ =>
    isCompactObject_of_retract (isCompactObject_q_of_isFinite A hP hD) i r hir
  tfae_finish

end DifferentialGradedModule

end
