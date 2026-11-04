module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceSums
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Locality of the sectionwise finite-type condition

The sectionwise finite-type condition `PresheafOfModules.IsFiniteType` is local in every
variable, and the cokernel clause of Stacks 01BY (3) needs three of those localities which the
kernel and direct-sum clauses did not.  They are collected here, with no reference to cokernels
or to sheaves of modules, because each is a statement about an arbitrary presheaf of modules on
an arbitrary site.

## Main results

* `Stacks.SheafOfModules.isFiniteType_of_locallySurjective`: **the target of a sectionwise
  locally surjective map out of a presheaf of modules of finite type is of finite type.**  This
  is how a quotient inherits finite type: a generating family maps to a generating family, by
  `Stacks.SheafOfModules.generates_of_locallySurjective`.
* `Stacks.SheafOfModules.isFiniteType_of_locallyMem`: **a presheaf of modules with a
  finite-type subpresheaf each of whose sections lies locally in it is of finite type.**  This
  is the keystone of the cokernel clause: the comparison of the relations among a family of
  sections of a cokernel with the relations among a lift of that family is an inclusion whose
  quotient is only locally trivial, and this lemma is what makes such an inclusion enough.
* `Stacks.SheafOfModules.imageSubmodule` and
  `Stacks.SheafOfModules.isFiniteType_imageSubmodule`: the sectionwise image of a map of
  presheaves of modules, and the fact that the image of a presheaf of modules of finite type is
  of finite type.
* `Stacks.SheafOfModules.isFiniteType_relations_of_cover`: **finite type of the presheaf of
  relations among a finite family of sections over `U` may be tested on the members of a
  covering sieve of `U`.**  A section of a cokernel lifts only locally, so the relations clause
  of coherence can only be proved over the members of a covering sieve, and this is what
  assembles those proofs.

## Implementation notes

**Why `isFiniteType_of_locallyMem` is a corollary of the locally surjective statement.**  Being
locally in a submodule is exactly local surjectivity of the inclusion of that submodule, so the
keystone is `isFiniteType_of_locallySurjective` applied to
`PresheafOfModules.Submodule.ι`; no second induction is needed.

**Local surjectivity is stated on sections.**  The hypothesis of
`generates_of_locallySurjective` is spelled out as "every section of the target restricts, on a
covering sieve, into the image", rather than through `Presheaf.IsLocallySurjective`.  That keeps
the lemma free of the sheafification hypotheses which the comparison of epimorphisms with
locally surjective maps needs, and it is the form in which both of its uses supply it: for a
quotient of sheaves of modules the hypothesis comes from
`Stacks.SheafOfModules.LocalCokernel.locallySurjective_of_epi`, and for a submodule it is the
membership hypothesis itself.

**The two localizations of the quotient statement are composed by `exists_cover_comb_of_bind`.**
A section of the target is locally in the image, and a section of the source is locally a
combination of the generators, so the covering sieve witnessing generation in the target is the
bind of the two.

**How the relations presheaf is compared across a slice.**  For `g : V ⟶ U` the relations among
the restricted family `g⁻¹t` and the relations among `t` are *the same* submodule of the module
of coefficient tuples at every object `Z` of the slice over `V`, read once over `Z` and once
over `Z` seen in the slice over `U` through `Over.map g`; that is `relations_ker_eq_of_eq`,
and the comparison `relCast` is the identity on coefficients.  The transport of
`PresheafOfModules.Generates` across it, `generates_relations_overMap`, is then a computation
with `Sieve.overEquiv` and with `relations_comb_val`.

**Why the coefficient computations are done with `Eq.trans` and never with `rw`.** The sections
of `PresheafOfModules.relations M s` at an object are a subtype of a module of coefficient
tuples, and the two spellings are defeq but not type-correct at `implicit` transparency, so
`rw` and `simp only` refuse to fire on a goal of that shape.  Every equation here is therefore
stated as its own lemma — `relations_comb_val` — and composed with `Eq.trans`.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe u v w m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {S : Cᵒᵖ ⥤ RingCat.{w}}

/-! ### Quotients -/

/-- A linear combination of images of restricted sections is the image of the corresponding
linear combination, by naturality of the map. -/
private theorem sum_smul_map_eq {A B : PresheafOfModules.{m} S} (φ : A ⟶ B) {U Z : C}
    (f : Z ⟶ U) {n : ℕ} (s : Fin n → A.obj (op U)) (a : Fin n → S.obj (op Z))
    (z : A.obj (op Z)) (ha : ∑ i, a i • A.restrictₛₗ f.op (s i) = z) :
    ∑ i, a i • B.restrictₛₗ f.op (φ.app (op U) (s i)) = φ.app (op Z) z := by
  have h := congrArg (fun y ↦ φ.app (op Z) y) ha
  simp only [map_sum, map_smul] at h
  refine Eq.trans (Finset.sum_congr rfl fun i _ ↦ ?_) h
  exact congrArg (fun y ↦ a i • y) (PresheafOfModules.naturality_apply φ f.op (s i)).symm

/-- **A generating family maps to a generating family along a sectionwise locally surjective
map.**  A section of the target is, on a covering sieve, the image of a section of the source,
which is in turn locally a combination of the given generators; the two localizations are
composed by `exists_cover_comb_of_bind`. -/
theorem generates_of_locallySurjective {A B : PresheafOfModules.{m} S} (φ : A ⟶ B)
    (hφ : ∀ (V : C) (x : B.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ (W : C) (g : W ⟶ V), T g →
        ∃ y : A.obj (op W), φ.app (op W) y = B.restrictₛₗ g.op x)
    {U : C} {n : ℕ} (s : Fin n → A.obj (op U))
    (hs : PresheafOfModules.Generates J A s) :
    PresheafOfModules.Generates J B (fun j ↦ φ.app (op U) (s j)) := by
  intro V f x
  obtain ⟨T₀, hT₀, hT₀img⟩ := hφ V x
  refine exists_cover_comb_of_bind _ f x hT₀ ?_
  intro W g hg
  obtain ⟨y, hy⟩ := hT₀img W g hg
  obtain ⟨T, hT, hTgen⟩ := hs W (g ≫ f) y
  refine ⟨T, hT, fun Z k hk ↦ ?_⟩
  obtain ⟨a, ha⟩ := hTgen Z k hk
  refine ⟨a, ?_⟩
  rw [Category.assoc]
  exact (sum_smul_map_eq φ _ s a _ ha).trans
    ((PresheafOfModules.naturality_apply φ k.op y).trans
      ((congrArg (B.restrictₛₗ k.op) hy).trans (restrict_restrict g k x)))

/-- **The target of a sectionwise locally surjective map out of a presheaf of modules of finite
type is of finite type.**  The same covering family works, with the images of the generators as
generators. -/
theorem isFiniteType_of_locallySurjective {A B : PresheafOfModules.{m} S} (φ : A ⟶ B)
    (hφ : ∀ (V : C) (x : B.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ (W : C) (g : W ⟶ V), T g →
        ∃ y : A.obj (op W), φ.app (op W) y = B.restrictₛₗ g.op x)
    (hA : PresheafOfModules.IsFiniteType J A) :
    PresheafOfModules.IsFiniteType J B := by
  obtain ⟨I, U, hU, hgen⟩ := hA.exists_generators
  refine ⟨I, U, hU, fun i ↦ ?_⟩
  obtain ⟨n, s, hs⟩ := hgen i
  exact ⟨n, fun j ↦ φ.app (op (U i)) (s j), generates_of_locallySurjective φ hφ s hs⟩

/-- **A presheaf of modules with a subpresheaf of finite type each of whose sections lies
locally in it is of finite type.**

This is the form in which a comparison of presheaves of modules that is an inclusion with
locally trivial quotient — rather than an isomorphism — still transports finite type, and it is
what the cokernel clause of Stacks 01BY (3) needs: the relations among a finite family of
sections of a sheaf cokernel contain the relations coming from a lift of that family, and
contain them with locally trivial quotient only, because a sheaf cokernel kills a section only
locally.

It is a corollary of `isFiniteType_of_locallySurjective`: lying locally in a submodule is
exactly local surjectivity of the inclusion of that submodule. -/
theorem isFiniteType_of_locallyMem {M : PresheafOfModules.{m} S} (N : M.Submodule)
    (hloc : ∀ (V : C) (x : M.obj (op V)), ∃ T : Sieve V, T ∈ J V ∧
      ∀ (W : C) (g : W ⟶ V), T g → M.restrictₛₗ g.op x ∈ N.obj (op W))
    (hN : PresheafOfModules.IsFiniteType J N.toPresheafOfModules) :
    PresheafOfModules.IsFiniteType J M :=
  isFiniteType_of_locallySurjective N.ι
    (fun V x ↦ by
      obtain ⟨T, hT, hmem⟩ := hloc V x
      exact ⟨T, hT, fun W g hg ↦ ⟨⟨_, hmem W g hg⟩, rfl⟩⟩) hN

/-! ### Images -/

/-- The sectionwise image of a map of presheaves of modules, as a submodule of the target: the
family of images is stable under restriction because the map is natural. -/
noncomputable def imageSubmodule {A B : PresheafOfModules.{m} S} (φ : A ⟶ B) : B.Submodule where
  obj X := LinearMap.range (φ.app X).hom
  map {X Y} f := by
    rintro y ⟨z, rfl⟩
    exact ⟨A.map f z, PresheafOfModules.naturality_apply φ f z⟩

/-- A generating family maps to a generating family of the sectionwise image.  Unlike
`generates_of_locallySurjective` this needs no localization at all: a section of the image is
*globally* the image of a section of the source. -/
theorem generates_imageSubmodule {A B : PresheafOfModules.{m} S} (φ : A ⟶ B)
    {U : C} {n : ℕ} (s : Fin n → A.obj (op U))
    (hs : PresheafOfModules.Generates J A s) :
    PresheafOfModules.Generates J (imageSubmodule φ).toPresheafOfModules
      (fun j ↦ ⟨φ.app (op U) (s j), ⟨s j, rfl⟩⟩) := by
  refine generates_submodule _ _ ?_
  intro V f t
  obtain ⟨z, hz⟩ := t.2
  obtain ⟨T, hT, hTgen⟩ := hs V f z
  refine ⟨T, hT, fun W g hg ↦ ?_⟩
  obtain ⟨a, ha⟩ := hTgen W g hg
  refine ⟨a, ?_⟩
  exact (sum_smul_map_eq φ _ s a _ ha).trans
    ((PresheafOfModules.naturality_apply φ g.op z).trans (congrArg (B.restrictₛₗ g.op) hz))

/-- **The sectionwise image of a presheaf of modules of finite type is of finite type.** -/
theorem isFiniteType_imageSubmodule {A B : PresheafOfModules.{m} S} (φ : A ⟶ B)
    (hA : PresheafOfModules.IsFiniteType J A) :
    PresheafOfModules.IsFiniteType J (imageSubmodule φ).toPresheafOfModules := by
  obtain ⟨I, U, hU, hgen⟩ := hA.exists_generators
  refine ⟨I, U, hU, fun i ↦ ?_⟩
  obtain ⟨n, s, hs⟩ := hgen i
  exact ⟨n, _, generates_imageSubmodule φ s hs⟩

/-! ### The relations presheaf is local on the base -/

/-- The relations among a family of sections restricted along `g` and the relations among the
family itself are the same submodule of the module of coefficient tuples, whenever the two
arrows to the base agree. -/
private theorem relations_ker_eq_of_eq {Q : PresheafOfModules.{m} S} {U : C} {n : ℕ}
    (t : Fin n → Q.obj (op U)) {Y V : C} {g : V ⟶ U} {a : Y ⟶ V} {b : Y ⟶ U}
    (hab : a ≫ g = b) :
    LinearMap.ker (Fintype.linearCombination (S.obj (op Y))
        (fun j ↦ Q.restrictₛₗ a.op (Q.restrictₛₗ g.op (t j)))) =
      LinearMap.ker (Fintype.linearCombination (S.obj (op Y))
        (fun j ↦ Q.restrictₛₗ b.op (t j))) := by
  congr 1
  congr 1
  funext j
  rw [restrict_restrict g a (t j), hab]

/-- A section of the relations presheaf of a restricted family, read as a section of the
relations presheaf of the original family. -/
private def relCast {Q : PresheafOfModules.{m} S} {U : C} {n : ℕ}
    (t : Fin n → Q.obj (op U)) {V : C} (g : V ⟶ U) (Z : Over V)
    (z : (PresheafOfModules.relations Q (fun j ↦ Q.restrictₛₗ g.op (t j))).obj (op Z)) :
    (PresheafOfModules.relations Q t).obj (op ((Over.map g).obj Z)) :=
  ⟨z.val, relations_ker_eq_of_eq t (g := g) (a := Z.hom) (b := Z.hom ≫ g) rfl ▸ z.2⟩

/-- A section of the relations presheaf of a family, read as a section of the relations presheaf
of the family restricted along `g`. -/
private def relCastSymm {Q : PresheafOfModules.{m} S} {U : C} {n : ℕ}
    (t : Fin n → Q.obj (op U)) {V : C} (g : V ⟶ U) (Y : Over U) (a : Y.left ⟶ V)
    (hab : a ≫ g = Y.hom) (z : (PresheafOfModules.relations Q t).obj (op Y)) :
    (PresheafOfModules.relations Q
      (fun j ↦ Q.restrictₛₗ g.op (t j))).obj (op (Over.mk a)) :=
  ⟨z.val, (relations_ker_eq_of_eq t (g := g) (a := a) hab).symm ▸ z.2⟩

/-- The coefficients of a linear combination of restricted sections of a relations presheaf.

Stating this as its own lemma is what makes the coefficient computations possible: the sections
of a relations presheaf at an object are a subtype of a module of coefficient tuples, and the
two spellings are defeq but not type-correct at `implicit` transparency, so `rw` refuses to fire
on a goal of that shape.  Every use of this lemma is through `Eq.trans`. -/
theorem relations_comb_val {M : PresheafOfModules.{m} S} {U : C} {n : ℕ}
    (s : Fin n → M.obj (op U)) {X Y : (Over U)ᵒᵖ} (φ : X ⟶ Y) {q : ℕ}
    (b : Fin q → S.obj (op Y.unop.left))
    (z : Fin q → (PresheafOfModules.relations M s).obj X) (j : Fin n) :
    (∑ l, b l • (PresheafOfModules.relations M s).restrictₛₗ φ (z l)).val j
      = ∑ l, b l * ConcreteCategory.hom (S.map φ.unop.left.op) ((z l).val j) := by
  rw [relations_coe_sum]
  exact Finset.sum_congr rfl fun l _ ↦ congrArg (fun y ↦ b l * y)
    (relations_coe_restrict s φ (z l) j)

/-- Generation of the relations presheaf of a restricted family, read on the larger slice.  At
every object the two presheaves have the same coefficient tuples as sections, and a covering
sieve of an object of one slice is a covering sieve of the corresponding object of the other by
`Sieve.overEquiv`. -/
private theorem generates_relations_overMap (Q : PresheafOfModules.{m} S) {U : C} {n : ℕ}
    (t : Fin n → Q.obj (op U)) {V : C} (g : V ⟶ U) {Z : Over V} {q : ℕ}
    (c : Fin q → (PresheafOfModules.relations Q
      (fun j ↦ Q.restrictₛₗ g.op (t j))).obj (op Z))
    (hc : PresheafOfModules.Generates (J.over V)
      (PresheafOfModules.relations Q (fun j ↦ Q.restrictₛₗ g.op (t j))) c) :
    PresheafOfModules.Generates (J.over U) (PresheafOfModules.relations Q t)
      (fun k ↦ relCast t g Z (c k)) := by
  intro Y f x
  have hYV : (f.left ≫ Z.hom) ≫ g = Y.hom := by simpa using Over.w f
  obtain ⟨T, hT, hTgen⟩ := hc (Over.mk (f.left ≫ Z.hom)) (Over.homMk f.left)
    (relCastSymm t g Y (f.left ≫ Z.hom) hYV x)
  refine ⟨(Sieve.overEquiv Y).symm (Sieve.overEquiv (Over.mk (f.left ≫ Z.hom)) T),
    J.overEquiv_symm_mem_over Y _ ((J.mem_over_iff T).mp hT), ?_⟩
  intro Y'' h hh
  rw [Sieve.overEquiv_symm_iff, Sieve.overEquiv_iff] at hh
  obtain ⟨a, ha⟩ := hTgen _ _ hh
  refine ⟨a, Subtype.ext (funext fun j ↦ ?_)⟩
  have h1 := Eq.trans (relations_comb_val (fun j ↦ Q.restrictₛₗ g.op (t j)) _ a c j).symm
    (Eq.trans (congrArg (fun z ↦ z.val j) ha)
      (relations_coe_restrict (fun j ↦ Q.restrictₛₗ g.op (t j)) _ _ j))
  exact Eq.trans (relations_comb_val t (h ≫ f).op a _ j)
    (Eq.trans h1 (relations_coe_restrict t h.op x j).symm)

/-- **Finite type of the presheaf of relations among a finite family of sections over `U` is
local on `U`.**  If the relations among the family restricted along every arrow of a covering
sieve of `U` form a presheaf of finite type on the corresponding slice site, then so do the
relations among the family itself.

This is what lets the relations clause of coherence be proved only over the members of a
covering sieve, which is all that a construction producing a *local* description of a family of
sections — a lift of a family of sections of a sheaf cokernel, say — can offer.  The covering
family of the slice over `U` is assembled from the inner covering families by
`generates_relations_overMap`, and it covers because a covering family of covering families
covers. -/
@[ega "0 5.3.1" "Locality of condition b)"]
theorem isFiniteType_relations_of_cover (Q : PresheafOfModules.{m} S) {U : C} {n : ℕ}
    (t : Fin n → Q.obj (op U)) {S₀ : Sieve U} (hS₀ : S₀ ∈ J U)
    (h : ∀ ⦃V : C⦄ (g : V ⟶ U), S₀ g →
      PresheafOfModules.IsFiniteType (J.over V)
        (PresheafOfModules.relations Q (fun j ↦ Q.restrictₛₗ g.op (t j)))) :
    PresheafOfModules.IsFiniteType (J.over U) (PresheafOfModules.relations Q t) := by
  classical
  choose Ii Zc hZc hgen using fun (V : C) (g : V ⟶ U) (hg : S₀ g) ↦ (h g hg).exists_generators
  refine isFiniteType_presheaf_of_coversTop
    (J := J.over U)
    (fun j : Σ p : Σ V : C, {g : V ⟶ U // S₀.arrows g}, Ii p.1 p.2.1 p.2.2 ↦
      (Over.map j.1.2.1).obj (Zc j.1.1 j.1.2.1 j.1.2.2 j.2)) ?_ ?_
  · intro Y
    rw [J.mem_over_iff]
    apply J.transitive (J.pullback_stable Y.hom hS₀)
    intro Y₁ k hk
    have hk' : S₀ (k ≫ Y.hom) := hk
    have hcov := (J.mem_over_iff _).mp (hZc Y₁ (k ≫ Y.hom) hk' (Over.mk (𝟙 Y₁)))
    apply J.superset_covering ?_ hcov
    intro Y₂ m hm
    rw [Sieve.overEquiv_iff, Sieve.mem_ofObjects_iff] at hm
    obtain ⟨i, ⟨θ⟩⟩ := hm
    rw [Sieve.pullback_apply, Sieve.overEquiv_iff, Sieve.mem_ofObjects_iff]
    refine ⟨⟨⟨Y₁, ⟨k ≫ Y.hom, hk'⟩⟩, i⟩, ⟨Over.homMk θ.left ?_⟩⟩
    have hθ := Over.w θ
    dsimp at hθ ⊢
    rw [← Category.assoc, hθ]
    simp
  · rintro ⟨⟨V, g, hg⟩, i⟩
    obtain ⟨q, c, hc⟩ := hgen V g hg i
    exact ⟨q, _, generates_relations_overMap Q t g c hc⟩

end Stacks.SheafOfModules

end
