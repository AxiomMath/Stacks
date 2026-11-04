module

public import StacksFrontier.Topology.Sheaves.Sheaf.PointwiseProduct
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks 0075 — a presheaf of spaces whose underlying presheaf of sets is a sheaf, but which is
not a sheaf of spaces

Stacks 0075 explains why Lemma 0073 — a presheaf of algebraic structures whose underlying
presheaf of sets is a sheaf is itself a sheaf — has no analogue for topological spaces: the
forgetful functor `Top → Sets` preserves products and equalizers, but it does not reflect
isomorphisms.

The counterexample of the tag: let `X = ℕ` be discrete, let `A i` be discrete spaces each having
at least two points, and give `F(U) = ∏_{i ∈ U} A i` the *discrete* topology. The underlying
presheaf of sets is the sheaf of Example 006X, but `F` is not a sheaf of topological spaces: the
covering of `ℕ` by its singletons forces the sheaf condition of Definition 0072 to exhibit
`F(ℕ)` as a product in `Top` of the `F({i})`, i.e. to carry the *product* topology, and an
infinite product of spaces with at least two points is never discrete.

The crux is therefore `not_isOpen_singleton_pi_of_infinite`: in an infinite product of spaces with
at least two points no singleton is open (Mathlib's `Pi.discreteTopology` is available only for a
`Finite` index type, and this is exactly why). The tag is registered on
`exists_presheaf_topCat_isSheaf_forget_not_isSheaf`, the existence of the counterexample.

The closing aside of the tag — that the product topology on each `F(U)` *does* give a sheaf of
topological spaces — is left to the reader there and is not formalized here.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace

universe u

section Pi

variable {ι : Type*} {A : ι → Type*} [∀ i, TopologicalSpace (A i)]

/-- In a product of infinitely many topological spaces each having at least two points, no
singleton is open: an open set containing a point contains a basic open cylinder constraining
only finitely many coordinates, and any free coordinate provides a second point of that
cylinder. -/
theorem not_isOpen_singleton_pi_of_infinite [Infinite ι] [∀ i, Nontrivial (A i)]
    (c : ∀ i, A i) : ¬ IsOpen ({c} : Set (∀ i, A i)) := by
  classical
  intro hc
  obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.1 hc c rfl
  obtain ⟨j, hj⟩ := Infinite.exists_notMem_finset I
  obtain ⟨b, hb⟩ := exists_ne (c j)
  have hmem : Function.update c j b ∈ (I : Set ι).pi u := by
    intro i hi
    rw [Function.update_of_ne (fun h : i = j => hj (h ▸ hi))]
    exact (hu i hi).2
  have hcj : Function.update c j b j = c j := congrFun (hsub hmem) j
  rw [Function.update_self] at hcj
  exact hb hcj

/-- A product of infinitely many topological spaces each having at least two points does not
carry the discrete topology. Mathlib's `Pi.discreteTopology` is the complementary statement for
a `Finite` index type. -/
theorem not_discreteTopology_pi_of_infinite [Infinite ι] [∀ i, Nontrivial (A i)] :
    ¬ DiscreteTopology (∀ i, A i) := fun _ =>
  not_isOpen_singleton_pi_of_infinite (fun i => Classical.arbitrary (A i)) (isOpen_discrete _)

/-- A map into a *finite* product of discrete spaces is continuous for the discrete topology on
the product as soon as each of its components is continuous, because on a finite product of
discrete spaces the product topology is already the discrete one. -/
theorem continuous_bot_pi_of_finite {Z J : Type*} [TopologicalSpace Z] [Finite J]
    {B : J → Type*} [∀ j, TopologicalSpace (B j)] [∀ j, DiscreteTopology (B j)]
    {f : Z → ∀ j, B j} (hf : ∀ j, Continuous fun z => f z j) :
    @Continuous Z (∀ j, B j) inferInstance ⊥ f := by
  have h : (inferInstance : TopologicalSpace (∀ j, B j)) = ⊥ := DiscreteTopology.eq_bot
  exact h ▸ continuous_pi hf

end Pi

section Presheaf

variable (X : TopCat.{u}) (A : X → Type u)

/-- The presheaf of topological spaces on `X` whose sections over an open `U` are the functions
`(a_x)_{x ∈ U}` with `a_x ∈ A x`, carrying the **discrete** topology: the pointwise product
presheaf of Example 006X followed by the functor equipping a type with the discrete topology. -/
def presheafToDiscreteTypes : X.Presheaf TopCat.{u} :=
  X.presheafToTypes A ⋙ TopCat.discrete

/-- The presheaf of sets underlying `presheafToDiscreteTypes X A` is the pointwise product
presheaf of Example 006X: forgetting the discrete topology returns the bare functions. -/
theorem presheafToDiscreteTypes_comp_forget :
    presheafToDiscreteTypes X A ⋙ forget TopCat = X.presheafToTypes A := rfl

/-- The presheaf of sets underlying `presheafToDiscreteTypes X A` is a sheaf: it is the
pointwise product presheaf, which is a sheaf by Example 006X. -/
theorem isSheaf_presheafToDiscreteTypes_comp_forget :
    TopCat.Presheaf.IsSheaf (presheafToDiscreteTypes X A ⋙ forget TopCat) :=
  presheafToDiscreteTypes_comp_forget X A ▸ presheafToTypes_isSheaf A

/-- **The counterexample of Stacks 0075.** If `X` is an infinite discrete space and every `A x`
is a discrete space with at least two points, then the presheaf of topological spaces
`presheafToDiscreteTypes X A` is *not* a sheaf. Indeed, test the sheaf condition against the
space `W = ∏_x A x` carrying the *product* topology and the covering of `X` by its singletons:
the projections `W → A x` are continuous, hence so would be their gluing `W → F(X)`, which on
points is the identity of `∏_x A x`. The discrete topology of `F(X)` would then make every
singleton of the infinite product `W` open, which it is not. -/
theorem not_isSheaf_presheafToDiscreteTypes [DiscreteTopology X] [Infinite X]
    [∀ x, TopologicalSpace (A x)] [∀ x, DiscreteTopology (A x)] [∀ x, Nontrivial (A x)] :
    ¬ (presheafToDiscreteTypes X A).IsSheaf := by
  intro hF
  set F := presheafToDiscreteTypes X A
  -- the covering of `X` by its singletons
  set U : X → Opens X := fun i => ⟨{i}, isOpen_discrete _⟩
  have hmem : ∀ i : X, i ∈ iSup U := fun i => Opens.mem_iSup.2 ⟨i, rfl⟩
  have hfin : ∀ i : X, Finite ↥(U i) := fun i => (Set.finite_singleton i).to_subtype
  -- the product `∏ x, A x` with the *product* topology
  set W : TopCat.{u} := TopCat.of (∀ i : X, A i)
  -- the projections, continuous into the discrete topology because each `U i` is finite
  have hcont : ∀ i : X,
      @Continuous (∀ j : X, A j) (∀ x : ↥(U i), A ↑x) inferInstance ⊥
        (fun w x => w ↑x) := fun i =>
    continuous_bot_pi_of_finite fun x => continuous_apply (A := A) x.1
  set κ : ∀ i : X, W ⟶ F.obj (op (U i)) := fun i =>
    ConcreteCategory.ofHom ⟨fun w x => w ↑x, hcont i⟩
  -- the sheaf condition of `F` for the test object `W` is the sheaf condition of the
  -- presheaf of sets `V ↦ (W ⟶ F V)`, so the projections glue to a map `W ⟶ F (⨆ i, U i)`
  have hG : TopCat.Presheaf.IsSheaf (F ⋙ coyoneda.obj (op W)) :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type _ _).2 (hF W)
  obtain ⟨l₀, hl₀, -⟩ := hG.isSheafUniqueGluing_types (U := U) κ fun _ _ => rfl
  let l : W ⟶ F.obj (op (iSup U)) := l₀
  have hl : ∀ i : X, l ≫ F.map (Opens.leSupr U i).op = κ i := hl₀
  -- `l` is the identity of `∏ x, A x` read through the coordinates
  have key : ∀ (w : ↥W) (i : X), l w ⟨i, hmem i⟩ = w i := fun w i =>
    congrFun (ConcreteCategory.congr_hom (hl i) w) ⟨i, rfl⟩
  -- hence `l` is injective, and a singleton of the product topology would be open
  have hopen : IsOpen ((fun w : ↥W => l w) ⁻¹' {l fun i => Classical.arbitrary (A i)}) :=
    IsOpen.preimage l.hom.continuous (@isOpen_discrete _ _ ⟨rfl⟩ _)
  have heq : ((fun w : ↥W => l w) ⁻¹' {l fun i => Classical.arbitrary (A i)})
      = {fun i => Classical.arbitrary (A i)} := by
    ext w
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    refine ⟨fun h => funext fun i => ?_, fun h => by rw [h]⟩
    rw [← key w i, ← key (fun i => Classical.arbitrary (A i)) i, h]
  rw [heq] at hopen
  exact not_isOpen_singleton_pi_of_infinite _ hopen

end Presheaf

/-- **Stacks Tag 0075.** There is a topological space `X` and a presheaf `F` of topological
spaces on `X` whose underlying presheaf of sets is a sheaf, but which is not a sheaf of
topological spaces: so Lemma 0073 has no analogue for `Top`, the forgetful functor
`Top → Sets` not reflecting isomorphisms. The witness is the tag's: `X = ℕ` discrete, and
`F(U) = ∏_{i ∈ U} Bool` with the discrete topology. -/
@[stacks 0075, ega "0 3.1.4" "failure for top. spaces"]
theorem exists_presheaf_topCat_isSheaf_forget_not_isSheaf :
    ∃ (X : TopCat.{0}) (F : X.Presheaf TopCat.{0}),
      TopCat.Presheaf.IsSheaf (F ⋙ forget TopCat) ∧ ¬ TopCat.Presheaf.IsSheaf F :=
  ⟨TopCat.of ℕ, presheafToDiscreteTypes (TopCat.of ℕ) (fun _ => Bool),
    isSheaf_presheafToDiscreteTypes_comp_forget _ _,
    not_isSheaf_presheafToDiscreteTypes _ _⟩
