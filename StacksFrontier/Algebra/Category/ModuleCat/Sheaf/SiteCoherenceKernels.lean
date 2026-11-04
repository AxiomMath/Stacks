module

public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentExtensionOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedModuleAbelian
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SiteCoherenceClosure

/-!
# Kernels of maps of coherent sheaves of modules on a site

Stacks 01BY (2) says that the kernel of a map from a sheaf of modules of finite type into a
coherent sheaf of modules is of finite type. This file proves it over a ringed site, for the
predicate `SheafOfModules.IsCoherentOnSite` of Stacks 03DL(8), together with the restriction
calculus for linear combinations of sections that the clauses of Stacks 01BY on a site use.

## Main results

* `Stacks.SheafOfModules.isFiniteType_kerSubmodule`: the sectionwise kernel of a map from a
  presheaf of modules of finite type into one whose finite families of sections have
  finite-type presheaves of relations is of finite type.
* `Stacks.SheafOfModules.isFiniteType_kerObj`: the sectionwise kernel `SheafOfModules.kerObj`
  of a map from a sheaf of modules of finite type into a coherent sheaf of modules is of finite
  type.
* `Stacks.SheafOfModules.isFiniteType_presheaf_of_coversTop`: finite type may be certified by a
  covering family indexed by an arbitrary type.
* `Stacks.SheafOfModules.generates_submodule`: a finite family of sections of a submodule
  generates it as soon as their images generate it in the ambient presheaf of modules.
* `Stacks.SheafOfModules.exists_cover_comb_of_bind`: being locally a linear combination of a
  fixed finite family of sections is a local condition.
* `Stacks.SheafOfModules.restrict_sum_smul`, `Stacks.SheafOfModules.relations_coe_restrict`,
  `Stacks.SheafOfModules.relations_coe_sum`: restriction of sections and of linear combinations,
  in a presheaf of modules and in a presheaf of relations; that a map of presheaves of modules
  commutes with restriction is Mathlib's `PresheafOfModules.naturality_apply`.

## Implementation notes

`SheafOfModules.IsCoherentOnSite` asks that the presheaf `PresheafOfModules.relations B s` of
relations among a finite family of sections be of finite type, and
`PresheafOfModules.IsFiniteType` asks for finitely many generators only locally, so the kernel
statement is stated and proved for presheaves of modules, with no sheafification.

`PresheafOfModules.IsFiniteType` indexes its covering family by `Type u`, the universe of the
objects of the site, whereas generators obtained on slice sites are indexed in `Type (max u v)`;
`isFiniteType_presheaf_of_coversTop` passes to the set of objects that carry generators.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe u v w m

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {S : Cᵒᵖ ⥤ RingCat.{w}}

/-! ### Restriction maps and linear combinations -/

private theorem restrict_arrow_congr (M : PresheafOfModules.{m} S) {X Y : C} {f g : Y ⟶ X}
    (h : f = g) (x : M.obj (op X)) :
    M.restrictₛₗ f.op x = M.restrictₛₗ g.op x :=
  M.congr_map_apply (by rw [h]) x

/-- Restricting a linear combination of restricted sections along a further arrow. -/
theorem restrict_sum_smul (M : PresheafOfModules.{m} S) {X Y Z : C}
    (h : Y ⟶ X) (g : Z ⟶ Y) {n : ℕ} (x : Fin n → S.obj (op Y)) (b : Fin n → M.obj (op X)) :
    M.restrictₛₗ g.op (∑ j, x j • M.restrictₛₗ h.op (b j))
      = ∑ j, S.map g.op (x j) • M.restrictₛₗ (g ≫ h).op (b j) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smulₛₗ, restrict_restrict]

/-! ### Sections of a submodule and of a relations presheaf -/

private theorem submodule_coe_restrict {M : PresheafOfModules.{m} S} (N : M.Submodule)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : N.toPresheafOfModules.obj X) :
    (N.toPresheafOfModules.restrictₛₗ f x).val = M.restrictₛₗ f x.val := rfl

private theorem submodule_coe_sum_smul {M : PresheafOfModules.{m} S} (N : M.Submodule)
    {X : Cᵒᵖ} {n : ℕ}
    (b : Fin n → S.obj X) (z : Fin n → N.toPresheafOfModules.obj X) :
    (∑ i, b i • z i).val = ∑ i, b i • (z i).val := by
  show (N.ι.app X) (∑ i, b i • z i) = _
  rw [map_sum]
  simp only [map_smul]
  rfl

/-- Restriction in a presheaf of relations is restriction of each coefficient. -/
theorem relations_coe_restrict {M : PresheafOfModules.{m} S} {U : C} {n : ℕ}
    (s : Fin n → M.obj (op U)) {X Y : (Over U)ᵒᵖ} (f : X ⟶ Y)
    (x : (PresheafOfModules.relations M s).obj X) (j : Fin n) :
    ((PresheafOfModules.relations M s).restrictₛₗ f x).val j = S.map f.unop.left.op (x.val j) :=
  rfl

/-- A linear combination in a presheaf of relations is computed coefficientwise. -/
theorem relations_coe_sum {M : PresheafOfModules.{m} S} {U : C} {n : ℕ}
    (s : Fin n → M.obj (op U)) {X : (Over U)ᵒᵖ} {q : ℕ}
    (b : Fin q → S.obj (op X.unop.left))
    (z : Fin q → (PresheafOfModules.relations M s).obj X) (j : Fin n) :
    (∑ l, b l • z l).val j = ∑ l, b l * (z l).val j := by
  classical
  induction (Finset.univ : Finset (Fin q)) using Finset.induction with
  | empty => simp; rfl
  | insert l t hl ih =>
      rw [Finset.sum_insert hl, Finset.sum_insert hl]
      show (b l • z l).val j + (∑ x ∈ t, b x • z x).val j = _
      rw [ih]
      rfl

/-! ### Certifying finite type -/

/-- A presheaf of modules is of finite type as soon as it is generated by finitely many sections
over each object of a covering family indexed by an arbitrary type. -/
theorem isFiniteType_presheaf_of_coversTop {M : PresheafOfModules.{m} S}
    {I : Type*} (U : I → C) (hU : J.CoversTop U)
    (hgen : ∀ i, ∃ (n : ℕ) (s : Fin n → M.obj (op (U i))), PresheafOfModules.Generates J M s) :
    PresheafOfModules.IsFiniteType J M := by
  refine ⟨⟨Set.range U, fun t => t.1, fun Z ↦ J.superset_covering (fun Y f hf ↦ ?_) (hU Z), ?_⟩⟩
  · rw [Sieve.mem_ofObjects_iff] at hf ⊢
    obtain ⟨i, ⟨g⟩⟩ := hf
    exact ⟨⟨U i, ⟨i, rfl⟩⟩, ⟨g⟩⟩
  · rintro ⟨x, i, rfl⟩
    exact hgen i

/-- A finite family of sections of a submodule of a presheaf of modules generates the submodule
as soon as their images generate it inside the ambient presheaf. -/
theorem generates_submodule {M : PresheafOfModules.{m} S} (N : M.Submodule)
    {U : C} {n : ℕ} (s : Fin n → N.toPresheafOfModules.obj (op U))
    (h : ∀ (V : C) (f : V ⟶ U) (t : N.toPresheafOfModules.obj (op V)),
      ∃ T : Sieve V, T ∈ J V ∧ ∀ (W : C) (g : W ⟶ V), T g →
        ∃ a : Fin n → S.obj (op W),
          ∑ i, a i • M.restrictₛₗ (g ≫ f).op (s i).val = M.restrictₛₗ g.op t.val) :
    PresheafOfModules.Generates J N.toPresheafOfModules s := by
  intro V f t
  obtain ⟨T, hT, hTgen⟩ := h V f t
  refine ⟨T, hT, fun W g hg => ?_⟩
  obtain ⟨b, hb⟩ := hTgen W g hg
  refine ⟨b, Subtype.ext ?_⟩
  simpa only [submodule_coe_sum_smul, submodule_coe_restrict] using hb

/-- Being locally a linear combination of a fixed finite family of sections is itself a local
condition: a covering family on which the property holds after one further localization may be
replaced by the bind of the two covering sieves. -/
theorem exists_cover_comb_of_bind
    {M : PresheafOfModules.{m} S} {U V : C} {n : ℕ}
    (s : Fin n → M.obj (op U)) (f : V ⟶ U) (t : M.obj (op V))
    {S₀ : Sieve V} (hS₀ : S₀ ∈ J V)
    (h : ∀ (W : C) (g : W ⟶ V), S₀ g → ∃ T : Sieve W, T ∈ J W ∧
      ∀ (Z : C) (k : Z ⟶ W), T k → ∃ a : Fin n → S.obj (op Z),
        ∑ i, a i • M.restrictₛₗ ((k ≫ g) ≫ f).op (s i) = M.restrictₛₗ (k ≫ g).op t) :
    ∃ T : Sieve V, T ∈ J V ∧ ∀ (W : C) (g : W ⟶ V), T g → ∃ a : Fin n → S.obj (op W),
      ∑ i, a i • M.restrictₛₗ (g ≫ f).op (s i) = M.restrictₛₗ g.op t := by
  classical
  choose T hT hTgen using h
  refine ⟨Sieve.bind S₀.arrows (fun Y g hg => T Y g hg),
    J.bind_covering hS₀ (fun _ _ hg => hT _ _ hg), ?_⟩
  rintro W g ⟨Y, g₁, g₂, hg₂, hg₁, rfl⟩
  exact hTgen Y g₂ hg₂ W g₁ hg₁

/-! ### Stacks 01BY (2) and (3) for kernels -/

private theorem sum_smul_mem_submodule {A B : PresheafOfModules.{m} S} (φ : A ⟶ B)
    (K : A.Submodule) (hK : ∀ (X : Cᵒᵖ) (x : A.obj X), x ∈ K.obj X ↔ φ.app X x = 0)
    {U V : C} (h : V ⟶ U) {n : ℕ}
    (a : Fin n → A.obj (op U)) (x : Fin n → S.obj (op V))
    (hx : ∑ j, x j • B.restrictₛₗ h.op (φ.app (op U) (a j)) = 0) :
    (∑ j, x j • A.restrictₛₗ h.op (a j)) ∈ K.obj (op V) := by
  rw [hK, map_sum]
  have hnat : ∀ y, φ.app (op V) (A.restrictₛₗ h.op y) = B.restrictₛₗ h.op (φ.app (op U) y) :=
    fun y => PresheafOfModules.naturality_apply φ h.op y
  simp only [map_smul, hnat]
  exact hx

/-- The sectionwise kernel of a map `φ : A ⟶ B` of presheaves of modules is of finite type as
soon as `A` is of finite type and every finite family of sections of `B` has a finite-type
presheaf of relations. The kernel is given as any submodule `K` of `A` whose membership condition
is `φ x = 0`. -/
theorem isFiniteType_kerSubmodule {A B : PresheafOfModules.{m} S} (φ : A ⟶ B)
    (K : A.Submodule) (hK : ∀ (X : Cᵒᵖ) (x : A.obj X), x ∈ K.obj X ↔ φ.app X x = 0)
    (hA : PresheafOfModules.IsFiniteType J A)
    (hB : ∀ (U : C) (n : ℕ) (s : Fin n → B.obj (op U)),
      PresheafOfModules.IsFiniteType (J.over U) (PresheafOfModules.relations B s)) :
    PresheafOfModules.IsFiniteType J K.toPresheafOfModules := by
  classical
  obtain ⟨I, A', hA', hgen⟩ := hA.exists_generators
  choose p a ha using hgen
  choose Ii W hW hgenW using fun i =>
    (hB (A' i) (p i) (fun j => φ.app (op (A' i)) (a i j))).exists_generators
  refine isFiniteType_presheaf_of_coversTop (fun j : Σ i, Ii i => (W j.1 j.2).left)
    (hA'.over hW) ?_
  rintro ⟨i, k⟩
  obtain ⟨q, c, hc⟩ := hgenW i k
  have hmem : ∀ l : Fin q,
      (∑ jj, (c l).val jj • A.restrictₛₗ (W i k).hom.op (a i jj)) ∈
        K.obj (op (W i k).left) := by
    intro l
    refine sum_smul_mem_submodule φ K hK _ _ _ ?_
    simpa only [LinearMap.mem_ker, Fintype.linearCombination_apply] using (c l).2
  refine ⟨q, fun l => ⟨_, hmem l⟩, ?_⟩
  refine generates_submodule _ _ ?_
  intro Z f t
  obtain ⟨S₀, hS₀, hS₀gen⟩ := ha i Z (f ≫ (W i k).hom) t.val
  refine exists_cover_comb_of_bind _ f t.val hS₀ ?_
  intro Y g hg
  obtain ⟨α, hα⟩ := hS₀gen Y g hg
  have ht0 : φ.app (op Z) t.val = 0 := (hK (op Z) t.val).mp t.2
  have hαmem : α ∈ LinearMap.ker (Fintype.linearCombination (S.obj (op Y))
      (fun jj => B.restrictₛₗ (g ≫ f ≫ (W i k).hom).op
        (φ.app (op (A' i)) (a i jj)))) := by
    rw [LinearMap.mem_ker, Fintype.linearCombination_apply]
    have hφ := congrArg (fun z => φ.app (op Y) z) hα
    have hnat : ∀ {X : C} (e : Y ⟶ X) (z : A.obj (op X)),
        φ.app (op Y) (A.restrictₛₗ e.op z) = B.restrictₛₗ e.op (φ.app (op X) z) :=
      fun e z => PresheafOfModules.naturality_apply φ e.op z
    simp only [map_sum, map_smul, hnat] at hφ
    rw [hφ, ht0]
    exact map_zero _
  obtain ⟨T', hT', hT'gen⟩ :=
    hc (Over.mk (g ≫ f ≫ (W i k).hom)) (Over.homMk (g ≫ f) (by simp)) ⟨α, hαmem⟩
  refine ⟨Sieve.overEquiv (Over.mk (g ≫ f ≫ (W i k).hom)) T',
    (J.mem_over_iff T').mp hT', ?_⟩
  intro Z' k' hk'
  obtain ⟨lam, hlam⟩ := hT'gen (Over.mk (k' ≫ (g ≫ f ≫ (W i k).hom))) (Over.homMk k')
    ((Sieve.overEquiv_iff T' k').mp hk')
  refine ⟨lam, ?_⟩
  have h2 := fun jj => congrArg (fun z => z.val jj) hlam
  simp only [relations_coe_sum, relations_coe_restrict] at h2
  have hres := congrArg (fun z => A.restrictₛₗ k'.op z) hα
  simp only [restrict_sum_smul, restrict_restrict] at hres
  rw [← hres]
  simp only [restrict_sum_smul, Finset.smul_sum, smul_smul, Category.assoc]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun jj _ => ?_
  rw [← Finset.sum_smul,
    restrict_arrow_congr A
      (show (((k' ≫ g) ≫ f) ≫ (W i k).hom) = k' ≫ g ≫ f ≫ (W i k).hom by simp) (a i jj)]
  congr 1
  exact h2 jj

section Kernel

variable {R : Sheaf J RingCat.{w}}

/-- The kernel of a map from a sheaf of modules of finite type into a coherent sheaf of modules
is of finite type. -/
theorem isFiniteType_kerObj {M N : SheafOfModules.{m} R} (φ : M ⟶ N)
    (hM : PresheafOfModules.IsFiniteType J M.val)
    (hN : SheafOfModules.IsCoherentOnSite N) :
    PresheafOfModules.IsFiniteType J (SheafOfModules.kerObj φ).val :=
  isFiniteType_kerSubmodule φ.val (SheafOfModules.kerSubmodule φ).toSubmodule
    (SheafOfModules.mem_kerSubmodule φ) hM hN.kernel_isFiniteType

end Kernel

end Stacks.SheafOfModules

end
