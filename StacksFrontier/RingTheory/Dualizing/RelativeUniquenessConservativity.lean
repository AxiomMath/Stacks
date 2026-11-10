module

public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.RingTheory.Dualizing.Relative
public import Mathlib.RingTheory.Kaehler.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.Homology.DerivedCategory.IsZero

/-!
# Conservativity of `Δ^! ∘ p₁^*`

Let `R → A` be a flat ring map of finite type, `B = A ⊗[R] A`, `p₁ : A → B` the left coprojection
and `Δ : B → A` the multiplication map. The functor `T = Δ^! ∘ p₁^*`, i.e.
`Y ↦ RHom_B(A, Y ⊗ᴸ_A B)`, is the functor in which the defining condition of a relative dualizing
complex ([stacks 0E2C]) is stated. This file proves that `T` is **conservative**: `T(Y) = 0`
forces `Y = 0`, for every object `Y` of `D(A)`, with no finiteness hypothesis on `Y`.

The argument. Choose generators `t₁, …, tₙ` of `ker Δ`. If `T(Y) = 0` then, by the adjunction
`Δ_* ⊣ Δ^!`, no shift of a `B`-module killed by `ker Δ` maps nontrivially to `p₁^*Y`.
Multiplication by `t₁` is then bijective on maps from modules killed by `(t₂, …, tₙ)` (dévissage
through the kernel and cokernel of `t₁`), so the cone of `t₁` on `p₁^*Y` receives no nonzero map
from such modules; iterating, the iterated cone of `t₁, …, tₙ` receives no nonzero map from any
shift of `B`, so it is zero. Finally, restricted along `p₁`, `Y` is a retract of that iterated
cone: the map `B ⊗_A Y → Y`, `b ⊗ y ↦ Δ(b) y`, kills every `tᵢ` and so extends along the cones, and
it is split by `y ↦ 1 ⊗ y`.

## Main results

* `Dualizing.Conservativity.Vanish.mappingCone` — the torsion step.
* `Dualizing.Conservativity.acyclic_of_acyclic_coneSeq` — the retraction along a section.
* `Dualizing.Conservativity.isZero_of_isZero_derivedHom_diagonalDerivedExtension` —
  **conservativity of `Δ^! ∘ p₁^*`**.

## References

* [Stacks Project, Tag 0E2C](https://stacks.math.columbia.edu/tag/0E2C)
* [Stacks Project, Tag 0E2D](https://stacks.math.columbia.edu/tag/0E2D)
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe w u

namespace Dualizing.Conservativity

section Triangulated

variable {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

/-- In a distinguished triangle whose third object maps trivially to `W`, together with its
shift by `-1`, precomposition with the first morphism is a bijection onto maps into `W`. -/
lemma bijective_precomp_mor₁ (T : Triangle C) (hT : T ∈ distTriang C) (W : C)
    (h₃ : ∀ φ : T.obj₃ ⟶ W, φ = 0) (h₃' : ∀ φ : T.obj₃⟦(-1 : ℤ)⟧ ⟶ W, φ = 0) :
    Function.Bijective (fun f : T.obj₂ ⟶ W => T.mor₁ ≫ f) := by
  constructor
  · intro f g hfg
    rw [← sub_eq_zero]
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ T hT (f - g)
      (by simp only [Preadditive.comp_sub]; exact sub_eq_zero.mpr hfg)
    rw [hk, h₃ k, comp_zero]
  · intro g
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT) g (h₃' _)
    exact ⟨k, hk.symm⟩

/-- In a distinguished triangle whose first object maps trivially to `W`, together with its
shift by `1`, precomposition with the second morphism is a bijection onto maps into `W`. -/
lemma bijective_precomp_mor₂ (T : Triangle C) (hT : T ∈ distTriang C) (W : C)
    (h₁ : ∀ φ : T.obj₁ ⟶ W, φ = 0) (h₁' : ∀ φ : T.obj₁⟦(1 : ℤ)⟧ ⟶ W, φ = 0) :
    Function.Bijective (fun f : T.obj₃ ⟶ W => T.mor₂ ≫ f) := by
  constructor
  · intro f g hfg
    rw [← sub_eq_zero]
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₃ T hT (f - g)
      (by simp only [Preadditive.comp_sub]; exact sub_eq_zero.mpr hfg)
    rw [hk, h₁' k, comp_zero]
  · intro g
    obtain ⟨k, hk⟩ := Triangle.yoneda_exact₂ T hT g (h₁ _)
    exact ⟨k, hk.symm⟩

end Triangulated

section Modules

variable {B : Type u} [CommRing B] [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- `Vanish J W`: every map from a shift of a module annihilated by `J`, placed in degree zero,
to `W` vanishes. -/
def Vanish (J : Ideal B) (W : DerivedCategory (ModuleCat.{u} B)) : Prop :=
  ∀ (M : ModuleCat.{u} B), (∀ j ∈ J, ∀ m : M, j • m = 0) →
    ∀ (q : ℤ) (φ : ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)⟦q⟧ ⟶ W), φ = 0

/-- If `Vanish J W` holds, then every map to `W` from a twice-shifted module `M⟦q⟧⟦a⟧`, with `M`
annihilated by `J` and placed in degree zero, vanishes. -/
lemma Vanish.shift_source {J : Ideal B} {W : DerivedCategory (ModuleCat.{u} B)}
    (hV : Vanish J W) (M : ModuleCat.{u} B) (hM : ∀ j ∈ J, ∀ m : M, j • m = 0) (q a : ℤ)
    (φ : ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)⟦q⟧⟦a⟧ ⟶ W) : φ = 0 := by
  have e := (shiftFunctorAdd' (DerivedCategory (ModuleCat.{u} B)) q a (q + a) rfl).app
    ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)
  have h0 := hV M hM (q + a) (e.hom ≫ φ)
  simpa using congrArg (fun g => e.inv ≫ g) h0

/-- `Vanish J` is stable under shifting the target: `Vanish J W` implies `Vanish J (W⟦a⟧)`. -/
lemma Vanish.shift {J : Ideal B} {W : DerivedCategory (ModuleCat.{u} B)}
    (hV : Vanish J W) (a : ℤ) : Vanish J (W⟦a⟧) := by
  intro M hM q φ
  have h0 := hV.shift_source M hM q (-a)
    (φ⟦-a⟧' ≫ (shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} B)) a (-a)
      (add_neg_cancel a)).hom.app W)
  have h1 : φ⟦-a⟧' = 0 := by
    simpa using congrArg (fun g => g ≫ (shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} B))
      a (-a) (add_neg_cancel a)).inv.app W) h0
  exact (shiftFunctor (DerivedCategory (ModuleCat.{u} B)) (-a)).map_injective
    (by rw [h1, Functor.map_zero])

/-- Acting twice by a unit `ε` of `ℤ` on a morphism is the identity: `ε • ε • f = f`. -/
lemma units_smul_smul_self {X Y : DerivedCategory (ModuleCat.{u} B)} (ε : ℤˣ) (f : X ⟶ Y) :
    ε • ε • f = f := by
  rw [smul_smul, Int.units_mul_self, one_smul]

/-- If precomposition with `ε • a` is bijective for a unit `ε` of `ℤ`, so is precomposition
with `a`. -/
private lemma bijective_precomp_of_units_smul {X Y W : DerivedCategory (ModuleCat.{u} B)}
    (ε : ℤˣ) (a : X ⟶ Y) (h : Function.Bijective (fun g : Y ⟶ W => (ε • a) ≫ g)) :
    Function.Bijective (fun g : Y ⟶ W => a ≫ g) := by
  have e : (fun g : Y ⟶ W => a ≫ g) = (fun g => ε • g) ∘ (fun g => (ε • a) ≫ g) := by
    funext g
    simp only [Function.comp_apply, Linear.units_smul_comp]
    exact (units_smul_smul_self _ _).symm
  rw [e]
  exact (MulAction.bijective _).comp h

/-- Multiplication by `t` is bijective on maps from a shifted module killed by `J` into an object
that receives no maps from shifted modules killed by `J + (t)`. -/
lemma bijective_smul (J : Ideal B) (t : B) {W : DerivedCategory (ModuleCat.{u} B)}
    (hV : Vanish (J ⊔ Ideal.span {t}) W) (M : ModuleCat.{u} B)
    (hM : ∀ j ∈ J, ∀ m : M, j • m = 0) (q : ℤ) :
    Function.Bijective
      (fun φ : ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)⟦q⟧ ⟶ W => t • φ) := by
  let F := DerivedCategory.singleFunctor (ModuleCat.{u} B) 0
  let f : M →ₗ[B] M := t • LinearMap.id
  have kill : ∀ (N : ModuleCat.{u} B), (∀ j ∈ J, ∀ n : N, j • n = 0) →
      (∀ n : N, t • n = 0) → ∀ j ∈ J ⊔ Ideal.span {t}, ∀ n : N, j • n = 0 := by
    intro N hJ ht j hj n
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp hj
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    rw [add_smul, hJ y hy, mul_smul, ht, smul_zero, add_zero]
  -- the kernel sequence `0 → ker → M → range f → 0`
  let S₁ := LinearMap.shortComplexKer f.rangeRestrict
  have hS₁ : S₁.ShortExact := LinearMap.shortExact_shortComplexKer f.surjective_rangeRestrict
  -- the cokernel sequence `0 → range f → M → M / range f → 0`
  let S₂ := ModuleCat.shortComplexOfCompEqZero (LinearMap.range f).subtype
    (LinearMap.range f).mkQ (by ext x; simp)
  have hS₂ : S₂.ShortExact := ModuleCat.shortComplex_shortExact S₂
    (LinearMap.exact_subtype_mkQ _) (Submodule.injective_subtype _) (Submodule.mkQ_surjective _)
  have hker : ∀ j ∈ J ⊔ Ideal.span {t}, ∀ n : S₁.X₁, j • n = 0 := by
    refine kill _ (fun j hj n => Subtype.ext ?_) (fun n => Subtype.ext ?_)
    · exact hM j hj n.1
    · have h := congrArg Subtype.val (LinearMap.mem_ker.mp n.2)
      exact h
  have hcok : ∀ j ∈ J ⊔ Ideal.span {t}, ∀ n : S₂.X₃, j • n = 0 := by
    refine kill _ (fun j hj n => ?_) (fun n => ?_)
    · obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ n
      change j • Submodule.Quotient.mk m = 0
      rw [← Submodule.Quotient.mk_smul, hM j hj m, Submodule.Quotient.mk_zero]
    · obtain ⟨m, rfl⟩ := Submodule.mkQ_surjective _ n
      change t • Submodule.Quotient.mk m = 0
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact ⟨m, by simp [f]⟩
  let a := (F.map S₁.g)⟦q⟧'
  let b := (F.map S₂.f)⟦q⟧'
  have hab : t • 𝟙 ((F.obj M)⟦q⟧) = a ≫ b := by
    have : t • 𝟙 M = S₁.g ≫ S₂.f := by
      ext x
      simp [S₁, S₂, f]
    simp only [a, b, ← Functor.map_comp, ← this, Functor.map_smul]
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id]
  have key : (fun φ : (F.obj M)⟦q⟧ ⟶ W => t • φ) =
      (fun g => a ≫ g) ∘ (fun φ => b ≫ φ) := by
    funext φ
    simp only [Function.comp_apply]
    rw [← Category.assoc, ← hab, Linear.smul_comp, Category.id_comp]
  rw [key]
  refine Function.Bijective.comp ?_ ?_
  · have hT := Triangle.shift_distinguished _ hS₁.singleTriangle_distinguished q
    have h := bijective_precomp_mor₂ _ hT W
      (fun φ => hV _ hker q φ) (fun φ => hV.shift_source _ hker q 1 φ)
    exact bijective_precomp_of_units_smul q.negOnePow a h
  · have hT := Triangle.shift_distinguished _ hS₂.singleTriangle_distinguished q
    have h := bijective_precomp_mor₁ _ hT W
      (fun φ => hV _ hcok q φ) (fun φ => hV.shift_source _ hcok q (-1) φ)
    exact bijective_precomp_of_units_smul q.negOnePow b h

/-- The third object of a distinguished triangle whose first morphism is multiplication by a
scalar `c` receives only zero maps from any `S` on whose maps into the first object, and into its
shift, `c` acts bijectively. -/
lemma eq_zero_of_triangle_smul {W Z' S : DerivedCategory (ModuleCat.{u} B)} (c : B)
    (f₂ : W ⟶ Z') (f₃ : Z' ⟶ W⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (c • 𝟙 W) f₂ f₃ ∈ distTriang _)
    (hb₀ : Function.Bijective (fun g : S ⟶ W => c • g))
    (hb₁ : Function.Bijective (fun g : S ⟶ W⟦(1 : ℤ)⟧ => c • g)) (φ : S ⟶ Z') : φ = 0 := by
  have h31 : f₃ ≫ (c • 𝟙 W)⟦(1 : ℤ)⟧' = 0 := comp_distTriang_mor_zero₃₁ _ hT
  have h12 : (c • 𝟙 W) ≫ f₂ = 0 := comp_distTriang_mor_zero₁₂ _ hT
  have hs : (c • 𝟙 W)⟦(1 : ℤ)⟧' = c • 𝟙 _ := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  have h3 : φ ≫ f₃ = 0 := by
    apply hb₁.1
    change c • (φ ≫ f₃) = c • 0
    rw [smul_zero, ← Category.comp_id (φ ≫ f₃), ← Linear.comp_smul, ← hs, Category.assoc,
      h31, comp_zero]
  obtain ⟨g, rfl⟩ := Triangle.coyoneda_exact₃ _ hT φ h3
  obtain ⟨g', hg'⟩ := hb₀.2 g
  change c • g' = g at hg'
  change g ≫ f₂ = 0
  rw [← hg', ← Category.comp_id g', ← Linear.comp_smul, Category.assoc, h12, comp_zero]

/-- **The torsion step.** If `Q(X)` receives no maps from shifted modules killed by `J + (t)`,
then the cone of multiplication by `t` on `X` receives no maps from shifted modules killed by
`J`. -/
lemma Vanish.mappingCone (J : Ideal B) (t : B) (X : CochainComplex (ModuleCat.{u} B) ℤ)
    (hV : Vanish (J ⊔ Ideal.span {t}) (DerivedCategory.Q.obj X)) :
    Vanish J (DerivedCategory.Q.obj (CochainComplex.mappingCone (t • 𝟙 X))) := by
  intro M hM q φ
  have hmor : DerivedCategory.Q.map (t • 𝟙 X) = t • 𝟙 (DerivedCategory.Q.obj X) := by
    rw [Functor.map_smul, CategoryTheory.Functor.map_id]
  have hT : Triangle.mk (t • 𝟙 (DerivedCategory.Q.obj X))
      (DerivedCategory.Q.map (CochainComplex.mappingCone.inr (t • 𝟙 X)))
      (DerivedCategory.Q.mapTriangle.obj
        (CochainComplex.mappingCone.triangle (t • 𝟙 X))).mor₃ ∈ distTriang _ := by
    rw [← hmor]
    exact DerivedCategory.mappingCone_triangle_distinguished _
  exact eq_zero_of_triangle_smul t _ _ hT (bijective_smul J t hV M hM q)
    (bijective_smul J t (hV.shift 1) M hM q) φ

/-- An object of `D(B)` receiving no map from any shift of `B` itself is zero. -/
lemma isZero_of_vanish_bot {W : DerivedCategory (ModuleCat.{u} B)} (hV : Vanish ⊥ W) :
    IsZero W := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  have : Projective (ModuleCat.of B B) :=
    ModuleCat.projective_of_free (Module.Basis.singleton PUnit.{1} B)
  let e := ((DerivedCategory.singleFunctors (ModuleCat.{u} B)).shiftIso (-n) n 0
    (neg_add_cancel n)).app (ModuleCat.of B B)
  suffices h : ∀ x : (DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj W, x = 0 by
    have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj W) :=
      ⟨fun x y => by rw [h x, h y]⟩
    exact ModuleCat.isZero_of_subsingleton _
  intro x
  have hφ : ∀ φ : (DerivedCategory.singleFunctor (ModuleCat.{u} B) n).obj (ModuleCat.of B B) ⟶ W,
      φ = 0 := fun φ => by
    have := hV (ModuleCat.of B B) (by simp) (-n) (e.hom ≫ φ)
    simpa using congrArg (fun g => e.inv ≫ g) this
  let ψ : ModuleCat.of B B ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{u} B) n).obj W :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton B _ x)
  obtain ⟨φ, hφψ⟩ :=
    (DerivedCategory.homologyFromSingleAddEquiv (ModuleCat.of B B) W n).surjective ψ
  have h0 : ψ = 0 := by rw [← hφψ, hφ φ, map_zero]
  have := congrArg (fun g => g.hom (1 : B)) h0
  simpa [ψ] using this

/-- The iterated cone of multiplication by the elements of a list. -/
noncomputable def coneSeq : CochainComplex (ModuleCat.{u} B) ℤ → List B →
    CochainComplex (ModuleCat.{u} B) ℤ
  | X, [] => X
  | X, t :: ts => coneSeq (CochainComplex.mappingCone (t • 𝟙 X)) ts

/-- If `Q(X)` receives no maps from shifted modules killed by `J` and the elements of `ts`, then
the iterated cone `coneSeq X ts` receives no maps from shifted modules killed by `J`. -/
lemma Vanish.coneSeq (ts : List B) : ∀ (J : Ideal B) (X : CochainComplex (ModuleCat.{u} B) ℤ),
    Vanish (J ⊔ Ideal.span {x | x ∈ ts}) (DerivedCategory.Q.obj X) →
      Vanish J (DerivedCategory.Q.obj (Conservativity.coneSeq X ts)) := by
  induction ts with
  | nil =>
    intro J X hV
    simpa [Conservativity.coneSeq] using hV
  | cons t ts ih =>
    intro J X hV
    refine ih J _ (Vanish.mappingCone _ t X ?_)
    have : J ⊔ Ideal.span {x | x ∈ t :: ts} = J ⊔ Ideal.span {x | x ∈ ts} ⊔ Ideal.span {t} := by
      have hs : {x | x ∈ t :: ts} = insert t {x | x ∈ ts} := by
        ext x; simp
      rw [hs, Ideal.span_insert, sup_comm (Ideal.span {t}), sup_assoc]
    rwa [← this]

omit [HasDerivedCategory.{w} (ModuleCat.{u} B)] in
/-- A chain map into a complex killed by every element of a list extends along the iterated cone
of multiplication by those elements. -/
lemma exists_coneSeq_retraction (ts : List B) : ∀ (X Y : CochainComplex (ModuleCat.{u} B) ℤ)
    (_ : ∀ t ∈ ts, t • 𝟙 Y = 0) (r : X ⟶ Y),
      ∃ (ι : X ⟶ Conservativity.coneSeq X ts) (ρ : Conservativity.coneSeq X ts ⟶ Y), ι ≫ ρ = r := by
  induction ts with
  | nil => exact fun X Y _ r => ⟨𝟙 X, r, Category.id_comp r⟩
  | cons t ts ih =>
    intro X Y hY r
    have hr : (t • 𝟙 X) ≫ r = 0 := by
      rw [Linear.smul_comp, Category.id_comp, ← Category.comp_id r, ← Linear.comp_smul,
        hY t (List.mem_cons_self), comp_zero]
    let r' := CochainComplex.mappingCone.desc (t • 𝟙 X) 0 r (by simp [hr])
    obtain ⟨ι, ρ, h⟩ := ih _ Y (fun t' ht' => hY t' (List.mem_cons_of_mem _ ht')) r'
    have key : CochainComplex.mappingCone.inr (t • 𝟙 X) ≫ ι ≫ ρ = r := by
      rw [h, CochainComplex.mappingCone.inr_desc]
    refine ⟨(CochainComplex.mappingCone.inr (t • 𝟙 X) ≫ ι :), ρ, ?_⟩
    exact (Category.assoc _ ι ρ).trans key

end Modules

section Retract

variable {A B : Type u} [CommRing A] [CommRing B]
  [HasDerivedCategory.{w} (ModuleCat.{u} A)] [HasDerivedCategory.{w} (ModuleCat.{u} B)]

/-- A cochain complex is zero in the derived category if and only if it is acyclic. -/
lemma isZero_Q_obj_iff {R : Type u} [Ring R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsZero (DerivedCategory.Q.obj K) ↔ K.Acyclic := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  refine forall_congr' fun n => ?_
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact ⟨fun h => h.of_iso ((DerivedCategory.homologyFunctorFactors _ n).app K).symm,
    fun h => h.of_iso ((DerivedCategory.homologyFunctorFactors _ n).app K)⟩

omit [HasDerivedCategory.{w} (ModuleCat.{u} B)] in
/-- **The retraction argument.** Let `p : A → B` be a ring map with a retraction `Δ`, let `P` be
a complex of `A`-modules and `ts` a list of elements of `ker Δ`. If the iterated cone of
multiplication by `ts` on the base change of `P` along `p` is acyclic, then `P` is acyclic. -/
lemma acyclic_of_acyclic_coneSeq (p : A →+* B) (Δ : B →+* A) (hΔ : Δ.comp p = RingHom.id A)
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (ts : List B) (hts : ∀ t ∈ ts, Δ t = 0)
    (h : (coneSeq ((CochainComplex.extendScalars p).obj P) ts).Acyclic) : P.Acyclic := by
  let adj := ModuleCat.extendRestrictScalarsAdj p
  let e : 𝟭 (ModuleCat.{u} A) ≅ ModuleCat.restrictScalars Δ ⋙ ModuleCat.restrictScalars p :=
    (ModuleCat.restrictScalarsId' (RingHom.id A) rfl).symm ≪≫
      ModuleCat.restrictScalarsComp' p Δ (RingHom.id A) hΔ.symm
  let θ : ModuleCat.extendScalars p ⟶ ModuleCat.restrictScalars Δ :=
    { app := fun M => (adj.homEquiv _ _).symm (e.hom.app M)
      naturality := fun M N f => by
        rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
        congr 1 }
  have hunit : ∀ M, adj.unit.app M ≫ (ModuleCat.restrictScalars p).map (θ.app M) =
      e.hom.app M := fun M => by
    exact (adj.homEquiv_unit _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  let c := ComplexShape.up ℤ
  let X := (CochainComplex.extendScalars p).obj P
  let Y := ((ModuleCat.restrictScalars Δ).mapHomologicalComplex c).obj P
  let r : X ⟶ Y := (NatTrans.mapHomologicalComplex θ c).app P
  have hY : ∀ t ∈ ts, t • 𝟙 Y = 0 := by
    intro t ht
    ext n x
    change t • x = 0
    rw [ModuleCat.restrictScalars.smul_def, hts t ht, zero_smul]
    rfl
  obtain ⟨ι, ρ, hιρ⟩ := exists_coneSeq_retraction ts X Y hY r
  let G := (ModuleCat.restrictScalars p).mapHomologicalComplex c
  have hres : (G.obj (coneSeq X ts)).Acyclic := by
    rw [← CochainComplex.restrictScalars_acyclic_iff p] at h
    exact h
  let U : P ⟶ G.obj X := (NatTrans.mapHomologicalComplex adj.unit c).app P
  have hkey : U ≫ G.map r = ((NatIso.mapHomologicalComplex e c).hom.app P : P ⟶ G.obj Y) := by
    ext n : 1
    exact hunit (P.X n)
  have hzero : IsZero (DerivedCategory.Q.obj (G.obj (coneSeq X ts))) :=
    (isZero_Q_obj_iff _).mpr hres
  have hQ : DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex e c).hom.app P : P ⟶ G.obj Y) = 0 := by
    have h1 : U ≫ G.map r = U ≫ G.map ι ≫ G.map ρ := by rw [← G.map_comp, hιρ]
    rw [← hkey, h1, Functor.map_comp, Functor.map_comp,
      hzero.eq_of_src (DerivedCategory.Q.map (G.map ρ)) 0, comp_zero, comp_zero]
  rw [← isZero_Q_obj_iff]
  have hiso : IsIso (DerivedCategory.Q.map
      ((NatIso.mapHomologicalComplex e c).hom.app P : P ⟶ G.obj Y)) := inferInstance
  rw [hQ] at hiso
  rw [IsZero.iff_id_eq_zero]
  exact (@IsIso.hom_inv_id _ _ _ _ _ hiso).symm.trans (zero_comp)

end Retract

section Diagonal

attribute [local instance] HasDerivedCategory.standard

open scoped TensorProduct

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]

/-- Derived Hom along the multiplication map, after derived base change along the left
coprojection, is conservative: it kills only the zero object. -/
theorem isZero_of_isZero_derivedHom_diagonalDerivedExtension [Module.Flat R A]
    [Algebra.FiniteType R A] (Y : DerivedCategory (ModuleCat.{u} A))
    (hY : IsZero ((derivedHom.{u, u}
      (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom).obj
        ((diagonalDerivedExtension R A).obj Y))) : IsZero Y := by
  let Δ : A ⊗[R] A →+* A := (Algebra.TensorProduct.lmul' R : A ⊗[R] A →ₐ[R] A).toRingHom
  let p₁ : A →+* A ⊗[R] A := Algebra.TensorProduct.includeLeftRingHom
  have hΔ : Δ.comp p₁ = RingHom.id A := by
    ext a; simp [Δ, p₁]
  let P := DerivedCategory.Q.objPreimage Y
  let eP : DerivedCategory.Q.obj P ≅ Y := DerivedCategory.Q.objObjPreimageIso Y
  let X₀ := (CochainComplex.extendScalars p₁).obj P
  have hD : IsZero ((derivedHom.{u, u} Δ).obj (DerivedCategory.Q.obj X₀)) :=
    hY.of_iso ((derivedHom.{u, u} Δ).mapIso (diagonalDerivedExtensionIso R A Y P eP)).symm
  -- generators of the diagonal ideal
  have : Algebra.EssFiniteType R A := inferInstance
  obtain ⟨s, hs⟩ := KaehlerDifferential.ideal_fg R A
  let ts := s.toList
  have hspan : Ideal.span {x | x ∈ ts} = RingHom.ker Δ := by
    have : {x | x ∈ ts} = (s : Set (A ⊗[R] A)) := by ext x; simp [ts]
    rw [this, hs]
    rfl
  -- the base case of the torsion induction
  obtain ⟨adj⟩ := restrictScalarsDerived_adj_derivedHom.{u, u, u} Δ
  have hbase : Vanish (RingHom.ker Δ) (DerivedCategory.Q.obj X₀) := by
    intro M hM q φ
    let W := (ModuleCat.restrictScalars p₁).obj M
    have hsmul : ∀ (b : A ⊗[R] A) (m : M), p₁ (Δ b) • m = b • m := by
      intro b m
      have hb : b - p₁ (Δ b) ∈ RingHom.ker Δ := by
        rw [RingHom.mem_ker, map_sub]
        have := congrArg (fun g => g (Δ b)) hΔ
        simp only [RingHom.comp_apply, RingHom.id_apply] at this
        rw [this, sub_self]
      have := hM _ hb m
      rw [sub_smul, sub_eq_zero] at this
      exact this.symm
    let iM : (ModuleCat.restrictScalars Δ).obj W ≅ M :=
      (AddEquiv.toLinearEquiv (M := ↑((ModuleCat.restrictScalars Δ).obj W)) (M₂ := ↑M)
        (AddEquiv.refl _) (fun b x => hsmul b x)).toModuleIso
    let L := (ModuleCat.restrictScalars.{u} Δ).mapDerivedCategory
    let e₁ : L.obj (((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj W)⟦q⟧) ≅
        ((DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).obj M)⟦q⟧ :=
      (L.commShiftIso q).app _ ≪≫ (shiftFunctor _ q).mapIso
        (((ModuleCat.restrictScalars.{u} Δ).mapDerivedCategorySingleFunctor 0).app W ≪≫
          (DerivedCategory.singleFunctor (ModuleCat.{u} (A ⊗[R] A)) 0).mapIso iM)
    have h0 : e₁.hom ≫ φ = 0 := by
      have hf : adj.homEquiv _ _ (e₁.hom ≫ φ) = 0 := hD.eq_of_tgt _ _
      calc e₁.hom ≫ φ = (adj.homEquiv _ _).symm (adj.homEquiv _ _ (e₁.hom ≫ φ)) :=
            (Equiv.symm_apply_apply _ _).symm
        _ = 0 := by rw [hf, adj.homEquiv_counit, Functor.map_zero, zero_comp]
    simpa using congrArg (fun g => e₁.inv ≫ g) h0
  have hcone : Vanish ⊥ (DerivedCategory.Q.obj (coneSeq X₀ ts)) := by
    refine Vanish.coneSeq ts ⊥ X₀ ?_
    rwa [bot_sup_eq, hspan]
  have hac := (isZero_Q_obj_iff _).mp (isZero_of_vanish_bot hcone)
  have hP := acyclic_of_acyclic_coneSeq p₁ Δ hΔ P ts
    (fun t ht => by
      rw [← RingHom.mem_ker, ← hspan]
      exact Ideal.subset_span ht) hac
  exact ((isZero_Q_obj_iff P).mpr hP).of_iso eP.symm

end Diagonal

end Dualizing.Conservativity
