module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedIdempotents
public import Mathlib.RingTheory.Idempotents

/-!
# Product decompositions of the structure sheaf of a ringed site from global idempotents

Let `(C, O)` be a ringed site and let `(e_n)_{n ∈ ℤ}` be a family of global sections of `O`
which are idempotent and pairwise orthogonal, and which are *locally finite and complete*: every
object of the site has a covering on whose members all but finitely many `e_n` vanish and the
remaining ones sum to `1`. Then `O = ∏_{n ∈ ℤ} e_n O` is a locally finite direct product
decomposition of the structure sheaf in the sense of clause (2) of Stacks 0FPY, the `n`-th factor
being the sheaf of corner rings `U ↦ e_n O(U)`. A module on which `e_n` acts as the identity is a
module over the `n`-th factor.

## Main definitions

* `AlgebraicGeometry.RingedSite.InvertibleDerived.GlobalSection`: a global section of `O`, as a
  family of sections compatible with the restriction maps.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.LocallyFiniteIdempotents`: a locally finite
  complete family of orthogonal idempotent global sections.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.LocallyFiniteIdempotents.factor`: the sheaf of
  corner rings `U ↦ e_n O(U)`.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.LocallyFiniteIdempotents.productDecomposition`:
  the resulting `ProductDecomposition` of `O`.
* `AlgebraicGeometry.RingedSite.InvertibleDerived.LocallyFiniteIdempotents.factorModule`: a module
  on which `e_n` acts as the identity, as a module over the `n`-th factor.

## Main results

* `AlgebraicGeometry.RingedSite.InvertibleDerived.LocallyFiniteIdempotents.toOModFactorModuleIso`:
  the factor module, read back as an `O`-module, is the module one started with.

## Implementation notes

This is the site counterpart of `Stacks.Cohomology.InvertibleDerived.LocallyFiniteIdempotents`,
which is written over the opens of a topological space and glues along open covers. Here a
global section is a compatible family of sections over all objects of the site, the covers are
covering sieves, and gluing is the sheaf condition of the underlying sheaf of sets of `O`. The
ring-theoretic lemmas about corners and the identification of a product presentation with a limit
fan are taken from the ringed-space file, where they are stated for arbitrary rings and sites.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.RingedSite.InvertibleDerived

open Stacks.Cohomology.InvertibleDerived (mem_corner_iff_of_comm idem_mul_mul)

variable {X : RingedSite.{u, u, u}}

/-! ### The sheaf of sets underlying the structure sheaf -/

variable (X) in
/-- The sections of the structure sheaf of a ringed site form a sheaf of sets. -/
theorem isSheaf_types : Presieve.IsSheaf X.J (X.O.obj ⋙ forget CommRingCat.{u}) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    ((Presheaf.isSheaf_iff_isSheaf_forget X.J X.O.obj (forget CommRingCat.{u})).1 X.O.property)

/-- Two sections of `O` which agree on the members of a covering sieve agree. -/
theorem eq_of_locally_eq {U : X.C} {S : Sieve U} (hS : S ∈ X.J U)
    (s t : (X.O.obj.obj (op U) : Type u))
    (h : ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f → X.O.obj.map f.op s = X.O.obj.map f.op t) : s = t :=
  (isSheaf_types X S hS).isSeparatedFor.ext fun _ f hf => h f hf

/-- A family of sections of `O` over the members of a covering sieve which agree on every common
refinement glues. -/
theorem exists_glue {U : X.C} {S : Sieve U} (hS : S ∈ X.J U)
    (x : ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f → (X.O.obj.obj (op V) : Type u))
    (hx : ∀ ⦃V₁ V₂ W : X.C⦄ (g₁ : W ⟶ V₁) (g₂ : W ⟶ V₂) (f₁ : V₁ ⟶ U) (f₂ : V₂ ⟶ U)
      (h₁ : S f₁) (h₂ : S f₂), g₁ ≫ f₁ = g₂ ≫ f₂ →
        X.O.obj.map g₁.op (x f₁ h₁) = X.O.obj.map g₂.op (x f₂ h₂)) :
    ∃ s : (X.O.obj.obj (op U) : Type u), ∀ ⦃V : X.C⦄ (f : V ⟶ U) (hf : S f),
      X.O.obj.map f.op s = x f hf := by
  obtain ⟨s, hs, -⟩ := isSheaf_types X S hS (fun V f hf => x f hf)
    (fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ w => hx g₁ g₂ f₁ f₂ h₁ h₂ w)
  exact ⟨s, fun V f hf => hs f hf⟩

/-! ### Global sections -/

variable (X) in
/-- A **global section** of the structure sheaf: a section over every object of the site,
compatible with the restriction maps. -/
structure GlobalSection where
  /-- The section over each object. -/
  val (U : X.Cᵒᵖ) : (X.O.obj.obj U : Type u)
  /-- Compatibility with restriction. -/
  map_val ⦃U V : X.Cᵒᵖ⦄ (f : U ⟶ V) : X.O.obj.map f (val U) = val V

namespace GlobalSection

/-- Two global sections with the same sections are equal. -/
@[ext]
theorem ext {s t : GlobalSection X} (h : ∀ U, s.val U = t.val U) : s = t := by
  obtain ⟨s, hs⟩ := s
  obtain ⟨t, ht⟩ := t
  obtain rfl : s = t := funext h
  rfl

/-- The product of two global sections. -/
instance : Mul (GlobalSection X) where
  mul s t := ⟨fun U => s.val U * t.val U, fun U V f => by rw [map_mul, s.map_val, t.map_val]⟩

/-- The global section `1`. -/
instance : One (GlobalSection X) where
  one := ⟨fun _ => 1, fun _ _ _ => map_one _⟩

/-- The global section `0`. -/
instance : Zero (GlobalSection X) where
  zero := ⟨fun _ => 0, fun _ _ _ => map_zero _⟩

/-- The sections of a product are the products of the sections. -/
@[simp]
theorem mul_val (s t : GlobalSection X) (U : X.Cᵒᵖ) : (s * t).val U = s.val U * t.val U := rfl

/-- The sections of the global section `1` are `1`. -/
@[simp]
theorem one_val (U : X.Cᵒᵖ) : (1 : GlobalSection X).val U = 1 := rfl

/-- The sections of the global section `0` are `0`. -/
@[simp]
theorem zero_val (U : X.Cᵒᵖ) : (0 : GlobalSection X).val U = 0 := rfl

end GlobalSection

/-- A section of `O`, read as a scalar for `O`-modules. -/
abbrev ringSec {U : X.Cᵒᵖ} (a : (X.O.obj.obj U : Type u)) :
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U := a

/-! ### Locally finite families of idempotents -/

variable (X) in
/-- **A locally finite complete family of orthogonal idempotents** of `Γ(C, O)`: idempotent,
pairwise orthogonal global sections such that every object of the site has a covering on whose
members all but finitely many of them vanish and the others sum to `1`. -/
structure LocallyFiniteIdempotents where
  /-- The idempotents. -/
  e : ℤ → GlobalSection X
  /-- Each `e n` is idempotent. -/
  idem : ∀ n U, IsIdempotentElem ((e n).val U)
  /-- Distinct idempotents are orthogonal. -/
  ortho : ∀ n m, n ≠ m → ∀ U, (e n).val U * (e m).val U = 0
  /-- On a covering of every object finitely many of the idempotents survive, and they sum to
  `1`. -/
  locallyFinite : ∀ U : X.C, ∃ S : Sieve U, S ∈ X.J U ∧ ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
    ∃ T : Finset ℤ, (∀ n ∉ T, (e n).val (op V) = 0) ∧ ∑ n ∈ T, (e n).val (op V) = 1

namespace LocallyFiniteIdempotents

variable (E : LocallyFiniteIdempotents X)

/-- An object on which only the idempotents indexed by `T` survive, and these sum to `1`. -/
def IsSplitOn (V : X.C) (T : Finset ℤ) : Prop :=
  (∀ n ∉ T, (E.e n).val (op V) = 0) ∧ ∑ n ∈ T, (E.e n).val (op V) = 1

/-- Being split by a finite set of indices passes to objects lying over. -/
theorem IsSplitOn.map {V W : X.C} {T : Finset ℤ} (h : E.IsSplitOn V T) (g : W ⟶ V) :
    E.IsSplitOn W T := by
  refine ⟨fun n hn => ?_, ?_⟩
  · rw [← (E.e n).map_val g.op, h.1 n hn, map_zero]
  · have h2 := congrArg (X.O.obj.map g.op) h.2
    rw [map_sum, map_one] at h2
    simpa only [(E.e _).map_val] using h2

/-- The sieve of arrows over whose source the family splits along a finite set of indices. -/
def splitSieve (U : X.C) : Sieve U where
  arrows V _ := ∃ T : Finset ℤ, E.IsSplitOn V T
  downward_closed := fun ⟨T, hT⟩ g => ⟨T, hT.map E g⟩

/-- The sieve on which the family splits is a covering sieve of every object. -/
theorem splitSieve_mem (U : X.C) : E.splitSieve U ∈ X.J U := by
  obtain ⟨S, hS, h⟩ := E.locallyFinite U
  exact X.J.superset_covering (fun V f hf => h f hf) hS

/-- On a split object every section is the sum of its components. -/
theorem sum_mul {V : X.C} {T : Finset ℤ} (h : E.IsSplitOn V T)
    (s : (X.O.obj.obj (op V) : Type u)) : ∑ n ∈ T, (E.e n).val (op V) * s = s := by
  rw [← Finset.sum_mul, h.2, one_mul]

/-- A section of `O` is determined by its components. -/
theorem eq_of_mul_eq {U : X.C} {s t : (X.O.obj.obj (op U) : Type u)}
    (h : ∀ n, (E.e n).val (op U) * s = (E.e n).val (op U) * t) : s = t := by
  refine eq_of_locally_eq (E.splitSieve_mem U) s t fun V f ⟨T, hT⟩ => ?_
  rw [← E.sum_mul hT (X.O.obj.map f.op s), ← E.sum_mul hT (X.O.obj.map f.op t)]
  refine Finset.sum_congr rfl fun n _ => ?_
  have := congrArg (X.O.obj.map f.op) (h n)
  rwa [map_mul, map_mul, (E.e n).map_val] at this

/-! ### The corner rings -/

/-- The ring of sections of the `n`-th factor over `U`: the corner `e_n O(U)`. -/
abbrev Corner (n : ℤ) (U : X.Cᵒᵖ) : Type u := (E.idem n U).Corner

/-- An element of the corner `e_n O(U)` is fixed by multiplication by `e_n`. -/
theorem mem_corner (n : ℤ) {U : X.Cᵒᵖ} (a : E.Corner n U) : (E.e n).val U * a.1 = a.1 :=
  (mem_corner_iff_of_comm (E.idem n U)).mp a.2

/-- Where `e_n` vanishes, so does its corner. -/
theorem corner_val_eq_zero {n : ℤ} {U : X.Cᵒᵖ} (h : (E.e n).val U = 0) (a : E.Corner n U) :
    a.1 = 0 :=
  (E.mem_corner n a).symm.trans (by simp only [h, zero_mul])

/-- Two elements of a corner ring with the same underlying section are equal. -/
theorem Corner.ext {n : ℤ} {U : X.Cᵒᵖ} {a b : E.Corner n U} (h : a.1 = b.1) : a = b :=
  Subtype.ext h

/-- The element `e_n s` of the corner, for a section `s` of `O`. -/
def toCorner (n : ℤ) {U : X.Cᵒᵖ} (s : (X.O.obj.obj U : Type u)) : E.Corner n U :=
  ⟨(E.e n).val U * s, (mem_corner_iff_of_comm (E.idem n U)).mpr
    (by rw [← mul_assoc, (E.idem n U).eq])⟩

/-- The underlying section of `toCorner n s` is `e_n s`. -/
theorem toCorner_val (n : ℤ) {U : X.Cᵒᵖ} (s : (X.O.obj.obj U : Type u)) :
    (E.toCorner n s).1 = (E.e n).val U * s := rfl

/-- Restriction of sections of the corner rings. -/
def cornerMap (n : ℤ) {U V : X.Cᵒᵖ} (f : U ⟶ V) : E.Corner n U →+* E.Corner n V where
  toFun a := ⟨X.O.obj.map f a.1, (mem_corner_iff_of_comm (E.idem n V)).mpr (by
    rw [← (E.e n).map_val f, ← map_mul, E.mem_corner n a])⟩
  map_one' := Corner.ext E ((E.e n).map_val f)
  map_mul' a b := Corner.ext E (map_mul _ a.1 b.1)
  map_zero' := Corner.ext E (map_zero (X.O.obj.map f).hom)
  map_add' a b := Corner.ext E (map_add _ a.1 b.1)

/-- Restriction in the corner rings is restriction of the underlying sections of `O`. -/
theorem cornerMap_val (n : ℤ) {U V : X.Cᵒᵖ} (f : U ⟶ V) (a : E.Corner n U) :
    (E.cornerMap n f a).1 = X.O.obj.map f a.1 := rfl

/-- The presheaf of corner rings `U ↦ e_n O(U)`. -/
def factorPresheaf (n : ℤ) : X.Cᵒᵖ ⥤ CommRingCat.{u} where
  obj U := CommRingCat.of (E.Corner n U)
  map f := CommRingCat.ofHom (E.cornerMap n f)
  map_id U := by
    ext a
    exact Corner.ext E (ConcreteCategory.congr_hom (X.O.obj.map_id U) a.1)
  map_comp f g := by
    ext a
    exact Corner.ext E (ConcreteCategory.congr_hom (X.O.obj.map_comp f g) a.1)

/-- The presheaf of corner rings is a sheaf: a compatible family of sections of the corners
glues in `O`, and the gluing lies in the corner because that is checked on the covering. -/
theorem isSheaf_factorPresheaf (n : ℤ) : Presheaf.IsSheaf X.J (E.factorPresheaf n) := by
  refine (Presheaf.isSheaf_iff_isSheaf_forget X.J _ (forget CommRingCat.{u})).2
    ((isSheaf_iff_isSheaf_of_type _ _).2 fun U S hS x hx => ?_)
  obtain ⟨t, ht, htu⟩ := isSheaf_types X S hS
    (fun V f hf => ((x f hf).1 : (X.O.obj.obj (op V) : Type u)))
    (fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ w => congrArg Subtype.val (hx g₁ g₂ h₁ h₂ w))
  change (X.O.obj.obj (op U) : Type u) at t
  have hmem : (E.e n).val (op U) * t = t := by
    refine eq_of_locally_eq hS _ _ fun V f hf => ?_
    rw [map_mul, (E.e n).map_val]
    exact (congrArg _ (ht f hf)).trans ((E.mem_corner n (x f hf)).trans (ht f hf).symm)
  exact ⟨⟨t, (mem_corner_iff_of_comm (E.idem n _)).mpr hmem⟩,
    fun V f hf => Corner.ext E (ht f hf),
    fun t' ht' => Corner.ext E (htu t'.1 fun V f hf => congrArg Subtype.val (ht' f hf))⟩

/-- **The `n`-th factor**: the sheaf of corner rings `U ↦ e_n O(U)`. -/
def factor (n : ℤ) : Sheaf X.J CommRingCat.{u} :=
  ⟨E.factorPresheaf n, E.isSheaf_factorPresheaf n⟩

/-- Restriction commutes with the projection to the corner. -/
theorem toCorner_naturality (n : ℤ) {U V : X.Cᵒᵖ} (f : U ⟶ V) (s : (X.O.obj.obj U : Type u)) :
    E.cornerMap n f (E.toCorner n s) = E.toCorner n (X.O.obj.map f s) :=
  Corner.ext E (by rw [cornerMap_val, toCorner_val, toCorner_val, map_mul, (E.e n).map_val])

/-- The projection `O(U) ⟶ e_n O(U)`, `s ↦ e_n s`, as a ring homomorphism. -/
def toCornerHom (n : ℤ) (U : X.Cᵒᵖ) : (X.O.obj.obj U : Type u) →+* E.Corner n U where
  toFun s := E.toCorner n s
  map_one' := Corner.ext E (mul_one _)
  map_mul' s t := Corner.ext E (idem_mul_mul (E.idem n U) s t)
  map_zero' := Corner.ext E (mul_zero _)
  map_add' s t := Corner.ext E (mul_add _ s t)

/-- The projection `O ⟶ O_n` onto the `n`-th factor, as a morphism of sheaves of rings. -/
def proj (n : ℤ) : X.O ⟶ E.factor n :=
  ObjectProperty.homMk
    { app := fun U => CommRingCat.ofHom (E.toCornerHom n U)
      naturality := fun U V f => by
        ext s
        exact (E.toCorner_naturality n f s).symm }

/-- The projection `O ⟶ O_n` sends a section `s` to `e_n s`. -/
theorem proj_app_val (n : ℤ) (U : X.Cᵒᵖ) (s : (X.O.obj.obj U : Type u)) :
    ((E.proj n).hom.app U s).1 = (E.e n).val U * s := rfl

/-- **The sections of `O` are the products of the sections of the factors**: the projections
`O ⟶ O_n` exhibit `O` as the product of the corner sheaves. -/
def productPresentation :
    Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation X.O E.factor where
  π := E.proj
  injective U s t h := by
    induction U with
    | op U => exact E.eq_of_mul_eq fun n => congrArg Subtype.val (h n)
  surjective U a := by
    classical
    induction U with
    | op U =>
    choose T hT using fun (V : X.C) (f : V ⟶ U) (hf : E.splitSieve U f) => hf
    let x : ∀ ⦃V : X.C⦄ (f : V ⟶ U), E.splitSieve U f → (X.O.obj.obj (op V) : Type u) :=
      fun V f hf => ∑ n ∈ T V f hf, X.O.obj.map f.op (a n).1
    have hcomp : ∀ ⦃V : X.C⦄ (f : V ⟶ U) (hf : E.splitSieve U f) (m : ℤ) {W : X.C}
        (g : W ⟶ V), (E.e m).val (op W) * X.O.obj.map g.op (x f hf) =
          X.O.obj.map (g ≫ f).op (a m).1 := by
      intro V f hf m W g
      have hsW : E.IsSplitOn W (T V f hf) := (hT V f hf).map E g
      simp only [x, map_sum, Finset.mul_sum]
      simp_rw [← ConcreteCategory.comp_apply, ← X.O.obj.map_comp, ← op_comp]
      have hterm : ∀ n, (E.e m).val (op W) * X.O.obj.map (g ≫ f).op (a n).1 =
          if n = m then X.O.obj.map (g ≫ f).op (a m).1 else 0 := by
        intro n
        have han := E.mem_corner n (a n)
        split_ifs with hnm
        · subst hnm
          rw [← (E.e n).map_val (g ≫ f).op, ← map_mul, han]
        · rw [← han, map_mul, (E.e n).map_val, ← mul_assoc, E.ortho m n (Ne.symm hnm),
            zero_mul]
      simp_rw [hterm]
      rw [Finset.sum_ite_eq']
      split_ifs with hm
      · rfl
      · rw [← E.mem_corner m (a m), map_mul, (E.e m).map_val, hsW.1 m hm, zero_mul]
    obtain ⟨s, hs⟩ := exists_glue (E.splitSieve_mem U) x
      (fun V₁ V₂ W g₁ g₂ f₁ f₂ h₁ h₂ w => E.eq_of_mul_eq fun m => by
        rw [hcomp f₁ h₁ m g₁, hcomp f₂ h₂ m g₂, w])
    refine ⟨s, fun m => Corner.ext E ?_⟩
    refine eq_of_locally_eq (E.splitSieve_mem U) _ _ fun V f hf => ?_
    change X.O.obj.map f.op ((E.e m).val (op U) * s) = X.O.obj.map f.op (a m).1
    rw [map_mul, (E.e m).map_val, hs f hf]
    have := hcomp f hf m (𝟙 V)
    rwa [op_id, X.O.obj.map_id, ConcreteCategory.id_apply, Category.id_comp] at this

/-- **The product decomposition of `O` cut out by a locally finite complete family of
orthogonal idempotents**: `O = ∏_{n ∈ ℤ} e_n O`. -/
def productDecomposition : ProductDecomposition X where
  factor := E.factor
  presentation := E.productPresentation
  locallyFinite U := by
    refine ⟨(E.splitSieve U).arrows, by rw [Sieve.generate_sieve]; exact E.splitSieve_mem U,
      fun V f ⟨T, hT⟩ => (T : Set ℤ).toFinite.subset fun n hn => ?_⟩
    by_contra hnT
    refine hn ⟨fun a b => Corner.ext E ?_⟩
    exact (E.corner_val_eq_zero (hT.1 n hnT) a).trans (E.corner_val_eq_zero (hT.1 n hnT) b).symm

/-! ### Modules on which an idempotent acts as the identity -/

/-- `e_n` acts as the identity on the `O`-module `F`. -/
def ActsAsOne (n : ℤ) (F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    Prop :=
  ∀ (U : X.Cᵒᵖ) (m : F.val.obj U), ringSec ((E.e n).val U) • m = m

section ActsAsOne

variable {E} {n : ℤ} {F : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  (hF : E.ActsAsOne n F)

/-- The module structure over the corner `e_n O(U)` of the sections of a module on which `e_n`
acts as the identity. -/
abbrev cornerModuleStruct (U : X.Cᵒᵖ) :
    Module ((Stacks.SheafOfModules.Tensor.ringSheaf (E.factor n)).obj.obj U)
      (F.val.presheaf.obj U) where
  smul c m := (ringSec (X := X) (U := U) c.1 • (m : F.val.obj U) : F.val.obj U)
  one_smul m := hF U m
  mul_smul a b m := mul_smul (ringSec (X := X) (U := U) a.1) (ringSec (X := X) (U := U) b.1)
    (m : F.val.obj U)
  smul_zero a := smul_zero (A := F.val.obj U) (ringSec (X := X) (U := U) a.1)
  smul_add a m m' := smul_add (ringSec (X := X) (U := U) a.1) (m : F.val.obj U) m'
  add_smul a b m := add_smul (ringSec (X := X) (U := U) a.1) (ringSec (X := X) (U := U) b.1)
    (m : F.val.obj U)
  zero_smul m := zero_smul _ (m : F.val.obj U)

/-- **A module on which `e_n` acts as the identity, as a module over the `n`-th factor.** -/
def factorModule : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (E.factor n)) :=
  letI := cornerModuleStruct hF
  { val := PresheafOfModules.ofPresheaf F.val.presheaf fun {U _V} f c m =>
      F.val.map_smul f (ringSec (X := X) (U := U) c.1) (m : F.val.obj U)
    isSheaf := F.isSheaf }

include hF in
/-- If `e_n` acts as the identity on `F`, then `e_n r` acts on `F` as `r` does. -/
theorem smul_eq_of_actsAsOne (U : X.Cᵒᵖ)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj U) (m : F.val.obj U) :
    (ringSec ((E.e n).val U) * r) • m = r • m := by
  have hc : ringSec ((E.e n).val U) * r = r * ringSec ((E.e n).val U) :=
    mul_comm (G := (X.O.obj.obj U : Type u)) ((E.e n).val U) r
  exact (congrArg (· • m) hc).trans ((mul_smul r _ m).trans (congrArg (r • ·) (hF U m)))

/-- **The factor module of `F`, read back as an `O`-module, is `F`.** -/
def toOModFactorModuleIso : (E.productDecomposition.toOMod n).obj (factorModule hF) ≅ F where
  hom := ⟨PresheafOfModules.homMk (𝟙 F.val.presheaf) fun U r m =>
    smul_eq_of_actsAsOne hF U r m⟩
  inv := ⟨PresheafOfModules.homMk (𝟙 F.val.presheaf) fun U r m =>
    (smul_eq_of_actsAsOne hF U r m).symm⟩
  hom_inv_id := rfl
  inv_hom_id := rfl

end ActsAsOne

end LocallyFiniteIdempotents

end AlgebraicGeometry.RingedSite.InvertibleDerived

end
