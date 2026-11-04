module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.AlgebraicTopology.Decalage
public import StacksFrontier.AlgebraicTopology.SimplicialHomotopyTensor

/-!
# Connectivity of the degreewise tensor product of simplicial modules

Let `M` and `N` be simplicial modules over a commutative ring `B`, let `M` be degreewise flat and
let the Moore complex of `M` have vanishing homology in degree zero. If the Moore complex of `N`
has vanishing homology in every degree below `b`, then the Moore complex of the degreewise tensor
product `M ⊗ N` has vanishing homology in every degree below `b + 1`.

This is the Künneth-type vanishing with one factor one-connected. It is proved here without any
Eilenberg–Zilber comparison, by an induction which lowers `b` one step at a time: a simplicial
module `N` with `H_0(N) = 0` is covered by the *reduced décalage*
`decRed N = ker(dec N → N_0)`, which is simplicially homotopy equivalent to zero. A simplicial
homotopy survives degreewise tensoring with `M` — this is the point, and it is what a
contraction of the Moore complex does not do — so both `decRed N` and `M ⊗ decRed N` have
acyclic Moore complexes, and the long exact sequences of the short exact sequence
`0 → W → decRed N → N → 0` identify `H_{n+1}(M ⊗ N)` with `H_n(M ⊗ W)` and `H_i(W)` with
`H_{i+1}(N)`, which is the inductive step.

## Main definitions

* `StacksDraft.SimplicialTensor.simpKer`: the degreewise kernel of a morphism of simplicial
  modules.
* `StacksDraft.SimplicialTensor.decRed`: the reduced décalage, the kernel of the augmentation
  of the décalage.

## Main results

* `StacksDraft.SimplicialTensor.decRedδ₀_app_surjective`: the reduced décalage covers `N` as
  soon as the Moore complex of `N` has vanishing homology in degree zero.
* `StacksDraft.SimplicialTensor.isZero_homology_tensor_of_lt`: the vanishing statement above.

## Implementation notes

The degree-zero case is a hypothesis `hzero` of the main theorem rather than a lemma of this
file: it is proved directly from the two face maps of the simplicial tensor product, by the
caller.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.SimplicialObject MonoidalCategory
open Opposite AlgebraicTopology

open scoped Simplicial TensorProduct

universe v w

namespace StacksDraft.SimplicialTensor

variable {B : Type w} [CommRing B]

/-! ### Elementary bookkeeping -/

/-- An equality of morphisms of modules, read on an element. -/
private lemma hom_apply_congr {M₁ M₂ : ModuleCat.{max v w} B} {f g : M₁ ⟶ M₂} (e : f = g)
    (x : M₁) : f.hom x = g.hom x :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e) x

/-- An equality of morphisms of modules, read on an element of a composite. -/
private lemma comp_hom_apply {M₁ M₂ M₃ : ModuleCat.{max v w} B} {f : M₁ ⟶ M₂} {g : M₂ ⟶ M₃}
    {h : M₁ ⟶ M₃} (e : f ≫ g = h) (x : M₁) : g.hom (f.hom x) = h.hom x :=
  LinearMap.congr_fun (congrArg ModuleCat.Hom.hom e) x

/-- Composition of two operators of a simplicial object, as the operator of the composite
morphism of `SimplexCategory`. -/
private lemma map_op_comp (X : SimplicialObject (ModuleCat.{max v w} B))
    {a b c : SimplexCategory} (f : a ⟶ b) (g : b ⟶ c) :
    X.map g.op ≫ X.map f.op = X.map (f ≫ g).op := by
  rw [op_comp, X.map_comp]

/-! ### The degreewise kernel of a morphism of simplicial modules -/

section SimpKer

variable {X Y : SimplicialObject (ModuleCat.{max v w} B)}

public lemma map_mem_ker (f : X ⟶ Y) {n m : SimplexCategoryᵒᵖ} (θ : n ⟶ m)
    (x : X.obj n) (hx : x ∈ LinearMap.ker (f.app n).hom) :
    (X.map θ).hom x ∈ LinearMap.ker (f.app m).hom := by
  rw [LinearMap.mem_ker] at hx ⊢
  rw [comp_hom_apply (f.naturality θ) x, ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero]

/-- The degreewise kernel of a morphism of simplicial modules. -/
public def simpKer (f : X ⟶ Y) : SimplicialObject (ModuleCat.{max v w} B) where
  obj n := ModuleCat.of B (LinearMap.ker (f.app n).hom)
  map θ := ModuleCat.ofHom ((X.map θ).hom.restrict (map_mem_ker f θ))
  map_id n := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [LinearMap.coe_restrict_apply]
  map_comp θ θ' := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    simp [LinearMap.coe_restrict_apply]

/-- The inclusion of the degreewise kernel. -/
public def simpKerι (f : X ⟶ Y) : simpKer f ⟶ X where
  app n := ModuleCat.ofHom (LinearMap.ker (f.app n).hom).subtype
  naturality n m θ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    rfl

@[simp]
public lemma simpKerι_app_apply (f : X ⟶ Y) (n : SimplexCategoryᵒᵖ)
    (x : LinearMap.ker (f.app n).hom) :
    ((simpKerι f).app n).hom x = (x : X.obj n) := rfl

public lemma simpKerι_comp (f : X ⟶ Y) : simpKerι f ≫ f = 0 := by
  ext n : 2
  exact LinearMap.ext fun x => LinearMap.mem_ker.mp x.2

/-- A morphism of simplicial modules landing degreewise in the kernel of `f`, corestricted to
that kernel. -/
public def simpKerLift (f : X ⟶ Y) (r : X ⟶ X)
    (hr : ∀ (n : SimplexCategoryᵒᵖ) (x : X.obj n), (r.app n).hom x ∈
      LinearMap.ker (f.app n).hom) :
    X ⟶ simpKer f where
  app n := ModuleCat.ofHom (((r.app n).hom).codRestrict _ (hr n))
  naturality n m θ := by
    exact ModuleCat.hom_ext <| LinearMap.ext fun x =>
      Subtype.ext (comp_hom_apply (r.naturality θ) x)

end SimpKer

/-! ### The reduced décalage -/

section DecRed

variable (N : SimplicialObject (ModuleCat.{max v w} B))

/-- The section of the augmentation of the décalage, with its source and target spelled in
terms of `N` rather than through the augmented object: `Comma.right` and `Functor.id` are not
reducible, so a composite written with Mathlib's spelling of `section_` has implicit arguments
that no rewrite can match against one written with `decAug`. -/
public def decSection : (const (ModuleCat.{max v w} B)).obj (N _⦋0⦌) ⟶ dec N :=
  (decExtraDegeneracy N).section_

public lemma decSection_comp_decAug :
    decSection N ≫ decAug N = 𝟙 ((const (ModuleCat.{max v w} B)).obj (N _⦋0⦌)) :=
  (decExtraDegeneracy N).section_comp_hom

/-- The idempotent of the décalage cut out by its augmentation. -/
public def decIdem : dec N ⟶ dec N :=
  decAug N ≫ decSection N

public lemma decIdem_comp_decAug : decIdem N ≫ decAug N = decAug N := by
  rw [decIdem, Category.assoc, decSection_comp_decAug, Category.comp_id]

/-- The reduced décalage of `N`: the degreewise kernel of the augmentation of the décalage. -/
public def decRed : SimplicialObject (ModuleCat.{max v w} B) := simpKer (decAug N)

/-- The inclusion of the reduced décalage into the décalage. -/
public def decRedι : decRed N ⟶ dec N := simpKerι (decAug N)

public lemma decRedι_comp_decAug : decRedι N ≫ decAug N = 0 := simpKerι_comp (decAug N)

/-- The retraction of the décalage onto its reduced part. -/
public def decRedπ : dec N ⟶ decRed N :=
  simpKerLift (decAug N) (𝟙 (dec N) - decIdem N) (by
    intro n x
    rw [LinearMap.mem_ker]
    have h : ((decAug N).app n).hom (((decIdem N).app n).hom x) =
        ((decAug N).app n).hom x :=
      comp_hom_apply (NatTrans.congr_app (decIdem_comp_decAug N) n) x
    rw [NatTrans.app_sub, ModuleCat.hom_sub, LinearMap.sub_apply, map_sub,
      NatTrans.id_app, ModuleCat.hom_id, LinearMap.id_apply, h, sub_self])

public lemma decRedι_comp_decIdem : decRedι N ≫ decIdem N = 0 := by
  rw [decIdem, ← Category.assoc, decRedι_comp_decAug, zero_comp]

/-- The idempotent of the décalage kills its reduced part, degreewise. -/
public lemma decIdem_app_apply_eq_zero (n : SimplexCategoryᵒᵖ)
    (x : LinearMap.ker ((decAug N).app n).hom) :
    ((decIdem N).app n).hom (x : (dec N).obj n) = 0 := by
  have h : ((decIdem N).app n).hom (x : (dec N).obj n) =
      ((decSection N).app n).hom (((decAug N).app n).hom (x : (dec N).obj n)) := rfl
  rw [h, LinearMap.mem_ker.mp x.2, map_zero]

/-- Two morphisms into the reduced décalage agree as soon as they agree after the inclusion. -/
public lemma decRed_hom_ext {Z : SimplicialObject (ModuleCat.{max v w} B)}
    {a b : Z ⟶ decRed N} (h : a ≫ decRedι N = b ≫ decRedι N) : a = b := by
  ext n : 2
  exact LinearMap.ext fun x => Subtype.ext (hom_apply_congr (NatTrans.congr_app h n) x)

public lemma decRedπ_comp_decRedι : decRedπ N ≫ decRedι N = 𝟙 (dec N) - decIdem N := by
  ext n : 2
  exact LinearMap.ext fun _ => rfl

public lemma decRedι_comp_decRedπ : decRedι N ≫ decRedπ N = 𝟙 (decRed N) := by
  apply decRed_hom_ext
  rw [Category.assoc, decRedπ_comp_decRedι, Preadditive.comp_sub, Category.comp_id,
    decRedι_comp_decIdem, sub_zero, Category.id_comp]

/-- The reduced décalage is simplicially null-homotopic: its identity is simplicially homotopic
to zero, and therefore remains so after degreewise tensoring with any simplicial module. -/
public def decRedNullHomotopy : Homotopy (0 : decRed N ⟶ decRed N) (𝟙 (decRed N)) := by
  refine (((decExtraDegeneracy N).homotopy.precomp (decRedι N)).postcomp
    (decRedπ N)).ofEq ?_ ?_
  · change (decRedι N ≫ decIdem N) ≫ decRedπ N = 0
    rw [decRedι_comp_decIdem, zero_comp]
  · change (decRedι N ≫ 𝟙 (dec N)) ≫ decRedπ N = 𝟙 (decRed N)
    rw [Category.comp_id, decRedι_comp_decRedπ]

public lemma isZero_homology_decRed (n : ℕ) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj (decRed N)).homology n) :=
  Homotopy.isZero_homology_of_nullHomotopy (decRedNullHomotopy N) n

public lemma isZero_homology_tensor_decRed (M : SimplicialObject (ModuleCat.{max v w} B))
    (n : ℕ) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj
      (M ⊗ decRed N)).homology n) :=
  Homotopy.isZero_homology_of_nullHomotopy
    (Homotopy.whiskerLeftNullHomotopy M (decRedNullHomotopy N)) n

/-- The covering of `N` by its reduced décalage. -/
public def decRedδ₀ : decRed N ⟶ N := decRedι N ≫ decδ₀ N

end DecRed

/-! ### The reduced décalage covers a simplicial module with vanishing `H₀` -/

private lemma isZero_homology_zero_iff (X : SimplicialObject (ModuleCat.{max v w} B)) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj X).homology 0) ↔
      Function.Surjective ((X.δ (0 : Fin 2)).hom - (X.δ (1 : Fin 2)).hom) := by
  let D := (alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj X
  show IsZero (D.homology 0) ↔ _
  rw [← D.exactAt_iff_isZero_homology,
    D.exactAt_iff' 1 0 ((ComplexShape.down ℕ).next 0) (by simp) rfl,
    ShortComplex.exact_iff_epi _ (by
      show D.d 0 _ = 0
      exact D.shape _ _ (by simp)),
    ModuleCat.epi_iff_surjective]
  show Function.Surjective ((AlternatingFaceMapComplex.obj X).d 1 0).hom ↔ _
  rw [AlternatingFaceMapComplex.obj_d_eq X 0]
  simp [Fin.sum_univ_two, sub_eq_add_neg]

/-- The décalage of the constant morphism `⦋k⦌ ⟶ ⦋0⦌`, as an operator of `N` from degree one
to degree `k + 1`. Its source and target are spelled in terms of `N`: `dec` is not reducible,
so `(dec N).obj (op ⦋k⦌)` and `N _⦋k + 1⦌` are definitionally but not syntactically equal, and
instance synthesis for the addition of simplices needs the latter. -/
private def decCone (N : SimplicialObject (ModuleCat.{max v w} B)) (k : ℕ) :
    N.obj (op ⦋1⦌) ⟶ N.obj (op ⦋k + 1⦌) :=
  (dec N).map (SimplexCategory.const ⦋k⦌ ⦋0⦌ 0).op

/-- The correction term of the covering: the décalage of the constant morphism minus the
constant-degenerate simplex at the zeroth vertex. The two have the same zeroth face, so the
correction is invisible to it, while the augmentation sends the correction to `δ₁ - δ₀`. It is
a single morphism, so that the witness of the covering is a sum of two simplices and no
subtraction of simplices ever occurs. -/
private def decCorr (N : SimplicialObject (ModuleCat.{max v w} B)) (k : ℕ) :
    N.obj (op ⦋1⦌) ⟶ N.obj (op ⦋k + 1⦌) :=
  decCone N k - N.δ (0 : Fin 2) ≫ N.map (SimplexCategory.const ⦋k + 1⦌ ⦋0⦌ 0).op

private lemma σ_zero_comp_decAug_app (N : SimplicialObject (ModuleCat.{max v w} B)) (k : ℕ) :
    N.σ (0 : Fin (k + 1)) ≫ (decAug N).app (op ⦋k⦌) =
      N.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ 0).op := by
  have hσ0 : (SimplexCategory.σ (0 : Fin (k + 1))).toOrderHom 0 = 0 := by
    simp [SimplexCategory.σ, Fin.predAbove]
  rw [N.σ_def, decAug_app, map_op_comp N (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ 0)
    (SimplexCategory.σ 0), SimplexCategory.const_comp, hσ0]

private lemma decCorr_comp_decAug_app (N : SimplicialObject (ModuleCat.{max v w} B)) (k : ℕ) :
    decCorr N k ≫ (decAug N).app (op ⦋k⦌) = N.δ (1 : Fin 2) - N.δ (0 : Fin 2) := by
  have hCaug : N.map (SimplexCategory.const ⦋k + 1⦌ ⦋0⦌ 0).op ≫ (decAug N).app (op ⦋k⦌) =
      𝟙 (N.obj (op ⦋0⦌)) := by
    rw [decAug_app, map_op_comp N (SimplexCategory.const ⦋0⦌ ⦋k + 1⦌ 0)
      (SimplexCategory.const ⦋k + 1⦌ ⦋0⦌ 0), SimplexCategory.const_comp,
      SimplexCategory.const_apply, SimplexCategory.const_eq_id, op_id, N.map_id]
  have hGaug : decCone N k ≫ (decAug N).app (op ⦋k⦌) = N.δ (1 : Fin 2) := by
    have h : decCone N k ≫ (decAug N).app (op ⦋k⦌) =
        (decAug N).app (op ⦋0⦌) ≫ 𝟙 (N.obj (op ⦋0⦌)) :=
      (decAug N).naturality (SimplexCategory.const ⦋k⦌ ⦋0⦌ 0).op
    exact h.trans ((Category.comp_id _).trans (decAug_app_zero N))
  have hCCaug : (N.δ (0 : Fin 2) ≫
        N.map (SimplexCategory.const ⦋k + 1⦌ ⦋0⦌ 0).op) ≫ (decAug N).app (op ⦋k⦌) =
      N.δ (0 : Fin 2) :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun g => N.δ (0 : Fin 2) ≫ g) hCaug).trans (Category.comp_id _))
  exact (Preadditive.sub_comp _ _ _).trans (congrArg₂ (· - ·) hGaug hCCaug)

private lemma decCorr_comp_δ_zero (N : SimplicialObject (ModuleCat.{max v w} B)) (k : ℕ) :
    decCorr N k ≫ N.δ (0 : Fin (k + 2)) = 0 := by
  have hCδ : N.map (SimplexCategory.const ⦋k + 1⦌ ⦋0⦌ 0).op ≫ N.δ (0 : Fin (k + 2)) =
      N.map (SimplexCategory.const ⦋k⦌ ⦋0⦌ 0).op := by
    rw [N.δ_def, map_op_comp N (SimplexCategory.δ (0 : Fin (k + 2)))
      (SimplexCategory.const ⦋k + 1⦌ ⦋0⦌ 0), SimplexCategory.comp_const]
  have hGδ : decCone N k ≫ N.δ (0 : Fin (k + 2)) =
      N.δ (0 : Fin 2) ≫ N.map (SimplexCategory.const ⦋k⦌ ⦋0⦌ 0).op :=
    (decδ₀ N).naturality (SimplexCategory.const ⦋k⦌ ⦋0⦌ 0).op
  have hCCδ : (N.δ (0 : Fin 2) ≫
        N.map (SimplexCategory.const ⦋k + 1⦌ ⦋0⦌ 0).op) ≫ N.δ (0 : Fin (k + 2)) =
      N.δ (0 : Fin 2) ≫ N.map (SimplexCategory.const ⦋k⦌ ⦋0⦌ 0).op :=
    (Category.assoc _ _ _).trans (congrArg (fun g => N.δ (0 : Fin 2) ≫ g) hCδ)
  exact (Preadditive.sub_comp _ _ _).trans ((congrArg₂ (· - ·) hGδ hCCδ).trans (sub_self _))

/-- **The reduced décalage covers.** If the Moore complex of `N` has vanishing homology in
degree zero then the reduced décalage of `N` surjects onto `N` in every degree: a simplex `y` of
`N` is the zeroth face of `σ 0 y`, corrected by two simplices built from a `1`-simplex `u`
witnessing that the zeroth vertex of `y` is a boundary — the décalage of the constant map at
`u`, and the constant-degenerate simplex at the zeroth face of `u` — whose zeroth faces agree,
so that the correction is invisible to the zeroth face and cancels the vertex of `y` against
the augmentation. -/
public lemma decRedδ₀_app_surjective (N : SimplicialObject (ModuleCat.{max v w} B))
    (h₀ : IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj N).homology 0))
    (k : ℕ) :
    Function.Surjective ((decRedδ₀ N).app (op ⦋k⦌)).hom := by
  intro y
  obtain ⟨u, hu⟩ :=
    (isZero_homology_zero_iff N).mp h₀ ((N.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ 0).op).hom y)
  rw [LinearMap.sub_apply] at hu
  have hσδ : N.σ (0 : Fin (k + 1)) ≫ N.δ (0 : Fin (k + 2)) = 𝟙 _ :=
    N.δ_comp_σ_self' (by simp)
  have e₁ : ((decAug N).app (op ⦋k⦌)).hom ((N.σ (0 : Fin (k + 1))).hom y) =
      (N.map (SimplexCategory.const ⦋0⦌ ⦋k⦌ 0).op).hom y :=
    comp_hom_apply (σ_zero_comp_decAug_app N k) y
  have e₂ : ((decAug N).app (op ⦋k⦌)).hom ((decCorr N k).hom u) =
      (N.δ (1 : Fin 2)).hom u - (N.δ (0 : Fin 2)).hom u := by
    have h := comp_hom_apply (decCorr_comp_decAug_app N k) u
    rwa [ModuleCat.hom_sub, LinearMap.sub_apply] at h
  have e₃ : (N.δ (0 : Fin (k + 2))).hom ((N.σ (0 : Fin (k + 1))).hom y) = y :=
    (comp_hom_apply hσδ y).trans rfl
  have e₄ : (N.δ (0 : Fin (k + 2))).hom ((decCorr N k).hom u) = 0 :=
    (comp_hom_apply (decCorr_comp_δ_zero N k) u).trans rfl
  have hadd : ∀ {P Q : ModuleCat.{max v w} B} (f : P ⟶ Q) (a b : P),
      f.hom (a + b) = f.hom a + f.hom b := fun _ _ _ => map_add _ _ _
  obtain ⟨z, hz₁, hz₂⟩ : ∃ z : N.obj (op ⦋k + 1⦌),
      ((decAug N).app (op ⦋k⦌)).hom z = 0 ∧ (N.δ (0 : Fin (k + 2))).hom z = y := by
    refine ⟨(N.σ (0 : Fin (k + 1))).hom y + (decCorr N k).hom u, ?_, ?_⟩
    · refine (hadd _ _ _).trans ?_
      rw [e₁, e₂, ← hu]
      abel
    · exact (hadd _ _ _).trans (by rw [e₃, e₄, add_zero])
  exact ⟨⟨z, LinearMap.mem_ker.mpr hz₁⟩, hz₂⟩

/-! ### The two short exact sequences and the induction -/

/-- The degreewise-kernel short complex of simplicial modules. -/
private def kerSES {X Y : SimplicialObject (ModuleCat.{max v w} B)} (f : X ⟶ Y) :
    ShortComplex (SimplicialObject (ModuleCat.{max v w} B)) where
  X₁ := simpKer f
  X₂ := X
  X₃ := Y
  f := simpKerι f
  g := f
  zero := simpKerι_comp f

/-- The same short complex, tensored on the left with a simplicial module. -/
private def tensorKerSES (M : SimplicialObject (ModuleCat.{max v w} B))
    {X Y : SimplicialObject (ModuleCat.{max v w} B)} (f : X ⟶ Y) :
    ShortComplex (SimplicialObject (ModuleCat.{max v w} B)) where
  X₁ := M ⊗ simpKer f
  X₂ := M ⊗ X
  X₃ := M ⊗ Y
  f := M ◁ simpKerι f
  g := M ◁ f
  zero := by
    rw [← MonoidalCategory.whiskerLeft_comp, simpKerι_comp]
    exact whiskerLeft_eq_zero M

/-- The Moore complexes of a short complex of simplicial modules. -/
private def mooreSES (S : ShortComplex (SimplicialObject (ModuleCat.{max v w} B))) :
    ShortComplex (ChainComplex (ModuleCat.{max v w} B) ℕ) where
  X₁ := (alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj S.X₁
  X₂ := (alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj S.X₂
  X₃ := (alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj S.X₃
  f := (alternatingFaceMapComplex (ModuleCat.{max v w} B)).map S.f
  g := (alternatingFaceMapComplex (ModuleCat.{max v w} B)).map S.g
  zero := by rw [← Functor.map_comp, S.zero, Functor.map_zero]

private lemma mooreSES_shortExact
    (S : ShortComplex (SimplicialObject (ModuleCat.{max v w} B)))
    (hexact : ∀ n : SimplexCategoryᵒᵖ, Function.Exact (S.f.app n).hom (S.g.app n).hom)
    (hmono : ∀ n : SimplexCategoryᵒᵖ, Function.Injective (S.f.app n).hom)
    (hepi : ∀ n : SimplexCategoryᵒᵖ, Function.Surjective (S.g.app n).hom) :
    (mooreSES S).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun _ =>
    ModuleCat.shortComplex_shortExact _ (hexact _) (hmono _) (hepi _)

private lemma kerSES_shortExact {X Y : SimplicialObject (ModuleCat.{max v w} B)} (f : X ⟶ Y)
    (hf : ∀ k : ℕ, Function.Surjective ((f.app (op ⦋k⦌))).hom) :
    (mooreSES (kerSES f)).ShortExact :=
  mooreSES_shortExact _ (fun n => LinearMap.exact_subtype_ker_map (f.app n).hom)
    (fun n => (LinearMap.ker (f.app n).hom).injective_subtype) (fun n => hf n.unop.len)

private lemma tensorKerSES_shortExact (M : SimplicialObject (ModuleCat.{max v w} B))
    (hMflat : ∀ n, Module.Flat B (M.obj n))
    {X Y : SimplicialObject (ModuleCat.{max v w} B)} (f : X ⟶ Y)
    (hf : ∀ k : ℕ, Function.Surjective ((f.app (op ⦋k⦌))).hom) :
    (mooreSES (tensorKerSES M f)).ShortExact := by
  refine mooreSES_shortExact _ (fun n => ?_) (fun n => ?_) (fun n => ?_)
  · have := hMflat n
    exact Module.Flat.lTensor_exact (M := M.obj n)
      (LinearMap.exact_subtype_ker_map (f.app n).hom)
  · have := hMflat n
    exact Module.Flat.lTensor_preserves_injective_linearMap (M := M.obj n) _
      ((LinearMap.ker (f.app n).hom).injective_subtype)
  · exact LinearMap.lTensor_surjective _ (hf n.unop.len)

/-- Through the kernel of the covering by the reduced décalage, the vanishing of `H_{i+1}(N)`
gives that of `H_i` of the kernel. -/
private lemma isZero_homology_simpKer_decRedδ₀ (N : SimplicialObject (ModuleCat.{max v w} B))
    (h₀ : IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj N).homology 0))
    (i : ℕ)
    (h : IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj N).homology (i + 1))) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj
      (simpKer (decRedδ₀ N))).homology i) :=
  h.of_iso ((kerSES_shortExact (decRedδ₀ N) (decRedδ₀_app_surjective N h₀)).δIso (i + 1) i
    (by simp) (isZero_homology_decRed N (i + 1)) (isZero_homology_decRed N i)).symm

/-- The inductive step: with `M` degreewise flat, the vanishing of `H_n` of `M` tensored with the
kernel of the covering by the reduced décalage gives that of `H_{n+1}(M ⊗ N)`. -/
private lemma isZero_homology_tensor_succ (M : SimplicialObject (ModuleCat.{max v w} B))
    (hMflat : ∀ n, Module.Flat B (M.obj n)) (N : SimplicialObject (ModuleCat.{max v w} B))
    (h₀ : IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj N).homology 0))
    (n : ℕ)
    (h : IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj
      (M ⊗ simpKer (decRedδ₀ N))).homology n)) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj (M ⊗ N)).homology (n + 1)) :=
  h.of_iso ((tensorKerSES_shortExact M hMflat (decRedδ₀ N)
    (decRedδ₀_app_surjective N h₀)).δIso (n + 1) n (by simp)
      (isZero_homology_tensor_decRed N M (n + 1)) (isZero_homology_tensor_decRed N M n))

/-- The induction: with `M` degreewise flat, and the degree-zero vanishing available for every
second factor whose homology vanishes below `c`, the degree-`n` homology of the Moore complex of
`M ⊗ N` vanishes as soon as that of `N` vanishes below `n + c`. -/
private lemma isZero_homology_tensor_aux (M : SimplicialObject (ModuleCat.{max v w} B))
    (hMflat : ∀ n, Module.Flat B (M.obj n)) (c : ℕ)
    (hzero : ∀ N' : SimplicialObject (ModuleCat.{max v w} B),
      (∀ i, i < c →
        IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj N').homology i)) →
      IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj (M ⊗ N')).homology 0)) :
    ∀ (n : ℕ) (N : SimplicialObject (ModuleCat.{max v w} B)),
      (∀ i, i < n + c →
        IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj N).homology i)) →
      IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj (M ⊗ N)).homology n) := by
  intro n
  induction n with
  | zero => exact fun N hN => hzero N fun i hi => hN i (by omega)
  | succ n ih =>
    intro N hN
    exact isZero_homology_tensor_succ M hMflat N (hN 0 (by omega)) n
      (ih (simpKer (decRedδ₀ N)) fun i hi =>
        isZero_homology_simpKer_decRedδ₀ N (hN 0 (by omega)) i (hN (i + 1) (by omega)))

/-- **Künneth vanishing with a one-connected factor, without Eilenberg–Zilber.** Let `M` and `N`
be simplicial modules over `B`, let `M` be degreewise flat, and assume the degree-zero vanishing
`H₀(M ⊗ N') = 0` for every simplicial module `N'` — which holds as soon as `H₀(M) = 0`, by the
two face maps of the tensor product. If the Moore complex of `N` has vanishing homology in every
degree `< b`, then the Moore complex of `M ⊗ N` has vanishing homology in every degree
`< b + 1`. -/
public theorem isZero_homology_tensor_of_lt (M N : SimplicialObject (ModuleCat.{max v w} B))
    (hMflat : ∀ n, Module.Flat B (M.obj n))
    (hzero : ∀ N' : SimplicialObject (ModuleCat.{max v w} B),
      IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj (M ⊗ N')).homology 0))
    (b n : ℕ)
    (hN : ∀ i, i < b →
      IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj N).homology i))
    (hn : n < b + 1) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj (M ⊗ N)).homology n) :=
  isZero_homology_tensor_aux M hMflat 0 (fun N' _ => hzero N') n N
    (fun i hi => hN i (by omega))

/-! ### Tensoring with a degreewise flat simplicial module -/

/-- If the Moore complex of `N` has vanishing homology in degree zero, then so does that of
`M ⊗ N`: a pure tensor `x ⊗ (d₀ z - d₁ z)` is the boundary of `σ₀ x ⊗ z`. -/
public lemma isZero_homology_zero_tensor_of_right (M N : SimplicialObject (ModuleCat.{max v w} B))
    (hN : IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj N).homology 0)) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj (M ⊗ N)).homology 0) := by
  apply (isZero_homology_zero_iff _).mpr
  have hsurj := (isZero_homology_zero_iff N).mp hN
  intro x
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul x y =>
    obtain ⟨z, hz⟩ := hsurj y
    refine ⟨M.σ (0 : Fin 1) x ⊗ₜ[B] z, ?_⟩
    show M.δ (0 : Fin 2) (M.σ (0 : Fin 1) x) ⊗ₜ[B] N.δ (0 : Fin 2) z -
      M.δ (1 : Fin 2) (M.σ (0 : Fin 1) x) ⊗ₜ[B] N.δ (1 : Fin 2) z = x ⊗ₜ[B] y
    rw [show M.δ (0 : Fin 2) (M.σ (0 : Fin 1) x) = x from
      ConcreteCategory.congr_hom (M.δ_comp_σ_self (i := (0 : Fin 1))) x,
      show M.δ (1 : Fin 2) (M.σ (0 : Fin 1) x) = x from
      ConcreteCategory.congr_hom (M.δ_comp_σ_succ (i := (0 : Fin 1))) x,
      ← TensorProduct.tmul_sub]
    exact congrArg (fun z => x ⊗ₜ[B] z) hz
  | add x y hx hy =>
    obtain ⟨x', rfl⟩ := hx
    obtain ⟨y', rfl⟩ := hy
    exact ⟨x' + y', map_add _ _ _⟩

/-- **Tensoring with a degreewise flat simplicial module preserves acyclicity.** If `M` is
degreewise flat and the Moore complex of `N` is acyclic, then so is the Moore complex of
`M ⊗ N`. No Eilenberg–Zilber comparison is used: the induction lowers the degree through the
reduced décalage, as for `StacksDraft.SimplicialTensor.isZero_homology_tensor_of_lt`, with the
degree-zero case supplied by the vanishing of `H₀(N)`. -/
public theorem isZero_homology_tensor_of_acyclic (M N : SimplicialObject (ModuleCat.{max v w} B))
    (hMflat : ∀ n, Module.Flat B (M.obj n))
    (hN : ∀ i, IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj N).homology i))
    (n : ℕ) :
    IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj (M ⊗ N)).homology n) :=
  isZero_homology_tensor_aux M hMflat 1
    (fun N' hN' => isZero_homology_zero_tensor_of_right M N' (hN' 0 one_pos)) n N fun i _ => hN i

/-- **Tensoring with a degreewise flat simplicial module preserves surjective
quasi-isomorphisms.** If `f : X ⟶ Y` is degreewise surjective and induces a quasi-isomorphism of
Moore complexes, and `M` is degreewise flat, then `M ◁ f : M ⊗ X ⟶ M ⊗ Y` induces a
quasi-isomorphism of Moore complexes. The degreewise kernel `K` of `f` has acyclic Moore complex
by the long exact homology sequence, hence so does `M ⊗ K`, and `0 → M ⊗ K → M ⊗ X → M ⊗ Y → 0`
is degreewise exact since `M` is flat. -/
public theorem quasiIso_whiskerLeft_of_quasiIso (M : SimplicialObject (ModuleCat.{max v w} B))
    (hMflat : ∀ n, Module.Flat B (M.obj n))
    {X Y : SimplicialObject (ModuleCat.{max v w} B)} (f : X ⟶ Y)
    (hf : ∀ k : ℕ, Function.Surjective ((f.app (op ⦋k⦌))).hom)
    (hq : QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max v w} B)).map f)) :
    QuasiIso ((alternatingFaceMapComplex (ModuleCat.{max v w} B)).map (M ◁ f)) := by
  have hK : ∀ i, IsZero (((alternatingFaceMapComplex (ModuleCat.{max v w} B)).obj
      (simpKer f)).homology i) := fun i =>
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).mp
      ((kerSES_shortExact f hf).acyclic_X₁ (hg := hq) i)
  have hMK := isZero_homology_tensor_of_acyclic M (simpKer f) hMflat hK
  have hSM := tensorKerSES_shortExact M hMflat f hf
  show QuasiIso (mooreSES (tensorKerSES M f)).g
  refine (_root_.quasiIso_iff _).mpr fun i => ?_
  rw [_root_.quasiIsoAt_iff_isIso_homologyMap]
  have : Mono (HomologicalComplex.homologyMap (mooreSES (tensorKerSES M f)).g i) :=
    (hSM.homology_exact₂ i).mono_g ((hMK i).eq_of_src _ _)
  rcases i with _ | j
  · have := hSM.epi_g
    have : Epi (HomologicalComplex.homologyMap (mooreSES (tensorKerSES M f)).g 0) :=
      HomologicalComplex.epi_homologyMap_of_epi_of_not_rel _ 0 (by simp)
    exact isIso_of_mono_of_epi _
  · have : Epi (HomologicalComplex.homologyMap (mooreSES (tensorKerSES M f)).g (j + 1)) :=
      (hSM.homology_exact₃ (j + 1) j (by simp)).epi_f ((hMK j).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _

end StacksDraft.SimplicialTensor

end
