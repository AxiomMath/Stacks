module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.RingTheory.Ideal.Maps
public import StacksFrontier.RingTheory.Tor.Balancing

/-!
# Uniform annihilation of Tor along an almost-flat resolution

Let `A` be a commutative ring and `M` an `A`-module. The modules
`Tor_i(X, M) = ((Tor (ModuleCat A) i).obj X).obj M` are functorial in the first variable `X`, and
the long exact sequence attached to a short exact sequence of first variables propagates bounds on
annihilators from two terms of the sequence to the third. Iterating the two propagation steps
along a resolution whose terms are flat up to a uniformly annihilated error produces a single ring
element annihilating `Tor_i(X, M)` in all large degrees `i`.

## Main results

* `mem_annihilator_tor_of_mem_annihilator`: an element annihilating `X` annihilates every
  `Tor_i(X, M)`.
* `mem_annihilator_tor_middle`: if `r` annihilates `T.X₃` and `s` annihilates `Tor_j(T.X₁, M)`
  for all `j ≥ m`, then `r * s` annihilates `Tor_j(T.X₂, M)` for all `j ≥ m`.
* `mem_annihilator_tor_of_shift`: if `v` annihilates `Tor_j(S.X₁, M)` for all `j ≥ m` and `u`
  annihilates `Tor_i(S.X₂, M)` for all `i ≥ p`, then `v * u` annihilates `Tor_i(S.X₃, M)` for all
  `i ≥ m + 1` with `i ≥ p`.
* `torShortComplexExact` and `torShortComplexExact₃`: exactness of the `Tor` long exact sequence
  in the first variable at `Tor_j(T.X₂, M)` and at `Tor_{k+1}(S.X₃, M)`, the latter involving the
  connecting map `torDelta`.
* `tor_map_smul_id`: `Tor` sends multiplication by a ring element on the first variable to
  multiplication by that element.

## Implementation notes

Annihilation is phrased with `Module.annihilator`, so that membership unfolds to `∀ x, r • x = 0`
by `Module.mem_annihilator`. `Tor_i(X, M)` is compared with the homology of `X ⊗ P_•`, where `P_•`
is the chosen projective resolution of `M`, by the isomorphism `torIsoHomology`, natural in `X`;
the long exact sequence is the homology sequence of the short exact sequence of complexes
`lesShift.ses`.
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.MonoidalCategory CategoryTheory.Limits

universe u

variable {A : Type u} [CommRing A]

/-! ### Annihilators of homology and of tensor products -/

/-- An element annihilating a module annihilates every module isomorphic to it. -/
theorem mem_annihilator_of_moduleCat_iso {X Y : ModuleCat.{u} A} (e : X ≅ Y) {r : A}
    (hr : r ∈ Module.annihilator A X) : r ∈ Module.annihilator A Y := by
  rwa [← e.toLinearEquiv.annihilator_eq]

/-- An element annihilating the degree `i` term of a complex annihilates the degree `i`
homology. -/
theorem mem_annihilator_homology_of_mem_annihilator {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} A) c) (i : ι) {r : A}
    (hr : r ∈ Module.annihilator A (K.X i)) :
    r ∈ Module.annihilator A (K.homology i) := by
  rw [Module.mem_annihilator] at hr ⊢
  intro z
  obtain ⟨y, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance z
  have hinj := (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
  have hy : r • y = 0 := hinj (by rw [map_smul, hr, map_zero])
  rw [← map_smul, hy, map_zero]

/-- An element annihilating `X` annihilates `X ⊗ Y` for every `Y`. -/
theorem mem_annihilator_tensor_of_mem_annihilator {X : ModuleCat.{u} A} {r : A}
    (hr : r ∈ Module.annihilator A X) (Y : ModuleCat.{u} A) :
    r ∈ Module.annihilator A ((tensorLeft X).obj Y) := by
  rw [Module.mem_annihilator] at hr ⊢
  intro t
  show (r • t : TensorProduct A X Y) = 0
  induction t using TensorProduct.induction_on with
  | zero => simp
  | tmul x y => rw [TensorProduct.smul_tmul', hr, TensorProduct.zero_tmul]
  | add a b ha hb => rw [smul_add, ha, hb, add_zero]

/-- Multiplication by a ring element on a complex induces multiplication by that element on
homology. -/
theorem HomologicalComplex.homologyMap_smul_id {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} A) c) (i : ι) (r : A) :
    HomologicalComplex.homologyMap (r • 𝟙 K) i = r • 𝟙 (K.homology i) := by
  have h : (HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) c i).map (r • 𝟙 K)
      = r • 𝟙 (K.sc i) := by ext <;> rfl
  show ShortComplex.homologyMap
    ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} A) c i).map (r • 𝟙 K)) = _
  rw [h, ShortComplex.homologyMap_smul, ShortComplex.homologyMap_id]
  rfl

/-! ### The comparison of `Tor` with the homology of a tensored projective resolution -/

/-- The comparison `Tor_i(X, M) ≅ H_i(X ⊗ P_•)`, where `P_•` is the chosen projective resolution
of `M`. -/
noncomputable def torIsoHomology (X M : ModuleCat.{u} A) (i : ℕ) :
    ((Tor (ModuleCat.{u} A) i).obj X).obj M ≅
      ((lesShift.phi A (projectiveResolution M).complex).obj X).homology i :=
  (projectiveResolution M).isoLeftDerivedObj (tensorLeft X) i

/-- Under `torIsoHomology`, the map induced on `Tor` by a morphism of first variables becomes the
map induced on the homology of the tensored resolution. -/
theorem torIsoHomology_hom_naturality {X Y : ModuleCat.{u} A} (f : X ⟶ Y) (M : ModuleCat.{u} A)
    (i : ℕ) :
    ((Tor (ModuleCat.{u} A) i).map f).app M ≫ (torIsoHomology Y M i).hom
      = (torIsoHomology X M i).hom ≫ HomologicalComplex.homologyMap
          ((lesShift.phi A (projectiveResolution M).complex).map f) i := by
  refine (Iso.eq_comp_inv (torIsoHomology Y M i)).mp ?_
  rw [Category.assoc]
  exact ProjectiveResolution.leftDerived_app_eq ((tensoringLeft (ModuleCat.{u} A)).map f)
    (projectiveResolution M) i

/-- The inverse comparison `torIsoHomology` intertwines the map induced on the homology of the
tensored resolution with the map induced on `Tor`. -/
theorem torIsoHomology_inv_naturality {X Y : ModuleCat.{u} A} (f : X ⟶ Y) (M : ModuleCat.{u} A)
    (i : ℕ) :
    HomologicalComplex.homologyMap
          ((lesShift.phi A (projectiveResolution M).complex).map f) i
        ≫ (torIsoHomology Y M i).inv
      = (torIsoHomology X M i).inv ≫ ((Tor (ModuleCat.{u} A) i).map f).app M :=
  lesShift.comp_inv_eq_inv_comp_of_comm _ _ _ _ (torIsoHomology_hom_naturality f M i)

/-- `Tor` carries multiplication by a ring element on the first variable to multiplication by
that element. -/
theorem tor_map_smul_id (X M : ModuleCat.{u} A) (i : ℕ) (r : A) :
    ((Tor (ModuleCat.{u} A) i).map (r • 𝟙 X)).app M
      = r • 𝟙 (((Tor (ModuleCat.{u} A) i).obj X).obj M) := by
  have hmap : (lesShift.phi A (projectiveResolution M).complex).map (r • 𝟙 X)
      = r • 𝟙 ((lesShift.phi A (projectiveResolution M).complex).obj X) := by
    apply HomologicalComplex.hom_ext
    intro q
    show (r • 𝟙 X) ▷ (projectiveResolution M).complex.X q
      = r • 𝟙 ((tensorLeft X).obj ((projectiveResolution M).complex.X q))
    simp
  have h := torIsoHomology_hom_naturality (r • 𝟙 X) M i
  rw [hmap, HomologicalComplex.homologyMap_smul_id] at h
  rw [← cancel_mono (torIsoHomology X M i).hom, h]
  simp

/-! ### Annihilation of `Tor` in the first variable -/

/-- An element annihilating the first variable annihilates every `Tor` module built from it. -/
theorem mem_annihilator_tor_of_mem_annihilator (X M : ModuleCat.{u} A) (i : ℕ) {r : A}
    (hr : r ∈ Module.annihilator A X) :
    r ∈ Module.annihilator A (((Tor (ModuleCat.{u} A) i).obj X).obj M) :=
  mem_annihilator_of_moduleCat_iso (torIsoHomology X M i).symm
    (mem_annihilator_homology_of_mem_annihilator _ i
      (mem_annihilator_tensor_of_mem_annihilator hr _))

/-! ### The two exactness statements of the long exact sequence -/

/-- The two maps induced on `Tor` by a short complex of first variables compose to zero. -/
theorem tor_map_comp_eq_zero (T : ShortComplex (ModuleCat.{u} A)) (M : ModuleCat.{u} A) (j : ℕ) :
    ((Tor (ModuleCat.{u} A) j).map T.f).app M ≫ ((Tor (ModuleCat.{u} A) j).map T.g).app M = 0 := by
  have hz : HomologicalComplex.homologyMap
        ((lesShift.phi A (projectiveResolution M).complex).map T.f) j
      ≫ HomologicalComplex.homologyMap
        ((lesShift.phi A (projectiveResolution M).complex).map T.g) j = 0 := by
    rw [← HomologicalComplex.homologyMap_comp, ← Functor.map_comp, T.zero, Functor.map_zero,
      HomologicalComplex.homologyMap_zero]
  rw [← cancel_mono (torIsoHomology T.X₃ M j).hom, Category.assoc,
    torIsoHomology_hom_naturality T.g M j, ← Category.assoc,
    torIsoHomology_hom_naturality T.f M j, Category.assoc, hz, comp_zero, zero_comp]

/-- The degree `j` part of the `Tor` sequence of a short complex `T` of first variables,
`Tor_j(T.X₁, M) → Tor_j(T.X₂, M) → Tor_j(T.X₃, M)`. -/
noncomputable def torShortComplex (T : ShortComplex (ModuleCat.{u} A)) (M : ModuleCat.{u} A)
    (j : ℕ) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk (((Tor (ModuleCat.{u} A) j).map T.f).app M)
    (((Tor (ModuleCat.{u} A) j).map T.g).app M) (tor_map_comp_eq_zero T M j)

/-- Exactness of `Tor_j(T.X₁, M) → Tor_j(T.X₂, M) → Tor_j(T.X₃, M)` for a short exact sequence
`T` of first variables. -/
theorem torShortComplexExact (T : ShortComplex (ModuleCat.{u} A)) (hT : T.ShortExact)
    (M : ModuleCat.{u} A) (j : ℕ) : (torShortComplex T M j).Exact := by
  refine ShortComplex.exact_of_iso ?_ ((lesShift.ses A T hT M).homology_exact₂ j)
  exact ShortComplex.isoMk (torIsoHomology T.X₁ M j).symm (torIsoHomology T.X₂ M j).symm
    (torIsoHomology T.X₃ M j).symm (torIsoHomology_inv_naturality T.f M j).symm
    (torIsoHomology_inv_naturality T.g M j).symm

/-- A class in `Tor_j(T.X₂, M)` killed by `T.g` comes from `Tor_j(T.X₁, M)`, for a short exact
sequence `T` of first variables. -/
theorem exists_tor_map_eq_of_tor_map_eq_zero (T : ShortComplex (ModuleCat.{u} A))
    (hT : T.ShortExact) (M : ModuleCat.{u} A) (j : ℕ)
    (z : ((Tor (ModuleCat.{u} A) j).obj T.X₂).obj M)
    (hz : ((Tor (ModuleCat.{u} A) j).map T.g).app M z = 0) :
    ∃ w : ((Tor (ModuleCat.{u} A) j).obj T.X₁).obj M,
      ((Tor (ModuleCat.{u} A) j).map T.f).app M w = z :=
  (ShortComplex.moduleCat_exact_iff (torShortComplex T M j)).mp
    (torShortComplexExact T hT M j) z hz

/-- The connecting map `Tor_{k+1}(S.X₃, M) → Tor_k(S.X₁, M)` of the long exact sequence attached
to a short exact sequence `S` of first variables. -/
noncomputable def torDelta (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact)
    (M : ModuleCat.{u} A) (k : ℕ) :
    ((Tor (ModuleCat.{u} A) (k + 1)).obj S.X₃).obj M ⟶
      ((Tor (ModuleCat.{u} A) k).obj S.X₁).obj M :=
  (torIsoHomology S.X₃ M (k + 1)).hom ≫
    (lesShift.ses A S hS M).δ (k + 1) k (by simp [ComplexShape.down_Rel]) ≫
      (torIsoHomology S.X₁ M k).inv

/-- The map induced on `Tor_{k+1}` by `S.g`, followed by the connecting map, is zero. -/
theorem tor_map_comp_torDelta_eq_zero (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact)
    (M : ModuleCat.{u} A) (k : ℕ) :
    ((Tor (ModuleCat.{u} A) (k + 1)).map S.g).app M ≫ torDelta S hS M k = 0 := by
  have hδ : HomologicalComplex.homologyMap
        ((lesShift.phi A (projectiveResolution M).complex).map S.g) (k + 1)
      ≫ (lesShift.ses A S hS M).δ (k + 1) k (by simp [ComplexShape.down_Rel]) = 0 :=
    (lesShift.ses A S hS M).comp_δ (k + 1) k (by simp [ComplexShape.down_Rel])
  rw [torDelta, ← Category.assoc, torIsoHomology_hom_naturality S.g M (k + 1), Category.assoc,
    ← Category.assoc (HomologicalComplex.homologyMap _ _), hδ, zero_comp, comp_zero]

/-- The segment `Tor_{k+1}(S.X₂, M) → Tor_{k+1}(S.X₃, M) → Tor_k(S.X₁, M)` of the long exact
sequence attached to a short exact sequence `S` of first variables. -/
noncomputable def torShortComplexDelta (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact)
    (M : ModuleCat.{u} A) (k : ℕ) : ShortComplex (ModuleCat.{u} A) :=
  ShortComplex.mk (((Tor (ModuleCat.{u} A) (k + 1)).map S.g).app M) (torDelta S hS M k)
    (tor_map_comp_torDelta_eq_zero S hS M k)

/-- Exactness of `Tor_{k+1}(S.X₂, M) → Tor_{k+1}(S.X₃, M) → Tor_k(S.X₁, M)` for a short exact
sequence `S` of first variables. -/
theorem torShortComplexExact₃ (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact)
    (M : ModuleCat.{u} A) (k : ℕ) : (torShortComplexDelta S hS M k).Exact := by
  have hrel : (ComplexShape.down ℕ).Rel (k + 1) k := by simp [ComplexShape.down_Rel]
  refine ShortComplex.exact_of_iso ?_ ((lesShift.ses A S hS M).homology_exact₃ (k + 1) k hrel)
  refine ShortComplex.isoMk (torIsoHomology S.X₂ M (k + 1)).symm
    (torIsoHomology S.X₃ M (k + 1)).symm (torIsoHomology S.X₁ M k).symm
    (torIsoHomology_inv_naturality S.g M (k + 1)).symm ?_
  show (torIsoHomology S.X₃ M (k + 1)).inv ≫ torDelta S hS M k
    = (lesShift.ses A S hS M).δ (k + 1) k hrel ≫ (torIsoHomology S.X₁ M k).inv
  rw [torDelta, Iso.inv_hom_id_assoc]

/-- A class in `Tor_{k+1}(S.X₃, M)` killed by the connecting map comes from `Tor_{k+1}(S.X₂, M)`,
for a short exact sequence `S` of first variables. -/
theorem exists_tor_map_eq_of_torDelta_eq_zero (S : ShortComplex (ModuleCat.{u} A))
    (hS : S.ShortExact) (M : ModuleCat.{u} A) (k : ℕ)
    (x : ((Tor (ModuleCat.{u} A) (k + 1)).obj S.X₃).obj M) (hx : torDelta S hS M k x = 0) :
    ∃ w : ((Tor (ModuleCat.{u} A) (k + 1)).obj S.X₂).obj M,
      ((Tor (ModuleCat.{u} A) (k + 1)).map S.g).app M w = x :=
  (ShortComplex.moduleCat_exact_iff (torShortComplexDelta S hS M k)).mp
    (torShortComplexExact₃ S hS M k) x hx

/-! ### The two propagation steps -/

/-- If `s` annihilates the source of `f` and `r • y` lies in the image of `f` for every `y`, then
`r * s` annihilates the target of `f`. -/
private theorem mem_annihilator_mul_of_exists_map_eq {X Y : ModuleCat.{u} A} (f : X ⟶ Y) {r s : A}
    (hs : s ∈ Module.annihilator A X) (h : ∀ y : Y, ∃ w : X, f w = r • y) :
    r * s ∈ Module.annihilator A Y := by
  rw [Module.mem_annihilator] at hs ⊢
  intro y
  obtain ⟨w, hw⟩ := h y
  rw [mul_comm, mul_smul, ← hw, ← map_smul, hs w, map_zero]

/-- Annihilation of the middle term of a short exact sequence of first variables: if `r`
annihilates `T.X₃` and `s` annihilates `Tor_j(T.X₁, M)` in all degrees `j ≥ m`, then `r * s`
annihilates `Tor_j(T.X₂, M)` in all degrees `j ≥ m`. -/
theorem mem_annihilator_tor_middle (T : ShortComplex (ModuleCat.{u} A)) (hT : T.ShortExact)
    (M : ModuleCat.{u} A) {r s : A} {m : ℕ} (hr : r ∈ Module.annihilator A T.X₃)
    (hs : ∀ j, m ≤ j → s ∈ Module.annihilator A (((Tor (ModuleCat.{u} A) j).obj T.X₁).obj M)) :
    ∀ j, m ≤ j → r * s ∈ Module.annihilator A (((Tor (ModuleCat.{u} A) j).obj T.X₂).obj M) := by
  intro j hj
  exact mem_annihilator_mul_of_exists_map_eq _ (hs j hj) fun z =>
    exists_tor_map_eq_of_tor_map_eq_zero T hT M j (r • z) (by
      rw [map_smul]
      exact Module.mem_annihilator.mp (mem_annihilator_tor_of_mem_annihilator T.X₃ M j hr) _)

/-- The dimension-shifting annihilation step: if `v` annihilates `Tor_j(S.X₁, M)` in all degrees
`j ≥ m` and `u` annihilates `Tor_i(S.X₂, M)` in all degrees `i ≥ p`, then `v * u` annihilates
`Tor_i(S.X₃, M)` in all degrees `i ≥ m + 1` with `i ≥ p`. -/
theorem mem_annihilator_tor_of_shift (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact)
    (M : ModuleCat.{u} A) {v u : A} {m p : ℕ}
    (hv : ∀ j, m ≤ j → v ∈ Module.annihilator A (((Tor (ModuleCat.{u} A) j).obj S.X₁).obj M))
    (hu : ∀ i, p ≤ i → u ∈ Module.annihilator A (((Tor (ModuleCat.{u} A) i).obj S.X₂).obj M)) :
    ∀ i, m + 1 ≤ i → p ≤ i →
      v * u ∈ Module.annihilator A (((Tor (ModuleCat.{u} A) i).obj S.X₃).obj M) := by
  intro i hmi hpi
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  exact mem_annihilator_mul_of_exists_map_eq _ (hu (k + 1) hpi) fun x =>
    exists_tor_map_eq_of_torDelta_eq_zero S hS M k (v • x) (by
      rw [map_smul]
      exact Module.mem_annihilator.mp (hv k (by omega)) _)
