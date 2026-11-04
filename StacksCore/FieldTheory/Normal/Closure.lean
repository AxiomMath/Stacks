module

public import Mathlib.FieldTheory.Normal.Closure
import StacksCore.FieldTheory.IntermediateField.Adjoin.Algebra
import StacksCore.FieldTheory.IntermediateField.Adjoin.Defs
import StacksCore.FieldTheory.Normal.Basic
public import StacksCore.RingTheory.PiTensorProduct
import StacksCore.Tactic.StacksAttribute

/-! # Normal closure -/

@[expose] public section

add_to_stacks 09DT "the relative normal closure" IntermediateField.normalClosure
add_to_stacks 0BMG "relative normal closure (covers 1 and 2)" IntermediateField.normalClosure
add_to_stacks 09DT "normal" normalClosure.normal
add_to_stacks 09DT "finite dimensional" normalClosure.is_finiteDimensional
add_to_stacks 09DT "unique" IsNormalClosure.equiv

open IntermediateField

attribute [mk_iff] IsNormalClosure

/-- Auxiliary definition for `AlgHom.liftNormalClosure`. -/
noncomputable def AlgHom.liftNormalClosureAux
    {F E N L : Type*} [Field F] [Field E] [Field N] [Field L]
    [Algebra F E] [Algebra F N] [Algebra F L]
    [IsNormalClosure F E N] [Normal F L]
    (i : E →ₐ[F] L) (j : E →ₐ[F] N) : {g : N →ₐ[F] L // g.comp j = i} :=
  let φ : N →ₐ[F] L := IsNormalClosure.lift fun x : E ↦ by
    simpa [minpoly.algHom_eq i i.injective] using Normal.splits' (F := F) (i x)
  let : Algebra E L := i.toAlgebra
  let : Algebra N L := φ.toAlgebra
  let c : L ≃ₐ[F] L := (Algebra.IsAlgebraic.algEquivEquivAlgHom F L).symm <| j.liftNormal L
  have hc (x : E) : c (i x) = φ (j x) := j.liftNormal_commutes L x
  ⟨c.symm.toAlgHom.comp (Algebra.algHom F N L), AlgHom.ext fun x ↦ by
    simp [AlgEquiv.symm_apply_eq, hc]; rfl⟩

/-- Let `N/F` be a normal closure of `E/F`, and let `L/F` be an arbitrary normal extension.
Then any `E →ₐ[F] L` can be lifted along any `E →ₐ[F] N` to an embedding `N →ₐ[F] L` that
makes the triangle commute.
-/
noncomputable def AlgHom.liftNormalClosure
    {F E N L : Type*} [Field F] [Field E] [Field N] [Field L]
    [Algebra F E] [Algebra F N] [Algebra F L]
    [IsNormalClosure F E N] [Normal F L]
    (i : E →ₐ[F] L) (j : E →ₐ[F] N) : N →ₐ[F] L := (i.liftNormalClosureAux j).1

theorem AlgHom.liftNormalClosure_commutes
    {F E N L : Type*} [Field F] [Field E] [Field N] [Field L]
    [Algebra F E] [Algebra F N] [Algebra F L]
    [IsNormalClosure F E N] [Normal F L]
    (i : E →ₐ[F] L) (j : E →ₐ[F] N) :
    (i.liftNormalClosure j).comp j = i := (i.liftNormalClosureAux j).2

@[simp] theorem AlgHom.liftNormalClosure_commutes'
    {F E N L : Type*} [Field F] [Field E] [Field N] [Field L]
    [Algebra F E] [Algebra F N] [Algebra F L]
    [IsNormalClosure F E N] [Normal F L]
    (i : E →ₐ[F] L) (j : E →ₐ[F] N) (x : E) :
    i.liftNormalClosure j (j x) = i x := congr($(liftNormalClosure_commutes i j) x)

/-- An even more relative version of `normalClosure`. Given `L/N/M` and `L/K` and `N/K`,
the normal closure of `N/K` in `L/K` is actually an `M`-subalgebra of `L`. -/
noncomputable def normalClosure' (K M N L : Type*)
    [Field K] [Field M] [Field N] [Field L]
    [Algebra K N] [Algebra K L] [Algebra M N] [Algebra M L] [Algebra N L]
    [IsScalarTower K N L] [IsScalarTower M N L] :
    IntermediateField M L where
  __ := normalClosure K N L
  algebraMap_mem' x := (Algebra.algHom K N L).fieldRange_le_normalClosure ⟨algebraMap M N x, by
    simp [Algebra.algHom, ← IsScalarTower.algebraMap_apply]⟩

@[stacks 0BMG "2, containment"]
noncomputable instance normalClosure.algebraOfTower (K M N L : Type*)
    [Field K] [Field M] [Field N] [Field L]
    [Algebra K N] [Algebra K L] [Algebra M N] [Algebra M L] [Algebra N L]
    [IsScalarTower K N L] [IsScalarTower M N L] :
    Algebra M (normalClosure K N L) :=
  (normalClosure' K M N L).algebra

/-- Given `L/N/M/K`, the normal closure of `N/M` in `L/M` is contained in the normal closure of
`N/K` in `L/K`. -/
theorem normalClosure_le_normalClosure' (K M N L : Type*)
    [Field K] [Field M] [Field N] [Field L]
    [Algebra K M] [Algebra K N] [Algebra K L] [Algebra M N] [Algebra M L] [Algebra N L]
    [IsScalarTower K M N] [IsScalarTower K M L] [IsScalarTower K N L] [IsScalarTower M N L] :
    normalClosure M N L ≤ normalClosure' K M N L :=
  normalClosure_le_iff.mpr fun f ↦ (f.restrictScalars K).fieldRange_le_normalClosure

/-- If we have `L/N/M/K` where `M/K` is normal and `N/M` is finite dimensional then
the normal closure of `N/K` in `L/K` is finite dimensional over `M`. -/
@[stacks 0BMG "2, finite"]
theorem finiteDimensional_normalClosure_of_tower (K M N L : Type*)
    [Field K] [Field M] [Field N] [Field L]
    [Algebra K M] [Algebra K N] [Algebra K L] [Algebra M N] [Algebra M L] [Algebra N L]
    [IsScalarTower K M N] [IsScalarTower K M L] [IsScalarTower K N L] [IsScalarTower M N L]
    [FiniteDimensional M N] [Normal K M] : FiniteDimensional M (normalClosure K N L) := by
  classical
  have : Algebra.IsAlgebraic K N := .trans K M N
  let b := Module.finBasis M N
  have hmb : adjoin M (Set.range b) = ⊤ := eq_top_iff.mpr <| by
    rw [← toSubalgebra_le_toSubalgebra, top_toSubalgebra]
    rw [adjoin_toSubalgebra_of_isAlgebraic fun _ _ ↦ Algebra.IsAlgebraic.isAlgebraic _,
      ← Algebra.adjoin_span, b.span_eq, Submodule.top_coe, Algebra.adjoin_univ]
  replace hmb := congr(($hmb).restrictScalars K)
  rw [restrictScalars_adjoin', restrictScalars_top] at hmb
  let roots := Finset.univ.biUnion fun i ↦ ((minpoly K (b i)).aroots L).toFinset
  have hroots (x) (hx : x ∈ roots) : IsIntegral K x := by
    obtain ⟨p, hp1, hp2⟩ := by simpa [roots] using hx
    exact IsAlgebraic.isIntegral ⟨minpoly K (b p), hp1, hp2⟩
  let C := adjoin M (roots : Set L)
  have hc : normalClosure K N L ≤ C.restrictScalars K := normalClosure_le_iff.mpr fun f ↦ by
    rw [AlgHom.fieldRange_eq_map, map_le_iff_le_comap, ← hmb, adjoin_le_iff, Set.union_subset_iff]
    simp_rw [Set.range_subset_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ subset_adjoin _ _ ?_⟩
    · change f.comp (Algebra.algHom K M N) x ∈ C
      obtain ⟨y, hy⟩ := (f.comp (Algebra.algHom K M N)).exists_algebraMap_of_normal x
      rw [hy]
      exact _root_.algebraMap_mem _ _
    · simpa [roots] using ⟨i, by simp [minpoly.ne_zero (Algebra.IsIntegral.isIntegral _)]⟩
  have : FiniteDimensional M C := finiteDimensional_adjoin fun _ hx ↦ (hroots _ hx).tower_top
  exact Submodule.finiteDimensional_of_le (S₁ := (normalClosure' K M N L).toSubmodule)
    (S₂ := C.toSubmodule) hc

theorem normal_iff_comp_surjective
    {F E N : Type*} [Field F] [Field E] [Field N]
    [Algebra F E] [Algebra F N] [Normal F N] (i : E →ₐ[F] N) :
    Normal F E ↔ Function.Surjective (i.comp : (E →ₐ[F] E) → (E →ₐ[F] N)) := by
  algebraize [i.toRingHom]
  have : Algebra.IsAlgebraic F E := .tower_bot F E N
  have hi : ⇑i = algebraMap E N := rfl
  refine ⟨fun _ x ↦ ⟨x.restrictNormal E, by ext; simp [hi]⟩, fun h ↦ ?_⟩
  let e : E ≃ₐ[F] i.fieldRange := .ofInjectiveField i
  simp_rw [e.transfer_normal, normal_iff_forall_fieldRange_le,
    (e.arrowCongr .refl).surjective.forall, h.forall,
    (Algebra.IsAlgebraic.algEquivEquivAlgHom F E).surjective.forall]
  simp [fieldRange_comp, ← AlgHom.fieldRange_eq_map]

theorem normal_iff_comp_bijective
    {F E N : Type*} [Field F] [Field E] [Field N]
    [Algebra F E] [Algebra F N] [Normal F N] (i : E →ₐ[F] N) :
    Normal F E ↔ Function.Bijective (i.comp : (E →ₐ[F] E) → (E →ₐ[F] N)) := by
  have : Function.Injective (i.comp (A := E)) := fun _ _ ↦ (AlgHom.cancel_left i.injective).mp
  simp_rw [normal_iff_comp_surjective i, Function.Bijective, this, true_and]

open TensorProduct PiTensorProduct

/-- **Stacks 0EXL** (the underlying map).
The canonical `F`-algebra map `(⨂[F] _ : K →ₐ[F] L, K) →ₐ[F] L` whose restriction to the tensor
factor indexed by an embedding `f : K →ₐ[F] L` is `f` itself; equivalently, on a pure tensor
`tprod F x` it returns `∏ f, f (x f)`. When `L` is a normal closure of an algebraic extension
`K/F` this map is surjective; see `IsNormalClosure.piTensorProductEmbeddings_surjective`. -/
@[stacks 0EXL]
def piTensorProductEmbeddings (F K L : Type*)
    [CommSemiring F] [Semiring K] [CommSemiring L] [Algebra F K] [Algebra F L]
    [Fintype (K →ₐ[F] L)] : (⨂[F] _ : K →ₐ[F] L, K) →ₐ[F] L :=
  productMap id

@[simp] theorem piTensorProductEmbeddings_tprod {F K L : Type*}
    [CommSemiring F] [Semiring K] [CommSemiring L] [Algebra F K] [Algebra F L]
    [Fintype (K →ₐ[F] L)] (x : (K →ₐ[F] L) → K) :
    piTensorProductEmbeddings F K L (tprod F x) = ∏ f : K →ₐ[F] L, f (x f) := by
  simp [piTensorProductEmbeddings]

/-- The map `piTensorProductEmbeddings F K L` sends the generator `of F _ f x` of the
`f`-indexed tensor factor to `f x`. -/
@[simp] theorem piTensorProductEmbeddings_of {F K L : Type*}
    [CommSemiring F] [Semiring K] [CommSemiring L] [Algebra F K] [Algebra F L]
    [Fintype (K →ₐ[F] L)] [DecidableEq (K →ₐ[F] L)] (f : K →ₐ[F] L) (x : K) :
    piTensorProductEmbeddings F K L (of F _ f x) = f x := by simp [piTensorProductEmbeddings]

/-- **Stacks 0EXL** (range).
For an algebraic extension `K/F`, the range of `piTensorProductEmbeddings F K L` as a subalgebra
of `L` is exactly the normal closure of `K/F` inside `L`. -/
@[stacks 0EXL]
theorem range_piTensorProductEmbeddings (F K L : Type*)
    [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [Fintype (K →ₐ[F] L)] [Algebra.IsAlgebraic F K] :
    (piTensorProductEmbeddings F K L).range = (normalClosure F K L).toSubalgebra := by
  have (f : K →ₐ[F] L) : Algebra.IsAlgebraic F f.fieldRange :=
    (AlgEquiv.ofInjectiveField f).isAlgebraic
  simp [piTensorProductEmbeddings, range_productMap, normalClosure,
    iSup_toSubalgebra_of_isAlgebraic]

instance (F E N : Type*) [Field F] [Field E] [Field N]
    [Algebra F E] [Algebra F N] [Algebra.IsAlgebraic F E] [IsNormalClosure F E N] :
    Nonempty (E →ₐ[F] N) :=
  nonempty_algHom_of_splits fun x ↦ ⟨Algebra.IsIntegral.isIntegral x, IsNormalClosure.splits x⟩

/-- A **non-canonical** embedding to any arbitrary normal closure. -/
@[stacks 09DT "extends"]
noncomputable def IsNormalClosure.of
    (F E N : Type*) [Field F] [Field E] [Field N]
    [Algebra F E] [Algebra F N] [Algebra.IsAlgebraic F E] [IsNormalClosure F E N] : E →ₐ[F] N :=
  Nonempty.some inferInstance

theorem IsNormalClosure.normalClosure_eq_top (F K L : Type*)
    [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [Algebra.IsAlgebraic F K] [IsNormalClosure F K L] :
    normalClosure F K L = ⊤ := (Algebra.IsAlgebraic.isNormalClosure_iff.mp ‹_›).2

@[stacks 09DT]
theorem IsNormalClosure.finiteDimensional
    (F E N : Type*) [Field F] [Field E] [Field N] [Algebra F E] [Algebra F N]
    [IsNormalClosure F E N] [FiniteDimensional F E] : FiniteDimensional F N := by
  suffices FiniteDimensional F (⊤ : IntermediateField F N) from
    topEquiv.toLinearEquiv.finiteDimensional
  have (f : E →ₐ[F] N) : FiniteDimensional F f.fieldRange :=
    (AlgEquiv.ofInjectiveField f).toLinearEquiv.finiteDimensional
  rw [← normalClosure_eq_top F E N, normalClosure]
  infer_instance

/-- **Stacks 0EXL** (surjectivity).
If `L` is a normal closure of an algebraic extension `K/F`, then the canonical `F`-algebra map
`piTensorProductEmbeddings F K L : (⨂[F] _ : K →ₐ[F] L, K) →ₐ[F] L` is surjective. -/
@[stacks 0EXL "surjective"]
theorem IsNormalClosure.piTensorProductEmbeddings_surjective
    (F K L : Type*) [Field F] [Field K] [Field L] [Algebra F K] [Algebra F L]
    [Fintype (K →ₐ[F] L)] [Algebra.IsAlgebraic F K] [IsNormalClosure F K L] :
    Function.Surjective (piTensorProductEmbeddings F K L) := by
  rw [← AlgHom.range_eq_top, range_piTensorProductEmbeddings, normalClosure_eq_top,
    top_toSubalgebra]
