module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamRowQuasiIso
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.DoubleComplexRowComparison

/-!
# The rows of the double complex of a cosimplicial pair, compared with the row zero

Let `W` be a cosimplicial module over the completed cosimplicial rings `D̂(*)` carrying a completed
connection in each cosimplicial degree, `Crystalline.CosimplicialCompletedPair`, and let
`K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` be its double complex.  This module compares every row
`K^{*,b}` with the row `K^{*,0}`, through the maps induced by the codiagonal `D(b) → D` and by
the coprojection `D → D(b)` onto the vertex `0`.

## Main definitions

* `Crystalline.CosimplicialCompletedPair.rowToZeroHom` — the map `K^{*,b} ⟶ K^{*,0}` induced by
  the unique map `⦋b⦌ ⟶ ⦋0⦌` of finite ordinals, i.e. by the codiagonal.
* `Crystalline.CosimplicialCompletedPair.rowZeroComparison` — the morphism from the double complex
  to the constant double complex on the row zero assembled from these maps.
* `Crystalline.CosimplicialCompletedPair.rowFromZeroHom` — the map `K^{*,0} ⟶ K^{*,b}` induced by
  the coprojection `⦋0⦌ ⟶ ⦋b⦌` onto the vertex `0`, a section of `rowToZeroHom`.

## Main results

* `Crystalline.CosimplicialCompletedPair.quasiIso_flipMap_rowZeroComparison` — **the rowwise
  hypothesis of the degeneration**: as soon as each `rowFromZeroDeg b` has a degreewise retraction
  `π` with `ι ∘ π` homotopic to the identity, every row of the morphism `rowZeroComparison` is a
  quasi-isomorphism.
* `Crystalline.CosimplicialCompletedPair.rowZeroColumnZeroHomologyIso` — **the cohomology of the
  row zero `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}` is the cohomology of the Moore complex of
  `M(0) → M(1) → ⋯`**, given those retractions and the acyclicity of the columns `a > 0`.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
-/

@[expose] public noncomputable section

universe u v w

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial

namespace Crystalline

namespace CosimplicialCompletedPair

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (W : CosimplicialCompletedPair.{u, v, w} E p)

/-- Two maps of finite ordinals into `⦋0⦌` agree. -/
theorem hom_toZero_ext {m : SimplexCategory} (φ ψ : m ⟶ ⦋0⦌) : φ = ψ :=
  SimplexCategory.isTerminalZero.hom_ext φ ψ

/-- **The map `K^{a,b} ⟶ K^{a,0}` of the double complex induced by the unique map `⦋b⦌ ⟶ ⦋0⦌`**,
read in one exterior degree. -/
def rowToZeroDeg (b a : ℕ) :
    W.toCosimplicialCompletedModule.obj a b →+ W.toCosimplicialCompletedModule.obj a 0 :=
  (W.toCosimplicialCompletedModule.tensorMap (SimplexCategory.const ⦋b⦌ ⦋0⦌ 0) a).toAddMonoidHom

/-- **The map `K^{a,0} ⟶ K^{a,b}` of the double complex induced by the coprojection
`⦋0⦌ ⟶ ⦋b⦌` onto the vertex `0`**, read in one exterior degree. -/
def rowFromZeroDeg (b a : ℕ) :
    W.toCosimplicialCompletedModule.obj a 0 →+ W.toCosimplicialCompletedModule.obj a b :=
  (W.toCosimplicialCompletedModule.tensorMap (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) a).toAddMonoidHom

/-- The coprojection followed by the codiagonal is the identity of `⦋0⦌`. -/
theorem const_comp_const_toZero (b : ℕ) :
    SimplexCategory.const ⦋0⦌ ⦋b⦌ 0 ≫ SimplexCategory.const ⦋b⦌ ⦋0⦌ 0 = 𝟙 ⦋0⦌ :=
  hom_toZero_ext _ _

/-- **The codiagonal retracts the coprojection**, in every exterior degree. -/
theorem rowToZeroDeg_rowFromZeroDeg (b a : ℕ) (x : W.toCosimplicialCompletedModule.obj a 0) :
    W.rowToZeroDeg b a (W.rowFromZeroDeg b a x) = x := by
  change W.toCosimplicialCompletedModule.tensorMap (SimplexCategory.const ⦋b⦌ ⦋0⦌ 0) a
      (W.toCosimplicialCompletedModule.tensorMap (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) a x) = x
  rw [← W.toCosimplicialCompletedModule.tensorMap_comp, const_comp_const_toZero,
    W.toCosimplicialCompletedModule.tensorMap_id]

/-- The codiagonal commutes with the de Rham differential. -/
theorem degreeDifferential_rowToZeroDeg (b a : ℕ) (x : W.toCosimplicialCompletedModule.obj a b) :
    W.degreeDifferential 0 a (W.rowToZeroDeg b a x) =
      W.rowToZeroDeg b (a + 1) (W.degreeDifferential b a x) :=
  W.degreeDifferential_tensorMap (SimplexCategory.const ⦋b⦌ ⦋0⦌ 0) a x

/-- The coprojection commutes with the de Rham differential. -/
theorem degreeDifferential_rowFromZeroDeg (b a : ℕ)
    (x : W.toCosimplicialCompletedModule.obj a 0) :
    W.degreeDifferential b a (W.rowFromZeroDeg b a x) =
      W.rowFromZeroDeg b (a + 1) (W.degreeDifferential 0 a x) :=
  W.degreeDifferential_tensorMap (SimplexCategory.const ⦋0⦌ ⦋b⦌ 0) a x

/-- **The comparison of the double complex with the constant double complex on its row zero**:
in the simplex `m` and the exterior degree `a` it is the map induced by the unique map
`m ⟶ ⦋0⦌`. -/
def rowZeroComparison :
    W.doubleComplex ⟶ constantCosimplicialCochainComplex.obj (W.degreeDeRhamComplex 0) :=
  CosimplicialDoubleComplex.constHom (K := W.doubleComplex) (W.degreeDeRhamComplex 0)
    (fun a m => AddCommGrpCat.ofHom
      (W.toCosimplicialCompletedModule.tensorMap (SimplexCategory.const m ⦋0⦌ 0) a).toAddMonoidHom)
    (fun a m n φ => AddCommGrpCat.ext fun x =>
      (W.toCosimplicialCompletedModule.tensorMap_comp φ (SimplexCategory.const n ⦋0⦌ 0) a
        x).symm.trans
        (congrArg (fun ψ => W.toCosimplicialCompletedModule.tensorMap ψ a x)
          (hom_toZero_ext _ _)))
    (fun a a' m => by
      by_cases h : a + 1 = a'
      · subst h
        rw [W.degreeDeRhamComplex_d 0 a, W.doubleComplex_d a]
        refine AddCommGrpCat.ext fun x => ?_
        exact W.degreeDifferential_tensorMap (SimplexCategory.const m ⦋0⦌ 0) a x
      · rw [(W.degreeDeRhamComplex 0).shape a a' h, W.doubleComplex.shape a a' h]
        exact AddCommGrpCat.ext fun x => rfl)

/-- The row `b` of `rowZeroComparison` is the codiagonal map `rowToZeroDeg`, degree by degree. -/
theorem rowDeRhamComparison_rowZeroComparison_f (b a : ℕ)
    (x : W.toCosimplicialCompletedModule.obj a b) :
    (W.rowDeRhamComparison W.rowZeroComparison b).f a x = W.rowToZeroDeg b a x :=
  rfl

/-- **The rowwise hypothesis of the degeneration from a retraction of every coprojection.**

For every cosimplicial degree `b`, let `π_b` be a degreewise retraction of the coprojection
`ι_b = rowFromZeroDeg b : K^{*,0} ⟶ K^{*,b}` which commutes with the de Rham differentials and
such that `ι_b ∘ π_b` is homotopic to the identity through `h_b`.  Then every row of
`rowZeroComparison` is a quasi-isomorphism. -/
theorem quasiIso_flipMap_rowZeroComparison
    (piDeg : ∀ b i : ℕ, W.toCosimplicialCompletedModule.obj i b →+
      W.toCosimplicialCompletedModule.obj i 0)
    (hDeg : ∀ b i : ℕ, W.toCosimplicialCompletedModule.obj (i + 1) b →+
      W.toCosimplicialCompletedModule.obj i b)
    (hpi : ∀ (b i : ℕ) (y : W.toCosimplicialCompletedModule.obj i b),
      W.degreeDifferential 0 i (piDeg b i y) = piDeg b (i + 1) (W.degreeDifferential b i y))
    (hretract : ∀ (b i : ℕ) (x : W.toCosimplicialCompletedModule.obj i 0),
      piDeg b i (W.rowFromZeroDeg b i x) = x)
    (h0 : ∀ (b : ℕ) (x : W.toCosimplicialCompletedModule.obj 0 b),
      hDeg b 0 (W.degreeDifferential b 0 x) + W.rowFromZeroDeg b 0 (piDeg b 0 x) = x)
    (hsucc : ∀ (b i : ℕ) (x : W.toCosimplicialCompletedModule.obj (i + 1) b),
      W.degreeDifferential b i (hDeg b i x) +
          hDeg b (i + 1) (W.degreeDifferential b (i + 1) x) +
          W.rowFromZeroDeg b (i + 1) (piDeg b (i + 1) x) = x)
    (b : ℤ) :
    QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map W.rowZeroComparison)).f b) := by
  refine W.quasiIso_flipMap_of_deRhamDegreewiseHomotopyEquiv W.rowZeroComparison
    (fun c i => AddCommGrpCat.ofHom (W.rowFromZeroDeg c i))
    (fun c i => AddCommGrpCat.ofHom (piDeg c i))
    (fun c i => AddCommGrpCat.ofHom (hDeg c i)) (fun c i => ?_) (fun c i => ?_)
    (fun c i => AddCommGrpCat.ext fun x => hretract c i x) (fun c => ?_) (fun c i => ?_)
    (fun c i => AddCommGrpCat.ext fun x => W.rowToZeroDeg_rowFromZeroDeg c i x) b
  all_goals simp only [degreeDeRhamComplex_d]
  · exact AddCommGrpCat.ext fun x => W.degreeDifferential_rowFromZeroDeg c i x
  · exact AddCommGrpCat.ext fun x => hpi c i x
  · exact AddCommGrpCat.ext fun x => h0 c x
  · refine AddCommGrpCat.ext fun x => ?_
    change hDeg c (i + 1) (W.degreeDifferential c (i + 1) x) +
        W.degreeDifferential c i (hDeg c i x) +
        W.rowFromZeroDeg c (i + 1) (piDeg c (i + 1) x) = x
    refine Eq.trans ?_ (hsucc c i x)
    abel

/-- **The cohomology of the row zero `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}` is the cohomology of the Moore
complex of the column zero `M(0) → M(1) → M(2) → ⋯`**, given the acyclicity of the columns
`a > 0` — [Stacks, Lemma 60.19.1, Tag 07LA] for a crystal — and a retraction of every coprojection
with the homotopy of [Stacks, Lemma 60.21.2, Tag 07LD]. -/
def rowZeroColumnZeroHomologyIso
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X n)).homology j))
    (piDeg : ∀ b i : ℕ, W.toCosimplicialCompletedModule.obj i b →+
      W.toCosimplicialCompletedModule.obj i 0)
    (hDeg : ∀ b i : ℕ, W.toCosimplicialCompletedModule.obj (i + 1) b →+
      W.toCosimplicialCompletedModule.obj i b)
    (hpi : ∀ (b i : ℕ) (y : W.toCosimplicialCompletedModule.obj i b),
      W.degreeDifferential 0 i (piDeg b i y) = piDeg b (i + 1) (W.degreeDifferential b i y))
    (hretract : ∀ (b i : ℕ) (x : W.toCosimplicialCompletedModule.obj i 0),
      piDeg b i (W.rowFromZeroDeg b i x) = x)
    (h0 : ∀ (b : ℕ) (x : W.toCosimplicialCompletedModule.obj 0 b),
      hDeg b 0 (W.degreeDifferential b 0 x) + W.rowFromZeroDeg b 0 (piDeg b 0 x) = x)
    (hsucc : ∀ (b i : ℕ) (x : W.toCosimplicialCompletedModule.obj (i + 1) b),
      W.degreeDifferential b i (hDeg b i x) +
          hDeg b (i + 1) (W.degreeDifferential b (i + 1) x) +
          W.rowFromZeroDeg b (i + 1) (piDeg b (i + 1) x) = x)
    (j : ℕ) :
    (W.degreeDeRhamComplex 0).homology j ≅
      ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X 0)).homology j :=
  (W.rowZeroHomologyIso j).symm ≪≫
    cosimplicialDoubleComplexRowComparisonHomologyIso W.doubleComplex (W.degreeDeRhamComplex 0)
      W.rowZeroComparison hcol
      (W.quasiIso_flipMap_rowZeroComparison piDeg hDeg hpi hretract h0 hsucc) j

/-! ### The quasi-isomorphism form -/

/-- **The coprojection `K^{*,0} ⟶ K^{*,b}` as a morphism of complexes**, the map
`M(0) ⊗^∧_{D(0)} Ω^*_{D(0)} ⟶ M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` induced by `⦋0⦌ ⟶ ⦋b⦌, 0 ↦ 0`. -/
def rowFromZeroHom (b : ℕ) : W.degreeDeRhamComplex 0 ⟶ W.degreeDeRhamComplex b :=
  cochainComplexHomOfDegreewise (fun i => AddCommGrpCat.ofHom (W.rowFromZeroDeg b i))
    (fun i => by
      rw [W.degreeDeRhamComplex_d b i, W.degreeDeRhamComplex_d 0 i]
      exact AddCommGrpCat.ext fun x => W.degreeDifferential_rowFromZeroDeg b i x)

/-- **The codiagonal `K^{*,b} ⟶ K^{*,0}` as a morphism of complexes**, induced by the unique map
`⦋b⦌ ⟶ ⦋0⦌`. -/
def rowToZeroHom (b : ℕ) : W.degreeDeRhamComplex b ⟶ W.degreeDeRhamComplex 0 :=
  cochainComplexHomOfDegreewise (fun i => AddCommGrpCat.ofHom (W.rowToZeroDeg b i))
    (fun i => by
      rw [W.degreeDeRhamComplex_d b i, W.degreeDeRhamComplex_d 0 i]
      exact AddCommGrpCat.ext fun x => W.degreeDifferential_rowToZeroDeg b i x)

/-- The codiagonal retracts the coprojection, as morphisms of complexes. -/
theorem rowFromZeroHom_rowToZeroHom (b : ℕ) :
    W.rowFromZeroHom b ≫ W.rowToZeroHom b = 𝟙 _ :=
  HomologicalComplex.hom_ext _ _ fun i =>
    AddCommGrpCat.ext fun x => W.rowToZeroDeg_rowFromZeroDeg b i x

/-- The row `b` of `rowZeroComparison`, read through `rowDeRhamIso`, is the codiagonal. -/
theorem rowDeRhamComparison_rowZeroComparison (b : ℕ) :
    W.rowDeRhamComparison W.rowZeroComparison b = W.rowToZeroHom b :=
  HomologicalComplex.hom_ext _ _ fun _ => AddCommGrpCat.ext fun _ => rfl

/-- **The rowwise hypothesis of the degeneration from the quasi-isomorphy of the
coprojections.**  If every coprojection `rowFromZeroHom b` is a quasi-isomorphism, then every row
of `rowZeroComparison` is one. -/
theorem quasiIso_flipMap_rowZeroComparison_of_quasiIso
    (hq : ∀ b : ℕ, QuasiIso (W.rowFromZeroHom b)) (b : ℤ) :
    QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map W.rowZeroComparison)).f b) := by
  refine quasiIso_flipMap_of_quasiIso_row _ (fun c => ?_) b
  have := hq c
  have : QuasiIso (W.rowFromZeroHom c ≫ W.rowToZeroHom c) := by
    rw [rowFromZeroHom_rowToZeroHom]
    infer_instance
  have hT : QuasiIso (W.rowToZeroHom c) := quasiIso_of_comp_left (W.rowFromZeroHom c) _
  rw [W.cosimplicialRowMap_eq_rowDeRhamComparison, rowDeRhamComparison_rowZeroComparison]
  exact (quasiIso_iff_comp_left _ _).mpr hT

/-- **The cohomology of the row zero is the cohomology of the Moore complex of the column zero**,
given the acyclicity of the columns `a > 0` and the quasi-isomorphy of every coprojection
`M(0) ⊗^∧_{D(0)} Ω^*_{D(0)} ⟶ M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}`, which is
[Stacks, Lemma 60.21.2, Tag 07LD]. -/
def rowZeroColumnZeroHomologyIsoOfQuasiIso
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X n)).homology j))
    (hq : ∀ b : ℕ, QuasiIso (W.rowFromZeroHom b)) (j : ℕ) :
    (W.degreeDeRhamComplex 0).homology j ≅
      ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X 0)).homology j :=
  (W.rowZeroHomologyIso j).symm ≪≫
    cosimplicialDoubleComplexRowComparisonHomologyIso W.doubleComplex (W.degreeDeRhamComplex 0)
      W.rowZeroComparison hcol (W.quasiIso_flipMap_rowZeroComparison_of_quasiIso hq) j

end CosimplicialCompletedPair

end Crystalline

end
