module

public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamRowRetraction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DerivedColimitPointResolution

/-!
# The zigzag of [Stacks, Proposition 60.21.3, Tag 07LG] at the level of complexes

The proof of [Stacks, Tag 07LG] compares the Moore complex of the column zero
`M(0) → M(1) → M(2) → ⋯` of the double complex `K^{a,b} = M(b) ⊗̂_{D(b)} Ω^a_{D(b)}` with its row
zero `M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}` through the total complex.  This file gives that comparison
as an explicit zigzag of quasi-isomorphisms of `ℤ`-indexed cochain complexes of abelian groups,

`M(•) ⟵ Tot(K) ⟶ Tot(Const(K^{*,0})) ⟵ K^{*,0}`,

where `Const(K^{*,0})` is the constant double complex on the row zero.  The first map is the
projection onto the column zero, a quasi-isomorphism when the columns `a > 0` are acyclic
([Stacks, Lemma 60.19.1, Tag 07LA]); the second is induced by
`Crystalline.CosimplicialCompletedPair.rowZeroComparison`, a quasi-isomorphism when every
coprojection `K^{*,0} ⟶ K^{*,b}` is one ([Stacks, Lemma 60.21.2, Tag 07LD]); the third is the
inclusion of the row zero, always a quasi-isomorphism because the columns of `Const(K^{*,0})`
resolve their degree-zero terms.

It then introduces morphisms of cosimplicial divided power algebras and of cosimplicial pairs
over them, and shows that a morphism of pairs induces morphisms of the double complexes, of the
completed de Rham complexes of each cosimplicial degree and of the Moore complexes of the
columns zero, compatibly with every leg of the zigzag.

## Main definitions

* `Crystalline.cosimplicialTotalToColumnZero`, `Crystalline.cosimplicialTotalMap` and
  `Crystalline.cosimplicialRowZeroToTotal` — the three legs, for any cochain complex of
  cosimplicial abelian groups.
* `Crystalline.CosimplicialCompletedPair.zigzagColumnZero`, `...zigzagTotal` and
  `...zigzagRowZero` — the three legs for the double complex of a pair, and
  `...zigzagHomologyIso` the isomorphism on cohomology they induce.
* `Crystalline.CosimplicialDPAlgebra.Hom` — a morphism of cosimplicial divided power algebras.
* `Crystalline.CosimplicialCompletedPair.Hom` — a morphism of pairs over such a morphism, with
  `...Hom.doubleComplexMap`, `...Hom.degreeDeRhamMap` and `...Hom.columnZeroMooreMap`.

## Main results

* `Crystalline.CosimplicialCompletedPair.quasiIso_zigzagColumnZero`, `...quasiIso_zigzagTotal`
  and the instance `...quasiIso_zigzagRowZero` — the three legs are quasi-isomorphisms.
* `Crystalline.CosimplicialCompletedPair.Hom.zigzagColumnZero_naturality`,
  `...zigzagTotal_naturality`, `...zigzagRowZero_naturality` and
  `...zigzagHomologyIso_naturality` — the zigzag is natural in the pair.

## References

* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
* [Stacks Project, Lemma 60.19.1, Tag 07LA](https://stacks.math.columbia.edu/tag/07LA)
* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial

universe u v w

namespace Crystalline

open StacksDraft.TotalComplexQuasiIso

attribute [local instance] StacksDraft.TotalComplexQuasiIso.hasTotal_singleColumn
  StacksDraft.TotalComplexQuasiIso.isIso_totalSingleColumnUnit

section General

variable (K : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ)

/-- The column `-1` of the double complex of `K` vanishes. -/
theorem isZero_cosimplicialDoubleComplex_X_neg_one :
    IsZero ((cosimplicialDoubleComplexFunctor.obj K).X ((0 : ℤ) - 1)) :=
  StacksDraft.TotalDegeneration.isZero_X_neg_one _
    (fun _ hp => isZero_cosimplicialDoubleComplex_X_of_neg K hp)

/-- The column `0` of the double complex of `K` is the extended Moore complex of `K.X 0`, read at
the integer `0`. -/
def cosimplicialDoubleComplexColumnZeroIso :
    (cosimplicialDoubleComplexFunctor.obj K).X 0 ≅
      ((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X 0)).extend
        ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendXIso (cosimplicialDoubleComplexInner K) ComplexShape.embeddingUpNat
    (show ComplexShape.embeddingUpNat.f 0 = 0 from rfl)

/-- **The projection `Tot(K) ⟶ M(K.X 0)` of the total complex onto the column zero**: the
projection `StacksDraft.TotalComplexQuasiIso.bottomProj` of the double complex onto its column `0`,
followed by the identification of the total complex of a double complex concentrated in the
column `0` with that column. -/
def cosimplicialTotalToColumnZero :
    (cosimplicialDoubleComplexFunctor.obj K).total (ComplexShape.up ℤ) ⟶
      ((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X 0)).extend
        ComplexShape.embeddingUpNat :=
  HomologicalComplex₂.total.map (bottomProj _ 0 (isZero_cosimplicialDoubleComplex_X_neg_one K))
      (ComplexShape.up ℤ) ≫
    inv (totalSingleColumnUnit ((cosimplicialDoubleComplexFunctor.obj K).X 0) 0) ≫
    (shiftFunctorZero (CochainComplex AddCommGrpCat.{u} ℤ) ℤ).hom.app _ ≫
    (cosimplicialDoubleComplexColumnZeroIso K).hom

/-- **The first degeneration at the level of complexes**: the projection onto the column zero is a
quasi-isomorphism as soon as the Moore complexes of the cosimplicial groups `K.X n`, `n > 0`, are
acyclic. -/
theorem quasiIso_cosimplicialTotalToColumnZero
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{u}).obj (K.X n)).homology j)) :
    QuasiIso (cosimplicialTotalToColumnZero K) := by
  have := StacksDraft.TotalDegeneration.quasiIso_total_bottomProj_zero
    (cosimplicialDoubleComplexFunctor.obj K)
    (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg K p hq)
    (fun _p hp => isZero_cosimplicialDoubleComplex_X_of_neg K hp)
    (acyclic_cosimplicialDoubleComplex_X_of_ne_zero K hcol)
  unfold cosimplicialTotalToColumnZero
  infer_instance

variable {K} in
/-- **The projection onto the column zero is natural in `K`.** -/
theorem cosimplicialTotalToColumnZero_naturality
    {K' : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ} (f : K ⟶ K') :
    HomologicalComplex₂.total.map (cosimplicialDoubleComplexFunctor.map f) (ComplexShape.up ℤ) ≫
        cosimplicialTotalToColumnZero K' =
      cosimplicialTotalToColumnZero K ≫
        HomologicalComplex.extendMap ((alternatingCofaceMapComplex AddCommGrpCat.{u}).map (f.f 0))
          ComplexShape.embeddingUpNat := by
  have h1 := bottomProj_naturality (cosimplicialDoubleComplexFunctor.map f) 0
    (isZero_cosimplicialDoubleComplex_X_neg_one K) (isZero_cosimplicialDoubleComplex_X_neg_one K')
  have h2 := totalSingleColumnUnit_naturality ((cosimplicialDoubleComplexFunctor.map f).f 0) 0
  have h3 : (shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) (-0 : ℤ)).map
        ((cosimplicialDoubleComplexFunctor.map f).f 0) ≫
      (shiftFunctorZero (CochainComplex AddCommGrpCat.{u} ℤ) ℤ).hom.app
        ((cosimplicialDoubleComplexFunctor.obj K').X 0) =
      (shiftFunctorZero (CochainComplex AddCommGrpCat.{u} ℤ) ℤ).hom.app
        ((cosimplicialDoubleComplexFunctor.obj K).X 0) ≫
        (cosimplicialDoubleComplexFunctor.map f).f 0 :=
    (shiftFunctorZero (CochainComplex AddCommGrpCat.{u} ℤ) ℤ).hom.naturality
      ((cosimplicialDoubleComplexFunctor.map f).f 0)
  have h4 : (cosimplicialDoubleComplexFunctor.map f).f 0 ≫
      (cosimplicialDoubleComplexColumnZeroIso K').hom =
      (cosimplicialDoubleComplexColumnZeroIso K).hom ≫
        HomologicalComplex.extendMap ((alternatingCofaceMapComplex AddCommGrpCat.{u}).map (f.f 0))
          ComplexShape.embeddingUpNat := by
    have e : (cosimplicialDoubleComplexFunctor.map f).f 0 =
        (cosimplicialDoubleComplexColumnZeroIso K).hom ≫
          HomologicalComplex.extendMap
            ((alternatingCofaceMapComplex AddCommGrpCat.{u}).map (f.f 0))
            ComplexShape.embeddingUpNat ≫ (cosimplicialDoubleComplexColumnZeroIso K').inv :=
      HomologicalComplex.extendMap_f (cosimplicialDoubleComplexInnerMap f)
        ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f 0 = 0 from rfl)
    rw [e]
    simp
  have h2' : inv (totalSingleColumnUnit ((cosimplicialDoubleComplexFunctor.obj K).X 0) 0) ≫
      (shiftFunctor (CochainComplex AddCommGrpCat.{u} ℤ) (-0 : ℤ)).map
        ((cosimplicialDoubleComplexFunctor.map f).f 0) =
      HomologicalComplex₂.total.map ((HomologicalComplex.single
        (CochainComplex AddCommGrpCat.{u} ℤ) (ComplexShape.up ℤ) 0).map
          ((cosimplicialDoubleComplexFunctor.map f).f 0)) (ComplexShape.up ℤ) ≫
        inv (totalSingleColumnUnit ((cosimplicialDoubleComplexFunctor.obj K').X 0) 0) := by
    rw [IsIso.inv_comp_eq, ← Category.assoc, ← h2, Category.assoc, IsIso.hom_inv_id,
      Category.comp_id]
  simp only [cosimplicialTotalToColumnZero, Category.assoc]
  rw [← HomologicalComplex₂.total.map_comp_assoc, ← h1, HomologicalComplex₂.total.map_comp_assoc,
    ← reassoc_of% h2', reassoc_of% h3, h4]

variable {K} in
/-- **The morphism of total complexes induced by a morphism of cochain complexes of cosimplicial
abelian groups**. -/
def cosimplicialTotalMap {K' : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ}
    (f : K ⟶ K') :
    (cosimplicialDoubleComplexFunctor.obj K).total (ComplexShape.up ℤ) ⟶
      (cosimplicialDoubleComplexFunctor.obj K').total (ComplexShape.up ℤ) :=
  HomologicalComplex₂.total.map (cosimplicialDoubleComplexFunctor.map f) (ComplexShape.up ℤ)

variable {K} in
/-- **A morphism which is a quasi-isomorphism on every row induces a quasi-isomorphism of total
complexes.** -/
theorem quasiIso_cosimplicialTotalMap
    {K' : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ} (f : K ⟶ K')
    (hrows : ∀ b : ℤ, QuasiIso ((StacksDraft.TotalRowComparison.flipMap
      (cosimplicialDoubleComplexFunctor.map f)).f b)) :
    QuasiIso (cosimplicialTotalMap f) := by
  have hflip := StacksDraft.TotalRowComparison.quasiIso_total_map_flip
    (cosimplicialDoubleComplexFunctor.map f)
    (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg K p hq)
    (fun _p hp => isZero_cosimplicialDoubleComplex_X_of_neg K hp)
    (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg K' p hq)
    (fun _p hp => isZero_cosimplicialDoubleComplex_X_of_neg K' hp) hrows
  have key := StacksDraft.TotalComplexQuasiIso.totalFlipIso_naturality
    (cosimplicialDoubleComplexFunctor.map f)
  have e : cosimplicialTotalMap f =
      ((cosimplicialDoubleComplexFunctor.obj K).totalFlipIso (ComplexShape.up ℤ)).inv ≫
        HomologicalComplex₂.total.map (StacksDraft.TotalRowComparison.flipMap
          (cosimplicialDoubleComplexFunctor.map f)) (ComplexShape.up ℤ) ≫
        ((cosimplicialDoubleComplexFunctor.obj K').totalFlipIso (ComplexShape.up ℤ)).hom := by
    rw [key, Iso.inv_hom_id_assoc]
    rfl
  rw [e]
  infer_instance

variable {K} in
/-- The induced morphism of total complexes is functorial. -/
theorem cosimplicialTotalMap_comp
    {K' K'' : CochainComplex (CosimplicialObject AddCommGrpCat.{u}) ℕ} (f : K ⟶ K')
    (f' : K' ⟶ K'') :
    cosimplicialTotalMap (f ≫ f') = cosimplicialTotalMap f ≫ cosimplicialTotalMap f' := by
  rw [cosimplicialTotalMap, Functor.map_comp, HomologicalComplex₂.total.map_comp]
  rfl

end General

section Constant

variable (R : CochainComplex AddCommGrpCat.{u} ℕ)

/-- **The row zero of the double complex of `Const(R)` is the extension of `R`**: this is
`Crystalline.cosimplicialDoubleComplexRowIso` at the row `0`, read at the integer `0`. -/
def cosimplicialConstRowZeroIso :
    (cosimplicialDoubleComplexFunctor.obj (constantCosimplicialCochainComplex.obj R)).flip.X 0 ≅
      R.extend ComplexShape.embeddingUpNat :=
  cosimplicialDoubleComplexRowIso (constantCosimplicialCochainComplex.obj R) 0

variable {R} in
/-- `Crystalline.cosimplicialConstRowZeroIso` is natural in `R`. -/
theorem cosimplicialConstRowZeroIso_naturality {R' : CochainComplex AddCommGrpCat.{u} ℕ}
    (g : R ⟶ R') :
    (StacksDraft.TotalRowComparison.flipMap
        (cosimplicialDoubleComplexFunctor.map (constantCosimplicialCochainComplex.map g))).f 0 ≫
        (cosimplicialConstRowZeroIso R').hom =
      (cosimplicialConstRowZeroIso R).hom ≫
        HomologicalComplex.extendMap g ComplexShape.embeddingUpNat :=
  cosimplicialDoubleComplexRowIso_naturality (constantCosimplicialCochainComplex.map g) 0

/-- **The inclusion of the row zero into the total complex of the double complex of `Const(R)`**,
in total degree `n` the inclusion of the summand indexed by `(n, 0)`, read through the
identification of that row with `R`. -/
def cosimplicialRowZeroToTotal :
    R.extend ComplexShape.embeddingUpNat ⟶
      (cosimplicialDoubleComplexFunctor.obj
        (constantCosimplicialCochainComplex.obj R)).total (ComplexShape.up ℤ) :=
  (cosimplicialConstRowZeroIso R).inv ≫
    StacksDraft.TotalRowComparison.rowZeroTotalMap _
      (diagonalFinite_constCosimplicialDoubleComplex R)
      (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg _ p hq)
      (fun a _q hq => exactAt_constCosimplicialDoubleComplex_X R a hq)
      (constCosimplicialDoubleComplex_X_d_zero_one R)

/-- `Crystalline.cosimplicialRowZeroToTotal` is a quasi-isomorphism. -/
instance quasiIso_cosimplicialRowZeroToTotal : QuasiIso (cosimplicialRowZeroToTotal R) := by
  have := StacksDraft.TotalRowComparison.quasiIso_rowZeroTotalMap
    (cosimplicialDoubleComplexFunctor.obj (constantCosimplicialCochainComplex.obj R))
    (diagonalFinite_constCosimplicialDoubleComplex R)
    (fun p _q hq => isZero_cosimplicialDoubleComplex_X_X_of_neg _ p hq)
    (fun a _q hq => exactAt_constCosimplicialDoubleComplex_X R a hq)
    (constCosimplicialDoubleComplex_X_d_zero_one R)
  unfold cosimplicialRowZeroToTotal
  infer_instance

variable {R} in
/-- `Crystalline.cosimplicialRowZeroToTotal` is natural in `R`. -/
theorem cosimplicialRowZeroToTotal_naturality {R' : CochainComplex AddCommGrpCat.{u} ℕ}
    (g : R ⟶ R') :
    cosimplicialRowZeroToTotal R ≫ cosimplicialTotalMap (constantCosimplicialCochainComplex.map g) =
      HomologicalComplex.extendMap g ComplexShape.embeddingUpNat ≫
        cosimplicialRowZeroToTotal R' := by
  have hrow' : HomologicalComplex.extendMap g ComplexShape.embeddingUpNat ≫
      (cosimplicialConstRowZeroIso R').inv =
      (cosimplicialConstRowZeroIso R).inv ≫
        (StacksDraft.TotalRowComparison.flipMap
          (cosimplicialDoubleComplexFunctor.map
            (constantCosimplicialCochainComplex.map g))).f 0 := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← cosimplicialConstRowZeroIso_naturality,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [cosimplicialRowZeroToTotal, cosimplicialRowZeroToTotal, Category.assoc,
    reassoc_of% hrow']
  congr 1
  ext n : 1
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    StacksDraft.TotalRowComparison.rowZeroTotalMap_f,
    StacksDraft.TotalRowComparison.rowZeroTotalMap_f, cosimplicialTotalMap]
  exact HomologicalComplex₂.ιTotal_map
    (φ := cosimplicialDoubleComplexFunctor.map (constantCosimplicialCochainComplex.map g))
    (c₁₂ := ComplexShape.up ℤ) (i₁ := n) (i₂ := 0) (i₁₂ := n) (h := add_zero n)

end Constant

/-! ### The zigzag of a cosimplicial pair -/

namespace CosimplicialCompletedPair

variable {A : Type u} [CommRing A] {E : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  (W : CosimplicialCompletedPair.{u, v, w} E p)

/-- **The Moore complex of the column zero `M(0) → M(1) → M(2) → ⋯`** of the double complex. -/
abbrev columnZeroMooreComplex : CochainComplex AddCommGrpCat.{max v w} ℕ :=
  (alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj (W.doubleComplex.X 0)

/-- **The total complex `Tot(K)` of the double complex of the pair.** -/
abbrev totalComplex : CochainComplex AddCommGrpCat.{max v w} ℤ :=
  (cosimplicialDoubleComplexFunctor.obj W.doubleComplex).total (ComplexShape.up ℤ)

/-- **The total complex of the constant double complex on the row zero.** -/
abbrev rowZeroTotalComplex : CochainComplex AddCommGrpCat.{max v w} ℤ :=
  (cosimplicialDoubleComplexFunctor.obj
    (constantCosimplicialCochainComplex.obj (W.degreeDeRhamComplex 0))).total (ComplexShape.up ℤ)

/-- **The first leg of the zigzag**: the projection `Tot(K) ⟶ M(•)` onto the column zero. -/
def zigzagColumnZero :
    W.totalComplex ⟶ W.columnZeroMooreComplex.extend ComplexShape.embeddingUpNat :=
  cosimplicialTotalToColumnZero W.doubleComplex

/-- **The second leg of the zigzag**: the comparison `Tot(K) ⟶ Tot(Const(K^{*,0}))` induced by
`Crystalline.CosimplicialCompletedPair.rowZeroComparison`. -/
def zigzagTotal : W.totalComplex ⟶ W.rowZeroTotalComplex :=
  cosimplicialTotalMap W.rowZeroComparison

/-- **The third leg of the zigzag**: the inclusion of the row zero
`M(0) ⊗^∧_{D(0)} Ω^*_{D(0)}` into `Tot(Const(K^{*,0}))`. -/
def zigzagRowZero :
    (W.degreeDeRhamComplex 0).extend ComplexShape.embeddingUpNat ⟶ W.rowZeroTotalComplex :=
  cosimplicialRowZeroToTotal (W.degreeDeRhamComplex 0)

/-- The projection onto the column zero is a quasi-isomorphism as soon as the columns `a > 0` of
the double complex are acyclic. -/
theorem quasiIso_zigzagColumnZero
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X n)).homology j)) :
    QuasiIso W.zigzagColumnZero :=
  quasiIso_cosimplicialTotalToColumnZero W.doubleComplex hcol

/-- The comparison of total complexes is a quasi-isomorphism as soon as every coprojection
`M(0) ⊗^∧_{D(0)} Ω^*_{D(0)} ⟶ M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` is one. -/
theorem quasiIso_zigzagTotal (hrow : ∀ b : ℕ, QuasiIso (W.rowFromZeroHom b)) :
    QuasiIso W.zigzagTotal :=
  quasiIso_cosimplicialTotalMap _ (W.quasiIso_flipMap_rowZeroComparison_of_quasiIso hrow)

/-- The inclusion of the row zero is a quasi-isomorphism. -/
instance quasiIso_zigzagRowZero : QuasiIso W.zigzagRowZero :=
  quasiIso_cosimplicialRowZeroToTotal _

/-- **The cohomology of the row zero is the cohomology of the Moore complex of the column zero**,
read off the zigzag `K^{*,0} ⟶ Tot(Const(K^{*,0})) ⟵ Tot(K) ⟶ M(•)` of quasi-isomorphisms. -/
def zigzagHomologyIso
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X n)).homology j))
    (hrow : ∀ b : ℕ, QuasiIso (W.rowFromZeroHom b)) (n : ℤ) :
    ((W.degreeDeRhamComplex 0).extend ComplexShape.embeddingUpNat).homology n ≅
      (W.columnZeroMooreComplex.extend ComplexShape.embeddingUpNat).homology n :=
  haveI := W.quasiIso_zigzagColumnZero hcol
  haveI := W.quasiIso_zigzagTotal hrow
  isoOfQuasiIsoAt W.zigzagRowZero n ≪≫
    (isoOfQuasiIsoAt W.zigzagTotal n).symm ≪≫
    isoOfQuasiIsoAt W.zigzagColumnZero n

end CosimplicialCompletedPair

/-! ### Morphisms of cosimplicial divided power algebras -/

namespace CosimplicialDPAlgebra

variable {A : Type u} [CommRing A]

/-- **A morphism of cosimplicial divided power algebras** `E ⟶ E'`: in each cosimplicial degree an
`A`-algebra map of the carriers which is a divided power morphism, commuting with the
transition maps. -/
structure Hom (E E' : CosimplicialDPAlgebra.{u, v} A) where
  /-- The component in the cosimplicial degree `b`. -/
  app (b : ℕ) : E.carrier b →ₐ[A] E'.carrier b
  /-- Each component is a divided power morphism. -/
  isDPMorphism (b : ℕ) :
    DividedPowers.IsDPMorphism (E.dividedPowers b) (E'.dividedPowers b) (app b).toRingHom
  /-- The components commute with the transition maps. -/
  naturality {m n : SimplexCategory} (φ : m ⟶ n) :
    (app n.len).comp (E.map φ) = (E'.map φ).comp (app m.len)

namespace Hom

variable {E E' : CosimplicialDPAlgebra.{u, v} A} (g : Hom E E') (p : ℕ)

/-- The component `D̂(b) → D̂'(b)` on the completed rings. -/
def completedRingMap (b : ℕ) : E.completedRing p b →+* E'.completedRing p b :=
  adicCompletionRingMap (g.app b).toRingHom (map_pAdicIdeal_le p _)

/-- **The component `Ω^a_{D(b)} → Ω^a_{D'(b)}` on the forms**, semilinear over the completed
rings. -/
def formsMap (b a : ℕ) : E.forms p a b →ₛₗ[g.completedRingMap p b] E'.forms p a b where
  toFun := completedMapDifferentialForms p A (E.dividedPowers b) (E'.dividedPowers b) (g.app b)
    (g.isDPMorphism b) a
  map_add' := map_add _
  map_smul' r x := adicCompletionMapₛₗ_smul _ _ r x

/-- The component on the forms respects the wedge product. -/
theorem formsMap_wedge (b a : ℕ) (ω : E.forms p a b) (η : E.forms p 1 b) :
    g.formsMap p b (a + 1) (E.wedge p b a ω η) =
      E'.wedge p b a (g.formsMap p b a ω) (g.formsMap p b 1 η) :=
  completedMapDifferentialForms_wedge p A (E.dividedPowers b) (E'.dividedPowers b) (g.app b)
    (g.isDPMorphism b) a ω η

/-- The component on the forms commutes with the de Rham differential. -/
theorem formsMap_deRham (b a : ℕ) (ω : E.forms p a b) :
    g.formsMap p b (a + 1) (E.deRham p b a ω) = E'.deRham p b a (g.formsMap p b a ω) :=
  completedMapDifferentialForms_deRham p A (E.dividedPowers b) (E'.dividedPowers b) (g.app b)
    (g.isDPMorphism b) a ω

/-- The component on the forms commutes with the cosimplicial transition maps. -/
theorem formsMap_formsMap {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ)
    (ω : E.forms p a m.len) :
    g.formsMap p n.len a (E.formsMap p φ a ω) = E'.formsMap p φ a (g.formsMap p m.len a ω) := by
  have hh : DividedPowers.IsDPMorphism (E.dividedPowers m.len) (E'.dividedPowers n.len)
      ((E'.map φ).comp (g.app m.len)).toRingHom :=
    DividedPowers.IsDPMorphism.comp _ (E'.map_isDPMorphism φ) (g.isDPMorphism m.len)
  exact (completedMapDifferentialForms_eq_comp p A (E.dividedPowers m.len)
      (E.dividedPowers n.len) (E'.dividedPowers n.len) (E.map φ) (g.app n.len)
      ((E'.map φ).comp (g.app m.len)) (E.map_isDPMorphism φ) (g.isDPMorphism n.len) hh
      (g.naturality φ).symm a ω).symm.trans
    (completedMapDifferentialForms_eq_comp p A (E.dividedPowers m.len)
      (E'.dividedPowers m.len) (E'.dividedPowers n.len) (g.app m.len) (E'.map φ)
      ((E'.map φ).comp (g.app m.len)) (g.isDPMorphism m.len) (E'.map_isDPMorphism φ) hh rfl a ω)

end Hom

end CosimplicialDPAlgebra

/-! ### Morphisms of cosimplicial pairs -/

namespace CosimplicialCompletedPair

variable {A : Type u} [CommRing A] {E E' : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}

/-- **A morphism of cosimplicial pairs over a morphism `g : E ⟶ E'` of cosimplicial divided power
algebras**: in each cosimplicial degree a map `M(b) → M'(b)`, semilinear over the completion of
`g`, which commutes with the transition maps and is horizontal for the connections. -/
structure Hom (g : E.Hom E') (W : CosimplicialCompletedPair.{u, v, w} E p)
    (W' : CosimplicialCompletedPair.{u, v, w} E' p) where
  /-- The component in the cosimplicial degree `b`. -/
  app (b : ℕ) : W.carrier b →ₛₗ[g.completedRingMap p b] W'.carrier b
  /-- The components commute with the transition maps. -/
  naturality {m n : SimplexCategory} (φ : m ⟶ n) (x : W.carrier m.len) :
    app n.len (W.map φ x) = W'.map φ (app m.len x)
  /-- The components are horizontal: they carry the connection of `W` to that of `W'`. -/
  nabla_app (b : ℕ) (x : W.carrier b) :
    W'.nabla b (app b x) =
      CompletedDeRham.comparisonValues p (E.completedRing p b) (E'.completedRing p b)
        (g.completedRingMap p b) (W.carrier b) (W'.carrier b) (app b)
        (fun i => E.forms p i b) (fun i => E'.forms p i b) (fun i => g.formsMap p b i) 1
        (W.nabla b x)

namespace Hom

variable {g : E.Hom E'} {W : CosimplicialCompletedPair.{u, v, w} E p}
  {W' : CosimplicialCompletedPair.{u, v, w} E' p} (F : Hom g W W')

/-- **The component `M(b) ⊗̂ Ω^a_{D(b)} → M'(b) ⊗̂ Ω^a_{D'(b)}` of the induced morphism of double
complexes**, the completion of `m ⊗ ω ↦ F m ⊗ g ω`. -/
def tensorApp (a b : ℕ) :
    W.toCosimplicialCompletedModule.obj a b →ₛₗ[g.completedRingMap p b]
      W'.toCosimplicialCompletedModule.obj a b :=
  CompletedDeRham.comparisonValues p (E.completedRing p b) (E'.completedRing p b)
    (g.completedRingMap p b) (W.carrier b) (W'.carrier b) (F.app b)
    (fun i => E.forms p i b) (fun i => E'.forms p i b) (fun i => g.formsMap p b i) a

/-- The induced map commutes with the cosimplicial transition maps. -/
theorem tensorApp_tensorMap {m n : SimplexCategory} (φ : m ⟶ n) (a : ℕ)
    (x : W.toCosimplicialCompletedModule.obj a m.len) :
    F.tensorApp a n.len (W.toCosimplicialCompletedModule.tensorMap φ a x) =
      W'.toCosimplicialCompletedModule.tensorMap φ a (F.tensorApp a m.len x) := by
  let l := semilinearComp (TensorProduct.map (F.app n.len) (g.formsMap p n.len a))
    (TensorProduct.map (W.map φ) (E.formsMapCompleted p φ a))
  have h1 := adicCompletionMapₛₗ_comp_apply
    (TensorProduct.map (W.map φ) (E.formsMapCompleted p φ a))
    (TensorProduct.map (F.app n.len) (g.formsMap p n.len a)) l
    (map_pAdicIdeal_le p _) (map_pAdicIdeal_le p _) (map_pAdicIdeal_le p _) (fun _ => rfl) x
  have h2 := adicCompletionMapₛₗ_comp_apply
    (TensorProduct.map (F.app m.len) (g.formsMap p m.len a))
    (TensorProduct.map (W'.map φ) (E'.formsMapCompleted p φ a)) l
    (map_pAdicIdeal_le p _) (map_pAdicIdeal_le p _) (map_pAdicIdeal_le p _) (fun y => by
      induction y using TensorProduct.induction_on with
      | zero => simp only [map_zero]
      | tmul y ω =>
        show F.app n.len (W.map φ y) ⊗ₜ[E'.completedRing p n.len]
            g.formsMap p n.len a (E.formsMap p φ a ω) =
          W'.map φ (F.app m.len y) ⊗ₜ[E'.completedRing p n.len]
            E'.formsMap p φ a (g.formsMap p m.len a ω)
        rw [F.naturality, g.formsMap_formsMap]
      | add y z hy hz => simp only [map_add, hy, hz]) x
  exact h1.symm.trans h2

/-- The induced map commutes with the de Rham differentials. -/
theorem degreeDifferential_tensorApp (b a : ℕ) (x : W.toCosimplicialCompletedModule.obj a b) :
    W'.degreeDifferential b a (F.tensorApp a b x) =
      F.tensorApp (a + 1) b (W.degreeDifferential b a x) :=
  CompletedDeRham.differential_comparisonValues p (E.completedRing p b) (E'.completedRing p b)
    (g.completedRingMap p b) (W.carrier b) (W'.carrier b) (F.app b) (fun i => E.forms p i b)
    (fun i => E'.forms p i b) (fun i => g.formsMap p b i) (E.wedge p b) (E'.wedge p b)
    (E.deRham p b) (E'.deRham p b) (W.nabla b) (W'.nabla b) (E.isGradedLeibniz p b)
    (E'.isGradedLeibniz p b) (fun i ω η => g.formsMap_wedge p b i ω η)
    (fun i ω => g.formsMap_deRham p b i ω) (fun y => F.nabla_app b y) a x

/-- **The induced morphism of the columns `K^{a,•} ⟶ K'^{a,•}`**, as cosimplicial abelian
groups. -/
def columnMap (a : ℕ) :
    W.toCosimplicialCompletedModule.column a ⟶ W'.toCosimplicialCompletedModule.column a where
  app n := AddCommGrpCat.ofHom (F.tensorApp a n.len).toAddMonoidHom
  naturality _ _ φ := AddCommGrpCat.ext fun x => F.tensorApp_tensorMap φ a x

/-- **The induced morphism of double complexes `K ⟶ K'`.** -/
def doubleComplexMap : W.doubleComplex ⟶ W'.doubleComplex :=
  CochainComplex.ofHom (fun a => F.columnMap a) (fun a => by
    rw [W.doubleComplex_d, W'.doubleComplex_d]
    exact NatTrans.ext (funext fun n =>
      AddCommGrpCat.ext fun x => F.degreeDifferential_tensorApp n.len a x))

/-- The exterior degree `a` of the induced morphism of double complexes is the induced morphism
of the columns. -/
theorem doubleComplexMap_f (a : ℕ) : F.doubleComplexMap.f a = F.columnMap a := rfl

/-- **The induced morphism of the completed de Rham complexes
`M(b) ⊗^∧_{D(b)} Ω^*_{D(b)} ⟶ M'(b) ⊗^∧_{D'(b)} Ω^*_{D'(b)}`** of one cosimplicial degree. -/
def degreeDeRhamMap (b : ℕ) : W.degreeDeRhamComplex b ⟶ W'.degreeDeRhamComplex b :=
  cochainComplexHomOfDegreewise
    (fun i => AddCommGrpCat.ofHom (F.tensorApp i b).toAddMonoidHom) (fun i => by
      rw [W.degreeDeRhamComplex_d b i, W'.degreeDeRhamComplex_d b i]
      exact AddCommGrpCat.ext fun x => F.degreeDifferential_tensorApp b i x)

/-- **The induced morphism of the Moore complexes of the columns zero**,
`M(•) ⟶ M'(•)`. -/
def columnZeroMooreMap : W.columnZeroMooreComplex ⟶ W'.columnZeroMooreComplex :=
  (alternatingCofaceMapComplex AddCommGrpCat.{max v w}).map (F.doubleComplexMap.f 0)

/-- **The induced morphism commutes with the comparisons with the row zero.** -/
theorem doubleComplexMap_rowZeroComparison :
    F.doubleComplexMap ≫ W'.rowZeroComparison =
      W.rowZeroComparison ≫ constantCosimplicialCochainComplex.map (F.degreeDeRhamMap 0) :=
  HomologicalComplex.hom_ext _ _ fun a => NatTrans.ext (funext fun m =>
    AddCommGrpCat.ext fun x => (F.tensorApp_tensorMap (SimplexCategory.const m ⦋0⦌ 0) a x).symm)

/-! ### The zigzag is natural -/

/-- **The projection onto the column zero is natural.** -/
theorem zigzagColumnZero_naturality :
    cosimplicialTotalMap F.doubleComplexMap ≫ W'.zigzagColumnZero =
      W.zigzagColumnZero ≫
        HomologicalComplex.extendMap F.columnZeroMooreMap ComplexShape.embeddingUpNat :=
  cosimplicialTotalToColumnZero_naturality F.doubleComplexMap

/-- **The comparison of total complexes is natural.** -/
theorem zigzagTotal_naturality :
    W.zigzagTotal ≫ cosimplicialTotalMap
        (constantCosimplicialCochainComplex.map (F.degreeDeRhamMap 0)) =
      cosimplicialTotalMap F.doubleComplexMap ≫ W'.zigzagTotal := by
  rw [zigzagTotal, zigzagTotal, ← cosimplicialTotalMap_comp, ← cosimplicialTotalMap_comp,
    doubleComplexMap_rowZeroComparison]

/-- **The inclusion of the row zero is natural.** -/
theorem zigzagRowZero_naturality :
    W.zigzagRowZero ≫ cosimplicialTotalMap
        (constantCosimplicialCochainComplex.map (F.degreeDeRhamMap 0)) =
      HomologicalComplex.extendMap (F.degreeDeRhamMap 0) ComplexShape.embeddingUpNat ≫
        W'.zigzagRowZero :=
  cosimplicialRowZeroToTotal_naturality (F.degreeDeRhamMap 0)

/-- **The cohomology isomorphism of the zigzag is natural.** -/
theorem zigzagHomologyIso_naturality
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X n)).homology j))
    (hrow : ∀ b : ℕ, QuasiIso (W.rowFromZeroHom b))
    (hcol' : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W'.doubleComplex.X n)).homology j))
    (hrow' : ∀ b : ℕ, QuasiIso (W'.rowFromZeroHom b)) (n : ℤ) :
    (W.zigzagHomologyIso hcol hrow n).hom ≫ HomologicalComplex.homologyMap
        (HomologicalComplex.extendMap F.columnZeroMooreMap ComplexShape.embeddingUpNat) n =
      HomologicalComplex.homologyMap
          (HomologicalComplex.extendMap (F.degreeDeRhamMap 0) ComplexShape.embeddingUpNat) n ≫
        (W'.zigzagHomologyIso hcol' hrow' n).hom := by
  have := W.quasiIso_zigzagTotal hrow
  have := W'.quasiIso_zigzagTotal hrow'
  have hT : (isoOfQuasiIsoAt W.zigzagTotal n).inv ≫
      HomologicalComplex.homologyMap (cosimplicialTotalMap F.doubleComplexMap) n =
      HomologicalComplex.homologyMap (cosimplicialTotalMap
          (constantCosimplicialCochainComplex.map (F.degreeDeRhamMap 0))) n ≫
        (isoOfQuasiIsoAt W'.zigzagTotal n).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, Iso.eq_comp_inv, isoOfQuasiIsoAt_hom,
      isoOfQuasiIsoAt_hom, ← HomologicalComplex.homologyMap_comp,
      ← HomologicalComplex.homologyMap_comp, F.zigzagTotal_naturality]
  simp only [zigzagHomologyIso, Iso.trans_hom, Iso.symm_hom, isoOfQuasiIsoAt_hom,
    Category.assoc]
  rw [← HomologicalComplex.homologyMap_comp, ← F.zigzagColumnZero_naturality,
    HomologicalComplex.homologyMap_comp, reassoc_of% hT,
    ← HomologicalComplex.homologyMap_comp_assoc, F.zigzagRowZero_naturality,
    HomologicalComplex.homologyMap_comp_assoc]

end Hom

end CosimplicialCompletedPair

end Crystalline
