module

public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.Algebra.Homology.TotalRowComparison
public import StacksFrontier.AlgebraicTopology.ConstantCofaceMapComplex

/-!
# The double complex of a cochain complex of cosimplicial objects, in any abelian category

This is the double complex of `StacksFrontier/AlgebraicGeometry/Crystalline/Cosimplicial/
DoubleComplex.lean` and its two degenerations, in an arbitrary abelian category `𝒞` rather than
in abelian groups.  The Čech–de Rham double complex `B^{a,r} = ∏_s M_s ⊗ Ω^a_{D_s}` of a crystal is
a double complex of modules over the global sections of the divided power base, and the
comparisons it yields are needed as *linear* isomorphisms of cohomology, so the construction is
redone here with `𝒞` a parameter (in the applications `𝒞 = ModuleCat A`).

Given `K : CochainComplex (CosimplicialObject 𝒞) ℕ` — the `a` direction a complex, the `b`
direction cosimplicial — `Crystalline.CosimplicialDoubleComplex.functor` applies the Moore
complex in each degree and extends both indices to `ℤ`.  Its column `a` is the Moore complex of
`K^a`, its row `b` is the complex `K^•(⦋b⦌)`.

## Main results

* `Crystalline.CosimplicialDoubleComplex.totalHomologyIsoColumnZero` — if the Moore complexes of
  the cosimplicial objects `K^a`, `a > 0`, are acyclic, the total complex has the cohomology of
  the Moore complex of `K^0`.
* `Crystalline.CosimplicialDoubleComplex.totalHomologyIsoOfRows` — a morphism `K ⟶ K'` which is
  a quasi-isomorphism on every row `K^•(⦋b⦌) ⟶ K'^•(⦋b⦌)` induces isomorphisms on the cohomology
  of the total complexes.
* `Crystalline.CosimplicialDoubleComplex.constTotalHomologyIso` — the total complex of the
  constant cosimplicial object on a complex `R` has the cohomology of `R`.
* `Crystalline.CosimplicialDoubleComplex.columnZeroHomologyIsoOfRowComparison` — the two
  combined: acyclic columns off `0` and a rowwise quasi-isomorphism `K ⟶ Const(R)` identify the
  cohomology of the Moore complex of `K^0` with the cohomology of `R`.

## References

* [Stacks Project, Tag 019I](https://stacks.math.columbia.edu/tag/019I)
* [Stacks Project, Tag 0133](https://stacks.math.columbia.edu/tag/0133)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology Simplicial

universe v u

namespace Crystalline.CosimplicialDoubleComplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The Moore complex functor is additive: a morphism of cosimplicial objects acts on the Moore
complexes degree by degree. -/
instance additive_alternatingCofaceMapComplex : (alternatingCofaceMapComplex C).Additive where
  map_add {_ _ _ _} := by
    apply HomologicalComplex.hom_ext
    intro n
    rfl

variable (C) in
/-- **The double complex of a cochain complex of cosimplicial objects**: the Moore complex in each
degree of the `a` direction, both indices then extended from `ℕ` to `ℤ`.  The first index is the
outer one, so the column `a` is the Moore complex of `K^a`. -/
def functor :
    CochainComplex (CosimplicialObject C) ℕ ⥤
      HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (alternatingCofaceMapComplex C).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    (ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor (CochainComplex C ℤ)

variable (K : CochainComplex (CosimplicialObject C) ℕ)

/-- The column `a` of the double complex is the `ℤ`-extension of the Moore complex of `K^a`. -/
def columnIso (a : ℕ) :
    ((functor C).obj K).X (a : ℤ) ≅
      ((alternatingCofaceMapComplex C).obj (K.X a)).extend ComplexShape.embeddingUpNat :=
  HomologicalComplex.extendXIso
    (((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
      (((alternatingCofaceMapComplex C).mapHomologicalComplex (ComplexShape.up ℕ)).obj K))
    ComplexShape.embeddingUpNat (show ComplexShape.embeddingUpNat.f a = (a : ℤ) from rfl)

/-- The double complex vanishes in negative first degrees. -/
theorem isZero_X_of_neg {a : ℤ} (ha : a < 0) : IsZero (((functor C).obj K).X a) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat a
    (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega)

/-- The double complex vanishes in the first degrees which are not natural numbers. -/
private theorem isZero_X_of_not_nat {a : ℤ} (ha : ¬∃ n : ℕ, (n : ℤ) = a) :
    IsZero (((functor C).obj K).X a) :=
  HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat a (fun i hi => ha ⟨i, hi⟩)

/-- The double complex vanishes in negative second degrees. -/
theorem isZero_X_X_of_neg (a : ℤ) {b : ℤ} (hb : b < 0) :
    IsZero ((((functor C).obj K).X a).X b) := by
  by_cases ha : ∃ n : ℕ, (n : ℤ) = a
  · obtain ⟨n, rfl⟩ := ha
    refine IsZero.of_iso ?_
      ((HomologicalComplex.eval C (ComplexShape.up ℤ) b).mapIso (columnIso K n))
    exact HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat b
      (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega)
  · exact Functor.map_isZero (HomologicalComplex.eval C (ComplexShape.up ℤ) b)
      (isZero_X_of_not_nat K ha)

/-- The total complex of the double complex exists. -/
instance hasTotal : ((functor C).obj K).HasTotal (ComplexShape.up ℤ) :=
  StacksDraft.TotalComplexQuasiIso.hasTotal_of_bounded _ 0
    (fun a _ hb => isZero_X_X_of_neg K a hb) (fun _ ha => isZero_X_of_neg K ha)

/-- The cohomology of a column of the double complex vanishes as soon as that of the Moore
complex of the corresponding cosimplicial object does. -/
private theorem isZero_homology_X (a q : ℤ)
    (h : ∀ n : ℕ, (n : ℤ) = a → ∀ j : ℕ, (j : ℤ) = q →
      IsZero (((alternatingCofaceMapComplex C).obj (K.X n)).homology j)) :
    IsZero ((((functor C).obj K).X a).homology q) := by
  by_cases ha : ∃ n : ℕ, (n : ℤ) = a
  · obtain ⟨n, rfl⟩ := ha
    refine IsZero.of_iso ?_
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q).mapIso (columnIso K n))
    by_cases hq : 0 ≤ q
    · lift q to ℕ using hq
      exact IsZero.of_iso (h n rfl q rfl)
        (((alternatingCofaceMapComplex C).obj (K.X n)).extendHomologyIso
          ComplexShape.embeddingUpNat (j := q) (j' := (q : ℤ)) rfl)
    · exact ShortComplex.isZero_homology_of_isZero_X₂ (_ : ShortComplex C)
        (HomologicalComplex.isZero_extend_X _ ComplexShape.embeddingUpNat q
          (fun i hi => by simp only [ComplexShape.embeddingUpNat_f] at hi; omega))
  · exact Functor.map_isZero (HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) q)
      (isZero_X_of_not_nat K ha)

/-- A column of the double complex is acyclic as soon as the Moore complex of the corresponding
cosimplicial object is. -/
theorem acyclic_X {a : ℤ}
    (h : ∀ n : ℕ, (a : ℤ) = (n : ℤ) → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex C).obj (K.X n)).homology j)) :
    (((functor C).obj K).X a).Acyclic := by
  intro m
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact isZero_homology_X K a m fun n hn j _ => h n hn.symm j

/-- The cohomology of the column `0` is the cohomology of the Moore complex of `K^0`. -/
def columnZeroHomologyIso (j : ℕ) :
    (((functor C).obj K).X (0 : ℤ)).homology (j : ℤ) ≅
      ((alternatingCofaceMapComplex C).obj (K.X 0)).homology j :=
  ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (j : ℤ)).mapIso
      (columnIso K 0)).trans
    (((alternatingCofaceMapComplex C).obj (K.X 0)).extendHomologyIso
      ComplexShape.embeddingUpNat (j := j) (j' := (j : ℤ)) rfl)

/-- **The first degeneration**: if the Moore complexes of the cosimplicial objects `K^a`,
`a > 0`, are acyclic, the total complex has the cohomology of the Moore complex of `K^0`. -/
def totalHomologyIsoColumnZero
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex C).obj (K.X n)).homology j)) (j : ℕ) :
    (((functor C).obj K).total (ComplexShape.up ℤ)).homology (j : ℤ) ≅
      ((alternatingCofaceMapComplex C).obj (K.X 0)).homology j :=
  (StacksDraft.TotalDegeneration.totalHomologyIsoColumnZero ((functor C).obj K)
      (fun p _q hq => isZero_X_X_of_neg K p hq) (fun _p hp => isZero_X_of_neg K hp)
      (fun a ha => acyclic_X K fun n hn j => hcol n (by omega) j) (j : ℤ)).trans
    (columnZeroHomologyIso K j)

/-! ### Rows -/

/-- **The row `b`**: the cochain complex `a ↦ K^a(⦋b⦌)`. -/
def rowComplex (b : ℕ) : CochainComplex C ℕ :=
  ((alternatingCofaceMapComplex C ⋙
    HomologicalComplex.eval C (ComplexShape.up ℕ) b).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj K

/-- The degree `a` of the row `b` is `K^a(⦋b⦌)`. -/
theorem rowComplex_X (b a : ℕ) : (rowComplex K b).X a = (K.X a).obj ⦋b⦌ := rfl

/-- The differential of the row `b` is the differential of `K` at `⦋b⦌`. -/
theorem rowComplex_d (b a a' : ℕ) : (rowComplex K b).d a a' = (K.d a a').app ⦋b⦌ := rfl

variable {K} {K' : CochainComplex (CosimplicialObject C) ℕ}

/-- **The row `b` of a morphism.** -/
def rowMap (rho : K ⟶ K') (b : ℕ) : rowComplex K b ⟶ rowComplex K' b :=
  ((alternatingCofaceMapComplex C ⋙
    HomologicalComplex.eval C (ComplexShape.up ℕ) b).mapHomologicalComplex
      (ComplexShape.up ℕ)).map rho

/-- The degree `a` of the row `b` of `rho` is `rho^a` at `⦋b⦌`. -/
theorem rowMap_f (rho : K ⟶ K') (b a : ℕ) : (rowMap rho b).f a = (rho.f a).app ⦋b⦌ := rfl

variable (K) in
/-- The Moore complex of `K` in each degree, with the inner extension performed. -/
abbrev inner : CochainComplex (CochainComplex C ℤ) ℕ :=
  ((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj
    (((alternatingCofaceMapComplex C).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)

/-- The map `inner` carries a morphism to. -/
abbrev innerMap (rho : K ⟶ K') : inner K ⟶ inner K' :=
  ((ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex
      (ComplexShape.up ℕ)).map
    (((alternatingCofaceMapComplex C).mapHomologicalComplex (ComplexShape.up ℕ)).map rho)

variable (K) in
/-- The outer half of the identification of the rows. -/
abbrev rowOuterIso (b : ℕ) :
    (((HomologicalComplex.eval C (ComplexShape.up ℤ) (b : ℤ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (inner K)).extend ComplexShape.embeddingUpNat ≅
      ((functor C).obj K).flip.X (b : ℤ) :=
  HomologicalComplex.mapHomologicalComplexExtendIso
    (HomologicalComplex.eval C (ComplexShape.up ℤ) (b : ℤ)) (inner K) ComplexShape.embeddingUpNat

variable (K) in
/-- The inner half of the identification of the rows. -/
abbrev rowInnerIso (b : ℕ) :
    ((HomologicalComplex.eval C (ComplexShape.up ℤ) (b : ℤ)).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (inner K) ≅ rowComplex K b :=
  (NatIso.mapHomologicalComplex
    (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso C
      (show ComplexShape.embeddingUpNat.f b = (b : ℤ) from rfl))
    (ComplexShape.up ℕ)).app
      (((alternatingCofaceMapComplex C).mapHomologicalComplex (ComplexShape.up ℕ)).obj K)

variable (K) in
/-- **The row `b` of the double complex is the `ℤ`-extension of the row `b` of `K`.** -/
def rowIso (b : ℕ) :
    ((functor C).obj K).flip.X (b : ℤ) ≅ (rowComplex K b).extend ComplexShape.embeddingUpNat :=
  (rowOuterIso K b).symm ≪≫
    (ComplexShape.embeddingUpNat.extendFunctor C).mapIso (rowInnerIso K b)

variable (K) in
/-- `rowIso` is the composite of its two halves. -/
theorem rowIso_hom (b : ℕ) :
    (rowIso K b).hom = (rowOuterIso K b).inv ≫
      HomologicalComplex.extendMap (rowInnerIso K b).hom ComplexShape.embeddingUpNat := rfl

/-- The identification of the rows is natural. -/
theorem rowIso_naturality (rho : K ⟶ K') (b : ℕ) :
    (StacksDraft.TotalRowComparison.flipMap ((functor C).map rho)).f (b : ℤ) ≫
        (rowIso K' b).hom =
      (rowIso K b).hom ≫
        HomologicalComplex.extendMap (rowMap rho b) ComplexShape.embeddingUpNat := by
  have hnat := (NatIso.mapHomologicalComplex
      (ComplexShape.embeddingUpNat.extendFunctorCompEvalIso C
        (show ComplexShape.embeddingUpNat.f b = (b : ℤ) from rfl))
      (ComplexShape.up ℕ)).hom.naturality
    (((alternatingCofaceMapComplex C).mapHomologicalComplex (ComplexShape.up ℕ)).map rho)
  have hext : (StacksDraft.TotalRowComparison.flipMap ((functor C).map rho)).f (b : ℤ) ≫
        (rowOuterIso K' b).inv =
      (rowOuterIso K b).inv ≫
        HomologicalComplex.extendMap
          (((HomologicalComplex.eval C (ComplexShape.up ℤ) (b : ℤ)).mapHomologicalComplex
            (ComplexShape.up ℕ)).map (innerMap rho)) ComplexShape.embeddingUpNat :=
    HomologicalComplex.mapHomologicalComplexExtendIso_inv_naturality
      (HomologicalComplex.eval C (ComplexShape.up ℤ) (b : ℤ))
      (inner K) (innerMap rho) ComplexShape.embeddingUpNat
  rw [rowIso_hom, rowIso_hom, ← Category.assoc, hext, Category.assoc, Category.assoc,
    ← HomologicalComplex.extendMap_comp, ← HomologicalComplex.extendMap_comp]
  exact congrArg (fun psi => (rowOuterIso K b).inv ≫
    HomologicalComplex.extendMap psi ComplexShape.embeddingUpNat) hnat

/-- The square of `rowIso_naturality` as an isomorphism of arrows. -/
def rowArrowIso (rho : K ⟶ K') (b : ℕ) :
    Arrow.mk (HomologicalComplex.extendMap (rowMap rho b) ComplexShape.embeddingUpNat) ≅
      Arrow.mk ((StacksDraft.TotalRowComparison.flipMap ((functor C).map rho)).f (b : ℤ)) :=
  Arrow.isoMk (rowIso K b).symm (rowIso K' b).symm (by
    dsimp only [Arrow.mk_hom, Iso.symm_hom]
    rw [Iso.inv_comp_eq, ← Category.assoc, ← rowIso_naturality, Category.assoc,
      Iso.hom_inv_id, Category.comp_id])

/-- A rowwise quasi-isomorphism gives a quasi-isomorphism on every row of the double complex. -/
theorem quasiIso_flipMap_of_quasiIso_row (rho : K ⟶ K')
    (h : ∀ b : ℕ, QuasiIso (rowMap rho b)) (b : ℤ) :
    QuasiIso ((StacksDraft.TotalRowComparison.flipMap ((functor C).map rho)).f b) := by
  by_cases hb : 0 ≤ b
  · lift b to ℕ using hb
    have : QuasiIso (HomologicalComplex.extendMap (rowMap rho b)
        ComplexShape.embeddingUpNat) :=
      (HomologicalComplex.quasiIso_extendMap_iff (rowMap rho b)
        ComplexShape.embeddingUpNat).2 (h b)
    exact quasiIso_of_arrow_mk_iso _ _ (rowArrowIso rho b)
  · have h₁ : IsZero (((functor C).obj K).flip.X b) :=
      StacksDraft.TotalDegeneration.isZero_of_isZero_X
        (fun a => isZero_X_X_of_neg K a (by omega))
    have h₂ : IsZero (((functor C).obj K').flip.X b) :=
      StacksDraft.TotalDegeneration.isZero_of_isZero_X
        (fun a => isZero_X_X_of_neg K' a (by omega))
    have := StacksDraft.TotalComplexQuasiIso.isIso_of_isZero
      ((StacksDraft.TotalRowComparison.flipMap ((functor C).map rho)).f b) h₁ h₂
    infer_instance

/-- **The rowwise comparison**: a morphism which is a quasi-isomorphism on every row induces
isomorphisms on the cohomology of the total complexes. -/
def totalHomologyIsoOfRows (rho : K ⟶ K') (h : ∀ b : ℕ, QuasiIso (rowMap rho b)) (n : ℤ) :
    (((functor C).obj K).total (ComplexShape.up ℤ)).homology n ≅
      (((functor C).obj K').total (ComplexShape.up ℤ)).homology n :=
  StacksDraft.TotalRowComparison.totalHomologyIsoOfRows ((functor C).map rho)
    (fun p _q hq => isZero_X_X_of_neg K p hq) (fun _p hp => isZero_X_of_neg K hp)
    (fun p _q hq => isZero_X_X_of_neg K' p hq) (fun _p hp => isZero_X_of_neg K' hp)
    (quasiIso_flipMap_of_quasiIso_row rho h) n

/-! ### The constant cosimplicial object -/

variable (R : CochainComplex C ℕ)

/-- **A cosimplicially compatible family of maps out of the rows of `K` is a morphism
`K ⟶ Const(R)`.** -/
def constHom (rho : ∀ (a : ℕ) (m : SimplexCategory), (K.X a).obj m ⟶ R.X a)
    (hcosimplicial : ∀ (a : ℕ) {m n : SimplexCategory} (φ : m ⟶ n),
      (K.X a).map φ ≫ rho a n = rho a m)
    (hd : ∀ (a a' : ℕ) (m : SimplexCategory),
      rho a m ≫ R.d a a' = (K.d a a').app m ≫ rho a' m) :
    K ⟶ constantCosimplicialCochainComplex.obj R where
  f a :=
    { app := fun m => rho a m
      naturality := fun _ _ φ => (hcosimplicial a φ).trans (Category.comp_id _).symm }
  comm' a a' _ := NatTrans.ext (funext fun m => hd a a' m)

/-- The rows of `Const(R)` are `R`. -/
theorem rowComplex_const (b : ℕ) :
    rowComplex (constantCosimplicialCochainComplex.obj R) b = R := rfl

/-- Each column of the double complex of `Const(R)` is exact off degree `0`. -/
theorem exactAt_const_X (a : ℤ) {q : ℤ} (hq : q ≠ 0) :
    (((functor C).obj (constantCosimplicialCochainComplex.obj R)).X a).ExactAt q := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  refine isZero_homology_X _ a q fun n _ j hj => ?_
  subst hj
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact constantAlternatingCofaceMapComplex_exactAt_of_ne_zero (R.X n) j
    (by exact_mod_cast hq)

/-- The differential out of degree `0` of each column of the double complex of `Const(R)`
vanishes. -/
theorem const_X_d_zero_one (a : ℤ) :
    (((functor C).obj (constantCosimplicialCochainComplex.obj R)).X a).d 0 1 = 0 := by
  by_cases ha : ∃ n : ℕ, (n : ℤ) = a
  · obtain ⟨n, rfl⟩ := ha
    refine StacksDraft.TotalRowComparison.d_eq_zero_of_iso
      (columnIso (constantCosimplicialCochainComplex.obj R) n) 0 1 ?_
    have h0 : ((alternatingCofaceMapComplex C).obj
        ((constantCosimplicialCochainComplex.obj R).X n)).d 0 1 = 0 :=
      constantAlternatingCofaceMapComplex_d_zero_one (R.X n)
    rw [HomologicalComplex.extend_d_eq _ ComplexShape.embeddingUpNat
      (i := 0) (j := 1) (show ComplexShape.embeddingUpNat.f 0 = (0 : ℤ) from rfl)
      (show ComplexShape.embeddingUpNat.f 1 = (1 : ℤ) from rfl), h0, zero_comp, comp_zero]
  · have hz : IsZero (((functor C).obj (constantCosimplicialCochainComplex.obj R)).X a) :=
      isZero_X_of_not_nat _ ha
    exact (Functor.map_isZero (HomologicalComplex.eval C (ComplexShape.up ℤ) 0) hz).eq_of_src _ _

/-- The double complex of `Const(R)` has finite diagonals. -/
theorem diagonalFinite_const :
    DiagonalFinite
      ((functor C).obj (constantCosimplicialCochainComplex.obj R)) :=
  StacksDraft.TotalRowComparison.diagonalFinite_of_bounded _ 0
    (fun a _ hb => isZero_X_X_of_neg _ a hb) (fun _ ha => isZero_X_of_neg _ ha)

/-- The row `0` of the double complex of `Const(R)` has the cohomology of `R`. -/
def constRowZeroHomologyIso (j : ℕ) :
    (((functor C).obj (constantCosimplicialCochainComplex.obj R)).flip.X 0).homology (j : ℤ) ≅
      R.homology j :=
  ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) (j : ℤ)).mapIso
      (rowIso (constantCosimplicialCochainComplex.obj R) 0)).trans
    ((rowComplex (constantCosimplicialCochainComplex.obj R) 0).extendHomologyIso
      ComplexShape.embeddingUpNat (j := j) (j' := (j : ℤ)) rfl)

/-- **The total complex of `Const(R)` has the cohomology of `R`.** -/
def constTotalHomologyIso (j : ℕ) :
    (((functor C).obj (constantCosimplicialCochainComplex.obj R)).total
      (ComplexShape.up ℤ)).homology (j : ℤ) ≅ R.homology j :=
  (StacksDraft.TotalRowComparison.rowZeroHomologyIsoTotal _ (diagonalFinite_const R)
      (fun p _q hq => isZero_X_X_of_neg _ p hq) (fun a _ hq => exactAt_const_X R a hq)
      (const_X_d_zero_one R) (j : ℤ)).symm.trans
    (constRowZeroHomologyIso R j)

variable (K) in
/-- **The two degenerations combined**: if the Moore complexes of the `K^a`, `a > 0`, are acyclic
and `rho : K ⟶ Const(R)` is a quasi-isomorphism on every row, the cohomology of the Moore complex
of `K^0` is the cohomology of `R`. -/
def columnZeroHomologyIsoOfRowComparison
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex C).obj (K.X n)).homology j))
    (rho : K ⟶ constantCosimplicialCochainComplex.obj R)
    (hrow : ∀ b : ℕ, QuasiIso (rowMap rho b)) (j : ℕ) :
    ((alternatingCofaceMapComplex C).obj (K.X 0)).homology j ≅ R.homology j :=
  (totalHomologyIsoColumnZero K hcol j).symm.trans
    ((totalHomologyIsoOfRows rho hrow (j : ℤ)).trans (constTotalHomologyIso R j))

end Crystalline.CosimplicialDoubleComplex
