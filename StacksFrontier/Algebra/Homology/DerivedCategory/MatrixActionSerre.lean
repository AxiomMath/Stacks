module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MatrixActionDerived
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.Homology.KFlat.BifunctorBoundedAbove
public import StacksFrontier.Homology.PseudoCoherent.Coherent

/-!
# Tensoring with a bounded complex of finite free modules preserves `D_B`

Let `A` be a commutative ring, `C` an `A`-linear abelian category, `B` a weak Serre subcategory
of `C` (Stacks 02MO) and `Q` a bounded complex of finite free `A`-modules with chosen bases.  If
every cohomology object of `L ∈ D(C)` lies in `B`, then so does every cohomology object of
`L ⊗_A Q` (`CategoryTheory.MatrixAction.derivedTot`).

## Main results

* `WeakSerre.mem_biproduct_const`: a weak Serre subcategory is closed under finite direct sums of
  copies of one object.
* `CategoryTheory.MatrixAction.derivedCategoryB_derivedTot`: the preservation statement.

## References

* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 06UQ](https://stacks.math.columbia.edu/tag/06UQ)
* [Stacks Project, Tag 08IS](https://stacks.math.columbia.edu/tag/08IS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v u

namespace WeakSerre

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory C]

/-- A weak Serre subcategory is closed under finite direct sums of copies of one object. -/
theorem mem_biproduct_const (B : ObjectProperty C) (hB : IsWeakSerre B) {ι : Type} [Finite ι]
    (X : C) (hX : B X) [HasBiproduct fun _ : ι => X] : B (⨁ fun _ : ι => X) := by
  have := DerivedCategoryB.derivedCategoryB_isTriangulated B hB
  have hcl := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms B hB
  have hsingle : ∀ Y : C, B Y →
      DerivedCategoryB.derivedCategoryB B ((DerivedCategory.singleFunctor C 0).obj Y) := by
    intro Y hY n
    rcases lt_trichotomy n 0 with h | rfl | h
    · exact DerivedCategoryB.zero_mem_of_isWeakSerre B hB _
        (DerivedCategory.isZero_of_isGE _ 0 n h)
    · exact hB.isClosedUnderIsomorphisms.of_iso
        ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app Y).symm hY
    · exact DerivedCategoryB.zero_mem_of_isWeakSerre B hB _
        (DerivedCategory.isZero_of_isLE _ 0 n h)
  have hprod : DerivedCategoryB.derivedCategoryB B
      (∏ᶜ fun _ : ι => (DerivedCategory.singleFunctor C 0).obj X) :=
    (DerivedCategoryB.derivedCategoryB B).prop_product
      (f := fun _ : ι => (DerivedCategory.singleFunctor C 0).obj X) fun _ => hsingle X hX
  have : PreservesBiproduct (fun _ : ι => X) (DerivedCategory.singleFunctor C 0) := by
    have := Fintype.ofFinite ι
    infer_instance
  have e : (DerivedCategory.singleFunctor C 0).obj (⨁ fun _ : ι => X) ≅
      ∏ᶜ fun _ : ι => (DerivedCategory.singleFunctor C 0).obj X :=
    (DerivedCategory.singleFunctor C 0).mapBiproduct _ ≪≫ biproduct.isoProduct _
  exact hB.isClosedUnderIsomorphisms.of_iso
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).app _) (hcl.of_iso e.symm hprod 0)

end WeakSerre

namespace CategoryTheory.MatrixAction

variable (A : Type w) [CommRing A]

attribute [local instance] Abelian.hasFiniteBiproducts hasBinaryBiproducts_of_finite_biproducts


section Split

open HomologicalComplex ComplexShape

variable {Bc : Type*} [Category Bc] [Preadditive Bc] [HasZeroObject Bc]

/-- The stupid truncation of `L` in the degrees `≤ b` vanishes in the degrees `> b`. -/
private lemma isZero_stupidTrunc_embeddingUpIntLE_X (L : CochainComplex Bc ℤ) {b q : ℤ}
    (h : b < q) : IsZero ((L.stupidTrunc (embeddingUpIntLE b)).X q) :=
  L.isZero_stupidTrunc_X _ q fun k => by
    show b - (k : ℤ) ≠ q
    omega

omit [HasZeroObject Bc] in
/-- In a complex strictly concentrated in degrees `≤ b`, the differential out of degree `b` is
zero. -/
lemma comp_d_eq_zero_of_isStrictlyLE (L : CochainComplex Bc ℤ) (b : ℤ) [L.IsStrictlyLE b] :
    ∀ k, (ComplexShape.up ℤ).Rel b k → (𝟙 (L.X b)) ≫ L.d b k = 0 := by
  intro k hk
  simp only [ComplexShape.up_Rel] at hk
  exact (L.isZero_of_isStrictlyLE b k (by omega)).eq_of_tgt _ _

/-- A complex concentrated in the single degree `b` is its term in degree `b` placed in
degree `b`. -/
def isoSingleOfConcentrated (L : CochainComplex Bc ℤ) (b : ℤ) [L.IsStrictlyLE b]
    [L.IsStrictlyGE b] : (single Bc (ComplexShape.up ℤ) b).obj (L.X b) ≅ L := by
  haveI : ∀ i : ℤ,
      IsIso ((mkHomFromSingle (𝟙 (L.X b)) (comp_d_eq_zero_of_isStrictlyLE L b)).f i) := by
    intro i
    by_cases hi : i = b
    · subst hi
      rw [mkHomFromSingle_f, Category.comp_id]
      infer_instance
    · refine (isZero_single_obj_X (ComplexShape.up ℤ) b (L.X b) i hi).isIso ?_ _
      rcases lt_or_gt_of_ne hi with h | h
      · exact L.isZero_of_isStrictlyGE b i h
      · exact L.isZero_of_isStrictlyLE b i h
  haveI := HomologicalComplex.Hom.isIso_of_components
    (mkHomFromSingle (𝟙 (L.X b)) (comp_d_eq_zero_of_isStrictlyLE L b))
  exact asIso (mkHomFromSingle (𝟙 (L.X b)) (comp_d_eq_zero_of_isStrictlyLE L b))

/-- **Splitting off the top term of a strictly bounded above complex**: there is a degreewise
split short exact sequence whose first term is the top term placed in its degree, whose middle
term is the complex and whose last term is the stupid truncation below it. -/
theorem exists_degreewiseSplit_top (L : CochainComplex Bc ℤ) (b : ℤ) [L.IsStrictlyLE b] :
    ∃ (S : ShortComplex (CochainComplex Bc ℤ))
      (_ : ∀ n, (S.map (HomologicalComplex.eval Bc _ n)).Splitting),
      Nonempty (S.X₁ ≅ (single Bc (ComplexShape.up ℤ) b).obj (L.X b)) ∧ Nonempty (S.X₂ ≅ L) ∧
        Nonempty (S.X₃ ≅ L.stupidTrunc (embeddingUpIntLE (b - 1))) := by
  set e := embeddingUpIntLE (b - 1)
  set ι := mkHomFromSingle (𝟙 (L.X b)) (comp_d_eq_zero_of_isStrictlyLE L b) with hιdef
  have hιb : IsIso (ι.f b) := by
    rw [hιdef, mkHomFromSingle_f, Category.comp_id]
    infer_instance
  have hlift : e.HasLift (𝟙 (L.restriction e)) :=
    fun _ hj _ _ => (hj.false_of_isTruncLE).elim
  set π := e.liftExtend (𝟙 (L.restriction e)) hlift with hπdef
  have hπiso : ∀ i : ℤ, i ≠ b → IsIso (π.f i) := by
    intro i hi
    by_cases hib : i ≤ b - 1
    · refine (e.isIso_liftExtend_f_iff _ hlift
        (DerivedCategory.embeddingUpIntLE_f_toNat (b - 1) i hib)).2 ?_
      rw [HomologicalComplex.id_f]
      infer_instance
    · exact (L.isZero_of_isStrictlyLE b i (by omega)).isIso
        (isZero_stupidTrunc_embeddingUpIntLE_X L (by omega)) _
  have hTb : IsZero ((L.stupidTrunc e).X b) := isZero_stupidTrunc_embeddingUpIntLE_X L (by omega)
  have hcomp : ι ≫ π = 0 := HomologicalComplex.hom_ext _ _ fun i => by
    by_cases hi : i = b
    · subst hi
      exact hTb.eq_of_tgt _ _
    · exact (isZero_single_obj_X (ComplexShape.up ℤ) b (L.X b) i hi).eq_of_src _ _
  refine ⟨ShortComplex.mk ι π hcomp, fun n => ?_, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩, ⟨Iso.refl _⟩⟩
  by_cases hn : n = b
  · subst hn
    have := hιb
    exact { r := inv (ι.f n)
            s := 0
            f_r := by simp
            s_g := hTb.eq_of_tgt _ _
            id := by simp }
  · have := hπiso n hn
    exact { r := 0
            s := inv (π.f n)
            f_r := (isZero_single_obj_X (ComplexShape.up ℤ) b (L.X b) n hn).eq_of_src _ _
            s_g := by simp
            id := by simp }

end Split

section Induction

variable {Bc : Type*} [Category Bc] [Preadditive Bc] [HasZeroObject Bc] [HasBinaryBiproducts Bc]
  (P : CochainComplex Bc ℤ → Prop)
  (hiso : ∀ {M M' : CochainComplex Bc ℤ}, (M ≅ M') → P M → P M')
  (hext : ∀ (S : ShortComplex (CochainComplex Bc ℤ))
    (_ : ∀ n, (S.map (HomologicalComplex.eval Bc _ n)).Splitting), P S.X₁ → P S.X₃ → P S.X₂)
  (hsingle : ∀ (M : Bc) (q : ℤ), P ((HomologicalComplex.single Bc (ComplexShape.up ℤ) q).obj M))

omit [HasBinaryBiproducts Bc] in
include hiso hext hsingle in
private lemma prop_of_bounds (n : ℕ) : ∀ (L : CochainComplex Bc ℤ) (a b : ℤ),
    L.IsStrictlyLE b → L.IsStrictlyGE a → a + n = b → P L := by
  induction n with
  | zero =>
      intro L a b hle hge hab
      obtain rfl : a = b := by omega
      exact hiso (isoSingleOfConcentrated L a) (hsingle _ a)
  | succ n IH =>
      intro L a b hle hge hab
      set e := ComplexShape.embeddingUpIntLE (b - 1)
      have hiso' : ∀ q : ℤ, q ≤ b - 1 → ((L.stupidTrunc e).X q ≅ L.X q) := fun q hq =>
        L.stupidTruncXIso e (DerivedCategory.embeddingUpIntLE_f_toNat (b - 1) q hq)
      have hgeT : CochainComplex.IsStrictlyGE (L.stupidTrunc e) a := by
        rw [CochainComplex.isStrictlyGE_iff]
        intro i hi
        by_cases hib : i ≤ b - 1
        · exact IsZero.of_iso (L.isZero_of_isStrictlyGE a i hi) (hiso' i hib)
        · exact isZero_stupidTrunc_embeddingUpIntLE_X L (by omega)
      obtain ⟨S, σ, ⟨h₁⟩, ⟨h₂⟩, ⟨h₃⟩⟩ := exists_degreewiseSplit_top L b
      exact hiso h₂ (hext S σ (hiso h₁.symm (hsingle _ b))
        (hiso h₃.symm (IH _ a (b - 1) inferInstance hgeT (by omega))))

omit [HasBinaryBiproducts Bc] in
include hiso hext hsingle in
/-- **A property of complexes stable under isomorphism and under extensions in degreewise split
short exact sequences, and holding for complexes concentrated in one degree, holds for strictly
bounded complexes.** -/
theorem prop_of_isStrictlyLE_of_isStrictlyGE (L : CochainComplex Bc ℤ) (a b : ℤ)
    [L.IsStrictlyLE b] [L.IsStrictlyGE a] : P L := by
  by_cases hab : a ≤ b
  · exact prop_of_bounds P hiso hext hsingle (b - a).toNat L a b inferInstance inferInstance
      (by omega)
  · have hge : L.IsStrictlyGE b := L.isStrictlyGE_of_ge b a (by omega)
    exact prop_of_bounds P hiso hext hsingle 0 L b b inferInstance hge (by omega)

end Induction

section Serre

variable {C : Type u} [Category.{v} C] [Abelian C] [Linear A C]
  [∀ (K : CochainComplex C ℤ) (Q : CochainComplex (Mat_ (SingleObj A)) ℤ),
      HomologicalComplex.HasMapBifunctor K Q (matrixAction A (C := C)) (ComplexShape.up ℤ)]
  [HasDerivedCategory C]

/-- `Tot(K ⊗_A M[q])` for one finite free module `M` is the shift by `-q` of the complex
`p ↦ ⨁_{M} Kᵖ`. -/
def totSingleIso (K : CochainComplex C ℤ) (M : Mat_ (SingleObj A)) (q : ℤ) :
    (tot A ((HomologicalComplex.single (Mat_ (SingleObj A)) (ComplexShape.up ℤ) q).obj M)).obj K ≅
      (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-q)).obj
        (CochainComplex.KFlatBifunctor.rowComplex (matrixAction A) K M) :=
  have : (StacksDraft.TotalSingleRow.singleRow
      (CochainComplex.KFlatBifunctor.rowComplex (matrixAction A) K M) q).HasTotal
        (ComplexShape.up ℤ) :=
    HomologicalComplex₂.hasTotal_of_iso
      (CochainComplex.KFlatBifunctor.mapBifunctorSingleIso (matrixAction A) K M q) _
  have := StacksDraft.TotalSingleRow.isIso_totalSingleRowUnit
    (CochainComplex.KFlatBifunctor.rowComplex (matrixAction A) K M) q
  HomologicalComplex₂.total.mapIso
      (CochainComplex.KFlatBifunctor.mapBifunctorSingleIso (matrixAction A) K M q) _ ≪≫
    (asIso (StacksDraft.TotalSingleRow.totalSingleRowUnit
      (CochainComplex.KFlatBifunctor.rowComplex (matrixAction A) K M) q)).symm

variable (P : ObjectProperty C) (hP : WeakSerre.IsWeakSerre P)

include hP in
/-- The cohomology of `Tot(K ⊗_A M[q])` lies in a weak Serre subcategory if that of `K` does. -/
lemma derivedCategoryB_tot_single (K : CochainComplex C ℤ)
    (hK : ∀ n : ℤ, P (K.homology n)) (M : Mat_ (SingleObj A)) (q : ℤ) :
    DerivedCategoryB.derivedCategoryB P (DerivedCategory.Q.obj
      ((tot A ((HomologicalComplex.single (Mat_ (SingleObj A)) (ComplexShape.up ℤ) q).obj M)).obj
        K)) := by
  have hcl := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms P hP
  have hrow : DerivedCategoryB.derivedCategoryB P (DerivedCategory.Q.obj
      (CochainComplex.KFlatBifunctor.rowComplex (matrixAction A) K M)) := by
    intro n
    let R := (((matrixAction A).flip.obj M).mapHomologicalComplex (ComplexShape.up ℤ)).obj K
    have eR : CochainComplex.KFlatBifunctor.rowComplex (matrixAction A) K M ≅ R :=
      HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (fun _ _ _ => by
        simp [CochainComplex.KFlatBifunctor.rowComplex, R])
    exact hP.isClosedUnderIsomorphisms.of_iso
      (((K.sc n).mapHomologyIso ((matrixAction A).flip.obj M)).symm ≪≫
        (HomologicalComplex.homologyMapIso eR n).symm ≪≫
          ((DerivedCategory.homologyFunctorFactors C n).app _).symm)
      (WeakSerre.mem_biproduct_const P hP (K.homology n) (hK n))
  exact hcl.of_iso (((DerivedCategory.Q.commShiftIso (-q)).app _).symm ≪≫
    DerivedCategory.Q.mapIso (totSingleIso A K M q).symm)
    (DerivedCategoryB.derivedCategoryB_shift_mem P hP (-q) hrow)

include hP in
/-- **Tensoring with a bounded complex of finite free modules preserves `D_B`**, for a weak Serre
subcategory `B` of `C`. -/
theorem derivedCategoryB_derivedTot (Q : CochainComplex (Mat_ (SingleObj A)) ℤ) (a b : ℤ)
    [Q.IsStrictlyLE b] [Q.IsStrictlyGE a] (K : DerivedCategory C)
    (hK : DerivedCategoryB.derivedCategoryB P K) :
    DerivedCategoryB.derivedCategoryB P ((derivedTot A Q a b).obj K) := by
  have hcl := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms P hP
  let X : CochainComplex C ℤ := DerivedCategory.Q.objPreimage K
  let eX : DerivedCategory.Q.obj X ≅ K := DerivedCategory.Q.objObjPreimageIso K
  have hX : ∀ n : ℤ, P (X.homology n) := fun n =>
    hP.isClosedUnderIsomorphisms.of_iso
      ((DerivedCategory.homologyFunctor C n).mapIso eX.symm ≪≫
        (DerivedCategory.homologyFunctorFactors C n).app X) (hK n)
  refine hcl.of_iso (derivedTotObjIso A Q a b eX).symm ?_
  let R : CochainComplex (Mat_ (SingleObj A)) ℤ → Prop := fun Q' =>
    DerivedCategoryB.derivedCategoryB P (DerivedCategory.Q.obj ((tot A Q').obj X))
  refine prop_of_isStrictlyLE_of_isStrictlyGE R (fun {M M'} e h => ?_) (fun S σ h₁ h₃ => ?_)
    (fun M q => derivedCategoryB_tot_single A P hP X hX M q) Q a b
  · exact hcl.of_iso (DerivedCategory.Q.mapIso
      ((((matrixAction A).map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj X).mapIso e)) h
  · let Φ := Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhi (matrixAction A) X
    let := Stacks.SheafOfModules.Tensor.Reduction.bifunctorXi (matrixAction A) X
    let e : ∀ Q' : CochainComplex (Mat_ (SingleObj A)) ℤ,
        DerivedCategory.Qh.obj (Φ.obj ((HomotopyCategory.quotient _ _).obj Q')) ≅
          DerivedCategory.Q.obj ((tot A Q').obj X) := fun Q' =>
      DerivedCategory.Qh.mapIso
        ((Stacks.SheafOfModules.Tensor.Reduction.bifunctorPhiFactors (matrixAction A) X).app Q') ≪≫
        (DerivedCategory.quotientCompQhIso C).app _
    refine hcl.of_iso (e S.X₂) (DerivedCategoryB.derivedCategoryB_mem_obj₂_of_distinguished P hP _
      (DerivedCategory.Qh.map_distinguished _
        (CochainComplex.KFlatBifunctor.bifunctorPhi_mapTriangle_distinguished (matrixAction A) X _
          (CochainComplex.trianglehOfDegreewiseSplit_distinguished S σ))) ?_ ?_)
    · exact hcl.of_iso (e S.X₁).symm h₁
    · exact hcl.of_iso (e S.X₃).symm h₃

end Serre

end CategoryTheory.MatrixAction

end
