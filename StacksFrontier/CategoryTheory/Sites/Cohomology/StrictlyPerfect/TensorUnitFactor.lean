module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.TensorOfStrictlyPerfectComplexes
public import StacksFrontier.Algebra.Homology.ReindexCochainComplex
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TensorComplex.TotalComplexComparisonSections
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.ExtensionByZeroTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPushforwardModules.HasSheafComposeForget

/-!
# Tensoring with a complex concentrated in one degree and trivialised there

Let `X` be a ringed site, let `A` be a cochain complex of `O`-modules which vanishes outside the
single degree `k` and whose term there is isomorphic to the structure sheaf, and let `Y` be any
cochain complex of `O`-modules. In each total degree `n` the total tensor complex
`Tot(A ⊗_O Y)` is then just `Y^{n - k}`:

`(Tot(A ⊗_O Y))^n ≅ Y^{n - k}`

That is `AlgebraicGeometry.RingedSite.tensorTotalUnitFactorIso`, and it is the tensor-side
analogue of `AlgebraicGeometry.RingedSite.homUnitEvaluationIso`, which collapses the internal
Hom complex out of such an `A` and from which the single-degree base case of Stacks 0ATN part (1)
was built. This file supplies what the corresponding base case of part (2) needs, where the
complex concentrated in one degree is the tensor factor rather than the source of the internal
Hom.

The statement is **degreewise only, and deliberately so.** The morphism it is used on — the
interchange morphism of Stacks 0BYR — is already a morphism of complexes, so showing it is an
isomorphism needs only that each of its components is one, and the Koszul sign that makes the
chain-level collapse awkward never has to be computed.

Degreewise the total complex is the coproduct of the `A^p ⊗_O Y^q` over `p + q = n`, and all of
its terms but the one with `p = k` vanish, because tensoring with a zero module gives zero. So
the inclusion of that one term is an isomorphism, which is
`AlgebraicGeometry.RingedSite.isIso_ιTotal_of_unitFactor`; composing with the trivialisation of
`A^k` and the left unit constraint `O ⊗_O Y^q ≅ Y^q` gives the collapse.

The **left** unit constraint `Stacks.SheafOfModules.Tensor.sheafTensorUnitIsoLeft` is used, not
the right one together with a braiding, because the surviving summand is `A^k ⊗_O Y^q` with the
trivialised factor on the left, and because only the left constraint has a description on local
sections — which is what the consumer of this collapse needs.

## References

* [Stacks Project, Lemma 36.10.11 (Tag 0ATN)](https://stacks.math.columbia.edu/tag/0ATN)
* [Stacks Project, Lemma 20.49.10 (Tag 0BYR)](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Section 20.48 (Tag 06YM)](https://stacks.math.columbia.edu/tag/06YM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open Stacks.SheafOfModules.Tensor

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable (X : RingedSite.{u, u, u})
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]

variable {A Y : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **The inclusion of a single possibly-nonzero term of a colimit cofan is an isomorphism.**
The inverse is the morphism out of the colimit which is the identity on that term and zero on
the others, which are zero objects. -/
private theorem isIso_cofan_inj_of_isZero {C : Type*} [Category C] [HasZeroMorphisms C]
    {ι : Type*} {F : ι → C} (c : Cofan F) (hc : IsColimit c) (j : ι)
    (hz : ∀ i, i ≠ j → IsZero (F i)) : IsIso (c.inj j) := by
  classical
  let f (i : ι) : F i ⟶ F j := if h : i = j then eqToHom (congrArg F h) else 0
  refine ⟨⟨Cofan.IsColimit.desc hc f, ?_, ?_⟩⟩
  · rw [Cofan.IsColimit.fac]
    simp [f]
  · refine Cofan.IsColimit.hom_ext hc _ _ fun i => ?_
    rw [← Category.assoc, Cofan.IsColimit.fac]
    by_cases hi : i = j
    · subst i; simp [f]
    · exact (hz i hi).eq_of_src _ _

/-- The inclusion of the summand `(a, b)` of `Tot(K ⊗_O L)` in total degree `n` is an isomorphism
if all the summands `(p, q)` with `p ≠ a` are zero. -/
private theorem isIso_ιTotal_of_isZero_of_ne {K L : CochainComplex
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ} (a b n : ℤ) (h : a + b = n)
    (hz : ∀ p q, p + q = n → p ≠ a → IsZero (((sheafTensor.{u, u, u, u, u} X.O).obj (K.X p)).obj
      (L.X q))) :
    IsIso ((Stacks.SheafOfModules.Tensor.tensorBicomplex X.O K L).ιTotal
      (ComplexShape.up ℤ) a b n h) := by
  refine isIso_cofan_inj_of_isZero _
    ((Stacks.SheafOfModules.Tensor.tensorBicomplex X.O K L).toGradedObject.isColimitCofanMapObj
      _ n) _ ?_
  rintro ⟨⟨p, q⟩, hpq⟩ hb
  refine hz p q hpq ?_
  rintro rfl
  obtain rfl : q = b := by
    have hs : p + q = n := hpq
    omega
  exact hb rfl

/-- **The summand of the total tensor complex at a single-degree tensor factor exhausts it.**
If `A` vanishes outside degree `k`, then in total degree `n` the only possibly-nonzero summand
of `Tot(A ⊗_O Y)` is the one of bidegree `(k, n - k)`, so its inclusion is an isomorphism. -/
theorem isIso_ιTotal_of_unitFactor (k n : ℤ) (hA : ∀ p, p ≠ k → IsZero (A.X p)) :
    IsIso ((Stacks.SheafOfModules.Tensor.tensorBicomplex X.O A Y).ιTotal
      (ComplexShape.up ℤ) k (n - k) n (by simp)) :=
  isIso_ιTotal_of_isZero_of_ne X _ _ n _ fun p q _ hp =>
    ((sheafTensor.{u, u, u, u, u} X.O).flip.obj (Y.X q)).map_isZero (hA p hp)

/-- **Tensoring with a complex concentrated in one degree and trivialised there, degreewise.**
If `A` vanishes outside degree `k` and `A^k ≅ O`, then in total degree `n` the total tensor
complex `Tot(A ⊗_O Y)` is `Y^{n - k}`. -/
def tensorTotalUnitFactorIso (k : ℤ)
    (e : A.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hA : ∀ p, p ≠ k → IsZero (A.X p)) (n : ℤ) :
    (tensorTotal X A Y).X n ≅ Y.X (n - k) :=
  (HomologicalComplex.eval _ _ n).mapIso (tensorTotalIsoTensorComplex X A Y) ≪≫
    (@asIso _ _ _ _ _ (isIso_ιTotal_of_unitFactor X k n hA)).symm ≪≫
      ((sheafTensor.{u, u, u, u, u} X.O).mapIso e).app (Y.X (n - k)) ≪≫
        sheafTensorUnitIsoLeft.{u, u, u} X.O (Y.X (n - k))

/-- **The collapse carries a section to the local pure tensor with the trivialising section.**
Read backwards: the inverse of `tensorTotalUnitFactorIso` sends a section `y` of `Y^{c-k}` over
`W` to the local pure tensor of `y` with the section of `A^k` corresponding to `1` under the
trivialisation `e`.

This is what makes the collapse usable in the base case of Stacks 0ATN part (2): the interchange
morphism of Stacks 0BYR is described on local pure tensors by
`tensorHomInterchange_applyHomSectionOver`, so to compute it on a section of the collapsed source
one needs to know that the section is a pure tensor, which is this statement.

Five steps, each of which is an existing description read in term mode: composition acts on
sections by composition; the left unit constraint sends the pure tensor of the unit section back
(`sheafTensorUnitIsoLeft_hom_unit_tmul`), read backwards through `hom_inv_id`; the sheaf tensor
product carries a pure tensor of sections to the pure tensor of the images
(`sheafTensor_map_app_sheafifyUnit_tmul`); the local pure tensor of the sheafified bicomplex is
by definition the sheafification unit followed by the summand inclusion; and the comparison of
the two total tensor complexes matches the two local pure tensors
(`tensorTotalIsoTensorComplex_inv_tensorComplexSection`). -/
lemma tensorTotalUnitFactorIso_inv_apply (k : ℤ)
    (e : A.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hA : ∀ p, p ≠ k → IsZero (A.X p)) (c : ℤ) (W : X.C)
    (y : (Y.X (c - k)).val.obj (op W)) :
    (tensorTotalUnitFactorIso X k e hA c).inv.val.app (op W) y =
      tensorTotalSectionAt X A Y W k (c - k) c (by omega)
        (e.inv.val.app (op W)
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W))) y := by
  have h0 : (tensorTotalUnitFactorIso X k e hA c).inv.val.app (op W) y =
      ((tensorTotalIsoTensorComplex X A Y).inv.f c).val.app (op W)
        ((((Stacks.SheafOfModules.Tensor.tensorBicomplex X.O A Y).ιTotal (ComplexShape.up ℤ)
                k (c - k) c (by simp)).val.app (op W))
          ((((sheafTensor.{u, u, u, u, u} X.O).mapIso e).app (Y.X (c - k))).inv.val.app (op W)
            ((sheafTensorUnitIsoLeft X.O (Y.X (c - k))).inv.val.app (op W) y))) := rfl
  have hiso : ∀ u, (sheafTensorUnitIsoLeft X.O (Y.X (c - k))).inv.val.app (op W)
      ((sheafTensorUnitIsoLeft X.O (Y.X (c - k))).hom.val.app (op W) u) = u := fun u =>
    congrArg (fun φ => φ.val.app (op W) u) (sheafTensorUnitIsoLeft X.O (Y.X (c - k))).hom_inv_id
  have h3 : (sheafTensorUnitIsoLeft X.O (Y.X (c - k))).inv.val.app (op W) y =
      (((PresheafOfModules.sheafificationAdjunction
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
          ((SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).val ⊗
            (Y.X (c - k)).val)).app (op W)
            ((1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) ⊗ₜ y)) :=
    ((hiso _).symm.trans (congrArg
      (fun z => (sheafTensorUnitIsoLeft X.O (Y.X (c - k))).inv.val.app (op W) z)
      (sheafTensorUnitIsoLeft_hom_unit_tmul X.O (Y.X (c - k)) (op W) y))).symm
  refine h0.trans ?_
  refine Eq.trans (congrArg (fun z =>
    ((tensorTotalIsoTensorComplex X A Y).inv.f c).val.app (op W)
      ((((Stacks.SheafOfModules.Tensor.tensorBicomplex X.O A Y).ιTotal (ComplexShape.up ℤ) k
            (c - k) c (by simp)).val.app (op W))
        ((((sheafTensor.{u, u, u, u, u} X.O).mapIso e).app (Y.X (c - k))).inv.val.app (op W)
          z))) h3) ?_
  refine Eq.trans (congrArg (fun z =>
    ((tensorTotalIsoTensorComplex X A Y).inv.f c).val.app (op W)
      ((((Stacks.SheafOfModules.Tensor.tensorBicomplex X.O A Y).ιTotal (ComplexShape.up ℤ) k
            (c - k) c (by simp)).val.app (op W)) z))
    (Stacks.SheafOfModules.ExtensionByZero.sheafTensor_map_app_sheafifyUnit_tmul X.J X.O e.inv
      (Y.X (c - k)) W (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op W)) y)) ?_
  exact tensorTotalIsoTensorComplex_inv_tensorComplexSection X A Y W k (c - k) c (by omega) _ y

/-! ### The unit as the second tensor factor -/

section Right

variable {Z : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}

/-- **The summand of the total tensor complex at a single-degree second factor exhausts it.**
If `Z` vanishes outside degree `k`, then in total degree `n` the only possibly-nonzero summand of
`Tot(Y ⊗_O Z)` is the one of bidegree `(-k + n, k)`, so its inclusion is an isomorphism. This is
the companion of `isIso_ιTotal_of_unitFactor` with the single-degree complex in the other tensor
variable. -/
theorem isIso_ιTotal_of_unitFactorRight (k n : ℤ) (hZ : ∀ q, q ≠ k → IsZero (Z.X q)) :
    IsIso ((Stacks.SheafOfModules.Tensor.tensorBicomplex X.O Y Z).ιTotal (ComplexShape.up ℤ)
      (-k + n) k n (by simp)) :=
  isIso_ιTotal_of_isZero_of_ne X _ _ n _ fun p q hpq hp =>
    ((sheafTensor.{u, u, u, u, u} X.O).obj (Y.X p)).map_isZero (hZ q (by omega))

/-- The trivialisation of the surviving tensor factor, as an isomorphism
`Y^{-k+n} ≅ Y^{-k+n} ⊗_O Z^k`: the right unit constraint followed by the trivialisation of
`Z^k`. -/
def unitFactorRightIso (k : ℤ)
    (e : Z.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (n : ℤ) :
    Y.X (-k + n) ≅ ((sheafTensor.{u, u, u, u, u} X.O).obj (Y.X (-k + n))).obj (Z.X k) :=
  (sheafTensorUnitIsoRight.{u, u, u} X.O (Y.X (-k + n))).symm ≪≫
    (((sheafTensor.{u, u, u, u, u} X.O).obj (Y.X (-k + n))).mapIso e).symm

omit [(sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)] in
/-- The trivialisation of the surviving factor is natural in `Y`. This is the naturality of the
right unit constraint together with the naturality of the tensor bifunctor in its first variable,
and it is what the differential square of the chain-level collapse reduces to. -/
theorem unitFactorRightIso_hom_naturality (k : ℤ)
    (e : Z.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (i j : ℤ) :
    (unitFactorRightIso X k e i).hom ≫
        ((sheafTensor.{u, u, u, u, u} X.O).map (Y.d (-k + i) (-k + j))).app (Z.X k) =
      Y.d (-k + i) (-k + j) ≫ (unitFactorRightIso X k e j).hom := by
  have hinv : ∀ m : ℤ, (unitFactorRightIso X k e m).inv =
      ((sheafTensor.{u, u, u, u, u} X.O).obj (Y.X (-k + m))).map e.hom ≫
        (sheafTensorUnitIsoRight.{u, u, u} X.O (Y.X (-k + m))).hom := fun m => rfl
  have hnat : ((sheafTensor.{u, u, u, u, u} X.O).obj (Y.X (-k + i))).map e.hom ≫
        (sheafTensorUnitIsoRight.{u, u, u} X.O (Y.X (-k + i))).hom ≫
          Y.d (-k + i) (-k + j) =
      ((sheafTensor.{u, u, u, u, u} X.O).map (Y.d (-k + i) (-k + j))).app (Z.X k) ≫
        ((sheafTensor.{u, u, u, u, u} X.O).obj (Y.X (-k + j))).map e.hom ≫
          (sheafTensorUnitIsoRight.{u, u, u} X.O (Y.X (-k + j))).hom := by
    rw [← Category.assoc, ← Category.assoc,
      ← ((sheafTensor.{u, u, u, u, u} X.O).map (Y.d (-k + i) (-k + j))).naturality e.hom,
      Category.assoc, Category.assoc, sheafTensorUnitIsoRight_naturality]
  have hnat' : (unitFactorRightIso X k e i).inv ≫ Y.d (-k + i) (-k + j) =
      ((sheafTensor.{u, u, u, u, u} X.O).map (Y.d (-k + i) (-k + j))).app (Z.X k) ≫
        (unitFactorRightIso X k e j).inv := by
    rw [hinv i, hinv j]
    exact (Category.assoc _ _ _).trans hnat
  exact ((Iso.inv_comp_eq _).1
    (((Category.assoc _ _ _).symm.trans
      (congrArg (fun z => z ≫ (unitFactorRightIso X k e j).hom) hnat')).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z =>
            ((sheafTensor.{u, u, u, u, u} X.O).map (Y.d (-k + i) (-k + j))).app (Z.X k) ≫ z)
          (unitFactorRightIso X k e j).inv_hom_id).trans
          (Category.comp_id _))))).symm

/-- **Tensoring with a complex concentrated in one degree and trivialised there, at the level of
complexes.** If `Z` vanishes outside degree `k` and `Z^k ≅ O`, then `Y` reindexed by `-k` is
isomorphic to `Tot(Y ⊗_O Z)` as a complex, not merely degreewise. The degreewise part is the
surviving summand together with the trivialisation; what is new is the differential square.

**The collapse is sign-free, and that is why the unit is taken as the second tensor factor.**
Mathlib's `TotalComplexShape c c c` has `ε₁ = 1` and `ε₂ = c.ε p`, so of the two terms of the
total differential it is the one carrying the *second* factor's differential that bears the
Koszul sign. With `Z` concentrated in one degree that term vanishes, `Z` having no differential
out of degree `k`, and only the sign-free term survives. Had the trivialised complex been the
first factor the surviving term would have been the signed one, with sign `(-1)^k`.

The chain-level statement is what the K-injectivity side condition of Stacks 0ATN part (2)
needs: `IsKInjective` is a property of a complex, where the base case of the interchange morphism
needed only a degreewise identification. -/
def tensorTotalUnitFactorRightIso (k : ℤ)
    (e : Z.X k ≅ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (hZ : ∀ q, q ≠ k → IsZero (Z.X q)) :
    CochainComplex.reindexBy Y (-k) ≅
      ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj Y).obj Z :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => unitFactorRightIso X k e n ≪≫
      (@asIso _ _ _ _ _ (isIso_ιTotal_of_unitFactorRight X k n hZ)))
    (fun i j hij => by
      obtain rfl : j = i + 1 := hij.symm
      have hd2 : HomologicalComplex.mapBifunctor.d₂ Y Z (sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ) (-k + i) k (i + 1) = 0 := by
        rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _
          (show (ComplexShape.up ℤ).Rel k (k + 1) from rfl) _ (by simp; omega)]
        rw [show Z.d k (k + 1) = 0 from (hZ (k + 1) (by omega)).eq_of_tgt _ _]
        rw [Functor.map_zero, zero_comp, smul_zero]
      have hd1 : HomologicalComplex.mapBifunctor.d₁ Y Z (sheafTensor.{u, u, u, u, u} X.O)
          (ComplexShape.up ℤ) (-k + i) k (i + 1) =
          ((sheafTensor.{u, u, u, u, u} X.O).map (Y.d (-k + i) (-k + (i + 1)))).app (Z.X k) ≫
            HomologicalComplex.ιMapBifunctor Y Z (sheafTensor.{u, u, u, u, u} X.O)
              (ComplexShape.up ℤ) (-k + (i + 1)) k (i + 1) (by simp) := by
        rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show (ComplexShape.up ℤ).Rel
          (-k + i) (-k + (i + 1)) by simp; omega) _ _ (by simp)]
        exact one_smul ℤˣ _
      have hpin : ∀ n : ℤ, (unitFactorRightIso X k e n ≪≫
          (@asIso _ _ _ _ _ (isIso_ιTotal_of_unitFactorRight X k n hZ))).hom =
          (unitFactorRightIso X k e n).hom ≫
            HomologicalComplex.ιMapBifunctor Y Z (sheafTensor.{u, u, u, u, u} X.O)
              (ComplexShape.up ℤ) (-k + n) k n (by simp) := fun n => rfl
      have hid : HomologicalComplex.ιMapBifunctor Y Z (sheafTensor.{u, u, u, u, u} X.O)
              (ComplexShape.up ℤ) (-k + i) k i (by simp) ≫
            (HomologicalComplex.mapBifunctor Y Z (sheafTensor.{u, u, u, u, u} X.O)
              (ComplexShape.up ℤ)).d i (i + 1) =
          ((sheafTensor.{u, u, u, u, u} X.O).map (Y.d (-k + i) (-k + (i + 1)))).app (Z.X k) ≫
            HomologicalComplex.ιMapBifunctor Y Z (sheafTensor.{u, u, u, u, u} X.O)
              (ComplexShape.up ℤ) (-k + (i + 1)) k (i + 1) (by simp) := by
        rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
          HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂, hd2,
          add_zero, hd1]
      exact (congrArg (fun z => z ≫ (((tensorComplex X.O).obj Y).obj Z).d i (i + 1))
        (hpin i)).trans
        ((Category.assoc _ _ _).trans
          ((congrArg (fun z => (unitFactorRightIso X k e i).hom ≫ z) hid).trans
            ((Category.assoc _ _ _).symm.trans
              ((congrArg (fun z => z ≫ HomologicalComplex.ιMapBifunctor Y Z
                  (sheafTensor.{u, u, u, u, u} X.O)
              (ComplexShape.up ℤ) (-k + (i + 1)) k (i + 1) (by simp))
                (unitFactorRightIso_hom_naturality X k e i (i + 1))).trans
                ((Category.assoc _ _ _).trans
                  (congrArg (fun z => Y.d (-k + i) (-k + (i + 1)) ≫ z)
                    (hpin (i + 1)).symm)))))))

end Right

end AlgebraicGeometry.RingedSite

end
