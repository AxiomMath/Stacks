module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorRightUnitor
public import StacksFrontier.Homology.KFlat.BifunctorSingleShift

/-! # The shifted-unitor coherence of the comparison of total tensor complexes

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi presented by a functor of
the underlying sites which is a morphism of sites.  `Stacks 07A4` is proved by comparing total
tensor complexes of K-flat representatives, and
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso` is the comparison that carries it.
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPullback/DerivedPullbackTensorRightUnitor.lean`
proves the **right-unitor coherence** of that comparison, at `L = 𝒪_D[0]`, where the unit law is
`Tot(K ⊗ 𝒪_D[0]) ≅ K`.  This file is the same statement at `L = 𝒪_D[q]` for an arbitrary degree
`q`, where the unit law is `Tot(K ⊗ 𝒪_D[q]) ≅ K⟦-q⟧` instead.

That is what the dévissage of **Stacks 0944** asks for: its base case is the invertibility of
Equation 21.50.0.1 at the structure sheaf placed in *every* degree, and `𝒪_D[q]` is the unit of
`⊗^𝐋` only for `q = 0`.

## Main results

* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorTotalIso_singleUnitor`: **the
  shifted-unitor coherence of the comparison of total tensor complexes.**
* `Stacks.Sheaves.DerivedPullback.mapBifunctorSingleUnitIso`: the unit law
  `Tot(K ⊗_𝒪 𝒪[q]) ≅ K⟦-q⟧`, with its value and the value of its inverse on the one summand of
  each total degree that does not vanish.
* `Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap_naturality_right`: the module-level
  comparison of Stacks 03EL for the site-presented pullback is natural in its second variable.
* `Stacks.Sheaves.DerivedPullback.rightUnitorCoherence_single_deg`: the module-level
  right-unitor coherence read at the degree-`q` term of `𝒪_D[q]`, which is the structure sheaf
  up to `HomologicalComplex.singleObjXSelf`.
* `Stacks.SheafOfModules.isKFlat_single_unit_deg`: the structure sheaf placed in an arbitrary
  degree is a K-flat complex.
* `Stacks.Sheaves.DerivedPullback.isFlat_single_unit_X_deg`: it has flat terms.
* `Stacks.Sheaves.DerivedPullback.pullbackUnitComplexMapDeg`: the unit comparison
  `f^*(𝒪_D[q]) ⟶ 𝒪_C[q]` on complexes.

## Implementation notes

**What changes with the degree, and what does not.**  Nothing in the mathematics: the module-level
right-unitor coherence `Stacks.Sheaves.DerivedPullback.pullbackToposRightUnitorCoherence` of
Stacks 03EL is still the only input.  Two bookkeeping layers appear.

*The sign.*  `CochainComplex.KFlatBifunctor.totalSingleShiftIso` carries `(-1)^{qn}` in degree
`n`.  It appears on both sides of the coherence at the same `n` and the same `q`, and
`Int.units_mul_self` cancels it; the degreewise pullback has to be moved past it, which is
`CategoryTheory.Functor.map_units_smul` for the additive functor `f^*`.

*The identification of the degree-`q` term of `𝒪[q]` with `𝒪`.*  For `q = 0` that
identification, `HomologicalComplex.singleObjXSelf`, is the identity on the nose — the term is
`if (0 : ℤ) = 0 then 𝒪 else 0` — and the degree-zero file disposes of it by `rfl`.  For a
variable `q` it is a genuine transport, so the module-level coherence has to be transported along
it, which needs the naturality of the comparison of Stacks 03EL in its second variable.  That
naturality is proved here, from the naturality of each of the four factors of
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap`.

## References

* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 0944](https://stacks.math.columbia.edu/tag/0944)
* [Stacks Project, Tag 06YM](https://stacks.math.columbia.edu/tag/06YM)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Sheaves.DerivedPullback.KFlatPullback

open scoped CategoryTheory.Prod

/-! ## The structure sheaf placed in an arbitrary degree is K-flat -/

namespace Stacks.SheafOfModules

universe u

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

open CochainComplex.KFlatBifunctor in
/-- **The structure sheaf placed in an arbitrary degree is a K-flat complex.**  By the base case
`CochainComplex.KFlatBifunctor.kFlat_single_of_exact` of Stacks 06YQ it suffices that
`K ↦ K ⊗_𝒪 𝒪` carry acyclic complexes to acyclic complexes, and that functor is the identity by
`Stacks.SheafOfModules.rowComplexUnitIso`.  The hypothesis does not mention the degree, so the
degree-zero statement `Stacks.SheafOfModules.isKFlat_single_unit` and this one have the same
proof. -/
theorem isKFlat_single_unit_deg (q : ℤ) :
    IsKFlat R ((HomologicalComplex.single _ (ComplexShape.up ℤ) q).obj
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))) :=
  kFlat_single_of_exact (Stacks.SheafOfModules.Tensor.sheafTensor R) _ q
    (fun G hG n =>
      HomologicalComplex.ExactAt.of_iso (hG n) (rowComplexUnitIso R G).symm)

end Stacks.SheafOfModules

namespace Stacks.Sheaves.DerivedPullback

universe u

/-! ## The structure sheaf placed in an arbitrary degree has flat terms -/

section Flatness

variable (Y : RingedTopos.{u, u, u})
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **The complex `𝒪[q]` has flat terms.**  In the degree `q` the term is the structure sheaf,
which is flat by `Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit`; in every other degree
it is a zero object, which is flat by
`Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero`. -/
theorem isFlat_single_unit_X_deg (q i : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := Y.O)
      (((HomologicalComplex.single
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ) q).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).X i) := by
  by_cases h : i = q
  · subst h
    exact Stacks.SheafOfModules.FlatRetract.isFlat_of_iso Y.O
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) i
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).symm
      (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit
        (Y := ⟨Y.C, Y.J, Y.O⟩))
  · exact Stacks.SheafOfModules.DerivedTensorProduct.isFlat_of_isZero
      (Y := ⟨Y.C, Y.J, Y.O⟩) _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) q _ i h)

end Flatness

/-! ## The unit law of the total tensor complex at an arbitrary degree -/

section TensorUnitDeg

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u}) [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)]

/-- The structure sheaf of a ringed site, placed in the degree `q`. -/
abbrev singleUnitComplex (q : ℤ) :
    CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ :=
  (HomologicalComplex.single
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (ComplexShape.up ℤ) q).obj
    (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))

/-- **The unit law `A ⊗_𝒪 (𝒪[q])^q ≅ A`**: the degree-`q` term of `𝒪[q]` is the structure sheaf,
by `HomologicalComplex.singleObjXSelf`, and tensoring with the structure sheaf is the identity.
For `q = 0` the first factor is the identity and this is `tensorUnitRight`; for a general `q` it
is not, which is the whole difference between this file and the degree-zero one. -/
def tensorUnitRightDeg (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R))
    (q : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).obj ((singleUnitComplex R q).X q) ≅ A :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).mapIso
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))) ≪≫
    tensorUnitRight R A

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)] in
/-- The unit law at the degree-`q` term is the identification of that term with the structure
sheaf followed by the unit law of the tensor product. -/
lemma tensorUnitRightDeg_hom
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) (q : ℤ) :
    (tensorUnitRightDeg R A q).hom =
      ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj A).map
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).hom ≫
        (tensorUnitRight R A).hom := rfl

/-- **The inclusion of the summand of bidegree `(n - q, q)` of `Tot(K ⊗_𝒪 𝒪[q])`**, the one
summand of total degree `n` that does not vanish. -/
def ιSingleUnitSummand
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (q n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).obj (K.X (n + -q))).obj
        ((singleUnitComplex R q).X q) ⟶
      (HomologicalComplex.mapBifunctor K (singleUnitComplex R q)
        (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ)).X n :=
  HomologicalComplex.ιMapBifunctor K (singleUnitComplex R q)
    (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) (n + -q) q n
    (by dsimp; omega)

/-- **The unit law `Tot(K ⊗_𝒪 𝒪[q]) ≅ K⟦-q⟧`.**  The double complex is concentrated in the row
`q`, where it is the termwise complex `p ↦ K^p ⊗_𝒪 𝒪`, and the total complex of a double complex
concentrated in the row `q` is the shift by `-q` of that row
(`CochainComplex.KFlatBifunctor.totalSingleShiftIso`); the termwise complex is `K` by
`Stacks.SheafOfModules.rowComplexUnitIso`.

For `q = 0` this is `Stacks.Sheaves.DerivedPullback.mapBifunctorUnitIso`; for `q ≠ 0` it is not a
unit law of the tensor product at all, which is why the dévissage of [Stacks, Tag 0944] needs the
*shifted*-unitor machinery rather than the right unitor. -/
def mapBifunctorSingleUnitIso
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (q : ℤ) :
    HomologicalComplex.mapBifunctor K (singleUnitComplex R q)
        (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) ≅
      (CategoryTheory.shiftFunctor
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
        (-q)).obj K :=
  CochainComplex.KFlatBifunctor.totalSingleShiftIso
      (Stacks.SheafOfModules.Tensor.sheafTensor R) K
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) q ≪≫
    (CategoryTheory.shiftFunctor
      (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
      (-q)).mapIso (Stacks.SheafOfModules.rowComplexUnitIso R K)

/-- **The unit law `Tot(K ⊗_𝒪 𝒪[q]) ≅ K⟦-q⟧` on the one summand of total degree `n` that does
not vanish**: on the summand of bidegree `(n - q, q)` it is the unit law of the tensor product
there, scaled by `(-1)^{qn}`. -/
lemma ι_mapBifunctorSingleUnitIso_hom
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (q n : ℤ) :
    ιSingleUnitSummand R K q n ≫ (mapBifunctorSingleUnitIso R K q).hom.f n =
      (q * n).negOnePow • (tensorUnitRightDeg R (K.X (n + -q)) q).hom := by
  have hrow : ((CategoryTheory.shiftFunctor
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
        (-q)).map (Stacks.SheafOfModules.rowComplexUnitIso R K).hom).f n =
      (tensorUnitRight R (K.X (n + -q))).hom := Category.comp_id _
  rw [tensorUnitRightDeg_hom, mapBifunctorSingleUnitIso, ιSingleUnitSummand, Iso.trans_hom,
    HomologicalComplex.comp_f, ← Category.assoc,
    CochainComplex.KFlatBifunctor.ι_totalSingleShiftIso_hom]
  refine (Linear.units_smul_comp (R := ℤ) _ _ _).trans ?_
  rw [Functor.mapIso_hom, hrow]
  rfl

/-- **The inverse of the unit law, in a single degree**: the inverse unit law at the degree-`q`
term followed by the inclusion of the summand of bidegree `(n - q, q)`, scaled by
`(-1)^{qn}`. -/
lemma mapBifunctorSingleUnitIso_inv_f
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
    (q n : ℤ) :
    (mapBifunctorSingleUnitIso R K q).inv.f n =
      (q * n).negOnePow •
        ((tensorUnitRightDeg R (K.X (n + -q)) q).inv ≫ ιSingleUnitSummand R K q n) := by
  have : IsIso ((mapBifunctorSingleUnitIso R K q).hom.f n) :=
    ((HomologicalComplex.eval _ (ComplexShape.up ℤ) n).mapIso
      (mapBifunctorSingleUnitIso R K q)).isIso_hom
  refine (cancel_mono ((mapBifunctorSingleUnitIso R K q).hom.f n)).1 ?_
  rw [Linear.units_smul_comp, Category.assoc, ι_mapBifunctorSingleUnitIso_hom,
    Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul, Iso.inv_hom_id,
    ← HomologicalComplex.comp_f, Iso.inv_hom_id, HomologicalComplex.id_f]

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} R).obj M).Additive]
  [∀ (K L : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor R)
      (ComplexShape.up ℤ)] in
/-- **The unit law at the degree-`q` term is natural in the module.**  Both factors are: the
first by the bifunctoriality of `⊗_𝒪`, the second by the naturality of
`Stacks.SheafOfModules.sheafTensorUnitNatIso`. -/
lemma tensorUnitRightDeg_naturality
    {A A' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)} (a : A ⟶ A')
    (q : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor R).map a).app ((singleUnitComplex R q).X q) ≫
        (tensorUnitRightDeg R A' q).hom =
      (tensorUnitRightDeg R A q).hom ≫ a := by
  have hnat : ((Stacks.SheafOfModules.Tensor.sheafTensor R).map a).app
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R)) ≫
      (tensorUnitRight R A').hom = (tensorUnitRight R A).hom ≫ a :=
    (Stacks.SheafOfModules.sheafTensorUnitNatIso R).hom.naturality a
  rw [tensorUnitRightDeg_hom, tensorUnitRightDeg_hom,
    ← reassoc_of% (((Stacks.SheafOfModules.Tensor.sheafTensor R).map a).naturality
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf R))).hom),
    hnat, Category.assoc]

/-- **The unit law `Tot(K ⊗_𝒪 𝒪[q]) ≅ K⟦-q⟧` is natural in `K`.**  Both sides are morphisms out
of a total complex, so it is enough to compare them on the one summand of each total degree that
does not vanish; there both are the unit law at a module, which is natural by
`tensorUnitRightDeg_naturality`.  The sign of
`CochainComplex.KFlatBifunctor.totalSingleShiftIso` appears on both sides and cancels. -/
lemma mapBifunctorSingleUnitIso_naturality
    {K K' : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ}
    (φ : K ⟶ K') (q : ℤ) :
    HomologicalComplex.mapBifunctorMap φ (𝟙 (singleUnitComplex R q))
          (Stacks.SheafOfModules.Tensor.sheafTensor R) (ComplexShape.up ℤ) ≫
        (mapBifunctorSingleUnitIso R K' q).hom =
      (mapBifunctorSingleUnitIso R K q).hom ≫
        (CategoryTheory.shiftFunctor
          (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
          (-q)).map φ := by
  refine (cancel_epi (mapBifunctorSingleUnitIso R K q).inv).1 ?_
  rw [Iso.inv_hom_id_assoc]
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  have h2 : ((CategoryTheory.shiftFunctor
        (CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf R)) ℤ)
        (-q)).map φ).f n = φ.f (n + -q) := rfl
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    mapBifunctorSingleUnitIso_inv_f, Linear.units_smul_comp, Category.assoc,
    ιSingleUnitSummand, HomologicalComplex.ι_mapBifunctorMap_assoc,
    HomologicalComplex.id_f, CategoryTheory.Functor.map_id, Category.id_comp,
    ← ιSingleUnitSummand, ι_mapBifunctorSingleUnitIso_hom, Linear.comp_units_smul,
    Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul, h2,
    tensorUnitRightDeg_naturality R (φ.f (n + -q)) q, Iso.inv_hom_id_assoc]

end TensorUnitDeg

/-! ## The two spellings of the tensor bifunctor -/

section Bifunctor

variable (Z : RingedTopos.{u, u, u})
  [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Z.J AddCommGrpCat.{u}] [Z.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [Z.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] in
/-- **The uncurried tensor product of sheaves of modules at an identity in the first variable**
is the curried one in the second variable.  This is the one seam between the two spellings of the
tensor bifunctor that the naturality of the comparison of [Stacks, Tag 03EL] has to cross; the
two spellings differ by the image of `𝟙 M`, and declaring the crossing once keeps it out of the
goals. -/
lemma uncurry_sheafTensor_map_id_fst
    {M N N' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)} (v : N ⟶ N') :
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Z.O)).map
        ((𝟙 M ×ₘ v) : ((M, N) : _ × _) ⟶ (M, N')) =
      ((Stacks.SheafOfModules.Tensor.sheafTensor Z.O).obj M).map v := by
  rw [Functor.uncurry_obj_map, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

end Bifunctor

/-! ## The shifted-unitor coherence at the level of complexes -/

section Complexes

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y) (hmos : f.u.IsMorphismOfSites Y.J X.J)

open Stacks.Sheaves.RingedToposModules in
/-- **The comparison of [Stacks, Tag 03EL] for the four-field pullback**, at a pair of sheaves of
modules, with its source and target ascribed in the spellings the factors of
`Stacks.Sheaves.DerivedPullback.pullbackToposTensorMap` are written at.

The comparison is a natural transformation of bifunctors, so its component at a pair carries the
composite spelling of the functors in its type; a rewrite whose motive abstracts a subterm
containing it is then not type-correct at the transparency `rw` checks at.  Declaring the
crossing once, in a type, is what this is for. -/
def pullbackTensorComparisonApp
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    ((modulesHomOfSiteHom f hmos).pullbackModules).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj A).obj B) ⟶
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (((modulesHomOfSiteHom f hmos).pullbackModules).obj A)).obj
        (((modulesHomOfSiteHom f hmos).pullbackModules).obj B) :=
  (Stacks.SheafOfModules.pullbackTensorIso (modulesHomOfSiteHom f hmos)).hom.app (A, B)

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
open Stacks.Sheaves.RingedToposModules in
/-- The module-level comparison for the site-presented pullback, written through the ascribed
comparison of [Stacks, Tag 03EL].  The two sides are the same term. -/
lemma pullbackToposTensorMap_eq_comparisonApp
    (A B : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    pullbackToposTensorMap f hmos A B =
      (pullbackModulesSiteIso f hmos).inv.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj A).obj B) ≫
        pullbackTensorComparisonApp f hmos A B ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
            ((pullbackModulesSiteIso f hmos).hom.app A)).app
          (((modulesHomOfSiteHom f hmos).pullbackModules).obj B) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (f.pullbackTopos.obj A)).map ((pullbackModulesSiteIso f hmos).hom.app B) := rfl

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
open Stacks.Sheaves.RingedToposModules in
/-- **The comparison of [Stacks, Tag 03EL] is natural in its second variable**, in the ascribed
spelling.  This is the naturality of `Stacks.SheafOfModules.pullbackTensorIso` at `(𝟙 A, g)`,
with the one seam between the uncurried and curried spellings of the tensor bifunctor crossed by
`uncurry_sheafTensor_map_id_fst`. -/
lemma pullbackTensorComparisonApp_naturality_right
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {B B' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (g : B ⟶ B') :
    ((modulesHomOfSiteHom f hmos).pullbackModules).map
          (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj A).map g) ≫
        pullbackTensorComparisonApp f hmos A B' =
      pullbackTensorComparisonApp f hmos A B ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
            (((modulesHomOfSiteHom f hmos).pullbackModules).obj A)).map
          (((modulesHomOfSiteHom f hmos).pullbackModules).map g) := by
  have hΘ := (Stacks.SheafOfModules.pullbackTensorIso
      (modulesHomOfSiteHom f hmos)).hom.naturality ((𝟙 A ×ₘ g) : ((A, B) : _ × _) ⟶ (A, B'))
  dsimp only [Functor.comp_map, Functor.prod_map] at hΘ
  rw [uncurry_sheafTensor_map_id_fst Y g, CategoryTheory.Functor.map_id,
    uncurry_sheafTensor_map_id_fst X
      (((modulesHomOfSiteHom f hmos).pullbackModules).map g)] at hΘ
  exact hΘ

omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
open Stacks.Sheaves.RingedToposModules in
/-- **The module-level comparison of [Stacks, Tag 03EL] for the site-presented pullback is
natural in its second variable.**

The comparison is a composite of four factors: the identification of the two pullbacks on the
source, the comparison of Stacks 03EL for the four-field pullback, and the identification of the
two pullbacks in each tensor factor.  Each of the four is natural.

The degree-zero file does not need this: there the second variable is the degree-zero term of
`𝒪_D[0]`, which is the structure sheaf on the nose. -/
lemma pullbackToposTensorMap_naturality_right
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {B B' : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (g : B ⟶ B') :
    f.pullbackTopos.map (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj A).map g) ≫
        pullbackToposTensorMap f hmos A B' =
      pullbackToposTensorMap f hmos A B ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (f.pullbackTopos.obj A)).map (f.pullbackTopos.map g) := by
  rw [pullbackToposTensorMap_eq_comparisonApp, pullbackToposTensorMap_eq_comparisonApp,
    reassoc_of% ((pullbackModulesSiteIso f hmos).inv.naturality
      (((Stacks.SheafOfModules.Tensor.sheafTensor Y.O).obj A).map g)),
    reassoc_of% (pullbackTensorComparisonApp_naturality_right f hmos A g),
    reassoc_of% (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).map
      ((pullbackModulesSiteIso f hmos).hom.app A)).naturality
        (((modulesHomOfSiteHom f hmos).pullbackModules).map g)),
    ← CategoryTheory.Functor.map_comp
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (f.pullbackTopos.obj A)),
    (pullbackModulesSiteIso f hmos).hom.naturality g,
    CategoryTheory.Functor.map_comp]
  simp only [Category.assoc]

/-- **The unit comparison `f^*(𝒪_D[q]) ⟶ 𝒪_C[q]` on complexes**: the degreewise pullback of the
structure sheaf in the degree `q` is the pullback of the structure sheaf in the degree `q`, and
that is carried to the structure sheaf of the source by the ordinary comparison. -/
def pullbackUnitComplexMapDeg (q : ℤ) :
    (pullbackComplex f).obj (singleUnitComplex Y.O q) ⟶ singleUnitComplex X.O q :=
  ((HomologicalComplex.singleMapHomologicalComplex f.pullbackTopos (ComplexShape.up ℤ) q).app
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom ≫
    (HomologicalComplex.single
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) q).map (pullbackUnitComparison f)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- In the degree `q` the unit comparison on complexes is the ordinary comparison
`f^*𝒪_D ⟶ 𝒪_C`, conjugated by the two identifications of the degree-`q` term of a complex
concentrated in the degree `q`.  For `q = 0` both identifications are identities. -/
lemma pullbackUnitComplexMapDeg_f_self (q : ℤ) :
    (pullbackUnitComplexMapDeg f q).f q =
      f.pullbackTopos.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom ≫
        pullbackUnitComparison f ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
            (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).inv := by
  rw [pullbackUnitComplexMapDeg, HomologicalComplex.comp_f,
    Iso.app_hom, HomologicalComplex.singleMapHomologicalComplex_hom_app_self,
    HomologicalComplex.single_map_f_self, Category.assoc, Iso.inv_hom_id_assoc]

set_option maxHeartbeats 1000000 in
omit [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- **The module-level right-unitor coherence read at the degree-`q` term of `𝒪_D[q]`.**

This is `Stacks.Sheaves.DerivedPullback.pullbackToposRightUnitorCoherence` transported along the
identification of that term with the structure sheaf, which is
`pullbackToposTensorMap_naturality_right`. -/
lemma rightUnitorCoherence_single_deg
    (A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (q : ℤ) :
    pullbackToposTensorMap f hmos A ((singleUnitComplex Y.O q).X q) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (f.pullbackTopos.obj A)).map ((pullbackUnitComplexMapDeg f q).f q) ≫
          (tensorUnitRightDeg X.O (f.pullbackTopos.obj A) q).hom =
      f.pullbackTopos.map (tensorUnitRightDeg Y.O A q).hom := by
  have hmod : pullbackToposTensorMap f hmos A
          (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (f.pullbackTopos.obj A)).map (pullbackUnitComparison f) ≫
          (tensorUnitRight X.O (f.pullbackTopos.obj A)).hom =
      f.pullbackTopos.map (tensorUnitRight Y.O A).hom :=
    pullbackToposRightUnitorCoherence f hmos A
  rw [pullbackUnitComplexMapDeg_f_self, tensorUnitRightDeg_hom, tensorUnitRightDeg_hom,
    ← Category.assoc (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
      (f.pullbackTopos.obj A)).map _),
    ← CategoryTheory.Functor.map_comp
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (f.pullbackTopos.obj A)),
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    CategoryTheory.Functor.map_comp, Category.assoc,
    ← reassoc_of% (pullbackToposTensorMap_naturality_right f hmos A
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) q
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).hom),
    hmod, ← CategoryTheory.Functor.map_comp]

/-- **The inclusion of the summand of bidegree `(n - q, q)` of
`Tot(f^*K ⊗_{𝒪_C} f^*(𝒪_D[q]))`**, with its source spelled with the degrees of the pullback
complexes. -/
def ιSinglePullSummand
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (q n : ℤ) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (((pullbackComplex f).obj K).X (n + -q))).obj
        (((pullbackComplex f).obj (singleUnitComplex Y.O q)).X q) ⟶
      (HomologicalComplex.mapBifunctor ((pullbackComplex f).obj K)
        ((pullbackComplex f).obj (singleUnitComplex Y.O q))
        (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ)).X n :=
  HomologicalComplex.ιMapBifunctor ((pullbackComplex f).obj K)
    ((pullbackComplex f).obj (singleUnitComplex Y.O q))
    (Stacks.SheafOfModules.Tensor.sheafTensor X.O) (ComplexShape.up ℤ) (n + -q) q n
    (by dsimp; omega)

omit [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify Y.J AddCommGrpCat.{u}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (ComplexShape.up ℤ)] in
/-- The last two factors of the left-hand side of the shifted-unitor coherence, on the summand of
bidegree `(n - q, q)`. -/
private lemma ι_singleUnitor_lhs
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (q n : ℤ) :
    ιSinglePullSummand f K q n ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
            (pullbackUnitComplexMapDeg f q) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (ComplexShape.up ℤ)).f n ≫
          (mapBifunctorSingleUnitIso X.O ((pullbackComplex f).obj K) q).hom.f n =
      (q * n).negOnePow •
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (((pullbackComplex f).obj K).X (n + -q))).map
            ((pullbackUnitComplexMapDeg f q).f q) ≫
          (tensorUnitRightDeg X.O (((pullbackComplex f).obj K).X (n + -q)) q).hom) := by
  rw [ιSinglePullSummand, HomologicalComplex.ι_mapBifunctorMap_assoc, HomologicalComplex.id_f,
    CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp,
    ← ιSingleUnitSummand, ι_mapBifunctorSingleUnitIso_hom, Linear.comp_units_smul]

/-- The shifted-unitor coherence on complexes, in a single degree, after the unit law of the
target has been cancelled: the composite is the identity. -/
private lemma singleUnitor_degree
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (q n : ℤ) :
    f.pullbackTopos.map ((mapBifunctorSingleUnitIso Y.O K q).inv.f n) ≫
        (pullbackToposTensorTotalIso f hmos K (singleUnitComplex Y.O q)).hom.f n ≫
          (HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
              (pullbackUnitComplexMapDeg f q) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
              (ComplexShape.up ℤ)).f n ≫
            (mapBifunctorSingleUnitIso X.O ((pullbackComplex f).obj K) q).hom.f n =
      𝟙 (f.pullbackTopos.obj (K.X (n + -q))) := by
  have h1 : f.pullbackTopos.map ((mapBifunctorSingleUnitIso Y.O K q).inv.f n) =
      (q * n).negOnePow •
        (f.pullbackTopos.map (tensorUnitRightDeg Y.O (K.X (n + -q)) q).inv ≫
          f.pullbackTopos.map (ιSingleUnitSummand Y.O K q n)) := by
    rw [mapBifunctorSingleUnitIso_inv_f, CategoryTheory.Functor.map_units_smul,
      CategoryTheory.Functor.map_comp]
  have h2 : f.pullbackTopos.map (ιSingleUnitSummand Y.O K q n) ≫
        (pullbackToposTensorTotalIso f hmos K (singleUnitComplex Y.O q)).hom.f n =
      pullbackToposTensorMapDeg f hmos K (singleUnitComplex Y.O q) (n + -q) q ≫
        ιSinglePullSummand f K q n :=
    ι_pullbackToposTensorTotalIso_hom f hmos K (singleUnitComplex Y.O q) (n + -q) q n
      (by omega)
  have hcoh : pullbackToposTensorMap f hmos (K.X (n + -q)) ((singleUnitComplex Y.O q).X q) ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (((pullbackComplex f).obj K).X (n + -q))).map
            ((pullbackUnitComplexMapDeg f q).f q) ≫
          (tensorUnitRightDeg X.O (((pullbackComplex f).obj K).X (n + -q)) q).hom =
      f.pullbackTopos.map (tensorUnitRightDeg Y.O (K.X (n + -q)) q).hom :=
    rightUnitorCoherence_single_deg f hmos (K.X (n + -q)) q
  rw [h1, Linear.units_smul_comp, Category.assoc, reassoc_of% h2,
    ι_singleUnitor_lhs f K q n, Linear.comp_units_smul, Linear.comp_units_smul,
    smul_smul, Int.units_mul_self, one_smul, pullbackToposTensorMapDeg_eq, hcoh,
    ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id, CategoryTheory.Functor.map_id]

/-- **The shifted-unitor coherence of the comparison of total tensor complexes.**  The comparison
`f^*Tot(K ⊗_{𝒪_D} 𝒪_D[q]) ≅ Tot(f^*K ⊗_{𝒪_C} f^*(𝒪_D[q]))`, followed by the unit comparison in
the second tensor factor and by the unit law `Tot(f^*K ⊗ 𝒪_C[q]) ≅ (f^*K)⟦-q⟧` of the source, is
the degreewise pullback of the unit law of the target followed by the commutation of the
degreewise pullback with the shift.

That last factor is the identity in each degree
(`CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_hom_app_f`); it is there because
`f^*(K⟦-q⟧)` and `(f^*K)⟦-q⟧` are equal only up to moving `f^*` past the sign in the differential
of a shift, and for `q = 0` it does not appear at all. -/
theorem pullbackToposTensorTotalIso_singleUnitor
    (K : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (q : ℤ) :
    (pullbackToposTensorTotalIso f hmos K (singleUnitComplex Y.O q)).hom ≫
        HomologicalComplex.mapBifunctorMap (𝟙 ((pullbackComplex f).obj K))
            (pullbackUnitComplexMapDeg f q) (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (ComplexShape.up ℤ) ≫
          (mapBifunctorSingleUnitIso X.O ((pullbackComplex f).obj K) q).hom =
      (pullbackComplex f).map (mapBifunctorSingleUnitIso Y.O K q).hom ≫
        ((pullbackComplex f).commShiftIso (-q)).hom.app K := by
  refine (cancel_epi ((pullbackComplex f).map
    (mapBifunctorSingleUnitIso Y.O K q).inv)).1 ?_
  rw [← CategoryTheory.Functor.map_comp_assoc, Iso.inv_hom_id,
    CategoryTheory.Functor.map_id, Category.id_comp]
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    CategoryTheory.Functor.mapHomologicalComplex_map_f,
    CategoryTheory.Functor.mapHomologicalComplex_commShiftIso_hom_app_f]
  exact singleUnitor_degree f hmos K q n

end Complexes

end Stacks.Sheaves.DerivedPullback

end
