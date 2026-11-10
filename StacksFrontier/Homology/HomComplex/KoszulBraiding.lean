module

public import Mathlib.Algebra.Category.ModuleCat.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Homology.BifunctorFlip
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Limits.Preserves

/-!
# The Koszul braiding on cochain complexes

Let `R` be a commutative ring. The total complex of the degreewise tensor product makes
`CochainComplex (ModuleCat R) ℤ` a monoidal category, and this module equips that monoidal
structure with its commutativity constraint: on the summand of bidegree `(p, q)` the braiding is
the ordinary symmetry of tensor products of modules multiplied by the Koszul sign `(-1)^(p*q)`.
The Koszul sign is exactly what is needed for the braiding to commute with the total
differential, and it makes the braiding a symmetry rather than merely a braiding, since the sign
is unchanged under swapping `p` and `q`.

## Main definitions

* `CochainComplex.Koszul.koszulSymmetric`: the Koszul symmetric monoidal structure on
  `CochainComplex (ModuleCat R) ℤ`, as data.

## Main results

* `CochainComplex.Koszul.koszulSymmetric_braiding_ιTensorObj`: the braiding of
  `koszulSymmetric` on the homogeneous summand `K^p ⊗ L^q`, which pins it down completely.
* `TotalTensorComplex.cochainComplex_symmetricMonoidalCategory`: the same content in
  existential form, for consumers that only want *some* symmetric structure with this braiding.

## Implementation notes

The monoidal structure on `CochainComplex (ModuleCat R) ℤ` is already fixed by Mathlib: the
tensor product is the total complex of the degreewise tensor product, the unit is `R` placed in
degree zero, and the associator is the canonical total-complex associator. Only the
commutativity constraint is added here, so the braiding is built degreewise out of
`HomologicalComplex.mapBifunctorDesc`, and every verification is reduced to the homogeneous
summands by `HomologicalComplex.mapBifunctor.hom_ext`.

The symmetric structure is deliberately *not* a global instance: `CochainComplex (ModuleCat R) ℤ`
has other braidings, and making this one an instance would silently fix the sign convention for
every downstream file. Consumers take it either as the named datum `koszulSymmetric`, or as a
`[BraidedCategory _]` hypothesis, or existentially through
`TotalTensorComplex.cochainComplex_symmetricMonoidalCategory`.

This module is the conceptual provider for the content of Stacks tags 0FNI and 0GWR; it carries
no tag attribute itself, since those tags are realized elsewhere.

## References

* [Stacks Project, Tag 0FNI](https://stacks.math.columbia.edu/tag/0FNI)
* [Stacks Project, Tag 0GWR](https://stacks.math.columbia.edu/tag/0GWR)
-/

@[expose] public section

open CategoryTheory MonoidalCategory

universe u

namespace CochainComplex.Koszul

variable {R : Type u} [CommRing R]

/-! ## The braiding, degree by degree -/

/-- Right whiskering in `ModuleCat R` commutes with scalar multiplication by a unit of `ℤ`:
`(r • f) ▷ Z = r • (f ▷ Z)`. -/
lemma units_smul_whiskerRight (r : ℤˣ) {X Y Z : ModuleCat R}
    (f : X ⟶ Y) : (r • f) ▷ Z = r • (f ▷ Z) := by
  change (tensorRight Z).map (r • f) = r • (tensorRight Z).map f
  exact Functor.map_units_smul (tensorRight Z) r f

/-- Left whiskering in `ModuleCat R` commutes with scalar multiplication by a unit of `ℤ`:
`Z ◁ (r • f) = r • (Z ◁ f)`. -/
lemma units_smul_whiskerLeft (r : ℤˣ) {X Y Z : ModuleCat R}
    (f : X ⟶ Y) : Z ◁ (r • f) = r • (Z ◁ f) := by
  change (tensorLeft Z).map (r • f) = r • (tensorLeft Z).map f
  exact Functor.map_units_smul (tensorLeft Z) r f

/-- The degree-`n` component of the Koszul braiding: on the summand `K^p ⊗ L^q` it is the
symmetry of `ModuleCat R` scaled by the Koszul sign `(-1)^(p*q)`. -/
noncomputable def braidingX
    (K L : CochainComplex (ModuleCat R) ℤ) (n : ℤ) :
    (K ⊗ L).X n ≅ (L ⊗ K).X n where
  hom := HomologicalComplex.mapBifunctorDesc (fun p q h =>
    ((p * q).negOnePow : ℤˣ) • ((β_ (K.X p) (L.X q)).hom ≫
      HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h)))
  inv := HomologicalComplex.mapBifunctorDesc (fun q p h =>
    ((p * q).negOnePow : ℤˣ) • ((β_ (L.X q) (K.X p)).hom ≫
      HomologicalComplex.ιTensorObj K L p q n (by simpa [add_comm] using h)))
  hom_inv_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q h
    simp only [HomologicalComplex.ι_mapBifunctorDesc_assoc, Linear.units_smul_comp,
      Category.assoc, HomologicalComplex.ι_mapBifunctorDesc, Linear.comp_units_smul,
      smul_smul, SymmetricCategory.symmetry_assoc]
    simp
    rfl
  inv_hom_id := by
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro q p h
    simp only [HomologicalComplex.ι_mapBifunctorDesc_assoc, Linear.units_smul_comp,
      Category.assoc, HomologicalComplex.ι_mapBifunctorDesc, Linear.comp_units_smul,
      smul_smul, SymmetricCategory.symmetry_assoc]
    simp
    rfl

-- The total differential of a tensor product of complexes splits into four terms on each
-- homogeneous summand, and discharging the Koszul-sign bookkeeping for all of them in a single
-- normalization exceeds the default heartbeat budget.
/-- The Koszul sign is exactly what makes the degreewise braiding commute with the total
differential: the sign picked up by moving `K`'s differential past `L^q` cancels the sign
picked up by moving `L`'s differential past `K^p`. -/
lemma braidingX_hom_comm (K L : CochainComplex (ModuleCat R) ℤ) (n m : ℤ)
    (hnm : (ComplexShape.up ℤ).Rel n m) :
    (braidingX K L n).hom ≫ (L ⊗ K).d n m =
      (K ⊗ L).d n m ≫ (braidingX K L m).hom := by
  change (braidingX K L n).hom ≫
      (HomologicalComplex.mapBifunctor L K (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ)).d n m =
    (HomologicalComplex.mapBifunctor K L (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ)).d n m ≫
      (braidingX K L m).hom
  simp only [HomologicalComplex.mapBifunctor.d_eq]
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  have hsum : p + q = n := h
  have hm : n + 1 = m := hnm
  have hp : (ComplexShape.up ℤ).Rel p (p + 1) := rfl
  have hq : (ComplexShape.up ℤ).Rel q (q + 1) := rfl
  have hA : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p + 1, q) = m := by
    change p + 1 + q = m
    omega
  have hB : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p, q + 1) = m := by
    change p + (q + 1) = m
    omega
  simp only [Preadditive.comp_add, Preadditive.add_comp,
    HomologicalComplex.mapBifunctor.ι_D₁_assoc,
    HomologicalComplex.mapBifunctor.ι_D₂_assoc]
  simp only [braidingX, HomologicalComplex.ι_mapBifunctorDesc_assoc,
    Linear.units_smul_comp, Category.assoc, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  have hL₁ : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (q + 1, p) = m := by
    change q + 1 + p = m
    omega
  have hL₂ : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (q, p + 1) = m := by
    change q + (p + 1) = m
    omega
  rw [HomologicalComplex.mapBifunctor.d₁_eq (K₁ := L) (K₂ := K)
    (F := curriedTensor (ModuleCat R)) (c := ComplexShape.up ℤ) (i₁' := q + 1) hq p m hL₁]
  rw [HomologicalComplex.mapBifunctor.d₂_eq (K₁ := L) (K₂ := K)
    (F := curriedTensor (ModuleCat R)) (c := ComplexShape.up ℤ) q (i₂' := p + 1) hp m hL₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq (K₁ := K) (K₂ := L)
    (F := curriedTensor (ModuleCat R)) (c := ComplexShape.up ℤ) (i₁' := p + 1) hp q m hA]
  rw [HomologicalComplex.mapBifunctor.d₂_eq (K₁ := K) (K₂ := L)
    (F := curriedTensor (ModuleCat R)) (c := ComplexShape.up ℤ) p (i₂' := q + 1) hq m hB]
  simp only [curriedTensor_obj_obj, ComplexShape.ε₁_def, curriedTensor_map_app, one_smul,
    ComplexShape.ε₂_def, ComplexShape.ε_up_ℤ, curriedTensor_obj_map, Linear.comp_units_smul,
    ComplexShape.π_def, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc,
    BraidedCategory.braiding_naturality_left_assoc, Linear.units_smul_comp,
    BraidedCategory.braiding_naturality_right_assoc]
  simp only [smul_smul]
  have hsign₁ : (p * q).negOnePow * q.negOnePow = ((p + 1) * q).negOnePow := by
    rw [← Int.negOnePow_add]
    congr 1
    ring
  have hsign₂ : (p * q).negOnePow = p.negOnePow * (p * (q + 1)).negOnePow := by
    calc
      (p * q).negOnePow = (p * q).negOnePow * (2 * p).negOnePow := by
        simp [Int.negOnePow_two_mul]
      _ = (p * q + 2 * p).negOnePow := by rw [Int.negOnePow_add]
      _ = (p + p * (q + 1)).negOnePow := by congr 1; ring
      _ = p.negOnePow * (p * (q + 1)).negOnePow := Int.negOnePow_add _ _
  rw [hsign₁, hsign₂]
  abel

/-- The Koszul braiding `K ⊗ L ≅ L ⊗ K`, assembled from its degreewise components. -/
noncomputable def complexBraiding
    (K L : CochainComplex (ModuleCat R) ℤ) : K ⊗ L ≅ L ⊗ K :=
  HomologicalComplex.Hom.isoOfComponents (braidingX K L)
    (fun n m h => braidingX_hom_comm K L n m h)

/-- On the summand `K^p ⊗ L^q` of `(K ⊗ L)^n`, the braiding `complexBraiding K L` is the
symmetry `K^p ⊗ L^q ≅ L^q ⊗ K^p` multiplied by `(-1)^(p*q)`, followed by the inclusion of the
summand `L^q ⊗ K^p` of `(L ⊗ K)^n`. -/
lemma complexBraiding_ι (K L : CochainComplex (ModuleCat R) ℤ)
    (p q n : ℤ) (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫ (complexBraiding K L).hom.f n =
      ((p * q).negOnePow : ℤˣ) •
        ((β_ (K.X p) (L.X q)).hom ≫
          HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h)) := by
  simp [complexBraiding, braidingX]

/-! ## Naturality, the hexagons and the symmetry -/

/-- The Koszul braiding is natural in its first argument. -/
lemma complexBraiding_naturality_left {K L : CochainComplex (ModuleCat R) ℤ}
    (f : K ⟶ L) (M : CochainComplex (ModuleCat R) ℤ) :
    f ▷ M ≫ (complexBraiding L M).hom =
      (complexBraiding K M).hom ≫ M ◁ f := by
  change HomologicalComplex.tensorHom f (𝟙 M) ≫ (complexBraiding L M).hom =
    (complexBraiding K M).hom ≫ HomologicalComplex.tensorHom (𝟙 M) f
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp [complexBraiding, braidingX, HomologicalComplex.ι_mapBifunctorMap_assoc]

/-- The Koszul braiding is natural in its second argument. -/
lemma complexBraiding_naturality_right (K : CochainComplex (ModuleCat R) ℤ)
    {L M : CochainComplex (ModuleCat R) ℤ} (f : L ⟶ M) :
    K ◁ f ≫ (complexBraiding K M).hom =
      (complexBraiding K L).hom ≫ f ▷ K := by
  change HomologicalComplex.tensorHom (𝟙 K) f ≫ (complexBraiding K M).hom =
    (complexBraiding K L).hom ≫ HomologicalComplex.tensorHom f (𝟙 K)
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp [complexBraiding, braidingX, HomologicalComplex.ι_mapBifunctorMap_assoc]

/-- In degree `n`, the associator `(K ⊗ L) ⊗ M ≅ K ⊗ (L ⊗ M)` of cochain complexes is the
degree-`n` component `HomologicalComplex.mapBifunctorAssociatorX` of the total-complex
associator. -/
lemma complexAssociator_hom_f (K L M : CochainComplex (ModuleCat R) ℤ)
    (n : ℤ) :
    (α_ K L M).hom.f n =
      (HomologicalComplex.mapBifunctorAssociatorX
        (curriedAssociatorNatIso (ModuleCat R)) K L M
        (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) n).hom := by
  change (HomologicalComplex.associator K L M).hom.f n = _
  rfl

/-- Whiskering the inclusion of `K^p ⊗ L^q` with `M^r`, then including into `((K ⊗ L) ⊗ M)^n`,
is the inclusion of the summand `(p, q, r)` of the triple total complex. -/
private lemma ιTensorObj_whiskerRight_ιTensorObj (K L M : CochainComplex (ModuleCat R) ℤ)
    (p q r s n : ℤ) (hs : p + q = s) (hn : s + r = n) (h : p + q + r = n) :
    HomologicalComplex.ιTensorObj K L p q s hs ▷ M.X r ≫
        HomologicalComplex.ιTensorObj (K ⊗ L) M s r n hn =
      HomologicalComplex.mapBifunctor₁₂.ι
        (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R))
        K L M (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r n h :=
  (HomologicalComplex.mapBifunctor₁₂.ι_eq
    (F₁₂ := curriedTensor (ModuleCat R)) (G := curriedTensor (ModuleCat R))
    K L M (ComplexShape.up ℤ) (ComplexShape.up ℤ) p q r s n hs hn).symm

-- The hexagon is checked on every homogeneous summand `K^p ⊗ L^q ⊗ M^r` of the triple total
-- complex, which forces a long chain of associator and inclusion rewrites well past the default
-- heartbeat budget.
set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The forward hexagon identity for the Koszul braiding `complexBraiding`. -/
lemma complexBraiding_hexagon_forward
    (K L M : CochainComplex (ModuleCat R) ℤ) :
    (α_ K L M).hom ≫ (complexBraiding K (L ⊗ M)).hom ≫ (α_ L M K).hom =
      (complexBraiding K L).hom ▷ M ≫ (α_ L K M).hom ≫
        L ◁ (complexBraiding K M).hom := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor₁₂.hom_ext
  intro p q r h
  have hpqr : p + q + r = n := h
  simp only [HomologicalComplex.comp_f]
  simp only [complexAssociator_hom_f]
  simp only [HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc]
  rw [HomologicalComplex.mapBifunctor₂₃.ι_eq
    (F := curriedTensor (ModuleCat R)) (G₂₃ := curriedTensor (ModuleCat R))
    K L M (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
    p q r (q + r) n rfl (by change p + (q + r) = n; omega)]
  rw [Category.assoc]
  simp only [complexBraiding, HomologicalComplex.Hom.isoOfComponents_hom_f,
    braidingX, HomologicalComplex.ι_mapBifunctorDesc_assoc]
  simp only [CategoryTheory.MonoidalCategory.curriedAssociatorNatIso_hom_app_app_app]
  simp only [bifunctorComp₂₃, bifunctorComp₂₃Obj, curriedTensor_obj_obj,
    curriedTensor_obj_map, curriedTensor_map_app]
  have hnat :
      K.X p ◁ HomologicalComplex.ιMapBifunctor L M (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) q r (q + r) rfl ≫
        (β_ (K.X p) ((L ⊗ M).X (q + r))).hom =
      (β_ (K.X p) (L.X q ⊗ M.X r)).hom ≫
        HomologicalComplex.ιMapBifunctor L M (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) q r (q + r) rfl ▷ K.X p := by
    exact BraidedCategory.braiding_naturality_right (K.X p)
      (HomologicalComplex.ιMapBifunctor L M (curriedTensor (ModuleCat R))
        (ComplexShape.up ℤ) q r (q + r) rfl)
  have hnatScalar :
      K.X p ◁ HomologicalComplex.ιMapBifunctor L M (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) q r (q + r) rfl ≫
        (((p * (q + r)).negOnePow : ℤˣ) •
          ((β_ (K.X p) ((L ⊗ M).X (q + r))).hom ≫
            HomologicalComplex.ιTensorObj (L ⊗ M) K (q + r) p n
              (by omega))) =
      (((p * (q + r)).negOnePow : ℤˣ) •
        ((β_ (K.X p) (L.X q ⊗ M.X r)).hom ≫
          HomologicalComplex.ιMapBifunctor L M (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) q r (q + r) rfl ▷ K.X p ≫
          HomologicalComplex.ιTensorObj (L ⊗ M) K (q + r) p n
            (by omega))) := by
    let s : ℤˣ := (p * (q + r)).negOnePow
    have hnatCompose :
        (K.X p ◁ HomologicalComplex.ιMapBifunctor L M (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) q r (q + r) rfl ≫
          (β_ (K.X p) ((L ⊗ M).X (q + r))).hom) ≫
          HomologicalComplex.ιTensorObj (L ⊗ M) K (q + r) p n (by omega) =
        ((β_ (K.X p) (L.X q ⊗ M.X r)).hom ≫
          HomologicalComplex.ιMapBifunctor L M (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) q r (q + r) rfl ▷ K.X p) ≫
          HomologicalComplex.ιTensorObj (L ⊗ M) K (q + r) p n (by omega) := by
      rw [hnat]
    calc
      _ = s • ((K.X p ◁ HomologicalComplex.ιMapBifunctor L M
          (curriedTensor (ModuleCat R)) (ComplexShape.up ℤ) q r (q + r) rfl ≫
          (β_ (K.X p) ((L ⊗ M).X (q + r))).hom) ≫
          HomologicalComplex.ιTensorObj (L ⊗ M) K (q + r) p n (by omega)) := by
            simp only [Linear.comp_units_smul, Category.assoc, s]
      _ = s • (((β_ (K.X p) (L.X q ⊗ M.X r)).hom ≫
          HomologicalComplex.ιMapBifunctor L M (curriedTensor (ModuleCat R))
            (ComplexShape.up ℤ) q r (q + r) rfl ▷ K.X p) ≫
          HomologicalComplex.ιTensorObj (L ⊗ M) K (q + r) p n (by omega)) := by
            rw [hnatCompose]
  have hfirstAssoc :
      ((α_ (K.X p) (L.X q) (M.X r)).hom ≫
        K.X p ◁ HomologicalComplex.ιMapBifunctor L M (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) q r (q + r) rfl) ≫
        (((p * (q + r)).negOnePow : ℤˣ) •
          ((β_ (K.X p) ((L ⊗ M).X (q + r))).hom ≫
            HomologicalComplex.ιTensorObj (L ⊗ M) K (q + r) p n (by omega))) =
      (α_ (K.X p) (L.X q) (M.X r)).hom ≫
        (K.X p ◁ HomologicalComplex.ιMapBifunctor L M (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) q r (q + r) rfl ≫
          (((p * (q + r)).negOnePow : ℤˣ) •
            ((β_ (K.X p) ((L ⊗ M).X (q + r))).hom ≫
              HomologicalComplex.ιTensorObj (L ⊗ M) K (q + r) p n (by omega)))) := by
    exact Category.assoc _ _ _
  calc
    _ = ((α_ (K.X p) (L.X q) (M.X r)).hom ≫
        (K.X p ◁ HomologicalComplex.ιMapBifunctor L M (curriedTensor (ModuleCat R))
          (ComplexShape.up ℤ) q r (q + r) rfl ≫
          (((p * (q + r)).negOnePow : ℤˣ) •
            ((β_ (K.X p) ((L ⊗ M).X (q + r))).hom ≫
              HomologicalComplex.ιTensorObj (L ⊗ M) K (q + r) p n (by omega))))) ≫
        (HomologicalComplex.mapBifunctorAssociatorX (curriedAssociatorNatIso (ModuleCat R))
          L M K (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) n).hom := by
          exact congrArg (fun f => f ≫
            (HomologicalComplex.mapBifunctorAssociatorX (curriedAssociatorNatIso (ModuleCat R))
              L M K (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) n).hom) hfirstAssoc
    _ = ((α_ (K.X p) (L.X q) (M.X r)).hom ≫
        (((p * (q + r)).negOnePow : ℤˣ) •
          ((β_ (K.X p) (L.X q ⊗ M.X r)).hom ≫
            HomologicalComplex.ιMapBifunctor L M (curriedTensor (ModuleCat R))
              (ComplexShape.up ℤ) q r (q + r) rfl ▷ K.X p ≫
            HomologicalComplex.ιTensorObj (L ⊗ M) K (q + r) p n (by omega)))) ≫
        (HomologicalComplex.mapBifunctorAssociatorX (curriedAssociatorNatIso (ModuleCat R))
          L M K (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ) n).hom := by
          rw [hnatScalar]
    _ = _ := by
      have hsum : q + r + p = n := by omega
      have houter :
          ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (q + r, p) = n := by
        change q + r + p = n
        omega
      have hqpr :
          (ComplexShape.up ℤ).r (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ) (q, r, p) = n := by
        change q + r + p = n
        omega
      rw [ιTensorObj_whiskerRight_ιTensorObj L M K q r p (q + r) n rfl houter hqpr]
      simp only [Category.assoc, Linear.units_smul_comp, Linear.comp_units_smul]
      rw [HomologicalComplex.ι_mapBifunctorAssociatorX_hom
        (associator := curriedAssociatorNatIso (ModuleCat R))
        L M K (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        q r p n hqpr]
      simp only [CategoryTheory.MonoidalCategory.curriedAssociatorNatIso_hom_app_app_app]
      have hhex := BraidedCategory.hexagon_forward (K.X p) (L.X q) (M.X r)
      have hhexIncl :
          (α_ (K.X p) (L.X q) (M.X r)).hom ≫
            (β_ (K.X p) (L.X q ⊗ M.X r)).hom ≫
            (α_ (L.X q) (M.X r) (K.X p)).hom ≫
              HomologicalComplex.mapBifunctor₂₃.ι
                (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R))
                L M K (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
                q r p n hqpr =
          (β_ (K.X p) (L.X q)).hom ▷ M.X r ≫
            (α_ (L.X q) (K.X p) (M.X r)).hom ≫
            (L.X q ◁ (β_ (K.X p) (M.X r)).hom) ≫
              HomologicalComplex.mapBifunctor₂₃.ι
                (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R))
                L M K (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
                q r p n hqpr := by
        calc
          _ = ((α_ (K.X p) (L.X q) (M.X r)).hom ≫
                (β_ (K.X p) (L.X q ⊗ M.X r)).hom ≫
                (α_ (L.X q) (M.X r) (K.X p)).hom) ≫
                HomologicalComplex.mapBifunctor₂₃.ι
                  (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R))
                  L M K (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
                  q r p n hqpr := by simp only [← Category.assoc]
          _ = ((β_ (K.X p) (L.X q)).hom ▷ M.X r ≫
                (α_ (L.X q) (K.X p) (M.X r)).hom ≫
                L.X q ◁ (β_ (K.X p) (M.X r)).hom) ≫
                HomologicalComplex.mapBifunctor₂₃.ι
                  (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R))
                  L M K (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
                  q r p n hqpr := congrArg (fun f => f ≫
                HomologicalComplex.mapBifunctor₂₃.ι
                  (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R))
                  L M K (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
                  q r p n hqpr) hhex
          _ = _ := by simp only [Category.assoc]
      rw [hhexIncl]
      have hpqouter : ComplexShape.π (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (p + q, r) = n := by
        change p + q + r = n
        omega
      rw [← ιTensorObj_whiskerRight_ιTensorObj K L M p q r (p + q) n rfl hpqouter h]
      have hwhiskerKL :
          ((complexBraiding K L).hom ▷ M).f n =
            (HomologicalComplex.tensorHom (complexBraiding K L).hom (𝟙 M)).f n := rfl
      have hwhiskerKM :
          (L ◁ (complexBraiding K M).hom).f n =
            (HomologicalComplex.tensorHom (𝟙 L) (complexBraiding K M).hom).f n := rfl
      simp only [complexBraiding] at hwhiskerKL
      rw [hwhiskerKL]
      simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap_assoc]
      simp only [curriedTensor_map_app, curriedTensor_obj_map, HomologicalComplex.id_f,
        MonoidalCategory.whiskerLeft_id]
      rw [← comp_whiskerRight_assoc]
      simp only [HomologicalComplex.Hom.isoOfComponents_hom_f, braidingX,
        HomologicalComplex.ι_mapBifunctorDesc]
      simp only [units_smul_whiskerRight, Linear.units_smul_comp]
      simp only [comp_whiskerRight, Category.assoc]
      have hqpn : q + p + r = n := by omega
      have hsecond :
          HomologicalComplex.mapBifunctor₂₃.ι
              (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R))
              L K M (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              q p r n hqpn ≫ (L ◁ (complexBraiding K M).hom).f n =
            ((p * r).negOnePow : ℤˣ) •
              ((L.X q ◁ (β_ (K.X p) (M.X r)).hom) ≫
                HomologicalComplex.mapBifunctor₂₃.ι
                  (curriedTensor (ModuleCat R)) (curriedTensor (ModuleCat R))
                  L M K (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
                  q r p n hqpr) := by
        rw [HomologicalComplex.mapBifunctor₂₃.ι_eq
          (F := curriedTensor (ModuleCat R)) (G₂₃ := curriedTensor (ModuleCat R))
          L K M (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          q p r (p + r) n rfl (by change q + (p + r) = n; omega)]
        rw [hwhiskerKM]
        rw [Category.assoc, HomologicalComplex.ι_mapBifunctorMap]
        simp only [HomologicalComplex.id_f, curriedTensor_map_app, curriedTensor_obj_map,
          MonoidalCategory.id_whiskerRight]
        rw [HomologicalComplex.mapBifunctor₂₃.ι_eq
          (F := curriedTensor (ModuleCat R)) (G₂₃ := curriedTensor (ModuleCat R))
          L M K (ComplexShape.up ℤ) (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          q r p (p + r) n (by change r + p = p + r; omega)
            (by change q + (p + r) = n; omega)]
        erw [Category.id_comp]
        rw [← Category.assoc, ← whiskerLeft_comp, complexBraiding_ι]
        simp only [curriedTensor_obj_map, units_smul_whiskerLeft, whiskerLeft_comp,
          Linear.units_smul_comp, Category.assoc]
        rfl
      erw [Category.id_comp]
      simp only [← Category.assoc]
      rw [Category.assoc ((β_ (K.X p) (L.X q)).hom ▷ M.X r)
        (HomologicalComplex.ιTensorObj L K q p (p + q) (by omega) ▷ M.X r)
        (HomologicalComplex.ιTensorObj (L ⊗ K) M (p + q) r n hpqouter)]
      rw [ιTensorObj_whiskerRight_ιTensorObj L K M q p r (p + q) n (by omega) hpqouter hqpn]
      simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorAssociatorX_hom_assoc,
        CategoryTheory.MonoidalCategory.curriedAssociatorNatIso_hom_app_app_app,
        curriedTensor_obj_obj]
      dsimp only [bifunctorComp₂₃, bifunctorComp₂₃Obj, curriedTensor_obj_obj]
      simp only [complexBraiding] at hsecond
      rw [hsecond]
      have hsign : (p * (q + r)).negOnePow =
          (p * q).negOnePow * (p * r).negOnePow := by
        rw [← Int.negOnePow_add]
        congr 1
        ring
      rw [hsign]
      simp only [Linear.comp_units_smul, smul_smul]

/-- The Koszul braiding is a symmetry: braiding `K ⊗ L` to `L ⊗ K` and back is the identity. -/
lemma complexBraiding_symmetry
    (K L : CochainComplex (ModuleCat R) ℤ) :
    (complexBraiding K L).hom ≫ (complexBraiding L K).hom = 𝟙 (K ⊗ L) := by
  apply HomologicalComplex.Hom.ext
  funext n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q h
  simp only [curriedTensor_obj_obj, HomologicalComplex.comp_f, HomologicalComplex.id_f,
    complexBraiding, braidingX, HomologicalComplex.Hom.isoOfComponents_hom_f,
    HomologicalComplex.ι_mapBifunctorDesc_assoc, Linear.units_smul_comp, Category.assoc,
    HomologicalComplex.ι_mapBifunctorDesc, Linear.comp_units_smul,
    SymmetricCategory.symmetry_assoc]
  rw [smul_smul, ← Int.negOnePow_add]
  rw [show p * q + q * p = 2 * (p * q) by ring, Int.negOnePow_two_mul, one_smul]
  change HomologicalComplex.ιMapBifunctor K L (curriedTensor (ModuleCat R))
    (ComplexShape.up ℤ) p q _ h = _
  exact (Category.comp_id _).symm

/-- The Koszul braiding `K ⊗ L ≅ L ⊗ K` is the inverse of the Koszul braiding
`L ⊗ K ≅ K ⊗ L`. -/
lemma complexBraiding_swap (K L : CochainComplex (ModuleCat R) ℤ) :
    complexBraiding K L = (complexBraiding L K).symm :=
  Iso.ext ((complexBraiding L K).hom_comp_eq_id.mp (complexBraiding_symmetry L K))

private lemma complexBraiding_symm (K L : CochainComplex (ModuleCat R) ℤ) :
    (complexBraiding K L).symm = complexBraiding L K := by
  simpa using congrArg Iso.symm (complexBraiding_swap K L)

-- Deducing the reverse hexagon from the forward one transports an equality of isomorphisms
-- through `Iso.symm`, whose elaboration inherits the cost of the forward hexagon.
private lemma complexBraiding_hexagon_reverse
    (K L M : CochainComplex (ModuleCat R) ℤ) :
    (α_ K L M).inv ≫ (complexBraiding (K ⊗ L) M).hom ≫ (α_ M K L).inv =
      K ◁ (complexBraiding L M).hom ≫ (α_ K M L).inv ≫
        (complexBraiding K M).hom ▷ L := by
  have hf :
      (α_ M K L) ≪≫ complexBraiding M (K ⊗ L) ≪≫ (α_ K L M) =
        whiskerRightIso (complexBraiding M K) L ≪≫ (α_ K M L) ≪≫
          whiskerLeftIso K (complexBraiding M L) :=
    Iso.ext (complexBraiding_hexagon_forward M K L)
  have hr :
      (α_ K L M).symm ≪≫ complexBraiding (K ⊗ L) M ≪≫ (α_ M K L).symm =
        whiskerLeftIso K (complexBraiding L M) ≪≫ (α_ K M L).symm ≪≫
          whiskerRightIso (complexBraiding K M) L := by
    simpa only [Iso.trans_assoc, Iso.trans_symm, complexBraiding_symm, whiskerLeftIso_symm,
      whiskerRightIso_symm] using congrArg Iso.symm hf
  change ((α_ K L M).symm ≪≫ complexBraiding (K ⊗ L) M ≪≫
    (α_ M K L).symm).hom = _
  exact congrArg Iso.hom hr

/-! ## The symmetric monoidal structure -/

/-- The Koszul symmetric monoidal structure on `CochainComplex (ModuleCat R) ℤ`.

The monoidal structure itself is the existing one, whose tensor product is the total complex of
the degreewise tensor product; this adds the commutativity constraint, which on the summand of
bidegree `(p, q)` is the symmetry of `ModuleCat R` scaled by the Koszul sign `(-1)^(p*q)`.

This is deliberately not an instance: see the module documentation. -/
@[no_expose, instance_reducible]
noncomputable def koszulSymmetric (R : Type u) [CommRing R] :
    SymmetricCategory (CochainComplex (ModuleCat R) ℤ) where
  braiding := complexBraiding
  braiding_naturality_left := complexBraiding_naturality_left
  braiding_naturality_right := complexBraiding_naturality_right
  hexagon_forward := complexBraiding_hexagon_forward
  hexagon_reverse := complexBraiding_hexagon_reverse
  symmetry := complexBraiding_symmetry

/-- The braiding of `koszulSymmetric` on homogeneous summands: restricted to the summand
`K^p ⊗ L^q` of `Tot^n(K ⊗ L)`, it is the symmetry `K^p ⊗ L^q ≅ L^q ⊗ K^p` of `R`-modules,
multiplied by the Koszul sign `(-1)^(p*q)` and followed by the inclusion of the summand
`L^q ⊗ K^p` of `Tot^n(L ⊗ K)`. Since the summands generate, this determines the braiding. -/
theorem koszulSymmetric_braiding_ιTensorObj
    (R : Type u) [CommRing R] (K L : CochainComplex (ModuleCat R) ℤ) (p q n : ℤ)
    (h : p + q = n) :
    HomologicalComplex.ιTensorObj K L p q n h ≫
        ((koszulSymmetric R).toBraidedCategory.braiding K L).hom.f n =
      ((p * q).negOnePow : ℤˣ) •
        ((β_ (K.X p) (L.X q)).hom ≫
          HomologicalComplex.ιTensorObj L K q p n (by simpa [add_comm] using h)) :=
  complexBraiding_ι K L p q n h

end CochainComplex.Koszul
