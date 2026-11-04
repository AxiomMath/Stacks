module

public import StacksFrontier.Algebra.Homology.KFlat

@[expose] public section

-- needed below: the cofan index `⟨(q, pp), h⟩` identifies `q + pp = i` with
-- `(q, pp) ∈ p ⁻¹' {i}`, a defeq the default transparency setting rejects
set_option backward.isDefEq.respectTransparency false

/-!
# Base change of K-flat complexes

This formalizes Stacks Project Lemma 15.60.3 (tag 06Y1), in the section
"Derived tensor product" (Section 15.60, tag 06XY).

Throughout, `R` denotes a commutative ring, complexes are cochain complexes of
`R`-modules indexed by the integers (with differentials raising degree by one),
and the tensor product is the tensor product of `R`-modules.

## Main Definitions

- An *acyclic* complex `M` is one all of whose cohomology modules vanish, i.e.
  `H^n(M) = ker(d^n) / im(d^{n-1}) = 0` for every integer `n`.

- The *total complex* `Tot(M ⊗_R K)` of a tensor product of two complexes is the
  complex whose degree-`n` term is `⨁_{p+q=n} M^p ⊗_R K^q`, with the standard
  Koszul-sign differential `d(x ⊗ y) = d_M(x) ⊗ y + (-1)^p x ⊗ d_K(y)`.

- A complex `K` of `R`-modules is *K-flat* (Stacks Definition 15.60.1, tag 06XZ)
  if for every acyclic complex `M` of `R`-modules the total complex `Tot(M ⊗_R K)`
  is acyclic.

- *Base change* of a complex `K` along a ring map `φ : R → R'` is the complex
  `K ⊗_R R'` of `R'`-modules with terms `K^n ⊗_R R'` and differentials
  `d ⊗ id_{R'}`, where `R'` is an `R`-module via `φ`.

## Main Statement

If `φ : R → R'` is a ring map and `K` is a K-flat complex of `R`-modules, then
`K ⊗_R R'` is a K-flat complex of `R'`-modules.
-/

open CategoryTheory MonoidalCategory

open scoped TensorProduct

universe u

/-!
## Implementation notes: the formalization choices

We model complexes of `R`-modules as `CochainComplex (ModuleCat R) ℤ`, i.e.
`HomologicalComplex (ModuleCat R) (ComplexShape.up ℤ)`. This category carries a
`MonoidalCategory` instance whose tensor product `K ⊗ L` is *exactly* the total
complex of the tensor product double complex `⨁_{p+q=n} K^p ⊗_R L^q` with the
standard Koszul sign convention. Hence the Mathlib monoidal product `M ⊗ K`
realizes `Tot(M ⊗_R K)` of Definition 2.

`HomologicalComplex.Acyclic K` is defined as `∀ i, K.ExactAt i`, where `ExactAt`
says the short complex around degree `i` is exact; this is exactly the vanishing
of all cohomology, i.e. Definition 1.

Base change of complexes is the functor obtained by applying the (strong
monoidal) extension-of-scalars functor `ModuleCat.extendScalars φ`, which sends
an `R`-module `M` to `R' ⊗_R M`, degreewise to a complex via
`Functor.mapHomologicalComplex`.
-/

variable {R R' : Type u} [CommRing R] [CommRing R']

/-! ### Proof ingredients

The proof of `kFlat_baseChange` follows the Stacks Project. For an acyclic complex `L` of
`R'`-modules we use:

* **(C) `HomologicalComplex.Acyclic.of_iso`** — acyclicity transports along an
  isomorphism of cochain complexes.

* **(B) `CochainComplex.restrictScalars_acyclic_iff`** — restriction of scalars
  along `φ` neither creates nor destroys acyclicity, because `restrictScalars φ`
  is the identity on underlying abelian groups and on the differentials.

* **(A) `baseChangeTensorIso`** — the natural isomorphism (*) of the Stacks
  proof, transported to the level of `R`-complexes:

      (restrict φ) (L ⊗_{R'} (K ⊗_R R'))  ≅  (restrict φ) L ⊗_R K.

  This is the total complex of the degreewise base-change isomorphism
  `(L^q ⊗_{R'} (K^p ⊗_R R')) ≅ (L^q ⊗_R K^p)`, i.e. the projection / change-of-
  rings formula `(R' ⊗_R K^p) ⊗_{R'} L^q ≅ K^p ⊗_R L^q`, which is the engine
  provided by strong monoidality of `ModuleCat.extendScalars φ`.

Ingredients (B) and (C), together with the change-of-rings functors
`CochainComplex.extendScalars` (base change `K ↦ K ⊗_R R'`) and
`CochainComplex.restrictScalars`, and the predicate `CochainComplex.KFlat`
itself, are supplied by `StacksFrontier.Algebra.Homology.KFlat`. Only ingredient (A)
is built here, and with it the proof is the four-line wiring in
`kFlat_baseChange`. -/

/-! ### Ingredient A: the natural isomorphism (*)

For any complex `L` of `R'`-modules and complex `K` of `R`-modules there is a
natural isomorphism of cochain complexes of `R`-modules

    (restrict φ) (L ⊗_{R'} (K ⊗_R R'))  ≅  (restrict φ) L ⊗_R K.

This is the formalization of the Stacks isomorphism
`(K ⊗_R R') ⊗_{R'} L ≅ K ⊗_R L`, read after
restriction of scalars so that both sides are `R`-complexes (which is what the
final transport step needs).

Ingredient A is decomposed below into three sub-ingredients A1, A2, A3; the iso
`baseChangeTensorIso` is then assembled from them via `Hom.isoOfComponents`.
Degreewise this is the base-change / projection-formula isomorphism
`(L^q ⊗_{R'} (K^p ⊗_R R')) ≅ (L^q ⊗_R K^p)` of `R`-modules, equivalently
`(R' ⊗_R K^p) ⊗_{R'} L^q ≅ K^p ⊗_R L^q`. The engine is the strong-monoidal
structure on `ModuleCat.extendScalars φ` (`instMonoidalExtendScalars`), together
with the extension/restriction adjunction. -/

/-- **Sub-ingredient A1.** The degreewise projection-formula / change-of-rings
isomorphism of `R`-modules `ρ(V ⊗_{R'} (R' ⊗_R W)) ≅ ρ(V) ⊗_R W`, where
`ρ = restrictScalars φ` and `R' ⊗_R W = extendScalars φ W`. On pure tensors it
sends `v ⊗ (r' ⊗ w)` to `(r' • v) ⊗ w`. -/
noncomputable def projectionFormulaIso (φ : R →+* R') (V : ModuleCat R') (W : ModuleCat R) :
    (ModuleCat.restrictScalars φ).obj (V ⊗ (ModuleCat.extendScalars φ).obj W)
      ≅ (ModuleCat.restrictScalars φ).obj V ⊗ W :=
  letI : Algebra R R' := φ.toAlgebra
  letI : Module R V := ((ModuleCat.restrictScalars φ).obj V).isModule
  letI : IsScalarTower R R' V := .of_algebraMap_smul fun _ _ => rfl
  LinearEquiv.toModuleIso
    ((TensorProduct.AlgebraTensorModule.cancelBaseChange R R' R' V W).restrictScalars R)

open CategoryTheory.GradedObject CategoryTheory.Limits in
/-- **Sub-ingredient A2** (degreewise assembly). The isomorphism of degree-`n`
objects underlying `baseChangeTensorIso`. The degree-`n` term of a tensor of
cochain complexes is the direct sum `⨁_{q+p=n} L^q ⊗ (βK)^p`; this iso is the
direct sum over `q+p=n` of `projectionFormulaIso φ (L.X q) (K.X p)`. -/
noncomputable def baseChangeTensorIsoX (φ : R →+* R')
    (K : CochainComplex (ModuleCat R) ℤ) (L : CochainComplex (ModuleCat R') ℤ) (n : ℤ) :
    ((CochainComplex.restrictScalars φ).obj (L ⊗ (CochainComplex.extendScalars φ).obj K)).X n
      ≅ ((CochainComplex.restrictScalars φ).obj L ⊗ K).X n := by
  let p : ℤ × ℤ → ℤ := fun ⟨i, j⟩ => i + j
  let Z := ((mapBifunctor (curriedTensor (ModuleCat R')) ℤ ℤ).obj L.X).obj
      ((CochainComplex.extendScalars φ).obj K).X
  have hcolim := isColimitOfPreserves (ModuleCat.restrictScalars φ) (Z.isColimitCofanMapObj p n)
  let inv : (((CochainComplex.restrictScalars φ).obj L ⊗ K).X n) ⟶
      (((CochainComplex.restrictScalars φ).obj (L ⊗ (CochainComplex.extendScalars φ).obj K)).X n) :=
    GradedObject.Monoidal.tensorObjDesc (fun q pp h =>
      (projectionFormulaIso φ (L.X q) (K.X pp)).inv ≫
        (ModuleCat.restrictScalars φ).map
          (HomologicalComplex.ιTensorObj L ((CochainComplex.extendScalars φ).obj K) q pp n h))
  let leg : (i : ↑(p ⁻¹' {n})) →
      ((ModuleCat.restrictScalars φ).obj (Z.mapObjFun p n i)) ⟶
        (((CochainComplex.restrictScalars φ).obj L ⊗ K).X n) :=
    fun ⟨⟨q, pp⟩, (h : q + pp = n)⟩ =>
      (projectionFormulaIso φ (L.X q) (K.X pp)).hom ≫
        HomologicalComplex.ιTensorObj ((CochainComplex.restrictScalars φ).obj L) K q pp n h
  let tgt : Cocone (Discrete.functor (Z.mapObjFun p n) ⋙ ModuleCat.restrictScalars φ) :=
    { pt := ((CochainComplex.restrictScalars φ).obj L ⊗ K).X n
      ι := Discrete.natTrans (fun ⟨i⟩ => leg i) }
  let hom := hcolim.desc tgt
  have fac : ∀ (q pp : ℤ) (h : q + pp = n),
      (ModuleCat.restrictScalars φ).map
        (HomologicalComplex.ιTensorObj L ((CochainComplex.extendScalars φ).obj K) q pp n h) ≫ hom
      = (projectionFormulaIso φ (L.X q) (K.X pp)).hom ≫
        HomologicalComplex.ιTensorObj ((CochainComplex.restrictScalars φ).obj L) K q pp n h :=
    fun q pp h => hcolim.fac tgt ⟨⟨(q, pp), h⟩⟩
  have hinv : ∀ (q pp : ℤ) (h : q + pp = n),
      HomologicalComplex.ιTensorObj ((CochainComplex.restrictScalars φ).obj L) K q pp n h ≫ inv
      = (projectionFormulaIso φ (L.X q) (K.X pp)).inv ≫
        (ModuleCat.restrictScalars φ).map
          (HomologicalComplex.ιTensorObj L ((CochainComplex.extendScalars φ).obj K) q pp n h) :=
    fun q pp h => GradedObject.Monoidal.ι_tensorObjDesc _ q pp h
  refine ⟨hom, inv, ?_, ?_⟩
  · apply hcolim.hom_ext
    rintro ⟨⟨q, pp⟩, (h : q + pp = n)⟩
    change (ModuleCat.restrictScalars φ).map
        (HomologicalComplex.ιTensorObj L ((CochainComplex.extendScalars φ).obj K) q pp n h)
        ≫ hom ≫ inv = _
    rw [reassoc_of% fac q pp h, hinv q pp h, Iso.hom_inv_id_assoc]
    exact (Category.comp_id _).symm
  · refine GradedObject.Monoidal.tensorObj_ext _ _ fun q pp h => ?_
    change HomologicalComplex.ιTensorObj ((CochainComplex.restrictScalars φ).obj L) K q pp n h
        ≫ inv ≫ hom = _
    rw [reassoc_of% hinv q pp h, fac q pp h, Iso.inv_hom_id_assoc]
    exact (Category.comp_id _).symm

/-- The characterizing factorization of `baseChangeTensorIsoX`'s `inv`: on the right-hand
summand inclusion at bidegree `(q,pp)` it is the inverse projection-formula iso followed by the
restricted summand inclusion on the left-hand side. -/
theorem baseChangeTensorIsoX_inv_ι (φ : R →+* R')
    (K : CochainComplex (ModuleCat R) ℤ) (L : CochainComplex (ModuleCat R') ℤ) (n : ℤ)
    (q pp : ℤ) (h : q + pp = n) :
    HomologicalComplex.ιTensorObj ((CochainComplex.restrictScalars φ).obj L) K q pp n h
      ≫ (baseChangeTensorIsoX φ K L n).inv
      = (projectionFormulaIso φ (L.X q) (K.X pp)).inv ≫
        (ModuleCat.restrictScalars φ).map
          (HomologicalComplex.ιTensorObj L ((CochainComplex.extendScalars φ).obj K) q pp n h) :=
  GradedObject.Monoidal.ι_tensorObjDesc (fun q pp h =>
      (projectionFormulaIso φ (L.X q) (K.X pp)).inv ≫
        (ModuleCat.restrictScalars φ).map
          (HomologicalComplex.ιTensorObj L ((CochainComplex.extendScalars φ).obj K) q pp n h))
    q pp h

/-- The characterizing factorization of `baseChangeTensorIsoX`'s `hom`: it sends the
restricted summand inclusion at bidegree `(q,pp)` to the projection-formula iso followed by
the corresponding summand inclusion on the right-hand side. -/
theorem baseChangeTensorIsoX_hom_ι (φ : R →+* R')
    (K : CochainComplex (ModuleCat R) ℤ) (L : CochainComplex (ModuleCat R') ℤ) (n : ℤ)
    (q pp : ℤ) (h : q + pp = n) :
    (ModuleCat.restrictScalars φ).map
        (HomologicalComplex.ιTensorObj L ((CochainComplex.extendScalars φ).obj K) q pp n h)
      ≫ (baseChangeTensorIsoX φ K L n).hom
      = (projectionFormulaIso φ (L.X q) (K.X pp)).hom ≫
        HomologicalComplex.ιTensorObj ((CochainComplex.restrictScalars φ).obj L) K q pp n h := by
  rw [← Iso.eq_comp_inv, Category.assoc, baseChangeTensorIsoX_inv_ι, Iso.hom_inv_id_assoc]

/-- The action of `(projectionFormulaIso φ V W).hom` on a pure tensor `v ⊗ (r' ⊗ w)`:
it sends it to `(r' • v) ⊗ w`, matching the informal description of the projection formula. -/
theorem projectionFormulaIso_hom_tmul (φ : R →+* R') (V : ModuleCat R') (W : ModuleCat R)
    (v : V) (r' : R') (w : W) :
    (ModuleCat.Hom.hom (projectionFormulaIso φ V W).hom)
        (v ⊗ₜ[R'] ((r' : ((ModuleCat.restrictScalars φ).obj (ModuleCat.of R' R'))) ⊗ₜ[R] w))
      = (letI : Module R V := ((ModuleCat.restrictScalars φ).obj V).isModule; (r' • v) ⊗ₜ[R] w) :=
  rfl

/-- **Naturality of `projectionFormulaIso` in `V`** (the `L`-direction). For an `R'`-linear
map `f : V ⟶ V'`, the projection-formula iso intertwines `restrict (f ▷ EW)` and `(restrict f) ▷
W`. -/
theorem projectionFormulaIso_natural_left (φ : R →+* R') {V V' : ModuleCat R'} (W : ModuleCat R)
    (f : V ⟶ V') :
    (ModuleCat.restrictScalars φ).map (f ▷ (ModuleCat.extendScalars φ).obj W)
        ≫ (projectionFormulaIso φ V' W).hom
      = (projectionFormulaIso φ V W).hom ≫ ((ModuleCat.restrictScalars φ).map f ▷ W) := by
  apply ModuleCat.hom_ext
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    | tmul r' w =>
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.restrictScalars.map_apply, ModuleCat.MonoidalCategory.whiskerRight_apply,
        projectionFormulaIso_hom_tmul, projectionFormulaIso_hom_tmul,
        ModuleCat.MonoidalCategory.whiskerRight_apply, ModuleCat.restrictScalars.map_apply,
        map_smul]

/-- **Naturality of `projectionFormulaIso` in `W`** (the `K`-direction). For an `R`-linear
map `g : W ⟶ W'`, the projection-formula iso intertwines `restrict (V ◁ E g)` and `(restrict V) ◁
g`. -/
theorem projectionFormulaIso_natural_right (φ : R →+* R') (V : ModuleCat R') {W W' : ModuleCat R}
    (g : W ⟶ W') :
    (ModuleCat.restrictScalars φ).map (V ◁ (ModuleCat.extendScalars φ).map g)
        ≫ (projectionFormulaIso φ V W').hom
      = (projectionFormulaIso φ V W).hom ≫ ((ModuleCat.restrictScalars φ).obj V ◁ g) := by
  let : Algebra R R' := φ.toAlgebra
  apply ModuleCat.hom_ext
  ext x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul v y =>
    induction y using TensorProduct.induction_on with
    | zero => simp
    | add a b ha hb => simp only [TensorProduct.tmul_add, map_add, ha, hb]
    | tmul r' w =>
      rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_comp, LinearMap.comp_apply,
        ModuleCat.restrictScalars.map_apply, ModuleCat.MonoidalCategory.whiskerLeft_apply]
      have hg : (ModuleCat.Hom.hom ((ModuleCat.extendScalars φ).map g))
          (r' ⊗ₜ[R] w : (ModuleCat.extendScalars φ).obj W) = r' ⊗ₜ[R] (g w) := rfl
      rw [hg, projectionFormulaIso_hom_tmul, projectionFormulaIso_hom_tmul,
        ModuleCat.MonoidalCategory.whiskerLeft_apply]

/-- Decomposition of `ιTensorObj ≫ d` on a tensor of homological complexes into the two
summand differentials `d₁ + d₂`. -/
theorem HomologicalComplex.ι_tensorObj_d {C : Type*} [Category C] [MonoidalCategory C]
    [Preadditive C] [Limits.HasZeroObject C] [(curriedTensor C).Additive]
    [∀ (X₁ : C), ((curriedTensor C).obj X₁).Additive]
    {I : Type*} [AddMonoid I] [DecidableEq I] {c : ComplexShape I} [c.TensorSigns]
    [∀ (X₁ X₂ : GradedObject I C), GradedObject.HasTensor X₁ X₂]
    [∀ (X₁ : C), Limits.PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).obj X₁)]
    [∀ (X₂ : C), Limits.PreservesColimit (Functor.empty.{0} C) ((curriedTensor C).flip.obj X₂)]
    [∀ (X₁ X₂ X₃ X₄ : GradedObject I C), GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
    [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
    [∀ (X₁ X₂ X₃ : GradedObject I C), GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]
    (A B : HomologicalComplex C c) (q pp i j : I) (h : q + pp = i) :
    HomologicalComplex.ιTensorObj A B q pp i h ≫ (A ⊗ B).d i j
      = HomologicalComplex.mapBifunctor.d₁ A B (curriedTensor C) c q pp j
        + HomologicalComplex.mapBifunctor.d₂ A B (curriedTensor C) c q pp j := by
  rw [show (A ⊗ B).d i j = HomologicalComplex.mapBifunctor.D₁ A B (curriedTensor C) c i j
      + HomologicalComplex.mapBifunctor.D₂ A B (curriedTensor C) c i j from
      HomologicalComplex.mapBifunctor.d_eq _ _ _ _ _ _,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]

/-- **Sub-ingredient A3** (differential compatibility / chain-map condition).
The degreewise isos `baseChangeTensorIsoX` commute with the (Koszul-signed)
total differentials, so they assemble (via `Hom.isoOfComponents`) into an iso of
cochain complexes. On the bidegree-`(q,p)` summand both sides carry the same
Koszul sign `(-1)^q`; the `L`-direction square is naturality of
`projectionFormulaIso` in `V`, the `K`-direction naturality in `W`. -/
theorem baseChangeTensorIsoX_comm (φ : R →+* R')
    (K : CochainComplex (ModuleCat R) ℤ) (L : CochainComplex (ModuleCat R') ℤ)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (baseChangeTensorIsoX φ K L i).hom ≫ ((CochainComplex.restrictScalars φ).obj L ⊗ K).d i j
      = ((CochainComplex.restrictScalars φ).obj (L ⊗ (CochainComplex.extendScalars φ).obj K)).d i j
        ≫ (baseChangeTensorIsoX φ K L j).hom := by
  let p : ℤ × ℤ → ℤ := fun ⟨i, j⟩ => i + j
  let Z := ((CategoryTheory.GradedObject.mapBifunctor (curriedTensor (ModuleCat R')) ℤ ℤ).obj
      L.X).obj
      ((CochainComplex.extendScalars φ).obj K).X
  have hcolim := CategoryTheory.Limits.isColimitOfPreserves (ModuleCat.restrictScalars φ)
    (Z.isColimitCofanMapObj p i)
  apply hcolim.hom_ext
  rintro ⟨⟨q, pp⟩, (h : q + pp = i)⟩
  have hleg : ((ModuleCat.restrictScalars φ).mapCocone (Z.cofanMapObj p i)).ι.app ⟨⟨(q, pp), h⟩⟩
      = (ModuleCat.restrictScalars φ).map
        (HomologicalComplex.ιTensorObj L ((CochainComplex.extendScalars φ).obj K) q pp i h) := rfl
  rw [hleg, reassoc_of% baseChangeTensorIsoX_hom_ι φ K L i q pp h,
    HomologicalComplex.ι_tensorObj_d ((CochainComplex.restrictScalars φ).obj L) K q pp i j h]
  -- Handle the RHS: pull `restrictScalars φ` through and decompose the L-side differential.
  have hdLHS : ((CochainComplex.restrictScalars φ).obj
    (L ⊗ (CochainComplex.extendScalars φ).obj K)).d i j
      = (ModuleCat.restrictScalars φ).map
        ((L ⊗ (CochainComplex.extendScalars φ).obj K).d i j) := rfl
  rw [hdLHS, ← Functor.map_comp_assoc,
    HomologicalComplex.ι_tensorObj_d L ((CochainComplex.extendScalars φ).obj K) q pp i j h,
    Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]
  have hij' : i + 1 = j := hij
  have hq' : (ComplexShape.up ℤ).Rel q (q + 1) := by simp [ComplexShape.up_Rel]
  have hpp' : (ComplexShape.up ℤ).Rel pp (pp + 1) := by simp [ComplexShape.up_Rel]
  have hd1L : (q + 1) + pp = j := by omega
  have hd2K : q + (pp + 1) = j := by omega
  congr 1
  · -- L-direction (d₁): naturality in V with f = d_L^q
    rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hq' pp j hd1L,
      HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ hq' pp j hd1L,
      Linear.comp_units_smul, Functor.map_units_smul, Linear.units_smul_comp]
    congr 1
    rw [Functor.map_comp, Category.assoc, baseChangeTensorIsoX_hom_ι φ K L j (q + 1) pp hd1L,
      ← Category.assoc, ← Category.assoc]
    congr 1
    exact (projectionFormulaIso_natural_left φ (K.X pp) (L.d q (q + 1))).symm
  · -- K-direction (d₂): naturality in W with g = d_K^p
    rw [HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ q hpp' j hd2K,
      HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ q hpp' j hd2K,
      Linear.comp_units_smul, Functor.map_units_smul, Linear.units_smul_comp]
    congr 1
    rw [Functor.map_comp, Category.assoc, baseChangeTensorIsoX_hom_ι φ K L j q (pp + 1) hd2K,
      ← Category.assoc, ← Category.assoc]
    congr 1
    exact (projectionFormulaIso_natural_right φ (L.X q) (K.d pp (pp + 1))).symm

/-- **Ingredient A.** The natural isomorphism of cochain complexes of `R`-modules
`(restrict φ) (L ⊗_{R'} (K ⊗_R R')) ≅ (restrict φ) L ⊗_R K`, assembled from the
degreewise projection-formula isomorphisms `baseChangeTensorIsoX` and their
compatibility with the total differentials, `baseChangeTensorIsoX_comm`. -/
noncomputable def baseChangeTensorIso (φ : R →+* R')
    (K : CochainComplex (ModuleCat R) ℤ) (L : CochainComplex (ModuleCat R') ℤ) :
    ((CochainComplex.restrictScalars φ).obj (L ⊗ (CochainComplex.extendScalars φ).obj K))
      ≅ ((CochainComplex.restrictScalars φ).obj L ⊗ K) :=
  HomologicalComplex.Hom.isoOfComponents (baseChangeTensorIsoX φ K L)
    (baseChangeTensorIsoX_comm φ K L)

/-! ### Main statement -/

/-- **Stacks Lemma 15.60.3 (tag 06Y1), for two rings in one universe.**
Let `φ : R → R'` be a ring map. If `K` is a K-flat complex of `R`-modules, then
`K ⊗_R R'` is a K-flat complex of `R'`-modules.

The tag itself sits on `CochainComplex.KFlat.ScalarBaseChange.kFlat_extendScalars` in
`StacksFrontier.Homology.KFlat.ScalarBaseChange`, which states the same lemma with the two rings
in independent universes, as the source has them — here `R` and `R'` are both forced into a
single `Type u`, which the source does not ask for. This declaration is that statement's
specialization to a common universe, kept because `StacksFrontier.Homology.Tor.FlatBaseChangeHomology`
consumes it in that form.

Explicitly: for every acyclic complex `L` of `R'`-modules, the total complex
`Tot(L ⊗_{R'} (K ⊗_R R'))` is acyclic.

Proof (wiring of ingredients A, B, C): let `L` be acyclic over `R'`.
1. By (B), the restriction `(restrict φ) L` is acyclic over `R`.
2. By K-flatness of `K` over `R`, `(restrict φ) L ⊗_R K` is acyclic.
3. By (A) and (C), transporting along the iso (*) gives that
   `(restrict φ) (L ⊗_{R'} (K ⊗_R R'))` is acyclic.
4. By (B) again (reflecting direction), `L ⊗_{R'} (K ⊗_R R')` is acyclic. -/
theorem kFlat_baseChange (φ : R →+* R') (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : K.KFlat) : ((CochainComplex.extendScalars φ).obj K).KFlat := by
  intro L hL
  -- (B): the restriction of `L` to an `R`-complex is acyclic.
  have hLR : ((CochainComplex.restrictScalars φ).obj L).Acyclic :=
    (CochainComplex.restrictScalars_acyclic_iff φ L).mpr hL
  -- K-flatness of `K` over `R`, applied to the restricted complex.
  have hac : (((CochainComplex.restrictScalars φ).obj L) ⊗ K).Acyclic := hK _ hLR
  -- (A) + (C): transport across the natural iso (*) to the restricted total complex.
  have hrestr : ((CochainComplex.restrictScalars φ).obj
      (L ⊗ (CochainComplex.extendScalars φ).obj K)).Acyclic :=
    HomologicalComplex.Acyclic.of_iso (baseChangeTensorIso φ K L).symm hac
  -- (B) again: restriction reflects acyclicity, so the `R'`-total complex is acyclic.
  exact (CochainComplex.restrictScalars_acyclic_iff φ
    (L ⊗ (CochainComplex.extendScalars φ).obj K)).mp hrestr
