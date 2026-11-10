module

public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.HomComplex.Currying
public import Mathlib.Algebra.Homology.Embedding.StupidTrunc

/-!
# Tensoring with a bounded-below complex of flat modules

Let `R` be a commutative ring. A bounded *above* complex of flat `R`-modules is K-flat
([stacks 064K]), so tensoring with it preserves every quasi-isomorphism. For a bounded *below*
complex `X` of flat modules this fails in general, but it survives for quasi-isomorphisms between
bounded-below complexes: in a fixed degree `n`, the total complex `X ⊗ Y` of a complex `Y`
concentrated in degrees `≥ b` only sees the terms `X^i` with `i ≤ n + 1 - b`, so `X` may be
replaced by its stupid truncation `σ^{≤ n + 1 - b} X`, which is bounded with flat terms.

This is the one homological input of the comparison of two relative dualizing complexes
([stacks 0E2D]) carried out in `StacksFrontier.RingTheory.Dualizing.RelativeUniquenessTensorForm`,
and the second half of this file is the purely monoidal core of that comparison.

## Main results

* `Dualizing.FlatTensor.quasiIso_whiskerLeft_of_flat` — for `X` bounded below with flat terms
  and `f` a quasi-isomorphism between bounded-below complexes, `X ◁ f` is a quasi-isomorphism.
* `Dualizing.FlatTensor.quasiIso_core` — the monoidal core: given quasi-isomorphisms
  `ι : 𝟙 ⟶ D'` and `ι' : 𝟙 ⟶ D ⊗ P` with `D'` having flat terms and `D ⊗ P` bounded below,
  the map `D ◁ (λ⁻¹ ≫ ι ▷ P) : D ⊗ P ⟶ D ⊗ (D' ⊗ P)` is a quasi-isomorphism.
-/

@[expose] public section

open CategoryTheory MonoidalCategory Limits

universe u

namespace Dualizing.FlatTensor

variable {R : Type u} [CommRing R]

/-- The termwise map from a complex to its stupid truncation `σ^{≤ m}`: the identity in degrees
`≤ m` and zero above. -/
noncomputable def truncProjf (X : CochainComplex (ModuleCat.{u} R) ℤ) (m j : ℤ) :
    X.X j ⟶ (X.stupidTrunc (ComplexShape.embeddingUpIntLE m)).X j :=
  if h : j ≤ m then
    (X.stupidTruncXIso (ComplexShape.embeddingUpIntLE m) (i := (m - j).toNat)
      (by simp only [ComplexShape.embeddingUpIntLE_f]; omega)).inv
  else 0

/-- In degrees `j ≤ m`, `truncProjf X m j` is the inverse of the identification of the degree-`j`
term of `σ^{≤ m} X` with `X^j`. -/
lemma truncProjf_of_le (X : CochainComplex (ModuleCat.{u} R) ℤ) (m j : ℤ) (h : j ≤ m) :
    truncProjf X m j = (X.stupidTruncXIso (ComplexShape.embeddingUpIntLE m)
      (i := (m - j).toNat) (by simp only [ComplexShape.embeddingUpIntLE_f]; omega)).inv := by
  simp [truncProjf, h]

/-- The stupid truncation `σ^{≤ m} X` is zero in every degree `j > m`. -/
lemma isZero_stupidTrunc_X_of_lt (X : CochainComplex (ModuleCat.{u} R) ℤ) (m j : ℤ)
    (h : m < j) : IsZero ((X.stupidTrunc (ComplexShape.embeddingUpIntLE m)).X j) :=
  X.isZero_stupidTrunc_X _ j (by
    intro i
    simp only [ComplexShape.embeddingUpIntLE_f]
    omega)

/-- In degrees within range, the differential of the stupid truncation `σ^{≤ m} X` is the
differential of `X`, conjugated by the identifications of the terms of `σ^{≤ m} X` with those of
`X`. -/
lemma stupidTrunc_d_eq' (X : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    {i j : ℕ} {i' j' : ℤ} (hi : (ComplexShape.embeddingUpIntLE m).f i = i')
    (hj : (ComplexShape.embeddingUpIntLE m).f j = j') :
    (X.stupidTrunc (ComplexShape.embeddingUpIntLE m)).d i' j' =
      (X.stupidTruncXIso _ hi).hom ≫ X.d i' j' ≫ (X.stupidTruncXIso _ hj).inv := by
  subst hi hj
  have h₁ : ∀ {Z : ModuleCat.{u} R}
      (h : (X.restriction (ComplexShape.embeddingUpIntLE m)).X i =
        X.X ((ComplexShape.embeddingUpIntLE m).f i))
      (g : X.X ((ComplexShape.embeddingUpIntLE m).f i) ⟶ Z),
      eqToHom h ≫ g = g := fun _ g => Category.id_comp g
  have h₂ : ∀ {Z : ModuleCat.{u} R}
      (h : X.X ((ComplexShape.embeddingUpIntLE m).f j) =
        (X.restriction (ComplexShape.embeddingUpIntLE m)).X j)
      (g : (X.restriction (ComplexShape.embeddingUpIntLE m)).X j ⟶ Z), eqToHom h ≫ g = g :=
    fun _ g => Category.id_comp g
  simp [HomologicalComplex.stupidTrunc, HomologicalComplex.stupidTruncXIso,
    (X.restriction _).extend_d_eq _ rfl rfl, h₁, h₂]
  rfl

/-- The projection of a complex onto its stupid truncation `σ^{≤ m}`. -/
noncomputable def truncProj (X : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ) :
    X ⟶ X.stupidTrunc (ComplexShape.embeddingUpIntLE m) where
  f j := truncProjf X m j
  comm' i j hij := by
    change i + 1 = j at hij
    subst hij
    by_cases hi : i + 1 ≤ m
    · have hi' : i ≤ m := by omega
      rw [truncProjf_of_le X m i hi', truncProjf_of_le X m (i + 1) hi,
        stupidTrunc_d_eq' X m (i := (m - i).toNat) (j := (m - (i + 1)).toNat)
          (by simp only [ComplexShape.embeddingUpIntLE_f]; omega)
          (by simp only [ComplexShape.embeddingUpIntLE_f]; omega)]
      simp
    · exact (isZero_stupidTrunc_X_of_lt X m (i + 1) (by omega)).eq_of_tgt _ _

/-- The projection onto the stupid truncation `σ^{≤ m}` is an isomorphism in every degree
`j ≤ m`. -/
lemma isIso_truncProj_f (X : CochainComplex (ModuleCat.{u} R) ℤ) (m j : ℤ) (h : j ≤ m) :
    IsIso ((truncProj X m).f j) := by
  change IsIso (truncProjf X m j)
  rw [truncProjf_of_le X m j h]
  infer_instance

/-- The degree-`k` component of `π ▷ Y`, for `π` the projection onto `σ^{≤ m}` and `Y`
concentrated in degrees `≥ b`, is an isomorphism as soon as `k ≤ m + b`. -/
lemma isIso_truncProj_whiskerRight_f (X Y : CochainComplex (ModuleCat.{u} R) ℤ) (m b k : ℤ)
    [Y.IsStrictlyGE b] (hk : k ≤ m + b) :
    IsIso ((truncProj X m ▷ Y).f k) := by
  let Q := X.stupidTrunc (ComplexShape.embeddingUpIntLE m)
  let s : ∀ i : ℤ, Q.X i ⟶ X.X i := fun i =>
    if h : i ≤ m then (X.stupidTruncXIso (ComplexShape.embeddingUpIntLE m) (i := (m - i).toNat)
      (by simp only [ComplexShape.embeddingUpIntLE_f]; omega)).hom else 0
  have hs : ∀ i, i ≤ m → (truncProj X m).f i ≫ s i = 𝟙 _ := by
    intro i hi
    change truncProjf X m i ≫ s i = _
    simp [s, truncProjf_of_le X m i hi, hi]
  have hs' : ∀ i, i ≤ m → s i ≫ (truncProj X m).f i = 𝟙 _ := by
    intro i hi
    change s i ≫ truncProjf X m i = _
    simp [s, truncProjf_of_le X m i hi, hi]
  let g : (Q ⊗ Y).X k ⟶ (X ⊗ Y).X k :=
    HomologicalComplex.mapBifunctorDesc (fun i j (h : i + j = k) =>
      (s i ▷ Y.X j) ≫ HomologicalComplex.ιTensorObj X Y i j k h)
  have hg : ∀ i j (h : i + j = k), HomologicalComplex.ιTensorObj Q Y i j k h ≫ g =
      (s i ▷ Y.X j) ≫ HomologicalComplex.ιTensorObj X Y i j k h := by
    intro i j h
    exact HomologicalComplex.ι_mapBifunctorDesc _ _ _ _
  refine ⟨g, ?_, ?_⟩
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    change i + j = k at h
    change HomologicalComplex.ιTensorObj X Y i j k h ≫ _ ≫ g =
      HomologicalComplex.ιTensorObj X Y i j k h ≫ 𝟙 _
    rw [reassoc_of% (Stacks.HomComplex.Currying.ιTensorObj_comp_whiskerRight
      (truncProj X m) i j k h), hg, Category.comp_id]
    by_cases hi : i ≤ m
    · rw [← comp_whiskerRight_assoc, hs i hi, id_whiskerRight, Category.id_comp]
    · have hY : IsZero (Y.X j) := Y.isZero_of_isStrictlyGE b j (by omega)
      exact ((tensorLeft (X.X i)).map_isZero hY).eq_of_src _ _
  · apply HomologicalComplex.mapBifunctor.hom_ext
    intro i j h
    change i + j = k at h
    change HomologicalComplex.ιTensorObj Q Y i j k h ≫ g ≫ _ =
      HomologicalComplex.ιTensorObj Q Y i j k h ≫ 𝟙 _
    rw [reassoc_of% hg, Stacks.HomComplex.Currying.ιTensorObj_comp_whiskerRight
      (truncProj X m) i j k h, Category.comp_id]
    by_cases hi : i ≤ m
    · rw [← comp_whiskerRight_assoc, hs' i hi, id_whiskerRight, Category.id_comp]
    · have hQ : IsZero (Q.X i) := isZero_stupidTrunc_X_of_lt X m i (by omega)
      exact ((tensorRight (Y.X j)).map_isZero hQ).eq_of_src _ _

/-- A morphism of complexes whose components in degrees `n - 1`, `n`, `n + 1` are isomorphisms
induces an isomorphism on cohomology in degree `n`. -/
lemma isIso_homologyMap_of_isIso_f {X Y : CochainComplex (ModuleCat.{u} R) ℤ} (φ : X ⟶ Y)
    (n : ℤ) (h₁ : IsIso (φ.f (n - 1))) (h₂ : IsIso (φ.f n)) (h₃ : IsIso (φ.f (n + 1))) :
    IsIso (HomologicalComplex.homologyMap φ n) := by
  have h₁' : IsIso (φ.f ((ComplexShape.up ℤ).prev n)) := by
    rw [CochainComplex.prev]; exact h₁
  have h₃' : IsIso (φ.f ((ComplexShape.up ℤ).next n)) := by
    rw [CochainComplex.next]; exact h₃
  have : IsIso ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℤ) n).map φ) := by
    have : IsIso ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℤ) n).map φ).τ₁ := h₁'
    have : IsIso ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℤ) n).map φ).τ₂ := h₂
    have : IsIso ((HomologicalComplex.shortComplexFunctor (ModuleCat.{u} R)
      (ComplexShape.up ℤ) n).map φ).τ₃ := h₃'
    exact ShortComplex.isIso_of_isIso _
  change IsIso (ShortComplex.homologyMap _)
  infer_instance

/-- Every term of the stupid truncation `σ^{≤ m} X` of a complex `X` of flat modules is flat. -/
lemma flat_stupidTrunc_X (X : CochainComplex (ModuleCat.{u} R) ℤ) (m : ℤ)
    [∀ n, Module.Flat R (X.X n)] (j : ℤ) :
    Module.Flat R ((X.stupidTrunc (ComplexShape.embeddingUpIntLE m)).X j) := by
  by_cases h : j ≤ m
  · exact Module.Flat.of_linearEquiv (X.stupidTruncXIso (ComplexShape.embeddingUpIntLE m)
      (i := (m - j).toNat) (by simp only [ComplexShape.embeddingUpIntLE_f]; omega)).toLinearEquiv
  · have : Subsingleton ((X.stupidTrunc (ComplexShape.embeddingUpIntLE m)).X j) :=
      ModuleCat.subsingleton_of_isZero (isZero_stupidTrunc_X_of_lt X m j (by omega))
    infer_instance

/-- **Tensoring with a bounded-below complex of flat modules preserves quasi-isomorphisms
between bounded-below complexes.** -/
theorem quasiIso_whiskerLeft_of_flat (X : CochainComplex (ModuleCat.{u} R) ℤ)
    [∀ n, Module.Flat R (X.X n)] {Y₁ Y₂ : CochainComplex (ModuleCat.{u} R) ℤ} (b : ℤ)
    [Y₁.IsStrictlyGE b] [Y₂.IsStrictlyGE b] (f : Y₁ ⟶ Y₂) [QuasiIso f] :
    QuasiIso (X ◁ f) := by
  rw [quasiIso_iff]
  intro n
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let m := n + 1 - b
  let Q := X.stupidTrunc (ComplexShape.embeddingUpIntLE m)
  have : ∀ j, Module.Flat R (Q.X j) := flat_stupidTrunc_X X m
  have hQ : CochainComplex.KFlat Q := CochainComplex.KFlat.kFlat_of_flat.{u, u} Q m
  have hQf : QuasiIso (Q ◁ f) :=
    StacksDraft.TorAmplitude.quasiIso_tensorLeft_map Q hQ f
  have hsq : truncProj X m ▷ Y₁ ≫ Q ◁ f = X ◁ f ≫ truncProj X m ▷ Y₂ :=
    (whisker_exchange _ _).symm
  have key : ∀ (Y : CochainComplex (ModuleCat.{u} R) ℤ) [Y.IsStrictlyGE b],
      IsIso (HomologicalComplex.homologyMap (truncProj X m ▷ Y) n) := fun Y _ =>
    isIso_homologyMap_of_isIso_f _ n
      (isIso_truncProj_whiskerRight_f X Y m b _ (by omega))
      (isIso_truncProj_whiskerRight_f X Y m b _ (by omega))
      (isIso_truncProj_whiskerRight_f X Y m b _ (by omega))
  have h₁ := key Y₁
  have h₂ := key Y₂
  have h₃ : IsIso (HomologicalComplex.homologyMap (Q ◁ f) n) :=
    (quasiIsoAt_iff_isIso_homologyMap _ n).1 inferInstance
  have hc := congrArg (fun φ => HomologicalComplex.homologyMap φ n) hsq
  simp only [HomologicalComplex.homologyMap_comp] at hc
  have : IsIso (HomologicalComplex.homologyMap (X ◁ f) n ≫
      HomologicalComplex.homologyMap (truncProj X m ▷ Y₂) n) := by
    rw [← hc]; infer_instance
  exact IsIso.of_isIso_comp_right _ (HomologicalComplex.homologyMap (truncProj X m ▷ Y₂) n)

/-- The monoidal unit of complexes, `R` placed in degree zero, is concentrated in degrees `≥ b`
for every `b ≤ 0`. -/
lemma tensorUnit_isStrictlyGE (b : ℤ) (hb : b ≤ 0) :
    (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)).IsStrictlyGE b := by
  have : (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)).IsStrictlyGE 0 := by
    change CochainComplex.IsStrictlyGE ((HomologicalComplex.single (ModuleCat.{u} R)
      (ComplexShape.up ℤ) 0).obj (𝟙_ (ModuleCat.{u} R))) 0
    infer_instance
  exact CochainComplex.isStrictlyGE_of_ge _ b 0 hb

/-- **The monoidal core of the comparison of two relative dualizing complexes.**  Let `D`, `D'`,
`P` be complexes of `R`-modules, with `D'` having flat terms and `D ⊗ P` concentrated in degrees
`≥ b`. If `ι : 𝟙 ⟶ D'` and `ι' : 𝟙 ⟶ D ⊗ P` are quasi-isomorphisms, then so is
`D ◁ (λ⁻¹ ≫ ι ▷ P) : D ⊗ P ⟶ D ⊗ (D' ⊗ P)`.

Up to the symmetry exchanging `D` and `D'`, the map is `ι ▷ (D ⊗ P)`; and the interchange law
writes `ι ▷ (D ⊗ P)` after `𝟙 ◁ ι'` as `ι ▷ 𝟙` followed by `D' ◁ ι'`, where the last map is a
quasi-isomorphism by `Dualizing.FlatTensor.quasiIso_whiskerLeft_of_flat`. -/
theorem quasiIso_core (D D' P : CochainComplex (ModuleCat.{u} R) ℤ) [∀ n, Module.Flat R (D'.X n)]
    (b : ℤ) (hb : b ≤ 0) [(D ⊗ P).IsStrictlyGE b]
    (ι : 𝟙_ _ ⟶ D') (ι' : 𝟙_ _ ⟶ D ⊗ P) [QuasiIso ι] [QuasiIso ι'] :
    QuasiIso (D ◁ ((λ_ P).inv ≫ ι ▷ P)) := by
  let := CochainComplex.Koszul.koszulSymmetric R
  have := tensorUnit_isStrictlyGE (R := R) b hb
  -- `D' ◁ ι'` is a quasi-isomorphism.
  have h₁ : QuasiIso (D' ◁ ι') := quasiIso_whiskerLeft_of_flat D' b ι'
  -- `ι ▷ 𝟙` is a quasi-isomorphism.
  have h₂ : QuasiIso (ι ▷ 𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ)) := by
    rw [← quasiIso_iff_of_arrow_mk_iso ι _ (Arrow.isoMk (ρ_ _).symm (ρ_ _).symm
      (rightUnitor_inv_naturality ι).symm)]
    infer_instance
  -- `𝟙 ◁ ι'` is a quasi-isomorphism.
  have h₃ : QuasiIso (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ) ◁ ι') := by
    rw [← quasiIso_iff_of_arrow_mk_iso ι' _ (Arrow.isoMk (λ_ _).symm (λ_ _).symm
      (leftUnitor_inv_naturality ι').symm)]
    infer_instance
  -- hence `ι ▷ (D ⊗ P)` is.
  have h₄ : QuasiIso (ι ▷ (D ⊗ P)) := by
    have : QuasiIso (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ) ◁ ι' ≫ ι ▷ (D ⊗ P)) := by
      rw [whisker_exchange]; infer_instance
    exact quasiIso_of_comp_left (𝟙_ (CochainComplex (ModuleCat.{u} R) ℤ) ◁ ι') _
  -- transport along the symmetry `D ⊗ (Z ⊗ P) ≅ Z ⊗ (D ⊗ P)`.
  let c : ∀ Z : CochainComplex (ModuleCat.{u} R) ℤ, D ⊗ (Z ⊗ P) ≅ Z ⊗ (D ⊗ P) := fun Z =>
    (α_ D Z P).symm ≪≫ whiskerRightIso (β_ D Z) P ≪≫ α_ Z D P
  have hc : D ◁ (ι ▷ P) ≫ (c D').hom = (c _).hom ≫ ι ▷ (D ⊗ P) := by
    simp only [c, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, Category.assoc]
    rw [associator_inv_naturality_middle_assoc, ← comp_whiskerRight_assoc,
      BraidedCategory.braiding_naturality_right, comp_whiskerRight_assoc,
      associator_naturality_left]
  have h₅ : QuasiIso (D ◁ (ι ▷ P)) := by
    rw [quasiIso_iff_of_arrow_mk_iso (D ◁ (ι ▷ P)) (ι ▷ (D ⊗ P))
      (Arrow.isoMk (c _) (c D') hc.symm)]
    exact h₄
  rw [MonoidalCategory.whiskerLeft_comp]
  infer_instance

end Dualizing.FlatTensor
