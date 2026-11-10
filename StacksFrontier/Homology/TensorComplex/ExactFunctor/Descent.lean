module

public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import Mathlib.Combinatorics.Quiver.ReflQuiver
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Tensor–total functors and their descent to the homotopy category

For a fixed cochain complex `G`, the functors `TleftCochain G : F ↦ Tot(G ⊗ F)` and
`TrightCochain G : F ↦ Tot(F ⊗ G)` on cochain complexes, their additivity, the proof that they
preserve the chain-homotopy relation, their descent `Tleft G` / `Tright G` to
`K(C) = HomotopyCategory C (ComplexShape.up ℤ)`, and the `CommShift ℤ` data `TleftCommShift G`
/ `TrightCommShift G` of the descended functors.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.Limits
  CategoryTheory.Pretriangulated

variable {C : Type*} [Category C] [Preadditive C] [MonoidalCategory C] [HasZeroObject C]
  [HasBinaryBiproducts C]
  [(curriedTensor C).Additive] [∀ X₁ : C, ((curriedTensor C).obj X₁).Additive]
  [∀ (K₁ K₂ : CochainComplex C ℤ),
      HomologicalComplex.HasMapBifunctor K₁ K₂ (curriedTensor C) (ComplexShape.up ℤ)]

-- Main Definition(s)

/-- Definition 2 (left version), on cochain complexes.

For a fixed complex `G`, the functor `F ↦ Tot(G ⊗ F)` on cochain complexes of `O_X`-modules,
realized as the curried tensor bifunctor lifted to cochain complexes
(`Functor.map₂CochainComplex`) and evaluated at `G` in the first variable. -/
@[sga "4 XVII 7.3.3" "special case", sga "7 VII 3.6" "more general"]
noncomputable def TleftCochain (G : CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  (curriedTensor C).map₂CochainComplex.obj G

/-- Definition 2 (right version), on cochain complexes: `F ↦ Tot(F ⊗ G)`. -/
@[sga "4 XVII 7.3.3" "special case"]
noncomputable def TrightCochain (G : CochainComplex C ℤ) :
    CochainComplex C ℤ ⥤ CochainComplex C ℤ :=
  (curriedTensor C).map₂CochainComplex.flip.obj G

/-- The left tensor–total functor is additive (it sends `f + g` to `T f + T g`), part of
the assertion that it is a functor of additive categories. -/
instance TleftCochain_additive (G : CochainComplex C ℤ) : (TleftCochain G).Additive := by
  constructor
  intro X Y f g
  change HomologicalComplex.mapBifunctorMap (𝟙 G) (f + g) (curriedTensor C) (ComplexShape.up ℤ)
      = HomologicalComplex.mapBifunctorMap (𝟙 G) f (curriedTensor C) (ComplexShape.up ℤ)
        + HomologicalComplex.mapBifunctorMap (𝟙 G) g (curriedTensor C) (ComplexShape.up ℤ)
  ext n i₁ i₂ h
  rw [HomologicalComplex.add_f_apply,
    HomologicalComplex.ι_mapBifunctorMap _ _ _ _ i₁ i₂ n h,
    Preadditive.comp_add,
    HomologicalComplex.ι_mapBifunctorMap _ _ _ _ i₁ i₂ n h,
    HomologicalComplex.ι_mapBifunctorMap _ _ _ _ i₁ i₂ n h]
  simp only [HomologicalComplex.add_f_apply, Functor.map_add,
    Preadditive.add_comp, Preadditive.comp_add]

/-- The right tensor–total functor is additive. -/
instance TrightCochain_additive (G : CochainComplex C ℤ) : (TrightCochain G).Additive := by
  constructor
  intro X Y f g
  change HomologicalComplex.mapBifunctorMap (f + g) (𝟙 G) (curriedTensor C) (ComplexShape.up ℤ)
      = HomologicalComplex.mapBifunctorMap f (𝟙 G) (curriedTensor C) (ComplexShape.up ℤ)
        + HomologicalComplex.mapBifunctorMap g (𝟙 G) (curriedTensor C) (ComplexShape.up ℤ)
  ext n i₁ i₂ h
  rw [HomologicalComplex.add_f_apply,
    HomologicalComplex.ι_mapBifunctorMap _ _ _ _ i₁ i₂ n h,
    Preadditive.comp_add,
    HomologicalComplex.ι_mapBifunctorMap _ _ _ _ i₁ i₂ n h,
    HomologicalComplex.ι_mapBifunctorMap _ _ _ _ i₁ i₂ n h]
  simp only [HomologicalComplex.add_f_apply, Functor.map_add,
    Preadditive.add_comp, NatTrans.app_add]

/-- `F` preserves the chain-homotopy relation: homotopic morphisms have homotopic images.
This is the condition that lets a cochain-level functor descend to the homotopy category
("homotopic morphisms are sent to homotopic morphisms"). -/
def PreservesHomotopyRel (F : CochainComplex C ℤ ⥤ CochainComplex C ℤ) : Prop :=
  ∀ {X Y : CochainComplex C ℤ} {f g : X ⟶ Y},
    homotopic C (ComplexShape.up ℤ) f g → homotopic C (ComplexShape.up ℤ) (F.map f) (F.map g)

/-- `dNext` on cochain complexes is the differential followed by the next component. -/
private theorem dNext_up_eq {D : Type*} [Category D] [Preadditive D] {K L : CochainComplex D ℤ}
    (f : ∀ i j, K.X i ⟶ L.X j) (i : ℤ) : dNext i f = K.d i (i + 1) ≫ f (i + 1) i :=
  dNext_eq f rfl

/-- `prevD` on cochain complexes is the previous component followed by the differential. -/
private theorem prevD_up_eq {D : Type*} [Category D] [Preadditive D] {K L : CochainComplex D ℤ}
    (f : ∀ i j, K.X i ⟶ L.X j) (i : ℤ) : prevD i f = f i (i - 1) ≫ L.d (i - 1) i :=
  prevD_eq f (by rw [ComplexShape.up_Rel]; omega)

/-- The Koszul sign `ε₁` of the total complex shape on `ℤ × ℤ` is trivial. -/
private theorem up_ε₁_eq (a b : ℤ) :
    (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = 1 := rfl

/-- The Koszul sign `ε₂` of the total complex shape on `ℤ × ℤ` is `(-1) ^ a`. -/
private theorem up_ε₂_eq (a b : ℤ) :
    (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (a, b) = a.negOnePow := rfl

/-- The relation of `ComplexShape.up ℤ` between `a` and `a + 1`. -/
private theorem up_rel_succ (a : ℤ) : (ComplexShape.up ℤ).Rel a (a + 1) := rfl

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- **The left tensor–total functor descends to the homotopy category.**

This is part of the asserted content of the lemma (Definition 2: "Both descend to
well-defined additive functors ... since homotopic morphisms are sent to homotopic
morphisms"), *not* a hypothesis.  It follows from additivity of the tensor bifunctor:
tensoring a chain homotopy `h` for `f ≃ g` with `G` produces a chain homotopy for
`T_left f ≃ T_left g`. -/
@[sga "4½ Etat_0 1.3.3" "P*(Z, special case"]
theorem TleftCochain_preservesHomotopyRel (G : CochainComplex C ℤ) :
    PreservesHomotopyRel (TleftCochain G) := by
  /- STRATEGY (homotopy preservation, left version).
     Unfold `homotopic`: from `f ≃ g` we get a chain homotopy `H : Homotopy f g`, i.e. maps
     `H.hom i j : X.X i ⟶ Y.X j` (nonzero only for `j = i - 1` in the cochain convention)
     with `f - g = d ∘ H + H ∘ d`.  We must produce a chain homotopy
     `Tot(id_G ⊗ f) ≃ Tot(id_G ⊗ g)`.
     Build it summand-wise on the total complex: on the `(i₁, i₂)` summand
     `G.X i₁ ⊗ X.X i₂` of `Tot(G ⊗ X)^n`, use the component
       `ε • (id_{G.X i₁} ⊗ H.hom i₂ (i₂-1))` followed by the inclusion
       `ιMapBifunctor G Y _ _ i₁ (i₂-1) m`,
     with `ε = (ComplexShape.up ℤ).ε₂ ... (i₁,i₂)` the Koszul sign coming from moving the
     homotopy across the first tensor factor (`(-1)^{i₁}`), assembled with `Homotopy.mk` and
     `mapBifunctorDesc`.
     The `comm` identity is verified by `HomologicalComplex₂.total.hom_ext`: the `dite_eq_right`
     (off-diagonal) components are zero; the main
     diagonal component is the Leibniz bookkeeping
       `d(id⊗H) + (id⊗H)d = id⊗(dH+Hd) = id⊗(f-g) = Tot(id⊗f) - Tot(id⊗g)`,
     where the only nontrivial point is matching the Koszul signs `ε₂` of `mapBifunctor.d₁`/`d₂`
     against the sign chosen above.  Key Mathlib API: `Homotopy.mk`,
     `HomologicalComplex.mapBifunctorDesc`, `HomologicalComplex.ι_mapBifunctorDesc`,
     `HomologicalComplex₂.total.hom_ext`, `HomologicalComplex.mapBifunctor.d₁_eq`/`d₂_eq`,
     `HomologicalComplex.ι_mapBifunctorMap`, and `Functor.map_add`/additivity of
     `((curriedTensor C).obj _)`.  Self-contained; uses only additivity of the bifunctor. -/
  -- SANITY CHECK PASSED
  rintro X Y f g ⟨H⟩
  refine ⟨Homotopy.mk
    (fun n m => HomologicalComplex.mapBifunctorDesc (fun i₁ i₂ hn =>
      if hm : m = n - 1 then
        (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (i₁, i₂) •
          (((curriedTensor C).obj (G.X i₁)).map (H.hom i₂ (i₂ - 1)) ≫
            HomologicalComplex.ιMapBifunctor G Y (curriedTensor C) (ComplexShape.up ℤ)
              i₁ (i₂ - 1) m (by
                simp only [ComplexShape.π, TotalComplexShape.π] at hn ⊢; omega))
      else 0)) ?_ ?_⟩
  · intro i j hij
    apply HomologicalComplex₂.total.hom_ext
    intro i₁ i₂ hi
    rw [HomologicalComplex.ι_mapBifunctorDesc, comp_zero]
    have : ¬ (j = i - 1) := by
      simp only [ComplexShape.up_Rel] at hij; omega
    rw [dite_eq_right this]
  · intro i
    apply HomologicalComplex₂.total.hom_ext
    intro i₁ i₂ hi
    have hi' : i₁ + i₂ = i := by
      simpa only [ComplexShape.π, TotalComplexShape.π] using hi
    -- LHS/RHS-g via ι_mapBifunctorMap
    have hTf : (TleftCochain G).map f
        = HomologicalComplex.mapBifunctorMap (𝟙 G) f (curriedTensor C) (ComplexShape.up ℤ) := rfl
    have hTg : (TleftCochain G).map g
        = HomologicalComplex.mapBifunctorMap (𝟙 G) g (curriedTensor C) (ComplexShape.up ℤ) := rfl
    -- Identify .ιTotal with ιMapBifunctor
    change HomologicalComplex.ιMapBifunctor G X (curriedTensor C) (ComplexShape.up ℤ) i₁ i₂ i hi ≫
          ((TleftCochain G).map f).f i
      = HomologicalComplex.ιMapBifunctor G X (curriedTensor C) (ComplexShape.up ℤ) i₁ i₂ i hi ≫
          ((dNext i) _ + (prevD i) _ + ((TleftCochain G).map g).f i)
    rw [hTf, HomologicalComplex.ι_mapBifunctorMap]
    rw [Preadditive.comp_add, Preadditive.comp_add,
      hTg, HomologicalComplex.ι_mapBifunctorMap]
    -- Expand dNext / prevD
    rw [dNext_up_eq, prevD_up_eq]
    erw [HomologicalComplex.mapBifunctor.d_eq, HomologicalComplex.mapBifunctor.d_eq]
    simp only [Preadditive.add_comp, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    -- Identify the identity component on LHS / g-term
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id, NatTrans.id_app,
      Category.id_comp]
    -- Expand d₁/d₂ in the dNext term
    rw [HomologicalComplex.mapBifunctor.d₁_eq G X (curriedTensor C) (ComplexShape.up ℤ)
        (up_rel_succ i₁) i₂ (i+1)
        (by change (i₁+1)+i₂ = i+1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq G X (curriedTensor C) (ComplexShape.up ℤ) i₁
        (up_rel_succ i₂) (i+1)
        (by change i₁+(i₂+1) = i+1; omega)]
    -- Expand D₁/D₂ in the prevD term: first fire ι_mapBifunctorDesc
    simp only [
      Linear.units_smul_comp, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc,
      ]
    -- resolve the (decidable) `if` conditions in the dNext term
    have hii : i = i + 1 - 1 := by omega
    rw [dite_eq_left hii, dite_eq_left hii]
    -- reduce the `dite True` in the prevD term
    simp only [dite_eq_left (trivial : True)]
    -- prevD term: fire ι_mapBifunctorDesc (reassociate), then expand D₁/D₂
    rw [← Category.assoc (HomologicalComplex.ιMapBifunctor G X (curriedTensor C)
        (ComplexShape.up ℤ) i₁ i₂ i hi),
      ← Category.assoc (HomologicalComplex.ιMapBifunctor G X (curriedTensor C)
        (ComplexShape.up ℤ) i₁ i₂ i hi)]
    simp only [HomologicalComplex.ι_mapBifunctorDesc]
    simp only [Linear.units_smul_comp, Category.assoc,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
    rw [HomologicalComplex.mapBifunctor.d₁_eq G Y (curriedTensor C) (ComplexShape.up ℤ)
        (up_rel_succ i₁) (i₂-1) i
        (by change (i₁+1)+(i₂-1) = i; omega),
      HomologicalComplex.mapBifunctor.d₂_eq G Y (curriedTensor C) (ComplexShape.up ℤ) i₁
        (up_rel_succ (i₂-1)) i
        (by change i₁+(i₂-1+1) = i; omega)]
    -- Normalize the sign factors: ε₁ = 1, ε₂(i₁, _) = (i₁).negOnePow.
    simp only [up_ε₁_eq, up_ε₂_eq]
    -- Normalize shifted inner indices in the diagonal (term2, term4) summands.
    have shift : ∀ (A : C) (g : ∀ k, A ⟶ Y.X k) (j : ℤ) (hj : j = i₂) (h : i₁ + j = i),
        ((curriedTensor C).obj (G.X i₁)).map (g j) ≫
            HomologicalComplex.ιMapBifunctor G Y (curriedTensor C) (ComplexShape.up ℤ) i₁ j i h
          = ((curriedTensor C).obj (G.X i₁)).map (g i₂) ≫
            HomologicalComplex.ιMapBifunctor G Y (curriedTensor C) (ComplexShape.up ℤ) i₁ i₂ i hi :=
      by rintro A g j rfl h; rfl
    rw [shift _ (H.hom (i₂ + 1)) (i₂ + 1 - 1) (by omega), shift _ (Y.d (i₂ - 1)) _ (by omega)]
    -- term1/term3 cancel by the unit-sign bookkeeping;
    -- term2/term4 combine via additivity + the homotopy relation `H.comm i₂`.
    have ep : ((i₁ + 1 : ℤ)).negOnePow = - (i₁:ℤ).negOnePow := by rw [Int.negOnePow_succ]
    -- the homotopy relation at degree i₂
    have hcomm := H.comm i₂
    rw [dNext_up_eq, prevD_up_eq] at hcomm
    -- normalize all scalars: pull out, collapse `negOnePow • negOnePow = 1`, sign of term1
    rw [ep]
    simp only [one_smul, Linear.comp_units_smul,
      smul_smul, Int.units_mul_self]
    -- now combine: term1+term3 cancel by naturality + sign; LHS expands via `H.comm i₂`.
    have hnat := ((curriedTensor C).map (G.d i₁ (i₁+1))).naturality (H.hom i₂ (i₂-1))
    rw [reassoc_of% hnat]
    -- expand LHS `f.f i₂` via the homotopy relation; recombine RHS diagonal composites.
    rw [hcomm, Functor.map_add, Functor.map_add, Preadditive.add_comp, Preadditive.add_comp,
      one_mul, Units.neg_smul, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    abel

omit [HasZeroObject C] [HasBinaryBiproducts C] in
/-- **The right tensor–total functor descends to the homotopy category.** -/
theorem TrightCochain_preservesHomotopyRel (G : CochainComplex C ℤ) :
    PreservesHomotopyRel (TrightCochain G) := by
  /- STRATEGY (homotopy preservation, right version).  Mirror of
     `TleftCochain_preservesHomotopyRel`, tensoring the homotopy on the *first* (left) variable
     instead of the second: `Tot(f ⊗ id_G) ≃ Tot(g ⊗ id_G)`.  Build the homotopy summand-wise
     with components `ε • (H.hom i₁ (i₁-1) ⊗ id_{G.X i₂})` and inclusion
     `ιMapBifunctor X G _ _ (i₁-1) i₂ m`, where the Koszul sign is now the one for moving the
     homotopy past nothing on the left (`ε₁`/sign `1` on the first variable).  Same `comm`
     verification via `HomologicalComplex₂.total.hom_ext` and `mapBifunctor.d₁_eq`/`d₂_eq`,
     using `map₂CochainComplex.flip`.  Uses additivity of `curriedTensor C` in the first
     variable (`(curriedTensor C).Additive`). -/
  -- SANITY CHECK PASSED
  rintro X Y f g ⟨H⟩
  refine ⟨Homotopy.mk
    (fun n m => HomologicalComplex.mapBifunctorDesc (fun i₁ i₂ hn =>
      if hm : m = n - 1 then
        ((curriedTensor C).map (H.hom i₁ (i₁ - 1))).app (G.X i₂) ≫
          HomologicalComplex.ιMapBifunctor Y G (curriedTensor C) (ComplexShape.up ℤ)
            (i₁ - 1) i₂ m (by
              simp only [ComplexShape.π, TotalComplexShape.π] at hn ⊢; omega)
      else 0)) ?_ ?_⟩
  · intro i j hij
    apply HomologicalComplex₂.total.hom_ext
    intro i₁ i₂ hi
    rw [HomologicalComplex.ι_mapBifunctorDesc, comp_zero]
    have : ¬ (j = i - 1) := by
      simp only [ComplexShape.up_Rel] at hij; omega
    rw [dite_eq_right this]
  · intro i
    apply HomologicalComplex₂.total.hom_ext
    intro i₁ i₂ hi
    have hi' : i₁ + i₂ = i := by
      simpa only [ComplexShape.π, TotalComplexShape.π] using hi
    have hTf : (TrightCochain G).map f
        = HomologicalComplex.mapBifunctorMap f (𝟙 G) (curriedTensor C) (ComplexShape.up ℤ) := rfl
    have hTg : (TrightCochain G).map g
        = HomologicalComplex.mapBifunctorMap g (𝟙 G) (curriedTensor C) (ComplexShape.up ℤ) := rfl
    change HomologicalComplex.ιMapBifunctor X G (curriedTensor C) (ComplexShape.up ℤ) i₁ i₂ i hi ≫
          ((TrightCochain G).map f).f i
      = HomologicalComplex.ιMapBifunctor X G (curriedTensor C) (ComplexShape.up ℤ) i₁ i₂ i hi ≫
          ((dNext i) _ + (prevD i) _ + ((TrightCochain G).map g).f i)
    rw [hTf, HomologicalComplex.ι_mapBifunctorMap]
    rw [Preadditive.comp_add, Preadditive.comp_add,
      hTg, HomologicalComplex.ι_mapBifunctorMap]
    rw [dNext_up_eq, prevD_up_eq]
    erw [HomologicalComplex.mapBifunctor.d_eq, HomologicalComplex.mapBifunctor.d_eq]
    simp only [Preadditive.add_comp, Preadditive.comp_add,
      HomologicalComplex.mapBifunctor.ι_D₁_assoc, HomologicalComplex.mapBifunctor.ι_D₂_assoc]
    -- Identify the identity component on LHS / g-term (the G-side, second variable)
    simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
      ]
    -- Expand d₁/d₂ in the dNext term
    rw [HomologicalComplex.mapBifunctor.d₁_eq X G (curriedTensor C) (ComplexShape.up ℤ)
        (up_rel_succ i₁) i₂ (i+1)
        (by change (i₁+1)+i₂ = i+1; omega),
      HomologicalComplex.mapBifunctor.d₂_eq X G (curriedTensor C) (ComplexShape.up ℤ) i₁
        (up_rel_succ i₂) (i+1)
        (by change i₁+(i₂+1) = i+1; omega)]
    -- prevD term: fire ι_mapBifunctorDesc, expand D₁/D₂
    simp only [
      Linear.units_smul_comp, Category.assoc, HomologicalComplex.ι_mapBifunctorDesc,
      ]
    have hii : i = i + 1 - 1 := by omega
    rw [dite_eq_left hii, dite_eq_left hii]
    simp only [dite_eq_left (trivial : True)]
    rw [← Category.assoc (HomologicalComplex.ιMapBifunctor X G (curriedTensor C)
        (ComplexShape.up ℤ) i₁ i₂ i hi),
      ← Category.assoc (HomologicalComplex.ιMapBifunctor X G (curriedTensor C)
        (ComplexShape.up ℤ) i₁ i₂ i hi)]
    simp only [HomologicalComplex.ι_mapBifunctorDesc]
    simp only [ Category.assoc,
      HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
    rw [HomologicalComplex.mapBifunctor.d₁_eq Y G (curriedTensor C) (ComplexShape.up ℤ)
        (up_rel_succ (i₁-1)) i₂ i
        (by change (i₁-1+1)+i₂ = i; omega),
      HomologicalComplex.mapBifunctor.d₂_eq Y G (curriedTensor C) (ComplexShape.up ℤ) (i₁-1)
        (up_rel_succ i₂) i
        (by change (i₁-1)+(i₂+1) = i; omega)]
    -- Normalize the sign factors: ε₁ = 1, ε₂(_, _) = (first).negOnePow.
    simp only [up_ε₁_eq, up_ε₂_eq]
    -- Normalize shifted inner indices in the diagonal summands.
    have shift : ∀ (A : C) (g : ∀ k, A ⟶ Y.X k) (j : ℤ) (hj : j = i₁) (h : j + i₂ = i),
        ((curriedTensor C).map (g j)).app (G.X i₂) ≫
            HomologicalComplex.ιMapBifunctor Y G (curriedTensor C) (ComplexShape.up ℤ) j i₂ i h
          = ((curriedTensor C).map (g i₁)).app (G.X i₂) ≫
            HomologicalComplex.ιMapBifunctor Y G (curriedTensor C) (ComplexShape.up ℤ) i₁ i₂ i hi :=
      by rintro A g j rfl h; rfl
    rw [shift _ (H.hom (i₁ + 1)) (i₁ + 1 - 1) (by omega), shift _ (Y.d (i₁ - 1)) _ (by omega)]
    -- the homotopy relation at degree i₁
    have hcomm := H.comm i₁
    rw [dNext_up_eq, prevD_up_eq] at hcomm
    have ep : ((i₁ - 1 : ℤ)).negOnePow = - (i₁:ℤ).negOnePow := by
      have h := Int.negOnePow_succ (i₁-1)
      rw [show (i₁-1+1:ℤ) = i₁ from by omega] at h
      rw [h, neg_neg]
    rw [ep]
    -- LHS: expand f.f i₁ via homotopy relation, then `.map` is additive on the first variable
    rw [hcomm]
    simp only [Functor.map_add, NatTrans.app_add, Preadditive.add_comp, Category.id_comp,
      one_smul, Linear.comp_units_smul]
    -- term2/term4 cancel by naturality of `map (H.hom i₁ (i₁-1))` on `G.d i₂ (i₂+1)`.
    have hnat := ((curriedTensor C).map (H.hom i₁ (i₁-1))).naturality (G.d i₂ (i₂+1))
    rw [Functor.map_comp, NatTrans.comp_app, Functor.map_comp, NatTrans.comp_app,
      Category.assoc, Category.assoc]
    rw [reassoc_of% hnat]
    rw [Units.neg_smul]
    abel

/-- Descend a homotopy-preserving cochain functor to the homotopy category
`K(C) = HomotopyCategory C (ComplexShape.up ℤ)`, via the universal property of the homotopy
category as a quotient (`CategoryTheory.Quotient.lift`). -/
noncomputable def descendF (F : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (hF : PreservesHomotopyRel F) :
    HomotopyCategory C (ComplexShape.up ℤ) ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift (homotopic C (ComplexShape.up ℤ))
    (F ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ))
    (fun _ _ _ _ h => CategoryTheory.Quotient.sound _ (hF h))

set_option linter.unusedSectionVars false in
/-- The descended functor really is a lift: it commutes (strictly) with the quotient functor
`K(C)`. This is the correctness statement uniquely characterizing `descendF F hF`. -/
theorem descendF_comp_quotient (F : CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (hF : PreservesHomotopyRel F) :
    HomotopyCategory.quotient C (ComplexShape.up ℤ) ⋙ descendF F hF
      = F ⋙ HomotopyCategory.quotient C (ComplexShape.up ℤ) :=
  CategoryTheory.Quotient.lift_spec _ _ _

/-- The functor `T_left : K(Mod(O_X)) ⟶ K(Mod(O_X))`, `F ↦ Tot(G ⊗ F)`, of Definition 2
(left version), defined unconditionally as the descent of the cochain-level functor
`TleftCochain G` to the homotopy category. -/
noncomputable def Tleft (G : CochainComplex C ℤ) :
    HomotopyCategory C (ComplexShape.up ℤ) ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  descendF (TleftCochain G) (TleftCochain_preservesHomotopyRel G)

/-- The functor `T_right : K(Mod(O_X)) ⟶ K(Mod(O_X))`, `F ↦ Tot(F ⊗ G)`, of Definition 2
(right version). -/
@[sga "4 XVII 7.3.3" "special case"]
noncomputable def Tright (G : CochainComplex C ℤ) :
    HomotopyCategory C (ComplexShape.up ℤ) ⥤ HomotopyCategory C (ComplexShape.up ℤ) :=
  descendF (TrightCochain G) (TrightCochain_preservesHomotopyRel G)

-- Main Statement(s)

/-- The `CommShift ℤ` comparison datum `ξ` for the descended functor `Tleft G` on `K(C)`.

This is the Stacks Tag 0FNG isomorphism `Tot(G ⊗ F[1]) ≅ Tot(G ⊗ F)[1]` descended to the
homotopy category.  It is obtained for free: at the cochain level `TleftCochain G =
(curriedTensor C).map₂CochainComplex.obj G` already carries a `CommShift ℤ` instance
(`Mathlib/Algebra/Homology/BifunctorShift.lean`, the `(p*y).negOnePow`-signed comparison iso),
and `descendF` is literally `Quotient.lift (homotopic ..) (TleftCochain G ⋙ quotient) ..`, so
`CategoryTheory.Quotient.liftCommShift` transports the `CommShift` through the quotient. -/
@[reducible] noncomputable def TleftCommShift (G : CochainComplex C ℤ) :
    (Tleft G).CommShift ℤ := by
  unfold Tleft descendF
  haveI : (TleftCochain G).CommShift ℤ := by unfold TleftCochain; infer_instance
  exact Quotient.liftCommShift _ _ _ _

/-- The analogous `CommShift ℤ` comparison datum `ξ` for `Tright G`. -/
@[reducible] noncomputable def TrightCommShift (G : CochainComplex C ℤ) :
    (Tright G).CommShift ℤ := by
  unfold Tright descendF
  haveI : (TrightCochain G).CommShift ℤ := by unfold TrightCochain; infer_instance
  exact Quotient.liftCommShift _ _ _ _
