module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery.TotalComplexDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The right-factor functor is triangulated

Part of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery`:
the descent `bifunctorPhiR` of `Tot(F(-, G))`
(fixed complex in the right factor), its cochain transport `ΨcochR`, the mapping-cone and
triangle isomorphisms, and `bifunctorPhiR_isTriangulated`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

noncomputable section

universe u v w

namespace Stacks.SheafOfModules.Tensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{w})
  [HasWeakSheafify J AddCommGrpCat] [J.WEqualsLocallyBijective AddCommGrpCat]

variable [HasBinaryBiproducts (SheafOfModules (ringSheaf R))]

namespace Reduction

attribute [local implicit_reducible] Functor.map₂HomologicalComplex

variable {A B D : Type*} [Category A] [Category B] [Category D]
  [Preadditive A] [Preadditive B] [Preadditive D]
  [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D]

/-- **Right-factor case.**  The descended functor `Φ : K(A) ⥤ K(D)` lifting
`F^• ↦ Tot(F(F^•, G))`.  Homotopy-invariance in the first variable
(`mapBifunctorMapHomotopy₁`) makes the descent well defined. -/
@[sga "4½ Etat_0 1.3.3" "partial"]
noncomputable def bifunctorPhiR
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ)) :
    HomotopyCategory A (ComplexShape.up ℤ) ⥤ HomotopyCategory D (ComplexShape.up ℤ) :=
  haveI := map₂HomologicalComplex_flip_obj_additive F G
  CategoryTheory.Quotient.lift (homotopic A (ComplexShape.up ℤ))
    ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj G ⋙ HomotopyCategory.quotient D (ComplexShape.up ℤ))
    (by
      rintro x y f₁ f₂ ⟨hfg⟩
      dsimp
      rw [HomotopyCategory.eq_of_homotopy]
      exact HomologicalComplex.mapBifunctorMapHomotopy₁ hfg (𝟙 G) F (ComplexShape.up ℤ))

/-- The lift isomorphism `quotient ⋙ Φ ≅ Tot(F(-, G)) ⋙ quotient` (right case). -/
noncomputable def bifunctorPhiRFactors
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ)) :
    HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ bifunctorPhiR F G ≅
      (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj G ⋙ HomotopyCategory.quotient D (ComplexShape.up ℤ) :=
  haveI := map₂HomologicalComplex_flip_obj_additive F G
  Quotient.lift.isLift _ _ _

/-- `Φ` (right case) is additive. -/
instance bifunctorPhiR_additive
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ)) :
    (bifunctorPhiR F G).Additive := by
  have := map₂HomologicalComplex_flip_obj_additive F G
  have : (HomotopyCategory.quotient A (ComplexShape.up ℤ) ⋙ bifunctorPhiR F G).Additive :=
    Functor.additive_of_iso (bifunctorPhiRFactors F G).symm
  exact Functor.additive_of_full_essSurj_comp
    (HomotopyCategory.quotient A (ComplexShape.up ℤ)) _

/-- The commutation-with-shift datum `ξ` for `Φ` (right case): the descent of the
complex-level (sign-free, tag 0FLG) `CommShift ℤ` in the first variable. -/
@[reducible]
noncomputable def bifunctorXiR
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ)) :
    (bifunctorPhiR F G).CommShift ℤ :=
  haveI := map₂HomologicalComplex_flip_obj_additive F G
  Quotient.liftCommShift _ _ _ _

/-- **C1aR (right bifunctor cochain transport).**  Flip of `Ψcoch`: transport a
cochain `z : Cochain X Y n` of `A` through `Ψ = Tot(F(-, G))`.  On the `(p,q)`
total-complex summand (p = moving X-index, q = fixed G-index), a component
`z.v : X^p → Y^{p+n}` transports as `F(z.v, G^q)`, with Koszul sign
`(n*q).negOnePow`. -/
noncomputable def ΨcochR
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ))
    {X Y : CochainComplex A ℤ} {n : ℤ}
    (z : CochainComplex.HomComplex.Cochain X Y n) :
    CochainComplex.HomComplex.Cochain
      (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj G).obj X)
      (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj G).obj Y) n :=
  CochainComplex.HomComplex.Cochain.mk fun a a' h =>
    X.mapBifunctorDesc (K₂ := G) (c := ComplexShape.up ℤ) fun p q hpq =>
      (F.map (z.v p (p + n) (by omega))).app (G.X q) ≫
        HomologicalComplex.ιMapBifunctor Y G F (ComplexShape.up ℤ) (p + n) q a'
          (by have : p + q = a := hpq; change (p + n) + q = a'; omega)

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
/-- **C1bR.**  Degreewise value of `ΨcochR` (flip of `Ψcoch_v`). -/
lemma ΨcochR_v
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ))
    {X Y : CochainComplex A ℤ} {n : ℤ}
    (z : CochainComplex.HomComplex.Cochain X Y n) (a a' : ℤ) (h : a + n = a')
    (p q : ℤ) (hpq : p + q = a) :
    HomologicalComplex.ιMapBifunctor X G F (ComplexShape.up ℤ) p q a hpq ≫ (ΨcochR F G z).v a a' h =
        (F.map (z.v p (p + n) (by omega))).app (G.X q) ≫
          HomologicalComplex.ιMapBifunctor Y G F (ComplexShape.up ℤ) (p + n) q a'
            (by change (p + n) + q = a'; omega) := by
  simp only [ΨcochR, CochainComplex.HomComplex.Cochain.mk_v]
  rw [X.ι_mapBifunctorDesc]

/-- Two ways of writing the target index of a morphism followed by `ιMapBifunctor` agree. -/
private theorem map_app_comp_ιMapBifunctor_congr
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive D]
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ)) (Y : CochainComplex A ℤ) {X' : A} {c : ℤ}
    (f : ∀ r, c = r → (X' ⟶ Y.X r)) (q a' r r' : ℤ) (hr : c = r) (hr' : c = r')
    (hι : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (r, q) = a')
    (hι' : (ComplexShape.up ℤ).π (ComplexShape.up ℤ) (ComplexShape.up ℤ) (r', q) = a') :
    (F.map (f r hr)).app (G.X q) ≫
        HomologicalComplex.ιMapBifunctor Y G F (ComplexShape.up ℤ) r q a' hι =
      (F.map (f r' hr')).app (G.X q) ≫
        HomologicalComplex.ιMapBifunctor Y G F (ComplexShape.up ℤ) r' q a' hι' := by
  subst hr hr'
  rfl

/-- Cochains of `Tot(F(-, G))` are equal if they agree after each `ιMapBifunctor`. -/
private theorem cochain_ext_of_ιMapBifunctor_comp
    {A B D : Type*} [Category A] [Category B] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive D]
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ)) {X Y : CochainComplex A ℤ} {n : ℤ}
    {z z' : CochainComplex.HomComplex.Cochain
      (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj G).obj X)
      (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj G).obj Y) n}
    (h : ∀ (a a' : ℤ) (h : a + n = a') (p q : ℤ) (hpq : p + q = a),
      HomologicalComplex.ιMapBifunctor X G F (ComplexShape.up ℤ) p q a hpq ≫ z.v a a' h =
        HomologicalComplex.ιMapBifunctor X G F (ComplexShape.up ℤ) p q a hpq ≫ z'.v a a' h) :
    z = z' := by
  refine CochainComplex.HomComplex.Cochain.ext _ _ fun a a' ha => ?_
  exact HomologicalComplex.mapBifunctor.hom_ext fun p q hpq => h a a' ha p q hpq

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
/-- **C1cR.**  `ΨcochR` of a chain map (flip of `Ψcoch_ofHom`). -/
lemma ΨcochR_ofHom
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ))
    {X Y : CochainComplex A ℤ} (f : X ⟶ Y) :
    ΨcochR F G (CochainComplex.HomComplex.Cochain.ofHom f) =
      CochainComplex.HomComplex.Cochain.ofHom
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).flip.obj G).map f) := by
  refine cochain_ext_of_ιMapBifunctor_comp F G fun a a' h p q hpq2 => ?_
  obtain rfl : a = a' := by omega
  rw [ΨcochR_v F G _ a a h p q hpq2,
    map_app_comp_ιMapBifunctor_congr F G Y
      (fun r hr => (CochainComplex.HomComplex.Cochain.ofHom f).v p r hr) q a (p + 0) p
      (by omega) (by omega) _ (by simpa using hpq2),
    CochainComplex.HomComplex.Cochain.ofHom_v, Functor.flip_obj_map,
    Functor.map₂HomologicalComplex_map_app, CochainComplex.HomComplex.Cochain.ofHom_v,
    HomologicalComplex.ι_mapBifunctorMap]
  simp

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
/-- **C1dR.**  `ΨcochR` is multiplicative for cochain composition (flip of
`Ψcoch_comp`).  Signs match via `(n₁+n₂)*q = n₁*q+n₂*q`; the G-index `q` is
preserved across composition (the moving index is the FIRST/X-index `p`). -/
lemma ΨcochR_comp
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ))
    {X Y Z : CochainComplex A ℤ} {n₁ n₂ n₁₂ : ℤ}
    (z₁ : CochainComplex.HomComplex.Cochain X Y n₁)
    (z₂ : CochainComplex.HomComplex.Cochain Y Z n₂) (h : n₁ + n₂ = n₁₂) :
    ΨcochR F G (z₁.comp z₂ h) = (ΨcochR F G z₁).comp (ΨcochR F G z₂) h := by
  refine cochain_ext_of_ιMapBifunctor_comp F G fun a a' h' p q hpq2 => ?_
  rw [ΨcochR_v F G (z₁.comp z₂ h) a a' h' p q hpq2,
    CochainComplex.HomComplex.Cochain.comp_v z₁ z₂ h p (p + n₁) (p + n₁₂)
      rfl (by omega),
    Functor.map_comp, NatTrans.comp_app]
  rw [CochainComplex.HomComplex.Cochain.comp_v (ΨcochR F G z₁) (ΨcochR F G z₂) h
      a (a + n₁) a' rfl (by omega),
    ← Category.assoc,
    ΨcochR_v F G z₁ a (a + n₁) rfl p q hpq2,
    Category.assoc ((F.map (z₁.v p (p + n₁) (by omega))).app (G.X q))
      (HomologicalComplex.ιMapBifunctor Y G F (ComplexShape.up ℤ) (p + n₁) q (a + n₁)
        (by simp; omega))
      ((ΨcochR F G z₂).v (a + n₁) a' (by omega)),
    ΨcochR_v F G z₂ (a + n₁) a' (by omega) (p + n₁) q (by omega)]
  rw [map_app_comp_ιMapBifunctor_congr F G Z (fun r hr => z₂.v (p + n₁) r hr) q a'
      (p + n₁ + n₂) (p + n₁₂) rfl (by omega) (by simp; omega) (by simp; omega),
    ← Category.assoc]

omit [HasZeroObject A] [HasZeroObject B] [HasZeroObject D]
  [HasBinaryBiproducts A] [HasBinaryBiproducts B] [HasBinaryBiproducts D] in
/-- **C1eR.**  `ΨcochR` commutes with the cochain differential `δ` (flip of
`Ψcoch_δ`).  Here the fixed G-index is the SECOND slot `q` (carrying the Koszul
sign `ε₂ = p.negOnePow` in `d₂`), and the moving X-index is the FIRST slot `p`
(carrying `ε₁ = 1` in `d₁`).  The G-side `d₂` cross-terms cancel via the sign
`(n*q)` carried by `ΨcochR`; the X-side `d₁` terms match `δ` in `A`. -/
lemma ΨcochR_δ
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ))
    {X Y : CochainComplex A ℤ} (n m : ℤ)
    (z : CochainComplex.HomComplex.Cochain X Y n) :
    CochainComplex.HomComplex.δ n m (ΨcochR F G z) =
      ΨcochR F G (CochainComplex.HomComplex.δ n m z) := by
  by_cases hnm : n + 1 = m
  · refine cochain_ext_of_ιMapBifunctor_comp F G fun a a' h p q hpq2 => ?_
    subst hnm
    -- Helper: decompose `ι ≫ d` of the total complex into the two Koszul pieces.
    -- For the flip, slot 1 is `W` (X-type, moving) and slot 2 is `G` (fixed).
    have hd : ∀ (W : CochainComplex A ℤ) (p₀ q₀ p₀' q₀' j j' : ℤ) (hjj : p₀ + q₀ = j)
        (hjj' : j + 1 = j') (hp : p₀ + 1 = p₀') (hq : q₀ + 1 = q₀'),
        HomologicalComplex.ιMapBifunctor W G F (ComplexShape.up ℤ) p₀ q₀ j hjj ≫
          (HomologicalComplex.mapBifunctor W G F (ComplexShape.up ℤ)).d j j'
        = (F.map (W.d p₀ p₀')).app (G.X q₀) ≫
            HomologicalComplex.ιMapBifunctor W G F (ComplexShape.up ℤ) p₀' q₀ j' (by simp; omega)
          + p₀.negOnePow • ((F.obj (W.X p₀)).map (G.d q₀ q₀') ≫
            HomologicalComplex.ιMapBifunctor W G F (ComplexShape.up ℤ) p₀ q₀' j'
              (by simp; omega)) := by
      intro W p₀ q₀ p₀' q₀' j j' hjj hjj' hp hq
      subst hp hq
      rw [HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
        HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂,
        HomologicalComplex.mapBifunctor.d₁_eq W G F (ComplexShape.up ℤ) (i₁ := p₀)
          (i₁' := p₀ + 1) (by simp) q₀ j' (by simp; omega),
        HomologicalComplex.mapBifunctor.d₂_eq W G F (ComplexShape.up ℤ) p₀ (i₂ := q₀)
          (i₂' := q₀ + 1) (by simp) j' (by simp; omega),
        show (ComplexShape.up ℤ).ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p₀, q₀) = 1 from rfl,
        show (ComplexShape.up ℤ).ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ) (p₀, q₀)
            = p₀.negOnePow from by rw [← ComplexShape.ε_up_ℤ p₀]; rfl, one_smul]
    rw [CochainComplex.HomComplex.δ_v n (n + 1) rfl _ a a' h (a' - 1) (a + 1)
        (by ring) (by ring)]
    rw [Preadditive.comp_add, Linear.comp_units_smul]
    -- Term 1: ι_X ≫ (ΨcochR z).v a (a'-1) ≫ d
    rw [← Category.assoc, ΨcochR_v F G z a (a' - 1) (by omega) p q hpq2,
      Category.assoc,
      show (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).flip.obj G).obj Y).d (a' - 1) a'
        = (HomologicalComplex.mapBifunctor Y G F (ComplexShape.up ℤ)).d (a' - 1) a' from rfl,
      hd Y (p + n) q (p + n + 1) (q + 1) (a' - 1) a' (by omega) (by omega) rfl rfl]
    -- Term 2: ι_X ≫ d ≫ (ΨcochR z).v (a+1) a'
    rw [show (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).flip.obj G).obj X).d a (a + 1)
        = (HomologicalComplex.mapBifunctor X G F (ComplexShape.up ℤ)).d a (a + 1) from rfl,
      ← Category.assoc, hd X p q (p + 1) (q + 1) a (a + 1) hpq2 rfl rfl rfl,
      Preadditive.add_comp,
      Category.assoc,
      ΨcochR_v F G z (a + 1) a' (by omega) (p + 1) q (by omega),
      Linear.units_smul_comp, Category.assoc,
      ΨcochR_v F G z (a + 1) a' (by omega) p (q + 1) (by omega)]
    -- RHS expansion.
    rw [ΨcochR_v F G (CochainComplex.HomComplex.δ n (n + 1) z) a a' h p q hpq2,
      CochainComplex.HomComplex.δ_v n (n + 1) rfl z p (p + (n + 1)) (by ring)
        (p + n) (p + 1) (by ring) (by ring),
      Functor.map_add, NatTrans.app_add, Preadditive.add_comp]
    -- Distribute composites: `(F.map (g ≫ h)).app = (F.map g).app ≫ (F.map h).app`.
    rw [Functor.map_units_smul, Functor.map_comp, NatTrans.comp_app,
      Functor.map_comp, NatTrans.app_units_zsmul, NatTrans.comp_app,
      Linear.units_smul_comp]
    -- Distribute and normalise associativity/scalars so the naturality square appears.
    simp only [Preadditive.comp_add, Category.assoc,
      Linear.comp_units_smul]
    -- Naturality aligns the two G-side `d₂` terms.
    rw [(F.map (z.v p (p + n) (by omega))).naturality_assoc (G.d q (q + 1))]
    -- Sign reconciliation: the two `d₂` terms cancel; the `d₁` terms match.
    have hsign : (p + n).negOnePow = - ((n + 1).negOnePow * p.negOnePow) := by
      rw [← Int.negOnePow_add, show (n + 1) + p = (p + n) + 1 by ring, Int.negOnePow_succ]
      simp
    rw [hsign]
    -- Bridge the indices `p + n + 1` and `p + 1 + n` to `p + (n + 1)` in the surviving terms.
    rw [map_app_comp_ιMapBifunctor_congr F G Y (fun r _ => Y.d (p + n) r) q a'
        (p + n + 1) (p + (n + 1)) rfl (by ring) (by simp; omega) (by simp; omega),
      map_app_comp_ιMapBifunctor_congr F G Y (fun r hr => z.v (p + 1) r hr) q a'
        (p + 1 + n) (p + (n + 1)) rfl (by ring) (by simp; omega) (by simp; omega)]
    simp only [smul_add,
      smul_smul]
    rw [Units.neg_smul]
    abel
  · rw [CochainComplex.HomComplex.δ_shape n m hnm,
      CochainComplex.HomComplex.δ_shape n m hnm]
    refine cochain_ext_of_ιMapBifunctor_comp F G fun a a' h p q hpq2 => ?_
    rw [ΨcochR_v]
    simp

/-- **C1fR (cone-object iso, right case).**  Flip of `bifunctorMappingConeIso`:
`Ψ.obj (mappingCone φ) ≅ mappingCone (Ψ.map φ)` for `Ψ = Tot(F(-, G))`. -/
noncomputable def bifunctorMappingConeIsoR
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ))
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj G).obj (CochainComplex.mappingCone φ) ≅
      CochainComplex.mappingCone
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).flip.obj G).map φ) :=
  letI Ψ := (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj G
  letI φ' := Ψ.map φ
  haveI hcofib : HomologicalComplex.HasHomotopyCofiber φ' := inferInstance
  have ΨcochR_zero : ∀ {X Y : CochainComplex A ℤ} {n : ℤ},
      ΨcochR F G (0 : CochainComplex.HomComplex.Cochain X Y n) = 0 := by
    intro X Y n
    apply CochainComplex.HomComplex.Cochain.ext
    intro a a' h
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpq2 : p + q = a := hpq
    rw [ΨcochR_v F G (0 : CochainComplex.HomComplex.Cochain X Y n) a a' h p q hpq2]
    simp
  have ΨcochR_neg : ∀ {X Y : CochainComplex A ℤ} {n : ℤ}
      (z : CochainComplex.HomComplex.Cochain X Y n),
      ΨcochR F G (-z) = -(ΨcochR F G z) := by
    intro X Y n z
    apply CochainComplex.HomComplex.Cochain.ext
    intro a a' h
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpq2 : p + q = a := hpq
    rw [ΨcochR_v F G (-z) a a' h p q hpq2,
      show (-z).v p (p + n) (by omega) = -(z.v p (p + n) (by omega)) from rfl,
      Functor.map_neg]
    simp only [CochainComplex.HomComplex.Cochain.neg_v,
      Preadditive.comp_neg]
    rw [ΨcochR_v F G z a a' h p q hpq2]
    simp
  have ΨcochR_add : ∀ {X Y : CochainComplex A ℤ} {n : ℤ}
      (z₁ z₂ : CochainComplex.HomComplex.Cochain X Y n),
      ΨcochR F G (z₁ + z₂) = ΨcochR F G z₁ + ΨcochR F G z₂ := by
    intro X Y n z₁ z₂
    apply CochainComplex.HomComplex.Cochain.ext
    intro a a' h
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpq2 : p + q = a := hpq
    rw [ΨcochR_v F G (z₁ + z₂) a a' h p q hpq2,
      show (z₁ + z₂).v p (p + n) (by omega)
        = z₁.v p (p + n) (by omega) + z₂.v p (p + n) (by omega) from rfl,
      Functor.map_add, NatTrans.app_add]
    simp only [CochainComplex.HomComplex.Cochain.add_v, Preadditive.add_comp,
      Preadditive.comp_add]
    rw [ΨcochR_v F G z₁ a a' h p q hpq2, ΨcochR_v F G z₂ a a' h p q hpq2]
  { hom := CochainComplex.mappingCone.lift φ'
      (CochainComplex.HomComplex.Cocycle.mk
        (ΨcochR F G (↑(CochainComplex.mappingCone.fst φ))) 2 (by norm_num)
        (by rw [ΨcochR_δ, CochainComplex.HomComplex.Cocycle.δ_eq_zero, ΨcochR_zero]))
      (ΨcochR F G (CochainComplex.mappingCone.snd φ))
      (by
        rw [CochainComplex.HomComplex.Cocycle.mk_coe, ΨcochR_δ,
          CochainComplex.mappingCone.δ_snd]
        change ΨcochR F G _ +
          (ΨcochR F G _).comp (CochainComplex.HomComplex.Cochain.ofHom φ') _ = 0
        rw [show CochainComplex.HomComplex.Cochain.ofHom φ' = ΨcochR F G
              (CochainComplex.HomComplex.Cochain.ofHom φ) from (ΨcochR_ofHom F G φ).symm,
          ← ΨcochR_comp, ΨcochR_neg]
        abel)
    inv := CochainComplex.mappingCone.desc φ'
      (ΨcochR F G (CochainComplex.mappingCone.inl φ))
      (Ψ.map (CochainComplex.mappingCone.inr φ))
      (by
        rw [ΨcochR_δ, CochainComplex.mappingCone.δ_inl, ΨcochR_ofHom,
          Functor.map_comp])
    hom_inv_id := by
      ext p
      rw [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        CochainComplex.mappingCone.lift_desc_f φ' _ _ _ _ _ _ p (p + 1) rfl,
        CochainComplex.HomComplex.Cocycle.mk_coe]
      have hinr : (Ψ.map (CochainComplex.mappingCone.inr φ)).f p
          = (ΨcochR F G (CochainComplex.HomComplex.Cochain.ofHom
              (CochainComplex.mappingCone.inr φ))).v p p (by ring) := by
        rw [ΨcochR_ofHom, CochainComplex.HomComplex.Cochain.ofHom_v]
      rw [hinr]
      rw [← CochainComplex.HomComplex.Cochain.comp_v _ _ (show (1 : ℤ) + (-1) = 0 by ring)
            p (p + 1) p rfl (by ring),
        ← CochainComplex.HomComplex.Cochain.comp_v _ _ (show (0 : ℤ) + 0 = 0 by ring)
            p p p (by ring) (by ring),
        ← ΨcochR_comp, ← ΨcochR_comp]
      rw [← CochainComplex.HomComplex.Cochain.add_v]
      rw [← ΨcochR_add, CochainComplex.mappingCone.id φ, ΨcochR_ofHom,
        CochainComplex.HomComplex.Cochain.ofHom_v]
      rw [CategoryTheory.Functor.map_id, HomologicalComplex.id_f]
    inv_hom_id := by
      have hIF : ∀ p : ℤ, (ΨcochR F G (CochainComplex.mappingCone.inl φ)).v (p + 1) p (by ring) ≫
          (ΨcochR F G ((CochainComplex.mappingCone.fst φ :
            CochainComplex.HomComplex.Cochain (CochainComplex.mappingCone φ) K 1))).v p (p + 1)
              (by ring)
            = 𝟙 ((Ψ.obj K).X (p + 1)) := by
        intro p
        rw [← CochainComplex.HomComplex.Cochain.comp_v _ _ (show (-1 : ℤ) + 1 = 0 by ring)
            (p + 1) p (p + 1) (by ring) (by ring),
          ← ΨcochR_comp, CochainComplex.mappingCone.inl_fst, ΨcochR_ofHom,
          CochainComplex.HomComplex.Cochain.ofHom_v, CategoryTheory.Functor.map_id,
          HomologicalComplex.id_f]
      have hIS : ∀ p : ℤ, (ΨcochR F G (CochainComplex.mappingCone.inl φ)).v (p + 1) p (by ring) ≫
          (ΨcochR F G (CochainComplex.mappingCone.snd φ)).v p p (by ring) = 0 := by
        intro p
        rw [← CochainComplex.HomComplex.Cochain.comp_v _ _ (show (-1 : ℤ) + 0 = -1 by ring)
            (p + 1) p p (by ring) (by ring),
          ← ΨcochR_comp, CochainComplex.mappingCone.inl_snd, ΨcochR_zero,
          CochainComplex.HomComplex.Cochain.zero_v]
      have hRF : ∀ p : ℤ, (Ψ.map (CochainComplex.mappingCone.inr φ)).f p ≫
          (ΨcochR F G ((CochainComplex.mappingCone.fst φ :
            CochainComplex.HomComplex.Cochain (CochainComplex.mappingCone φ) K 1))).v p (p + 1)
            (by ring) = 0 := by
        intro p
        rw [show (Ψ.map (CochainComplex.mappingCone.inr φ)).f p
              = (ΨcochR F G (CochainComplex.HomComplex.Cochain.ofHom
                  (CochainComplex.mappingCone.inr φ))).v p p (by ring) from by
            rw [ΨcochR_ofHom, CochainComplex.HomComplex.Cochain.ofHom_v],
          ← CochainComplex.HomComplex.Cochain.comp_v _ _ (show (0 : ℤ) + 1 = 1 by ring)
            p p (p + 1) (by ring) (by ring),
          ← ΨcochR_comp, CochainComplex.mappingCone.inr_fst, ΨcochR_zero,
          CochainComplex.HomComplex.Cochain.zero_v]
      have hRS : ∀ p : ℤ, (Ψ.map (CochainComplex.mappingCone.inr φ)).f p ≫
          (ΨcochR F G (CochainComplex.mappingCone.snd φ)).v p p (by ring)
            = 𝟙 ((Ψ.obj L).X p) := by
        intro p
        rw [show (Ψ.map (CochainComplex.mappingCone.inr φ)).f p
              = (ΨcochR F G (CochainComplex.HomComplex.Cochain.ofHom
                  (CochainComplex.mappingCone.inr φ))).v p p (by ring) from by
            rw [ΨcochR_ofHom, CochainComplex.HomComplex.Cochain.ofHom_v],
          ← CochainComplex.HomComplex.Cochain.comp_v _ _ (show (0 : ℤ) + 0 = 0 by ring)
            p p p (by ring) (by ring),
          ← ΨcochR_comp, CochainComplex.mappingCone.inr_snd, ΨcochR_ofHom,
          CochainComplex.HomComplex.Cochain.ofHom_v, CategoryTheory.Functor.map_id,
          HomologicalComplex.id_f]
      ext p
      rw [HomologicalComplex.comp_f, HomologicalComplex.id_f]
      apply CochainComplex.mappingCone.ext_from φ' (p + 1) p rfl
      · rw [← Category.assoc, CochainComplex.mappingCone.inl_v_desc_f]
        apply CochainComplex.mappingCone.ext_to φ' p (p + 1) rfl
        · rw [Category.assoc, CochainComplex.mappingCone.lift_f_fst_v,
            CochainComplex.HomComplex.Cocycle.mk_coe, hIF, Category.comp_id,
            CochainComplex.mappingCone.inl_v_fst_v]
        · rw [Category.assoc, CochainComplex.mappingCone.lift_f_snd_v,
            hIS, Category.comp_id, CochainComplex.mappingCone.inl_v_snd_v]
      · rw [← Category.assoc, CochainComplex.mappingCone.inr_f_desc_f]
        apply CochainComplex.mappingCone.ext_to φ' p (p + 1) rfl
        · rw [Category.assoc, CochainComplex.mappingCone.lift_f_fst_v,
            CochainComplex.HomComplex.Cocycle.mk_coe, hRF, Category.comp_id,
            CochainComplex.mappingCone.inr_f_fst_v]
        · rw [Category.assoc, CochainComplex.mappingCone.lift_f_snd_v,
            hRS, Category.comp_id, CochainComplex.mappingCone.inr_f_snd_v] }

/-- **C2R (triangle iso, right case).**  Flip of `bifunctorMapTriangleIso`:
upgrade `bifunctorMappingConeIsoR` to an iso of mapping-cone *triangles*.  The
shift square uses the SIGN-FREE `mapBifunctorShift₁Iso` (`ξ = bifunctorXiR`). -/
noncomputable def bifunctorMapTriangleIsoR
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ))
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    letI := map₂HomologicalComplex_flip_obj_additive F G
    ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj G).mapTriangle.obj (CochainComplex.mappingCone.triangle φ) ≅
      CochainComplex.mappingCone.triangle
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).flip.obj G).map φ) :=
  letI := map₂HomologicalComplex_flip_obj_additive F G
  letI Ψ := (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj G
  letI := bifunctorXiR F G
  CategoryTheory.Pretriangulated.Triangle.isoMk _ _
    (Iso.refl _) (Iso.refl _) (bifunctorMappingConeIsoR F G φ)
    (by
      dsimp [CochainComplex.mappingCone.triangle, Functor.mapTriangle, Pretriangulated.Triangle.mk]
      simp) (by
      have heq : CochainComplex.HomComplex.δ (-1) 0
            (ΨcochR F G (CochainComplex.mappingCone.inl φ)) =
          CochainComplex.HomComplex.Cochain.ofHom
            (Ψ.map φ ≫ Ψ.map (CochainComplex.mappingCone.inr φ)) := by
        rw [ΨcochR_δ, CochainComplex.mappingCone.δ_inl, ΨcochR_ofHom, Functor.map_comp]
      have hmap_inr :
          Ψ.map (CochainComplex.mappingCone.inr φ) ≫ (bifunctorMappingConeIsoR F G φ).hom =
            CochainComplex.mappingCone.inr (Ψ.map φ) := by
        rw [← CategoryTheory.Iso.eq_comp_inv]
        exact (CochainComplex.mappingCone.inr_desc (Ψ.map φ)
          (ΨcochR F G (CochainComplex.mappingCone.inl φ))
          (Ψ.map (CochainComplex.mappingCone.inr φ)) heq).symm
      dsimp [CochainComplex.mappingCone.triangle, Functor.mapTriangle, Pretriangulated.Triangle.mk]
      -- `dsimp` above now reduces `(Iso.refl _).hom` to `𝟙 _` on its own.
      rw [Category.id_comp]
      exact hmap_inr) (by
      dsimp [CochainComplex.mappingCone.triangle, Functor.mapTriangle, Pretriangulated.Triangle.mk]
      simp only [CategoryTheory.Functor.map_id, Category.comp_id]
      rw [← CategoryTheory.Iso.inv_comp_eq]
      ext n
      apply CochainComplex.mappingCone.ext_from (Ψ.map φ) (n + 1) n rfl
      · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
          ← Category.assoc]
        simp only [bifunctorMappingConeIsoR]
        rw [CochainComplex.mappingCone.inl_v_desc_f]
        apply HomologicalComplex.mapBifunctor.hom_ext
        intro p q hpq
        rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
          ΨcochR_v F G (CochainComplex.mappingCone.inl φ) (n + 1) n (by ring) p q hpq]
        simp only [Category.assoc]
        rw [Functor.flip_obj_map, Functor.map₂HomologicalComplex_map_app,
          HomologicalComplex.ι_mapBifunctorMap_assoc]
        simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
          ]
        rw [Functor.commShiftIso_map₂CochainComplex_flip_hom_app]
        have hpq' : p + q = n + 1 := hpq
        rw [CochainComplex.ι_mapBifunctorShift₁Iso_hom_f G (F := F) (K₁ := K) 1 (p + -1) q n
            (by omega) p (n + 1) (by omega) (by omega)]
        rw [CochainComplex.HomComplex.Cocycle.homOf_f,
          CochainComplex.HomComplex.Cocycle.rightShift_coe,
          CochainComplex.HomComplex.Cochain.rightShift_v
            _ 1 0 (by ring) (p + -1) (p + -1) (by ring) p (by ring),
          CochainComplex.HomComplex.Cocycle.homOf_f,
          CochainComplex.HomComplex.Cocycle.rightShift_coe,
          CochainComplex.HomComplex.Cochain.rightShift_v
            _ 1 0 (by ring) n n (by ring) (n + 1) (by ring)]
        simp only [CochainComplex.HomComplex.Cocycle.coe_neg,
          CochainComplex.HomComplex.Cochain.neg_v,
          Functor.map_neg, NatTrans.app_neg, Preadditive.neg_comp, Preadditive.comp_neg,
          Functor.map_comp, NatTrans.comp_app, Category.assoc]
        rw [Category.id_comp]
        have hcollapse :
            (F.map ((CochainComplex.mappingCone.inl φ).v p (p + -1) (by ring))).app (G.X q) ≫
              (F.map ((↑(CochainComplex.mappingCone.fst φ) :
                CochainComplex.HomComplex.Cochain (CochainComplex.mappingCone φ) K 1).v (p + -1) p
                  (by ring))).app (G.X q) ≫
                (F.map (K.shiftFunctorObjXIso 1 (p + -1) p (by ring)).inv).app (G.X q) ≫
                  (F.map (K.shiftFunctorObjXIso 1 (p + -1) p (by ring)).hom).app (G.X q)
              = 𝟙 _ := by
          rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← NatTrans.comp_app,
            ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
            Iso.inv_hom_id, Category.comp_id,
            CochainComplex.mappingCone.inl_v_fst_v φ p (p + -1) (by ring),
            CategoryTheory.Functor.map_id, CategoryTheory.NatTrans.id_app]
        rw [reassoc_of% hcollapse]
        -- These re-display the mapping-cone data over `mapBifunctorMap`. The left-hand sides
        -- must be spelled in the form the goal actually carries, `(F.map φ).app G`, rather
        -- than via `Ψ.map φ` (`Ψ = F.flip.obj G`), which no longer matches syntactically.
        rw [show CochainComplex.mappingCone.inl
              (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
                (ComplexShape.up ℤ)).map φ).app G) =
            CochainComplex.mappingCone.inl
              (HomologicalComplex.mapBifunctorMap φ (𝟙 G) F (ComplexShape.up ℤ)) from rfl,
          show CochainComplex.mappingCone.fst
              (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
                (ComplexShape.up ℤ)).map φ).app G) =
            CochainComplex.mappingCone.fst
              (HomologicalComplex.mapBifunctorMap φ (𝟙 G) F (ComplexShape.up ℤ)) from rfl]
        rw [CochainComplex.mappingCone.inl_v_fst_v_assoc
            (HomologicalComplex.mapBifunctorMap φ (𝟙 G) F (ComplexShape.up ℤ)) (n + 1) n (by ring)]
        rfl
      · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
          ← Category.assoc]
        simp only [bifunctorMappingConeIsoR]
        rw [CochainComplex.mappingCone.inr_f_desc_f]
        -- LHS: Ψ.map (inr φ) ≫ Ψ.map mor₃ = Ψ.map (inr φ ≫ mor₃) = Ψ.map 0 = 0
        -- The second factor now appears in unfolded `(F.map _).app G` form while the first is
        -- still `Ψ.map _`; re-display it so `← Functor.map_comp` can unify the two functors.
        rw [show ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ)).map
                ((-CochainComplex.mappingCone.fst φ).rightShift 1 0 (zero_add 1)).homOf).app G
            = Ψ.map ((-CochainComplex.mappingCone.fst φ).rightShift 1 0 (zero_add 1)).homOf
            from rfl]
        rw [← HomologicalComplex.comp_f, ← Functor.map_comp,
          show CochainComplex.mappingCone.inr φ ≫
              ((-CochainComplex.mappingCone.fst φ).rightShift 1 0 (zero_add 1)).homOf
            = (0 : L ⟶ K⟦(1 : ℤ)⟧) from
              CochainComplex.mappingCone.inr_triangleδ φ,
          Functor.map_zero]
        -- RHS: inr ≫ fst = 0
        rw [CochainComplex.HomComplex.Cocycle.homOf_f,
          CochainComplex.HomComplex.Cocycle.rightShift_coe,
          CochainComplex.HomComplex.Cochain.rightShift_v _ 1 0 (by ring) n n (by ring)
            (n + 1) (by ring),
          CochainComplex.HomComplex.Cocycle.coe_neg, CochainComplex.HomComplex.Cochain.neg_v]
        -- `inr_f_fst_v` needs `inr` and `fst` to name the same morphism; normalise the
        -- remaining unfolded `(F.map φ).app G` back to `Ψ.map φ` first.
        rw [show (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
              (ComplexShape.up ℤ)).map φ).app G) = Ψ.map φ from rfl]
        rw [HomologicalComplex.zero_f, Limits.zero_comp,
          Preadditive.neg_comp, Preadditive.comp_neg, ← Category.assoc,
          CochainComplex.mappingCone.inr_f_fst_v, Limits.zero_comp, neg_zero]
      )

/-- **Right-case kernel.**  Bifunctor mapping-cone triangle comparison (right
factor): `Φ(triangleh φ) ≅ triangleh (Ψ.map φ)` where `Ψ = Tot(F(-, G))`.
Mirror of `bifunctorPhi_mapTrianglehIso`. -/
noncomputable def bifunctorPhiR_mapTrianglehIso
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ))
    {K L : CochainComplex A ℤ} (φ : K ⟶ L) :
    letI := bifunctorXiR F G;
    (bifunctorPhiR F G).mapTriangle.obj (CochainComplex.mappingCone.triangleh φ) ≅
      CochainComplex.mappingCone.triangleh
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).flip.obj G).map φ) := by
  letI := bifunctorXiR F G
  letI := map₂HomologicalComplex_flip_obj_additive F G
  letI Ψ := (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).flip.obj G
  haveI : NatTrans.CommShift (bifunctorPhiRFactors F G).hom ℤ :=
    Quotient.liftCommShift_compatibility _ _ _ _
  exact
    ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).mapTriangleCompIso
          (bifunctorPhiR F G)).symm.app
        (CochainComplex.mappingCone.triangle φ) ≪≫
      (Functor.mapTriangleIso (bifunctorPhiRFactors F G)).app
          (CochainComplex.mappingCone.triangle φ) ≪≫
        (Ψ.mapTriangleCompIso (HomotopyCategory.quotient D (ComplexShape.up ℤ))).app
            (CochainComplex.mappingCone.triangle φ) ≪≫
          (HomotopyCategory.quotient D (ComplexShape.up ℤ)).mapTriangle.mapIso
            (bifunctorMapTriangleIsoR F G φ)

omit [HasZeroObject B] [HasBinaryBiproducts B] in
/-- **CRUX (right case).**  `Φ` (right factor), equipped with `ξ = bifunctorXiR`,
is triangulated.  Same argument as `bifunctorPhi_isTriangulated`, applied to the
additive functor `Tot(F(-, G))` of cochain complexes: every distinguished
triangle reduces to a mapping-cone triangle `triangleh φ`, and the bifunctor cone
comparison `Tot(F(cone φ, G)) ≅ cone (Tot(F(φ, G)))` (compatible with `ξ`)
exhibits `Φ(triangleh φ) ≅ triangleh (Ψ.map φ)` as distinguished. -/
theorem bifunctorPhiR_isTriangulated
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex B (ComplexShape.up ℤ)) :
    letI := bifunctorXiR F G; (bifunctorPhiR F G).IsTriangulated := by
  let := bifunctorXiR F G
  apply Functor.IsTriangulated.mk
  rintro T ⟨K, L, φ, ⟨e⟩⟩
  exact ⟨_, _, _, ⟨(bifunctorPhiR F G).mapTriangle.mapIso e ≪≫
    bifunctorPhiR_mapTrianglehIso F G φ⟩⟩

end Reduction

end Stacks.SheafOfModules.Tensor

end
