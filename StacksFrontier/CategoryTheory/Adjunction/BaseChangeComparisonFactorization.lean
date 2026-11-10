module

public import StacksFrontier.CategoryTheory.Adjunction.BaseChangeSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ProjectionFormula
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints

/-!
# The base change map of derived functors through the underived one

Consider a commutative square, read twice: once with underived functors `p` and their right
adjoints `q`, once with derived functors `L` and right adjoints `R`,

```
       p_f / L_f
    H_S -------→ H_X
     |            |
 p_g |            | p_g'
     v            v
    H_S' ------→ H_X'
       p_f' / L_f'
```

related by functors `Q : H → D` and comparisons `c_h : Q ⋙ L_h ⟶ p_h ⋙ Q` and
`η_h : q_h ⋙ Q ⟶ Q ⋙ R_h` compatible with the counits. Then the derived base change map
`L_f(R_g(QM)) ⟶ R_g'(L_f'(QM))`, between the comparisons, is the image under `Q` of the
underived base change map `p_f(q_g M) ⟶ q_g'(p_f' M)`. In particular it is invertible as soon as
the underived one and the four comparisons are.

## Main results

* `Stacks.CategoryTheory.BaseChange.map_factorization` — the derived base change map, between
  the comparisons, is the image under `Q` of the underived base change map.
* `Stacks.CategoryTheory.BaseChange.isIso_map_of_factorization` — the derived base change map is
  invertible as soon as the underived one and the four comparisons are.
* `Stacks.CategoryTheory.BaseChange.map_mapHomotopyCategory` — on homotopy categories, the base
  change map of the induced adjunctions is the degreewise base change map.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

open Stacks.AffineProjectionFormula

variable {HS HX HS' HX' DS DX DS' DX' : Type*}
  [Category HS] [Category HX] [Category HS'] [Category HX']
  [Category DS] [Category DX] [Category DS'] [Category DX']
  {pf : HS ⥤ HX} {pf' : HS' ⥤ HX'} {pg : HS ⥤ HS'} {pg' : HX ⥤ HX'}
  {qg : HS' ⥤ HS} {qg' : HX' ⥤ HX} {pc : HS ⥤ HX'}
  {Lf : DS ⥤ DX} {Lf' : DS' ⥤ DX'} {Lg : DS ⥤ DS'} {Lg' : DX ⥤ DX'}
  {Rg : DS' ⥤ DS} {Rg' : DX' ⥤ DX} {Lc : DS ⥤ DX'}
  (ag : pg ⊣ qg) (ag' : pg' ⊣ qg') (Ag : Lg ⊣ Rg) (Ag' : Lg' ⊣ Rg')
  (e₁ : pf ⋙ pg' ≅ pc) (e₂ : pg ⋙ pf' ≅ pc) (E₁ : Lf ⋙ Lg' ≅ Lc) (E₂ : Lg ⋙ Lf' ≅ Lc)
  {QS : HS ⥤ DS} {QX : HX ⥤ DX} {QS' : HS' ⥤ DS'} {QX' : HX' ⥤ DX'}
  (cf : QS ⋙ Lf ⟶ pf ⋙ QX) (cf' : QS' ⋙ Lf' ⟶ pf' ⋙ QX')
  (cg : QS ⋙ Lg ⟶ pg ⋙ QS') (cg' : QX ⋙ Lg' ⟶ pg' ⋙ QX')
  (ηg : qg ⋙ QS ⟶ QS' ⋙ Rg) (ηg' : qg' ⋙ QX ⟶ QX' ⋙ Rg')

/-- Transporting a compatibility `a.hom ≫ v = w ≫ F.map d.hom` along the inverse isomorphisms. -/
private theorem inv_comp_eq_of_hom_comp_eq {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y : D} {A B : C} (a : X ≅ Y) (d : A ≅ B) {Z : D} {v : Y ⟶ F.obj B}
    {w₁ : X ⟶ Z} {w₂ : Z ⟶ F.obj A} (h : a.hom ≫ v = w₁ ≫ w₂ ≫ F.map d.hom) :
    a.inv ≫ w₁ ≫ w₂ = v ≫ F.map d.inv := by
  rw [← cancel_epi a.hom, Iso.hom_inv_id_assoc, ← Category.assoc, h]
  simp only [Category.assoc, ← F.map_comp, Iso.hom_inv_id, F.map_id, Category.comp_id]

/-- **The derived base change map through the underived one.** If the comparisons are compatible
with the counits of `g` and `g'` (`hg`, `hg'`) and with the identifications of the two composites
around the square (`hsq`), then `L_f` of the comparison `η_g`, the derived base change map, and
`R_g'` of the comparison `c_f'` compose to `c_f`, then `Q` of the underived base change map, then
`η_g'`. -/
theorem map_factorization (M : HS')
    (hg : ∀ K : HS', Lg.map (ηg.app K) ≫ Ag.counit.app (QS'.obj K) =
      cg.app (qg.obj K) ≫ QS'.map (ag.counit.app K))
    (hg' : ∀ K : HX', Lg'.map (ηg'.app K) ≫ Ag'.counit.app (QX'.obj K) =
      cg'.app (qg'.obj K) ≫ QX'.map (ag'.counit.app K))
    (hsq : ∀ K : HS, (squareCompositeIso E₂ E₁).hom.app (QS.obj K) ≫
        Lg'.map (cf.app K) ≫ cg'.app (pf.obj K) =
      Lf'.map (cg.app K) ≫ cf'.app (pg.obj K) ≫ QX'.map ((squareCompositeIso e₂ e₁).hom.app K)) :
    Lf.map (ηg.app M) ≫ map Ag Ag' E₁ E₂ (QS'.obj M) ≫ Rg'.map (cf'.app M) =
      cf.app (qg.obj M) ≫ QX.map (map ag ag' e₁ e₂ M) ≫ ηg'.app (pf'.obj M) := by
  apply (Ag'.homEquiv _ _).symm.injective
  simp only [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
  have hb := homEquiv_symm_map ag ag' e₁ e₂ M
  rw [Adjunction.homEquiv_counit] at hb
  have hB := homEquiv_symm_map Ag Ag' E₁ E₂ (QS'.obj M)
  rw [Adjunction.homEquiv_counit] at hB
  have hcn := cg'.naturality (map ag ag' e₁ e₂ M)
  simp only [Functor.comp_map, Functor.comp_obj] at hcn
  have hcf' := cf'.naturality (ag.counit.app M)
  simp only [Functor.comp_map, Functor.comp_obj, Functor.id_obj] at hcf'
  have hε := Ag'.counit.naturality (cf'.app M)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hε
  have hSq := (squareCompositeIso E₂ E₁).inv.naturality (ηg.app M)
  simp only [Functor.comp_map, Functor.comp_obj, squareCompositeIso_inv_app,
    Category.assoc] at hSq
  have hsq' : (squareCompositeIso E₂ E₁).inv.app (QS.obj (qg.obj M)) ≫
      Lf'.map (cg.app (qg.obj M)) ≫ cf'.app (pg.obj (qg.obj M)) =
      (Lg'.map (cf.app (qg.obj M)) ≫ cg'.app (pf.obj (qg.obj M))) ≫
        QX'.map ((squareCompositeIso e₂ e₁).inv.app (qg.obj M)) := by
    exact inv_comp_eq_of_hom_comp_eq QX' ((squareCompositeIso E₂ E₁).app (QS.obj (qg.obj M)))
      ((squareCompositeIso e₂ e₁).app (qg.obj M))
      (hsq (qg.obj M))
  simp only [squareCompositeIso_inv_app, Category.assoc] at hsq'
  calc Lg'.map (Lf.map (ηg.app M)) ≫ Lg'.map (map Ag Ag' E₁ E₂ (QS'.obj M)) ≫
        Lg'.map (Rg'.map (cf'.app M)) ≫ Ag'.counit.app (QX'.obj (pf'.obj M))
      = Lg'.map (Lf.map (ηg.app M)) ≫ (Lg'.map (map Ag Ag' E₁ E₂ (QS'.obj M)) ≫
          Ag'.counit.app (Lf'.obj (QS'.obj M))) ≫ cf'.app M := by
        rw [hε]; simp only [Category.assoc]
    _ = (E₁.hom.app (QS.obj (qg.obj M)) ≫ E₂.inv.app (QS.obj (qg.obj M))) ≫
          Lf'.map (Lg.map (ηg.app M) ≫ Ag.counit.app (QS'.obj M)) ≫ cf'.app M := by
        rw [hB]; simp only [Category.assoc]; rw [reassoc_of% hSq]
        simp only [Functor.map_comp, Category.assoc]
    _ = (E₁.hom.app (QS.obj (qg.obj M)) ≫ E₂.inv.app (QS.obj (qg.obj M))) ≫
          Lf'.map (cg.app (qg.obj M)) ≫ cf'.app (pg.obj (qg.obj M)) ≫
            QX'.map (pf'.map (ag.counit.app M)) := by
        rw [hg, Functor.map_comp]; simp only [Category.assoc]; rw [hcf']
    _ = Lg'.map (cf.app (qg.obj M)) ≫ cg'.app (pf.obj (qg.obj M)) ≫
          QX'.map (e₁.hom.app (qg.obj M) ≫ e₂.inv.app (qg.obj M) ≫ pf'.map (ag.counit.app M)) := by
        simp only [Category.assoc]
        rw [reassoc_of% hsq']
        simp only [Functor.map_comp, Category.assoc]
    _ = _ := by
        rw [← hb, Functor.map_comp, ← reassoc_of% hcn, ← hg' (pf'.obj M)]
        rfl

/-- **Invertibility of the derived base change map from the underived one.** Under the
hypotheses of `map_factorization`, if the comparisons `η_g` at `M`, `c_f'` at `M`, `c_f` at
`q_g M`, `η_g'` at `p_f' M` and the underived base change map at `M` are invertible, so is the
derived base change map at `QM`. -/
theorem isIso_map_of_factorization (M : HS')
    (hg : ∀ K : HS', Lg.map (ηg.app K) ≫ Ag.counit.app (QS'.obj K) =
      cg.app (qg.obj K) ≫ QS'.map (ag.counit.app K))
    (hg' : ∀ K : HX', Lg'.map (ηg'.app K) ≫ Ag'.counit.app (QX'.obj K) =
      cg'.app (qg'.obj K) ≫ QX'.map (ag'.counit.app K))
    (hsq : ∀ K : HS, (squareCompositeIso E₂ E₁).hom.app (QS.obj K) ≫
        Lg'.map (cf.app K) ≫ cg'.app (pf.obj K) =
      Lf'.map (cg.app K) ≫ cf'.app (pg.obj K) ≫ QX'.map ((squareCompositeIso e₂ e₁).hom.app K))
    [IsIso (ηg.app M)] [IsIso (cf'.app M)] [IsIso (cf.app (qg.obj M))]
    [IsIso (ηg'.app (pf'.obj M))] [IsIso (map ag ag' e₁ e₂ M)] :
    IsIso (map Ag Ag' E₁ E₂ (QS'.obj M)) := by
  have h := map_factorization ag ag' Ag Ag' e₁ e₂ E₁ E₂ cf cf' cg cg' ηg ηg' M hg hg' hsq
  have : IsIso (Lf.map (ηg.app M) ≫ map Ag Ag' E₁ E₂ (QS'.obj M) ≫ Rg'.map (cf'.app M)) := by
    rw [h]; infer_instance
  have : IsIso (map Ag Ag' E₁ E₂ (QS'.obj M) ≫ Rg'.map (cf'.app M)) :=
    IsIso.of_isIso_comp_left (Lf.map (ηg.app M)) _
  exact IsIso.of_isIso_comp_right _ (Rg'.map (cf'.app M))

/-- If two identifications `C₁` and `C₂` of the composites around the square are each compatible
with a comparison `c` (`h₁`, `h₂`), then `squareCompositeIso C₂ C₁` is compatible with the
comparisons around the square. -/
theorem squareCompositeIso_comparison {L : DS ⥤ DX'} {p : HS ⥤ HX'}
    (C₁ : Lf ⋙ Lg' ≅ L) (C₂ : Lg ⋙ Lf' ≅ L) (D₁ : pf ⋙ pg' ≅ p) (D₂ : pg ⋙ pf' ≅ p)
    (c : QS ⋙ L ⟶ p ⋙ QX') (K : HS)
    (h₁ : C₁.hom.app (QS.obj K) ≫ c.app K =
      Lg'.map (cf.app K) ≫ cg'.app (pf.obj K) ≫ QX'.map (D₁.hom.app K))
    (h₂ : C₂.hom.app (QS.obj K) ≫ c.app K =
      Lf'.map (cg.app K) ≫ cf'.app (pg.obj K) ≫ QX'.map (D₂.hom.app K)) :
    (squareCompositeIso C₂ C₁).hom.app (QS.obj K) ≫ Lg'.map (cf.app K) ≫ cg'.app (pf.obj K) =
      Lf'.map (cg.app K) ≫ cf'.app (pg.obj K) ≫
        QX'.map ((squareCompositeIso D₂ D₁).hom.app K) := by
  have k₁ : C₁.inv.app (QS.obj K) ≫ Lg'.map (cf.app K) ≫ cg'.app (pf.obj K) =
      c.app K ≫ QX'.map (D₁.inv.app K) := by
    exact inv_comp_eq_of_hom_comp_eq QX' (C₁.app (QS.obj K)) (D₁.app K)
      h₁
  simp only [squareCompositeIso_hom_app, Category.assoc, Functor.map_comp]
  rw [k₁, reassoc_of% h₂]

/-- Compatibility of an identification with comparisons survives composing with a transport
compatible with the comparisons. -/
theorem comparison_trans {L₀ L : DS ⥤ DX'} {p₀ p : HS ⥤ HX'} (C₀ : Lf ⋙ Lg' ≅ L₀) (T : L₀ ≅ L)
    (D₀ : pf ⋙ pg' ≅ p₀) (t : p₀ ≅ p) (c₀ : QS ⋙ L₀ ⟶ p₀ ⋙ QX') (c : QS ⋙ L ⟶ p ⋙ QX') (K : HS)
    (h₀ : C₀.hom.app (QS.obj K) ≫ c₀.app K =
      Lg'.map (cf.app K) ≫ cg'.app (pf.obj K) ≫ QX'.map (D₀.hom.app K))
    (hT : T.hom.app (QS.obj K) ≫ c.app K = c₀.app K ≫ QX'.map (t.hom.app K)) :
    (C₀ ≪≫ T).hom.app (QS.obj K) ≫ c.app K =
      Lg'.map (cf.app K) ≫ cg'.app (pf.obj K) ≫ QX'.map ((D₀ ≪≫ t).hom.app K) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc, Functor.map_comp]
  rw [hT, reassoc_of% h₀]

/-- The derived base change map at `QM` is invertible under the hypotheses of
`isIso_map_of_factorization`, with the compatibility around the square replaced by the
compatibility of each identification of a composite with a comparison `c` along `Lc`. -/
theorem isIso_map_of_factorization_of_comparison (M : HS')
    (hg : ∀ K : HS', Lg.map (ηg.app K) ≫ Ag.counit.app (QS'.obj K) =
      cg.app (qg.obj K) ≫ QS'.map (ag.counit.app K))
    (hg' : ∀ K : HX', Lg'.map (ηg'.app K) ≫ Ag'.counit.app (QX'.obj K) =
      cg'.app (qg'.obj K) ≫ QX'.map (ag'.counit.app K))
    (c : QS ⋙ Lc ⟶ pc ⋙ QX')
    (h₁ : ∀ K : HS, E₁.hom.app (QS.obj K) ≫ c.app K =
      Lg'.map (cf.app K) ≫ cg'.app (pf.obj K) ≫ QX'.map (e₁.hom.app K))
    (h₂ : ∀ K : HS, E₂.hom.app (QS.obj K) ≫ c.app K =
      Lf'.map (cg.app K) ≫ cf'.app (pg.obj K) ≫ QX'.map (e₂.hom.app K))
    [IsIso (ηg.app M)] [IsIso (cf'.app M)] [IsIso (cf.app (qg.obj M))]
    [IsIso (ηg'.app (pf'.obj M))] [IsIso (map ag ag' e₁ e₂ M)] :
    IsIso (map Ag Ag' E₁ E₂ (QS'.obj M)) :=
  isIso_map_of_factorization ag ag' Ag Ag' e₁ e₂ E₁ E₂ cf cf' cg cg' ηg ηg' M hg hg'
    (fun K => squareCompositeIso_comparison cf cf' cg cg' E₁ E₂ e₁ e₂ c K (h₁ K) (h₂ K))

/-- The base change map depends on the identifications of the two composites only through the
comparison `eg.hom ≫ ef.inv` of the composites. -/
theorem map_eq_of_hom_comp_inv_eq {A B A' B' : Type*} [Category A] [Category B] [Category A']
    [Category B'] {Lf : A ⥤ B} {Rf : B ⥤ A} {Lf' : A' ⥤ B'} {Rf' : B' ⥤ A'}
    {Lg : A ⥤ A'} {Lg' : B ⥤ B'} {Lc Lc' : A ⥤ B'}
    (adjf : Lf ⊣ Rf) (adjf' : Lf' ⊣ Rf') (eg : Lg ⋙ Lf' ≅ Lc) (ef : Lf ⋙ Lg' ≅ Lc)
    (eg' : Lg ⋙ Lf' ≅ Lc') (ef' : Lf ⋙ Lg' ≅ Lc') (h : eg.hom ≫ ef.inv = eg'.hom ≫ ef'.inv)
    (K : B) : map adjf adjf' eg ef K = map adjf adjf' eg' ef' K := by
  simp only [map, twoSquare, pullbackComparison, h]

section Homotopy

variable {ι : Type*} {A B A' B' : Type*} [Category A] [Category B] [Category A'] [Category B']
  [Preadditive A] [Preadditive B] [Preadditive A'] [Preadditive B']
  {Pf : A ⥤ B} {Qf : B ⥤ A} {Pf' : A' ⥤ B'} {Qf' : B' ⥤ A'}
  {Pg : A ⥤ A'} {Pg' : B ⥤ B'} {Pc : A ⥤ B'}
  [Pf.Additive] [Qf.Additive] [Pf'.Additive] [Qf'.Additive] [Pg.Additive] [Pg'.Additive]
  [Pc.Additive]
  (af : Pf ⊣ Qf) (af' : Pf' ⊣ Qf') (e₁ : Pg ⋙ Pf' ≅ Pc) (e₂ : Pf ⋙ Pg' ≅ Pc)
  (c : ComplexShape ι)

/-- **The base change map on homotopy categories is degreewise.** For the adjunctions induced on
homotopy categories and the induced identifications of the composites, the base change map at
the class of a complex `K` is the class of the degreewise base change map. -/
theorem map_mapHomotopyCategory (K : HomologicalComplex B c) :
    map (Adjunction.mapHomotopyCategoryAdjunction af c)
        (Adjunction.mapHomotopyCategoryAdjunction af' c)
        (Functor.mapHomotopyCategoryCompIso e₁ c) (Functor.mapHomotopyCategoryCompIso e₂ c)
        ((HomotopyCategory.quotient B c).obj K) =
      (HomotopyCategory.quotient A' c).map
        ((NatTrans.mapHomologicalComplex (twoSquare af af' e₁ e₂) c).app K) := by
  apply ((Adjunction.mapHomotopyCategoryAdjunction af' c).homEquiv _ _).symm.injective
  rw [homEquiv_symm_map]
  change (HomotopyCategory.quotient B' c).map
      ((NatTrans.mapHomologicalComplex e₁.hom c).app ((Qf.mapHomologicalComplex c).obj K) ≫
        (NatTrans.mapHomologicalComplex e₂.inv c).app ((Qf.mapHomologicalComplex c).obj K) ≫
          (Pg'.mapHomologicalComplex c).map
            ((Adjunction.mapHomologicalComplexAdjunction af c).counit.app K)) =
    (HomotopyCategory.quotient B' c).map
      (((Adjunction.mapHomologicalComplexAdjunction af' c).homEquiv
        ((Pg.mapHomologicalComplex c).obj ((Qf.mapHomologicalComplex c).obj K))
        ((Pg'.mapHomologicalComplex c).obj K)).symm
          ((NatTrans.mapHomologicalComplex (twoSquare af af' e₁ e₂) c).app K))
  congr 1
  ext n
  have h := homEquiv_symm_map af af' e₁ e₂ (K.X n)
  rw [Adjunction.homEquiv_counit] at h
  rw [Adjunction.homEquiv_counit]
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f,
    Functor.mapHomologicalComplex_map_f, Functor.mapHomologicalComplex_obj_X]
  exact h.symm

end Homotopy

end Stacks.CategoryTheory.BaseChange
