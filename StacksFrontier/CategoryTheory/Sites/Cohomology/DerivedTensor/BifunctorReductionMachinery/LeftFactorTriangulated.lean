module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery.TotalComplexDescent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The left-factor functor is triangulated

Part of
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BifunctorReductionMachinery`:
the mapping-cone and triangle isomorphisms for
`Tot(F(G, -))` (fixed complex in the left factor) and `bifunctorPhi_isTriangulated`.
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

/-- **C1f (assembly).**  Assemble the cone-object iso from `mappingCone.lift`
and `mappingCone.desc` exactly as `mapHomologicalComplexIso` does, with `Ψcoch`
in place of `Cochain.map`.  The `hom` is
`mappingCone.lift _ (Ψcoch ↑(fst φ)) (Ψcoch (snd φ)) _`, the `inv` is
`mappingCone.desc _ (Ψcoch (inl φ)) (Ψ.map (inr φ)) _`; the cocycle/cone
equations and the two round-trip identities follow from C1b–C1e via
`mapBifunctor.hom_ext` + the `lift`/`desc` `f`-lemmas. -/
noncomputable def bifunctorMappingConeIso
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ))
    {K L : CochainComplex B ℤ} (φ : K ⟶ L) :
    ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G).obj (CochainComplex.mappingCone φ) ≅
      CochainComplex.mappingCone
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj G).map φ) :=
  letI Ψ := (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G
  letI φ' := Ψ.map φ
  haveI hcofib : HomologicalComplex.HasHomotopyCofiber φ' := inferInstance
  -- Local additivity facts for the bifunctor cochain transport `Ψcoch`
  -- (analogues of `Cochain.map_zero` / additivity of `Cochain.map`).
  have Ψcoch_zero : ∀ {X Y : CochainComplex B ℤ} {n : ℤ},
      Ψcoch F G (0 : CochainComplex.HomComplex.Cochain X Y n) = 0 := by
    intro X Y n
    apply CochainComplex.HomComplex.Cochain.ext
    intro a a' h
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpq2 : p + q = a := hpq
    rw [Ψcoch_v F G (0 : CochainComplex.HomComplex.Cochain X Y n) a a' h p q hpq2]
    simp
  have Ψcoch_neg : ∀ {X Y : CochainComplex B ℤ} {n : ℤ}
      (z : CochainComplex.HomComplex.Cochain X Y n),
      Ψcoch F G (-z) = -(Ψcoch F G z) := by
    intro X Y n z
    apply CochainComplex.HomComplex.Cochain.ext
    intro a a' h
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpq2 : p + q = a := hpq
    rw [Ψcoch_v F G (-z) a a' h p q hpq2]
    simp only [CochainComplex.HomComplex.Cochain.neg_v, Preadditive.comp_neg]
    rw [Ψcoch_v F G z a a' h p q hpq2]
    simp
  have Ψcoch_add : ∀ {X Y : CochainComplex B ℤ} {n : ℤ}
      (z₁ z₂ : CochainComplex.HomComplex.Cochain X Y n),
      Ψcoch F G (z₁ + z₂) = Ψcoch F G z₁ + Ψcoch F G z₂ := by
    intro X Y n z₁ z₂
    apply CochainComplex.HomComplex.Cochain.ext
    intro a a' h
    apply HomologicalComplex.mapBifunctor.hom_ext
    intro p q hpq
    have hpq2 : p + q = a := hpq
    rw [Ψcoch_v F G (z₁ + z₂) a a' h p q hpq2]
    simp only [CochainComplex.HomComplex.Cochain.add_v, Preadditive.comp_add,
      Functor.map_add]
    rw [Ψcoch_v F G z₁ a a' h p q hpq2, Ψcoch_v F G z₂ a a' h p q hpq2]
    simp [smul_add]
  { hom := CochainComplex.mappingCone.lift φ'
      (CochainComplex.HomComplex.Cocycle.mk
        (Ψcoch F G (↑(CochainComplex.mappingCone.fst φ))) 2 (by norm_num)
        (by rw [Ψcoch_δ, CochainComplex.HomComplex.Cocycle.δ_eq_zero, Ψcoch_zero]))
      (Ψcoch F G (CochainComplex.mappingCone.snd φ))
      (by
        rw [CochainComplex.HomComplex.Cocycle.mk_coe, Ψcoch_δ,
          CochainComplex.mappingCone.δ_snd]
        change Ψcoch F G _ +
          (Ψcoch F G _).comp (CochainComplex.HomComplex.Cochain.ofHom φ') _ = 0
        rw [show CochainComplex.HomComplex.Cochain.ofHom φ' = Ψcoch F G
              (CochainComplex.HomComplex.Cochain.ofHom φ) from (Ψcoch_ofHom F G φ).symm,
          ← Ψcoch_comp, Ψcoch_neg]
        abel)
    inv := CochainComplex.mappingCone.desc φ'
      (Ψcoch F G (CochainComplex.mappingCone.inl φ))
      (Ψ.map (CochainComplex.mappingCone.inr φ))
      (by
        rw [Ψcoch_δ, CochainComplex.mappingCone.δ_inl, Ψcoch_ofHom,
          Functor.map_comp])
    hom_inv_id := by
      ext p
      rw [HomologicalComplex.comp_f, HomologicalComplex.id_f,
        CochainComplex.mappingCone.lift_desc_f φ' _ _ _ _ _ _ p (p + 1) rfl,
        CochainComplex.HomComplex.Cocycle.mk_coe]
      -- Turn the `Ψ.map (inr φ)` factor into `Ψcoch (ofHom (inr φ))` degreewise.
      have hinr : (Ψ.map (CochainComplex.mappingCone.inr φ)).f p
          = (Ψcoch F G (CochainComplex.HomComplex.Cochain.ofHom
              (CochainComplex.mappingCone.inr φ))).v p p (by ring) := by
        rw [Ψcoch_ofHom, CochainComplex.HomComplex.Cochain.ofHom_v]
      rw [hinr]
      -- Recombine the two terms into `Ψcoch` of a single cochain via `comp_v`.
      rw [← CochainComplex.HomComplex.Cochain.comp_v _ _ (show (1 : ℤ) + (-1) = 0 by ring)
            p (p + 1) p rfl (by ring),
        ← CochainComplex.HomComplex.Cochain.comp_v _ _ (show (0 : ℤ) + 0 = 0 by ring)
            p p p (by ring) (by ring),
        ← Ψcoch_comp, ← Ψcoch_comp]
      rw [← CochainComplex.HomComplex.Cochain.add_v]
      rw [← Ψcoch_add, CochainComplex.mappingCone.id φ, Ψcoch_ofHom,
        CochainComplex.HomComplex.Cochain.ofHom_v]
      rw [CategoryTheory.Functor.map_id, HomologicalComplex.id_f]
    inv_hom_id := by
      -- Four transported `inl/inr` vs `fst/snd` identities (mirroring
      -- `inl_v_fst_v`, `inl_v_snd_v`, `inr_f_fst_v`, `inr_f_snd_v` for `cone φ`).
      have hIF : ∀ p : ℤ, (Ψcoch F G (CochainComplex.mappingCone.inl φ)).v (p + 1) p (by ring) ≫
          (Ψcoch F G ((CochainComplex.mappingCone.fst φ :
            CochainComplex.HomComplex.Cochain (CochainComplex.mappingCone φ) K 1))).v p (p + 1)
              (by ring)
            = 𝟙 ((Ψ.obj K).X (p + 1)) := by
        intro p
        rw [← CochainComplex.HomComplex.Cochain.comp_v _ _ (show (-1 : ℤ) + 1 = 0 by ring)
            (p + 1) p (p + 1) (by ring) (by ring),
          ← Ψcoch_comp, CochainComplex.mappingCone.inl_fst, Ψcoch_ofHom,
          CochainComplex.HomComplex.Cochain.ofHom_v, CategoryTheory.Functor.map_id,
          HomologicalComplex.id_f]
      have hIS : ∀ p : ℤ, (Ψcoch F G (CochainComplex.mappingCone.inl φ)).v (p + 1) p (by ring) ≫
          (Ψcoch F G (CochainComplex.mappingCone.snd φ)).v p p (by ring) = 0 := by
        intro p
        rw [← CochainComplex.HomComplex.Cochain.comp_v _ _ (show (-1 : ℤ) + 0 = -1 by ring)
            (p + 1) p p (by ring) (by ring),
          ← Ψcoch_comp, CochainComplex.mappingCone.inl_snd, Ψcoch_zero,
          CochainComplex.HomComplex.Cochain.zero_v]
      have hRF : ∀ p : ℤ, (Ψ.map (CochainComplex.mappingCone.inr φ)).f p ≫
          (Ψcoch F G ((CochainComplex.mappingCone.fst φ :
            CochainComplex.HomComplex.Cochain (CochainComplex.mappingCone φ) K 1))).v p (p + 1)
            (by ring) = 0 := by
        intro p
        rw [show (Ψ.map (CochainComplex.mappingCone.inr φ)).f p
              = (Ψcoch F G (CochainComplex.HomComplex.Cochain.ofHom
                  (CochainComplex.mappingCone.inr φ))).v p p (by ring) from by
            rw [Ψcoch_ofHom, CochainComplex.HomComplex.Cochain.ofHom_v],
          ← CochainComplex.HomComplex.Cochain.comp_v _ _ (show (0 : ℤ) + 1 = 1 by ring)
            p p (p + 1) (by ring) (by ring),
          ← Ψcoch_comp, CochainComplex.mappingCone.inr_fst, Ψcoch_zero,
          CochainComplex.HomComplex.Cochain.zero_v]
      have hRS : ∀ p : ℤ, (Ψ.map (CochainComplex.mappingCone.inr φ)).f p ≫
          (Ψcoch F G (CochainComplex.mappingCone.snd φ)).v p p (by ring)
            = 𝟙 ((Ψ.obj L).X p) := by
        intro p
        rw [show (Ψ.map (CochainComplex.mappingCone.inr φ)).f p
              = (Ψcoch F G (CochainComplex.HomComplex.Cochain.ofHom
                  (CochainComplex.mappingCone.inr φ))).v p p (by ring) from by
            rw [Ψcoch_ofHom, CochainComplex.HomComplex.Cochain.ofHom_v],
          ← CochainComplex.HomComplex.Cochain.comp_v _ _ (show (0 : ℤ) + 0 = 0 by ring)
            p p p (by ring) (by ring),
          ← Ψcoch_comp, CochainComplex.mappingCone.inr_snd, Ψcoch_ofHom,
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

/-- **C2 (triangle iso).**  Upgrade C1 (`bifunctorMappingConeIso`) to an iso of the
standard mapping-cone *triangles* at the complex level:
`Ψ.mapTriangle.obj (mappingCone.triangle φ) ≅ mappingCone.triangle (Ψ.map φ)`.

Mirror `CochainComplex.mappingCone.mapTriangleIso`: build `Triangle.isoMk` with
component isos `𝟙 (Ψ K)`, `𝟙 (Ψ L)`, and `bifunctorMappingConeIso F G φ` (on
`obj₁,obj₂,obj₃`), and verify the three commuting squares:
  - `mor₁ = Ψ.map (mappingCone.inr ?)` / the chain map `K → L`: trivial since the
    first two components are identities and the cone iso is compatible with `inr`
    (the bifunctor analogue of `mappingCone.map_inr`);
  - `mor₂` (the `inr` into the cone): compatibility of `bifunctorMappingConeIso`
    with `inr` (`map_inr` analogue);
  - `mor₃` (the connecting map `cone φ → K⟦1⟧`, built from `fst φ`, a COCYCLE):
    this is the only square using the shift — it needs the compatibility of
    `bifunctorMappingConeIso` with the connecting cocycle `fst`, i.e. the
    `Ψ.CommShift ℤ` datum (`bifunctorXi`) and the `map_δ` analogue.
Needs `Ψ.CommShift ℤ` in scope (= `bifunctorXi F G`).
DEPENDENCY: built from C1 (`bifunctorMappingConeIso`); no Mathlib support. -/
noncomputable def bifunctorMapTriangleIso
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ))
    {K L : CochainComplex B ℤ} (φ : K ⟶ L) :
    letI := map₂HomologicalComplex_obj_additive F G
    ((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G).mapTriangle.obj (CochainComplex.mappingCone.triangle φ) ≅
      CochainComplex.mappingCone.triangle
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
          (ComplexShape.up ℤ)).obj G).map φ) :=
  letI := map₂HomologicalComplex_obj_additive F G
  letI Ψ := (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G
  letI := bifunctorXi F G
  CategoryTheory.Pretriangulated.Triangle.isoMk _ _
    (Iso.refl _) (Iso.refl _) (bifunctorMappingConeIso F G φ)
    (by
      dsimp [CochainComplex.mappingCone.triangle, Functor.mapTriangle, Pretriangulated.Triangle.mk]
      simp) (by
      have heq : CochainComplex.HomComplex.δ (-1) 0
            (Ψcoch F G (CochainComplex.mappingCone.inl φ)) =
          CochainComplex.HomComplex.Cochain.ofHom
            (Ψ.map φ ≫ Ψ.map (CochainComplex.mappingCone.inr φ)) := by
        rw [Ψcoch_δ, CochainComplex.mappingCone.δ_inl, Ψcoch_ofHom, Functor.map_comp]
      have hmap_inr :
          Ψ.map (CochainComplex.mappingCone.inr φ) ≫ (bifunctorMappingConeIso F G φ).hom =
            CochainComplex.mappingCone.inr (Ψ.map φ) := by
        rw [← CategoryTheory.Iso.eq_comp_inv]
        exact (CochainComplex.mappingCone.inr_desc (Ψ.map φ)
          (Ψcoch F G (CochainComplex.mappingCone.inl φ))
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
        simp only [bifunctorMappingConeIso]
        rw [CochainComplex.mappingCone.inl_v_desc_f]
        apply HomologicalComplex.mapBifunctor.hom_ext
        intro p q hpq
        rw [← Category.assoc, ← Category.assoc, ← Category.assoc,
          Ψcoch_v F G (CochainComplex.mappingCone.inl φ) (n + 1) n (by ring) p q hpq]
        -- LHS: push ι through mapBifunctorMap and the shift iso
        rw [Linear.units_smul_comp, Category.assoc, Category.assoc,
          Functor.map₂HomologicalComplex_obj_map F (ComplexShape.up ℤ) (ComplexShape.up ℤ)
            (ComplexShape.up ℤ) G _,
          HomologicalComplex.ι_mapBifunctorMap]
        simp only [HomologicalComplex.id_f, CategoryTheory.Functor.map_id,
          CategoryTheory.NatTrans.id_app, Category.id_comp]
        rw [Functor.commShiftIso_map₂CochainComplex_hom_app]
        have hpq' : p + q = n + 1 := hpq
        rw [Linear.units_smul_comp, Category.assoc, Category.assoc,
          CochainComplex.ι_mapBifunctorShift₂Iso_hom_f G K F 1 p (q + -1) n
            (by omega) q (n + 1) (by omega) (by omega)]
        -- compute the rightShift cochains on both sides
        rw [CochainComplex.HomComplex.Cocycle.homOf_f,
          CochainComplex.HomComplex.Cocycle.rightShift_coe,
          CochainComplex.HomComplex.Cochain.rightShift_v
            _ 1 0 (by ring) (q + -1) (q + -1) (by ring) q (by ring),
          CochainComplex.HomComplex.Cocycle.homOf_f,
          CochainComplex.HomComplex.Cocycle.rightShift_coe,
          CochainComplex.HomComplex.Cochain.rightShift_v
            _ 1 0 (by ring) n n (by ring) (n + 1) (by ring)]
        -- cancel the shift isos under F, combine signs, use inl_v_fst_v
        simp only [CochainComplex.HomComplex.Cocycle.coe_neg,
          CochainComplex.HomComplex.Cochain.neg_v,
          Functor.map_neg, Linear.comp_units_smul,
          Preadditive.neg_comp, Preadditive.comp_neg, Functor.map_comp, Category.assoc]
        have hcollapse :
            (F.obj (G.X p)).map ((CochainComplex.mappingCone.inl φ).v q (q + -1) (by ring)) ≫
              (F.obj (G.X p)).map ((↑(CochainComplex.mappingCone.fst φ) :
                CochainComplex.HomComplex.Cochain (CochainComplex.mappingCone φ) K 1).v (q + -1) q
                  (by ring)) ≫
                (F.obj (G.X p)).map (K.shiftFunctorObjXIso 1 (q + -1) q (by ring)).inv ≫
                  (F.obj (G.X p)).map (K.shiftFunctorObjXIso 1 (q + -1) q (by ring)).hom
              = 𝟙 _ := by
          rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp,
            Iso.inv_hom_id, Category.comp_id,
            CochainComplex.mappingCone.inl_v_fst_v φ q (q + -1) (by ring),
            CategoryTheory.Functor.map_id]
        rw [reassoc_of% hcollapse]
        rw [show (CochainComplex.mappingCone.inl (Ψ.map φ)) =
            CochainComplex.mappingCone.inl
              (HomologicalComplex.mapBifunctorMap (𝟙 G) φ F (ComplexShape.up ℤ)) from rfl,
          show (CochainComplex.mappingCone.fst (Ψ.map φ)) =
            CochainComplex.mappingCone.fst
              (HomologicalComplex.mapBifunctorMap (𝟙 G) φ F (ComplexShape.up ℤ)) from rfl]
        rw [CochainComplex.mappingCone.inl_v_fst_v_assoc
            (HomologicalComplex.mapBifunctorMap (𝟙 G) φ F (ComplexShape.up ℤ)) (n + 1) n (by ring)]
        rw [smul_smul, ← Int.negOnePow_add]
        ring_nf
        rw [Int.negOnePow_zero, one_smul]
        rfl
      · rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, ← Category.assoc,
          ← Category.assoc]
        simp only [bifunctorMappingConeIso]
        rw [CochainComplex.mappingCone.inr_f_desc_f]
        -- LHS: Ψ.map (inr φ) ≫ Ψ.map mor₃ = Ψ.map (inr φ ≫ mor₃) = Ψ.map 0 = 0
        rw [← HomologicalComplex.comp_f, ← Functor.map_comp,
          show CochainComplex.mappingCone.inr φ ≫
              ((-CochainComplex.mappingCone.fst φ).rightShift 1 0 (zero_add 1)).homOf
            = (0 : L ⟶ K⟦(1 : ℤ)⟧) from
              CochainComplex.mappingCone.inr_triangleδ φ,
          CategoryTheory.Functor.map_zero, HomologicalComplex.zero_f, Limits.zero_comp]
        -- RHS: inr ≫ fst = 0
        rw [CochainComplex.HomComplex.Cocycle.homOf_f,
          CochainComplex.HomComplex.Cocycle.rightShift_coe,
          CochainComplex.HomComplex.Cochain.rightShift_v _ 1 0 (by ring) n n (by ring)
            (n + 1) (by ring),
          CochainComplex.HomComplex.Cocycle.coe_neg, CochainComplex.HomComplex.Cochain.neg_v]
        rw [Preadditive.neg_comp, Preadditive.comp_neg, ← Category.assoc,
          CochainComplex.mappingCone.inr_f_fst_v, Limits.zero_comp, neg_zero]
      )

/-- **C3 (homotopy assembly).**  Assemble `bifunctorPhi_mapTrianglehIso` from C2
(`bifunctorMapTriangleIso`) by transporting across the homotopy quotient via
`bifunctorPhiFactors`, mirroring the body of
`#print CochainComplex.mappingCone.mapTrianglehIso`:
```
(quotient.mapTriangleCompIso (bifunctorPhi F G)).symm.app (triangle φ) ≪≫
(Functor.mapTriangleIso (bifunctorPhiFactors F G)).app (triangle φ) ≪≫
(Ψ.mapTriangleCompIso quotient).app (triangle φ) ≪≫
quotient.mapTriangle.mapIso (bifunctorMapTriangleIso F G φ)
```
where `Ψ := (F.map₂HomologicalComplex …).obj G`, `quotient := HomotopyCategory.quotient _ _`,
and `triangle φ := CochainComplex.mappingCone.triangle φ`.  Note `quotient ⋙
bifunctorPhi F G = quotient ⋙ Φ`, `Φ.mapTriangle` and the `CommShift` data require
`bifunctorXi F G` in scope.  This step should be essentially mechanical once C2
exists (it is the verbatim shape of the Mathlib model with the three substitutions).
DEPENDENCY: built from C2 (`bifunctorMapTriangleIso`). -/
noncomputable def bifunctorPhi_mapTrianglehIso_C3
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ))
    {K L : CochainComplex B ℤ} (φ : K ⟶ L) :
    letI := bifunctorXi F G;
    (bifunctorPhi F G).mapTriangle.obj (CochainComplex.mappingCone.triangleh φ) ≅
      CochainComplex.mappingCone.triangleh
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G).map φ) := by
  letI := bifunctorXi F G
  letI := map₂HomologicalComplex_obj_additive F G
  letI Ψ := (F.map₂HomologicalComplex (ComplexShape.up ℤ) (ComplexShape.up ℤ)
        (ComplexShape.up ℤ)).obj G
  haveI : NatTrans.CommShift (bifunctorPhiFactors F G).hom ℤ :=
    Quotient.liftCommShift_compatibility _ _ _ _
  exact
    ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).mapTriangleCompIso
          (bifunctorPhi F G)).symm.app
        (CochainComplex.mappingCone.triangle φ) ≪≫
      (Functor.mapTriangleIso (bifunctorPhiFactors F G)).app
          (CochainComplex.mappingCone.triangle φ) ≪≫
        (Ψ.mapTriangleCompIso (HomotopyCategory.quotient D (ComplexShape.up ℤ))).app
            (CochainComplex.mappingCone.triangle φ) ≪≫
          (HomotopyCategory.quotient D (ComplexShape.up ℤ)).mapTriangle.mapIso
            (bifunctorMapTriangleIso F G φ)

/-- **THE remaining analytic kernel (left case): the bifunctor mapping-cone
triangle comparison.**  This is the bifunctor analogue of Mathlib's
`CochainComplex.mappingCone.mapTrianglehIso` (which is stated only for functors of
the form `G.mapHomologicalComplex`).  Writing `Ψ := Tot(F(G, -)) =
(F.map₂HomologicalComplex …).obj G : CochainComplex B ℤ ⥤ CochainComplex D ℤ`
(an additive functor of cochain complexes, but NOT of the form
`H.mapHomologicalComplex`), this exhibits the image under the descended functor
`Φ = bifunctorPhi F G` of the standard homotopy mapping-cone triangle `triangleh φ`
as isomorphic to the standard mapping-cone triangle of `Ψ.map φ`.

Informal content: `Φ(triangleh φ)` is, via `bifunctorPhiFactors`, the image of
`triangleh φ` under `Ψ`.  The geometric input is the complex-level comparison
`Ψ(cone φ) ≅ cone(Ψ φ)` (degreewise from biproducts + shift, the additive
degreewise functor `F(G,-)` and `Tot` commuting with the cone up to the Koszul
sign already encoded in `ξ = bifunctorXi`), upgraded to a comparison of the
mapping-cone *triangles* (compatibility of `inr`/`δ` with the shift), then
transported across the homotopy quotient via `bifunctorPhiFactors`.  Mirror
`#print CochainComplex.mappingCone.mapTrianglehIso`, replacing
`mapHomotopyCategoryFactors`/`mapTriangleIso` by `bifunctorPhiFactors F G` and the
to-be-built complex-level bifunctor cone comparison.

DEPENDENCY (no Mathlib support): requires the complex-level bifunctor cone
comparison `Ψ.obj (mappingCone φ) ≅ mappingCone (Ψ.map φ)`, then its `triangle`
upgrade `Ψ.mapTriangle.obj (mappingCone.triangle φ) ≅ mappingCone.triangle (Ψ.map φ)`,
then the homotopy-level assembly through `bifunctorPhiFactors`.  This is the
genuine new API.

FORMAL SKETCH (this step): decomposed into the C1/C2/C3 helpers below.

CRITICAL MATH NOTE: the cone comparison is **FALSE for an abstract additive
functor `Ψ` carrying only a `CommShift ℤ` datum** — a `CommShift` can transport
only *closed* cochains (cocycles / chain maps), but the mapping cone is built
from the *non-closed* cochains `inl φ : Cochain K (cone φ) (-1)` and
`snd φ : Cochain (cone φ) L 0`.  Hence C1 below MUST be built from the *concrete
degreewise* structure of `Ψ = Tot(F(G,-))` (each total-complex summand is
`F(G^p, (-)^q)` with `F(G^p,-)` a degreewise additive functor on `B`), NOT
abstractly.  Use the `mapBifunctorMap`/`ιMapBifunctor` API (cf.
`map₂HomologicalComplex_obj_additive`) — this is the bifunctor analogue of
`CochainComplex.HomComplex.Cochain.map` (`z ↦ Cochain.mk (fun p q h => Φ.map (z.v …))`,
which exists only for `Φ.mapHomologicalComplex`). -/
noncomputable def bifunctorPhi_mapTrianglehIso
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ))
    {K L : CochainComplex B ℤ} (φ : K ⟶ L) :
    letI := bifunctorXi F G;
    (bifunctorPhi F G).mapTriangle.obj (CochainComplex.mappingCone.triangleh φ) ≅
      CochainComplex.mappingCone.triangleh
        (((F.map₂HomologicalComplex (ComplexShape.up ℤ)
          (ComplexShape.up ℤ) (ComplexShape.up ℤ)).obj G).map φ) := by
  letI := bifunctorXi F G
  -- C3: assemble from the complex-level triangle iso C2 (`bifunctorMapTriangleIso`)
  -- by transporting across the homotopy quotient via `bifunctorPhiFactors`,
  -- mirroring the body of `#print CochainComplex.mappingCone.mapTrianglehIso`:
  --   (quotient.mapTriangleCompIso (bifunctorPhi F G)).symm.app (triangle φ) ≪≫
  --   (Functor.mapTriangleIso (bifunctorPhiFactors F G)).app (triangle φ) ≪≫
  --   (Ψ.mapTriangleCompIso quotient).app (triangle φ) ≪≫
  --   quotient.mapTriangle.mapIso (bifunctorMapTriangleIso F G φ)
  -- where `Ψ := (F.map₂HomologicalComplex …).obj G` and `triangle φ` is the
  -- complex-level `mappingCone.triangle φ`. The mapTriangleCompIso/mapTriangleIso
  -- steps need the CommShift compatibility carried by `bifunctorXi`.
  exact bifunctorPhi_mapTrianglehIso_C3 F G φ

omit [HasZeroObject A] [HasBinaryBiproducts A] in
/-- **CRUX (left case).**  `Φ`, equipped with `ξ = bifunctorXi`, is a
triangulated functor.

Informal proof (the genuine content of tag 0G6E).  By `Functor.IsTriangulated.mk`
it suffices to show that `Φ.mapTriangle` sends every distinguished triangle of
`K(B)` to a distinguished triangle of `K(D)`.  Every distinguished triangle of
`K(B)` is isomorphic (as a triangle) to the standard mapping-cone triangle
`triangleh φ : X → Y → cone φ → X[1]` of some chain map `φ : X → Y`
(`HomotopyCategory.mappingCone…`/the definition of the pretriangulated structure);
since `Φ.mapTriangle` preserves triangle isomorphisms and distinguished triangles
are closed under isomorphism, it suffices to treat `T = triangleh φ`.

Now `Φ(triangleh φ)` is computed by transporting through `bifunctorPhiFactors` to
the complex level: it is the image of `triangleh φ` under the complex-level
functor `Ψ := Tot(F(G, -))`.  The key geometric input is the bifunctor
mapping-cone comparison isomorphism
`Tot(F(G, cone φ)) ≅ cone (Tot(F(G, φ)))`,
natural and compatible with the shift datum `ξ` — i.e. the bifunctor analogue of
`CochainComplex.mappingCone.mapHomologicalComplexIso`/`.mapTrianglehIso`.  This
isomorphism holds because `Tot(F(G, -))` is an additive functor of cochain
complexes and `Tot`/`F(G, -)` commute with the cone construction degreewise
(the cone is built from biproducts and the shift, both preserved by the additive
degreewise functor `F(G, -)` and by `Tot`, up to the Koszul sign already encoded
in `ξ`).  Composing this comparison isomorphism with `bifunctorPhiFactors` yields
`Φ.mapTriangle.obj (triangleh φ) ≅ triangleh (Ψ.map φ)` as triangles, exhibiting
`Φ(triangleh φ)` as isomorphic to a standard mapping-cone triangle, hence
distinguished.  (This mirrors exactly how Mathlib proves
`(G.mapHomotopyCategory _).IsTriangulated` for a single additive functor `G` via
`mappingCone.mapTrianglehIso`; here the single functor is replaced by the
additive functor `Tot(F(G, -))` on cochain complexes.)

Formalization plan: state and prove the bifunctor cone comparison as a helper
`Tot(F(G, cone φ)) ≅ cone (Tot(F(G, φ)))`; package it (with shift compatibility)
into a triangle isomorphism `Φ.mapTriangle.obj (triangleh φ) ≅ triangleh (Ψ.map φ)`;
conclude with `Pretriangulated.isomorphic_distinguished` +
`HomotopyCategory.mappingCone` distinguished-triangle membership, fed to
`Functor.IsTriangulated.mk`. -/
@[sga "4 XVII 1.1.7" "partial", sga "4½ Etat_0 1.3.3" "partial"]
theorem bifunctorPhi_isTriangulated
    (F : A ⥤ B ⥤ D) [F.Additive] [∀ X, (F.obj X).Additive]
    [∀ (K₁ : HomologicalComplex A (ComplexShape.up ℤ))
        (K₂ : HomologicalComplex B (ComplexShape.up ℤ)),
        K₁.HasMapBifunctor K₂ F (ComplexShape.up ℤ)]
    (G : HomologicalComplex A (ComplexShape.up ℤ)) :
    letI := bifunctorXi F G; (bifunctorPhi F G).IsTriangulated := by
  -- SANITY CHECK PASSED (statement is verbatim tag 0G6E, a published true theorem).
  -- Reduced to the single kernel `bifunctorPhi_mapTrianglehIso` (the bifunctor
  -- mapping-cone triangle comparison), exactly as Mathlib's single-variable instance
  -- `HomotopyCategory.instIsTriangulatedIntUpMapHomotopyCategory` is built from
  -- `mappingCone.mapTrianglehIso`.
  let := bifunctorXi F G
  apply Functor.IsTriangulated.mk
  rintro T ⟨K, L, φ, ⟨e⟩⟩
  exact ⟨_, _, _, ⟨(bifunctorPhi F G).mapTriangle.mapIso e ≪≫
    bifunctorPhi_mapTrianglehIso F G φ⟩⟩

end Reduction

end Stacks.SheafOfModules.Tensor

end
