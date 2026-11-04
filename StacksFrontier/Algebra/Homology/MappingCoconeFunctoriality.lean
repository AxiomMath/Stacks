module

public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
import StacksCore.Tactic.StacksAttribute

/-!
# Functoriality of the mapping cocone of a morphism of cochain complexes

Mathlib's `CochainComplex.mappingCocone φ` is `(mappingCone φ)⟦-1⟧`, and a morphism of
arrows induces a morphism of mapping cocones, obtained by shifting
`HomologicalComplex.homotopyCofiber.mapArrowHom`. This file records how that morphism
interacts with the two projections `mappingCocone.fst` and `mappingCocone.snd`, and deduces
that a family of canonical maps into mapping cocones built by `mappingCocone.lift` is
natural.

## Main definitions

* `CochainComplex.mappingCocone.mapArrow`: the morphism of mapping cocones induced by a
  morphism of arrows.

## Main results

* `CochainComplex.mappingCocone.fst_f` and `CochainComplex.mappingCocone.snd_v`: the two
  projections of a mapping cocone, degreewise.
* `CochainComplex.mappingCocone.mapArrow_fst` and
  `CochainComplex.mappingCocone.mapArrow_snd`: the induced morphism of mapping cocones
  commutes with the two projections.
* `CochainComplex.mappingCocone.to_ext`: a morphism into a mapping cocone is determined by
  its two components.
* `CochainComplex.mappingCocone.comp_lift`: naturality of `mappingCocone.lift`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits HomologicalComplex

namespace CochainComplex

open HomComplex

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasBinaryBiproducts C]
  {K L K' L' : CochainComplex C ℤ} (φ : K ⟶ L) (φ' : K' ⟶ L')

namespace mappingCocone

section Projections

/-- The first projection of a mapping cocone, degreewise: the first projection of the
homotopy cofibre one degree down. -/
lemma fst_f (p : ℤ) :
    (mappingCocone.fst φ).f p =
      homotopyCofiber.fstX φ (p + -1) p (ComplexShape.up_mk _ _ (by lia)) := by
  have key : (mappingCocone.fst φ).f p =
      -(((mappingCone.fst φ).leftShift (-1) 0 (by lia)).homOf).f p := rfl
  rw [key, Cocycle.homOf_f, Cocycle.leftShift_coe,
    Cochain.leftShift_v (mappingCone.fst φ : Cochain (mappingCone φ) K 1) (-1) 0 (by lia)
      p p (add_zero p) (p + -1) (by lia)]
  simp [mappingCone.fst]
  rfl

/-- The second projection of a mapping cocone, degreewise: the second projection of the
homotopy cofibre one degree down. -/
lemma snd_v (p : ℤ) :
    (mappingCocone.snd φ).v p (p + -1) (by lia) =
      (mappingCone.snd φ).v (p + -1) (p + -1) (add_zero _) := by
  have key : (mappingCocone.snd φ).v p (p + -1) (by lia) =
      ((mappingCone.snd φ).leftShift (-1) (-1) (by lia)).v p (p + -1) (by lia) := rfl
  rw [key, Cochain.leftShift_v (mappingCone.snd φ) (-1) (-1) (by lia) p (p + -1) (by lia)
    (p + -1) (by lia)]
  simp only [shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl, Iso.refl_hom]
  rw [Int.negOnePow_even _ ⟨1, by norm_num⟩, one_smul]
  simp
  rfl

end Projections

section MapArrow

variable (H : ∀ j : ℤ, ∃ i, (ComplexShape.up ℤ).Rel i j)
  (α : Arrow.mk φ ⟶ Arrow.mk φ')

/-- The morphism of mapping cocones induced by a morphism of arrows. -/
def mapArrow : mappingCocone φ ⟶ mappingCocone φ' :=
  (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map
    (homotopyCofiber.mapArrowHom φ φ' H α)

/-- The morphism of mapping cocones induced by a morphism of arrows is, in degree `p`, the
morphism of homotopy cofibres in degree `p - 1`. -/
@[simp]
lemma mapArrow_f (p : ℤ) :
    (mapArrow φ φ' H α).f p = (homotopyCofiber.mapArrowHom φ φ' H α).f (p + -1) := rfl

/-- The identity of an arrow induces the identity of its mapping cocone. -/
@[simp]
lemma mapArrow_id : mapArrow φ φ H (𝟙 (Arrow.mk φ)) = 𝟙 _ := by
  rw [mapArrow, homotopyCofiber.mapArrowHom_id]
  exact (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map_id _

/-- The morphism of mapping cocones induced by a composite of morphisms of arrows is the
composite of the induced morphisms. -/
@[reassoc]
lemma mapArrow_comp {K'' L'' : CochainComplex C ℤ} (φ'' : K'' ⟶ L'')
    (β : Arrow.mk φ' ⟶ Arrow.mk φ'') :
    mapArrow φ φ'' H (α ≫ β) = mapArrow φ φ' H α ≫ mapArrow φ' φ'' H β := by
  rw [mapArrow, mapArrow, mapArrow, homotopyCofiber.mapArrowHom_comp]
  exact (CategoryTheory.shiftFunctor (CochainComplex C ℤ) (-1 : ℤ)).map_comp _ _

/-- The morphism of homotopy cofibres induced by a morphism of arrows commutes with the
first projection. -/
lemma mapArrowHom_fstX (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    (homotopyCofiber.mapArrowHom φ φ' H α).f i ≫ homotopyCofiber.fstX φ' i j hij =
      homotopyCofiber.fstX φ i j hij ≫ α.left.f j := by
  refine homotopyCofiber.ext_from_X φ j i hij ?_ ?_
  · simp [homotopyCofiber.mapArrowHom,
      homotopyCofiber.inrCompHomotopy_hom _ _ j i hij]
  · simp [homotopyCofiber.mapArrowHom]

/-- The morphism of homotopy cofibres induced by a morphism of arrows commutes with the
second projection. -/
lemma mapArrowHom_sndX (i : ℤ) :
    (homotopyCofiber.mapArrowHom φ φ' H α).f i ≫ homotopyCofiber.sndX φ' i =
      homotopyCofiber.sndX φ i ≫ α.right.f i := by
  refine homotopyCofiber.ext_from_X φ (i + 1) i (ComplexShape.up_mk _ _ rfl) ?_ ?_
  · simp [homotopyCofiber.mapArrowHom,
      homotopyCofiber.inrCompHomotopy_hom _ _ (i + 1) i (ComplexShape.up_mk _ _ rfl)]
  · simp [homotopyCofiber.mapArrowHom]

/-- The morphism of mapping cocones induced by a morphism of arrows `α` commutes with the
first projections, via `α.left`. -/
@[reassoc]
lemma mapArrow_fst :
    mapArrow φ φ' H α ≫ mappingCocone.fst φ' = mappingCocone.fst φ ≫ α.left := by
  ext p
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, fst_f, fst_f, mapArrow_f]
  exact mapArrowHom_fstX φ φ' H α (p + -1) p (ComplexShape.up_mk _ _ (by lia))

/-- The morphism of mapping cocones induced by a morphism of arrows `α` commutes with the
second projections, via `α.right`. -/
lemma mapArrow_snd :
    (Cochain.ofHom (mapArrow φ φ' H α)).comp (mappingCocone.snd φ') (zero_add (-1)) =
      (mappingCocone.snd φ).comp (Cochain.ofHom α.right) (add_zero (-1)) := by
  ext p q hpq
  obtain rfl : q = p + -1 := by lia
  rw [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v, Cochain.ofHom_v,
    snd_v, snd_v, mapArrow_f,
    show (mappingCone.snd φ).v (p + -1) (p + -1) (add_zero _) = _ from Cochain.ofHoms_v _ _,
    show (mappingCone.snd φ').v (p + -1) (p + -1) (add_zero _) = _ from Cochain.ofHoms_v _ _]
  exact mapArrowHom_sndX φ φ' H α (p + -1)

/-- The degreewise form of `mapArrow_snd`. -/
lemma mapArrow_snd_v (p : ℤ) :
    (mapArrow φ φ' H α).f p ≫ (mappingCocone.snd φ').v p (p + -1) (by lia) =
      (mappingCocone.snd φ).v p (p + -1) (by lia) ≫ α.right.f (p + -1) := by
  simpa only [Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v, Cochain.ofHom_v] using
    Cochain.congr_v (mapArrow_snd φ φ' H α) p (p + -1) (by lia)

end MapArrow

section Ext

variable {M M' : CochainComplex C ℤ}

/-- A morphism into a mapping cocone is determined by its two components. -/
lemma to_ext {f g : M ⟶ mappingCocone φ}
    (h₁ : f ≫ mappingCocone.fst φ = g ≫ mappingCocone.fst φ)
    (h₂ : (Cochain.ofHom f).comp (mappingCocone.snd φ) (zero_add (-1)) =
      (Cochain.ofHom g).comp (mappingCocone.snd φ) (zero_add (-1))) : f = g := by
  ext p
  have hid := mappingCocone.id_X φ p (p + -1) (by lia)
  have e₁ : f.f p ≫ (mappingCocone.fst φ).f p = g.f p ≫ (mappingCocone.fst φ).f p := by
    rw [← HomologicalComplex.comp_f, ← HomologicalComplex.comp_f, h₁]
  have e₂ : f.f p ≫ (mappingCocone.snd φ).v p (p + -1) (by lia) =
      g.f p ≫ (mappingCocone.snd φ).v p (p + -1) (by lia) := by
    simpa only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v] using
      Cochain.congr_v h₂ p (p + -1) (by lia)
  have key : f.f p ≫ 𝟙 ((mappingCocone φ).X p) = g.f p ≫ 𝟙 ((mappingCocone φ).X p) := by
    rw [← hid, Preadditive.comp_add, Preadditive.comp_add, ← assoc, ← assoc, e₁, e₂,
      assoc, assoc]
  rwa [comp_id, comp_id] at key

/-- Precomposing the canonical map into a mapping cocone with a morphism of complexes gives
the canonical map built from the precomposed data. -/
lemma comp_lift (ψ : M' ⟶ M) (a : M ⟶ K) (β : Cochain M L (-1))
    (hαβ : δ (-1) 0 β + Cochain.ofHom (a ≫ φ) = 0)
    (hαβ' : δ (-1) 0 ((Cochain.ofHom ψ).comp β (zero_add (-1))) +
      Cochain.ofHom ((ψ ≫ a) ≫ φ) = 0) :
    ψ ≫ mappingCocone.lift φ a β hαβ =
      mappingCocone.lift φ (ψ ≫ a) ((Cochain.ofHom ψ).comp β (zero_add (-1))) hαβ' := by
  refine to_ext φ ?_ ?_
  · rw [assoc, mappingCocone.lift_fst, mappingCocone.lift_fst]
  · ext p q hpq
    obtain rfl : q = p + -1 := by lia
    simp only [Cochain.zero_cochain_comp_v, Cochain.ofHom_v, HomologicalComplex.comp_f,
      mappingCocone.lift_f_snd_v, assoc]

end Ext

end mappingCocone

end CochainComplex

end
