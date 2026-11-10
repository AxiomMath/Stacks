module

public import StacksFrontier.AlgebraicGeometry.IdealSheafFromAffineFamily
public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Gluing quasi-coherent ideal sheaves along an open cover

Let `{f i : W i ⟶ Y}` be a jointly surjective family of open immersions and let `I i` be ideal
sheaves on the `W i` which agree on the pairwise fibre products: the pullbacks of `I i` and
`I j` to `W i ×_Y W j` coincide. Then there is an ideal sheaf on `Y` whose pullback to every
`W i` is `I i`. Together with uniqueness (an ideal sheaf is determined by its pullbacks along an
open cover) this says that ideal sheaves form a sheaf for the Zariski topology.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.localIdeal`: the ideal on an affine open `U` of `Y`
  contained in the image of an open immersion `W ⟶ Y` determined by an ideal sheaf on `W`.
* `AlgebraicGeometry.Scheme.IdealSheafData.glue`: the glued ideal sheaf.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.comap_glue`: the glued ideal sheaf pulls back to the
  given ideal sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {Y : Scheme.{u}}

/-- Restriction of an ideal sheaf along an equality of affine opens. -/
theorem comap_ideal_of_eq (I : Y.IdealSheafData) {A B : Y.affineOpens} (h : B ≤ A) (e : A = B) :
    (I.ideal B).comap (Y.presheaf.map (homOfLE (X := Y.Opens) h).op).hom = I.ideal A := by
  subst e
  rw [show homOfLE (X := Y.Opens) h = 𝟙 _ from Subsingleton.elim _ _, op_id,
    CategoryTheory.Functor.map_id, CommRingCat.hom_id]
  exact Ideal.comap_id _

/-- The ideal on an affine open `U` of `Y` contained in the image of an open immersion
`g : W ⟶ Y` determined by an ideal sheaf `I` on `W`: the inverse image of the ideal of `I` over
`g⁻¹ U` under the isomorphism `Γ(Y, U) ≅ Γ(W, g⁻¹ U)`. -/
def localIdeal {W : Scheme.{u}} (g : W ⟶ Y) [IsOpenImmersion g] (I : W.IdealSheafData)
    (U : Y.affineOpens) (hU : (U : Y.Opens) ≤ g.opensRange) : Ideal Γ(Y, U) :=
  (I.ideal ⟨g ⁻¹ᵁ U, U.2.preimage_of_isOpenImmersion g hU⟩).comap (g.app U).hom

/-- For an open immersion `g : W ⟶ Y` and an open `U` of `Y` contained in its image, the map
`Γ(Y, U) ⟶ Γ(W, g⁻¹ U)` is bijective. -/
theorem bijective_app {W : Scheme.{u}} (g : W ⟶ Y) [IsOpenImmersion g] (U : Y.Opens)
    (hU : U ≤ g.opensRange) : Function.Bijective (g.app U).hom := by
  have := g.isIso_app U hU
  exact ConcreteCategory.bijective_of_isIso (g.app U)

/-- The local ideals are compatible with restriction. -/
theorem localIdeal_map {W : Scheme.{u}} (g : W ⟶ Y) [IsOpenImmersion g] (I : W.IdealSheafData)
    {U V : Y.affineOpens} (hVU : V ≤ U) (hU : (U : Y.Opens) ≤ g.opensRange)
    (hV : (V : Y.Opens) ≤ g.opensRange) :
    (localIdeal g I U hU).map (Y.presheaf.map (homOfLE hVU).op).hom = localIdeal g I V hV := by
  let KU : W.affineOpens := ⟨g ⁻¹ᵁ U, U.2.preimage_of_isOpenImmersion g hU⟩
  let KV : W.affineOpens := ⟨g ⁻¹ᵁ V, V.2.preimage_of_isOpenImmersion g hV⟩
  have hK : KV ≤ KU := fun x hx => hVU hx
  have hnat : (g.app V).hom.comp (Y.presheaf.map (homOfLE hVU).op).hom =
      (W.presheaf.map (homOfLE hK).op).hom.comp (g.app U).hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp, g.naturality]
    rfl
  rw [localIdeal, localIdeal, ← I.map_ideal hK]
  conv_rhs => rw [← Ideal.map_comap_of_surjective _ (bijective_app g U hU).2 (I.ideal KU)]
  rw [Ideal.map_map, ← hnat, ← Ideal.map_map,
    Ideal.comap_map_of_bijective _ (bijective_app g V hV)]

/-- Computing a local ideal through an open immersion `p : P ⟶ W` and the pulled back ideal
sheaf gives the same ideal. -/
theorem localIdeal_comp {W P : Scheme.{u}} (p : P ⟶ W) (g : W ⟶ Y) [IsOpenImmersion p]
    [IsOpenImmersion g] (I : W.IdealSheafData) (U : Y.affineOpens)
    (hU : (U : Y.Opens) ≤ (p ≫ g).opensRange) :
    localIdeal (p ≫ g) (I.comap p) U hU =
      localIdeal g I U (hU.trans (by
        rintro _ ⟨x, rfl⟩
        exact ⟨p x, rfl⟩)) := by
  have hU' : (U : Y.Opens) ≤ g.opensRange := hU.trans (by
    rintro _ ⟨x, rfl⟩
    exact ⟨p x, rfl⟩)
  let V : W.affineOpens := ⟨g ⁻¹ᵁ U, U.2.preimage_of_isOpenImmersion g hU'⟩
  have hV : (V : W.Opens) ≤ p.opensRange := by
    intro w hw
    obtain ⟨x, hx⟩ := hU hw
    refine ⟨x, ?_⟩
    apply g.isOpenEmbedding.injective
    simpa [Scheme.Hom.comp_apply] using hx
  let Q : P.affineOpens := ⟨(p ≫ g) ⁻¹ᵁ U, U.2.preimage_of_isOpenImmersion _ hU⟩
  have himage : (⟨p ''ᵁ Q, Q.2.image_of_isOpenImmersion p⟩ : W.affineOpens) = V := by
    apply Subtype.ext
    change p ''ᵁ (p ⁻¹ᵁ (g ⁻¹ᵁ U)) = g ⁻¹ᵁ U
    rw [p.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hV]
  rw [localIdeal, localIdeal, ideal_comap_of_isOpenImmersion, Ideal.comap_comap]
  have e : ((p.appIso Q).inv.hom.comp ((p ≫ g).app U).hom) =
      (W.presheaf.map (homOfLE (X := W.Opens) (show (⟨p ''ᵁ Q, Q.2.image_of_isOpenImmersion p⟩ :
        W.affineOpens) ≤ V from himage.le)).op).hom.comp (g.app U).hom := by
    rw [← CommRingCat.hom_comp, ← CommRingCat.hom_comp]
    congr 1
    rw [Scheme.Hom.comp_app p g U]
    exact (Category.assoc _ _ _).trans (congrArg (g.app U ≫ ·) (p.app_appIso_inv (g ⁻¹ᵁ U)))
  rw [e, ← Ideal.comap_comap, comap_ideal_of_eq I _ himage.symm]

/-- Equal open immersions and equal ideal sheaves give equal local ideals on `U`, whatever the
proofs that `U` lies in their images. -/
theorem localIdeal_congr {W : Scheme.{u}} {g g' : W ⟶ Y} [IsOpenImmersion g] [IsOpenImmersion g']
    (e : g = g') {I I' : W.IdealSheafData} (eI : I = I') (U : Y.affineOpens)
    (hU : (U : Y.Opens) ≤ g.opensRange) (hU' : (U : Y.Opens) ≤ g'.opensRange) :
    localIdeal g I U hU = localIdeal g' I' U hU' := by
  subst e eI
  rfl

/-- Local ideals of two ideal sheaves which agree on a common refinement of the overlap of the
two open immersions agree. -/
theorem localIdeal_eq_of_comap_eq {W W' P : Scheme.{u}} (g : W ⟶ Y) (g' : W' ⟶ Y)
    [IsOpenImmersion g] [IsOpenImmersion g'] (p : P ⟶ W) (p' : P ⟶ W') [IsOpenImmersion p]
    [IsOpenImmersion p'] (hw : p ≫ g = p' ≫ g')
    (hrange : ∀ y, y ∈ g.opensRange → y ∈ g'.opensRange → y ∈ (p ≫ g).opensRange)
    (I : W.IdealSheafData) (I' : W'.IdealSheafData) (hI : I.comap p = I'.comap p')
    (U : Y.affineOpens) (hU : (U : Y.Opens) ≤ g.opensRange) (hU' : (U : Y.Opens) ≤ g'.opensRange) :
    localIdeal g I U hU = localIdeal g' I' U hU' := by
  have hP : (U : Y.Opens) ≤ (p ≫ g).opensRange := fun y hy => hrange y (hU hy) (hU' hy)
  have hP' : (U : Y.Opens) ≤ (p' ≫ g').opensRange := by
    intro y hy
    obtain ⟨x, hx⟩ := hP hy
    exact ⟨x, by rw [← hx, hw]⟩
  rw [← localIdeal_comp p g I U hP, ← localIdeal_comp p' g' I' U hP']
  exact localIdeal_congr hw hI U hP hP'

section Glue

variable {ι : Type*} {W : ι → Scheme.{u}} (g : ∀ i, W i ⟶ Y) [∀ i, IsOpenImmersion (g i)]
  (I : ∀ i, (W i).IdealSheafData)

/-- The affine opens of `Y` contained in the image of one of the open immersions. -/
def GlueSupport (U : Y.affineOpens) : Prop := ∃ i, (U : Y.Opens) ≤ (g i).opensRange

open Classical in
/-- The ideals on the affine opens of `Y` contained in the image of one of the open immersions,
computed through a chosen one. -/
def glueIdeal (U : Y.affineOpens) : Ideal Γ(Y, U) :=
  if h : GlueSupport g U then localIdeal (g h.choose) (I h.choose) U h.choose_spec else ⊤

variable (hcompat : ∀ i k (U : Y.affineOpens) (hi : (U : Y.Opens) ≤ (g i).opensRange)
    (hk : (U : Y.Opens) ≤ (g k).opensRange),
    localIdeal (g i) (I i) U hi = localIdeal (g k) (I k) U hk)

include hcompat in
/-- If the local ideals are compatible, then on an affine open `U` contained in the image of
`g i` the glued ideal is the local ideal computed through `g i`. -/
theorem glueIdeal_eq (i : ι) (U : Y.affineOpens) (hi : (U : Y.Opens) ≤ (g i).opensRange) :
    glueIdeal g I U = localIdeal (g i) (I i) U hi := by
  have h : GlueSupport g U := ⟨i, hi⟩
  rw [glueIdeal, dite_eq_left h]
  exact hcompat _ _ _ _ _

/-- **The glued ideal sheaf.** -/
def glue (hcov : ∀ y : Y, ∃ i, y ∈ (g i).opensRange) : Y.IdealSheafData :=
  ofAffineFamily (GlueSupport g) (glueIdeal g I)
    (fun y => by
      obtain ⟨i, hi⟩ := hcov y
      obtain ⟨U, hU, hyU, hUi⟩ := exists_isAffineOpen_mem_and_subset hi
      exact ⟨⟨U, hU⟩, ⟨i, hUi⟩, hyU⟩)
    (fun U f ⟨i, hi⟩ => ⟨i, (Y.basicOpen_le f).trans hi⟩)
    (fun U V hVU ⟨i, hi⟩ _ => by
      have hVi : (V : Y.Opens) ≤ (g i).opensRange := (show (V : Y.Opens) ≤ U from hVU).trans hi
      rw [glueIdeal_eq g I hcompat i U hi, glueIdeal_eq g I hcompat i V hVi]
      exact localIdeal_map (g i) (I i) hVU hi _)

include hcompat in
/-- **The glued ideal sheaf pulls back to the given ones.** -/
theorem comap_glue (hcov : ∀ y : Y, ∃ i, y ∈ (g i).opensRange) (i : ι) :
    (glue g I hcompat hcov).comap (g i) = I i := by
  ext Q : 2
  rw [ideal_comap_of_isOpenImmersion]
  have hS : GlueSupport g ⟨g i ''ᵁ Q, Q.2.image_of_isOpenImmersion (g i)⟩ :=
    ⟨i, (g i).image_le_opensRange _⟩
  rw [glue, ideal_ofAffineFamily _ _ _ _ _ hS, glueIdeal_eq g I hcompat i _
    ((g i).image_le_opensRange _), localIdeal, Ideal.comap_comap]
  have hle : (⟨g i ⁻¹ᵁ (g i ''ᵁ (Q : (W i).Opens)),
      (Q.2.image_of_isOpenImmersion (g i)).preimage_of_isOpenImmersion (g i)
        ((g i).image_le_opensRange _)⟩ : (W i).affineOpens) ≤ Q :=
    ((g i).preimage_image_eq _).le
  have e : ((g i).app (g i ''ᵁ Q)).hom.comp ((g i).appIso Q).inv.hom =
      ((W i).presheaf.map (homOfLE (X := (W i).Opens) hle).op).hom := by
    rw [← CommRingCat.hom_comp, (g i).appIso_inv_app]
    rfl
  rw [e]
  exact comap_ideal_of_eq _ hle (Subtype.ext ((g i).preimage_image_eq _).symm)

end Glue

end AlgebraicGeometry.Scheme.IdealSheafData

end
