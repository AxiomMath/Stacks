module

public import StacksFrontier.CategoryTheory.TwoFibreProductOver

/-!
# Base change of a fully faithful functor along a 2-fibre product over a base

Let `F : 𝒳 ⥤ 𝒮` and `G : 𝒴 ⥤ 𝒮` be functors over a base category `𝒞`. If `G` is faithful, then
so is the first projection `𝒳 ×_𝒮 𝒴 ⥤ 𝒳` of the 2-fibre product over `𝒞`; if `G` is moreover
full, then so is that projection. In other words the base change of a fully faithful functor
over `𝒞` is fully faithful. Faithfulness is
`CategoryTheory.TwoFibreProductOver.faithful_fst_of_faithful`; this file adds fullness.

## Main results

* `CategoryTheory.TwoFibreProductOver.full_fst`: the first projection is full when `G` is full
  and faithful.

## Implementation notes

The `𝒴`-component of a morphism `(a, b)` of the 2-fibre product is determined by its
`𝒳`-component through the comparison isomorphisms, `G b = φ⁻¹ ≫ F a ≫ φ'`
(`CategoryTheory.TwoFibreProductOver.Hom.map_b`), which gives faithfulness; for fullness the
morphism `G⁻¹(φ⁻¹ ≫ F a ≫ φ')` lies over the same morphism of `𝒞` as `a` because the comparison
isomorphisms are vertical.
-/

@[expose] public section

namespace CategoryTheory

namespace TwoFibreProductOver

variable {𝒞 𝒳 𝒴 𝒮 : Type*} [Category 𝒞] [Category 𝒳] [Category 𝒴] [Category 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- The comparison isomorphism of an object of the 2-fibre product is vertical, so its image in
the base is an `eqToHom`. -/
lemma map_iso_hom (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G)
    (h : p𝒮.obj (F.obj P.x) = p𝒮.obj (G.obj P.y)) : p𝒮.map P.iso.hom = eqToHom h := by
  have := P.vertical
  rw [IsHomLift.fac' p𝒮 (𝟙 P.base) P.iso.hom]
  simp

/-- The inverse comparison isomorphism of an object of the 2-fibre product is vertical, so its
image in the base is an `eqToHom`. -/
lemma map_iso_inv (P : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G)
    (h : p𝒮.obj (G.obj P.y) = p𝒮.obj (F.obj P.x)) : p𝒮.map P.iso.inv = eqToHom h := by
  have := P.vertical
  rw [IsHomLift.fac' p𝒮 (𝟙 P.base) P.iso.inv]
  simp

/-- The image under `G` of the `𝒴`-component of a morphism of the 2-fibre product is determined
by the `𝒳`-component: `G b = φ⁻¹ ≫ F a ≫ φ'`. -/
lemma Hom.map_b {P Q : TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G} (f : Hom P Q) :
    G.map f.b = P.iso.inv ≫ F.map f.a ≫ Q.iso.hom := by
  rw [f.w, Iso.inv_hom_id_assoc]

/-- If `G` is full and faithful and both `F` and `G` are functors over `𝒞`, the first projection
of the 2-fibre product is full. -/
theorem full_fst [G.Full] [G.Faithful] (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴) :
    (fst p𝒳 p𝒴 p𝒮 F G).Full where
  map_surjective {P Q} a := by
    change P.x ⟶ Q.x at a
    refine ⟨Hom.mk' a (G.preimage (P.iso.inv ≫ F.map a ≫ Q.iso.hom)) ?_
      (by rw [Functor.map_preimage, Iso.hom_inv_id_assoc]), rfl⟩
    have hb := Functor.congr_hom hG.symm (G.preimage (P.iso.inv ≫ F.map a ≫ Q.iso.hom))
    have ha := Functor.congr_hom hF.symm a
    rw [hb, ha]
    simp only [Functor.comp_map, Functor.map_preimage, Functor.map_comp,
      map_iso_inv P (by rw [← Functor.comp_obj, ← Functor.comp_obj, hF, hG, P.hx, P.hy]),
      map_iso_hom Q (by rw [← Functor.comp_obj, ← Functor.comp_obj, hF, hG, Q.hx, Q.hy]),
      Category.assoc, eqToHom_trans, eqToHom_trans_assoc]

end TwoFibreProductOver

end CategoryTheory
