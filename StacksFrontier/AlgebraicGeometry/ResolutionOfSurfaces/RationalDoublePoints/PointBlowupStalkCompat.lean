module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.PointBlowupLocalization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.ChartCaseTwo

/-!
# The local rings of the blowup of a point and of the blowup of its local ring

Let `y` be a closed point of a scheme `Y` and `A ≅ 𝒪_{Y,y}`. The blowup of `Spec(A)` in its
closed point maps to the blowup of `Y` in `y`
(`AlgebraicGeometry.exists_hom_blowUp_maximalIdealSheaf_localization`), with isomorphic local
rings. This file records that the identification of local rings is compatible with the maps from
`𝒪_{Y,y}` and from `A`: an element of `𝒪_{Y,y}` and its image in `A` have the same image in the
local ring at a point of the blowup.

## Main results

* `AlgebraicGeometry.stalkMap_stalkMap_germ_of_comm`: the compatibility for an arbitrary
  commutative square over `Spec(A) → Y`.
* `AlgebraicGeometry.stalkMap_stalkMap_cast_of_comm`: the same for an arbitrary element of the
  local ring at `y`.
* `AlgebraicGeometry.isIso_residueFieldMap_and_map_maximalIdeal_of_compat`: the residue field
  isomorphism and the extension of the maximal ideal, transported along such identifications.
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Germs along two equal morphisms agree. -/
theorem germ_stalkMap_apply_of_eq {Z Y : Scheme.{u}} (φ ψ : Z ⟶ Y) (h : φ = ψ) (z : Z)
    (U : Y.Opens) (hz : φ z ∈ U) (t : Γ(Y, U)) :
    (φ.stalkMap z).hom (Y.presheaf.germ U (φ z) hz t) =
      (ψ.stalkMap z).hom (Y.presheaf.germ U (ψ z) (h ▸ hz) t) := by
  subst h; rfl

/-- **Compatibility of local rings along a square over `Spec(𝒪_{Y,y}) → Y`.** Let
`f : 𝒪_{Y,y} → A` be a local homomorphism and `k : Z → W` a morphism over
`Spec(A) → Spec(𝒪_{Y,y}) → Y`. Then a germ at `y` and its image in `A` have the same image in the
local ring of `Z` at any point. -/
theorem stalkMap_stalkMap_germ_of_comm {Y Z W : Scheme.{u}} {A : Type u} [CommRing A]
    [IsLocalRing A] {y : Y} (f : Y.presheaf.stalk y ⟶ CommRingCat.of A) [IsLocalHom f.hom]
    (k : Z ⟶ W) (πZ : Z ⟶ Spec (.of A)) (πW : W ⟶ Y)
    (h : k ≫ πW = πZ ≫ Spec.map f ≫ Y.fromSpecStalk y) (z : Z) (U : Y.Opens) (hU : y ∈ U)
    (t : Γ(Y, U)) (hz : πW (k z) ∈ U) :
    (k.stalkMap z).hom ((πW.stalkMap (k z)).hom (Y.presheaf.germ U _ hz t)) =
      stalkHomOfSpec πZ z (f.hom (Y.presheaf.germ U y hU t)) := by
  have hgcp : (Spec.map f ≫ Y.fromSpecStalk y) (closedPoint A) = y :=
    (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg (fun t => (Y.fromSpecStalk y).base t)
        AlgebraicGeometry.Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)
  have hU' : (Spec.map f ≫ Y.fromSpecStalk y) (closedPoint A) ∈ U := by rwa [hgcp]
  have hpre : (Spec.map f ≫ Y.fromSpecStalk y) ⁻¹ᵁ U = ⊤ :=
    Scheme.preimage_eq_top_of_closedPoint_mem _ hU'
  have key := (Scheme.germ_stalkClosedPointTo (Spec.map f ≫ Y.fromSpecStalk y) U hU').symm.trans
    (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk f U hU')
  have key2 := congrArg (fun φ => φ.hom t) key
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, Iso.trans_hom, Functor.mapIso_hom,
    Iso.op_hom, eqToIso.hom] at key2
  have e1 : (k.stalkMap z).hom ((πW.stalkMap (k z)).hom (Y.presheaf.germ U _ hz t)) =
      ((k ≫ πW).stalkMap z).hom (Y.presheaf.germ U ((k ≫ πW) z) hz t) := by
    rw [Scheme.Hom.stalkMap_comp]; rfl
  have e2 := germ_stalkMap_apply_of_eq (k ≫ πW) (πZ ≫ Spec.map f ≫ Y.fromSpecStalk y) h z U hz t
  have e3 : ((πZ ≫ Spec.map f ≫ Y.fromSpecStalk y).stalkMap z).hom
      (Y.presheaf.germ U ((πZ ≫ Spec.map f ≫ Y.fromSpecStalk y) z) (by rw [← h]; exact hz) t) =
      (πZ.stalkMap z).hom ((Spec (.of A)).presheaf.germ ((Spec.map f ≫ Y.fromSpecStalk y) ⁻¹ᵁ U)
        (πZ z) (by rw [hpre]; exact TopologicalSpace.Opens.mem_top _)
        ((Spec.map f ≫ Y.fromSpecStalk y).app U t)) := by
    rw [Scheme.Hom.stalkMap_comp]
    exact congrArg (πZ.stalkMap z).hom
      (Scheme.Hom.germ_stalkMap_apply (Spec.map f ≫ Y.fromSpecStalk y) U (πZ z) _ t)
  rw [e1, e2, e3, stalkHomOfSpec_apply]
  congr 1
  rw [← key2]
  have h1 : ∀ s, ((Scheme.ΓSpecIso (.of A)).inv ≫
      (Spec (.of A)).presheaf.germ ⊤ (πZ z) trivial).hom ((Scheme.ΓSpecIso (.of A)).hom.hom s) =
      (Spec (.of A)).presheaf.germ ⊤ (πZ z) trivial s := fun s => by simp
  rw [h1]
  exact (TopCat.Presheaf.germ_res_apply (Spec (.of A)).presheaf _ _ _ _).symm

/-- The same compatibility for an arbitrary element of the local ring at `y`, read at a point of
`Z` whose image in `Y` is `y`. -/
theorem stalkMap_stalkMap_cast_of_comm {Y Z W : Scheme.{u}} {A : Type u} [CommRing A]
    [IsLocalRing A] {y : Y} (f : Y.presheaf.stalk y ⟶ CommRingCat.of A) [IsLocalHom f.hom]
    (k : Z ⟶ W) (πZ : Z ⟶ Spec (.of A)) (πW : W ⟶ Y)
    (h : k ≫ πW = πZ ≫ Spec.map f ≫ Y.fromSpecStalk y) (z : Z) (hz : πW (k z) = y)
    (s : Y.presheaf.stalk y) :
    (k.stalkMap z).hom ((πW.stalkMap (k z)).hom (hz.symm ▸ s)) =
      stalkHomOfSpec πZ z (f.hom s) := by
  subst hz
  obtain ⟨U, hU, t, rfl⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf s
  exact stalkMap_stalkMap_germ_of_comm f k πZ πW h z U hU t hU

/-- **The conditions of a rule for choosing centres, read through an identification of local
rings.** Let `π : Z → Y` take `q` to `y`, let `A ≅ 𝒪_{Y,y}`, and let `𝒪_{Z,q} ≅ C` be compatible
with a ring map `φ : A → C`. If `φ` extends the maximal ideal of `A` to the ideal of `φ(a)` and
induces a surjection on residue fields, then the residue field map of `π` at `q` is an
isomorphism and the maximal ideal of `𝒪_{Y,y}` extends to the ideal of the image of `a`. -/
theorem isIso_residueFieldMap_and_map_maximalIdeal_of_compat {Z Y : Scheme.{u}} (π : Z ⟶ Y)
    (q : Z) (y : Y) (hq : π q = y) {A : Type u} [CommRing A] [IsLocalRing A]
    (f : A ≃+* Y.presheaf.stalk y) {C : Type u} [CommRing C] [IsLocalRing C]
    (α : Z.presheaf.stalk q ≃+* C) (φ : A →+* C)
    (hcompat : ∀ s, α ((π.stalkMap q).hom (hq.symm ▸ s)) = φ (f.symm s)) (a : A)
    (hmap : Ideal.map φ (maximalIdeal A) = Ideal.span {φ a})
    (hres : Function.Surjective ((residue C).comp φ)) :
    IsIso (π.residueFieldMap q) ∧
      Ideal.map (π.stalkMap q).hom (hq.symm ▸ maximalIdeal (Y.presheaf.stalk y)) =
        Ideal.span {(π.stalkMap q).hom (hq.symm ▸ f a)} := by
  subst hq
  set σ := (π.stalkMap q).hom
  have hc : ∀ s, α (σ s) = φ (f.symm s) := hcompat
  have hασ : ((α : _ →+* C).comp σ).comp (f : A →+* _) = φ := by
    ext b; simp [hc]
  refine ⟨?_, ?_⟩
  · rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨RingHom.injective _, fun t => ?_⟩
    obtain ⟨c, rfl⟩ := residue_surjective t
    obtain ⟨b, hb⟩ := hres (residue C (α c))
    refine ⟨residue _ (f b), ?_⟩
    change ResidueField.map σ (residue _ (f b)) = _
    rw [ResidueField.map_residue, ← sub_eq_zero, ← map_sub, residue_eq_zero_iff]
    have h1 : α (σ (f b) - c) ∈ maximalIdeal C := by
      rwa [map_sub, hc, RingEquiv.symm_apply_apply, ← residue_eq_zero_iff, map_sub, sub_eq_zero]
    exact fun hu => h1 (hu.map (α : _ →+* C))
  · have hm : maximalIdeal (Y.presheaf.stalk (π q)) = (maximalIdeal A).map (f : A →+* _) :=
      (map_ringEquiv_maximalIdeal f).symm
    change Ideal.map σ (maximalIdeal (Y.presheaf.stalk (π q))) = Ideal.span {σ (f a)}
    have hinj : Function.Injective (Ideal.map (α : Z.presheaf.stalk q →+* C)) :=
      Function.LeftInverse.injective (g := Ideal.comap (α : Z.presheaf.stalk q →+* C))
        fun _ => Ideal.comap_map_of_bijective _ α.bijective
    apply hinj
    rw [hm, Ideal.map_map, Ideal.map_map, hασ, hmap, Ideal.map_span, Set.image_singleton,
      RingEquiv.coe_toRingHom, hc, RingEquiv.symm_apply_apply]

end AlgebraicGeometry

end
