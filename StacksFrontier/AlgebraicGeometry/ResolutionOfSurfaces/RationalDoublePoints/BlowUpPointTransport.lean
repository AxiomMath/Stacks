module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.StageSituation

/-!
# Points of the blowup of a closed point and of the blowup of the local ring there

Let `p` be a closed point of a scheme `X` and let `A` be a local ring together with an
isomorphism `e : A ≃+* 𝒪_{X, p}`. Blowing up `p` in `X` becomes, after the flat base change
`g : Spec A ≅ Spec 𝒪_{X, p} ⟶ X`, the blowup of `Spec A` in the maximal ideal of `A`
([Stacks, Tag 0805]). The morphism `h` between the two blowups is a flat preimmersion, so it
identifies the points of the blowup of `Spec A` lying over the closed point with the points of
the blowup of `X` lying over `p`, with isomorphic local rings.

The isomorphism of local rings is compatible with the maps from the local ring at the centre.
On the side of `Spec A` that map is `AlgebraicGeometry.maximalIdealBlowUpStalkHom`, the canonical
homomorphism from `A` to a local ring of its blowup, through the global sections; on the side of
`X` it is the stalk map of the blowup morphism.

## Main definitions

* `AlgebraicGeometry.maximalIdealBlowUpStalkHom`: the canonical homomorphism from a local ring
  `A` to the local ring of the blowup of `Spec A` in the maximal ideal at a point.

## Main results

* `AlgebraicGeometry.exists_isPullback_blowUp_maximalIdealSheaf`: the blowup of `Spec A` in the
  maximal ideal is the base change of the blowup of `X` in `p`, along a flat preimmersion.
* `AlgebraicGeometry.stalkMap_stalkMap_eqRec_eq_maximalIdealBlowUpStalkHom`: the compatibility of
  the stalk maps of such a square with `AlgebraicGeometry.maximalIdealBlowUpStalkHom`.
* `AlgebraicGeometry.exists_blowUp_point_of_maximalIdealSheaf`: a point of the blowup of `Spec A`
  over the closed point gives a point of the blowup of `X` over `p`, with a compatible
  isomorphism of local rings.
* `AlgebraicGeometry.exists_maximalIdealSheaf_point_of_blowUp`: conversely.

## References

* [Stacks Project, Tag 0805](https://stacks.math.columbia.edu/tag/0805)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The canonical homomorphism from a local ring `A` to the local ring at a point `q` of the
blowup of `Spec A` in the maximal ideal: the germ at the image of `q` of a global section of
`Spec A`, followed by the stalk map of the blowup morphism. -/
def maximalIdealBlowUpStalkHom (A : Type u) [CommRing A] [IsLocalRing A]
    (q : blowUp (maximalIdealSheaf A)) :
    A →+* (blowUp (maximalIdealSheaf A)).presheaf.stalk q :=
  ((Scheme.ΓSpecIso (.of A)).inv ≫
    (Spec (.of A)).presheaf.germ ⊤ (blowUpToBase (maximalIdealSheaf A) q) trivial ≫
      (blowUpToBase (maximalIdealSheaf A)).stalkMap q).hom

/-- `AlgebraicGeometry.maximalIdealBlowUpStalkHom` through the global sections of the blowup. -/
theorem maximalIdealBlowUpStalkHom_eq (A : Type u) [CommRing A] [IsLocalRing A]
    (q : blowUp (maximalIdealSheaf A)) :
    maximalIdealBlowUpStalkHom A q =
      ((Scheme.ΓSpecIso (.of A)).inv ≫ (blowUpToBase (maximalIdealSheaf A)).appTop ≫
        (blowUp (maximalIdealSheaf A)).presheaf.germ ⊤ q trivial).hom :=
  congrArg (fun k => ((Scheme.ΓSpecIso (.of A)).inv ≫ k).hom)
    (Scheme.Hom.germ_stalkMap (blowUpToBase (maximalIdealSheaf A)) ⊤ q trivial)

/-- Transport of an element of a local ring along an equality of points is the isomorphism of
local rings the equality induces. -/
theorem eqRec_stalk_eq_stalkCongr {X : Scheme.{u}} {x x' : X} (h : x = x')
    (y : X.presheaf.stalk x) :
    (h ▸ y : X.presheaf.stalk x') = (X.presheaf.stalkCongr (.of_eq h)).hom y := by
  subst h
  simp

/-- The germ of a section, transported along an equality of points and pushed through a stalk
map, is the germ of the pulled back section. -/
private theorem germ_stalkCongr_stalkMap {Z X : Scheme.{u}} (k : Z ⟶ X) (z : Z) {x : X}
    (hx : k z = x) (U : X.Opens) (hU : x ∈ U) :
    X.presheaf.germ U x hU ≫ (X.presheaf.stalkCongr (.of_eq hx.symm)).hom ≫ k.stalkMap z =
      k.app U ≫ Z.presheaf.germ (k ⁻¹ᵁ U) z (by rw [Scheme.Hom.mem_preimage, hx]; exact hU) := by
  subst hx
  simp [Scheme.Hom.germ_stalkMap]

/-- Equal morphisms pull back germs in the same way. -/
private theorem app_germ_congr {Z X : Scheme.{u}} {k₁ k₂ : Z ⟶ X} (hk : k₁ = k₂) (z : Z)
    (U : X.Opens) (h₁ : z ∈ k₁ ⁻¹ᵁ U) (h₂ : z ∈ k₂ ⁻¹ᵁ U) :
    k₁.app U ≫ Z.presheaf.germ (k₁ ⁻¹ᵁ U) z h₁ = k₂.app U ≫ Z.presheaf.germ (k₂ ⁻¹ᵁ U) z h₂ := by
  subst hk
  rfl

section Transport

variable (A : Type u) [CommRing A] [IsLocalRing A] {X : Scheme.{u}} (p : X)
  (hp : IsClosed ({p} : Set X)) (e : A ≃+* X.presheaf.stalk p)

/-- The morphism `Spec A ≅ Spec 𝒪_{X, p} ⟶ X` attached to an isomorphism `A ≃+* 𝒪_{X, p}`. -/
abbrev specToOfRingEquivStalk : Spec (.of A) ⟶ X :=
  Spec.map (CommRingCat.ofHom (e.symm : X.presheaf.stalk p →+* A)) ≫ X.fromSpecStalk p

/-- The inverse of `e` is a local homomorphism, being surjective. -/
private instance : IsLocalHom (CommRingCat.ofHom (e.symm : X.presheaf.stalk p →+* A)).hom :=
  IsLocalHom.of_surjective _ e.symm.surjective

/-- `Spec A ⟶ X` is flat: it is an isomorphism onto `Spec 𝒪_{X, p}` followed by the flat
morphism `Spec 𝒪_{X, p} ⟶ X`. -/
instance : Flat (specToOfRingEquivStalk A p e) := by
  have : Flat (X.fromSpecStalk p) := flat_fromSpecStalk X p
  have : IsIso (CommRingCat.ofHom (e.symm : X.presheaf.stalk p →+* A)) :=
    e.symm.toCommRingCatIso.isIso_hom
  infer_instance

/-- `Spec A ⟶ X` is a preimmersion: it is an isomorphism onto `Spec 𝒪_{X, p}` followed by the
preimmersion `Spec 𝒪_{X, p} ⟶ X`. -/
instance : IsPreimmersion (specToOfRingEquivStalk A p e) := by
  have : IsIso (CommRingCat.ofHom (e.symm : X.presheaf.stalk p →+* A)) :=
    e.symm.toCommRingCatIso.isIso_hom
  infer_instance

/-- The closed point of `Spec A` goes to `p`. -/
theorem specToOfRingEquivStalk_closedPoint :
    specToOfRingEquivStalk A p e (closedPoint A) = p := by
  exact (Scheme.Hom.comp_apply _ _ _).trans
    ((congrArg (fun t => (X.fromSpecStalk p).base t)
      AlgebraicGeometry.Spec_closedPoint).trans Scheme.fromSpecStalk_closedPoint)

/-- A point of `Spec A` going to `p` is the closed point. -/
theorem eq_closedPoint_of_specToOfRingEquivStalk_eq {y : Spec (.of A)}
    (hy : specToOfRingEquivStalk A p e y = p) : y = closedPoint A :=
  (specToOfRingEquivStalk A p e).isEmbedding.injective
    (hy.trans (specToOfRingEquivStalk_closedPoint A p e).symm)

/-- The inverse image of the centre `p` along `Spec A ⟶ X` is the maximal ideal sheaf. -/
theorem comap_specToOfRingEquivStalk_vanishingIdeal :
    (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X)).comap
      (specToOfRingEquivStalk A p e) = maximalIdealSheaf A := by
  rw [Scheme.IdealSheafData.comap_comp, comap_fromSpecStalk_vanishingIdeal_singleton X p hp,
    comap_maximalIdealSheaf_specMap_ringEquiv]

/-- **The blowup of `Spec A` in the maximal ideal is the base change of the blowup of `X` in a
closed point `p`** along `Spec A ≅ Spec 𝒪_{X, p} ⟶ X` ([Stacks, Tag 0805]); the morphism between
the blowups is a flat preimmersion. -/
theorem exists_isPullback_blowUp_maximalIdealSheaf :
    ∃ h : blowUp (maximalIdealSheaf A) ⟶
        blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X)),
      IsPullback (blowUpToBase (maximalIdealSheaf A)) h (specToOfRingEquivStalk A p e)
        (blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X))) ∧
      Flat h ∧ IsPreimmersion h := by
  have key := exists_isPullback_blowUpToBase_comap (specToOfRingEquivStalk A p e)
    (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X))
  rw [comap_specToOfRingEquivStalk_vanishingIdeal A p hp e] at key
  obtain ⟨h, hsq⟩ := key
  exact ⟨h, hsq, MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance,
    MorphismProperty.IsStableUnderBaseChange.of_isPullback hsq inferInstance⟩

variable {A p e} in
/-- **Compatibility of the stalk maps with the map from the local ring at the centre.** In a
commutative square from the blowup of `Spec A` to the blowup of `X` over `Spec A ⟶ X`, the
image of `e a` under the stalk maps of the blowup of `X` and of `h` is the image of `a` under
`AlgebraicGeometry.maximalIdealBlowUpStalkHom`. -/
theorem stalkMap_stalkMap_eqRec_eq_maximalIdealBlowUpStalkHom {Y : Scheme.{u}}
    {b : Y ⟶ X} {h : blowUp (maximalIdealSheaf A) ⟶ Y}
    (w : blowUpToBase (maximalIdealSheaf A) ≫ specToOfRingEquivStalk A p e = h ≫ b)
    (z : blowUp (maximalIdealSheaf A)) (hq : b (h z) = p) (a : A) :
    (h.stalkMap z).hom ((b.stalkMap (h z)).hom (hq.symm ▸ e a)) =
      maximalIdealBlowUpStalkHom A z a := by
  rw [eqRec_stalk_eq_stalkCongr]
  set g := specToOfRingEquivStalk A p e
  suffices hhom : (X.presheaf.stalkCongr (.of_eq hq.symm)).hom ≫ b.stalkMap (h z) ≫
      h.stalkMap z = CommRingCat.ofHom (e.symm : X.presheaf.stalk p →+* A) ≫
        CommRingCat.ofHom (maximalIdealBlowUpStalkHom A z) by
    simpa using congrArg (fun k => k.hom (e a)) hhom
  refine TopCat.Presheaf.stalk_hom_ext _ fun U hU => ?_
  have hgU : g (closedPoint A) ∈ U := by rwa [specToOfRingEquivStalk_closedPoint]
  have hL : X.presheaf.germ U p hU ≫ (X.presheaf.stalkCongr (.of_eq hq.symm)).hom ≫
      b.stalkMap (h z) ≫ h.stalkMap z =
      (h ≫ b).app U ≫ (blowUp (maximalIdealSheaf A)).presheaf.germ ((h ≫ b) ⁻¹ᵁ U) z
        (by rw [Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, hq]; exact hU) := by
    rw [reassoc_of% (germ_stalkCongr_stalkMap b (h z) hq U hU), Scheme.Hom.germ_stalkMap]
    rfl
  have hR : X.presheaf.germ U p hU ≫ CommRingCat.ofHom (e.symm : X.presheaf.stalk p →+* A) =
      g.app U ≫ ((Spec (.of A)).presheaf.mapIso (eqToIso
        (Scheme.preimage_eq_top_of_closedPoint_mem g hgU).symm).op ≪≫
          Scheme.ΓSpecIso (.of A)).hom := by
    rw [← Scheme.germ_stalkClosedPointTo g U hgU]
    exact (Scheme.germ_stalkClosedPointTo_Spec_fromSpecStalk
      (CommRingCat.ofHom (e.symm : X.presheaf.stalk p →+* A)) U hgU).symm
  have hz' : z ∈ (blowUpToBase (maximalIdealSheaf A) ≫ g) ⁻¹ᵁ U := by
    rwa [w, Scheme.Hom.mem_preimage, Scheme.Hom.comp_apply, hq]
  have hfin : (blowUpToBase (maximalIdealSheaf A) ≫ g).app U ≫
      (blowUp (maximalIdealSheaf A)).presheaf.germ _ z hz' =
      (X.presheaf.germ U p hU ≫ CommRingCat.ofHom (e.symm : X.presheaf.stalk p →+* A)) ≫
        CommRingCat.ofHom (maximalIdealBlowUpStalkHom A z) := by
    rw [hR]
    simp only [maximalIdealBlowUpStalkHom, CommRingCat.ofHom_hom, Iso.trans_hom,
      Functor.mapIso_hom, Iso.op_hom, eqToIso.hom, Category.assoc, Iso.hom_inv_id_assoc,
      Scheme.Hom.comp_app]
    refine (Category.assoc _ _ _).trans (congrArg (fun t => g.app U ≫ t) ?_)
    exact ((Scheme.Hom.germ_stalkMap (blowUpToBase (maximalIdealSheaf A)) (g ⁻¹ᵁ U) z
      hz').symm.trans (congrArg (· ≫ (blowUpToBase (maximalIdealSheaf A)).stalkMap z)
        (TopCat.Presheaf.germ_res (Spec (CommRingCat.of A)).presheaf
          (eqToHom (Scheme.preimage_eq_top_of_closedPoint_mem g hgU).symm) _ trivial).symm)).trans
      (Category.assoc _ _ _)
  rw [hL]
  exact (app_germ_congr w.symm z U _ hz').trans (hfin.trans (Category.assoc _ _ _))

/-- **A point of the blowup of `Spec A` over the closed point gives a point of the blowup of `X`
over `p`**, with an isomorphism of local rings compatible with the maps from the local ring at
the centre: the image of `e a` under the stalk map of the blowup morphism of `X` corresponds to
the image of `a` under `AlgebraicGeometry.maximalIdealBlowUpStalkHom`. If the given point is
closed, so is the point of the blowup of `X`. -/
theorem exists_blowUp_point_of_maximalIdealSheaf (z : blowUp (maximalIdealSheaf A))
    (hz : blowUpToBase (maximalIdealSheaf A) z = closedPoint A) :
    ∃ (q : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X)))
      (hq : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X)) q = p)
      (ε : (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X))).presheaf.stalk q
        ≃+* (blowUp (maximalIdealSheaf A)).presheaf.stalk z),
      (∀ a : A, ε (((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{p}, hp⟩ : Closeds X))).stalkMap q).hom (hq.symm ▸ e a)) =
          maximalIdealBlowUpStalkHom A z a) ∧
      (IsClosed ({z} : Set (blowUp (maximalIdealSheaf A))) →
        IsClosed ({q} : Set (blowUp (Scheme.IdealSheafData.vanishingIdeal
          (⟨{p}, hp⟩ : Closeds X))))) := by
  obtain ⟨h, hsq, _, _⟩ := exists_isPullback_blowUp_maximalIdealSheaf A p hp e
  have : IsIso (h.stalkMap z) := isIso_stalkMap_of_flat_isPreimmersion h z
  have hq : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X)) (h z) =
      p := by
    calc blowUpToBase _ (h z) = (h ≫ blowUpToBase _) z := rfl
      _ = (blowUpToBase (maximalIdealSheaf A) ≫ specToOfRingEquivStalk A p e) z := by
          rw [hsq.w]
      _ = specToOfRingEquivStalk A p e (blowUpToBase (maximalIdealSheaf A) z) := rfl
      _ = p := by rw [hz]; exact specToOfRingEquivStalk_closedPoint A p e
  refine ⟨h z, hq, (asIso (h.stalkMap z)).commRingCatIsoToRingEquiv, fun a => ?_, fun hzc => ?_⟩
  · exact stalkMap_stalkMap_eqRec_eq_maximalIdealBlowUpStalkHom hsq.w z hq a
  · obtain ⟨C, hC, hCz⟩ := (h.isEmbedding.isClosed_iff).mp hzc
    have hfib : IsClosed ((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{p}, hp⟩ : Closeds X))).base ⁻¹' {p}) := hp.preimage (Scheme.Hom.continuous _)
    convert hfib.inter hC using 1
    ext q'
    simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_preimage]
    refine ⟨fun hq' => hq' ▸ ⟨hq, ?_⟩, fun ⟨hq', hq'C⟩ => ?_⟩
    · exact (hCz ▸ Set.mem_singleton z : z ∈ h.base ⁻¹' C)
    · obtain ⟨z', hz'1, hz'2⟩ := Scheme.exists_preimage_of_isPullback hsq (closedPoint A) q'
        (by rw [hq']; exact specToOfRingEquivStalk_closedPoint A p e)
      have : z' ∈ h.base ⁻¹' C := by rwa [Set.mem_preimage, hz'2]
      rw [hCz] at this
      rw [← hz'2, this]

/-- **A point of the blowup of `X` over `p` comes from a point of the blowup of `Spec A` over
the closed point**, with isomorphic local rings, compatibly with the maps from the local ring at
the centre. -/
theorem exists_maximalIdealSheaf_point_of_blowUp
    (q : blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X)))
    (hq : blowUpToBase (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X)) q = p) :
    ∃ (z : blowUp (maximalIdealSheaf A))
      (_ : blowUpToBase (maximalIdealSheaf A) z = closedPoint A)
      (ε : (blowUp (Scheme.IdealSheafData.vanishingIdeal (⟨{p}, hp⟩ : Closeds X))).presheaf.stalk q
        ≃+* (blowUp (maximalIdealSheaf A)).presheaf.stalk z),
      ∀ a : A, ε (((blowUpToBase (Scheme.IdealSheafData.vanishingIdeal
        (⟨{p}, hp⟩ : Closeds X))).stalkMap q).hom (hq.symm ▸ e a)) =
          maximalIdealBlowUpStalkHom A z a := by
  obtain ⟨h, hsq, _, _⟩ := exists_isPullback_blowUp_maximalIdealSheaf A p hp e
  obtain ⟨z, hz1, hz2⟩ := Scheme.exists_preimage_of_isPullback hsq (closedPoint A) q
    (by rw [hq]; exact specToOfRingEquivStalk_closedPoint A p e)
  subst hz2
  have : IsIso (h.stalkMap z) := isIso_stalkMap_of_flat_isPreimmersion h z
  exact ⟨z, hz1, (asIso (h.stalkMap z)).commRingCatIsoToRingEquiv,
    fun a => stalkMap_stalkMap_eqRec_eq_maximalIdealBlowUpStalkHom hsq.w z hq a⟩

end Transport

end AlgebraicGeometry

end
