module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered
public import StacksCore.Tactic.StacksAttribute

/-!
# Residue fields in inverse limits of schemes

For a cofiltered diagram of schemes with affine transition morphisms, the residue field of a
point of the limit is the filtered colimit of the residue fields of its images in the stages.

The varying residue fields are presented by a functor on the opposite index category together
with isomorphisms identifying its objects and transition maps with the geometric residue fields
and their canonical maps. The conclusion is the universal property of the colimit of that
functor in commutative rings; it also records the canonical maps from the residue fields of the
images.

## Main results

* `AlgebraicGeometry.residueField_isColimit`: the universal property of the residue field of a
  point of the limit.

## Implementation notes

The colimit is recognised by the explicit criterion for filtered colimits of types
(`CategoryTheory.Limits.Types.FilteredColimit.isColimitOf'`), reflected back to commutative
rings. Injectivity of each comparison map is automatic because a map of fields is injective;
joint surjectivity is `residueFieldMap_jointly_surjective`, which spreads a germ at the limit
over an affine open of some stage and uses that the global sections of the limit of an affine
system are the colimit of the global sections.

## References

* [Stacks Project, Tag 0CUG](https://stacks.math.columbia.edu/tag/0CUG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Every element of the residue field of a point of a cofiltered limit of schemes with affine
transition morphisms comes from the residue field at one of its images. -/
private lemma residueFieldMap_jointly_surjective
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (s : c.pt) :
    ∀ z : c.pt.residueField s,
      ∃ (i : I) (x : (D.obj i).residueField (c.π.app i s)),
        (c.π.app i).residueFieldMap s x = z := by
  intro z
  obtain ⟨a, rfl⟩ := c.pt.residue_surjective s z
  obtain ⟨U, hsU, ⟨i, V, hV, rfl⟩, t, ht⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis
      (isBasis_preimage_isAffineOpen D c hc) c.pt.presheaf s a
  let E := opensDiagram D i V
  let ec := opensCone D c i V
  have (j : Over i) : IsAffine (E.obj j) := hV.preimage _
  have (j : (Over i)ᵒᵖ) : IsAffine (E.op.obj j).unop := hV.preimage _
  have hcolim : IsColimit ((Scheme.Γ ⋙ forget _).mapCocone ec.op) :=
    isColimitOfPreserves (Scheme.Γ ⋙ forget _) (isLimitOpensCone D c hc i V).op
  let t' : Γ(ec.pt, ⊤) := (c.π.app i ⁻¹ᵁ V).topIso.inv t
  obtain ⟨j, q, hq⟩ := Types.jointly_surjective_of_isColimit hcolim t'
  obtain ⟨q', rfl⟩ :=
    (D.map j.unop.hom ⁻¹ᵁ V).topIso.symm.commRingCatIsoToRingEquiv.surjective q
  have hsV : c.π.app j.unop.left s ∈ D.map j.unop.hom ⁻¹ᵁ V := by
    change (c.π.app j.unop.left ≫ D.map j.unop.hom) s ∈ V
    rw [c.w]
    exact hsU
  have hUeq : c.π.app j.unop.left ⁻¹ᵁ (D.map j.unop.hom ⁻¹ᵁ V) = c.π.app i ⁻¹ᵁ V := by
    rw [← Scheme.Hom.comp_preimage, c.w]
  refine ⟨j.unop.left, (D.obj j.unop.left).evaluation _ _ hsV q', ?_⟩
  rw [Scheme.evaluation_naturality_apply, ← ht]
  have hres : (D.map j.unop.hom ⁻¹ᵁ V).topIso.inv ≫
      ((c.π.app j.unop.left).resLE (D.map j.unop.hom ⁻¹ᵁ V)
        (c.π.app i ⁻¹ᵁ V) hUeq.symm.le).appTop ≫ (c.π.app i ⁻¹ᵁ V).topIso.hom =
      (c.π.app j.unop.left).appLE (D.map j.unop.hom ⁻¹ᵁ V)
        (c.π.app i ⁻¹ᵁ V) hUeq.symm.le := by
    rw [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hsec' : t = ((c.π.app j.unop.left).appLE (D.map j.unop.hom ⁻¹ᵁ V)
      (c.π.app i ⁻¹ᵁ V) hUeq.symm.le) q' := by
    rw [← hres]
    exact (c.π.app i ⁻¹ᵁ V).topIso.commRingCatIsoToRingEquiv.symm_apply_eq.mp hq.symm
  change c.pt.residue s (c.pt.presheaf.germ _ s _ ((c.π.app j.unop.left).app _ q')) =
    c.pt.residue s (c.pt.presheaf.germ _ s _ t)
  rw [hsec', Scheme.Hom.appLE, ConcreteCategory.comp_apply]
  exact congrArg _ (c.pt.presheaf.germ_res_apply (homOfLE hUeq.symm.le) s hsU _).symm

/-- **Stacks Project, Tag 0CUG.** The residue field of a point in a cofiltered limit of schemes
with affine transition morphisms is the filtered colimit of the residue fields of its images. -/
@[stacks 0CUG "residue_fields"]
theorem residueField_isColimit
    {I : Type u} [Category.{u} I] [IsCofiltered I]
    (D : I ⥤ Scheme.{u})
    [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]
    (c : Cone D) (hc : IsLimit c) (s : c.pt)
    (K : Iᵒᵖ ⥤ CommRingCat.{u})
    (e : ∀ i : I,
      K.obj (Opposite.op i) ≅ (D.obj i).residueField (c.π.app i s))
    (hK : ∀ {i j : I} (f : i ⟶ j),
      K.map f.op =
        (e j).hom ≫
          ((D.obj j).residueFieldCongr (by
            symm
            change (c.π.app i ≫ D.map f) s = _
            rw [c.w f])).hom ≫
          (D.map f).residueFieldMap (c.π.app i s) ≫ (e i).inv) :
    ∀ (T : CommRingCat.{u})
      (φ : ∀ i : I, K.obj (Opposite.op i) ⟶ T),
      (∀ {i j : I} (f : i ⟶ j), K.map f.op ≫ φ i = φ j) →
      ∃! ψ : c.pt.residueField s ⟶ T,
        ∀ i : I, (e i).hom ≫ (c.π.app i).residueFieldMap s ≫ ψ = φ i := by
  let μ : ∀ i : I, K.obj (Opposite.op i) ⟶ c.pt.residueField s :=
    fun i ↦ (e i).hom ≫ (c.π.app i).residueFieldMap s
  have hμ {i j : I} (f : i ⟶ j) : K.map f.op ≫ μ i = μ j := by
    simp only [μ, hK, Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Scheme.residueFieldMap_comp]
    simpa using (Scheme.Hom.residueFieldMap_congr (c.w f).symm s).symm
  let d : Cocone K := Cocone.mk (c.pt.residueField s) ⟨fun j ↦ μ j.unop,
    fun {i j} f ↦ hμ f.unop⟩
  have hsurj (z : d.pt) : ∃ i x, z = d.ι.app i x := by
    obtain ⟨i, x, hx⟩ := residueFieldMap_jointly_surjective D c hc s z
    refine ⟨Opposite.op i, (e i).inv x, ?_⟩
    simpa [d, μ] using hx.symm
  have hinj (i : Iᵒᵖ) (x y : K.obj i) (hxy : d.ι.app i x = d.ι.app i y) :
      ∃ (k : Iᵒᵖ) (f : i ⟶ k), K.map f x = K.map f y := by
    refine ⟨i, 𝟙 i, ?_⟩
    simpa using ((RingHom.injective ((c.π.app i.unop).residueFieldMap s).hom).comp
      (e i.unop).commRingCatIsoToRingEquiv.injective) hxy
  have : ReflectsColimit K (forget CommRingCat.{u}) :=
    reflectsColimit_of_reflectsIsomorphisms K (forget CommRingCat.{u})
  have hd : IsColimit d := isColimitOfReflects (forget CommRingCat.{u})
    (Types.FilteredColimit.isColimitOf' (K ⋙ forget _) _ hsurj hinj)
  intro T φ hφ
  let t : Cocone K := Cocone.mk T ⟨fun j ↦ φ j.unop, fun {i j} f ↦ hφ f.unop⟩
  exact ⟨hd.desc t, fun i ↦ hd.fac t (Opposite.op i),
    fun m hm ↦ hd.uniq t m (fun i ↦ hm i.unop)⟩

end AlgebraicGeometry

end
