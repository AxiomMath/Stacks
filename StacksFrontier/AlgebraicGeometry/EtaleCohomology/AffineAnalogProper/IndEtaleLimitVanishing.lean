module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitCohomologyQcqsRestriction
public import StacksFrontier.AlgebraicGeometry.SpecLimitOfIndSmooth
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport

/-!
# Cohomology over the spectrum of an ind-étale algebra

Let `A → B` be ind-étale, i.e. `B` is a filtered colimit of étale `A`-algebras `B_i`, and let `G`
be an abelian sheaf on `(Spec A)_étale` whose restriction to every affine scheme étale over
`Spec A` has no higher cohomology. Then the restriction of `G` to `Spec B` has no higher
cohomology either.

This is the step of the proof of Stacks 0A51 that applies Stacks 09YQ: `Spec B` is the limit of
the affine schemes `Spec B_i`, with affine transition morphisms, so every class of
`H^q(Spec B, G|_{Spec B})` comes from some `H^q(Spec B_i, G|_{Spec B_i})`
(`Stacks.EtaleCohomology.LimitExt.exists_le_restriction_eq_of_qcqs`), which vanishes because
`Spec B_i ⟶ Spec A` is étale. The filtered index category of the presentation is replaced by a
directed set mapping finally to it (Stacks 0032), the form in which Stacks 09YQ is stated.

## Main results

* `Stacks.EtaleCohomology.subsingleton_H_inverseImage_of_indEtale`.

## References

* [Stacks Project, Tag 0A51](https://stacks.math.columbia.edu/tag/0A51)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry Opposite

universe u

namespace Stacks.EtaleCohomology

/-- **Restriction to the spectrum of an ind-étale algebra keeps acyclicity.** Let `A → B` be
ind-étale and `G` an abelian sheaf on `(Spec A)_étale` with `H^q(W, G|_W) = 0` for every `q > 0`
and every affine `W` étale over `Spec A`. Then `H^q(Spec B, G|_{Spec B}) = 0` for every `q > 0`. -/
theorem subsingleton_H_inverseImage_of_indEtale {A B : Type u} [CommRing A] [CommRing B]
    [Algebra A B] (hB : (CommAlgCat.etale.{u} A).ind.{u} (CommAlgCat.of A B))
    (G : Sheaf (Spec (.of A)).smallEtaleTopology AddCommGrpCat.{u + 1})
    (hG : ∀ (W : Scheme.{u}) [IsAffine W] (j : W ⟶ Spec (.of A)) [Etale j] (q : ℕ), 0 < q →
      Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} j).obj G) q))
    (q : ℕ) (hq : 0 < q) :
    Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (Spec.map (CommRingCat.ofHom (algebraMap A B)))).obj G) q) := by
  obtain ⟨J, _, _, pres, hP⟩ := hB
  obtain ⟨α, _, _, hne, F, _⟩ := IsFiltered.exists_directed J
  let a₀ : α := hne.some
  let presU := (pres.reindex F).map (commAlgCatEquivUnder (.of A)).functor
  let L := specUnderLimitPresentation presU
  let D := L.diag
  let c : Cone D := ⟨_, L.π⟩
  let f : ∀ i, D.obj i ⟶ Spec (.of A) := fun i => (specUnderStructureMap presU.diag).app i
  have : ∀ i, Etale (f i) := fun i =>
    prop_specUnderStructureMap_app (P := @Etale) presU.diag i (by
      change (algebraMap A (pres.diag.obj (F.obj i.unop) : Type u)).Etale
      exact RingHom.etale_algebraMap.mpr (hP (F.obj i.unop)))
  have hDf : ∀ {i j : αᵒᵖ} (g : i ⟶ j), D.map g ≫ f j = f i := fun g =>
    ((specUnderStructureMap presU.diag).naturality g).trans (Category.comp_id _)
  have : ∀ i, IsAffine (D.obj i) := fun i => isAffine_specUnderDiagram_obj presU.diag i
  have : ∀ {i j : αᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := fun _ => inferInstance
  let G₀ := (etaleAbelianInverseImage.{u, 0} (f (op a₀))).obj G
  refine Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
    ((etaleAbelianInverseImageCompIso'.{u, 0} (c.π.app (op a₀)) (f (op a₀)) _
      (specUnderLimitPresentation_π_comp_structureMap presU (op a₀)).symm).app G).symm q ?_
  suffices h : ∀ z : Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0} (c.π.app (op a₀))).obj G₀)
      q, z = 0 from ⟨fun x y => (h x).trans (h y).symm⟩
  intro z
  obtain ⟨i, h, y, hy⟩ := LimitExt.exists_le_restriction_eq_of_qcqs D c L.isLimit a₀ G₀ q z
  have hvan : Subsingleton (Sheaf.H.{u + 1} ((etaleAbelianInverseImage.{u, 0}
      (D.map (homOfLE h).op)).obj G₀) q) :=
    Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
      ((etaleAbelianInverseImageCompIso'.{u, 0} (D.map (homOfLE h).op) (f (op a₀)) (f (op i))
        (hDf _).symm).app G) q (hG (D.obj (op i)) (f (op i)) q hq)
  rw [← hy, hvan.elim y 0, map_zero, Ext.zero_comp]

end Stacks.EtaleCohomology
