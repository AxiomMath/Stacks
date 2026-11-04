module

public import StacksFrontier.AlgebraicGeometry.SegreChartProduct.Ring
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# `Spec` of a ring isomorphism, and the geometric form of `awayCongr`

Two pieces of glue needed to compare the chart-level ring isomorphisms of
`StacksFrontier/AlgebraicGeometry/SegreChartProduct/Ring.lean` with morphisms of schemes.

## Main definitions

* `Stacks.AlgebraicGeometry.SegreProdIso.specIsoOfRingEquiv`: `Spec` of a ring isomorphism, as an
  isomorphism of schemes whose `hom` is `Spec.map` of the forward ring homomorphism *by
  definition*.  `AlgebraicGeometry.Spec` is a functor out of the opposite category, so the
  isomorphism obtained from `CategoryTheory.Functor.mapIso` has the wrong objects up to
  `Opposite.op`, and its `hom` is not syntactically a `Spec.map`; both matter when the
  isomorphism is fed to `CategoryTheory.IsPullback.of_iso`.

## Main results

* `Stacks.AlgebraicGeometry.SegreProdIso.basicOpenToSpec_awayCongr`: the geometric content of
  `Stacks.AlgebraicGeometry.SegreChartProduct.awayCongr`.  Transporting a degree-zero homogeneous
  localisation along an equality of elements is, on `Spec`, the transport of the standard open
  along the induced equality of opens.  This is what lets the geometric layer, which localises at
  `Stacks.AlgebraicGeometry.SegreProjection.substLeftGraded R X Y j (MvPolynomial.X i)`, be
  compared with the ring-theoretic layer, which localises at
  `Stacks.AlgebraicGeometry.SegreCharts.genSub R X Y (i, j)`.

## References

* [Stacks Project, Tag 01WD](https://stacks.math.columbia.edu/tag/01WD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Stacks.AlgebraicGeometry.SegreProdIso

universe u w

/-! ### `Spec` of a ring isomorphism -/

/-- **`Spec` of a ring isomorphism.**  The `hom` field is `Spec.map` of the forward ring
homomorphism by definition, which is what the comparison lemmas need. -/
public def specIsoOfRingEquiv {S T : Type u} [CommRing S] [CommRing T] (e : S ≃+* T) :
    Spec (CommRingCat.of T) ≅ Spec (CommRingCat.of S) where
  hom := Spec.map (CommRingCat.ofHom e.toRingHom)
  inv := Spec.map (CommRingCat.ofHom e.symm.toRingHom)
  hom_inv_id := by
    have h : CommRingCat.ofHom e.symm.toRingHom ≫ CommRingCat.ofHom e.toRingHom =
        CommRingCat.ofHom (RingHom.id T) := by
      rw [← CommRingCat.ofHom_comp]
      congr 1
      ext x
      simp
    rw [← Spec.map_comp, h, CommRingCat.ofHom_id, Spec.map_id]
  inv_hom_id := by
    have h : CommRingCat.ofHom e.toRingHom ≫ CommRingCat.ofHom e.symm.toRingHom =
        CommRingCat.ofHom (RingHom.id S) := by
      rw [← CommRingCat.ofHom_comp]
      congr 1
      ext x
      simp
    rw [← Spec.map_comp, h, CommRingCat.ofHom_id, Spec.map_id]

/-- The `hom` of `specIsoOfRingEquiv e` is `Spec.map` of `e`. -/
@[simp] public theorem specIsoOfRingEquiv_hom {S T : Type u} [CommRing S] [CommRing T]
    (e : S ≃+* T) :
    (specIsoOfRingEquiv e).hom = Spec.map (CommRingCat.ofHom e.toRingHom) := rfl

/-- The `inv` of `specIsoOfRingEquiv e` is `Spec.map` of `e.symm`. -/
@[simp] public theorem specIsoOfRingEquiv_inv {S T : Type u} [CommRing S] [CommRing T]
    (e : S ≃+* T) :
    (specIsoOfRingEquiv e).inv = Spec.map (CommRingCat.ofHom e.symm.toRingHom) := rfl

/-! ### The geometric form of `awayCongr` -/

section AwayCongr

variable {A : Type u} [CommRing A] {σ : Type w} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-- **The geometric form of `Stacks.AlgebraicGeometry.SegreChartProduct.awayCongr`.**  If `f = g`
then the canonical map `D₊(g) ⟶ Spec A_{(g)}` followed by `Spec` of the transport
`A_{(f)} ≃+* A_{(g)}` is the transport `D₊(g) ≅ D₊(f)` followed by the canonical map
`D₊(f) ⟶ Spec A_{(f)}`. -/
@[reassoc]
public theorem basicOpenToSpec_awayCongr {f g : A} (h : f = g) :
    AlgebraicGeometry.Proj.basicOpenToSpec 𝒜 g ≫
        Spec.map (CommRingCat.ofHom
          (SegreChartProduct.awayCongr 𝒜 h).toRingHom) =
      ((AlgebraicGeometry.Proj 𝒜).isoOfEq
          (congrArg (AlgebraicGeometry.Proj.basicOpen 𝒜) h.symm)).hom ≫
        AlgebraicGeometry.Proj.basicOpenToSpec 𝒜 f := by
  subst h
  rw [Scheme.isoOfEq_rfl, Iso.refl_hom, Category.id_comp]
  have hid : CommRingCat.ofHom
      (SegreChartProduct.awayCongr 𝒜 (rfl : f = f)).toRingHom =
      CommRingCat.ofHom (RingHom.id (HomogeneousLocalization.Away 𝒜 f)) := rfl
  rw [hid, CommRingCat.ofHom_id, Spec.map_id, Category.comp_id]

end AwayCongr

end Stacks.AlgebraicGeometry.SegreProdIso

end
