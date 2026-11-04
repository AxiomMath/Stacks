module

public import StacksFrontier.AlgebraicGeometry.StrictTransform.AffineChartExistence
public import StacksFrontier.RingTheory.Flat.BlowupGeometricallyIntegralFibres
public import StacksFrontier.RingTheory.GeometricallyIntegral.TensorProduct
public import StacksFrontier.RingTheory.Ideal.SymbolicPower

/-!
# The image of an affine chart of a base change, and the generic points of its fibres

Let `f : X ⟶ S` be a morphism of affine schemes, `b : S' ⟶ S` any morphism and
`c : Spec T ⟶ S'` an affine chart of the second factor lying over `Spec` of the structure map of
`T`. `Stacks.StrictTransform.affineBaseChangeChartMap` turns `c` into the chart

  `Spec (Γ(X, ⊤) ⊗_{Γ(S, ⊤)} T) ⟶ X ×_S S'`

of the base change. This file answers two questions about that chart which the conclusion of
[Stacks, Tag 0810] has to be read against: *which points of `X ×_S S'` it covers*, and, when
`Γ(S, ⊤) ⟶ Γ(X, ⊤)` is flat with geometrically integral fibres, *which prime of the chart
algebra is the generic point of the fibre over a prime of `T`*.

The first is purely topological: the chart covers exactly the preimage of the image of `c` under
the projection to `S'`, so a point of `X ×_S S'` is in the chart as soon as its image in `S'` is
in `c`. The second is the ring-theoretic statement that for `B = A ⊗_R T` the extension `qB` of a
prime `q ⊆ T` is prime, contracts to `q`, and is contained in every prime of `B` over `q`: it is
the generic point of the fibre of `Spec B → Spec T` over `q`.

## Main results

* `isDomain_fiber_tensorProduct_of_geometricallyIntegral_fibres`: if every fibre of `A` over `R`
  is geometrically integral, then the fibre of `A ⊗_R T` over a prime of `T` is a domain.
* `Module.Flat.tensorProduct_right`: `A ⊗_R T` is flat over `T` when `A` is flat over `R`.
* `Ideal.isPrime_map_includeRight_of_geometricallyIntegral_fibres`: the extension of a prime `q`
  of `T` to `A ⊗_R T` is prime.
* `Ideal.comap_map_includeRight_of_geometricallyIntegral_fibres`: that extension contracts to `q`.
* `Ideal.map_includeRight_le_of_comap_eq`: it is contained in every prime of `A ⊗_R T` lying
  over `q`, so it is the generic point of the fibre.
* `Stacks.StrictTransform.range_pullback_map_id_right` and
  `Stacks.StrictTransform.range_affineBaseChangeChartMap`: the image of the chart of a base
  change is the preimage of the image of `c` under the projection `X ×_S S' ⟶ S'`.

## Implementation notes

The chart is `(affinePullbackSpecIso ...).inv ≫ pullback.map f (c ≫ b) f b (𝟙 X) c (𝟙 S)`. The
first factor is an isomorphism, so it does not change the image, and the second factor is, up to
`CategoryTheory.Limits.pullbackLeftPullbackSndIso`, the first projection of
`(X ×_S S') ×_{S'} Spec T`, whose image is computed by
`AlgebraicGeometry.IsOpenImmersion.range_pullbackFst`.

On the ring side `B = A ⊗_R T` carries the `T`-algebra structure
`Algebra.TensorProduct.rightAlgebra`, whose structure map is
`Algebra.TensorProduct.includeRight`; the two spellings of the extension `qB` agree definitionally
and the statements use `Algebra.TensorProduct.includeRight`, which is the spelling the conclusion
of `exists_fg_ideal_forall_blowup_chart_exists_away_basis_of_projective` is phrased with. `B` is
flat over `T`, being the base change of the flat module `A` along `R ⟶ T` read through
`Algebra.TensorProduct.comm`, and its fibre over `q` is
`κ(q) ⊗_{κ(p)} (κ(p) ⊗_R A)` for `p = q ∩ R`, a domain because `κ(p) ⊗_R A` is geometrically
integral over `κ(p)`. Primality of `qB` is then
`Ideal.isPrime_map_of_flat_of_isDomain_fiber'`, and the contraction is
`comap_map_eq_of_flat_isPrime`, flatness being what makes the extension of a prime contract to
itself once it is prime.

## References

* [Stacks Project, Tag 0810](https://stacks.math.columbia.edu/tag/0810)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
* [Stacks Project, Tag 05DX](https://stacks.math.columbia.edu/tag/05DX)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

/-! ### The generic point of a fibre of an affine base change -/

/-- **Geometrically integral fibres survive base change of the base.** If every fibre of the
`R`-algebra `A` is geometrically integral, then for every prime `q` of an `R`-algebra `T` the
fibre of `A ⊗_R T` over `q` is a domain.

That fibre is the base change along the field extension `κ(p) ⟶ κ(q)` of the fibre of `A` over
`p = q ∩ R`, which is a domain precisely because the latter is *geometrically* integral. -/
public theorem isDomain_fiber_tensorProduct_of_geometricallyIntegral_fibres
    {R A T : Type u} [CommRing R] [CommRing A] [CommRing T] [Algebra R A] [Algebra R T]
    (hfibre : ∀ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      Algebra.IsGeometricallyIntegral p.ResidueField (p.Fiber A))
    (q : Ideal T) [q.IsPrime] :
    letI : Algebra T (A ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
    IsDomain (q.Fiber (A ⊗[R] T)) := by
  let B := A ⊗[R] T
  let : Algebra T B := Algebra.TensorProduct.rightAlgebra
  let p : Ideal R := q.comap (algebraMap R T)
  let : p.IsPrime := Ideal.IsPrime.comap (algebraMap R T)
  let : Algebra p.ResidueField q.ResidueField :=
    (Ideal.ResidueField.mapₐ p q (Algebra.ofId R T) rfl).toRingHom.toAlgebra
  let : Module p.ResidueField q.ResidueField :=
    (inferInstance : Algebra p.ResidueField q.ResidueField).toModule
  let : IsScalarTower R p.ResidueField q.ResidueField :=
    .of_algebraMap_eq fun x ↦
      ((Ideal.ResidueField.mapₐ p q (Algebra.ofId R T) rfl).commutes x).symm
  let : Algebra.IsPushout R A T B := inferInstance
  let e : (q.ResidueField ⊗[p.ResidueField] p.Fiber A) ≃+* q.Fiber B :=
    (Algebra.TensorProduct.cancelBaseChange R p.ResidueField q.ResidueField
      q.ResidueField A).toRingEquiv.trans
      ((Algebra.TensorProduct.comm R q.ResidueField A).toRingEquiv.trans
        ((Algebra.IsPushout.cancelBaseChangeAlg R A T B q.ResidueField).symm.toRingEquiv.trans
          (Algebra.TensorProduct.comm T B q.ResidueField).toRingEquiv))
  have hright : IsDomain (p.Fiber A ⊗[p.ResidueField] q.ResidueField) :=
    (Algebra.isGeometricallyIntegral_iff_isDomain_tensorProduct
      p.ResidueField (p.Fiber A)).mp (hfibre p inferInstance) q.ResidueField
  have hleft : IsDomain (q.ResidueField ⊗[p.ResidueField] p.Fiber A) :=
    (Algebra.TensorProduct.comm p.ResidueField q.ResidueField
      (p.Fiber A)).toRingEquiv.injective.isDomain _
  exact e.symm.injective.isDomain _

/-- **The base change of a flat algebra is flat over the new base.** For a flat `R`-module `A`
and any `R`-algebra `T`, the ring `A ⊗_R T` is flat over `T`.

This is `Module.Flat.baseChange` read through `Algebra.TensorProduct.comm`, the base change being
written with the new base on the right. -/
public theorem Module.Flat.tensorProduct_right {R A T : Type u} [CommRing R] [CommRing A]
    [CommRing T] [Algebra R A] [Algebra R T] [Module.Flat R A] :
    letI : Algebra T (A ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
    Module.Flat T (A ⊗[R] T) := by
  let : Algebra T (A ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  let e : (T ⊗[R] A) ≃ₐ[T] (A ⊗[R] T) :=
    AlgEquiv.ofRingEquiv (f := (Algebra.TensorProduct.comm R T A).toRingEquiv) fun _ ↦ rfl
  have : Module.Flat T (T ⊗[R] A) := Module.Flat.baseChange R T A
  exact Module.Flat.of_linearEquiv e.symm.toLinearEquiv

/-- **The generic point of a fibre of an affine base change is a prime.** Let `R ⟶ A` be flat
with geometrically integral fibres, let `T` be an `R`-algebra and let `q` be a prime of `T`. Then
the extension `qB` of `q` to `B = A ⊗_R T` along `Algebra.TensorProduct.includeRight` is prime.

`B` is flat over `T` and its fibre over `q` is a domain, which is exactly the hypothesis of
`Ideal.isPrime_map_of_flat_of_isDomain_fiber'`. -/
public theorem Ideal.isPrime_map_includeRight_of_geometricallyIntegral_fibres
    {R A T : Type u} [CommRing R] [CommRing A] [CommRing T] [Algebra R A] [Algebra R T]
    [Module.Flat R A]
    (hfibre : ∀ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      Algebra.IsGeometricallyIntegral p.ResidueField (p.Fiber A))
    (q : Ideal T) [q.IsPrime] :
    (Ideal.map (Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T) q).IsPrime := by
  let : Algebra T (A ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  have : Module.Flat T (A ⊗[R] T) := Module.Flat.tensorProduct_right
  exact Ideal.isPrime_map_of_flat_of_isDomain_fiber' (S := A ⊗[R] T) q
    (isDomain_fiber_tensorProduct_of_geometricallyIntegral_fibres hfibre q)

/-- **The generic point of a fibre of an affine base change lies over that fibre.** Under the
hypotheses of `Ideal.isPrime_map_includeRight_of_geometricallyIntegral_fibres` the extension `qB`
contracts to `q` again.

`B` is flat over `T` and `qB` is prime, which is `comap_map_eq_of_flat_isPrime`. -/
public theorem Ideal.comap_map_includeRight_of_geometricallyIntegral_fibres
    {R A T : Type u} [CommRing R] [CommRing A] [CommRing T] [Algebra R A] [Algebra R T]
    [Module.Flat R A]
    (hfibre : ∀ (p : Ideal R) (hp : p.IsPrime),
      letI := hp
      Algebra.IsGeometricallyIntegral p.ResidueField (p.Fiber A))
    (q : Ideal T) [q.IsPrime] :
    letI : Algebra T (A ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
    Ideal.comap (algebraMap T (A ⊗[R] T))
        (Ideal.map (Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T) q) = q := by
  let : Algebra T (A ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  have hflat : Module.Flat T (A ⊗[R] T) := Module.Flat.tensorProduct_right
  exact comap_map_eq_of_flat_isPrime (algebraMap T (A ⊗[R] T))
    (RingHom.flat_algebraMap_iff.mpr hflat) q
    (Ideal.isPrime_map_includeRight_of_geometricallyIntegral_fibres hfibre q)

/-- **The generic point of a fibre is below every point of that fibre.** Any ideal `P` of
`B = A ⊗_R T` contracting to the prime `q` of `T` contains the extension `qB`.

No hypothesis on `A` is needed: `qB` is the smallest ideal of `B` contracting into `q`. -/
public theorem Ideal.map_includeRight_le_of_comap_eq {R A T : Type u} [CommRing R] [CommRing A]
    [CommRing T] [Algebra R A] [Algebra R T] (q : Ideal T) (P : Ideal (A ⊗[R] T)) :
    letI : Algebra T (A ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
    Ideal.comap (algebraMap T (A ⊗[R] T)) P = q →
      Ideal.map (Algebra.TensorProduct.includeRight : T →ₐ[R] A ⊗[R] T) q ≤ P := by
  let : Algebra T (A ⊗[R] T) := Algebra.TensorProduct.rightAlgebra
  intro hP
  exact Ideal.map_le_iff_le_comap.mpr (hP ▸ le_rfl)

namespace Stacks.StrictTransform

/-! ### The image of an affine chart of a base change -/

/-- Precomposing with an isomorphism does not change the image of a morphism of schemes. -/
private theorem range_base_comp_of_isIso {Y Z W : Scheme.{u}} (e : Y ⟶ Z) [IsIso e]
    (m : Z ⟶ W) : Set.range (e ≫ m).base = Set.range m.base := by
  rw [Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr e.surjective, Set.image_univ]

/-- **The image of the comparison map of two base changes along an open immersion.** For
`f : X ⟶ S`, `b : S' ⟶ S` and an open immersion `c : W ⟶ S'`, the canonical map
`X ×_S W ⟶ X ×_S S'` has image the preimage of the image of `c` under the projection to `S'`.

Up to `CategoryTheory.Limits.pullbackLeftPullbackSndIso` the map is the first projection of
`(X ×_S S') ×_{S'} W`, whose image is `AlgebraicGeometry.IsOpenImmersion.range_pullbackFst`. -/
public theorem range_pullback_map_id_right {X S S' W : Scheme.{u}} (f : X ⟶ S) (b : S' ⟶ S)
    (c : W ⟶ S') [IsOpenImmersion c] (h₁ : f ≫ 𝟙 S = 𝟙 X ≫ f)
    (h₂ : (c ≫ b) ≫ 𝟙 S = c ≫ b) :
    Set.range (pullback.map f (c ≫ b) f b (𝟙 X) c (𝟙 S) h₁ h₂).base =
      (pullback.snd f b).base ⁻¹' Set.range c.base := by
  have key : pullback.map f (c ≫ b) f b (𝟙 X) c (𝟙 S) h₁ h₂ =
      (pullbackLeftPullbackSndIso f b c).inv ≫ pullback.fst (pullback.snd f b) c := by
    refine pullback.hom_ext ?_ ?_
    · simp only [pullback.map, pullback.lift_fst, Category.comp_id, Category.assoc,
        pullbackLeftPullbackSndIso_inv_fst]
    · simp only [pullback.map, pullback.lift_snd, Category.assoc,
        pullbackLeftPullbackSndIso_inv_fst_snd]
  rw [key, range_base_comp_of_isIso]
  simpa using IsOpenImmersion.range_pullbackFst c (pullback.snd f b)

/-- **The image of an affine chart of a base change.** The chart
`Stacks.StrictTransform.affineBaseChangeChartMap` of `X ×_S S'` built from an open immersion
`c : Spec T ⟶ S'` covers exactly the points whose image under the projection to `S'` lies in the
image of `c`.

In particular the charts built from a family of charts covering `S'` cover `X ×_S S'`, which is
what makes the universally quantified conclusion of [Stacks, Tag 0810] say something at every
point of the base change. -/
public theorem range_affineBaseChangeChartMap {X S S' : Scheme.{u}} [IsAffine X] [IsAffine S]
    (f : X ⟶ S) (b : S' ⟶ S) (T : Type u) [CommRing T] [Algebra Γ(S, ⊤) T]
    (c : Spec (CommRingCat.of T) ⟶ S') [IsOpenImmersion c]
    (hc : (c ≫ b) ≫ S.isoSpec.hom = Spec.map (CommRingCat.ofHom (algebraMap Γ(S, ⊤) T))) :
    Set.range (affineBaseChangeChartMap f b T c hc).base =
      (pullback.snd f b).base ⁻¹' Set.range c.base := by
  dsimp only [affineBaseChangeChartMap]
  rw [range_base_comp_of_isIso, range_pullback_map_id_right]

end Stacks.StrictTransform

end
