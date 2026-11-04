module

public import StacksFrontier.Deformation.Artin.Obstruction.Theory

/-!
# Detecting lifts on a family of deformation situations

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, carrying an
obstruction theory in the sense of Stacks 07YG. Let `x` be an object of `𝒳` over `Spec A` and
let `(x, A' → A)` be a deformation situation with kernel `I`. Suppose given a family of
deformation situations `(x, A'_i → A)` with kernels `I_i`, and for each `i` a morphism of
deformation situations `(x, A' → A) → (x, A'_i → A)` which is the identity on `(x, A)`, so that
it induces an `A`-linear map `I → I_i`. Condition (ii) of Stacks 07YG says that the obstruction
element of `(x, A' → A)` maps to the obstruction element of `(x, A'_i → A)` under the induced
map `𝒪_x(I) → 𝒪_x(I_i)`. Hence if every `x` lifts to `Spec A'_i` and the map
`𝒪_x(I) → ∏_i 𝒪_x(I_i)` is injective, then the obstruction element of `(x, A' → A)` vanishes
and `x` lifts to `Spec A'`.

This is the first step of the proof of Stacks 0CYF, where `A'` is the ring of sequences
`(r_1, r_2, …) ∈ ∏ R_n` with a common image in `A = R_1`, the `A'_i` are the `R_n`, and the
injectivity is assumption (5)(b) of that lemma.

## Main results

* `Deformation.Artin.ObstructionTheory.map_obs_eq` — for a morphism of deformation situations
  over the identity of `(x, A)`, the map of obstruction modules induced by the map of kernels
  carries obstruction element to obstruction element.
* `Deformation.Artin.ObstructionTheory.hasLift_of_injective` — if the obstruction elements are
  detected on a family of deformation situations each of which admits a lift, then the given
  deformation situation admits a lift.

## References

* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} {hp : p.IsFiberedInGroupoids}

/-- The element of `A'` underlying an element of the kernel determines that element. -/
public theorem DeformationSituation.kernelVal_injective {a : SiteAlgebra B S hS}
    (t : DeformationSituation B S hS a) : Function.Injective t.kernelVal :=
  fun _ _ h => Subtype.ext h

namespace ObstructionTheory

/-- Condition (ii) of Stacks 07YG for a morphism of deformation situations which is the identity
on `(x, A)`, phrased with the induced `A`-linear map `f : I → I'` of kernels: the map
`𝒪_x(f)` of obstruction modules carries the obstruction element of the source to that of the
target. -/
public theorem map_obs_eq (O : ObstructionTheory B S hS p hp) (P : AffineObject B S hS p)
    {s t : DeformationSituation B S hS P.alg} (m : DeformationSituation.Hom B S hS p s t)
    (hbase : m.base = AffineObject.Hom.id P) (f : s.kernelObj ⟶ t.kernelObj)
    (hf : ∀ z, t.kernelVal (f z) = m.top.ringMap (s.kernelVal z)) :
    ((O.obstruction P).functor.map f) (O.obs P s) = O.obs P t := by
  obtain ⟨base, top, comm⟩ := m
  change base = AffineObject.Hom.id P at hbase
  subst hbase
  obtain ⟨φ, hφ, hmap⟩ := O.obs_naturality P P s t ⟨AffineObject.Hom.id P, top, comm⟩
  obtain ⟨ψ, hψ, hloc⟩ := O.map_local P s.kernelObj t.kernelObj f
  have hφψ : φ = ψ := by
    refine LinearMap.ext fun z => t.kernelVal_injective ?_
    rw [hφ z, hψ z]
    exact (hf z).symm
  rw [← hloc, ← hφψ]
  exact hmap

/-- **Lifts detected on a family of deformation situations.** Let `(x, A' → A)` be a deformation
situation with kernel `I`, and let `(x, A' → A) → (x, A'_i → A)` be morphisms of deformation
situations which are the identity on `(x, A)`, with induced maps of kernels `f_i : I → I_i`. If
`x` lifts to every `Spec A'_i` and `𝒪_x(I) → ∏_i 𝒪_x(I_i)` is injective, then `x` lifts to
`Spec A'`. -/
public theorem hasLift_of_injective (O : ObstructionTheory B S hS p hp)
    (P : AffineObject B S hS p) (t : DeformationSituation B S hS P.alg)
    {ι : Type*} (s : ι → DeformationSituation B S hS P.alg)
    (m : ∀ i, DeformationSituation.Hom B S hS p t (s i))
    (hbase : ∀ i, (m i).base = AffineObject.Hom.id P)
    (f : ∀ i, t.kernelObj ⟶ (s i).kernelObj)
    (hf : ∀ i z, (s i).kernelVal (f i z) = (m i).top.ringMap (t.kernelVal z))
    (hinj : Function.Injective fun (o : (O.obstruction P).functor.obj t.kernelObj) (i : ι) =>
      ((O.obstruction P).functor.map (f i)) o)
    (hlift : ∀ i, AffineObject.HasLift hp P (s i)) :
    AffineObject.HasLift hp P t := by
  rw [O.hasLift_iff_obs_eq_zero]
  refine hinj (funext fun i => ?_)
  change ((O.obstruction P).functor.map (f i)) (O.obs P t) =
    ((O.obstruction P).functor.map (f i)) 0
  rw [O.map_obs_eq P (m i) (hbase i) (f i) (hf i), map_zero]
  exact (O.hasLift_iff_obs_eq_zero P (s i)).mp (hlift i)

end ObstructionTheory

end Deformation.Artin
