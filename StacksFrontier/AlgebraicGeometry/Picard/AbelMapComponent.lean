module

public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapFibreEuler

/-!
# The morphism `γ_d` from the Hilbert scheme of a curve to a degree component of its Picard scheme

Let `X` be a geometrically irreducible smooth proper curve of genus `g` over a field `k`, let `H`
represent the degree-`d` Hilbert functor of `X`, and let `P ⊂ Pic_{X/k}` be a subfunctor of the
Picard functor which contains the class of an invertible module `ℒ` on `X_T` exactly when every
fibre of `ℒ` has Euler characteristic `d + 1 - g` — the degree-`d` subfunctor `Pic^d_{X/k}` of
[Stacks, Tag 0BA0]. If `P` is represented by an object `Pic^d`, the invertible sheaf `𝒪(D_univ)` of
the universal family on `X ×_k H` defines a morphism

`γ_d : H ⟶ Pic^d`

by the Yoneda lemma: its class lies in `P(H)` because every fibre of `𝒪(D_univ)` has Euler
characteristic `d + 1 - g` (`Stacks.AbelMap.fibreEuler_divisorSheaf`). This is clause (4) of
[Stacks, Tag 0BA0].

## Main definitions

* `Stacks.AbelMap.HasFibreEuler`: every fibre of an invertible module on `X_T` has a given Euler
  characteristic.
* `Stacks.AbelMap.IsDegreeComponent`: a subfunctor of the Picard functor is cut out by the
  fibrewise Euler characteristic `d + 1 - g` on the classes of invertible modules.
* `Stacks.AbelMap.abelMap`: the morphism `γ_d`.

## Main results

* `Stacks.AbelMap.homEquiv_comp_abelMap`: the defining property of `γ_d`, namely that the point of
  `Pic^d` it assigns to a `T`-point of `H`, that is to a degree-`d` family `D` on `X_T`, is the
  class of `𝒪(D)`.
* `Stacks.AbelMap.abelMap_unique`: `γ_d` is the only morphism with that property.

## Implementation notes

The degree component is an argument: any subfunctor `P` satisfying `IsDegreeComponent` together
with a representing object. Nothing is assumed of `P` beyond what the tag says `Pic^d_{X/k}` is.

## References

* [Stacks Project, Tag 0BA0](https://stacks.math.columbia.edu/tag/0BA0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.Divisors (divisorSheaf IsEffectiveCartierDivisor)
open Stacks.FibreCohomology (fibreCohomology)
open Stacks.PicardFunctor (picardFunctor toPicardFunctor baseChange baseChangeMap picardAt
  picardMap testMap)

universe u

namespace Stacks.AbelMap

variable {k : Type u} [Field k] (B : BigFppfSite.{u}) {X : Scheme.{u}} (hX : B.Contains X)
  (hk : B.Contains (Spec (.of k))) (f : B.obj hX ⟶ B.obj hk)

/-- Every fibre `X_t` of the base change `X_T ⟶ T` carries the restriction of `ℒ` with Euler
characteristic `n`: `dim_{κ(t)} H⁰(X_t, ℒ_t) - dim_{κ(t)} H¹(X_t, ℒ_t) = n` for all `t ∈ T`. -/
def HasFibreEuler (T : BigFppfOver B (Spec (.of k)) hk) (L : (baseChange B hX hk f T).Modules)
    (n : ℤ) : Prop :=
  ∀ t : B.inclusion.obj T.left,
    (Module.finrank ((B.inclusion.obj T.left).residueField t)
        (fibreCohomology (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)) L t 0) : ℤ) -
      Module.finrank ((B.inclusion.obj T.left).residueField t)
        (fibreCohomology (pullback.snd (B.inclusion.map f) (B.inclusion.map T.hom)) L t 1) = n

/-- A subfunctor of the Picard functor is *the degree-`d` component* when it contains the class
of an invertible module `ℒ` on a base change `X_T` exactly when every fibre of `ℒ` has Euler
characteristic `d + 1 - g`, where `g` is the genus of `X`. This is how [Stacks, Tag 0BA0] describes
`Pic^d_{X/k}`, by way of [Stacks, Tag 0B9T]. -/
def IsDegreeComponent (d : ℤ) (P : Subfunctor (picardFunctor B hX hk f)) : Prop :=
  ∀ (T : BigFppfOver B (Spec (.of k)) hk) (L : (baseChange B hX hk f T).Modules)
    (hL : Stacks.SheafOfModules.IsInvertible (baseChange B hX hk f T).presheaf
      (Stacks.RingedSpace.structureIsSheaf (baseChange B hX hk f T).toRingedSpace) L),
    (toPicardFunctor B hX hk f).app (op T)
        (Stacks.SheafOfModules.picardClass _ _ L hL) ∈ P.obj (op T) ↔
      HasFibreEuler B hX hk f T L (d + 1 - genus (B.inclusion.map f))

variable [IsCurve k (B.inclusion.map f)] [GeometricallyIrreducible (B.inclusion.map f)]
  [Smooth (B.inclusion.map f)] [IsProper (B.inclusion.map f)]

/-- A smooth curve is smooth of relative dimension one. -/
instance smoothOfRelativeDimension_one :
    SmoothOfRelativeDimension 1 (B.inclusion.map f) :=
  AlgebraicGeometry.smoothOfRelativeDimension_one_of_isCurve k _

/-- **Every fibre of the sheaf of a degree-`d` family has Euler characteristic `d + 1 - g`.** -/
theorem hasFibreEuler_hilbertFamily {d : ℕ} (T : BigFppfOver B (Spec (.of k)) hk)
    (D : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map T.hom)) d) :
    HasFibreEuler B hX hk f T (divisorSheaf D.ideal) (d + 1 - genus (B.inclusion.map f)) :=
  fun t => fibreEuler_divisorSheaf (B.inclusion.map f) D t

variable {d : ℕ} {P : Subfunctor (picardFunctor B hX hk f)}
  (hP : IsDegreeComponent B hX hk f d P)

include hP in
/-- **The class of `𝒪(D)` of a degree-`d` family lies in the degree-`d` component.** -/
theorem toPicardFunctor_picardClass_mem (T : BigFppfOver B (Spec (.of k)) hk)
    (D : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map T.hom)) d) :
    (toPicardFunctor B hX hk f).app (op T) D.picardClass ∈ P.obj (op T) :=
  have := D.isEffectiveCartierDivisor_ideal
  (hP T (divisorSheaf D.ideal) (Stacks.Divisors.isInvertible_invertibleSheaf_picard D.ideal)).2
    (by exact_mod_cast hasFibreEuler_hilbertFamily B hX hk f T D)

/-- The class of `𝒪(D)` of a degree-`d` family, as a point of the degree-`d` component. -/
def familyPoint (T : BigFppfOver B (Spec (.of k)) hk)
    (D : Stacks.Hilbert.HilbertFamily (Over.mk (B.inclusion.map f))
      (Over.mk (B.inclusion.map T.hom)) d) : P.toFunctor.obj (op T) :=
  ⟨_, toPicardFunctor_picardClass_mem B hX hk f hP T D⟩

variable (H : BigFppfOver B (Spec (.of k)) hk)
  (hH : Stacks.Hilbert.RepresentsHilbertFunctorOfRank (Over.mk (B.inclusion.map f))
    (Over.mk (B.inclusion.map H.hom)) d)
  {Pd : BigFppfOver B (Spec (.of k)) hk} (R : P.toFunctor.RepresentableBy Pd)

/-- **Stacks Project, Tag 0BA0, clause (4): the morphism `γ_d : Hilb^d_{X/k} ⟶ Pic^d_{X/k}`.**
The morphism that the Yoneda lemma assigns to the class of the invertible sheaf `𝒪(D_univ)` of
the universal degree-`d` family on `X ×_k H`, which lies in the degree-`d` component. -/
def abelMap : H ⟶ Pd :=
  R.homEquiv.symm (familyPoint B hX hk f hP H (hH.family (𝟙 _)))

omit [GeometricallyIrreducible (B.inclusion.map f)] [IsProper (B.inclusion.map f)] in
/-- Restricting the class of the universal family along a `T`-point of `H` gives the class of
the family that point classifies. -/
theorem picardMap_universal {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ H) :
    picardMap B hX hk f t (hH.family (𝟙 _)).picardClass =
      (hH.family (testMap B hk t)).picardClass := by
  refine Stacks.Hilbert.HilbertFamily.schemePullbackClass_picardClass
    (hH.family (𝟙 (Over.mk (B.inclusion.map H.hom)))) (hH.family (testMap B hk t))
    (baseChangeMap B hX hk f t) ?_
  have h := hH.naturality (testMap B hk t) (𝟙 (Over.mk (B.inclusion.map H.hom)))
  rwa [Category.comp_id] at h

/-- **Stacks Project, Tag 0BA0, clause (4): the defining property of `γ_d`.** The point of
`Pic^d_{X/k}` that `γ_d` assigns to a `T`-point of `Hilb^d_{X/k}`, that is to a degree-`d` family
`D` on `X ×_k T`, is the class of the invertible sheaf `𝒪(D)`. -/
theorem homEquiv_comp_abelMap {T : BigFppfOver B (Spec (.of k)) hk} (t : T ⟶ H) :
    R.homEquiv (t ≫ abelMap B hX hk f hP H hH R) =
      familyPoint B hX hk f hP T (hH.family (testMap B hk t)) := by
  rw [R.homEquiv_comp, abelMap, Equiv.apply_symm_apply]
  apply Subtype.ext
  show (picardFunctor B hX hk f).map t.op
      ((toPicardFunctor B hX hk f).app (op H) (hH.family (𝟙 _)).picardClass) =
    (toPicardFunctor B hX hk f).app (op T) (hH.family (testMap B hk t)).picardClass
  rw [← picardMap_universal B hX hk f H hH t]
  exact (Stacks.PicardFunctor.toPicardFunctor_app_naturality B hX hk f t _).symm

/-- **`γ_d` is canonical**: it is the only morphism `H ⟶ Pic^d` sending every family to the class
of its sheaf. -/
theorem abelMap_unique (γ : H ⟶ Pd)
    (hγ : R.homEquiv γ = familyPoint B hX hk f hP H (hH.family (𝟙 _))) :
    γ = abelMap B hX hk f hP H hH R :=
  R.homEquiv.injective (by rw [hγ, abelMap, Equiv.apply_symm_apply])

end Stacks.AbelMap

end
