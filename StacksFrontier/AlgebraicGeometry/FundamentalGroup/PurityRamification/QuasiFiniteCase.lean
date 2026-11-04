module

public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.AnyDimension
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.EtaleLocus
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.ExcellentBase
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.Generizations
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.SpecializationLift
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The quasi-finite case of the purity lemma at a normal surface point

[Stacks, Tag 0EA3] says: let `A` be an excellent regular local ring, `f : X ⟶ Spec A` of finite
type and `x ∈ X` with `𝒪_{X, x}` normal of dimension two; if `f` is étale outside the closure of
`x`, then `f` is étale at `x`.  This file proves that statement when `f` is in addition
quasi-finite at `x`.  In that case it is purity of the branch locus, [Stacks, Tag 0BMB]
(`AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne`): the
one-dimensional generizations of `x` lie outside the closure of `x`, so `f` is étale, hence
unramified, there, and the dimension hypothesis of Tag 0BMB, `dim 𝒪_{X, x} = dim 𝒪_{Y, f x}`, is
the dimension formula over the universally catenary local ring `𝒪_{Y, f x}`.

## Main results

* `AlgebraicGeometry.stalkMap_injective_of_etaleAt_generization` — over a domain, the stalk map
  `𝒪_{Spec A, f x} ⟶ 𝒪_{X, x}` is injective once `f` is étale at a generization of `x`.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_of_quasiFiniteAt_of_injective` — the dimension formula
  at a point of quasi-finiteness over an excellent base, without assuming that the image of the
  point is the closed point.
* `AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_etaleAt_outside_closure` — the conclusion of
  [Stacks, Tag 0EA3] under its hypotheses, when `f` is quasi-finite at `x`.
* `AlgebraicGeometry.etaleAt_iff_finite_residueField_of_etaleAt_outside_closure` — under the
  hypotheses of [Stacks, Tag 0EA3], `f` is étale at `x` if and only if `κ(x)` is a finite
  extension of `κ(f x)`.  So the content of that tag beyond purity of the branch locus is
  exactly the finiteness of the residue field extension at `x`.

## What remains of Tag 0EA3

Under the hypotheses of the tag `x` is a generic point of its fibre (every proper generization
of `x` is a point of étaleness, hence isolated in its fibre), so `f` is quasi-finite at `x` as
soon as `κ(x)` is finite over `κ(f x)`.  The case left open here is therefore the one in which
`κ(x)` has positive transcendence degree `t` over `κ(f x)`; by the dimension formula the image
of `x` then has height `2 + t`, so `f` cannot be flat at `x`, and the tag asserts that this case
does not occur.  The source excludes it through a minimal resolution of `𝒪_{X, x}`
([Stacks, Tag 0BGP]) and [Stacks, Tag 0EA2]; neither is available in this library.

## References

* [Stacks Project, Tag 0EA3](https://stacks.math.columbia.edu/tag/0EA3)
* [Stacks Project, Tag 0BMB](https://stacks.math.columbia.edu/tag/0BMB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Points of `Spec A` have prime ideals. -/
private instance isPrime_asIdeal_spec {A : Type u} [CommRing A] (p : Spec (.of A)) :
    p.asIdeal.IsPrime := p.isPrime

/-- Over a domain `A`, the stalk map `𝒪_{Spec A, f x} ⟶ 𝒪_{X, x}` is injective as soon as `f` is
étale at some generization of `x`.  The structure map `A →+* 𝒪_{X, x}` is then injective
(`AlgebraicGeometry.baseToStalk_injective_of_etaleAt_generization`), and every element of the
source of the stalk map is a fraction `a / s` with `s` mapping to a unit. -/
theorem stalkMap_injective_of_etaleAt_generization {A : Type u} [CommRing A] [IsDomain A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {x z : X} (h : z ⤳ x) (hz : EtaleAt f z) :
    Function.Injective (f.stalkMap x).hom := by
  have hinj := baseToStalk_injective_of_etaleAt_generization f h hz
  let _ : Algebra A ((Spec (.of A)).presheaf.stalk (f x)) :=
    (StructureSheaf.toStalk A (f x)).hom.toAlgebra
  have _ : IsLocalization.AtPrime ((Spec (.of A)).presheaf.stalk (f x)) (f x).asIdeal :=
    StructureSheaf.IsLocalization.to_stalk A (f x)
  refine (injective_iff_map_eq_zero _).mpr fun b hb => ?_
  obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (f x).asIdeal.primeCompl b
  have ha : toStalkStalkMap f x a = 0 := by
    have h1 : (f.stalkMap x).hom (algebraMap A _ a) =
        (f.stalkMap x).hom (IsLocalization.mk' _ a s) *
          (f.stalkMap x).hom (algebraMap A _ (s : A)) := by
      rw [← map_mul, IsLocalization.mk'_spec]
    rwa [hb, zero_mul] at h1
  have ha0 : a = 0 := hinj (by rw [ha, map_zero])
  simp [ha0]

/-- **The dimension formula at a point of quasi-finiteness over an excellent base.**  Let `A` be
an excellent ring, `f : X ⟶ Spec A` locally of finite type and `x` a point at which `f` is
quasi-finite, with `𝒪_{X, x}` a domain, `𝒪_{Spec A, f x}` a domain and the stalk map injective.
Then `dim 𝒪_{X, x} = dim 𝒪_{Spec A, f x}`.

The local ring `𝒪_{Spec A, f x}` is a localization of `A`, hence excellent and in particular
universally catenary, and the dimension formula for the quasi-finite local homomorphism
`𝒪_{Spec A, f x} ⟶ 𝒪_{X, x}` is `AlgebraicGeometry.ringKrullDim_eq_of_local_quasiFinite`. -/
@[ega "IV 13.2.5" "(iv), special case"]
theorem ringKrullDim_stalk_eq_of_quasiFiniteAt_of_injective {A : Type u} [CommRing A]
    (hA : IsExcellent A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] (x : X)
    [IsDomain (X.presheaf.stalk x)] [IsDomain ((Spec (.of A)).presheaf.stalk (f x))]
    (hi : Function.Injective (f.stalkMap x).hom) (hqf : f.QuasiFiniteAt x) :
    ringKrullDim (X.presheaf.stalk x) =
      ringKrullDim ((Spec (.of A)).presheaf.stalk (f x)) := by
  let R : Type u := (Spec (.of A)).presheaf.stalk (f x)
  let S : Type u := X.presheaf.stalk x
  let _ : Algebra A R := (StructureSheaf.toStalk A (f x)).hom.toAlgebra
  have _ : IsLocalization.AtPrime R (f x).asIdeal := StructureSheaf.IsLocalization.to_stalk A (f x)
  have _ : Algebra.EssFiniteType A R := .of_isLocalization R (f x).asIdeal.primeCompl
  have hR := (isQuasiExcellent_and_isExcellent_of_essFiniteType (R := A) (S := R)).2 hA
  have _ : IsNoetherianRing R := hR.1.1
  let _ : Algebra R S := (f.stalkMap x).hom.toAlgebra
  have _ : IsLocalHom (algebraMap R S) := f.prop x
  have _ : FaithfulSMul R S := (faithfulSMul_iff_algebraMap_injective R S).mpr hi
  have _ : Algebra.EssFiniteType R S := LocallyOfFiniteType.stalkMap f x
  have _ : Algebra.QuasiFinite R S := hqf
  exact ringKrullDim_eq_of_local_quasiFinite
    (Ring.isUniversallyCatenary_iff_isUniversallyCatenary.mp hR.2)

/-- A generization of `x` other than `x` lies outside the closure of `x`: a point specializing
to `x` and lying in the closure of `x` is equal to `x`. -/
theorem notMem_closure_singleton_of_specializes {X : Scheme.{u}} {x z : X} (h : z ⤳ x)
    (hne : z ≠ x) : z ∉ closure ({x} : Set X) := fun hz =>
  hne (h.antisymm (specializes_iff_mem_closure.mpr hz)).eq

/-- **[Stacks, Tag 0EA3] when `f` is quasi-finite at `x`.**  Let `A` be an excellent regular
local ring, `f : X ⟶ Spec A` locally of finite type and `x ∈ X` with `𝒪_{X, x}` normal of
dimension two.  If `f` is étale outside the closure of `x` and quasi-finite at `x`, then `f` is
étale at `x`.

This is purity of the branch locus, [Stacks, Tag 0BMB]: the one-dimensional generizations of `x`
lie outside the closure of `x`, so `f` is étale, hence unramified, there; such a generization
makes the stalk map at `x` injective, and then the dimension formula over the excellent base
gives `dim 𝒪_{X, x} = dim 𝒪_{Spec A, f x}`. -/
theorem etaleAt_of_quasiFiniteAt_of_etaleAt_outside_closure {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (hA : IsExcellent A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] (x : X) (hX : IsNormalRing (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (het : ∀ z : X, z ∉ closure ({x} : Set X) → EtaleAt f z) (hqf : quasiFiniteAt f x) :
    EtaleAt f x := by
  have _ : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have _ : IsDomain A := IsRegularLocalRing.isDomain A
  have _ : IsDomain (X.presheaf.stalk x) := hX.of_isLocalRing.1
  have hY : IsRegularLocalRing ((Spec (.of A)).presheaf.stalk (f x)) :=
    isRegularLocalRing_stalk_spec A (f x)
  have _ : IsDomain ((Spec (.of A)).presheaf.stalk (f x)) := IsRegularLocalRing.isDomain _
  have hone : 1 ≤ ringKrullDim (X.presheaf.stalk x) := by rw [hdim]; norm_num
  have hcodim : ∀ z : X, z ⤳ x → ringKrullDim (X.presheaf.stalk z) = 1 → EtaleAt f z := by
    intro z hz hdz
    refine het z (notMem_closure_singleton_of_specializes hz fun hzx => ?_)
    rw [hzx, hdim] at hdz
    norm_num at hdz
  obtain ⟨z, hz, hdz⟩ := exists_specializes_ringKrullDim_stalk_eq_one x hone
  have hi := stalkMap_injective_of_etaleAt_generization f hz (hcodim z hz hdz)
  exact etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne f x hX hY hqf
    (ringKrullDim_stalk_eq_of_quasiFiniteAt_of_injective hA f x hi hqf.2) hone
    (fun w hw hdw => Stacks.Discriminant.unramifiedAt_of_etaleAt f w (hcodim w hw hdw))

/-- **[Stacks, Tag 0EA3] is equivalent to the finiteness of the residue field extension.**
Under the hypotheses of that tag, `f` is étale at `x` if and only if `κ(x)` is a finite extension
of `κ(f x)`.  One direction holds for any point of étaleness, which is a point of
quasi-finiteness.  For the other, every proper generization of `x` lies outside the closure of
`x`, so it is a point of étaleness; hence `x` is a generic point of its fibre, and a finite
residue field extension makes it a closed point of the fibre as well, so `f` is quasi-finite at
`x` (`AlgebraicGeometry.quasiFiniteAt_of_finite_residueField_of_etaleAt_generizations`) and
`AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_etaleAt_outside_closure` applies. -/
theorem etaleAt_iff_finite_residueField_of_etaleAt_outside_closure {A : Type u} [CommRing A]
    [IsRegularLocalRing A] (hA : IsExcellent A) {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    [LocallyOfFiniteType f] (x : X) (hX : IsNormalRing (X.presheaf.stalk x))
    (hdim : ringKrullDim (X.presheaf.stalk x) = 2)
    (het : ∀ z : X, z ∉ closure ({x} : Set X) → EtaleAt f z) :
    EtaleAt f x ↔ letI := (f.residueFieldMap x).hom.toAlgebra
      Module.Finite ((Spec (.of A)).residueField (f x)) (X.residueField x) :=
  ⟨fun hx => residueField_finite_of_quasiFiniteAt f x (quasiFiniteAt_of_etaleAt f x hx).2,
    fun hfin => etaleAt_of_quasiFiniteAt_of_etaleAt_outside_closure hA f x hX hdim het
      (quasiFiniteAt_of_finite_residueField_of_etaleAt_generizations f x hfin
        fun z hz hne => het z (notMem_closure_singleton_of_specializes hz hne))⟩

end AlgebraicGeometry

end
