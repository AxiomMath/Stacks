module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FibreStalkBridges
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization

/-!
# Generic points of a closed fibre, and the local algebra over the base ring

Let `f : X ⟶ S` be a morphism of schemes, `I` an ideal sheaf on `X` and `s : S`, and let `z` be
a generic point of an irreducible component of the fibre `V(I)_s` of `V(I) ⟶ S` over `s`. This
file turns the *geometric* hypotheses carried by that situation into the *algebraic* hypotheses
a statement about the local ring `𝒪_{X,x}` at the image `x` of `z` in `X` can consume.

Three transfers are provided, each one a hypothesis of
`Stacks.ValuationRingFibre.maximalIdeal_mem_associatedPrimes_quotient` — the valuation-ring core
of Stacks 0GSI — expressed on the geometric side:

* the **radical hypothesis** `√(q + 𝔪_s·𝒪_{X,x}) = 𝔪_x`, from `z` being a generic point;
* **essential finiteness** of `𝒪_{X,x}` over a local base ring `A`, from `f` being locally of
  finite type;
* **flatness** of a stalk over `A`, from flatness over `S` at the point.

The fourth hypothesis of that theorem, `Module.Finite 𝒪_{X,x} F_x` for a finite-type module `F`,
needs no transfer: it is `SheafOfModules.finite_stalk X.sheaf F x`
(`StacksFrontier/AlgebraicGeometry/Morphisms/Support/FiniteType.lean`).

## Main definitions

* `Stacks.BaseStalk.baseStalkIso`: the comparison `A ≅ 𝒪_{Spec A, f x}` at a point `x` lying over
  the closed point of the spectrum of a local ring `A`.
* `Stacks.BaseStalk.baseStalkHom`: the induced ring map `A ⟶ 𝒪_{X,x}`.
* `Stacks.BaseStalk.baseStalkModule`: the `A`-module structure on the stalk of an `𝒪_X`-module at
  such a point.

## Main results

* `Stacks.ClosedFibreGenericPoint.setOf_specializes_eq_singleton`: a generic point of an
  irreducible component of a `T0` space has no generalization but itself.
* `Stacks.ClosedFibreGenericPoint.isPrime_eq_maximalIdeal_of_mem_genericPoints`: at a generic
  point `x` of an irreducible component of a scheme `Z`, the local ring `𝒪_{Z,x}` has exactly one
  prime ideal.
* `Stacks.ClosedFibreGenericPoint.radical_ker_eq_maximalIdeal`: consequently, for any local
  homomorphism `B ⟶ 𝒪_{Z,x}` from a local ring, the kernel has radical `𝔪_B`.
* `Stacks.ClosedFibreGenericPoint.ker_stalkMap_fiberι_comp` and
  `ker_stalkMap_fiberι_comp_subschemeι`: the kernel of the stalk map of the composite
  `(ι ≫ f).fiber s ⟶ Y ⟶ X` is `ker(𝒪_{X,x} ⟶ 𝒪_{Y,·}) + 𝔪_s·𝒪_{X,x}`, which for `ι` the
  inclusion of the subscheme cut out by `I` reads `I_x + 𝔪_s·𝒪_{X,x}`.
* `Stacks.ClosedFibreGenericPoint.radical_stalkIdeal_sup_stalkFibreIdeal`: **the radical
  hypothesis**, `√(I_x + 𝔪_s·𝒪_{X,x}) = 𝔪_x` whenever `z` is a generic point of an irreducible
  component of `V(I)_s`.
* `Stacks.ClosedFibreGenericPoint.radical_sup_stalkFibreIdeal_of_stalkIdeal_le` and
  `radical_under_sup_stalkFibreIdeal`: the same with `I_x` replaced by any ideal `q` between `I_x`
  and `𝔪_x`, and then by the canonical prime of a generic point of `V(I)`.
* `Stacks.ClosedFibreGenericPoint.stalkIdeal_le_comap_maximalIdeal`: `I_x` is carried by the
  comparison `𝒪_{X,x} ⟶ 𝒪_{X,y}` into `𝔪_y`, for `y ⤳ x` a point of the support of `I`. This is
  what makes the previous item applicable to that prime.
* `Stacks.BaseStalk.essFiniteType_baseStalk`: for `f : X ⟶ Spec A` locally of finite type and `x`
  over the closed point, `𝒪_{X,x}` is essentially of finite type over `A`.
* `Stacks.BaseStalk.flat_of_isFlatOverAt`: an `𝒪_X`-module flat over `Spec A` at such an `x`
  (`AlgebraicGeometry.IsFlatOverAt`, Tag 08KT (1)) has `A`-flat stalk there.
* `Stacks.BaseStalk.map_maximalIdeal_baseStalkHom`: the ideal `𝔪_A·𝒪_{X,x}` of the algebra core
  and the ideal `AlgebraicGeometry.Scheme.Hom.stalkFibreIdeal` of the geometry agree.

## Implementation notes

**Why the unique-prime route rather than minimal primes.** `z ∈ genericPoints Z` says that
`closure {z}` is a maximal irreducible closed subset. Since `Set.range (Z.fromSpecStalk z)` is the
set of generalizations of `z` (Mathlib's `Scheme.range_fromSpecStalk`, Tag 01J7) and
`Z.fromSpecStalk z` is a preimmersion, hence injective on points, genericity makes `Spec 𝒪_{Z,z}`
a one-point space; the maximal ideal is then the only prime and `√⊥ = 𝔪`. Phrasing the conclusion
as `(RingHom.ker π).radical = 𝔪_B` for a local homomorphism `π` avoids ever naming the minimal
primes of the quotient and makes the geometric statements a single `rw` away.

**The kernel of the composite is computed, not assumed.** `I_x + 𝔪_s·𝒪_{X,x}` is reached from the
two kernels `Scheme.IdealSheafData.ker_stalkMap_subschemeι` and
`Scheme.Hom.ker_stalkMap_fiberι` — by `Ideal.comap_map_of_surjective` along the *surjective* stalk
map of the preimmersion. The general form `ker_stalkMap_fiberι_comp` is stated for an arbitrary
preimmersion `ι` so that the ideal-sheaf case is an instance; nothing about ideal sheaves enters
its proof.

**`q` need only contain `I_x`, not equal it.** The algebra core wants the radical of
`q + 𝔪_A·𝒪_{X,x}` for `q` the prime belonging to the generic point `y` of `V(I)`. Identifying `q`
with `I_x` would be a theorem about the ideal sheaf of a reduced closure; it is not needed, since
`I_x ≤ q ≤ 𝔪_x` already sandwiches the radical between two copies of `𝔪_x`. The inclusion
`I_x ≤ q` is `stalkIdeal_le_comap_maximalIdeal`, which needs only that the germs of sections of
`I` die in `𝒪_{V(I),·}`.

**The base comparison is an iso of local rings, and that is all it is used for.** Over a local
ring `A` the stalk of `Spec A` at the closed point is `A` (Mathlib's
`AlgebraicGeometry.stalkClosedPointIso`), so at a point `x` with `f x = closedPoint A` the
`𝒪_{Spec A, f x}`-structures appearing in `AlgebraicGeometry.IsFlatOverAt` and in
`AlgebraicGeometry.LocallyOfFiniteType.stalkMap` are `A`-structures. Flatness crosses by
`Module.Flat.trans` (the comparison makes `𝒪_{Spec A, f x}` a free `A`-module of rank one) and
essential finiteness by `Algebra.EssFiniteType.comp`; no new transfer principle is proved. The
module and algebra structures are supplied in `letI` binders rather than as instances, for the
reason recorded in
`StacksFrontier/AlgebraicGeometry/Scheme/Points/ModuleStalkSpecialization.lean`: a global
instance would put an `A`-module
structure on the stalk of every module at every point of every scheme over every local ring.

## References

* [Stacks Project, Tag 0GSI](https://stacks.math.columbia.edu/tag/0GSI)
* [Stacks Project, Tag 08KT](https://stacks.math.columbia.edu/tag/08KT)
* [Stacks Project, Tag 01J7](https://stacks.math.columbia.edu/tag/01J7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace Stacks.ClosedFibreGenericPoint

/-! ### Generic points and the primes of the local ring there -/

/-- A generic point of an irreducible component of a `T0` space has no generalization other than
itself: a generalization has a larger closure, and maximality forces the two closures, hence the
two points, to agree. -/
theorem setOf_specializes_eq_singleton {Z : Type*} [TopologicalSpace Z] [T0Space Z]
    {x : Z} (hx : x ∈ genericPoints Z) : {z | z ⤳ x} = {x} := by
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨specializes_rfl, fun z (hz : z ⤳ x) ↦ ?_⟩
  have h1 : closure ({x} : Set Z) ⊆ closure ({z} : Set Z) := hz.closure_subset
  have h2 : closure ({z} : Set Z) ⊆ closure ({x} : Set Z) :=
    hx.2 isIrreducible_singleton.closure h1
  exact (hz.antisymm (specializes_iff_closure_subset.mpr h2)).eq

/-- **At a generic point of an irreducible component the local ring has a single prime.** The
points of `Spec 𝒪_{Z,x}` are the generalizations of `x` (Tag 01J7), of which there is only one,
and `Z.fromSpecStalk x` is injective because it is a preimmersion. -/
theorem isPrime_eq_maximalIdeal_of_mem_genericPoints {Z : Scheme.{u}} {x : Z}
    (hx : x ∈ genericPoints Z) (J : Ideal (Z.presheaf.stalk x)) [J.IsPrime] :
    J = maximalIdeal (Z.presheaf.stalk x) := by
  have hinj : Function.Injective (Z.fromSpecStalk x) :=
    (IsPreimmersion.isEmbedding (Z.fromSpecStalk x)).injective
  have hrange : Set.range (Z.fromSpecStalk x) = {x} := by
    rw [Scheme.range_fromSpecStalk, setOf_specializes_eq_singleton hx]
  have key : ∀ a b : ↥(Spec (Z.presheaf.stalk x)), a = b := fun a b ↦ by
    refine hinj ?_
    have ha : (Z.fromSpecStalk x) a ∈ ({x} : Set Z) := hrange ▸ Set.mem_range_self a
    have hb : (Z.fromSpecStalk x) b ∈ ({x} : Set Z) := hrange ▸ Set.mem_range_self b
    rw [Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  exact congrArg PrimeSpectrum.asIdeal
    (key (⟨J, inferInstance⟩ : ↥(Spec (Z.presheaf.stalk x)))
      (closedPoint (Z.presheaf.stalk x)))

/-- The nilradical of the local ring at a generic point of an irreducible component is the maximal
ideal. -/
theorem radical_bot_stalk_eq_maximalIdeal {Z : Scheme.{u}} {x : Z} (hx : x ∈ genericPoints Z) :
    (⊥ : Ideal (Z.presheaf.stalk x)).radical = maximalIdeal (Z.presheaf.stalk x) := by
  rw [Ideal.radical_eq_sInf]
  refine le_antisymm (sInf_le ⟨bot_le, inferInstance⟩) (le_sInf ?_)
  rintro J ⟨-, hJ⟩
  exact le_of_eq (isPrime_eq_maximalIdeal_of_mem_genericPoints hx J).symm

/-- **The radical of a kernel, at a generic point.** For a local homomorphism `π` from a local ring
`B` to the local ring at a generic point of an irreducible component, `√(ker π) = 𝔪_B`. -/
theorem radical_ker_eq_maximalIdeal {Z : Scheme.{u}} {x : Z} (hx : x ∈ genericPoints Z)
    {B : Type*} [CommRing B] [IsLocalRing B] (π : B →+* Z.presheaf.stalk x) [IsLocalHom π] :
    (RingHom.ker π).radical = maximalIdeal B := by
  have h1 : RingHom.ker π = (⊥ : Ideal (Z.presheaf.stalk x)).comap π := rfl
  rw [h1, ← Ideal.comap_radical, radical_bot_stalk_eq_maximalIdeal hx,
    IsLocalRing.maximalIdeal_comap π]

/-! ### The kernel of the stalk map of a fibre of a composite -/

/-- **The kernel of the stalk map of a fibre of a composite.** For a preimmersion `ι : Y ⟶ X` and
`f : X ⟶ S`, the stalk map at `z` of the composite `(ι ≫ f).fiber s ⟶ Y ⟶ X` has kernel the sum
of the kernel of the stalk map of `ι` and the ideal generated by the maximal ideal of `𝒪_{S,s}`.
-/
theorem ker_stalkMap_fiberι_comp {X S Y : Scheme.{u}} (f : X ⟶ S) (ι : Y ⟶ X)
    [IsPreimmersion ι] (s : S) (z : (ι ≫ f).fiber s) :
    RingHom.ker ((((ι ≫ f).fiberι s) ≫ ι).stalkMap z).hom
      = RingHom.ker (ι.stalkMap ((ι ≫ f).fiberι s z)).hom
        ⊔ f.stalkFibreIdeal (ι ((ι ≫ f).fiberι s z)) := by
  have hcomp : ((((ι ≫ f).fiberι s) ≫ ι).stalkMap z)
      = ι.stalkMap ((ι ≫ f).fiberι s z) ≫ ((ι ≫ f).fiberι s).stalkMap z :=
    Scheme.Hom.stalkMap_comp _ _ _
  have hsurj : Function.Surjective (ι.stalkMap ((ι ≫ f).fiberι s z)).hom :=
    ι.stalkMap_surjective _
  have hgstalk : (ι ≫ f).stalkMap ((ι ≫ f).fiberι s z)
      = f.stalkMap (ι ((ι ≫ f).fiberι s z)) ≫ ι.stalkMap ((ι ≫ f).fiberι s z) :=
    Scheme.Hom.stalkMap_comp _ _ _
  have hfib : (ι ≫ f).stalkFibreIdeal ((ι ≫ f).fiberι s z)
      = Ideal.map (ι.stalkMap ((ι ≫ f).fiberι s z)).hom
        (f.stalkFibreIdeal (ι ((ι ≫ f).fiberι s z))) := by
    rw [Scheme.Hom.stalkFibreIdeal, Scheme.Hom.stalkFibreIdeal, Ideal.map_map]
    congr 1
    exact congrArg CommRingCat.Hom.hom hgstalk
  rw [hcomp]
  have h1 : RingHom.ker (ι.stalkMap ((ι ≫ f).fiberι s z)
        ≫ ((ι ≫ f).fiberι s).stalkMap z).hom
      = Ideal.comap (ι.stalkMap ((ι ≫ f).fiberι s z)).hom
        (RingHom.ker (((ι ≫ f).fiberι s).stalkMap z).hom) := rfl
  refine h1.trans ?_
  rw [(ι ≫ f).ker_stalkMap_fiberι s z, hfib,
    Ideal.comap_map_of_surjective _ hsurj, sup_comm]
  rfl

/-- The same for the inclusion of the closed subscheme cut out by an ideal sheaf: the kernel is
`I_x + 𝔪_s·𝒪_{X,x}`. -/
theorem ker_stalkMap_fiberι_comp_subschemeι {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (s : S) (z : (I.subschemeι ≫ f).fiber s) :
    RingHom.ker ((((I.subschemeι ≫ f).fiberι s) ≫ I.subschemeι).stalkMap z).hom
      = I.stalkIdeal (I.subschemeι ((I.subschemeι ≫ f).fiberι s z))
        ⊔ f.stalkFibreIdeal (I.subschemeι ((I.subschemeι ≫ f).fiberι s z)) := by
  rw [ker_stalkMap_fiberι_comp f I.subschemeι s z, I.ker_stalkMap_subschemeι]

/-! ### The radical hypothesis -/

/-- **The radical hypothesis, geometric form.** If `z` is a generic point of an irreducible
component of the fibre over `s` of `V(I) ⟶ S`, then at the image `x` of `z` in `X` the ideal
`I_x + 𝔪_s·𝒪_{X,x}` has radical the maximal ideal of `𝒪_{X,x}`. -/
theorem radical_stalkIdeal_sup_stalkFibreIdeal {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (s : S) (z : (I.subschemeι ≫ f).fiber s)
    (hz : z ∈ genericPoints ((I.subschemeι ≫ f).fiber s)) :
    (I.stalkIdeal (I.subschemeι ((I.subschemeι ≫ f).fiberι s z))
        ⊔ f.stalkFibreIdeal (I.subschemeι ((I.subschemeι ≫ f).fiberι s z))).radical
      = maximalIdeal (X.presheaf.stalk (I.subschemeι ((I.subschemeι ≫ f).fiberι s z))) := by
  rw [← ker_stalkMap_fiberι_comp_subschemeι f I s z]
  exact radical_ker_eq_maximalIdeal hz
    ((((I.subschemeι ≫ f).fiberι s) ≫ I.subschemeι).stalkMap z).hom

/-- **The radical hypothesis for an ideal containing `I_x`.** Any ideal `q` with
`I_x ≤ q ≤ 𝔪_x` has `√(q + 𝔪_s·𝒪_{X,x}) = 𝔪_x`. -/
theorem radical_sup_stalkFibreIdeal_of_stalkIdeal_le {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (s : S) (z : (I.subschemeι ≫ f).fiber s)
    (hz : z ∈ genericPoints ((I.subschemeι ≫ f).fiber s))
    (q : Ideal (X.presheaf.stalk (I.subschemeι ((I.subschemeι ≫ f).fiberι s z))))
    (hIq : I.stalkIdeal (I.subschemeι ((I.subschemeι ≫ f).fiberι s z)) ≤ q)
    (hqm : q ≤ maximalIdeal (X.presheaf.stalk (I.subschemeι ((I.subschemeι ≫ f).fiberι s z)))) :
    (q ⊔ f.stalkFibreIdeal (I.subschemeι ((I.subschemeι ≫ f).fiberι s z))).radical
      = maximalIdeal (X.presheaf.stalk (I.subschemeι ((I.subschemeι ≫ f).fiberι s z))) := by
  refine le_antisymm ?_ ?_
  · refine (Ideal.radical_mono
      (sup_le hqm (f.stalkFibreIdeal_le_maximalIdeal _))).trans (le_of_eq ?_)
    exact Ideal.IsPrime.radical (maximalIdeal.isMaximal _).isPrime
  · rw [← radical_stalkIdeal_sup_stalkFibreIdeal f I s z hz]
    exact Ideal.radical_mono (sup_le_sup_right hIq _)

/-! ### The stalk ideal at a point of the subscheme -/

/-- At a point of the subscheme cut out by `I`, the stalk `I_x` is a proper ideal, hence contained
in the maximal ideal. -/
theorem stalkIdeal_le_maximalIdeal {X : Scheme.{u}} (I : X.IdealSheafData) (z : I.subscheme) :
    I.stalkIdeal (I.subschemeι z) ≤ maximalIdeal (X.presheaf.stalk (I.subschemeι z)) := by
  refine (I.stalkIdeal_le_ker_stalkMap_subschemeι z).trans ?_
  rw [← IsLocalRing.maximalIdeal_comap (I.subschemeι.stalkMap z).hom]
  exact Ideal.comap_mono bot_le

/-- **`I_x` lies in the prime belonging to a point of `V(I)` generalizing `x`.** If `y ⤳ x` and
`y` lies in the support of `I`, then the comparison `𝒪_{X,x} ⟶ 𝒪_{X,y}` carries the stalk ideal
`I_x` into the maximal ideal of `𝒪_{X,y}`: the germ at `x` of a section of `I` specializes to its
germ at `y`, which lies in `I_y`, a proper ideal of the local ring `𝒪_{X,y}`. -/
theorem stalkIdeal_le_comap_maximalIdeal {X : Scheme.{u}} (I : X.IdealSheafData) {x y : X}
    (h : y ⤳ x) (hy : y ∈ I.support) :
    I.stalkIdeal x
      ≤ (maximalIdeal (X.presheaf.stalk y)).comap (X.presheaf.stalkSpecializes h).hom := by
  obtain ⟨z, rfl⟩ := (I.range_subschemeι ▸ hy : y ∈ Set.range I.subschemeι)
  refine iSup_le fun U ↦ Ideal.map_le_iff_le_comap.2 fun a ha ↦ ?_
  rw [Ideal.mem_comap, Ideal.mem_comap,
    Stacks.ModuleStalkSpecialization.ringGerm_stalkSpecializes_apply U.2 h a]
  exact stalkIdeal_le_maximalIdeal I z (I.germ_mem_stalkIdeal U.1 (h.mem_open U.1.1.2 U.2) ha)

/-- **The radical hypothesis at the canonical prime of a generic point of `V(I)`.** For `y` in the
support of `I` generalizing the image `x` of `z`, the prime of `𝒪_{X,x}` obtained by contracting
`𝔪_y` along the comparison of local rings satisfies `√(q + 𝔪_s·𝒪_{X,x}) = 𝔪_x`. -/
theorem radical_under_sup_stalkFibreIdeal {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (s : S) (z : (I.subschemeι ≫ f).fiber s)
    (hz : z ∈ genericPoints ((I.subschemeι ≫ f).fiber s))
    {y : X} (hy : y ∈ I.support)
    (h : y ⤳ I.subschemeι ((I.subschemeι ≫ f).fiberι s z)) :
    letI : Algebra (X.presheaf.stalk (I.subschemeι ((I.subschemeι ≫ f).fiberι s z)))
        (X.presheaf.stalk y) := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    (((maximalIdeal (X.presheaf.stalk y)).under
          (X.presheaf.stalk (I.subschemeι ((I.subschemeι ≫ f).fiberι s z))))
        ⊔ f.stalkFibreIdeal (I.subschemeι ((I.subschemeι ≫ f).fiberι s z))).radical
      = maximalIdeal (X.presheaf.stalk (I.subschemeι ((I.subschemeι ≫ f).fiberι s z))) := by
  let : Algebra (X.presheaf.stalk (I.subschemeι ((I.subschemeι ≫ f).fiberι s z)))
      (X.presheaf.stalk y) := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have hprime : ((maximalIdeal (X.presheaf.stalk y)).under
      (X.presheaf.stalk (I.subschemeι ((I.subschemeι ≫ f).fiberι s z)))).IsPrime :=
    Ideal.comap_isPrime _ _
  exact radical_sup_stalkFibreIdeal_of_stalkIdeal_le f I s z hz _
    (stalkIdeal_le_comap_maximalIdeal I h hy) (IsLocalRing.le_maximalIdeal hprime.ne_top)

/-! ### The point of `X` underlying a point of the fibre of a composite -/

/-- The image in `X` of a point of the fibre of `ι ≫ f` over `s` lies over `s`. -/
theorem apply_fiberι_comp {X S Y : Scheme.{u}} (f : X ⟶ S) (ι : Y ⟶ X) (s : S)
    (z : (ι ≫ f).fiber s) : f (ι ((ι ≫ f).fiberι s z)) = s := by
  have h : (ι ≫ f) ((ι ≫ f).fiberι s z) = s :=
    ((ι ≫ f).range_fiberι s ▸ Set.mem_range_self z : (ι ≫ f).fiberι s z ∈ (ι ≫ f) ⁻¹' {s})
  rwa [Scheme.Hom.comp_apply] at h

/-- A point lies in the support of the vanishing ideal of the closure of its own singleton. -/
theorem mem_support_vanishingIdeal_closure {X : Scheme.{u}} (y : X) :
    y ∈ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).support := by
  change y ∈ ((Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({y} : Set X))).support : Set X)
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact subset_closure rfl

/-- Every point of the reduced closure of `{y}`, viewed as a closed subscheme, is a
specialization of `y`. -/
theorem specializes_subschemeι_vanishingIdeal_closure {X : Scheme.{u}} (y : X)
    (z : (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).subscheme) :
    y ⤳ (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).subschemeι z := by
  have h1 : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set X))).subschemeι z
      ∈ ((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set X))).support : Set X) := by
    rw [← (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set X))).range_subschemeι]
    exact Set.mem_range_self z
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal] at h1
  exact specializes_iff_mem_closure.mpr h1

end Stacks.ClosedFibreGenericPoint

namespace Stacks.BaseStalk

/-! ### The local ring at a point over the closed point of the base -/

variable {A : Type u} [CommRing A] [IsLocalRing A] {X : Scheme.{u}}

/-- **The comparison `A ≅ 𝒪_{Spec A, f x}`** at a point `x` of `X` lying over the closed point of
`Spec A`, for `A` a local ring. It is Mathlib's `AlgebraicGeometry.stalkClosedPointIso` followed by
the transport of the stalk along the equality of points. -/
noncomputable def baseStalkIso (f : X ⟶ Spec (.of A)) (x : X) (hx : f x = closedPoint A) :
    CommRingCat.of A ≅ (Spec (.of A)).presheaf.stalk (f x) :=
  (stalkClosedPointIso (.of A)).symm ≪≫
    (Spec (.of A)).presheaf.stalkCongr (Inseparable.of_eq hx.symm)

/-- The canonical ring map `A ⟶ 𝒪_{X,x}` at a point over the closed point of `Spec A`. -/
noncomputable def baseStalkHom (f : X ⟶ Spec (.of A)) (x : X) (hx : f x = closedPoint A) :
    CommRingCat.of A ⟶ X.presheaf.stalk x :=
  (baseStalkIso f x hx).hom ≫ f.stalkMap x

/-- The `A`-module structure on the stalk of an `𝒪_X`-module at a point over the closed point of
`Spec A`, by restricting scalars along `baseStalkHom`. It is a definition rather than an instance,
for the reason given in the implementation notes. -/
@[instance_reducible]
noncomputable def baseStalkModule (f : X ⟶ Spec (.of A)) (F : X.Modules) (x : X)
    (hx : f x = closedPoint A) : Module A (F.presheaf.stalk x) :=
  letI := Stacks.ModuleStalkSpecialization.stalkModule F x
  Module.compHom _ (baseStalkHom f x hx).hom

/-- The comparison `A ≅ 𝒪_{Spec A, f x}` is bijective on underlying types. -/
private theorem bijective_baseStalkIso (f : X ⟶ Spec (.of A)) (x : X) (hx : f x = closedPoint A) :
    Function.Bijective (baseStalkIso f x hx).hom.hom :=
  ConcreteCategory.bijective_of_isIso (baseStalkIso f x hx).hom

/-- The comparison `A ≅ 𝒪_{Spec A, f x}` is a local homomorphism, being surjective out of a local
ring. -/
theorem isLocalHom_baseStalkIso (f : X ⟶ Spec (.of A)) (x : X) (hx : f x = closedPoint A) :
    IsLocalHom (baseStalkIso f x hx).hom.hom :=
  IsLocalHom.of_surjective _ (bijective_baseStalkIso f x hx).2

/-- The canonical map `A ⟶ 𝒪_{X,x}` is a local homomorphism. -/
theorem isLocalHom_baseStalkHom (f : X ⟶ Spec (.of A)) (x : X) (hx : f x = closedPoint A) :
    IsLocalHom (baseStalkHom f x hx).hom := by
  have := isLocalHom_baseStalkIso f x hx
  exact RingHom.isLocalHom_comp (f.stalkMap x).hom (baseStalkIso f x hx).hom.hom

/-- **The two spellings of `𝔪_A·𝒪_{X,x}` agree.** The ideal generated by the image of the maximal
ideal of `A` under `baseStalkHom` is `AlgebraicGeometry.Scheme.Hom.stalkFibreIdeal`, the ideal
generated by the image of the maximal ideal of `𝒪_{Spec A, f x}`. -/
theorem map_maximalIdeal_baseStalkHom (f : X ⟶ Spec (.of A)) (x : X)
    (hx : f x = closedPoint A) :
    Ideal.map (baseStalkHom f x hx).hom (maximalIdeal A) = f.stalkFibreIdeal x := by
  let _ := isLocalHom_baseStalkIso f x hx
  have hm : Ideal.map (baseStalkIso f x hx).hom.hom (maximalIdeal A)
      = maximalIdeal ((Spec (.of A)).presheaf.stalk (f x)) := by
    rw [← IsLocalRing.maximalIdeal_comap (baseStalkIso f x hx).hom.hom]
    exact Ideal.map_comap_of_surjective _ (bijective_baseStalkIso f x hx).2 _
  rw [Scheme.Hom.stalkFibreIdeal, ← hm, Ideal.map_map]
  rfl

/-- **Essential finiteness of the local ring over the base ring.** For `f : X ⟶ Spec A` locally of
finite type, `A` local and `x` a point over the closed point, the stalk `𝒪_{X,x}` is essentially
of finite type over `A`. -/
theorem essFiniteType_baseStalk (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] (x : X)
    (hx : f x = closedPoint A) :
    letI : Algebra A (X.presheaf.stalk x) := (baseStalkHom f x hx).hom.toAlgebra
    Algebra.EssFiniteType A (X.presheaf.stalk x) := by
  let : Algebra A ((Spec (.of A)).presheaf.stalk (f x)) :=
    (baseStalkIso f x hx).hom.hom.toAlgebra
  let : Algebra ((Spec (.of A)).presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let : Algebra A (X.presheaf.stalk x) := (baseStalkHom f x hx).hom.toAlgebra
  have : IsScalarTower A ((Spec (.of A)).presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have h1 : Algebra.EssFiniteType A ((Spec (.of A)).presheaf.stalk (f x)) :=
    Algebra.EssFiniteType.of_surjective (Algebra.ofId A _)
      (bijective_baseStalkIso f x hx).2
  have h2 : Algebra.EssFiniteType ((Spec (.of A)).presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    AlgebraicGeometry.LocallyOfFiniteType.stalkMap f x
  exact Algebra.EssFiniteType.comp A ((Spec (.of A)).presheaf.stalk (f x)) _

/-- **Flatness over the base ring.** An `𝒪_X`-module flat over `Spec A` at a point `x` lying over
the closed point of `Spec A` — that is, satisfying `AlgebraicGeometry.IsFlatOverAt` (Tag 08KT (1))
— has `A`-flat stalk at `x`. -/
theorem flat_of_isFlatOverAt (f : X ⟶ Spec (.of A)) (F : X.Modules) (x : X)
    (hx : f x = closedPoint A)
    (hF : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x) :
    letI := baseStalkModule f F x hx
    Module.Flat A (F.presheaf.stalk x) := by
  let : Algebra A ((Spec (.of A)).presheaf.stalk (f x)) :=
    (baseStalkIso f x hx).hom.hom.toAlgebra
  let := Stacks.ModuleStalkSpecialization.stalkModule F x
  let hR : Module ((Spec (.of A)).presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  let := baseStalkModule f F x hx
  have htower : IsScalarTower A ((Spec (.of A)).presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have hflatA : Module.Flat A ((Spec (.of A)).presheaf.stalk (f x)) :=
    Module.Flat.of_linearEquiv (R := A) (M := A)
      (LinearEquiv.ofBijective (Algebra.linearMap A _)
        (bijective_baseStalkIso f x hx)).symm
  have hflatR : Module.Flat ((Spec (.of A)).presheaf.stalk (f x)) (F.presheaf.stalk x) := hF
  exact Module.Flat.trans A ((Spec (.of A)).presheaf.stalk (f x)) (F.presheaf.stalk x)

end Stacks.BaseStalk

end
