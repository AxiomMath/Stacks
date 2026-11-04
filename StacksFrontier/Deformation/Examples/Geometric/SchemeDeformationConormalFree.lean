module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSectionsTuples
public import StacksFrontier.AlgebraicGeometry.Smooth.ThickeningRestriction
public import StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationConormal

/-!
# The conormal sheaf of the special fibre of a square-zero deformation, in arbitrary rank

Let `X` be a scheme over a field `k` and let `P` be a deformation of `X` over an object `A` of
`𝒞_Λ` whose maximal ideal is square-zero, `𝔪_A ^ 2 = 0`. This file computes the conormal sheaf
of the special-fibre closed immersion `X ⟶ X'` to be **free of rank `dim_k 𝔪_A`**, with no
hypothesis on that rank.

The conormal chain of
`StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationConormal` is already stated
without a rank hypothesis — `Deformation.Examples.idealSheafIsoOfKerIsoTop`,
`Deformation.Examples.conormalIsoOfIdealSheafIso`, `Deformation.Examples.residueConormalIso`
and `Deformation.Examples.deformationConormalIso` propagate an identification of the kernel of
the surjection on global sections to the conormal sheaf of the special fibre. What that chain
was missing is the identification itself in general rank: the only one available was
`Deformation.Examples.quotientEquivDualNumberKernel`, which identifies the kernel with the
residue field by multiplication by `ε` and so is confined to rank one. This file supplies the
general-rank identification and runs the chain with it.

Square-zeroness of `𝔪_A` is the *only* hypothesis, and finite-dimensionality is a consequence
of it rather than an input: `𝔪_A ^ 2 = 0` makes `𝔪_A` a module over `A/𝔪_A ≅ k`, an Artinian
ring is Noetherian so `𝔪_A` is a finitely generated `A`-module, and a module finitely generated
over `A` whose action factors through `k` is a finite-dimensional `k`-vector space — hence free,
with a basis indexed by `Fin (dim_k 𝔪_A)`.

## Main definitions

* `Deformation.Examples.topComorphism` is the comorphism of a morphism of ringed spaces on the
  global sections of the target, retyped so that the module structures below can be stated over
  it.
* `Deformation.Examples.residueKerRank` is `dim_k 𝔪_A`, the rank the answer has.
* `Deformation.Examples.kerIsoFreeTop` and
  `Deformation.Examples.idealSheafIsoPushforwardFree`: for a morphism of ringed spaces onto a
  one-point space whose kernel on global sections is the module of `n`-tuples of sections of the
  source, the ideal sheaf is the pushforward of the free sheaf of modules of rank `n`. This is
  what discharges the hypothesis of `Deformation.Examples.idealSheafIsoOfKerIsoTop` in rank `n`.
* `Deformation.Examples.residueKerEquivPi` and
  `Deformation.Examples.residueTopKerEquivPi`: the maximal ideal of `A` as the module of
  `dim_k 𝔪_A`-tuples over `k`, first on `A` itself and then read on the global sections of
  `Spec A`.
* `Deformation.Examples.residueIdealSheafIsoFree` and
  `Deformation.Examples.residueConormalIsoFree`: the ideal sheaf, resp. the conormal sheaf, of
  the closed point of `Spec A` is the pushforward of, resp. is, the free sheaf of modules on
  `Spec k` of rank `dim_k 𝔪_A`.
* `Deformation.Examples.deformationConormalIsoFree`: **the payoff.** The conormal sheaf of the
  special fibre of a deformation over a square-zero base is the free sheaf of modules on `X` of
  rank `dim_k 𝔪_A`.

## Main results

* `Deformation.Examples.maximalIdeal_pow_two_eq_bot_of_coordinate`: an object of `𝒞_Λ` carrying
  a dual-number coordinate has square-zero maximal ideal, so the hypothesis used here is implied
  by the one the rank-one declarations of
  `StacksFrontier.Deformation.Examples.Geometric.SchemeDeformationConormal` carry.
* `Deformation.Examples.residueKerRank_eq_one`: for a base carrying a dual-number coordinate the
  rank computed here is `1`, so the general-rank chain gives at such a base exactly what the
  rank-one chain gives. Together with the previous item this is the precise sense in which this
  file generalises `Deformation.Examples.residueConormalIsoUnit` and
  `Deformation.Examples.deformationConormalIsoUnit`: the hypothesis is weaker and the answer
  specialises to theirs.
* `Deformation.Examples.ker_residueMap_pow_two` and
  `Deformation.Examples.finite_ker_residueMap`: the kernel of the residue map is square-zero and
  is a finite-dimensional `k`-vector space.
* `Deformation.Examples.residueMap_eq_zero_iff_coordinate`: the ring-level form of
  `Deformation.Examples.residueSpecMap_app_eq_zero_iff` — the maximal ideal of an object of
  `𝒞_Λ` with a dual-number coordinate is the vanishing of the first coordinate.
* `Deformation.Examples.specIso_topComorphism`: the comorphism of the closed point on global
  sections is the residue map, read through `AlgebraicGeometry.Scheme.ΓSpecIso`. This is the
  commuting square along which the computation on `A` is transported to `Spec A`.

## Implementation notes

The index type of the free sheaf is `ULift (Fin n)`, not `Fin n`:
`CategoryTheory.SheafOfModules.free` takes an index type in the universe of the modules, which here
is the universe `u` of `k`, and `Fin n` lives in `Type 0`.
`Stacks.SheafOfModules.freeSectionsCoeff` is stated for exactly that index type and is what
identifies the sections of the free sheaf with tuples; no bundled identification had to be built,
and the finite coproduct defining the free sheaf is turned into a product there by additivity of
evaluation.

The computation happens twice, on two rings that are isomorphic but not equal: on `A`, where
`Stacks.Smooth.kerModule` and `Module.finBasis` are available, and on `Γ(Spec A, ⊤)`, which is
what the sheaf-theoretic statement is about. `Stacks.Smooth.kerEquivPiOfRingEquiv` carries the
first to the second along `AlgebraicGeometry.Scheme.ΓSpecIso`, whose naturality is
`Deformation.Examples.specIso_topComorphism`. Doing the algebra on `Γ(Spec A, ⊤)` directly would
need the local and Artinian structure of `A` transported there instead, which is the same work
in a less convenient place.

Two spellings of the global comorphism occur: `(t.hom.c.app (op ⊤)).hom`, whose codomain is read
in the pushforward presheaf, and `Deformation.Examples.topComorphism`, which is the same map with
its codomain read as the sections of the structure presheaf of the source over the preimage of
`⊤`. They are equal by `rfl`; only the second lets `RingHom.toAlgebra` and the module structure
on the tuples be stated, because the first presents its codomain in a form instance search does
not match against `Pi.module`.

## References

* [Stacks Project, Tag 0DY7](https://stacks.math.columbia.edu/tag/0DY7)
* [Stacks Project, Tag 0473](https://stacks.math.columbia.edu/tag/0473)
* [Stacks Project, Tag 0E3V](https://stacks.math.columbia.edu/tag/0E3V)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction

universe u

namespace Deformation.Examples

attribute [local instance] residueSpecMap_isClosedImmersion
  deformationSpecialMap_isClosedImmersion

/-! ### The ideal sheaf of a point whose global kernel is a module of tuples -/

/-- The comorphism of a morphism of ringed spaces on the global sections of the target, with its
codomain read as the sections of the structure presheaf of the source over the preimage of `⊤`.

This is `(t.hom.c.app (op ⊤)).hom` and equal to it by `rfl`; what the retyping buys is that the
codomain is now a value of `X.presheaf`, so that `RingHom.toAlgebra` applies and the module
structure on tuples of sections is found by instance search. -/
abbrev topComorphism {X Y : RingedSpace.{u, u}} (t : X ⟶ Y) :
    (Y.presheaf.obj (op ⊤) : Type u) →+*
      (X.presheaf.obj (op ((opensMap t).obj ⊤)) : Type u) :=
  (t.hom.c.app (op ⊤)).hom

/-- **The kernel of the comorphism on global sections, when it is the module of `n`-tuples of
sections of the source, is the global sections of the pushforward of the free sheaf of modules
of rank `n`.** This is the hypothesis of `Deformation.Examples.idealSheafIsoOfKerIsoTop` in rank
`n`, and no rank hypothesis is hidden in it: `n` is arbitrary.

The sections of the pushforward over `⊤` are the sections of the source over the preimage of
`⊤`, with scalars restricted along the comorphism — by `rfl` — and those are the tuples by
`Stacks.SheafOfModules.freeSectionsCoeff`. -/
def kerIsoFreeTop {X Y : RingedSpace.{u, u}} (t : X ⟶ Y) (n : ℕ)
    (e : letI := (topComorphism t).toAlgebra
      RingHom.ker (topComorphism t) ≃ₗ[Y.presheaf.obj (op ⊤)]
        (Fin n → X.presheaf.obj (op ((opensMap t).obj ⊤)))) :
    ModuleCat.of (Y.presheaf.obj (op ⊤)) (RingHom.ker (topComorphism t)) ≅
      (SheafOfModules.evaluation (structureSheafRing Y) (op ⊤)).obj
        ((modulePushforward t).obj (SheafOfModules.free (ULift.{u} (Fin n)))) :=
  letI := (topComorphism t).toAlgebra
  e.toModuleIso ≪≫
    (ModuleCat.restrictScalars (topComorphism t)).mapIso
      (Stacks.SheafOfModules.freeSectionsCoeff (R := structureSheafRing X) n
        (op ((opensMap t).obj ⊤))).toModuleIso

/-- **The ideal sheaf of a closed point of a one-point space whose kernel on global sections is
the module of `n`-tuples is the pushforward of the free sheaf of modules of rank `n`.** This is
`Deformation.Examples.idealSheafIsoOfKerIsoTop` with its hypothesis supplied by
`Deformation.Examples.kerIsoFreeTop`; it is the general-rank replacement for
`Deformation.Examples.idealSheafIsoPushforwardUnitOfCoordinate`, which is the case `n = 1` with
the trivialisation of the kernel coming from a dual-number coordinate. -/
def idealSheafIsoPushforwardFree {X Y : RingedSpace.{u, u}} [Subsingleton Y] (t : X ⟶ Y) (n : ℕ)
    (e : letI := (topComorphism t).toAlgebra
      RingHom.ker (topComorphism t) ≃ₗ[Y.presheaf.obj (op ⊤)]
        (Fin n → X.presheaf.obj (op ((opensMap t).obj ⊤)))) :
    Stacks.ClosedImmersion.idealSheaf t ≅
      (modulePushforward t).obj (SheafOfModules.free (ULift.{u} (Fin n))) :=
  idealSheafIsoOfKerIsoTop t _ (kerIsoFreeTop t n e)

/-! ### The maximal ideal of a square-zero object of `𝒞_Λ` as a vector space -/

variable {Λ k : Type u} [CommRing Λ] [Field k] [Algebra Λ k]

/-- An element of an object of `𝒞_Λ` with a dual-number coordinate lies in the maximal ideal
exactly when the first coordinate of its dual-number expansion vanishes. -/
private theorem mem_maximalIdeal_iff_coordinate_fst (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (coordinate : A ≃ₐ[Λ] DualNumber k) (x : (A : Type u)) :
    x ∈ IsLocalRing.maximalIdeal (A : Type u) ↔ (coordinate x).fst = 0 := by
  let r : (A : Type u) →+* k :=
    (TrivSqZeroExt.fstHom k k k).toRingHom.comp coordinate.toRingEquiv.toRingHom
  have hr : Function.Surjective r := fun a ↦
    ⟨coordinate.symm (TrivSqZeroExt.inl a), by simp [r]⟩
  rw [← IsLocalRing.ker_eq_maximalIdeal r hr]
  rfl

/-- **An object of `𝒞_Λ` carrying a dual-number coordinate has square-zero maximal ideal.**
Through the coordinate the maximal ideal is the vanishing of the first coordinate, and a product
of two dual numbers with vanishing first coordinate is zero.

This is what makes the hypothesis of the declarations below weaker than the one carried by
`Deformation.Examples.residueConormalIsoUnit` and
`Deformation.Examples.deformationConormalIsoUnit`. -/
theorem maximalIdeal_pow_two_eq_bot_of_coordinate (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (coordinate : A ≃ₐ[Λ] DualNumber k) :
    IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥ := by
  rw [pow_two]
  refine le_antisymm (Ideal.mul_le.2 fun x hx y hy ↦ ?_) bot_le
  have hx' := (mem_maximalIdeal_iff_coordinate_fst A coordinate x).1 hx
  have hy' := (mem_maximalIdeal_iff_coordinate_fst A coordinate y).1 hy
  have hxy : coordinate (x * y) = 0 := by
    rw [map_mul]
    ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, hx', hy']
  simpa using coordinate.injective (hxy.trans (map_zero coordinate).symm)

/-- The kernel of the residue map of an object of `𝒞_Λ` with square-zero maximal ideal is
square-zero: the kernel of a surjection onto a field out of a local ring is the maximal
ideal. -/
theorem ker_residueMap_pow_two (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hsq : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥) :
    RingHom.ker (Deformation.Artin.residueMap A) ^ 2 = ⊥ := by
  rw [IsLocalRing.ker_eq_maximalIdeal _ (residueMap_surjective A)]
  exact hsq

/-- **The maximal ideal of an object of `𝒞_Λ` with square-zero maximal ideal is a
finite-dimensional `k`-vector space.** It is a finitely generated module over `A`, which is
Artinian hence Noetherian, and the `k`-action of `Stacks.Smooth.kerModule` is the `A`-action read
through the residue map, so a finite generating family over `A` is one over `k`. -/
theorem finite_ker_residueMap (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hsq : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥) :
    letI := Stacks.Smooth.kerModule (residueMap_surjective A) (ker_residueMap_pow_two A hsq)
    Module.Finite k (RingHom.ker (Deformation.Artin.residueMap A)) := by
  let := Stacks.Smooth.kerModule (residueMap_surjective A) (ker_residueMap_pow_two A hsq)
  let := (Deformation.Artin.residueMap A).toAlgebra
  have : IsScalarTower (A : Type u) k (RingHom.ker (Deformation.Artin.residueMap A)) :=
    IsScalarTower.of_algebraMap_smul fun r x ↦
      Stacks.Smooth.kerModule_smul (residueMap_surjective A) (ker_residueMap_pow_two A hsq) r x
  exact Module.Finite.of_restrictScalars_finite (A : Type u) k _

/-- `dim_k 𝔪_A`, the embedding dimension of an object of `𝒞_Λ` with square-zero maximal ideal
and the rank of the conormal sheaf computed below. It is the dimension of the kernel of the
residue map, which is the maximal ideal by `IsLocalRing.ker_eq_maximalIdeal`, over the residue
field acting through `Stacks.Smooth.kerModule`. -/
def residueKerRank (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hsq : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥) : ℕ :=
  letI := Stacks.Smooth.kerModule (residueMap_surjective A) (ker_residueMap_pow_two A hsq)
  Module.finrank k (RingHom.ker (Deformation.Artin.residueMap A))

/-- **The maximal ideal of an object of `𝒞_Λ` with square-zero maximal ideal is the module of
`dim_k 𝔪_A`-tuples of elements of `k`**, as a module over `A` acting through the residue map.
The basis is `Module.finBasis`, available because
`Deformation.Examples.finite_ker_residueMap` makes the maximal ideal a finite-dimensional vector
space, and `Stacks.Smooth.kerEquivPi` reads it as an `A`-linear equivalence. -/
def residueKerEquivPi (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hsq : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥) :
    letI := (Deformation.Artin.residueMap A).toAlgebra
    RingHom.ker (Deformation.Artin.residueMap A) ≃ₗ[(A : Type u)]
      (Fin (residueKerRank A hsq) → k) :=
  letI := Stacks.Smooth.kerModule (residueMap_surjective A) (ker_residueMap_pow_two A hsq)
  haveI := finite_ker_residueMap A hsq
  Stacks.Smooth.kerEquivPi
    (Stacks.Smooth.kerModule_smul (residueMap_surjective A) (ker_residueMap_pow_two A hsq))
    (Module.finBasis k (RingHom.ker (Deformation.Artin.residueMap A)))

/-- A function on an object of `𝒞_Λ` with a dual-number coordinate restricts to zero at the
closed point exactly when the first coordinate of its dual-number expansion vanishes: both
conditions say that it lies in the maximal ideal. This is the ring-level form of
`Deformation.Examples.residueSpecMap_app_eq_zero_iff`, and is what feeds
`Deformation.Examples.quotientEquivDualNumberKernel` at the residue map itself. -/
theorem residueMap_eq_zero_iff_coordinate (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (coordinate : A ≃ₐ[Λ] DualNumber k) (x : (A : Type u)) :
    Deformation.Artin.residueMap A x = 0 ↔ (coordinate.toRingEquiv x).fst = 0 := by
  have := mem_maximalIdeal_iff_coordinate_fst A coordinate x
  rwa [← IsLocalRing.ker_eq_maximalIdeal _ (residueMap_surjective A)] at this

/-- **An object of `𝒞_Λ` carrying a dual-number coordinate has embedding dimension one**, so the
rank at which the general-rank chain below computes the conormal sheaf of its closed point is
`1`, the rank at which `Deformation.Examples.residueConormalIsoUnit` computes it.

`Deformation.Examples.quotientEquivDualNumberKernel` identifies the maximal ideal with `k` as a
module over `A`, by multiplication by `ε`, and
`Stacks.Smooth.kerEquivQuotientOfLinearEquiv` upgrades that to an identification over `k`, which
is what a dimension count needs. -/
theorem residueKerRank_eq_one (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (coordinate : A ≃ₐ[Λ] DualNumber k)
    (hsq : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥) :
    residueKerRank A hsq = 1 := by
  let := (Deformation.Artin.residueMap A).toAlgebra
  let := Stacks.Smooth.kerModule (residueMap_surjective A) (ker_residueMap_pow_two A hsq)
  let E := Stacks.Smooth.kerEquivQuotientOfLinearEquiv (residueMap_surjective A)
    (ker_residueMap_pow_two A hsq)
    (quotientEquivDualNumberKernel (Deformation.Artin.residueMap A) coordinate.toRingEquiv
      (residueMap_surjective A) (residueMap_eq_zero_iff_coordinate A coordinate)).val
  show Module.finrank k (RingHom.ker (Deformation.Artin.residueMap A)) = 1
  rw [← E.finrank_eq, Module.finrank_self]

/-! ### The conormal sheaf of the closed point, and of the special fibre -/

/-- **The comorphism of the closed point of `Spec A` on global sections is the residue map**,
read through `AlgebraicGeometry.Scheme.ΓSpecIso` on both sides. This is the naturality square of
`AlgebraicGeometry.Scheme.ΓSpecIso` at the residue map, and it is the square along which
`Deformation.Examples.residueKerEquivPi` is transported from `A` to `Γ(Spec A, ⊤)`. -/
theorem specIso_topComorphism (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (a : (baseSpec A).presheaf.obj (op ⊤)) :
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
        (topComorphism (residueSpecMap A).toLRSHom.toShHom a)
      = Deformation.Artin.residueMap A
          ((Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv a) :=
  congrArg (fun f : (baseSpec A).presheaf.obj (op ⊤) ⟶ CommRingCat.of k ↦ f.hom a)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Deformation.Artin.residueMap A)))

/-- `Deformation.Examples.residueKerEquivPi` read on the global sections of `Spec A`: the kernel
of the comorphism of the closed point is the module of `dim_k 𝔪_A`-tuples of global sections of
`Spec k`. The transport is `Stacks.Smooth.kerEquivPiOfRingEquiv` along the two instances of
`AlgebraicGeometry.Scheme.ΓSpecIso`, whose commuting square is
`Deformation.Examples.specIso_topComorphism`. -/
def residueTopKerEquivPi (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hsq : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥) :
    letI := (topComorphism (residueSpecMap A).toLRSHom.toShHom).toAlgebra
    RingHom.ker (topComorphism (residueSpecMap A).toLRSHom.toShHom)
        ≃ₗ[(baseSpec A).presheaf.obj (op ⊤)]
      (Fin (residueKerRank A hsq) → (Spec (CommRingCat.of k)).presheaf.obj
        (op ((opensMap (residueSpecMap A).toLRSHom.toShHom).obj ⊤))) :=
  Stacks.Smooth.kerEquivPiOfRingEquiv _ (Deformation.Artin.residueMap A)
    (Scheme.ΓSpecIso (CommRingCat.of A)).commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (CommRingCat.of k)).commRingCatIsoToRingEquiv
    (specIso_topComorphism A) (residueKerEquivPi A hsq)

/-- **The ideal sheaf of the closed point of the spectrum of an object of `𝒞_Λ` with square-zero
maximal ideal is the pushforward of the free sheaf of modules on `Spec k` of rank `dim_k 𝔪_A`.**
This is `Deformation.Examples.idealSheafIsoPushforwardFree` with its hypothesis supplied by
`Deformation.Examples.residueTopKerEquivPi`. -/
def residueIdealSheafIsoFree (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hsq : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥) :
    Stacks.ClosedImmersion.idealSheaf (residueSpecMap A).toLRSHom.toShHom ≅
      (modulePushforward (residueSpecMap A).toLRSHom.toShHom).obj
        (SheafOfModules.free (ULift.{u} (Fin (residueKerRank A hsq)))) :=
  idealSheafIsoPushforwardFree _ _ (residueTopKerEquivPi A hsq)

/-- **The conormal sheaf of the closed point of the spectrum of an object of `𝒞_Λ` with
square-zero maximal ideal is free of rank `dim_k 𝔪_A` on `Spec k`.** This is
`Deformation.Examples.residueConormalIso`, which carries no rank hypothesis, with its
ideal-sheaf hypothesis supplied by `Deformation.Examples.residueIdealSheafIsoFree`. It is the
general-rank form of `Deformation.Examples.residueConormalIsoUnit`, whose dual-number
coordinate implies this hypothesis by
`Deformation.Examples.maximalIdeal_pow_two_eq_bot_of_coordinate`. -/
def residueConormalIsoFree (A : ArtinianLocalAlgCat.{u, u, u} Λ k)
    (hsq : IsLocalRing.maximalIdeal (A : Type u) ^ 2 = ⊥) :
    Stacks.Thickenings.immersionConormalSheaf (residueSpecMap A) ≅
      SheafOfModules.free (R := structureSheafRing (Spec (CommRingCat.of k)).toRingedSpace)
        (ULift.{u} (Fin (residueKerRank A hsq))) :=
  residueConormalIso A (residueIdealSheafIsoFree A hsq)

variable {X : Over (Spec (CommRingCat.of k))}

/-- **The conormal sheaf of the special-fibre closed immersion of a deformation over a base with
square-zero maximal ideal is free of rank `dim_k 𝔪_A` on the scheme being deformed.** This is
`Deformation.Examples.deformationConormalIso`, which carries no rank hypothesis, with its
hypothesis supplied by `Deformation.Examples.residueConormalIsoFree`, followed by
`RingedSpaceModuleAdjunction.modulePullbackFreeIso`, which identifies the pullback of a free
sheaf of modules with the free sheaf of modules.

It is the general-rank form of `Deformation.Examples.deformationConormalIsoUnit`: for a base
carrying a dual-number coordinate the hypothesis holds by
`Deformation.Examples.maximalIdeal_pow_two_eq_bot_of_coordinate`. -/
def deformationConormalIsoFree (P : SchemeDeformationCategory (Λ := Λ) (k := k) X)
    (hsq : IsLocalRing.maximalIdeal (P.base : Type u) ^ 2 = ⊥) :
    Stacks.Thickenings.immersionConormalSheaf P.specialMap ≅
      SheafOfModules.free (R := structureSheafRing X.left.toRingedSpace)
        (ULift.{u} (Fin (residueKerRank P.base hsq))) :=
  deformationConormalIso P (residueConormalIsoFree P.base hsq) ≪≫
    modulePullbackFreeIso X.hom.toLRSHom.toShHom _

end Deformation.Examples

end
