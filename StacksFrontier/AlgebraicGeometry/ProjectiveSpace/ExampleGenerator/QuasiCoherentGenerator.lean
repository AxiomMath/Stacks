module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatCoproduct
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.InvertibleTwistDerived
public import StacksFrontier.AlgebraicGeometry.AmpleNonvanishing.TwistOrthogonalVanishing
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.DerivedStructureSheaf
public import StacksFrontier.AlgebraicGeometry.ProjKoszulComplex.LocallyFree
public import StacksFrontier.AlgebraicGeometry.ProjTwistPowers.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistQuotient.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.AmpleTwistingSheaf
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Cohomology.CoherentSerreVanishing
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.ExampleGenerator.Koszul
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DerivedTensorBoundedAbove
import StacksCore.Tactic.StacksAttribute

/-!
# `𝒪 ⊕ 𝒪(-1) ⊕ ⋯ ⊕ 𝒪(-n)` generates `D_QCoh(𝒪_{P^n_A})`

Let `A` be a ring and `X = P^n_A = Proj A[T₀, …, Tₙ]`. This file completes [Stacks, Tag 0A9V]
on `D_QCoh(𝒪_X)`: the object

`E = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)`,

placed in degree zero, is a weak generator of `D_QCoh(𝒪_X)` — every object of `D_QCoh(𝒪_X)`
receiving only zero morphisms from the shifts of `E` is zero.

## The argument

`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/ExampleGenerator/Koszul.lean` supplies the
generation step: every twist `𝒪_X(-m)`, `m ≥ 0`, lies in the subcategory `⟨E⟩` of
[Stacks, Tag 09SI]. With [Stacks, Tag 09SK] this turns the vanishing of `Hom(E, K⟦i⟧)` into the
vanishing of every `Hom(𝒪_X(-m)[-p], K)`.

What remains is that an object of `D_QCoh(𝒪_X)` orthogonal to all the non-positive twists is
zero, and that is `Stacks.AmpleNonvanishing.isZero_of_hom_single_eq_zero` applied with `𝒯` the
class of those twists. Its hypothesis — every quasi-coherent module of finite type is a quotient
of a finite direct sum of members of `𝒯` — is clause (8) of [Stacks, Tag 01Q3] for the ample
sheaf `𝒪_X(1)`, in the form `Stacks.AlgebraicGeometry.Tag0B5QAmpleRoute`
`.exists_epi_coproduct_twistingSheaf_of_isQuotientOfNegativeTwists`;
`exists_epi_coproduct_twist_nonpos` below is that theorem with the degrees recorded as
non-positive, which is what makes the *finite* window of Koszul's `twist_neg_mem_gen` enough.

## Main definitions

* `Stacks.AlgebraicGeometry.ExampleGenerator.twistModule` — `𝒪_X(d)` read in `X.Modules`.
* `Stacks.AlgebraicGeometry.ExampleGenerator.twistSumModule` — the module `E` displayed above.
* `Stacks.AlgebraicGeometry.ExampleGenerator.twistSumQCoh` — `E` in degree zero, as an object of
  `D_QCoh(𝒪_X)`.

## Main results

* `Stacks.AlgebraicGeometry.ExampleGenerator.isFlat_twistSumModule` — `E` is a flat
  `𝒪_X`-module, being a finite direct sum of invertible ones.
* `Stacks.AlgebraicGeometry.ExampleGenerator.isWeakTriangulatedGenerator_twistSumQCoh` —
  **[Stacks, Tag 0A9V] on `D_QCoh(𝒪_X)`.**

## Implementation notes

*Two spellings of the category of `𝒪_X`-modules.* Koszul.lean works in
`SheafOfModules (projRingSheaf (polyGrading A n))`, the spelling the twisting sheaves carry,
while `Stacks.Duality.quasiCoherentDerivedCategory` is stated over `X.Modules`. The two are
equal by `Stacks.AlgebraicGeometry.ProjTrivialization.ringCatSheaf_eq`, and crossing between
them costs nothing in term position; it does, however, defeat instance search, which compares
types at reducible transparency and cannot unfold the semireducible
`AlgebraicGeometry.Scheme.Modules`. That is why `twistModule` and `twistFamily` are introduced:
they name the twisting sheaves at the `X.Modules` spelling, so that the direct sum over them
finds its `HasBiproduct` instance.

## References

* [Stacks Project, Tag 0A9V](https://stacks.math.columbia.edu/tag/0A9V)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 03EU](https://stacks.math.columbia.edu/tag/03EU)
* [Stacks Project, Tag 09SK](https://stacks.math.columbia.edu/tag/09SK)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjPolyChart
open Stacks.AlgebraicGeometry.ProjTrivialization
open Stacks.Ample
open Stacks.SheafOfModules.FlatCoproduct
open Stacks.TriangulatedGenerators

universe u

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose
attribute [local instance_reducible] ProjectiveSpectrum.top

namespace Stacks.AlgebraicGeometry.ExampleGenerator

/-! ### Flatness of a finite direct sum -/

/-- Flatness of a sheaf of modules on a scheme is invariant under isomorphism: flatness is
exactness of the tensor endofunctor, and that endofunctor is functorial in the module. -/
theorem isFlat_of_iso {X : Scheme.{u}} {M N : X.Modules} (e : M ≅ N)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) N :=
  (isFlat_iff_exactFunctor_sheafTensor.{u, u} X.sheaf N).2
    ((exactFunctor _ _).prop_of_iso
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.sheaf).flip.mapIso e)
      ((isFlat_iff_exactFunctor_sheafTensor.{u, u} X.sheaf M).1 hM))

/-- **A finite direct sum of flat sheaves of modules on a scheme is flat.** The sum is
re-indexed by a universe lift of the index type, where [Stacks, Tag 03EU] applies. -/
theorem isFlat_of_iso_biproduct {X : Scheme.{u}} {r : ℕ} (F : Fin r → X.Modules)
    (M : X.Modules) (e : M ≅ ⨁ F)
    (hF : ∀ j, AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) (F j)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M :=
  isFlat_of_iso
    (e ≪≫ biproduct.isoCoproduct F ≪≫
      Sigma.whiskerEquiv (f := F) (g := fun j : ULift.{u} (Fin r) => F j.down)
        Equiv.ulift.symm (fun j => Iso.refl (F j))).symm
    (isFlat_coproduct (O := X.sheaf) (fun j : ULift.{u} (Fin r) => F j.down)
      (fun j => hF j.down))

/-! ### The twists and their direct sum, at the scheme spelling -/

variable (A : Type u) [CommRing A] (n : ℕ)

/-- `𝒪_X(d)` on `X = P^n_A`, named at the spelling `X.Modules`. -/
def twistModule (d : ℤ) : (AlgebraicGeometry.Proj (polyGrading A n)).Modules :=
  twistingSheaf (polyGrading A n) d

/-- The family `𝒪_X, 𝒪_X(-1), …, 𝒪_X(-n)`. -/
def twistFamily : Fin (n + 1) → (AlgebraicGeometry.Proj (polyGrading A n)).Modules :=
  fun j => twistModule A n (-(j : ℤ))

/-- **The module `E = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` on `X = P^n_A`.** -/
def twistSumModule : (AlgebraicGeometry.Proj (polyGrading A n)).Modules := ⨁ twistFamily A n

/-- Each twist is invertible: a polynomial ring is generated in degree one over its degree-zero
part, and [Stacks, Tag 01MW] applies. -/
instance isInvertibleModule_twistModule (d : ℤ) :
    IsInvertibleModule (AlgebraicGeometry.Proj (polyGrading A n)) (twistModule A n d) :=
  Stacks.AlgebraicGeometry.Tag0B5QAmpleRoute.isInvertibleModule_twistingSheaf_of_adjoin_degree_one
    (polyGrading A n)
    (Stacks.ProjectiveSpace.SerreVanishing.adjoin_range_one_polyGrading A n) d

/-- Each twist is flat, being invertible. -/
theorem isFlat_twistModule (d : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (AlgebraicGeometry.Proj (polyGrading A n)).sheaf) (twistModule A n d) :=
  Stacks.AmpleNonvanishing.isFlat_of_isInvertibleModule _ (twistModule A n d)

/-- **The direct sum of the `n + 1` twists is flat.** -/
theorem isFlat_twistSumModule :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u}
      (O := (AlgebraicGeometry.Proj (polyGrading A n)).sheaf) (twistSumModule A n) :=
  isFlat_of_iso_biproduct (twistFamily A n) _ (Iso.refl _)
    (fun j => isFlat_twistModule A n (-(j : ℤ)))

/-- Each twist is quasi-coherent. -/
instance isQuasicoherent_twistModule (d : ℤ) : (twistModule A n d).IsQuasicoherent :=
  inferInstanceAs (SheafOfModules.IsQuasicoherent (R := projRingSheaf (polyGrading A n))
    (twistingSheaf (polyGrading A n) d))

/-- Each member of the displayed family is quasi-coherent. -/
instance isQuasicoherent_twistFamily (j : Fin (n + 1)) :
    (twistFamily A n j).IsQuasicoherent :=
  isQuasicoherent_twistModule A n (-(j : ℤ))

/-- **The direct sum of the `n + 1` twists is quasi-coherent**: quasi-coherent modules form a
weak Serre subcategory, hence are closed under finite direct sums. -/
instance isQuasicoherent_twistSumModule : (twistSumModule A n).IsQuasicoherent := by
  let := Stacks.ConstantSheaf.isClosedUnderFiniteCoproducts_of_isWeakSerreClass
    (SheafOfModules.isQuasicoherent (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf)
  exact (SheafOfModules.isQuasicoherent
      (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf).prop_of_iso
    (biproduct.isoCoproduct (twistFamily A n)).symm
    ((SheafOfModules.isQuasicoherent
      (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf).prop_coproduct
        (fun j => isQuasicoherent_twistFamily A n j))

/-- **`E` in degree zero is the twist sum of Koszul.lean**: the single functor is additive, so
it carries the direct sum of the twists to the direct sum of their single complexes. -/
def twistSumModuleSingleIso :
    (DerivedCategory.singleFunctor
        (AlgebraicGeometry.Proj (polyGrading A n)).Modules 0).obj (twistSumModule A n) ≅
      twistSum A n :=
  (DerivedCategory.singleFunctor
    (AlgebraicGeometry.Proj (polyGrading A n)).Modules 0).mapBiproduct (twistFamily A n)

/-- **`E` in degree zero as an object of `D_QCoh(𝒪_X)`.** The underlying object is taken to be
the twist sum of
`StacksFrontier/AlgebraicGeometry/ProjectiveSpace/ExampleGenerator/Koszul.lean` on the nose, so that
the generation step proved there can be read on it with no transport. -/
def twistSumQCoh :
    Stacks.Duality.quasiCoherentDerivedCategory (AlgebraicGeometry.Proj (polyGrading A n)) :=
  ⟨twistSum A n, by
    intro i
    exact (SheafOfModules.isQuasicoherent
        (AlgebraicGeometry.Proj (polyGrading A n)).ringCatSheaf).prop_of_iso
      ((DerivedCategory.homologyFunctor
        (AlgebraicGeometry.Proj (polyGrading A n)).Modules i).mapIso
          (twistSumModuleSingleIso A n))
      (Stacks.Duality.DerivedPushforward.derivedCategoryB_singleFunctor_obj
        (twistSumModule A n) (isQuasicoherent_twistSumModule A n) i)⟩

/-! ### Quasi-compactness, quasi-separatedness and ampleness of `P^n_A` -/

/-- `𝒪_X(1)` is ample on `X = P^n_A`. -/
theorem isAmple_twistModule_one :
    IsAmple (AlgebraicGeometry.Proj (polyGrading A n)) (twistModule A n 1) :=
  Stacks.ProjectiveSpace.isAmple_twistingSheaf_one A n

/-- `P^n_A` is quasi-compact. -/
instance compactSpace_projectiveSpace :
    CompactSpace (AlgebraicGeometry.Proj (polyGrading A n)) :=
  (isAmple_twistModule_one A n).compactSpace

/-- `P^n_A` is quasi-separated. -/
instance quasiSeparatedSpace_projectiveSpace :
    QuasiSeparatedSpace (AlgebraicGeometry.Proj (polyGrading A n)) :=
  Stacks.AmplePullbackPart1.quasiSeparatedSpace_of_isAmple (twistModule A n 1)
    (isAmple_twistModule_one A n)

/-! ### Every finite-type quasi-coherent module is a quotient of non-positive twists -/

/-- **Clause (8) of [Stacks, Tag 01Q3] on `P^n_A`, with the degrees recorded as non-positive.**
Every quasi-coherent `𝒪_X`-module of finite type is the target of an epimorphism from a finite
direct sum `⨁ⱼ 𝒪_X(dⱼ)` with every `dⱼ ≤ 0`.

This is `Stacks.AlgebraicGeometry.Tag0B5QAmpleRoute`
`.exists_epi_coproduct_twistingSheaf_of_isQuotientOfNegativeTwists`
with the ample machine invoked at the bound `n₀ = 0`, so that the degrees it produces are
non-positive; the conclusion of that theorem drops that information, and it is exactly the
information the Koszul generation step needs. -/
theorem exists_epi_coproduct_twist_nonpos
    (F : (AlgebraicGeometry.Proj (polyGrading A n)).Modules)
    (hqc : F.IsQuasicoherent) (hft : SheafOfModules.IsFiniteType.{u, u, u} F) :
    ∃ (r : ℕ) (d : Fin r → ℤ), (∀ j, d j ≤ 0) ∧
      ∃ φ : (∐ fun j : Fin r => twistModule A n (d j)) ⟶ F, Epi φ := by
  obtain ⟨T, r, d, b, hb, e, hse, hX₃, -, hd0⟩ :=
    Stacks.ProjectiveSpace.SerreVanishing.isQuotientOfNegativeTwists_twistingSheaf_one A n
      0 F hqc hft
  subst hX₃
  have hbc : b.pt ≅ ∐ fun j : Fin r =>
      tensorPowModule (AlgebraicGeometry.Proj (polyGrading A n))
        (twistingSheaf (polyGrading A n) 1) (-(d j)) :=
    hb.isColimit.coconePointUniqueUpToIso (colimit.isColimit _)
  have hre : (∐ fun j : Fin r =>
        tensorPowModule (AlgebraicGeometry.Proj (polyGrading A n))
          (twistingSheaf (polyGrading A n) 1) (-(d j))) ≅
      ∐ fun j : Fin r => twistModule A n (-(d j)) :=
    HasColimit.isoOfNatIso (Discrete.natIso fun j =>
      Stacks.AlgebraicGeometry.ProjTwistPowers.tensorPowModuleIsoTwistingSheaf
        (polyGrading A n)
        (Stacks.ProjectiveSpace.SerreVanishing.adjoin_one_polyGrading A n) (-(d j.as)))
  obtain ⟨ι⟩ : Nonempty ((∐ fun j : Fin r => twistModule A n (-(d j))) ≅ T.X₂) :=
    ⟨hre.symm.trans (hbc.symm.trans e.symm)⟩
  have hιepi : Epi ι.hom := IsIso.epi_of_iso ι.hom
  exact ⟨r, fun j => -(d j), fun j => neg_nonpos.mpr (hd0 j), ι.hom ≫ T.g,
    epi_comp' hιepi hse.epi_g⟩

/-! ### [Stacks, Tag 0A9V] on `D_QCoh` -/

/-- **[Stacks, Tag 0A9V] on `D_QCoh(𝒪_X)`.** For `X = P^n_A` the object
`E = 𝒪_X ⊕ 𝒪_X(-1) ⊕ ⋯ ⊕ 𝒪_X(-n)` in degree zero is a weak generator of `D_QCoh(𝒪_X)`.

An object `K` of `D_QCoh(𝒪_X)` receiving only zero morphisms from the shifts of `E` receives
only zero morphisms from every object of `⟨E⟩` ([Stacks, Tag 09SK]), hence from every
`𝒪_X(-m)[-p]` with `m ≥ 0` — that is the generation step
`Stacks.AlgebraicGeometry.ExampleGenerator.twist_neg_mem_gen`. Those twists are enough to force
`K = 0` by `Stacks.AmpleNonvanishing.isZero_of_hom_single_eq_zero`, whose presentation
hypothesis is `exists_epi_coproduct_twist_nonpos`. -/
@[stacks 0A9V "the generator conclusion of Definition 09SJ(3) for D_QCoh(O_X), with no \
  hypothesis beyond the tag's. The generation step on the whole of D(O_X) is \
  Stacks.AlgebraicGeometry.ExampleGenerator.twist_neg_mem_gen"]
theorem isWeakTriangulatedGenerator_twistSumQCoh :
    (ObjectProperty.singleton (twistSumQCoh A n)).IsWeakTriangulatedGenerator := by
  classical
  refine (ObjectProperty.singleton (twistSumQCoh A n)).isWeakTriangulatedGenerator_iff.mpr ?_
  intro K hK
  by_contra! hf
  have hvanish := Stacks.AmpleNonvanishing.hom_obj_eq_zero_of_hom_eq_zero
    (twistSumQCoh A n) K (fun p g => hf (twistSumQCoh A n) (by simp) p g)
  have hgen := (hom_vanishing_iff_gen (twistSumQCoh A n).obj K.obj).1 hvanish
  refine hK (Stacks.AmpleNonvanishing.isZero_of_hom_single_eq_zero
    (AlgebraicGeometry.Proj (polyGrading A n)) (twistModule A n 1)
    (isAmple_twistModule_one A n) (fun M => ∃ m : ℕ, M = twistModule A n (-(m : ℤ))) ?_ K ?_)
  · intro F hqc hft
    obtain ⟨r, d, hd, φ, hφ⟩ := exists_epi_coproduct_twist_nonpos A n F hqc hft
    refine ⟨r, fun j => twistModule A n (d j), fun j => ⟨(d j).natAbs, ?_⟩, φ, hφ⟩
    have hdj : -((d j).natAbs : ℤ) = d j := by have := hd j; omega
    rw [hdj]
  · rintro M ⟨m, rfl⟩ p f
    refine hgen _ ?_ f
    refine mem_gen_of_iso
      (((DerivedCategory.singleFunctors
          (AlgebraicGeometry.Proj (polyGrading A n)).Modules).shiftIso (-p) p 0
        (by ring)).app (twistModule A n (-(m : ℤ)))) ?_
    exact shift_mem_gen_of_mem (-p) (twist_neg_mem_gen A n m)

end Stacks.AlgebraicGeometry.ExampleGenerator

end
