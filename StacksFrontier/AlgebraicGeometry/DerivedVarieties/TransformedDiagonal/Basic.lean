module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.QuasiCoherentDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImage.QuasiCoherentPullback
public import StacksFrontier.AlgebraicGeometry.Perfect.DiagonalResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Defs

/-!
# Transforming a resolution of the diagonal by a functor on perfect complexes

Let `X` and `Y` be schemes over `Spec A` and let

`… → ℰ₁ ⊠ 𝒢₁ → ℰ₀ ⊠ 𝒢₀ → 𝒪_Δ → 0`

be a resolution of the structure sheaf of the diagonal of `X` whose positive-degree terms are
external tensor products of finite locally free modules. Given a functor
`F : D_perf(𝒪_X) ⥤ D_perf(𝒪_Y)`, replacing each second factor `𝒢ᵢ` by `F(𝒢ᵢ)` gives the complex

`… → ℰ₂ ⊠ F(𝒢₂) → ℰ₁ ⊠ F(𝒢₁) → ℰ₀ ⊠ F(𝒢₀)`

on `X ×_A Y`, where `⊠` is now the derived external tensor product. Its differentials are those
of the resolution, read through the identification of Hom groups that the Künneth formula and the
full faithfulness of `F` provide.

## Main definitions

* `AlgebraicGeometry.derivedExternalTensor`: the derived external tensor product
  `K ⊠ L = Lpr₁^* K ⊗^𝐋 Lpr₂^* L` of `K ∈ D(𝒪_X)` and `L ∈ D(𝒪_Y)`, an object of `D(𝒪_{X ×_S Y})`.
* `AlgebraicGeometry.perfectDerived`: the strictly full subcategory `D_perf(𝒪_X)` of perfect
  objects of the locally small derived category of `𝒪_X`-modules.
* `AlgebraicGeometry.DiagonalResolution.boxTerm` and
  `AlgebraicGeometry.DiagonalResolution.boxDifferential`: the terms `ℰᵢ ⊠ 𝒢ᵢ` of a resolution of
  the diagonal and the differentials between them.
* `AlgebraicGeometry.DiagonalResolution.transformedTerm`: the term `ℰᵢ ⊠ F(𝒢ᵢ)`.
* `AlgebraicGeometry.DiagonalResolution.HomTransport`: an identification, functorial in the index,
  of the Hom groups between the terms `ℰᵢ ⊠ 𝒢ᵢ` with those between the terms `ℰᵢ ⊠ F(𝒢ᵢ)`.
* `AlgebraicGeometry.DiagonalResolution.HomTransport.complex`: the complex
  `… → ℰ₂ ⊠ F(𝒢₂) → ℰ₁ ⊠ F(𝒢₁) → ℰ₀ ⊠ F(𝒢₀)`.

## Main results

* `AlgebraicGeometry.DiagonalResolution.boxDifferential_comp`: two consecutive differentials of a
  resolution of the diagonal compose to zero on the external tensor products.
* `AlgebraicGeometry.DiagonalResolution.HomTransport.complex_d`: the differentials of the
  transformed complex are the transported differentials of the resolution.

## Implementation notes

The terms are indexed from zero, so the term with index `i` transforms the degree `i + 1` term of
the augmented resolution; degree zero of that resolution carries `𝒪_Δ` and plays no part here.

Everything is at the locally small derived category of `𝒪_X`-modules, the model at which
`Stacks.Duality.derivedPullback` and `Stacks.Duality.derivedTensor` are available for schemes.
Accordingly `perfectDerived` repeats the full subcategory of perfect objects at that model;
it uses the perfectness predicate `Stacks.Cohomology.PerfectComplexes.IsPerfect` of
`Stacks.Perfect.BoundedLocallyFreeComplexes.PerfectDerivedCategory`, which is itself pinned to
`CategoryTheory.HasDerivedCategory.standard` and so describes a different derived category.

The Künneth formula identifies `Hom(ℰᵢ ⊠ 𝒢ᵢ, ℰⱼ ⊠ 𝒢ⱼ)` with
`Hom(ℰᵢ, ℰⱼ) ⊗ Hom(𝒢ᵢ, 𝒢ⱼ)`, and likewise for the transformed terms; full faithfulness of `F`
identifies the second tensor factors. The composite identification is the data of a
`HomTransport`, whose compatibility with identities and composition is what makes the
transported differentials into a complex.

## References

* [Stacks Project, Tag 0G0A](https://stacks.math.columbia.edu/tag/0G0A)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Cohomology.PerfectComplexes

universe u

namespace AlgebraicGeometry

/-! ### The derived external tensor product -/

/-- The derived external tensor product `K ⊠ L` of an object of `D(𝒪_X)` and an object of
`D(𝒪_Y)`, for `X` and `Y` schemes over `S`: the derived tensor product on `X ×_S Y` of the
derived pullbacks of `K` and `L` along the two projections. -/
@[sga "6 III 1.6"]
def derivedExternalTensor {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (K : DerivedCategory X.Modules) (L : DerivedCategory Y.Modules) :
    DerivedCategory (pullback f g).Modules :=
  ((Stacks.Duality.derivedTensor (pullback f g)).obj
      ((Stacks.Duality.derivedPullback (pullback.fst f g)).obj K)).obj
    ((Stacks.Duality.derivedPullback (pullback.snd f g)).obj L)

/-- `D_perf(𝒪_X)`, the strictly full subcategory of the derived category of `𝒪_X`-modules whose
objects are the perfect ones. -/
abbrev perfectDerived (X : Scheme.{u}) :=
  ObjectProperty.FullSubcategory
    (fun K : DerivedCategory X.Modules => IsPerfect (X := X.toRingedSpace) K)

namespace DiagonalResolution

variable {A : Type u} [CommRing A] {X Y : Scheme.{u}} {f : X ⟶ Spec (.of A)}

/-! ### The external tensor products of a resolution of the diagonal -/

/-- The external tensor product `ℰᵢ ⊠ 𝒢ᵢ` of the two `i`-th factors of a resolution of the
diagonal, a module on `X ×_A X`. -/
abbrev boxTerm (R : DiagonalResolution f) (i : ℕ) : (pullback f f).Modules :=
  externalTensorProduct f f (R.left i) (R.right i)

/-- The differential `ℰᵢ₊₁ ⊠ 𝒢ᵢ₊₁ ⟶ ℰᵢ ⊠ 𝒢ᵢ` of a resolution of the diagonal, read through the
identifications of its terms with external tensor products. -/
def boxDifferential (R : DiagonalResolution f) (i : ℕ) : R.boxTerm (i + 1) ⟶ R.boxTerm i :=
  (R.termIso (i + 1)).inv ≫ R.complex.d (i + 2) (i + 1) ≫ (R.termIso i).hom

/-- Two consecutive differentials of a resolution of the diagonal compose to zero. -/
theorem boxDifferential_comp (R : DiagonalResolution f) (i : ℕ) :
    R.boxDifferential (i + 1) ≫ R.boxDifferential i = 0 := by
  rw [boxDifferential, boxDifferential, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc,
    R.complex.d_comp_d_assoc, zero_comp, comp_zero]

/-! ### The transformed complex -/

variable (R : DiagonalResolution f) (g : Y ⟶ Spec (.of A))
  (F : perfectDerived X ⥤ perfectDerived Y)

/-- The term `ℰᵢ ⊠ F(𝒢ᵢ)`: the derived external tensor product, on `X ×_A Y`, of the `i`-th first
factor of a resolution of the diagonal with the value of `F` at the `i`-th second factor. -/
@[stacks 0G0A "the terms of the complex"]
def transformedTerm (hG : ∀ i, IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj (R.right i))) (i : ℕ) :
    DerivedCategory (pullback f g).Modules :=
  derivedExternalTensor f g ((DerivedCategory.singleFunctor X.Modules 0).obj (R.left i))
    (F.obj ⟨(DerivedCategory.singleFunctor X.Modules 0).obj (R.right i), hG i⟩).obj

/-- An identification of the Hom groups between the terms `ℰᵢ ⊠ 𝒢ᵢ` of a resolution of the
diagonal with the Hom groups between the terms `ℰᵢ ⊠ F(𝒢ᵢ)`, compatible with identities and with
composition. This is the composite of the Künneth identifications of both sides with the
identification of `Hom(𝒢ᵢ, 𝒢ⱼ)` with `Hom(F(𝒢ᵢ), F(𝒢ⱼ))` given by full faithfulness of `F`. -/
structure HomTransport (hG : ∀ i, IsPerfect (X := X.toRingedSpace)
    ((DerivedCategory.singleFunctor X.Modules 0).obj (R.right i))) where
  /-- The identification of Hom groups. -/
  hom (i j : ℕ) : (R.boxTerm i ⟶ R.boxTerm j) ≃+
    (R.transformedTerm g F hG i ⟶ R.transformedTerm g F hG j)
  /-- The identification carries identities to identities. -/
  hom_id (i : ℕ) : hom i i (𝟙 _) = 𝟙 _
  /-- The identification is compatible with composition. -/
  hom_comp (i j l : ℕ) (a : R.boxTerm i ⟶ R.boxTerm j) (b : R.boxTerm j ⟶ R.boxTerm l) :
    hom i l (a ≫ b) = hom i j a ≫ hom j l b

namespace HomTransport

variable {R g F} {hG : ∀ i, IsPerfect (X := X.toRingedSpace)
    ((DerivedCategory.singleFunctor X.Modules 0).obj (R.right i))}

/-- The complex `… → ℰ₂ ⊠ F(𝒢₂) → ℰ₁ ⊠ F(𝒢₁) → ℰ₀ ⊠ F(𝒢₀)` on `X ×_A Y` obtained from a
resolution of the diagonal of `X` by transforming its second factors by `F`. Its differentials
are those of the resolution, transported along the given identification of Hom groups. -/
@[stacks 0G0A "the complex"]
def complex (T : HomTransport R g F hG) :
    ChainComplex (DerivedCategory (pullback f g).Modules) ℕ :=
  ChainComplex.of (R.transformedTerm g F hG) (fun i => T.hom (i + 1) i (R.boxDifferential i))
    fun i => by rw [← T.hom_comp, R.boxDifferential_comp, map_zero]

/-- The term of index `i` of the transformed complex is `ℰᵢ ⊠ F(𝒢ᵢ)`. -/
@[simp]
theorem complex_X (T : HomTransport R g F hG) (i : ℕ) :
    T.complex.X i = R.transformedTerm g F hG i :=
  rfl

/-- The differential of the transformed complex from index `i + 1` to index `i` is the
differential `ℰᵢ₊₁ ⊠ 𝒢ᵢ₊₁ ⟶ ℰᵢ ⊠ 𝒢ᵢ` of the resolution of the diagonal, transported along the
identification of Hom groups. -/
@[stacks 0G0A "the differentials of the complex"]
theorem complex_d (T : HomTransport R g F hG) (i : ℕ) :
    T.complex.d (i + 1) i = T.hom (i + 1) i (R.boxDifferential i) := by
  simp [complex]

end HomTransport

end DiagonalResolution

end AlgebraicGeometry

end
