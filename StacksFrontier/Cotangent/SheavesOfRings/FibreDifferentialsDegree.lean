module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsAlongIso
public import StacksFrontier.Cotangent.SheavesOfRings.FibreDifferentials
import StacksCore.Tactic.StacksAttribute

/-!
# The first term of the sequence of principal parts in the fibre, read over `P_n`

Let `C` be a small site, let `f : 𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative rings on it,
let `ℱ` be a sheaf of `ℬ`-modules and let `P_•` be the standard resolution of `ℬ` over `𝒜`, read
on `Δ × C` as the sheaf of commutative rings `𝒫` over `π^{-1}𝒜`.
`CategoryTheory.Sheaf.fibrePrincipalPartsX₁Iso` restricts the first term
`Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ` of the sequence of principal parts to the fibre over a simplicial degree
`n`, but leaves the answer over `i_n^{-1}𝒫`.  This file reads it over `P_n`:

`i_n^{-1}(Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ) ≅ Ω_{P_n/𝒜} ⊗_{P_n} i_n^{-1}ℱ`,

both sides read over `P_n` through the isomorphism `i_n^{-1}𝒫 ≅ P_n` of
`CategoryTheory.Sheaf.fibreResolutionIso`.

## What was owed, and what supplies it

The module documentation of `StacksFrontier/Cotangent/SheavesOfRings/FibreDifferentials.lean` records
exactly what this needed:

> What is still owed to read `CategoryTheory.Sheaf.fibrePrincipalPartsX₁Iso` entirely over `P_n`
> is the transport of a tensor product along the isomorphism `i_n^{-1}𝒫 ≅ P_n` of sheaves of
> commutative rings — the analogue for `⊗` of the transport
> `AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso` performs for derivations.

That transport is now
`Stacks.SheafOfModules.TensorTransitivity.tensorRestrictScalarsAlongIsoIso`, proved as the case
`L = ρ_*M` of the unconditional transitivity
`Stacks.SheafOfModules.TensorTransitivity.tensorRestrictScalarsTransitivityIso` with the counit
`ρ^*ρ_*M ≅ M` substituted; the counit is invertible because restriction of scalars along an
isomorphism of sheaves of rings is fully faithful.  So this file is the composite of three
isomorphisms already in the tree and builds no new comparison of its own.

## Main definitions

* `CategoryTheory.Sheaf.fibrePrincipalPartsX₁DegreeIso`:
  **`i_n^{-1}(Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ) ≅ Ω_{P_n/𝒜} ⊗_{P_n} i_n^{-1}ℱ` over `P_n`.**

## What this is not

No `@[stacks]` attribute is taken.  Tag 09DG asserts the short exactness of the whole sequence in
the fibre; only its first term is treated here, as in
`StacksFrontier/Cotangent/SheavesOfRings/FibreDifferentials.lean`.  Nor is this the first-term
identification `e₁` of [Stacks, Tag 09DH]: that one is about the whole simplicial object, not one
degree, and assembling the degrees here would be naturality in `n` of the isomorphism above,
which this file does not prove. The *objects* do carry their simplicial structure — at `π^{-1}O`
the two spellings of restriction to the fibre are one functor
(`Stacks.SimplicialModules.restrictedModules_fibreInclusion_eq_fibreRestrictionMod`) — but the
comparisons do not: `Stacks.Sheaves.Differentials.restrictedSheafTensorRightIso` and
`restrictedDifferentialsOfSiteIso` rest on
`Stacks.SheafOfModules.PushforwardSheafification.pushforwardSheafifyIso`, which is made natural
in the presheaf and not in the functor of sites, and the `*_naturality` lemmas around
`CategoryTheory.Sheaf.fibreResolutionIso` are naturality in the *ring object* with `n` a fixed
parameter.

`e₁` is proved — `CategoryTheory.Sheaf.nonempty_resolutionAtiyahTriangleFirstTermIso`
(`StacksFrontier/Cotangent/SheavesOfRings/AtiyahTriangleFirstTerm.lean`) — and it does **not** go
through this degreewise statement nor through any assembly of fibrewise comparisons: the
identification is written once on `Δ × C`, by the universal property of
`CategoryTheory.Sheaf.CotangentSimplicialModuleData` and by local bijectivity for the
sheafification step. So this file is the record of the same mathematics in one degree, and the
naturality it leaves open is not owed by anything.

## References

* [Stacks Project, Tag 09DG](https://stacks.math.columbia.edu/tag/09DG), the sequence of
  principal parts of the standard resolution, whose fibre over `n` is the sequence for `𝒜 ⟶ P_n`.
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), the extension of
  scalars whose counit makes the transport along `i_n^{-1}𝒫 ≅ P_n` invertible.
* [Stacks Project, Tag 03D1](https://stacks.math.columbia.edu/tag/03D1), the tensor product of
  sheaves of modules, which is what is transported.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite
open AlgebraicGeometry.SheafOfModules (moduleOfDifferentialsOfSite)
open Stacks.Sheaves.Differentials (restrictedCommRing restrictedModules)
open Stacks.SheafOfModules.TensorTransitivity (sheafTensorRightFactorIso
  sheafTensorRightRestrictScalarsIso)
open Stacks.SimplicialModules (projectionTopology fibreInclusion projection)

attribute [local instance_reducible] CategoryTheory.sheafCompose

universe u

namespace CategoryTheory.Sheaf

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B) (n : SimplexCategory)

/-- The isomorphism `P_n ≅ i_n^{-1}𝒫` of the *sheaves of rings* underlying
`CategoryTheory.Sheaf.fibreResolutionIso`, which is what restriction of scalars is taken along
and what makes the transport of the tensor product available. -/
instance isIso_forgetCommRingSheaf_map_fibreResolutionIso_inv :
    IsIso ((Stacks.forgetCommRingSheaf J).map (fibreResolutionIso J f n).inv) :=
  inferInstanceAs (IsIso ((Stacks.forgetCommRingSheaf J).mapIso
    (fibreResolutionIso J f n).symm).hom)

/-- **`i_n^{-1}(Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ) ≅ Ω_{P_n/𝒜} ⊗_{P_n} i_n^{-1}ℱ`, over `P_n`.**  The first
term of the sequence of principal parts of `𝒫` over `π^{-1}𝒜`, restricted to the fibre over a
simplicial degree `n` and read over the degree-`n` term `P_n` of the standard resolution, is the
sheaf of relative differentials of `𝒜 ⟶ P_n` tensored with the restricted coefficient module.

The three steps are `CategoryTheory.Sheaf.fibrePrincipalPartsX₁Iso` (restriction to the fibre
commutes with the sheafification in the tensor product),
`Stacks.SheafOfModules.TensorTransitivity.sheafTensorRightRestrictScalarsIso` (restriction of
scalars along `i_n^{-1}𝒫 ≅ P_n` commutes with the tensor product) and
`CategoryTheory.Sheaf.fibreDifferentialsIso` (the differentials factor is `Ω_{P_n/𝒜}`), the last
carried through the tensor product by
`Stacks.SheafOfModules.TensorTransitivity.sheafTensorRightFactorIso`. -/
def fibrePrincipalPartsX₁DegreeIso (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (fibreRestrictScalars J f n).obj
        ((restrictedModules J (fibreInclusion C n) (O₂ := simplicialResolution J f)).obj
          ((((Stacks.SheafOfModules.Tensor.sheafTensor (simplicialResolution J f)).flip.obj
            (moduleOfDifferentialsOfSite.{u, u, u, u} (simplicialBase J (A := A))
              (simplicialResolution J f) (simplicialBaseMap J f)))).obj
                (simplicialCoefficients J f F))) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor ((resolutionCommRing J f).obj (op n))).flip.obj
          (resolutionDegreeDifferentials J f n))).obj
        ((fibreRestrictScalars J f n).obj
          ((restrictedModules J (fibreInclusion C n) (O₂ := simplicialResolution J f)).obj
            (simplicialCoefficients J f F))) :=
  (fibreRestrictScalars J f n).mapIso (fibrePrincipalPartsX₁Iso J f n F) ≪≫
    (sheafTensorRightRestrictScalarsIso J (fibreResolutionIso J f n).inv
        (fibreDifferentials J f n)
        ((restrictedModules J (fibreInclusion C n) (O₂ := simplicialResolution J f)).obj
          (simplicialCoefficients J f F))).symm ≪≫
    sheafTensorRightFactorIso J ((resolutionCommRing J f).obj (op n))
      ((fibreRestrictScalars J f n).obj
        ((restrictedModules J (fibreInclusion C n) (O₂ := simplicialResolution J f)).obj
          (simplicialCoefficients J f F)))
      (fibreDifferentialsIso J f n)

end CategoryTheory.Sheaf

end
