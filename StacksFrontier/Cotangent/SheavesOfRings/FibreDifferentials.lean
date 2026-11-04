module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPoint
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Simplicial.FibreInclusion
public import StacksFrontier.CategoryTheory.Sites.Modules.DifferentialsRestriction
public import StacksFrontier.CategoryTheory.Sites.Modules.Localization.Differentials
public import StacksFrontier.Cotangent.SheavesOfRings.AtiyahTriangle
import StacksCore.Tactic.StacksAttribute

/-!
# `Ω_{𝒫/π^{-1}𝒜}` restricted to the fibre over a simplicial degree is `Ω_{P_n/𝒜}`

Let `C` be a small site, let `f : 𝒜 ⟶ ℬ` be a homomorphism of sheaves of commutative rings on
it and let `P_•` be the standard resolution of `ℬ` over `𝒜` of Section 08UQ, read on `Δ × C` as
the sheaf of commutative rings `𝒫 = `
`CategoryTheory.Sheaf.simplicialResolution` over `π^{-1}𝒜 = CategoryTheory.Sheaf.simplicialBase`.
This file proves that restricting the sheaf of relative differentials `Ω_{𝒫/π^{-1}𝒜}` on `Δ × C`
to the fibre `{n} × C` gives the sheaf of relative differentials of the ring map `𝒜 ⟶ P_n`:

`i_n^{-1}Ω_{𝒫/π^{-1}𝒜} ≅ Ω_{P_n/𝒜}`,

by the unique identification carrying one universal derivation to the other.

This is the statement the module docstring of
`StacksFrontier/Cotangent/SheavesOfRings/AtiyahTriangle.lean` flags as owed, in the note on
`CategoryTheory.Sheaf.simplicialPrincipalPartsShortComplex_X₁`:

> This identifies the term on `Δ × C`. It does *not* say that the restriction of
> `Ω_{𝒫/π^{-1}𝒜}` to the fibre over a simplicial degree `n` is `Ω_{P_n/𝒜}`: the sheaf of
> differentials is a sheafification, so that comparison needs restriction to the fibre to commute
> with it, and it is not proved here.

That commutation is `Stacks.Sheaves.Differentials.restrictedDifferentialsOfSiteIso`, for an
arbitrary continuous and cocontinuous functor of small sites; the fibre inclusion
`i_n : C ⥤ Δ × C` is both (`Stacks.SimplicialModules.isContinuous_fibreInclusion` and
`isCocontinuous_fibreInclusion`), so it applies here, and what is left is to identify the
restricted sheaves of commutative rings with the degree-`n` terms.

## The restriction of scalars in the statement, and why it is there

`i_n^{-1}𝒫` and `P_n` have the same sections and the same ring operations, but they are not the
same sheaf of commutative rings: `𝒫` is the uncurrying of `P_•`, so its restriction map along
`(𝟙 n, g)` carries the factor `P_•(𝟙_n)`, which is the identity only by `P_•.map_id` and not on
the nose. `Stacks.SimplicialModules.fibreCommRingIso` is the resulting isomorphism, the identity
on every section, and the two categories of modules it relates are identified by restriction of
scalars along it. The statement therefore reads

`(restriction of scalars along `i_n^{-1}𝒫 ≅ P_n`) (i_n^{-1}Ω_{𝒫/π^{-1}𝒜}) ≅ Ω_{P_n/𝒜}`,

which is the shape `AlgebraicGeometry.SheafOfModules.mapDifferentials` and
`AlgebraicGeometry.SheafOfModules.overDifferentialsIso` already use for comparisons of sheaves of
differentials over two different spellings of one sheaf of rings. Restriction of scalars along an
isomorphism does not change the underlying abelian sheaf
(`Stacks.Sheaves.RingedPoint.restrictScalarsCompToSheaf` is `Iso.refl`), so nothing is lost.

## Main definitions

* `Stacks.SimplicialModules.fibreCommRingIso`: the restriction along `i_n` of the sheaf of
  commutative rings on `Δ × C` of a simplicial sheaf of commutative rings is its degree-`n` term.
* `CategoryTheory.Sheaf.fibreDifferentialsCorepresentableBy`: the restriction of
  `Ω_{𝒫/π^{-1}𝒜}` to the fibre over `n` corepresents the `𝒜`-derivations of `P_n`.

## Main results

* `Stacks.SimplicialModules.fibreCommRingIso_naturality`: that identification is natural in the
  simplicial sheaf of commutative rings, which is what makes the square relating
  `i_n^{-1}(π^{-1}𝒜 ⟶ 𝒫)` to `𝒜 ⟶ P_n` commute.
* `CategoryTheory.Sheaf.fibreDifferentialsIso`: **`i_n^{-1}Ω_{𝒫/π^{-1}𝒜} ≅ Ω_{P_n/𝒜}`.**
* `CategoryTheory.Sheaf.fibrePrincipalPartsX₁Iso`: the first term of the sequence of principal
  parts, `Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ`, restricted to the fibre over `n`, is the restriction of
  `Ω_{𝒫/π^{-1}𝒜}` tensored with the restriction of the coefficient module — the tensor product
  being a sheafification too, and commuting with restriction to the fibre for the same reason.
  `CategoryTheory.Sheaf.restrictedModules_obj_principalPartsX₁` is the identification of its
  source with `i_n^{-1}` of that term.
* `CategoryTheory.Sheaf.homEquiv_fibreDifferentialsIso_hom`: it is the identification carrying
  the restricted universal derivation to the universal derivation of `Ω_{P_n/𝒜}`, so it is *the*
  comparison and not merely some isomorphism of the two sheaves.

## What this is not

No `@[stacks 09DH]` is claimed, and no `@[stacks 09DG]` either: what Tag 09DG asserts is the
short exactness of the whole sequence in the fibre, and only its first term is treated here.

Reading `CategoryTheory.Sheaf.fibrePrincipalPartsX₁Iso` entirely over `P_n` needs the transport
of a tensor product along the isomorphism `i_n^{-1}𝒫 ≅ P_n` of sheaves of commutative rings —
the analogue for `⊗` of the transport
`AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso` performs for derivations, which
is what carries `CategoryTheory.Sheaf.fibreDifferentialsIso` over. It is not proved here, but it
**is** proved: it is
`Stacks.SheafOfModules.TensorTransitivity.tensorRestrictScalarsAlongIsoIso`
(`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/TensorRestrictScalarsAlongIso.lean`), a corollary
of the unconditional transitivity
`Stacks.SheafOfModules.TensorTransitivity.tensorRestrictScalarsTransitivityIso` at its arbitrary
first factor `ρ_*M`, where what is left is the counit `ρ^*ρ_*M ≅ M` and that is invertible
because restriction of scalars along an isomorphism of sheaves of rings is fully faithful. The
term of this file read over `P_n` is
`CategoryTheory.Sheaf.fibrePrincipalPartsX₁DegreeIso`
(`StacksFrontier/Cotangent/SheavesOfRings/FibreDifferentialsDegree.lean`).

This is one of the two statements the Atiyah-triangle file lists
as separating `CategoryTheory.Sheaf.derivedLowerShriekSimplicialDifferentialsIso` — the 09CY form
of the first term, `Lπ_!(Ω_{P_•/𝒜} ⊗_{P_•} ℱ) ≅ L_{ℬ/𝒜} ⊗^𝐋_ℬ ℱ` — from the 09D3 form the
triangle needs. It is the one that identifies the *fibrewise reading* of the term on `Δ × C` with
the simplicial module `Ω_{P_•/𝒜}` used there. The other, that the derived base change along the
augmentation may be dropped (Tag 09D2 at module coefficients), is not touched here.

## References

* [Stacks Project, Tag 09DH](https://stacks.math.columbia.edu/tag/09DH), the Atiyah triangle,
  whose first term this is about.
* [Stacks Project, Tag 09DG](https://stacks.math.columbia.edu/tag/09DG), the sequence of
  principal parts of the standard resolution, whose fibre over `n` is the sequence for `𝒜 ⟶ P_n`.
* [Stacks Project, Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), the corepresentability
  of relative derivations, which pins the comparison down.
* [Stacks Project, Tag 04BO](https://stacks.math.columbia.edu/tag/04BO), the same statement for
  restriction to a slice site, whose proof this one follows.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry.SheafOfModules (derivationsFunctor moduleOfDifferentialsOfSite
  universalDerivationOfSite corepresentableByIso derivationEquivOfRingDataIso)

open Stacks.Sheaves.Differentials (restrictedCommRing restrictedCommRingMap restrictedModules
  restrictedDifferentialsOfSiteCorepresentableBy restrictedDifferentialsOfSiteIso
  restrictedSheafTensorRightIso)
open Stacks.Sheaves.RingedPoint (sheafRestrictScalarsCompIsoId)
open Stacks.SimplicialModules (projectionTopology simplicialCommRingSheaf
  simplicialCommRingSheafMap associatedCommRingPresheaf fibreInclusion projection)

attribute [local instance_reducible] CategoryTheory.sheafCompose

universe u

namespace Stacks.SimplicialModules

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)

/-- **The restriction to the fibre over `n` of the sheaf of commutative rings of a simplicial
sheaf of commutative rings is its degree-`n` term.** Both have `A_n(U)` as sections over `U`; the
uncurried presheaf inserts the factor `A_•(𝟙_n)` into its restriction maps, so the comparison is
the identity on every section but not an equality of sheaves.

These are the components of the isomorphism built inside the proof of
`Stacks.SimplicialModules.isSheaf_associatedCommRingPresheaf`, which is where the sheaf condition
on `Δ × C` is checked fibre by fibre. -/
def fibreCommRingIso (A : SimplicialObject (Sheaf J CommRingCat.{u})) (n : SimplexCategory) :
    restrictedCommRing J (fibreInclusion C n) (simplicialCommRingSheaf J A) ≅ A.obj (op n) :=
  (fullyFaithfulSheafToPresheaf _ _).preimageIso
    (NatIso.ofComponents (fun _ => Iso.refl _) (by
      intro X Y g
      change ((A.map (𝟙 (op n))).hom.app X ≫ (A.obj (op n)).obj.map g) ≫ 𝟙 _ =
        𝟙 _ ≫ (A.obj (op n)).obj.map g
      rw [A.map_id]
      simp))

/-- The identification of the fibre over `n` with the degree-`n` term is **natural in the
simplicial sheaf of commutative rings**. -/
theorem fibreCommRingIso_naturality {A B : SimplicialObject (Sheaf J CommRingCat.{u})}
    (φ : A ⟶ B) (n : SimplexCategory) :
    restrictedCommRingMap J (fibreInclusion C n) (simplicialCommRingSheafMap J φ) ≫
        (fibreCommRingIso J B n).hom =
      (fibreCommRingIso J A n).hom ≫ φ.app (op n) :=
  Sheaf.hom_ext (NatTrans.ext (funext fun _ =>
    (Category.comp_id _).trans (Category.id_comp _).symm))

end Stacks.SimplicialModules

namespace CategoryTheory.Sheaf

variable {C : Type u} [SmallCategory C] (J : GrothendieckTopology C)
  [(projection C).IsCocontinuous (projectionTopology C J) J]
  [Stacks.Sites.PreservesCoveringPullbacks (projectionTopology C J) (projection C)]
  {A B : Sheaf J CommRingCat.{u}} (f : A ⟶ B) (n : SimplexCategory)

/-- `Ω_{P_n/𝒜}`, the sheaf of relative differentials of the degree-`n` term of the standard
resolution over `𝒜`, in the corepresenting-object spelling the sequence of principal parts uses.
-/
abbrev resolutionDegreeDifferentials :
    SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((resolutionCommRing J f).obj (op n))) :=
  moduleOfDifferentialsOfSite.{u, u, u, u} A ((resolutionCommRing J f).obj (op n))
    ((resolutionCommBase J f).app (op n))

/-- The isomorphism `i_n^{-1}𝒫 ≅ P_n` of sheaves of commutative rings. -/
abbrev fibreResolutionIso :
    restrictedCommRing J (fibreInclusion C n) (simplicialResolution J f) ≅
      (resolutionCommRing J f).obj (op n) :=
  Stacks.SimplicialModules.fibreCommRingIso J (resolutionCommRing J f) n

/-- The isomorphism `i_n^{-1}(π^{-1}𝒜) ≅ 𝒜` of sheaves of commutative rings: the fibre of a
constant simplicial sheaf of commutative rings is that sheaf. -/
abbrev fibreBaseIso :
    restrictedCommRing J (fibreInclusion C n) (simplicialBase J (A := A)) ≅ A :=
  Stacks.SimplicialModules.fibreCommRingIso J ((Functor.const SimplexCategoryᵒᵖ).obj A) n

/-- The square identifying `i_n^{-1}(π^{-1}𝒜 ⟶ 𝒫)` with `𝒜 ⟶ P_n` commutes: it is the
naturality of `Stacks.SimplicialModules.fibreCommRingIso` at the structure maps
`CategoryTheory.Sheaf.resolutionCommBase`. -/
theorem fibreResolutionIso_naturality :
    restrictedCommRingMap J (fibreInclusion C n) (simplicialBaseMap J f) ≫
        (fibreResolutionIso J f n).hom =
      (fibreBaseIso J (A := A) n).hom ≫ (resolutionCommBase J f).app (op n) :=
  Stacks.SimplicialModules.fibreCommRingIso_naturality J (resolutionCommBase J f) n

/-- Restriction of scalars along `i_n^{-1}𝒫 ≅ P_n`, reading a sheaf of `i_n^{-1}𝒫`-modules as a
sheaf of `P_n`-modules. -/
abbrev fibreRestrictScalars :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J (fibreInclusion C n)
          (simplicialResolution J f))) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((resolutionCommRing J f).obj (op n))) :=
  SheafOfModules.restrictScalars
    ((Stacks.forgetCommRingSheaf J).map (fibreResolutionIso J f n).inv)

/-- Restriction of scalars in the other direction, along the inverse isomorphism. -/
abbrev fibreRestrictScalarsInv :
    SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((resolutionCommRing J f).obj (op n))) ⥤
      SheafOfModules.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (restrictedCommRing J (fibreInclusion C n)
          (simplicialResolution J f))) :=
  SheafOfModules.restrictScalars
    ((Stacks.forgetCommRingSheaf J).map (fibreResolutionIso J f n).hom)

/-- **The `𝒜`-derivations of `P_n` are the `i_n^{-1}(π^{-1}𝒜)`-derivations of `i_n^{-1}𝒫`**,
naturally in the coefficient sheaf of modules: the two notions of derivation are matched by
composing with the sections of `Stacks.SimplicialModules.fibreCommRingIso`, which is
`AlgebraicGeometry.SheafOfModules.derivationEquivOfRingDataIso` at the square
`CategoryTheory.Sheaf.fibreResolutionIso_naturality`. -/
def fibreDerivationsFunctorIso :
    fibreRestrictScalarsInv J f n ⋙ derivationsFunctor.{u}
          (restrictedCommRing J (fibreInclusion C n) (simplicialBase J (A := A)))
          (restrictedCommRing J (fibreInclusion C n) (simplicialResolution J f))
          (restrictedCommRingMap J (fibreInclusion C n) (simplicialBaseMap J f)) ≅
      derivationsFunctor.{u} A ((resolutionCommRing J f).obj (op n))
        ((resolutionCommBase J f).app (op n)) :=
  NatIso.ofComponents
    (fun M => (derivationEquivOfRingDataIso (fibreBaseIso J (A := A) n)
      (fibreResolutionIso J f n) (fibreResolutionIso_naturality J f n) M).toIso)
    (fun _ => rfl)

/-- `i_n^{-1}Ω_{𝒫/π^{-1}𝒜}`, the sheaf of relative differentials of `𝒫` over `π^{-1}𝒜` on
`Δ × C` restricted to the fibre over the simplicial degree `n`. This is the first term of the
sequence of principal parts of `CategoryTheory.Sheaf.simplicialPrincipalParts`, read in the
fibre. -/
abbrev fibreDifferentials :
    SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (restrictedCommRing J (fibreInclusion C n) (simplicialResolution J f))) :=
  (restrictedModules J (fibreInclusion C n) (O₂ := simplicialResolution J f)).obj
    (moduleOfDifferentialsOfSite.{u, u, u, u} (simplicialBase J (A := A))
      (simplicialResolution J f) (simplicialBaseMap J f))

/-- Reading `i_n^{-1}Ω_{𝒫/π^{-1}𝒜}` over `P_n` and back over `i_n^{-1}𝒫` returns it. -/
def fibreRestrictScalarsRoundTrip :
    (fibreRestrictScalarsInv J f n).obj ((fibreRestrictScalars J f n).obj
        (fibreDifferentials J f n)) ≅
      fibreDifferentials J f n :=
  (sheafRestrictScalarsCompIsoId
    ((Stacks.forgetCommRingSheaf J).map (fibreResolutionIso J f n).inv)
    ((Stacks.forgetCommRingSheaf J).map (fibreResolutionIso J f n).hom)
    (by rw [← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id])).app
      (fibreDifferentials J f n)

/-- Restriction of scalars along `i_n^{-1}𝒫 ≅ P_n` is fully faithful, being restriction of
scalars along an isomorphism of sheaves of rings. -/
def fullyFaithfulFibreRestrictScalarsInv :
    (fibreRestrictScalarsInv J f n).FullyFaithful :=
  have : IsIso ((Stacks.forgetCommRingSheaf J).map (fibreResolutionIso J f n).hom) :=
    inferInstanceAs (IsIso ((Stacks.forgetCommRingSheaf J).mapIso
      (fibreResolutionIso J f n)).hom)
  SheafOfModules.fullyFaithfulRestrictScalarsOfIsIso
    ((Stacks.forgetCommRingSheaf J).map (fibreResolutionIso J f n).hom)

/-- **The restriction of `Ω_{𝒫/π^{-1}𝒜}` to the fibre over `n` corepresents the `𝒜`-derivations
of `P_n`.** Read over `i_n^{-1}𝒫` it corepresents the `i_n^{-1}(π^{-1}𝒜)`-derivations of
`i_n^{-1}𝒫`, which is
`Stacks.Sheaves.Differentials.restrictedDifferentialsOfSiteCorepresentableBy` at the fibre
inclusion; restriction of scalars along an isomorphism of sheaves of rings is fully faithful, so
nothing is lost in reading it over `P_n`, and
`CategoryTheory.Sheaf.fibreDerivationsFunctorIso` identifies the two notions of derivation. -/
def fibreDifferentialsCorepresentableBy :
    (derivationsFunctor.{u} A ((resolutionCommRing J f).obj (op n))
        ((resolutionCommBase J f).app (op n))).CorepresentableBy
      ((fibreRestrictScalars J f n).obj (fibreDifferentials J f n)) :=
  (((restrictedDifferentialsOfSiteCorepresentableBy J (fibreInclusion C n)
        (simplicialBaseMap J f)).ofIsoObj
      (fibreRestrictScalarsRoundTrip J f n)).compFullyFaithful
    (fullyFaithfulFibreRestrictScalarsInv J f n)).ofIso (fibreDerivationsFunctorIso J f n)

/-- **`i_n^{-1}Ω_{𝒫/π^{-1}𝒜} ≅ Ω_{P_n/𝒜}`.** The sheaf of relative differentials of `𝒫` over
`π^{-1}𝒜` on `Δ × C`, restricted to the fibre over a simplicial degree `n` and read over `P_n`,
is the sheaf of relative differentials of the ring map `𝒜 ⟶ P_n`.

Both sides corepresent the `𝒜`-derivations of `P_n`. -/
def fibreDifferentialsIso :
    (fibreRestrictScalars J f n).obj (fibreDifferentials J f n) ≅
      resolutionDegreeDifferentials J f n :=
  corepresentableByIso (fibreDifferentialsCorepresentableBy J f n)
    (derivationsFunctor.{u} A ((resolutionCommRing J f).obj (op n))
      ((resolutionCommBase J f).app (op n))).corepresentableBy

/-- **The identification is the one carrying the restricted universal derivation to the universal
derivation of `Ω_{P_n/𝒜}`**: transposing it along the corepresentation of
`CategoryTheory.Sheaf.fibreDifferentialsCorepresentableBy` returns that universal derivation, and
by corepresentability no other morphism does. -/
theorem homEquiv_fibreDifferentialsIso_hom :
    (fibreDifferentialsCorepresentableBy J f n).homEquiv (fibreDifferentialsIso J f n).hom =
      universalDerivationOfSite.{u, u, u, u} A ((resolutionCommRing J f).obj (op n))
        ((resolutionCommBase J f).app (op n)) :=
  (fibreDifferentialsCorepresentableBy J f n).homEquiv.apply_symm_apply _

/-! ### The first term of the sequence of principal parts, in the fibre -/

/-- **`Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ` restricted to the fibre over `n`.** The first term of the sequence
of principal parts, which `CategoryTheory.Sheaf.simplicialPrincipalPartsShortComplex_X₁` says is
`Ω_{𝒫/π^{-1}𝒜} ⊗_𝒫 ℱ` on `Δ × C`, restricts to the fibre over a simplicial degree `n` as the
restriction of `Ω_{𝒫/π^{-1}𝒜}` tensored with the restriction of the coefficient module.

The tensor product of sheaves of modules is a sheafification, and it commutes with restriction to
the fibre by `Stacks.Sheaves.Differentials.restrictedSheafTensorRightIso`. Together with
`CategoryTheory.Sheaf.fibreDifferentialsIso`, which identifies the differentials factor
`CategoryTheory.Sheaf.fibreDifferentials` with `Ω_{P_n/𝒜}`, this is the fibrewise reading of the
first term that Tag 09DG asks for.

The source is `i_n^{-1}` of the first term by
`CategoryTheory.Sheaf.restrictedModules_obj_principalPartsX₁`; it is written out here rather than
as `i_n^{-1}(X₁)` because asking the elaborator to see through
`CategoryTheory.Sheaf.simplicialPrincipalPartsShortComplex_X₁` — itself a `rfl` — inside this
application exhausts the heartbeat budget, while the `congrArg` of that equation is cheap. -/
def fibrePrincipalPartsX₁Iso (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (restrictedModules J (fibreInclusion C n) (O₂ := simplicialResolution J f)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor (simplicialResolution J f)).flip.obj
          (moduleOfDifferentialsOfSite.{u, u, u, u} (simplicialBase J (A := A))
            (simplicialResolution J f) (simplicialBaseMap J f)))).obj
              (simplicialCoefficients J f F)) ≅
      (((Stacks.SheafOfModules.Tensor.sheafTensor
          (restrictedCommRing J (fibreInclusion C n) (simplicialResolution J f))).flip.obj
          (fibreDifferentials J f n))).obj
        ((restrictedModules J (fibreInclusion C n)
          (O₂ := simplicialResolution J f)).obj (simplicialCoefficients J f F)) :=
  (restrictedSheafTensorRightIso J (fibreInclusion C n)
      (moduleOfDifferentialsOfSite.{u, u, u, u} (simplicialBase J (A := A))
        (simplicialResolution J f) (simplicialBaseMap J f))).app
    (simplicialCoefficients J f F)

/-- The restriction to the fibre over `n` of the first term of the sequence of principal parts
**is** the source of `CategoryTheory.Sheaf.fibrePrincipalPartsX₁Iso`: the `congrArg` of
`CategoryTheory.Sheaf.simplicialPrincipalPartsShortComplex_X₁`. -/
theorem restrictedModules_obj_principalPartsX₁
    (F : SheafOfModules.{u} (targetRing J (B := B))) :
    (restrictedModules J (fibreInclusion C n) (O₂ := simplicialResolution J f)).obj
        (simplicialPrincipalPartsShortComplex J f F).X₁ =
      (restrictedModules J (fibreInclusion C n) (O₂ := simplicialResolution J f)).obj
        ((((Stacks.SheafOfModules.Tensor.sheafTensor (simplicialResolution J f)).flip.obj
          (moduleOfDifferentialsOfSite.{u, u, u, u} (simplicialBase J (A := A))
            (simplicialResolution J f) (simplicialBaseMap J f)))).obj
              (simplicialCoefficients J f F)) :=
  congrArg (restrictedModules J (fibreInclusion C n) (O₂ := simplicialResolution J f)).obj
    (simplicialPrincipalPartsShortComplex_X₁ J f F)

end CategoryTheory.Sheaf

end
