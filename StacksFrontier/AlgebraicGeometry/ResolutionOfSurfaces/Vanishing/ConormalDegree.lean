module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmplePullback.QuasiAffineUnitIso
public import StacksFrontier.AlgebraicGeometry.CartierConormal.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorInvertibleSheaf
public import StacksFrontier.AlgebraicGeometry.Fibres.SectionsFromFibre
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.ModulePullbackPseudofunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.Normal
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Vanishing.ComponentFactorization
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.ContractingRationalCurves
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection

/-!
# The conormal degree of a divisor supported in the special fibre

In the vanishing situation of [Stacks, Tag 0AX8] — a two-dimensional Noetherian normal local
domain `A` and a modification `f : X ⟶ S = Spec(A)` with the irreducible components
`C_1, …, C_r` of the special fibre `X_s` enumerated — let `X` be normal and let `Z ⊆ X` be a
nonempty effective Cartier divisor contained set theoretically in `X_s`. [Stacks, Tag 0AXA]
asserts that the conormal sheaf of `Z` is not trivial, and more precisely that there is an `i`
with `C_i ⊆ Z` and `deg(𝒞_{Z/X}|_{C_i}) > 0`.

This file equips each component `C_i` with everything the degree on the left needs — the
reduced induced structure of `AlgebraicGeometry.VanishingSituation.componentScheme`, a
structure morphism over the residue field `κ` of the closed point, properness, integrality and
dimension one — identifies the restriction of the conormal sheaf of `Z` to `C_i` with the
pullback of the ideal sheaf `ℐ_Z`, and proves the positivity of that degree from the section
the source's argument produces.

## Main definitions

The elided prefix throughout is `AlgebraicGeometry.VanishingSituation`.

* `componentIdeal`, `componentι`: the ideal sheaf cutting out `C_i` with its reduced induced
  structure inside `X`, and the closed immersion `C_i ⟶ X`.
* `componentToSpecResidueField`: the structure morphism `C_i ⟶ Spec(κ)`, obtained by factoring
  `C_i ⟶ X` through the special fibre.
* `componentSchemeHomeo`: `C_i` as a scheme is homeomorphic to `C_i` as a subspace of `X_s`.
* `componentToDivisor`: the closed immersion `C_i ⟶ Z` for a component contained in `Z`.
* `conormalOnComponent`: `𝒞_{Z/X}|_{C_i}`, written as the pullback of `ℐ_Z` along `C_i ⟶ X`.

## Main results

* `isProper_componentToSpecResidueField`, `isIntegral_componentScheme`,
  `topologicalKrullDim_componentScheme_le_one`: `C_i` is an integral scheme proper over `κ` of
  dimension at most one, so the degree of an invertible sheaf on it is defined. The dimension
  uses the standing observation following Situation 0AX8 that every component of the special
  fibre has dimension one, carried as a hypothesis exactly as in [Stacks, Tag 0AX9].
* `isInvertible_conormalOnComponent`: the restricted conormal sheaf is invertible.
* `conormalOnComponentIso`: the pullback along `C_i ⟶ Z` of the conormal sheaf of `Z` in `X`
  is the pullback of `ℐ_Z` along `C_i ⟶ X`. This is [Stacks, Tag 0B3P]'s conormal clause
  followed by pseudofunctoriality of the module pullback, and it is what makes
  `conormalOnComponent` the restricted conormal sheaf and not merely a sheaf resembling it.
* `invertibleCurveDegree_conormalOnComponent_pos`,
  `exists_component_subset_invertibleCurveDegree_pos`, `not_isTrivial_conormalSheaf`: the last
  step of the proof of [Stacks, Tag 0AXA] — the degree clause at a component carrying a section
  with a zero, the same in existential form, and the non-triviality clause derived from it.

## Relation to the full statement

The theorems of the last section are the final step of the source's argument, stated with the
inputs of that step as hypotheses, and carry no `@[stacks]` attribute. [Stacks, Tag 0AXA] itself,
under exactly the source's hypotheses, is proved in
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Vanishing/ConormalDegreePositive.lean` as
`AlgebraicGeometry.VanishingSituation.exists_subset_invertibleCurveDegree_conormalOnComponent_pos`
and `AlgebraicGeometry.VanishingSituation.not_isTrivial_conormalSheaf_of_nonempty`, which build
the section and prove the dimension-one observation from the hypotheses of the lemma.

The hypotheses of the step are three. `hpos` is part (2) of [Stacks, Tag 0B40] in the quantified
form `AlgebraicGeometry.VanishingSectionDegreePos κ`, a theorem of the library
(`AlgebraicGeometry.vanishingSectionDegreePos`); it is kept as an argument here so that these
statements do not change. `hdim` is the observation following Situation 0AX8 that every
component of the special fibre has dimension one. The last is a nonzero global section of
`𝒞_{Z/X}|_{C_i}` with a zero, which in the source is constructed from the function of
[Stacks, Tag 0AX9].

## Implementation notes

`componentToSpecResidueField` rebuilds, as a public declaration, the morphism that
`StacksFrontier/AlgebraicGeometry/ResolutionOfSurfaces/Vanishing/ComponentFactorization.lean`
constructs privately for its own use, and `componentSchemeHomeo` likewise; a `private`
declaration cannot be referenced from an exposed public body, so they are not reusable from
there. The elementary facts they rest on — that the image of a component in `X` is closed, and
that the ideal sheaf of the special fibre is contained in that of each component — are rebuilt
publicly for the same reason. The two facts for which a general form already exists elsewhere,
that the inclusion of a fibre over a closed point is a closed immersion and that a fibre is
proper over the residue field of its image point, are taken from
`Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι` and
`Stacks.AlgebraicGeometry.TopDegreeBaseChange.isProper_fiberToSpecResidueField` rather than
reproved; the instances here
only specialize them to the closed point, and are named with that suffix so that their bare
names do not shadow the general ones.

Containment `C_i ⊆ Z` is stated set theoretically, as an inclusion of subsets of `X`, which for
the reduced `C_i` is equivalent to the inclusion of ideal sheaves `ℐ_Z ≤ ℐ_{C_i}`
(`le_componentIdeal_of_subset`) and hence to the factorization `C_i ⟶ Z ⟶ X`
(`componentToDivisor`). Containment of `Z` in the special fibre is likewise set theoretic, as
the source has it, and not an inclusion of subschemes.

Invertibility of a module sheaf occurs in several spellings in this library;
`AlgebraicGeometry.invertibleCurveDegree` takes
`AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2`, and
`Stacks.Divisors.IsEffectiveCartierDivisor` is the same class at the `X.sheaf.obj` spelling, so
`isInvertible_conormalOnComponent` moves the witness across with a `haveI` of declared type
before pulling it back along `RingedSpaceModuleAdjunction`'s
`modulePullback_isInvertible_scheme`.

## References

* [Stacks Project, Tag 0AXA](https://stacks.math.columbia.edu/tag/0AXA)
* [Stacks Project, Tag 0AX8](https://stacks.math.columbia.edu/tag/0AX8)
* [Stacks Project, Tag 0AX9](https://stacks.math.columbia.edu/tag/0AX9)
* [Stacks Project, Tag 0B40](https://stacks.math.columbia.edu/tag/0B40)
* [Stacks Project, Tag 0B3P](https://stacks.math.columbia.edu/tag/0B3P)
* [Stacks Project, Tag 0B3S](https://stacks.math.columbia.edu/tag/0B3S)
* [Stacks Project, Tag 02OP](https://stacks.math.columbia.edu/tag/02OP)
* [Stacks Project, Tag 0AYX](https://stacks.math.columbia.edu/tag/0AYX)
* [Stacks Project, Tag 0346](https://stacks.math.columbia.edu/tag/0346)
* [Stacks Project, Tag 0B3M](https://stacks.math.columbia.edu/tag/0B3M)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.VanishingSituation

variable (V : VanishingSituation.{u})

/-- The ideal sheaf cutting out the `i`-th component of the special fibre, with its reduced
induced structure, inside the source of the modification. -/
abbrev componentIdeal (i : Fin V.numberOfComponents) : V.X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (componentClosed V i)

/-- The closed immersion of the `i`-th component of the special fibre into the source. -/
abbrev componentι (i : Fin V.numberOfComponents) : componentScheme V i ⟶ V.X :=
  (componentIdeal V i).subschemeι

/-- The inclusion of the special fibre is a closed immersion, the closed point of the base
being a closed point. -/
instance isClosedImmersion_fiberι_closedPoint :
    IsClosedImmersion (V.f.fiberι V.closedPoint) :=
  Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι V.f
    (IsLocalRing.isClosed_singleton_closedPoint V.A)

/-- The image in the source of a component of the special fibre is closed. -/
theorem isClosed_componentInSource (i : Fin V.numberOfComponents) :
    IsClosed (componentInSource V i) :=
  (V.f.fiberι V.closedPoint).isClosedEmbedding.isClosedMap _
    (isClosed_of_mem_irreducibleComponents _ (V.component_mem_irreducibleComponents i))

/-- The closure of the image of a component of the special fibre is that image. -/
theorem coe_componentClosed (i : Fin V.numberOfComponents) :
    (componentClosed V i : Set V.X) = componentInSource V i :=
  closure_eq_iff_isClosed.mpr (isClosed_componentInSource V i)

/-- The support of the ideal sheaf of the `i`-th component is the image of that component. -/
theorem supportSet_componentIdeal (i : Fin V.numberOfComponents) :
    (componentIdeal V i).supportSet = componentInSource V i := by
  change ((componentIdeal V i).support : Set V.X) = _
  rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, coe_componentClosed]

/-- An ideal sheaf whose support contains a component is contained in that component's ideal
sheaf. -/
private theorem le_componentIdeal_of_subset_support (I : V.X.IdealSheafData)
    (i : Fin V.numberOfComponents) (hCi : componentInSource V i ⊆ (I.support : Set V.X)) :
    I ≤ componentIdeal V i := by
  apply Scheme.IdealSheafData.le_support_iff_le_vanishingIdeal.mp
  change (componentClosed V i : Set V.X) ⊆ _
  rwa [coe_componentClosed]

/-- The ideal sheaf of the special fibre is contained in the ideal sheaf of each of its
components. -/
theorem ker_fiberι_le_componentIdeal (i : Fin V.numberOfComponents) :
    (V.f.fiberι V.closedPoint).ker ≤ componentIdeal V i := by
  apply le_componentIdeal_of_subset_support
  rw [Scheme.Hom.support_ker]
  exact Set.image_subset_iff.mpr fun x _ => subset_closure ⟨x, rfl⟩

/-- The structure morphism of the `i`-th component of the special fibre over the residue field
of the closed point of the base. -/
def componentToSpecResidueField (i : Fin V.numberOfComponents) :
    componentScheme V i ⟶ Spec (.of (V.base.residueField V.closedPoint)) :=
  Scheme.IdealSheafData.inclusion (ker_fiberι_le_componentIdeal V i) ≫
    (asIso (V.f.fiberι V.closedPoint).toImage).inv ≫
      V.f.fiberToSpecResidueField V.closedPoint

/-- The special fibre is proper over the residue field of the closed point. -/
instance isProper_fiberToSpecResidueField_closedPoint :
    IsProper (V.f.fiberToSpecResidueField V.closedPoint) :=
  Stacks.AlgebraicGeometry.TopDegreeBaseChange.isProper_fiberToSpecResidueField V.f
    V.closedPoint

/-- Each component of the special fibre is proper over the residue field of the closed
point. -/
instance isProper_componentToSpecResidueField (i : Fin V.numberOfComponents) :
    IsProper (componentToSpecResidueField V i) :=
  inferInstanceAs (IsProper (Scheme.IdealSheafData.inclusion (ker_fiberι_le_componentIdeal V i) ≫
    (asIso (V.f.fiberι V.closedPoint).toImage).inv ≫
      V.f.fiberToSpecResidueField V.closedPoint))

/-- The support of the ideal sheaf of the `i`-th component, as a set. -/
theorem coe_support_componentIdeal (i : Fin V.numberOfComponents) :
    ((componentIdeal V i).support : Set V.X) = componentInSource V i :=
  supportSet_componentIdeal V i

/-- The `i`-th component of the special fibre, with its reduced induced closed subscheme
structure, is homeomorphic to that component with its subspace topology. -/
def componentSchemeHomeo (i : Fin V.numberOfComponents) :
    componentScheme V i ≃ₜ V.component i :=
  let I := componentIdeal V i
  let e₁ : I.subscheme ≃ₜ I.support :=
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso I.subschemeIso)).trans I.gluedHomeo
  let e₂ : I.support ≃ₜ componentInSource V i :=
    Homeomorph.setCongr (coe_support_componentIdeal V i)
  let e₃ : V.component i ≃ₜ componentInSource V i :=
    (V.f.fiberι V.closedPoint).isClosedEmbedding.isEmbedding.homeomorphImage (V.component i)
  e₁.trans (e₂.trans e₃.symm)

/-- The `i`-th component of the special fibre, as a scheme, is irreducible. -/
instance irreducibleSpace_componentScheme (i : Fin V.numberOfComponents) :
    IrreducibleSpace (componentScheme V i) :=
  (componentSchemeHomeo V i).irreducibleSpace_iff.mpr
    (Subtype.irreducibleSpace (V.component_mem_irreducibleComponents i).1)

/-- The `i`-th component of the special fibre, as a scheme, is integral. -/
instance isIntegral_componentScheme (i : Fin V.numberOfComponents) :
    IsIntegral (componentScheme V i) :=
  haveI : IsReduced (componentScheme V i) :=
    Scheme.IdealSheafData.isReduced_subscheme_vanishingIdeal (componentClosed V i)
  isIntegral_of_irreducibleSpace_of_isReduced _

/-- Under the standing observation following Situation 0AX8 that every component of the special
fibre has dimension one, each component is a curve. -/
theorem topologicalKrullDim_componentScheme_le_one
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (i : Fin V.numberOfComponents) : topologicalKrullDim (componentScheme V i) ≤ 1 :=
  le_of_eq
    (((componentSchemeHomeo V i).isHomeomorph.topologicalKrullDim_eq).trans (hdim i))

/-! ### The conormal sheaf of a divisor, restricted to a component of the special fibre -/

/-- The restriction `𝒞_{Z/X}|_{C_i}` to the `i`-th component of the special fibre of the
conormal sheaf of a closed subscheme `Z = V(ℐ) ⊆ X`.

By [Stacks, Tag 0B3P] the conormal sheaf of `Z` in `X` is `ℐ|_Z`
(`Stacks.CartierConormal.conormalSheafIsoNegativeTwist`), so its restriction to a component
contained in `Z` is the pullback of `ℐ` along the closed immersion of that component into
`X`, which is what is written here. -/
abbrev conormalOnComponent (I : V.X.IdealSheafData) (i : Fin V.numberOfComponents) :
    (componentScheme V i).Modules :=
  (RingedSpaceModuleAdjunction.modulePullback (componentι V i).toLRSHom.toShHom).obj
    (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom)

/-- For an effective Cartier divisor `Z` the restriction of its conormal sheaf to a component
of the special fibre is invertible, being the pullback of the invertible ideal sheaf `ℐ_Z`. -/
instance isInvertible_conormalOnComponent (I : V.X.IdealSheafData)
    [hI : Stacks.Divisors.IsEffectiveCartierDivisor I] (i : Fin V.numberOfComponents) :
    SheafOfModules.IsInvertible (componentScheme V i).presheaf
      (componentScheme V i).ringCatSheaf.2 (conormalOnComponent V I i) :=
  haveI : SheafOfModules.IsInvertible V.X.presheaf V.X.ringCatSheaf.2
      (Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom) := hI
  RingedSpaceModuleAdjunction.modulePullback_isInvertible_scheme _ _

/-- A component of the special fibre contained set theoretically in a closed subscheme `Z` is
contained in it scheme theoretically: its reduced induced structure makes the inclusion of
ideal sheaves `ℐ_Z ≤ ℐ_{C_i}` hold. -/
theorem le_componentIdeal_of_subset (I : V.X.IdealSheafData) (i : Fin V.numberOfComponents)
    (hCi : componentInSource V i ⊆ I.supportSet) : I ≤ componentIdeal V i := by
  exact le_componentIdeal_of_subset_support V I i hCi

/-- The closed immersion of a component of the special fibre into a closed subscheme `Z`
containing it set theoretically. -/
def componentToDivisor (I : V.X.IdealSheafData) (i : Fin V.numberOfComponents)
    (hCi : componentInSource V i ⊆ I.supportSet) : componentScheme V i ⟶ I.subscheme :=
  Scheme.IdealSheafData.inclusion (le_componentIdeal_of_subset V I i hCi)

/-- The closed immersion of a component into `Z`, followed by that of `Z` into `X`, is the
closed immersion of the component into `X`. -/
theorem componentToDivisor_comp_subschemeι (I : V.X.IdealSheafData)
    (i : Fin V.numberOfComponents) (hCi : componentInSource V i ⊆ I.supportSet) :
    componentToDivisor V I i hCi ≫ I.subschemeι = componentι V i :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- **The restriction to a component is the restricted conormal sheaf.** The pullback along
`C_i ⟶ Z` of the conormal sheaf of `Z` in `X` is the pullback of `ℐ_Z` along `C_i ⟶ X`: the
conormal sheaf of `Z` is `ℐ_Z|_Z` by [Stacks, Tag 0B3P], and pullback is pseudofunctorial. -/
def conormalOnComponentIso (I : V.X.IdealSheafData) (i : Fin V.numberOfComponents)
    (hCi : componentInSource V i ⊆ I.supportSet) :
    (RingedSpaceModuleAdjunction.modulePullback
          (componentToDivisor V I i hCi).toLRSHom.toShHom).obj
        (Stacks.Conormal.conormalSheaf I.subschemeι) ≅ conormalOnComponent V I i :=
  (RingedSpaceModuleAdjunction.modulePullback
        (componentToDivisor V I i hCi).toLRSHom.toShHom).mapIso
      (Stacks.CartierConormal.conormalSheafIsoNegativeTwist I) ≪≫
    (Stacks.RingedSpace.modulePullbackComp (componentToDivisor V I i hCi).toLRSHom.toShHom
        I.subschemeι.toLRSHom.toShHom).app _ ≪≫
    (Stacks.RingedSpace.modulePullbackCongr
      (show (componentToDivisor V I i hCi).toLRSHom.toShHom ≫ I.subschemeι.toLRSHom.toShHom =
          (componentι V i).toLRSHom.toShHom from
        congrArg (fun g : componentScheme V i ⟶ V.X => g.toLRSHom.toShHom)
          (componentToDivisor_comp_subschemeι V I i hCi))).app _

/-! ### Positivity of the conormal degree -/

/-- **The last step of [Stacks, Tag 0AXA]**, the degree clause at a component carrying the
section the source's argument produces.

In Situation 0AX8 with `X` normal, let `Z ⊆ X` be a nonempty effective Cartier divisor
contained set theoretically in the special fibre, and let `C_i` be a component of the special
fibre contained in `Z`. If the restriction `𝒞_{Z/X}|_{C_i}` of the conormal sheaf of `Z` has a
nonzero global section with a zero, then `deg(𝒞_{Z/X}|_{C_i}) > 0`.

The component `C_i`, with its reduced induced structure, is an integral scheme proper over the
residue field `κ` of the closed point of the base, of dimension one by the standing observation
following Situation 0AX8 which is `hdim`; the restricted conormal sheaf is invertible because
`ℐ_Z` is. Part (2) of [Stacks, Tag 0B40] then gives the conclusion; it is the argument `hpos`,
in the form `AlgebraicGeometry.VanishingSectionDegreePos`, which the library proves as
`AlgebraicGeometry.vanishingSectionDegreePos`.

The section is an argument here. Its construction, and with it [Stacks, Tag 0AXA] under the
source's hypotheses alone, is
`exists_subset_invertibleCurveDegree_conormalOnComponent_pos`. -/
theorem invertibleCurveDegree_conormalOnComponent_pos [IsNormal V.X]
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (I : V.X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor I]
    (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint))
    (hpos : VanishingSectionDegreePos (V.base.residueField V.closedPoint))
    (i : Fin V.numberOfComponents) (hCi : componentInSource V i ⊆ I.supportSet)
    (s : (conormalOnComponent V I i).sections) (hs : s.eval (op ⊤) ≠ 0)
    (hzero : ∃ y : componentScheme V i, y ∉ Stacks.SheafOfModules.nonvanishingLocus
      (X := (componentScheme V i).toRingedSpace) (conormalOnComponent V I i) s) :
    0 < invertibleCurveDegree (V.base.residueField V.closedPoint)
      (componentToSpecResidueField V i)
      (topologicalKrullDim_componentScheme_le_one V hdim i) (conormalOnComponent V I i) := by
  -- The two remaining hypotheses of the source are carried but not consumed by this clause:
  -- the nonemptiness of `Z` and its containment in the special fibre enter only through the
  -- construction of the section, and the containment `C_i ⊆ Z` only through the identification
  -- of the restricted conormal sheaf.
  have : I.supportSet.Nonempty := hne
  have : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint) := hZs
  have : componentInSource V i ⊆ I.supportSet := hCi
  exact hpos (componentScheme V i) (componentToSpecResidueField V i) inferInstance
    inferInstance (topologicalKrullDim_componentScheme_le_one V hdim i)
    (conormalOnComponent V I i) inferInstance s hs hzero

/-- The last step of [Stacks, Tag 0AXA] in the source's existential form.

The hypothesis is that *some* component contained in `Z` carries a nonzero global section of
the restricted conormal sheaf with a zero; the conclusion is the source's: there is an `i` with
`C_i ⊆ Z` and `deg(𝒞_{Z/X}|_{C_i}) > 0`. The statement without the section is
`exists_subset_invertibleCurveDegree_conormalOnComponent_pos`. -/
theorem exists_component_subset_invertibleCurveDegree_pos [IsNormal V.X]
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (I : V.X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor I]
    (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint))
    (hpos : VanishingSectionDegreePos (V.base.residueField V.closedPoint))
    (hsec : ∃ (i : Fin V.numberOfComponents) (_ : componentInSource V i ⊆ I.supportSet)
      (s : (conormalOnComponent V I i).sections), s.eval (op ⊤) ≠ 0 ∧
        ∃ y : componentScheme V i, y ∉ Stacks.SheafOfModules.nonvanishingLocus
          (X := (componentScheme V i).toRingedSpace) (conormalOnComponent V I i) s) :
    ∃ i : Fin V.numberOfComponents, componentInSource V i ⊆ I.supportSet ∧
      0 < invertibleCurveDegree (V.base.residueField V.closedPoint)
        (componentToSpecResidueField V i)
        (topologicalKrullDim_componentScheme_le_one V hdim i) (conormalOnComponent V I i) := by
  obtain ⟨i, hCi, s, hs, hz⟩ := hsec
  exact ⟨i, hCi,
    invertibleCurveDegree_conormalOnComponent_pos V hdim I hne hZs hpos i hCi s hs hz⟩

/-- The non-triviality clause of [Stacks, Tag 0AXA], derived from the last step of its proof.

If the conormal sheaf of `Z` in `X` were trivial, its restriction to a component `C_i ⊆ Z`
would be isomorphic to the structure sheaf of `C_i` and so would have degree zero, which
contradicts the positivity of that degree. The statement under the source's hypotheses alone
is `not_isTrivial_conormalSheaf_of_nonempty`. -/
theorem not_isTrivial_conormalSheaf [IsNormal V.X]
    (hdim : ∀ i : Fin V.numberOfComponents, topologicalKrullDim (V.component i) = 1)
    (I : V.X.IdealSheafData) [Stacks.Divisors.IsEffectiveCartierDivisor I]
    (hne : I.supportSet.Nonempty)
    (hZs : I.supportSet ⊆ Set.range (V.f.fiberι V.closedPoint))
    (hpos : VanishingSectionDegreePos (V.base.residueField V.closedPoint))
    (i : Fin V.numberOfComponents) (hCi : componentInSource V i ⊆ I.supportSet)
    (s : (conormalOnComponent V I i).sections) (hs : s.eval (op ⊤) ≠ 0)
    (hzero : ∃ y : componentScheme V i, y ∉ Stacks.SheafOfModules.nonvanishingLocus
      (X := (componentScheme V i).toRingedSpace) (conormalOnComponent V I i) s) :
    ¬ SheafOfModules.IsTrivial I.subscheme.presheaf I.subscheme.ringCatSheaf.2
      (Stacks.Conormal.conormalSheaf I.subschemeι) := by
  rintro ⟨e⟩
  have hdeg :=
    invertibleCurveDegree_conormalOnComponent_pos V hdim I hne hZs hpos i hCi s hs hzero
  have hiso : conormalOnComponent V I i ≅
      SheafOfModules.unit (componentScheme V i).ringCatSheaf :=
    (conormalOnComponentIso V I i hCi).symm ≪≫
      Stacks.AmplePullback.modulePullbackIsoUnitModule (componentToDivisor V I i hCi) _ e
  rw [invertibleCurveDegree_eq_zero_of_iso_unit (V.base.residueField V.closedPoint)
    (componentToSpecResidueField V i) _ _ hiso] at hdeg
  exact absurd hdeg (lt_irrefl 0)

end AlgebraicGeometry.VanishingSituation

end
