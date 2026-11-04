module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectComposite
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeStalkTensorBoundProof
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectPerfectObjectsCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectTriangulated
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatPushforwardPerfectBaseChange

/-!
# Relative perfectness along a flat morphism of finite presentation

Let `g : X ⟶ S` and `f : Y ⟶ X` be flat and locally of finite presentation. If `K ∈ D(𝒪_X)` is
`S`-perfect, then `Lf^*K` is `S`-perfect for `f ≫ g`
(`AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_comp_derivedPullback`): `𝒪_Y` is perfect,
hence `X`-perfect (Stacks 0DI4), so `𝒪_Y ⊗ᴸ Lf^*K` is `S`-perfect (the relative perfectness of a
composite, through the pointwise Tor bound of Stacks 0B66), and `𝒪_Y ⊗ᴸ Lf^*K ≅ Lf^*K`
(Stacks 0FPT).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-- The standard model of `D(𝒪_T)`, for `letI`. -/
local macro "stdᴰ[" T:term "]" : term =>
  `(HasDerivedCategory.standard (StrictlyPerfect.OXMod $T))

/-- The standard models of `D(𝒪_{T|_U})` for all opens `U` of `T`, for `letI`. -/
local macro "stdOpens[" T:term "]" : term =>
  `(fun (U : TopologicalSpace.Opens ($T).carrier) =>
    HasDerivedCategory.standard (StrictlyPerfect.OXMod (($T).restrict U.isOpenEmbedding)))

/-- **Relative perfectness along a flat morphism locally of finite presentation.** If `K` is
`S`-perfect for `g : X ⟶ S` and `f : Y ⟶ X` is flat and locally of finite presentation, then
`Lf^*K` is `S`-perfect for `f ≫ g`. -/
theorem isPerfectRelativeTo_comp_derivedPullback {X Y S : Scheme.{u}} (g : X ⟶ S) (f : Y ⟶ X)
    [Flat g] [LocallyOfFinitePresentation g] [Flat f] [LocallyOfFinitePresentation f]
    (K : @DerivedCategory (StrictlyPerfect.OXMod.{u, u} X.toRingedSpace) _ _
      stdᴰ[X.toRingedSpace])
    (hK : letI := stdᴰ[X.toRingedSpace]
      letI := stdᴰ[RingedSpace.inverseImage S.toRingedSpace g.base]
      letI := stdOpens[RingedSpace.inverseImage S.toRingedSpace g.base]
      g.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K) :
    letI := stdᴰ[Y.toRingedSpace]
    letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing X.toSheafedSpace))
    letI := HasDerivedCategory.standard (SheafOfModules (structureSheafRing Y.toSheafedSpace))
    letI := stdᴰ[RingedSpace.inverseImage S.toRingedSpace (f ≫ g).base]
    letI := stdOpens[RingedSpace.inverseImage S.toRingedSpace (f ≫ g).base]
    (f ≫ g).IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
      ((derivedPullback f.toLRSHom.toShHom).obj K) := by
  let := stdᴰ[Y.toRingedSpace]
  let := stdᴰ[RingedSpace.inverseImage S.toRingedSpace (f ≫ g).base]
  let := stdOpens[RingedSpace.inverseImage S.toRingedSpace (f ≫ g).base]
  let :=
    HasDerivedCategory.standard (Stacks.DerivedTensor.RingedSite.Modules Y.toRingedSpace.sheaf)
  let := HasDerivedCategory.standard (Stacks.DerivedTensor.RingedSite.Modules Y.sheaf)
  have hM := isPerfectRelativeTo_canonical_of_isPerfect f _
    (ProperFlatBaseChange.isPerfect_structureComplex Y)
  have hE := isPerfectRelativeTo_comp_derivedTensor_of_stalkBound g f
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Y.toRingedSpace.sheaf)
    (relativeStalkTensorBound f g _) K _ hK hM
  have := isClosedUnderIsomorphisms_isPerfectRelativeTo (f ≫ g)
    (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
      (RingedSpace.inverseImage S.toRingedSpace (f ≫ g).base))
  exact (isPerfectRelativeTo (f ≫ g) _).prop_of_iso
    (ProperFlatBaseChange.structureComplexTensorIso Y _) hE

end AlgebraicGeometry.Scheme.Hom

end
