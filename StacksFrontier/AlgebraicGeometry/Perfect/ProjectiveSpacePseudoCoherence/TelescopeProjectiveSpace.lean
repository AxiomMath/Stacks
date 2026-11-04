module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectiveSpacePseudoCoherence.TelescopeProj
public import StacksFrontier.AlgebraicGeometry.ChartDictionary.Basic
public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeIso.Reduction
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow

/-!
# The telescope of a standard chart of projective space over a base

For a scheme `S` and the `i`-th standard chart `j : U ⟶ ℙⁿ_S`, the sequence
`0 ⟶ ⨁ₖ 𝒪(k) ⟶ ⨁ₖ 𝒪(k) ⟶ j_*𝒪_U ⟶ 0` is short exact. It is the inverse image along the projection
`ℙⁿ_S ⟶ ℙⁿ_ℤ` of the telescope on the integral model
(`AlgebraicGeometry.ProjectiveSpacePseudoCoherence.ProjTelescope.shortExact_telescope`): inverse
image preserves the colimit, and it carries `j_*𝒪` on `ℙⁿ_ℤ` to `j_*𝒪_U` by affine base change
([Stacks, Tag 02KG]).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveSpacePseudoCoherence

open ProjTelescope

attribute [local instance] MvPolynomial.gradedAlgebra

variable (n : ℕ) (S : Scheme.{u}) (i : Fin (n + 1))

/-- The coordinate `Tᵢ` is homogeneous of degree `1`. -/
theorem X_mem_one :
    (MvPolynomial.X i : MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ)) ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) 1 :=
  (MvPolynomial.mem_homogeneousSubmodule 1 _).2 (MvPolynomial.isHomogeneous_X _ i)

/-- The sequence `𝒪 --Tᵢ--> 𝒪(1) --Tᵢ--> ⋯` of sheaves of modules on the integral model `ℙⁿ_ℤ`. -/
def seqZ : ℕ ⥤ (projectiveSpaceAtUniverse.{u} n).Modules :=
  seq (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (X_mem_one n i)

/-- Its cocone on `j_*𝒪_{D₊(Tᵢ)}`. -/
def coconeZ : Cocone (seqZ n i) :=
  cocone (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (X_mem_one n i)

/-- The cocone `coconeZ` is a colimit. -/
def isColimitCoconeZ : IsColimit (coconeZ n i) :=
  isColimitCocone (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) (X_mem_one n i)

/-- The sequence `𝒪 --Tᵢ--> 𝒪(1) --Tᵢ--> ⋯` on `ℙⁿ_S`. -/
def seqP : ℕ ⥤ (projectiveSpaceOver n S).Modules :=
  seqZ n i ⋙ Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)

/-- Its cocone on the inverse image of `j_*𝒪_{D₊(Tᵢ)}`. -/
def coconeP : Cocone (seqP n S i) :=
  (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).mapCocone
    (coconeZ n i)

/-- The cocone `coconeP` is a colimit. -/
def isColimitCoconeP : IsColimit (coconeP n S i) :=
  letI : PreservesColimitsOfSize.{0, 0}
      (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)) :=
    (Scheme.Modules.pullbackPushforwardAdjunction
      (projectiveSpaceOver.toIntegralAtUniverse n S)).leftAdjoint_preservesColimits
  isColimitOfPreserves _ (isColimitCoconeZ n i)

/-- **The telescope on `ℙⁿ_S` is short exact.** -/
theorem shortExact_telescopeP :
    (ShortComplex.mk (telescopeDiff (seqP n S i)) (telescopeπ (coconeP n S i))
      (telescopeDiff_desc (coconeP n S i))).ShortExact :=
  AlgebraicGeometry.SheafOfModules.shortExact_telescope (seqP n S i) (isColimitCoconeP n S i)

/-- The terms of the sequence are the twists. -/
def seqPObjIso (k : ℕ) : (seqP n S i).obj k ≅
    Stacks.AlgebraicGeometry.ProjTwistTensorPow.twistOver n S (k : ℤ) :=
  (Scheme.Modules.pullback (projectiveSpaceOver.toIntegralAtUniverse n S)).mapIso
    (eqToIso (congrArg (ProjectiveSpectrum.Proj.twistingSheaf
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))) (by simp)))

/-- The standard open `D₊(Tᵢ)` of the integral model. -/
abbrev chartZ : (projectiveSpaceAtUniverse.{u} n).Opens :=
  AlgebraicGeometry.Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ))
    (MvPolynomial.X i)

/-- The `i`-th standard chart of `ℙⁿ_S`, the inverse image of `D₊(Tᵢ)`. -/
abbrev chartP : (projectiveSpaceOver n S).Opens :=
  projectiveSpaceOver.toIntegralAtUniverse n S ⁻¹ᵁ chartZ n i

/-- The standard open `D₊(Tᵢ)` of `ℙⁿ_ℤ` is affine. -/
instance : IsAffine (chartZ.{u} n i).toScheme :=
  AlgebraicGeometry.Proj.isAffineOpen_basicOpen _ _ (X_mem_one n i) Nat.one_pos

/-- The integral model `ℙⁿ_ℤ` is separated. -/
instance : IsSeparated (terminal.from (projectiveSpaceAtUniverse.{u} n)) := by
  dsimp [projectiveSpaceAtUniverse]
  infer_instance

/-- The inclusion of the standard open `D₊(Tᵢ)` into `ℙⁿ_ℤ` is an affine morphism. -/
instance : IsAffineHom (chartZ.{u} n i).ι :=
  IsAffineHom.of_comp (f := (chartZ.{u} n i).ι)
    (g := terminal.from (projectiveSpaceAtUniverse.{u} n))

/-- The inverse image of `j_*𝒪_{D₊(Tᵢ)}` is isomorphic to `j_*𝒪` of the standard chart of
`ℙⁿ_S`. -/
def coconePPtIso : (coconeP n S i).pt ≅
    (Scheme.Modules.pushforward (chartP n S i).ι).obj (Scheme.unitModule (chartP n S i)) :=
  have h := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    (isPullback_morphismRestrict (projectiveSpaceOver.toIntegralAtUniverse n S) (chartZ n i))
    (Scheme.unitModule (chartZ n i))
  @asIso _ _ _ _ ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans
      (isPullback_morphismRestrict (projectiveSpaceOver.toIntegralAtUniverse n S)
        (chartZ n i)).w).app (Scheme.unitModule (chartZ n i))) h ≪≫
    (Scheme.Modules.pushforward (chartP n S i).ι).mapIso
      (Scheme.Modules.pullbackUnitIso _)

end AlgebraicGeometry.ProjectiveSpacePseudoCoherence

end
