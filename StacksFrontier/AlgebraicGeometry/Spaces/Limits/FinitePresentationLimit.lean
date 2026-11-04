module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartRespectsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.EtaleLocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeApproximation

/-!
# Consequences of finite type over `Spec ℤ` for a space over `Spec ℤ`

Stacks 09NS writes a quasi-compact quasi-separated algebraic space `X` over a quasi-separated
algebraic space `Y` as a directed inverse limit of algebraic spaces of finite presentation over
`Y` with affine transition morphisms. Its route goes through Stacks 0GS3, which presents a
morphism of quasi-compact quasi-separated algebraic spaces over `Spec ℤ` as a limit of morphisms
whose sources and targets are quasi-separated and *of finite type over `Spec ℤ`*, and the stages
have then to be recognised as being of finite presentation over each other, for which what is
needed about a stage is quasi-compactness and local Noetherianity.

An algebraic space on the big fppf site of the terminal scheme whose structure morphism is of
finite type is quasi-compact and is locally Noetherian in the étale-local sense of Stacks 03E6. A
presheaf on that site is identified with its own view over the terminal scheme, which converts
the finite-type condition as the conclusion of Stacks 0GS3 records it, about the view, into the
same condition about the space.

## Main results

* `AlgebraicGeometry.Space.selfIso_viewOverIntegers`: a presheaf on the big fppf site of the
  terminal scheme is its own view over the terminal scheme.
* `AlgebraicGeometry.Space.isFiniteType_terminal_of_isFiniteType_viewOverIntegers`: the
  finite-type condition transfers from the view to the space.
* `AlgebraicGeometry.Space.isQuasiCompactSpace_of_isFiniteType_terminal`: a space of finite type
  over `Spec ℤ` is quasi-compact.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_isLocallyNoetherian_of_isFiniteType_terminal`: a
  space of finite type over `Spec ℤ` is locally Noetherian.

## Implementation notes

Quasi-compactness of the terminal presheaf is obtained from the object `Over.mk (𝟙 (B.obj hZ))`
of the site, which represents it and whose underlying scheme is the terminal scheme, affine
because it is isomorphic to the spectrum of `ULift ℤ`; local Noetherianity of that scheme is the
Noetherianity of `ULift ℤ`.

## References

* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
* [Stacks Project, Tag 03XF](https://stacks.math.columbia.edu/tag/03XF)
* [Stacks Project, Tag 0GS3](https://stacks.math.columbia.edu/tag/0GS3)
* [Stacks Project, Tag 09NS](https://stacks.math.columbia.edu/tag/09NS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-! ### The view over `Spec ℤ` of a space already over `Spec ℤ` -/

section Terminal

variable (B : BigFppfSite.{u}) (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **A presheaf on the big fppf site of the terminal scheme is its own view over the terminal
scheme.** The view is relocalization along the structure morphism of the base, which over the
terminal scheme is the identity, and relocalization along an identity is the identity functor,
being left adjoint to restriction along `CategoryTheory.Over.mapId`. -/
def selfIso_viewOverIntegers (F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :
    F ≅ viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F :=
  have hg : (𝟙 (B.obj hZ) : B.obj hZ ⟶ B.obj hZ) =
      (⟨terminal.from (⊤_ Scheme.{u})⟩ : B.obj hZ ⟶ B.obj hZ) :=
    B.inclusion.map_injective (terminal.hom_ext _ _)
  let hrestrict : (𝟭 ((Over (B.obj hZ))ᵒᵖ ⥤ Type u)) ≅
      OverShriek.relocalizeRestrict (𝟙 (B.obj hZ)) :=
    (Functor.whiskeringLeft (Over (B.obj hZ))ᵒᵖ (Over (B.obj hZ))ᵒᵖ (Type u)).mapIso
      (NatIso.op (Over.mapId (B.obj hZ)))
  let hfunctor : OverShriek.relocalizePresheafFunctor (𝟙 (B.obj hZ)) ≅
      𝟭 ((Over (B.obj hZ))ᵒᵖ ⥤ Type u) :=
    Adjunction.leftAdjointUniq (OverShriek.relocalizeAdjunction (𝟙 (B.obj hZ)))
      (Adjunction.id.ofNatIsoRight hrestrict)
  (hfunctor.app F).symm ≪≫
    eqToIso (congrArg (fun m => (OverShriek.relocalizePresheafFunctor m).obj F) hg)

variable {F : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}

/-- An algebraic space over the terminal scheme whose view over the terminal scheme is of finite
type over it is itself of finite type over it. -/
theorem isFiniteType_terminal_of_isFiniteType_viewOverIntegers
    (h : IsFiniteType B (⊤_ Scheme.{u}) hZ
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F))) :
    IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from F) := by
  refine ⟨(isLocallyOfFiniteType_terminal_iff_of_iso B (⊤_ Scheme.{u}) hZ
    (selfIso_viewOverIntegers B hZ F)).mpr h.1, ?_⟩
  have hsq : IsPullback (selfIso_viewOverIntegers B hZ F).hom (terminal.from F)
      (terminal.from (viewOverIntegers B (⊤_ Scheme.{u}) hZ hZ F))
      (𝟙 (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))) :=
    IsPullback.of_horiz_isIso ⟨terminal.hom_ext _ _⟩
  exact isQuasiCompact_of_isPullback B (⊤_ Scheme.{u}) hZ hsq h.2

/-- The presheaf represented by the identity of the base is isomorphic to the terminal presheaf. -/
private def yonedaMkIdIsoTerminal :
    yoneda.obj (Over.mk (𝟙 (B.obj hZ)) : BigFppfOver B (⊤_ Scheme.{u}) hZ) ≅
      ⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) :=
  ((Over.mkIdTerminal (X := B.obj hZ)).isTerminalObj yoneda _).uniqueUpToIso terminalIsTerminal

/-- **An algebraic space of finite type over `Spec ℤ` is quasi-compact.** Its structure morphism
is quasi-compact and the terminal presheaf is quasi-compact, being represented by the identity of
the base, whose underlying scheme is the terminal scheme, which is affine. -/
theorem isQuasiCompactSpace_of_isFiniteType_terminal
    (h : IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from F)) :
    IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ F := by
  have hTaff : IsAffine (⊤_ Scheme.{u}) :=
    IsAffine.of_isIso (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv
  have hTqc : IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ
      (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)) :=
    isQuasiCompactSpace_of_iso B (⊤_ Scheme.{u}) hZ
      (yonedaMkIdIsoTerminal B hZ)
      (isQuasiCompactSpace_yoneda_of_isAffine B (⊤_ Scheme.{u}) hZ
        (Over.mk (𝟙 (B.obj hZ))) hTaff)
  have hpb := h.2 (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u))
    (isAlgebraicSpace_terminal B (⊤_ Scheme.{u}) hZ) hTqc (𝟙 _)
  exact isQuasiCompactSpace_of_iso B (⊤_ Scheme.{u}) hZ
    (asIso (pullback.snd (𝟙 (⊤_ ((BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)))
      (terminal.from F))) hpb

/-- **An algebraic space of finite type over `Spec ℤ` is locally Noetherian in the étale-local
sense of Stacks 03E6.** Every étale scheme over it is locally of finite type over the terminal
scheme, which is the spectrum of a Noetherian ring. -/
theorem hasEtaleLocalProperty_isLocallyNoetherian_of_isFiniteType_terminal
    (hF : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ F)
    (h : IsFiniteType B (⊤_ Scheme.{u}) hZ (terminal.from F)) :
    HasEtaleLocalProperty B (⊤_ Scheme.{u}) hZ F
      (fun T : Scheme.{u} => IsLocallyNoetherian T) := by
  have hetaleId : ∀ U : BigFppfOver B (⊤_ Scheme.{u}) hZ,
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)) (𝟙 U) := by
    intro U
    have _ : MorphismProperty.ContainsIdentities
        (@Etale.{u} : MorphismProperty Scheme.{u}) :=
      MorphismProperty.IsMultiplicative.toContainsIdentities
    change AlgebraicGeometry.Etale ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map (𝟙 U))
    rw [CategoryTheory.Functor.map_id]
    exact MorphismProperty.id_mem (@Etale.{u} : MorphismProperty Scheme.{u}) _
  have _ : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  refine (exists_atlas_iff_forall_etale B (⊤_ Scheme.{u}) hZ F _ hF).2 ?_
  intro V a ha
  have hbT : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ)).presheaf
      (yonedaMkIdIsoTerminal B hZ).hom :=
    presheaf_of_isIso B (⊤_ Scheme.{u}) hZ
      (MorphismProperty.RespectsIso.inverseImage _ _) hetaleId _
  have hlft : AlgebraicGeometry.LocallyOfFiniteType
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
        (Over.mkIdTerminal.from V : V ⟶ Over.mk (𝟙 (B.obj hZ)))) :=
    h.1 V (Over.mk (𝟙 (B.obj hZ))) a (yonedaMkIdIsoTerminal B hZ).hom _ ha hbT
      (terminal.hom_ext _ _)
  have _ : IsNoetherianRing (ULift.{u} ℤ) :=
    isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
  have hbase : IsLocallyNoetherian
      ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
        (Over.mk (𝟙 (B.obj hZ)) : BigFppfOver B (⊤_ Scheme.{u}) hZ)) := by
    change IsLocallyNoetherian (⊤_ Scheme.{u})
    exact LocallyOfFiniteType.isLocallyNoetherian
      (specULiftZIsTerminal.{u}.uniqueUpToIso terminalIsTerminal).inv
  let := hbase
  let := hlft
  exact LocallyOfFiniteType.isLocallyNoetherian
    ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).map
      (Over.mkIdTerminal.from V : V ⟶ Over.mk (𝟙 (B.obj hZ))))

end Terminal

end AlgebraicGeometry.Space

end
