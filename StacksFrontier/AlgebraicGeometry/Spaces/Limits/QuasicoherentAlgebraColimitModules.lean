module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.CategoryTheory.Filtered.Connected
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ModuleColimitAffineChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentClausesUnconditional
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.CategoryTheory.Sites.SheafComposeColimits

/-!
# A filtered colimit of quasi-coherent algebras is a colimit of modules

Let `X` be an algebraic space.  A filtered colimit `𝒜 = colim 𝒜_i` in the category
`AlgebraicGeometry.Space.QuasicoherentAlgebra X` of quasi-coherent sheaves of commutative
`𝒪_X`-algebras is also a colimit of the underlying `𝒪_X`-modules.

This is the form in which the proof of Stacks 0GV1 consumes the colimit `π_* 𝒪_Y =
colim π_{i,*} 𝒪_{Y_i}` of Stacks 07VR, which is stated for quasi-coherent algebras
(`AlgebraicGeometry.Space.exists_affineOver_limit_pushforwardColimit_of_isFinite`): Stacks 07U7
(`AlgebraicGeometry.Space.preservesColimitsOfShape_coyoneda_of_isFinitePresentation`) is a
statement about filtered colimits of modules.

## Main results

* `AlgebraicGeometry.Space.nonempty_isColimit_underlyingModule_of_isColimit`: the colimit
  of modules.

## Implementation notes

Write `U` for the functor from algebra sheaves to modules.  Composed with the underlying abelian
sheaf functor it is the underlying sheaf of rings followed by composition with the forgetful
functor from rings to abelian groups.  The first preserves connected colimits (the algebra
sheaves are an under category), and the second preserves filtered colimits because the
forgetful functor from rings to abelian groups preserves filtered colimits and sheafification;
the underlying abelian sheaf functor reflects colimits, so `U` preserves filtered colimits.
The colimit of the algebra sheaves underlying a filtered diagram of quasi-coherent algebras is
then quasi-coherent, its module being a colimit of quasi-coherent modules (Stacks 03M1), so the
inclusion of the quasi-coherent algebras into all algebra sheaves preserves the colimit too.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 07U7](https://stacks.math.columbia.edu/tag/07U7)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The forgetful functor from commutative rings to abelian groups, through rings. -/
private abbrev ringToAb : CommRingCat.{u} ⥤ AddCommGrpCat.{u} :=
  forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}

/-- The forgetful functor from commutative rings to abelian groups preserves sheafification on
the small étale site: becoming an isomorphism after sheafification is local bijectivity, a
condition on the underlying sets of sections. -/
private theorem preservesSheafification_ringToAb :
    (SmallEtale.topology B S hS F).PreservesSheafification ringToAb.{u} where
  le := by
    intro P₁ P₂ f hf
    rw [GrothendieckTopology.W_iff_isLocallyBijective] at hf
    rw [MorphismProperty.inverseImage_iff, GrothendieckTopology.W_iff_isLocallyBijective]
    obtain ⟨h₁, h₂⟩ := hf
    exact ⟨⟨fun a b h => h₁.equalizerSieve_mem a b h⟩, ⟨fun a => h₂.imageSieve_mem a⟩⟩

/-- Composition with the forgetful functor from commutative rings to abelian groups preserves
filtered colimits of sheaves on the small étale site. -/
private theorem preservesColimitsOfShape_sheafCompose_ringToAb (K : Type u) [SmallCategory K]
    [IsFiltered K] :
    PreservesColimitsOfShape (D := Sheaf (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u}) K
      (sheafCompose (SmallEtale.topology B S hS F) ringToAb.{u}) :=
  have := preservesSheafification_ringToAb (B := B) (S := S) (hS := hS) (F := F)
  preservesColimitsOfShape_sheafCompose _ _ K

/-- The underlying module functor of algebra sheaves, followed by the underlying abelian sheaf,
is the underlying sheaf of rings followed by composition with the forgetful functor. -/
private def underlyingModuleToSheafIso :
    AlgebraSheaf.underlyingModuleFunctor.{u, u} (B := B) (S := S) (hS := hS) (F := F) (hF := hF) ⋙
        SheafOfModules.toSheaf.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O) ≅
      AlgebraSheaf.forget ⋙ sheafCompose (SmallEtale.topology B S hS F) ringToAb.{u} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

/-- The underlying module functor of algebra sheaves preserves filtered colimits. -/
private theorem preservesColimitsOfShape_underlyingModuleFunctor (K : Type u) [SmallCategory K]
    [IsFiltered K] :
    PreservesColimitsOfShape K
      (AlgebraSheaf.underlyingModuleFunctor.{u, u} (B := B) (S := S) (hS := hS) (F := F)
        (hF := hF)) :=
  have := preservesColimitsOfShape_sheafCompose_ringToAb (B := B) (S := S) (hS := hS) (F := F)
    (hF := hF) K
  have : IsConnected K := IsFiltered.isConnected K
  have : PreservesColimitsOfShape K (AlgebraSheaf.forget (B := B) (S := S) (hS := hS) (F := F)
      (hF := hF) : AlgebraSheaf.{u, u} B S hS F hF ⥤ _) :=
    AlgebraSheaf.preservesColimitsOfShape_forget K
  have hcomp : PreservesColimitsOfShape (C := AlgebraSheaf.{u, u} B S hS F hF)
      (D := Sheaf (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u}) K
      (AlgebraSheaf.forget ⋙ sheafCompose (SmallEtale.topology B S hS F) ringToAb.{u}) :=
    comp_preservesColimitsOfShape _ _
  have : PreservesColimitsOfShape K
      (AlgebraSheaf.underlyingModuleFunctor.{u, u} (B := B) (S := S) (hS := hS) (F := F)
          (hF := hF) ⋙
        SheafOfModules.toSheaf.{u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
    @preservesColimitsOfShape_of_natIso _ _ _ _ _ _ _ _ underlyingModuleToSheafIso.symm hcomp
  have : ReflectsColimitsOfShape K (SheafOfModules.toSheaf.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
    have : PreservesColimitsOfShape K (SheafOfModules.toSheaf.{u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) :=
      SheafOfModules.preservesColimitsOfShape_toSheaf _
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  preservesColimitsOfShape_of_reflects_of_preserves _
    (SheafOfModules.toSheaf.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))

/-- **A filtered colimit of quasi-coherent algebras is a colimit of the underlying modules.**
If `c` is a colimit cocone, in the quasi-coherent sheaves of commutative `𝒪_X`-algebras on an
algebraic space `X`, of a filtered diagram `Φ`, then the underlying cocone of `𝒪_X`-modules is a
colimit cocone.

Applied to the colimit `π_* 𝒪_Y = colim π_{i,*} 𝒪_{Y_i}` of
`AlgebraicGeometry.Space.exists_affineOver_limit_pushforwardColimit_of_isFinite` this gives the
colimit of modules that Stacks 07U7 consumes in the proof of Stacks 0GV1. -/
theorem nonempty_isColimit_underlyingModule_of_isColimit {X : AlgebraicSpaces B S hS}
    {K : Type u} [SmallCategory K] [IsFiltered K] {Φ : K ⥤ QuasicoherentAlgebra B S hS X}
    {c : Cocone Φ} (hc : IsColimit c) :
    Nonempty (IsColimit ((quasicoherentAlgebraInclusion B S hS X ⋙
      AlgebraSheaf.underlyingModuleFunctor.{u, u}).mapCocone c)) := by
  let ι := quasicoherentAlgebraInclusion B S hS X
  let U := AlgebraSheaf.underlyingModuleFunctor.{u, u} (B := B) (S := S) (hS := hS) (F := X.1)
    (hF := X.2)
  have : IsConnected K := IsFiltered.isConnected K
  have : HasColimitsOfShape K (AlgebraSheaf.{u, u} B S hS X.1 X.2) :=
    hasColimitsOfShape_algebraSheaf K
  have : PreservesColimitsOfShape K U := preservesColimitsOfShape_underlyingModuleFunctor K
  have hqc : (colimit (Φ ⋙ ι)).IsQuasicoherent :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso (preservesColimitIso U (Φ ⋙ ι)).symm
      (isQuasicoherent_colimit' B S hS X.1 X.2 ((Φ ⋙ ι) ⋙ U) fun k => (Φ.obj k).property)
  have : CreatesColimit Φ ι :=
    createsColimitOfFullyFaithfulOfIso ⟨colimit (Φ ⋙ ι), hqc⟩ (Iso.refl _)
  exact ⟨isColimitOfPreserves (ι ⋙ U) hc⟩

end AlgebraicGeometry.Space

end
