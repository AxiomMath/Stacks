module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineChart
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexCompositeDiagonal
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerived
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportDerivedInternalHomBifunctor
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp

/-!
# The exact-support computation for a composite

Let `g : X ⟶ S` and `f : Y ⟶ X` be morphisms of schemes with diagonal opens `W` and `V`, and let
`W' ⊆ Y ×_S Y` be the diagonal open of `f ≫ g` built in
`StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexCompositeDiagonal`, with closed
immersions `δ : V ⟶ W'` and `Δ_{Y/S} = δ ∘ Δ'`. Let `(M, η)` be a relative dualizing complex for
`f` on `V`, and `E ∈ D(𝒪_Y)`. This file proves the step of the proof of Stacks 0E30 that only
uses Stacks 0E2I and `η`: if `R ℰom(𝒪_V, L pr₁^*E|_{W'}) ≅ L pr₁^*M|_V` in `D(𝒪_V)`, then
`R ℰom(𝒪_Y, L pr₁^*E|_{W'}) ≅ 𝒪_Y[0]`.

Indeed `R SheafHom_{𝒪_{W'}}(Δ_{Y/S,*}𝒪_Y, L pr₁^*E)` is
`δ_* R SheafHom_{𝒪_V}(Δ'_*𝒪_Y, R ℰom(𝒪_V, L pr₁^*E))` by Stacks 0E2I, hence
`δ_* R SheafHom_{𝒪_V}(Δ'_*𝒪_Y, L pr₁^*M)`, which is `δ_* Δ'_*𝒪_Y` by `η`. By Stacks 0A77 the
left-hand side is `Δ_{Y/S,*} R ℰom(𝒪_Y, L pr₁^*E)`, and comparing cohomology sheaves (the
pushforward along a closed immersion is fully faithful on modules) gives the claim.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.nonempty_diagonalExactSupport_iso_of_pushforward`:
  `R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]` as soon as its pushforward along `Δ` is that of `𝒪_X[0]`.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.nonempty_comp_diagonalExactSupport_iso`: the
  computation for the composite.

## References

* [Stacks Project, Lemma 48.28.11 (Tag 0E30)](https://stacks.math.columbia.edu/tag/0E30)
* [Stacks Project, Tag 0E2I](https://stacks.math.columbia.edu/tag/0E2I)
* [Stacks Project, Tag 0A77](https://stacks.math.columbia.edu/tag/0A77)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

section

variable {X S : Scheme.{u}} {f : X ⟶ S} (D : DiagonalOpen f)

/-- **`R ℰom(𝒪_X, L pr₁^*K|_W) ≅ 𝒪_X[0]` is detected after `Δ_*`.** The pushforward along the
closed immersion `Δ` commutes with cohomology sheaves and is fully faithful on modules, so an
isomorphism `Δ_*𝒪_X[0] ≅ Δ_* R ℰom(𝒪_X, L pr₁^*K|_W)` identifies the cohomology sheaves of
`R ℰom(𝒪_X, L pr₁^*K|_W)` with those of `𝒪_X[0]`. -/
theorem nonempty_diagonalExactSupport_iso_of_pushforward (K : DerivedCategory X.Modules)
    (e : (RingedSpaceModuleAdjunction.modulePushforward D.diagQuotient.i).mapDerivedCategory.obj
        (structureSingle X) ≅
      (RingedSpaceModuleAdjunction.modulePushforward D.diagQuotient.i).mapDerivedCategory.obj
        (D.diagonalExactSupport K)) :
    Nonempty (D.diagonalExactSupport K ≅ structureSingle X) := by
  let F := RingedSpaceModuleAdjunction.modulePushforward D.diagQuotient.i
  let E := D.diagonalExactSupport K
  let hff := Stacks.ToposBridge.fullyFaithfulModulePushforward D.diag.toLRSHom.toShHom
    (IsClosedImmersion.isClosedEmbedding D.diag).isInducing
    (Stacks.ClosedImmersion.isLocallySurjective_c_toShHom D.diag)
  have hH : ∀ n : ℤ, (DerivedCategory.homologyFunctor X.Modules n).obj (structureSingle X) ≅
      (DerivedCategory.homologyFunctor X.Modules n).obj E := fun n =>
    hff.preimageIso (((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n).app
        (structureSingle X)).symm ≪≫
      (DerivedCategory.homologyFunctor _ n).mapIso e ≪≫
        (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n).app E)
  obtain ⟨e'⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero E 0
    (fun j hj => by
      refine IsZero.of_iso ?_ (hH j).symm
      let e₀ := (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app
        (SheafOfModules.unit X.ringCatSheaf)
      exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0
        (SheafOfModules.unit X.ringCatSheaf) j hj).of_iso
        ((DerivedCategory.homologyFunctor _ j).mapIso e₀ ≪≫
          (DerivedCategory.homologyFunctorFactors _ j).app _))
  exact ⟨e' ≪≫ (DerivedCategory.singleFunctor _ 0).mapIso
    ((hH 0).symm ≪≫ (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app _)⟩

end

variable {X Y S : Scheme.{u}} {g : X ⟶ S} {f : Y ⟶ X} (Dg : DiagonalOpen g) (Df : DiagonalOpen f)

/-- The closed immersion `δ : V ⟶ W'`, read as a closed quotient morphism of ringed spaces. -/
abbrev compQuotient : RingedSpaceModuleAdjunction.ClosedQuotientMorphismOfRingedSpaces.{u} :=
  Stacks.ClosedImmersion.closedQuotientOfClosedImmersion (Dg.compδ Df)

/-- `Δ_{Y/S,*}𝒪_Y = δ_* Δ'_*𝒪_Y` on derived categories. -/
def compPushforwardIso :
    (RingedSpaceModuleAdjunction.modulePushforward
        (Dg.comp Df).diagQuotient.i).mapDerivedCategory.obj (structureSingle Y) ≅
      (RingedSpaceModuleAdjunction.modulePushforward (Dg.compQuotient Df).i).mapDerivedCategory.obj
        ((RingedSpaceModuleAdjunction.modulePushforward Df.diagQuotient.i).mapDerivedCategory.obj
          (structureSingle Y)) :=
  ((RingedSpaceModuleAdjunction.modulePushforward
      (Dg.comp Df).diagQuotient.i).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor _ 0).mapIso
      ((RingedSpaceModuleAdjunction.modulePushforwardComp Df.diagQuotient.i
        (Dg.compQuotient Df).i).symm.app _) ≪≫
    (((RingedSpaceModuleAdjunction.modulePushforward
      (Dg.compQuotient Df).i).mapDerivedCategorySingleFunctor 0).app _).symm ≪≫
    (RingedSpaceModuleAdjunction.modulePushforward (Dg.compQuotient Df).i).mapDerivedCategory.mapIso
      (((RingedSpaceModuleAdjunction.modulePushforward
        Df.diagQuotient.i).mapDerivedCategorySingleFunctor 0).app _).symm

/-- **The exact-support step of Stacks 0E30.** If `R ℰom(𝒪_V, L pr₁^*E|_{W'}) ≅ L pr₁^*M|_V`
and `(M, η)` satisfies the diagonal condition of Stacks 0E2T for `f`, then
`R ℰom(𝒪_Y, L pr₁^*E|_{W'}) ≅ 𝒪_Y[0]`. -/
theorem nonempty_comp_diagonalExactSupport_iso (E M : DerivedCategory Y.Modules)
    (η : Df.diagonalObject ⟶ Df.derivedPullbackProj M) (hη : IsIso (Df.diagonalAction M η))
    (hstar : Nonempty ((Dg.compQuotient Df).derivedSheafHomExactSupport.obj
        ((Dg.comp Df).derivedPullbackProj E) ≅ Df.derivedPullbackProj M)) :
    Nonempty ((Dg.comp Df).diagonalExactSupport E ≅ structureSingle Y) := by
  obtain ⟨es⟩ := hstar
  let D := Dg.comp Df
  let Fδ :=
    (RingedSpaceModuleAdjunction.modulePushforward (Dg.compQuotient Df).i).mapDerivedCategory
  let F' := (RingedSpaceModuleAdjunction.modulePushforward Df.diagQuotient.i).mapDerivedCategory
  let P := D.derivedPullbackProj E
  let N := F'.obj (structureSingle Y)
  -- `R SheafHom(Δ'_*𝒪_Y, R ℰom(𝒪_V, P)) ≅ Δ'_*𝒪_Y`, from `η`
  let eV : ((Stacks.SheafOfModules.derivedSheafHom Df.W.sheaf).obj (op N)).obj
      ((Dg.compQuotient Df).derivedSheafHomExactSupport.obj P) ≅ N :=
    ((Stacks.SheafOfModules.derivedSheafHom Df.W.sheaf).obj (op N)).mapIso es ≪≫
      ((Stacks.SheafOfModules.derivedSheafHom Df.W.sheaf).mapIso Df.diagonalObjectIso.op).app _ ≪≫
      (@asIso _ _ _ _ (Df.diagonalAction M η) hη).symm ≪≫ Df.diagonalObjectIso
  -- Stacks 0E2I along `δ`
  let e0E2I := ((Dg.compQuotient Df).derivedSheafHomPushforwardNatIso N).app P
  exact D.nonempty_diagonalExactSupport_iso_of_pushforward E
    (Dg.compPushforwardIso Df ≪≫ Fδ.mapIso eV.symm ≪≫ e0E2I.symm ≪≫
      ((Stacks.SheafOfModules.derivedSheafHom D.W.sheaf).mapIso
        (Dg.compPushforwardIso Df).op).app P ≪≫
      (D.diagQuotient.derivedSheafHomExactSupportPushforwardNatIso.app P).symm)

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
