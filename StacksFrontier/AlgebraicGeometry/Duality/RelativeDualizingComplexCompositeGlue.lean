module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexCompositeAssembly
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexAffineSections
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.TensorHomTorAmplitudeModel
public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportFlatBaseChangeLocallyBounded
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointLemmas.ExactSupportFlatBaseChangeMap
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.Composition
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PseudoCoherentMorphism.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBaseChangeFull
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectBoundedBelow
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFromFibresCharts
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.DerivedSymmetryAndUnit
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.UnitComparison

/-!
# The exact-support computation of a composite, from the diagonal of 0BYS

Let `g : X ⟶ S` and `f : Y ⟶ X` be flat and locally of finite presentation, with diagonal opens
`W ⊆ X ×_S X` and `V ⊆ Y ×_X Y`, and let `W' ⊆ Y ×_S Y`, `δ : V ⟶ W'`, `f × f : W' ⟶ W` and
`m : V ⟶ X` be as in
`StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexCompositeDiagonal`. Let `(K, ξ)`
be a relative dualizing complex for `g` and `M ∈ D(𝒪_Y)`, and put `E = M ⊗ᴸ Lf^*K`,
`T = L(f × f)^*(L pr₁^*K|_W)` and `F = L pr₁^*M|_{W'}`. This file proves the middle step of the
proof of Stacks 0E30:

`R ℰom(𝒪_V, L pr₁^*E|_{W'}) ≅ L pr₁^*M|_V`,

as soon as the diagonal `F ⊗ᴸ R SheafHom(δ_*𝒪_V, T) ⟶ R SheafHom(δ_*𝒪_V, F ⊗ᴸ T)` of
Stacks 0BYS on `W'` is invertible. Indeed:

* `L pr₁^*E|_{W'} ≅ T ⊗ᴸ F`, derived pullback being monoidal (Stacks 079U) and
  `f ∘ pr₁ = pr₁ ∘ (f × f)`;
* the map of Stacks 0E2N, `R ℰom(𝒪_V, T) ⊗ᴸ Lδ^*F ⟶ R ℰom(𝒪_V, T ⊗ᴸ F)`, is then invertible;
* `R ℰom(𝒪_V, T) ≅ Lm^* R ℰom(𝒪_X, L pr₁^*K|_W)` by Stacks 0E2M along the cartesian square
  `V = W' ×_W X` (the closed immersion `Δ` is pseudo-coherent by Stacks 0695 and 0683, and
  `L pr₁^*K|_W` is locally bounded below by Stacks 0DI5 and 0GEH), and this is
  `Lm^*𝒪_X = 𝒪_V` by `ξ`;
* `Lδ^*F = L pr₁^*M|_V`.

## Main results

* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.pseudoCoherent_diag`: `Δ : X ⟶ W` is
  pseudo-coherent.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.isLocallyBoundedBelow_derivedPullbackProj`:
  `L pr₁^*K|_W` is locally bounded below for `K` `S`-perfect.
* `AlgebraicGeometry.Scheme.Hom.DiagonalOpen.nonempty_compExactSupport_iso_of_isIso_diagonal`:
  the computation above.

## References

* [Stacks Project, Lemma 48.28.11 (Tag 0E30)](https://stacks.math.columbia.edu/tag/0E30)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
* [Stacks Project, Tag 0E2M](https://stacks.math.columbia.edu/tag/0E2M)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

/-- Local boundedness below is invariant under isomorphism. -/
theorem _root_.AlgebraicGeometry.RingedSpace.isLocallyBoundedBelow_of_iso
    {Z : RingedSpace.{u, u}} {E E' : DerivedCategory (StrictlyPerfect.OXMod.{u, u} Z)} (e : E ≅ E')
    (hE : RingedSpace.IsLocallyBoundedBelow Z E) : RingedSpace.IsLocallyBoundedBelow Z E' := by
  intro x
  obtain ⟨U, hU, N, hN⟩ := hE x
  exact ⟨U, hU, N, fun i hi => (hN i hi).of_iso
    ((RingedSpace.restrictModules Z U).mapIso
      ((DerivedCategory.homologyFunctor (StrictlyPerfect.OXMod.{u, u} Z) i).mapIso e.symm))⟩

section Diagonal

variable {X S : Scheme.{u}} {g : X ⟶ S} (Dg : DiagonalOpen g)

/-- The structure morphism `W ⟶ S` of the diagonal open. -/
abbrev toBase : Dg.W ⟶ S := Dg.proj ≫ g

/-- The diagonal `Δ : X ⟶ W` followed by the structure morphism `W ⟶ S` is `g`. -/
theorem diag_toBase : Dg.diag ≫ Dg.toBase = g := by
  rw [toBase, ← Category.assoc, proj, ← Category.assoc, Dg.fac, pullback.diagonal_fst,
    Category.id_comp]

/-- The projection `pr₁ : W ⟶ X` of the diagonal open is flat when `g` is flat. -/
instance flat_proj [Flat g] : Flat Dg.proj :=
  MorphismProperty.comp_mem @Flat _ _ inferInstance inferInstance

/-- The projection `pr₁ : W ⟶ X` of the diagonal open is locally of finite presentation when
`g` is. -/
instance locallyOfFinitePresentation_proj [LocallyOfFinitePresentation g] :
    LocallyOfFinitePresentation Dg.proj :=
  MorphismProperty.comp_mem @LocallyOfFinitePresentation _ _ inferInstance inferInstance

/-- **`Δ : X ⟶ W` is pseudo-coherent.** Both `X` and `W` are flat and locally of finite
presentation over `S`, hence pseudo-coherent over `S` (Stacks 0695), and a morphism between
schemes pseudo-coherent over `S` is pseudo-coherent (Stacks 0683). -/
theorem pseudoCoherent_diag [Flat g] [LocallyOfFinitePresentation g] :
    AlgebraicGeometry.PseudoCoherent Dg.diag := by
  have : AlgebraicGeometry.PseudoCoherent (Dg.diag ≫ Dg.toBase) := by
    rw [diag_toBase]; infer_instance
  exact pseudoCoherent_of_comp Dg.diag Dg.toBase

/-- **`L pr₁^*K|_W` is locally bounded below** for an `S`-perfect `K`: `L pr₁^*K` is
`X`-perfect on `X ×_S X` by Stacks 0DI5, hence locally bounded below by Stacks 0GEH, and this
restricts to the open `W`. -/
theorem isLocallyBoundedBelow_derivedPullbackProj [Flat g] [LocallyOfFinitePresentation g]
    (K : DerivedCategory X.Modules)
    (hK : g.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K) :
    RingedSpace.IsLocallyBoundedBelow Dg.W.toRingedSpace (Dg.derivedPullbackProj K) := by
  have hpb : IsPullback (pullback.fst g g) (pullback.snd g g) g g := IsPullback.of_hasPullback g g
  have h1 := isPerfectRelativeTo_derivedPullback hpb K hK
  have h2 := isLocallyBoundedBelow_of_isPerfectRelativeTo (pullback.snd g g) _ (fun _ => rfl) _ h1
  have h3 := isLocallyBoundedBelow_restrict_of_isOpenImmersion Dg.ι _ h2
  refine RingedSpace.isLocallyBoundedBelow_of_iso ?_ h3
  exact (Scheme.Modules.derivedRestrictIsoDerivedPullback Dg.ι).app _ ≪≫
    Scheme.derivedPullbackCompObj Dg.ι (pullback.fst g g) K

end Diagonal

variable {X Y S : Scheme.{u}} {g : X ⟶ S} {f : Y ⟶ X} (Dg : DiagonalOpen g) (Df : DiagonalOpen f)

/-- `T = L(f × f)^*(L pr₁^*K|_W)` on `W'`. -/
abbrev compTensorFactor (K : DerivedCategory X.Modules) :
    DerivedCategory (Dg.comp Df).W.Modules :=
  (derivedPullback (Dg.compProd Df).toLRSHom.toShHom).obj (Dg.derivedPullbackProj K)

/-- The derived tensor product on a scheme. -/
abbrev tensorOn (Z : Scheme.{u}) :
    DerivedCategory Z.Modules ⥤ DerivedCategory Z.Modules ⥤ DerivedCategory Z.Modules :=
  Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor Z.toRingedSpace.sheaf

/-- **`L pr₁^*(M ⊗ᴸ Lf^*K)|_{W'} ≅ T ⊗ᴸ L pr₁^*M|_{W'}`**: derived pullback is monoidal
(Stacks 079U), `L pr₁^* Lf^* = L(f × f)^* L pr₁^*` because `f ∘ pr₁ = pr₁ ∘ (f × f)`
(Stacks 0D5S), and the derived tensor product is symmetric (Stacks 0FPT). -/
def derivedPullbackProjTensorIso (M : DerivedCategory Y.Modules) (K : DerivedCategory X.Modules) :
    (Dg.comp Df).derivedPullbackProj
        (((tensorOn Y).obj M).obj ((derivedPullback f.toLRSHom.toShHom).obj K)) ≅
      ((tensorOn (Dg.comp Df).W).obj (Dg.compTensorFactor Df K)).obj
        ((Dg.comp Df).derivedPullbackProj M) :=
  (Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso
      (Dg.comp Df).proj.toLRSHom.toShHom).app (M, (derivedPullback f.toLRSHom.toShHom).obj K) ≪≫
    ((tensorOn (Dg.comp Df).W).obj ((Dg.comp Df).derivedPullbackProj M)).mapIso
      (Scheme.derivedPullbackCompObj (Dg.comp Df).proj f K ≪≫
        Scheme.derivedPullbackCongrObj (Dg.comp_proj_comp Df) K ≪≫
        (Scheme.derivedPullbackCompObj (Dg.compProd Df) Dg.proj K).symm) ≪≫
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      (Dg.comp Df).W.toRingedSpace.sheaf).braidingIso
      (Stacks.SheafOfModules.ringedSite (Dg.comp Df).W.toRingedSpace.sheaf) _ _

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

attribute [local instance] DiagonalOpen.isOpenImmersion DiagonalOpen.isClosedImmersion

variable {X Y S : Scheme.{u}} {g : X ⟶ S} {f : Y ⟶ X} (Dg : DiagonalOpen g) (Df : DiagonalOpen f)

/-- **`R ℰom(𝒪_V, T) ≅ 𝒪_V[0]`.** By Stacks 0E2M along the cartesian square `V = W' ×_W X`
(the base change map of Stacks 0E2K is invertible at the locally bounded below
`L pr₁^*K|_W`, the closed immersion `Δ` being pseudo-coherent and `f × f` flat),
`R ℰom(𝒪_V, T) ≅ Lm^* R ℰom(𝒪_X, L pr₁^*K|_W)`, which is `Lm^*𝒪_X[0] = 𝒪_V[0]` by `ξ`. -/
theorem nonempty_compExactSupport_tensorFactor_iso [Flat g] [LocallyOfFinitePresentation g]
    [Flat f] (K : DerivedCategory X.Modules)
    (hK : g.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K)
    (ξ : Dg.diagonalObject ⟶ Dg.derivedPullbackProj K) (hξ : IsIso (Dg.diagonalAction K ξ)) :
    Nonempty ((Dg.compQuotient Df).derivedSheafHomExactSupport.obj (Dg.compTensorFactor Df K) ≅
      structureSingle Df.W) := by
  have := Dg.pseudoCoherent_diag
  have := Dg.flat_compProd Df
  have sq : IsPullback (Dg.compδ Df) Df.compBaseMap (Dg.compProd Df) Dg.diag :=
    (Dg.isPullback_compδ Df).flip
  have htor : TorIndependent Dg.diag (Dg.compProd Df) := torIndependent_of_flat_right _ _
  have hiso := open Stacks.Duality.ExactSupportBaseChange in
    isIso_baseChangeSheafHomExactSupportMap_app_of_flat_of_isLocallyBoundedBelow
      sq htor (Dg.derivedPullbackProj K) (Dg.isLocallyBoundedBelow_derivedPullbackProj K hK)
  obtain ⟨e⟩ := Dg.nonempty_diagonalExactSupport_iso K ξ hξ
  exact ⟨(asIso ((Stacks.Duality.ExactSupportBaseChange.baseChangeSheafHomExactSupportMap sq
      htor).app (Dg.derivedPullbackProj K))).symm ≪≫
    (derivedPullback Df.compBaseMap.toLRSHom.toShHom).mapIso e ≪≫
    Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso Df.compBaseMap.toLRSHom.toShHom⟩

/-- **The exact-support computation of the proof of Stacks 0E30**, from the invertibility of the
diagonal of Stacks 0BYS at `(L pr₁^*M|_{W'}, T, δ_*𝒪_V)` on `W'`:
`R ℰom(𝒪_V, L pr₁^*(M ⊗ᴸ Lf^*K)|_{W'}) ≅ L pr₁^*M|_V`. The map of Stacks 0E2N identifies the
left-hand side with `R ℰom(𝒪_V, T) ⊗ᴸ Lδ^*(L pr₁^*M|_{W'})`, and `R ℰom(𝒪_V, T) = 𝒪_V[0]`. -/
theorem nonempty_compExactSupport_iso_of_isIso_diagonal [Flat g] [LocallyOfFinitePresentation g]
    [Flat f] (M : DerivedCategory Y.Modules) (K : DerivedCategory X.Modules)
    (hK : g.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) K)
    (ξ : Dg.diagonalObject ⟶ Dg.derivedPullbackProj K) (hξ : IsIso (Dg.diagonalAction K ξ))
    (hdiag : IsIso ((Stacks.Duality.TensorHomTorAmplitude.ambientRingedSite
      (Dg.compQuotient Df)).derivedTensorHomDiagonal ((Dg.comp Df).derivedPullbackProj M)
        (Dg.compTensorFactor Df K)
        (Stacks.Duality.TensorHomTorAmplitude.pushforwardDerivedStructureSheaf
          (Dg.compQuotient Df)))) :
    Nonempty ((Dg.compQuotient Df).derivedSheafHomExactSupport.obj
        ((Dg.comp Df).derivedPullbackProj
          (((tensorOn Y).obj M).obj ((derivedPullback f.toLRSHom.toShHom).obj K))) ≅
      Df.derivedPullbackProj M) := by
  have h0E2N :=
    Stacks.Duality.TensorHomTorAmplitude.isIso_tensorDerivedSheafHomModelMap_of_isIso_diagonal
      (Dg.compQuotient Df) (Dg.compTensorFactor Df K) ((Dg.comp Df).derivedPullbackProj M) hdiag
  obtain ⟨eT⟩ := Dg.nonempty_compExactSupport_tensorFactor_iso Df K hK ξ hξ
  refine ⟨(Dg.compQuotient Df).derivedSheafHomExactSupport.mapIso
      (Dg.derivedPullbackProjTensorIso Df M K) ≪≫
    (asIso (Stacks.Duality.TensorHomTorAmplitude.tensorDerivedSheafHomModelMap (Dg.compQuotient Df)
      (Dg.compTensorFactor Df K) ((Dg.comp Df).derivedPullbackProj M))).symm ≪≫ ?_⟩
  refine ((tensorOn Df.W).mapIso eT).app _ ≪≫ ?_
  refine (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct
      Df.W.toRingedSpace.sheaf).leftUnitIso
      (Stacks.SheafOfModules.ringedSite Df.W.toRingedSpace.sheaf) _ ≪≫ ?_
  exact Scheme.derivedPullbackCompObj (Dg.compδ Df) (Dg.comp Df).proj M ≪≫
    Scheme.derivedPullbackCongrObj (Dg.compδ_proj Df) M

/-- **The diagonal of Stacks 0BYS is invertible after replacing the source of the internal Hom
by an isomorphic object**, by its naturality in that variable. -/
theorem _root_.AlgebraicGeometry.RingedSite.isIso_derivedTensorHomDiagonal_of_iso_hom
    (Z : RingedSite.{u, u, u})
    (A B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O)))
    {C C' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Z.O))}
    (e : C' ≅ C) (h : IsIso (Z.derivedTensorHomDiagonal A B C)) :
    IsIso (Z.derivedTensorHomDiagonal A B C') := by
  have hn := AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_natural_hom Z A B e.hom
  rw [← IsIso.eq_inv_comp] at hn
  rw [hn]
  infer_instance

/-- **`L(f × f)^*Δ_*𝒪_X ≅ δ_*𝒪_V`**, flat base change (Stacks 0E23) along the cartesian square
`V = W' ×_W X`, and `Lm^*𝒪_X = 𝒪_V`. -/
def compPushforwardStructureSheafIso [Flat f] :
    (derivedPullback (Dg.compProd Df).toLRSHom.toShHom).obj
        (Stacks.Duality.TensorHomTorAmplitude.pushforwardDerivedStructureSheaf Dg.diagQuotient) ≅
      Stacks.Duality.TensorHomTorAmplitude.pushforwardDerivedStructureSheaf
        (Dg.compQuotient Df) :=
  haveI := Dg.flat_compProd Df
  ((Stacks.Duality.ExactSupportBaseChange.pushforwardBaseChangeIso (Dg.isPullback_compδ Df).flip
      (torIndependent_of_flat_right Dg.diag (Dg.compProd Df))).app
      (Stacks.Duality.TensorHomTorAmplitude.derivedStructureSheafZ Dg.diagQuotient)).symm ≪≫
    (RingedSpaceModuleAdjunction.modulePushforward (Dg.compQuotient Df).i).mapDerivedCategory.mapIso
      (Stacks.Cohomology.DerivedPullbackUnit.derivedPullbackUnitIso
        Df.compBaseMap.toLRSHom.toShHom)

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

end
