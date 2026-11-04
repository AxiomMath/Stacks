module

public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.CategoryTheory.Triangulated.Functor
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.GlobalKunnethMap
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffinePushforwardQuasiCoherence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.BoundedBelowTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.TorAmplitude.BoundedBelowOnARingedSpace
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.BoundedCoherentConditions
public import StacksFrontier.Topology.Sheaves.Modules.Flat.Stalk
public import StacksFrontier.CategoryTheory.Sites.Cohomology.KFlat.ResolutionsOnARingedSite
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.PerfectGlobalSectionsAffineBase
public import StacksFrontier.AlgebraicGeometry.Perfect.CoherentBaseCohomology
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtension
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.StructureSheafUnit
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafAsADerivedUnit
public import StacksFrontier.AlgebraicGeometry.Perfect.TorIndependence
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.Basic
public import StacksFrontier.Homology.Tor.Presentation
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType.Basis
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedAmplitude.UpperBounds
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.UnitAlongAComposite
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentDerivedHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ItemAuxiliary
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.KunnethDischarged

/-!
# `H¹` of a product over a field injects into the faces

Let `k` be a field, let `P = X ×_S Y` be a fibre product with sections `σ`, `τ` of
`f : X ⟶ S` and `g : Y ⟶ S`, and let `s ∈ S`. Over `Spec κ(s)` the fibre `P_s` is the product
`X_s ×_{κ(s)} Y_s`, and the two faces `X ⟶ P` (`x ↦ (x, τ(f(x)))`) and `Y ⟶ P`
(`y ↦ (σ(g(y)), y)`) restrict to `X_s ⟶ P_s` and `Y_s ⟶ P_s`. This file proves that
`H¹(P_s, 𝒪) ⟶ H¹(X_s, 𝒪) ⊕ H¹(Y_s, 𝒪)` is injective, in the spelling of
`Stacks.Cohomology.GlobalKunneth.sectionsPullbackMap`, when `f` and `g` are proper with
`𝒪 ≅ f_*𝒪` and `𝒪 ≅ g_*𝒪` universally. This is the cohomological input of the proof of
[Stacks, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3), which the source obtains from the
Künneth formula [Stacks, Tag 0BED].

## Main results

* `AlgebraicGeometry.KunnethFirstCohomology.eq_zero_of_sectionsPullbackMap_faces`: the
  injectivity, from the relative Künneth isomorphism of [Stacks, Tag 0FLQ],
  `Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme`.
* `AlgebraicGeometry.KunnethFirstCohomology.isIso_structureSheafHom_pullback_snd_fst_comp`:
  the universal invariance of the structure sheaf passes from `f` and `g` to
  `X ×_S Y ⟶ S`.

## Implementation notes

*The argument is a dimension count, not a Künneth formula with its maps.* The source identifies
`H¹(P_s)` with `H¹(X_s) ⊕ H¹(Y_s)` through the Künneth map and reads off the two face maps. The
compatibility of the relative Künneth map of Tag 0FLP with pullback maps rests on the
monoidality coherence of derived pullback (Tags 079U/0D5S), which this library does not have.
So the proof avoids it:

1. *Surjectivity with known diagonal.* The projections `π₀ : P_s ⟶ X_s` and `π₁ : P_s ⟶ Y_s`
   satisfy `j₀ ≫ π₀ = 𝟙`, `j₁ ≫ π₁ = 𝟙`, while `j₁ ≫ π₀` and `j₀ ≫ π₁` factor through the
   point `Spec κ(s)`, where `H¹` vanishes. By the composition law of pulling back, in
   `Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces` as
   `map_unit_comp_derivedPushforwardCompIso_comp`, the composite
   `H¹(X_s) ⊕ H¹(Y_s) ⟶ H¹(P_s) ⟶ H¹(X_s) ⊕ H¹(Y_s)` is a diagonal of isomorphisms, so the face
   map is surjective.
2. *Dimension bound.* The relative Künneth isomorphism of Tag 0FLQ
   (`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme`) identifies `Rc_*𝒪_{P_s}` with
   `A ⊗^𝐋 B`, `A = Ra_*𝒪_{X_s}`, `B = Rb_*𝒪_{Y_s}`. The cones `A'`, `B'` of the units
   `𝒪 ⟶ A`, `𝒪 ⟶ B` lie in degrees `≥ 1` because `H⁰` of the units is `𝒪 ≅ a_*𝒪`; every module
   on `Spec κ(s)` is flat, so `A' ⊗^𝐋 B'` lies in degrees `≥ 2`; three long exact sequences give
   `dim H¹(A ⊗^𝐋 B) ≤ dim H¹(A) + dim H¹(B)`. The cohomology is finite dimensional by
   [Stacks, Tag 02O6].
3. A surjection of finite dimensional vector spaces with source of dimension at most that of the
   target is injective.

Everything is stated at `HasDerivedCategory.standard`, at priority `10000`, the model of
`Stacks.Cohomology.GlobalKunneth.sectionsPullbackMap` and of
`Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme`.

## References

* [Stacks Project, Tag 0BF3](https://stacks.math.columbia.edu/tag/0BF3)
* [Stacks Project, Tag 0BED](https://stacks.math.columbia.edu/tag/0BED)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated AlgebraicGeometry
open Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward
  derivedAdjunction derivedPushforwardCompIso)
open Stacks.Cohomology.DerivedPullbackUnit (derivedPullbackUnitIso)
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedStructureUnit (structureUnit)
open Stacks.Cohomology.GlobalKunneth (baseRing)
open Stacks.DerivedPullback.Composition (derivedPullbackCompIsoCanonical)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

namespace AlgebraicGeometry.KunnethFirstCohomology

attribute [local instance 10000] HasDerivedCategory.standard

/-- In an exact sequence `M₁ ⟶ M₂ ⟶ M₃` of vector spaces with finite dimensional ends, the
middle term is finite dimensional of dimension at most the sum. -/
private theorem finiteDimensional_and_finrank_le_of_exact {k : Type u} [Field k]
    (S : ShortComplex (ModuleCat.{u} k)) (hS : S.Exact)
    [FiniteDimensional k S.X₁] [FiniteDimensional k S.X₃] :
    FiniteDimensional k S.X₂ ∧
      Module.finrank k S.X₂ ≤ Module.finrank k S.X₁ + Module.finrank k S.X₃ := by
  rw [ShortComplex.moduleCat_exact_iff_range_eq_ker] at hS
  have hker : (LinearMap.ker S.g.hom).FG := by
    rw [← hS, LinearMap.range_eq_map]
    exact (Module.Finite.fg_top).map _
  have hrange : (Submodule.map S.g.hom ⊤).FG := IsNoetherian.noetherian _
  have htop : (⊤ : Submodule k S.X₂).FG :=
    Submodule.fg_of_fg_map_of_fg_inf_ker S.g.hom hrange (by rwa [top_inf_eq])
  have : FiniteDimensional k S.X₂ := Module.Finite.of_fg_top htop
  refine ⟨inferInstance, ?_⟩
  rw [← LinearMap.finrank_range_add_finrank_ker S.g.hom, ← hS, add_comm]
  exact add_le_add (LinearMap.finrank_range_le _) (Submodule.finrank_le _)

section Triangles

variable {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] [HasDerivedCategory 𝒜]
  {k : Type u} [Field k] [HasDerivedCategory (ModuleCat.{u} k)]
  (G : DerivedCategory 𝒜 ⥤ DerivedCategory (ModuleCat.{u} k)) [G.CommShift ℤ] [G.IsTriangulated]

/-- The exact sequence `H^n(G T.obj₁) ⟶ H^n(G T.obj₂) ⟶ H^n(G T.obj₃)` of a distinguished
triangle, read through an exact functor. -/
private theorem finiteDimensional_and_finrank_le_of_distTriang (T : Triangle (DerivedCategory 𝒜))
    (hT : T ∈ distTriang _) (n : ℤ)
    [FiniteDimensional k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj (G.obj T.obj₁))]
    [FiniteDimensional k
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj (G.obj T.obj₃))] :
    FiniteDimensional k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj (G.obj T.obj₂)) ∧
      Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj (G.obj T.obj₂)) ≤
        Module.finrank k
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj (G.obj T.obj₁)) +
          Module.finrank k
            ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) n).obj (G.obj T.obj₃)) :=
  @finiteDimensional_and_finrank_le_of_exact k _ _
    (DerivedCategory.HomologySequence.exact₂ _ (G.map_distinguished T hT) n) ‹_› ‹_›

/-- **A dimension bound from three triangles.** `T₃ : 𝟙 ⟶ A ⟶ A' ⟶`, `T₂ : A' ⊗ 𝟙 ⟶ A' ⊗ B ⟶
A' ⊗ B' ⟶` and `T₁ : 𝟙 ⊗ B ⟶ A ⊗ B ⟶ A' ⊗ B ⟶`, abstractly: if `H¹(G(A' ⊗ B')) = 0` and
`H²(G 𝟙) = 0` then `dim H¹(G(A ⊗ B)) ≤ dim H¹(G(𝟙 ⊗ B)) + dim H¹(G A)`. -/
private theorem finiteDimensional_and_finrank_le_of_three_triangles
    (T₁ T₂ T₃ : Triangle (DerivedCategory 𝒜))
    (h₁ : T₁ ∈ distTriang _) (h₂ : T₂ ∈ distTriang _) (h₃ : T₃ ∈ distTriang _)
    (e₂ : T₂.obj₂ ≅ T₁.obj₃) (e₃ : T₃.obj₃ ≅ T₂.obj₁)
    (hz₂ : IsZero (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).obj (G.obj T₂.obj₃))))
    (hz₃ : IsZero (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 2).obj (G.obj T₃.obj₁))))
    [FiniteDimensional k
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).obj (G.obj T₁.obj₁)))]
    [FiniteDimensional k
      (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).obj (G.obj T₃.obj₂)))] :
    FiniteDimensional k
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).obj (G.obj T₁.obj₂))) ∧
      Module.finrank k
          (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).obj (G.obj T₁.obj₂))) ≤
        Module.finrank k
            (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).obj (G.obj T₁.obj₁))) +
          Module.finrank k
            (((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).obj (G.obj T₃.obj₂))) := by
  have ex₃ := DerivedCategory.HomologySequence.exact₃ _ (G.map_distinguished T₃ h₃) 1 2
  have hz : ∀ {M : ModuleCat.{u} k}, IsZero M → FiniteDimensional k M ∧ Module.finrank k M = 0 :=
    fun hM => by
      have := ModuleCat.subsingleton_of_isZero hM
      exact ⟨inferInstance, Module.finrank_zero_of_subsingleton⟩
  obtain ⟨_, hz₃'⟩ := hz hz₃
  obtain ⟨hA', hA'le⟩ := @finiteDimensional_and_finrank_le_of_exact k _ _ ex₃ ‹_› ‹_›
  replace hA' : FiniteDimensional k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).obj
      (G.obj T₃.obj₃)) := hA'
  replace hA'le : Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).obj
      (G.obj T₃.obj₃)) ≤ Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).obj
      (G.obj T₃.obj₂)) + Module.finrank k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 2).obj
      (G.obj T₃.obj₁)) := hA'le
  let ε₃ :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).mapIso (G.mapIso e₃)).toLinearEquiv
  have : FiniteDimensional k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).obj
      (G.obj T₂.obj₁)) := Module.Finite.equiv ε₃
  obtain ⟨_, hz₂'⟩ := hz hz₂
  obtain ⟨hT₂, hT₂le⟩ := finiteDimensional_and_finrank_le_of_distTriang G T₂ h₂ 1
  let ε₂ :=
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).mapIso (G.mapIso e₂)).toLinearEquiv
  have : FiniteDimensional k ((DerivedCategory.homologyFunctor (ModuleCat.{u} k) 1).obj
      (G.obj T₁.obj₃)) := Module.Finite.equiv ε₂
  obtain ⟨hT₁, hT₁le⟩ := finiteDimensional_and_finrank_le_of_distTriang G T₁ h₁ 1
  refine ⟨hT₁, ?_⟩
  have := ε₂.finrank_eq
  have := ε₃.finrank_eq
  omega

end Triangles

section Cone

open DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- **The cone of a map out of an object in degree zero which is an isomorphism on `H⁰`, into an
object in degrees `≥ 0`, lives in degrees `≥ 1`.** -/
private theorem isGE_one_obj₃_of_isIso_homology_zero_mor₁ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _)
    (h₁ : ∀ j : ℤ, j ≠ 0 → IsZero ((homologyFunctor C j).obj T.obj₁))
    (h₂ : ∀ j : ℤ, j < 0 → IsZero ((homologyFunctor C j).obj T.obj₂))
    (hu : IsIso ((homologyFunctor C 0).map T.mor₁)) : T.obj₃.IsGE 1 := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  have hf : (homologyFunctor C i).map T.mor₂ = 0 := by
    rcases lt_or_eq_of_le (show i ≤ 0 by omega) with h | rfl
    · exact (h₂ i h).eq_of_src _ _
    · exact (HomologySequence.epi_homologyMap_mor₁_iff T hT 0).1 inferInstance
  have hg : HomologySequence.δ T i (i + 1) = 0 := by
    by_cases h : i + 1 = 0
    · have hi' : i = -1 := by omega
      subst hi'
      exact (HomologySequence.mono_homologyMap_mor₁_iff T hT (-1) 0).1 inferInstance
    · exact (h₁ (i + 1) h).eq_of_tgt _ _
  exact (HomologySequence.exact₃ T hT i (i + 1)).isZero_X₂ hf hg

end Cone

/-- **A split surjection of controlled dimension is injective.** Let `Φ_i : V ⟶ W_i` and
`Ψ_i : A_i ⟶ V` (`i = 0, 1`) be linear maps of vector spaces with `Φ_i ∘ Ψ_i` invertible and
`Φ_i ∘ Ψ_j = 0` for `i ≠ j`. If `V` is finite dimensional of dimension at most
`dim A₀ + dim A₁`, then `(Φ₀, Φ₁)` is injective. -/
private theorem eq_zero_of_split {k : Type u} [Field k] {V W₀ W₁ A₀ A₁ : ModuleCat.{u} k}
    (Φ₀ : V ⟶ W₀) (Φ₁ : V ⟶ W₁) (Ψ₀ : A₀ ⟶ V) (Ψ₁ : A₁ ⟶ V)
    (h₀ : IsIso (Ψ₀ ≫ Φ₀)) (h₁ : IsIso (Ψ₁ ≫ Φ₁)) (h₁₀ : Ψ₁ ≫ Φ₀ = 0) (h₀₁ : Ψ₀ ≫ Φ₁ = 0)
    [FiniteDimensional k A₀] [FiniteDimensional k A₁] [FiniteDimensional k V]
    (hdim : Module.finrank k V ≤ Module.finrank k A₀ + Module.finrank k A₁)
    (y : V) (hy₀ : Φ₀.hom y = 0) (hy₁ : Φ₁.hom y = 0) : y = 0 := by
  let e₀ := (asIso (Ψ₀ ≫ Φ₀)).toLinearEquiv
  let e₁ := (asIso (Ψ₁ ≫ Φ₁)).toLinearEquiv
  have : FiniteDimensional k W₀ := Module.Finite.equiv e₀
  have : FiniteDimensional k W₁ := Module.Finite.equiv e₁
  let Φ : V →ₗ[k] W₀ × W₁ := LinearMap.prod Φ₀.hom Φ₁.hom
  have hsurj : Function.Surjective Φ := by
    rintro ⟨w₀, w₁⟩
    refine ⟨Ψ₀.hom (e₀.symm w₀) + Ψ₁.hom (e₁.symm w₁), ?_⟩
    have a₀ : Φ₀.hom (Ψ₀.hom (e₀.symm w₀)) = w₀ := e₀.apply_symm_apply w₀
    have a₁ : Φ₁.hom (Ψ₁.hom (e₁.symm w₁)) = w₁ := e₁.apply_symm_apply w₁
    have b₀ : Φ₀.hom (Ψ₁.hom (e₁.symm w₁)) = 0 := by
      simpa using congrArg (fun f => f.hom (e₁.symm w₁)) h₁₀
    have b₁ : Φ₁.hom (Ψ₀.hom (e₀.symm w₀)) = 0 := by
      simpa using congrArg (fun f => f.hom (e₀.symm w₀)) h₀₁
    simp [Φ, a₀, a₁, b₀, b₁]
  have hrank : Module.finrank k V = Module.finrank k (W₀ × W₁) := by
    refine le_antisymm ?_ (LinearMap.finrank_range_le Φ |>.trans_eq' ?_)
    · rwa [Module.finrank_prod, ← e₀.finrank_eq, ← e₁.finrank_eq]
    · rw [LinearMap.range_eq_top.2 hsurj, finrank_top]
  have hinj := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hrank).2 hsurj
  exact hinj (by simp [Φ, hy₀, hy₁])

private theorem isGE_derivedSectionsOverOpen_obj (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (a : ℤ) (hE : E.IsGE a) :
    ((derivedSectionsOverOpen X U).obj E).IsGE a :=
  Stacks.SmallDerivedCategory.isGE_obj_of_isGE (sectionsOverOpen X U)
    (derivedSectionsOverOpen X U) (derivedSectionsOverOpenUnit X U)
    (fun I hI =>
      (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective
        (homotopySectionsOverOpen X U)
        (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)).2
          DerivedCategory.Qh _ _ I hI) E a hE

/-- Every module over a field (in the sense of `IsField`) is flat. -/
private theorem flat_of_isField {R : Type u} [CommRing R] (hR : IsField R) (N : Type u)
    [AddCommGroup N] (_ : Module R N) : Module.Flat R N :=
  let _ : Field R := hR.toField
  let _ : Module.Free R N := Module.Free.of_divisionRing R N
  Module.Flat.of_free

variable (X : RingedSpace.{u, u})

private theorem isFlat_of_isField_stalks (hX : ∀ x : X.carrier, IsField (X.presheaf.stalk x))
    (M : SheafOfModules.{u} (structureSheafRing X)) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M :=
  (AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat X.sheaf M).2 fun x =>
    flat_of_isField (hX x) _ _

private theorem isGE_derivedTensor_of_isField_stalks
    (hX : ∀ x : X.carrier, IsField (X.presheaf.stalk x))
    (E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (a b : ℤ)
    (hE : E.IsGE a) (hE' : E'.IsGE b) :
    (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.sheaf).obj E).obj E').IsGE
      (a + b) := by
  let T : Stacks.SheafOfModules.DerivedTensorProduct.{u, u, u, u + 1}
      (Stacks.RingedSpace.toRingedSite X) :=
    Stacks.Cohomology.TorAmplitude.derTensorSite.{u, u + 1} X
  have hF : ∀ F : SheafOfModules.{u} (structureSheafRing X),
      Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE.{u, u, u, u + 1} T
        ((DerivedCategory.singleFunctor _ 0).obj F) 0 := fun F =>
    Stacks.SheafOfModules.DerivedTensorProduct.hasTorAmplitudeGE_of_kFlatRepresentative.{u, u, u}
      T _ 0
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
      (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat X.sheaf F
        (isFlat_of_isField_stalks X hX F) 0)
      (fun i hi => HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F i (by omega))
      ((DerivedCategory.singleFunctorIsoCompQ _ 0).app F).symm
  have hEA :
      Stacks.SheafOfModules.DerivedTensorProduct.HasTorAmplitudeGE.{u, u, u, u + 1} T E a := by
    intro F i hi
    have h1 :=
      Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE.{u, u + 1} T
        ((DerivedCategory.singleFunctor _ 0).obj F) E 0 a (hF F) hE
    rw [zero_add] at h1
    have h2 := isGE_derivedTensor_swap X _ _ a h1
    exact DerivedCategory.isZero_of_isGE _ a i hi (hX := h2)
  exact Stacks.SheafOfModules.DerivedTensorProduct.isGE_tensor_of_hasTorAmplitudeGE.{u, u + 1} T
    E E' a b hEA hE'

variable {A : Type u} [CommRing A] {Y : Scheme.{u}} (q : Y ⟶ Spec (CommRingCat.of A))

private theorem nonempty_homology_baseSections_derivedPushforward_iso (M : Y.Modules) (n : ℕ) :
    Nonempty ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom).obj
        ((DerivedCategory.homologyFunctor _ (n : ℤ)).obj
          ((Stacks.Cohomology.GlobalKunneth.baseSections
              (Spec (CommRingCat.of A)).toRingedSpace).obj
            ((derivedPushforward q.toLRSHom.toShHom).obj
              ((DerivedCategory.singleFunctor Y.Modules 0).obj M)))) ≅
      (ModuleCat.restrictScalars (Stacks.Cech.globalRingHom q).hom).obj
        (((moduleGlobalSections Y).rightDerived n).obj M)) := by
  obtain ⟨eB⟩ := nonempty_derivedGlobalSectionsOver_iso_derivedGlobalSectionsOverBase q M
  refine ⟨((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom) (n : ℤ)).app
      _).symm ≪≫ ?_⟩
  refine (DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
    ((derivedSectionsBaseIso (A := A)).app _) ≪≫ ?_
  refine (DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso
    ((derivedGlobalSectionsOverPushforwardIso q).app _).symm ≪≫ ?_
  exact (DerivedCategory.homologyFunctor _ (n : ℤ)).mapIso eB ≪≫
    Stacks.AlgebraicGeometry.CoherentBaseCohomology.cohomologyIso q M n

private theorem isZero_homology_baseSections_spec_field (k : Type u) [Field k] (n : ℕ)
    (hn : 0 < n) :
    IsZero ((DerivedCategory.homologyFunctor
        (ModuleCat.{u} (Stacks.Cohomology.GlobalKunneth.baseRing
          (Spec (CommRingCat.of k)).toRingedSpace)) (n : ℤ)).obj
      ((Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of k)).toRingedSpace).obj
        ((derivedPushforward (Scheme.Hom.toLRSHom (𝟙 (Spec (CommRingCat.of k)))).toShHom).obj
          ((DerivedCategory.singleFunctor (Spec (CommRingCat.of k)).Modules 0).obj
            (SheafOfModules.unit _))))) := by
  obtain ⟨e⟩ := nonempty_homology_baseSections_derivedPushforward_iso
    (𝟙 (Spec (CommRingCat.of k))) (SheafOfModules.unit _) n
  have hdim : topologicalKrullDim (Spec (CommRingCat.of k)) ≤ ((0 : ℕ) : WithBot ℕ∞) := by
    change topologicalKrullDim (PrimeSpectrum k) ≤ _
    rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, ringKrullDim_eq_zero_of_field]
    rfl
  have hz := isZero_cohomologyOverField_of_topologicalKrullDim_le k (𝟙 (Spec (CommRingCat.of k)))
    (SheafOfModules.unit _) hdim hn
  have : Subsingleton ((ModuleCat.restrictScalars
      (Stacks.Cech.globalRingHom (𝟙 (Spec (CommRingCat.of k)))).hom).obj
        (((moduleGlobalSections _).rightDerived n).obj (SheafOfModules.unit _))) :=
    cohomologyOverField_eq_restrictScalars_appTop k (𝟙 (Spec (CommRingCat.of k)))
      (SheafOfModules.unit _) n ▸ ModuleCat.subsingleton_of_isZero hz
  have : Subsingleton ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (Stacks.Cohomology.GlobalKunneth.baseRing
        (Spec (CommRingCat.of k)).toRingedSpace)) (n : ℤ)).obj
          ((Stacks.Cohomology.GlobalKunneth.baseSections
              (Spec (CommRingCat.of k)).toRingedSpace).obj
            ((derivedPushforward (Scheme.Hom.toLRSHom (𝟙 (Spec (CommRingCat.of k)))).toShHom).obj
              ((DerivedCategory.singleFunctor (Spec (CommRingCat.of k)).Modules 0).obj
                (SheafOfModules.unit _)))))) := e.toLinearEquiv.toEquiv.subsingleton
  exact @ModuleCat.isZero_of_subsingleton _ _ _ this

/-- `𝒪_Z` in degree zero. -/
private abbrev unitObj (Z : RingedSpace.{u, u}) :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing Z)) :=
  (DerivedCategory.singleFunctor (SheafOfModules.{u} (structureSheafRing Z)) 0).obj
    (SheafOfModules.unit (structureSheafRing Z))

private theorem isDQCoh_unitObj (X : Scheme.{u}) :
    Stacks.DerivedQCoh.IsDQCoh.{u + 1, u, u, u} (unitObj X.toRingedSpace) := by
  intro i
  by_cases hi : i = 0
  · subst hi
    exact isQuasicoherent_of_iso X _ _
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) 0).app _).symm
      (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isQuasicoherent_unit.{u}
        (R := structureSheafRing X.toRingedSpace))
  · rcases lt_or_gt_of_ne hi with h | h
    · exact isQuasicoherent_of_isZero X _
        (DerivedCategory.isZero_of_isGE (unitObj X.toRingedSpace) 0 i h)
    · exact isQuasicoherent_of_isZero X _
        (DerivedCategory.isZero_of_isLE (unitObj X.toRingedSpace) 0 i h)

/-- Over a base whose local rings are fields, any two schemes are Tor independent. -/
private theorem torIndependent_of_isField_stalk {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S)
    (hS : ∀ s : S, IsField (S.presheaf.stalk s)) : TorIndependent a b := by
  intro x y h
  let : Algebra (S.presheaf.stalk (a.base x)) (X.presheaf.stalk x) :=
    (a.stalkMap x).hom.toAlgebra
  let : Algebra (S.presheaf.stalk (a.base x)) (Y.presheaf.stalk y) :=
    (eqToHom (congrArg (fun z ↦ S.presheaf.stalk z) h) ≫ b.stalkMap y).hom.toAlgebra
  intro p hp
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, by omega⟩
  have := flat_of_isField (hS (a.base x)) (X.presheaf.stalk x) inferInstance
  exact isZero_Tor_succ_of_flat (ModuleCat.of _ (X.presheaf.stalk x)) _ n

/-- The Künneth isomorphism `Ra_*𝒪_X ⊗^𝐋 Rb_*𝒪_Y ≅ R(p ≫ a)_*𝒪_{X ×_S Y}`, `p` the first
projection, for Tor independent `a` and `b`: the relative Künneth map of [Stacks, Tag 0FLP] at the
structure sheaves. -/
private def kunnethUnitIso
    {S X Y : Scheme.{u}} (a : X ⟶ S) (b : Y ⟶ S) [QuasiCompact a] [QuasiSeparated a]
    [QuasiCompact b] [QuasiSeparated b] (hab : TorIndependent a b) :
    ((derivedTensorProductFunctor S.sheaf).obj
        ((derivedPushforward a.toLRSHom.toShHom).obj (unitObj X.toRingedSpace))).obj
      ((derivedPushforward b.toLRSHom.toShHom).obj (unitObj Y.toRingedSpace)) ≅
    (derivedPushforward (pullback.fst a b ≫ a).toLRSHom.toShHom).obj
      (unitObj (pullback a b).toRingedSpace) := by
  haveI := Stacks.Cohomology.DerivedKunneth.isIso_kunnethMapScheme a b hab
    (unitObj X.toRingedSpace) (unitObj Y.toRingedSpace) (isDQCoh_unitObj X) (isDQCoh_unitObj Y)
  exact asIso (Stacks.Cohomology.DerivedKunneth.kunnethMap a.toLRSHom.toShHom b.toLRSHom.toShHom
      (pullback.fst a b).toLRSHom.toShHom (pullback.snd a b).toLRSHom.toShHom
      (pullback.fst a b ≫ a).toLRSHom.toShHom rfl
      (Stacks.Cohomology.GlobalKunneth.toShHom_pullback_condition a b) _ _) ≪≫
    (derivedPushforward (pullback.fst a b ≫ a).toLRSHom.toShHom).mapIso
      (((derivedTensorProductFunctor (pullback a b).sheaf).mapIso
          (derivedPullbackUnitIso (pullback.fst a b).toLRSHom.toShHom)).app
            ((derivedPullback (pullback.snd a b).toLRSHom.toShHom).obj (unitObj Y.toRingedSpace)) ≪≫
        ((derivedTensorProductFunctor (pullback a b).sheaf).obj
          (unitObj (pullback a b).toRingedSpace)).mapIso
            (derivedPullbackUnitIso (pullback.snd a b).toLRSHom.toShHom) ≪≫
        Stacks.RingedSpace.derivedTensorLeftUnitIso (pullback a b).toRingedSpace
          (unitObj (pullback a b).toRingedSpace))

open Stacks.Cohomology.DerivedSectionsLeray

/-- The cohomology modules `H^n(Spec k, E)` used below: `n`-th cohomology of the derived global
sections. -/
private abbrev H (k : Type u) [Field k] (n : ℤ)
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      (Spec (CommRingCat.of k)).toRingedSpace))) :
    ModuleCat.{u} (baseRing (Spec (CommRingCat.of k)).toRingedSpace) :=
  (DerivedCategory.homologyFunctor _ n).obj ((Stacks.Cohomology.GlobalKunneth.baseSections _).obj E)

/-- `H^n(Spec k, 𝒪) = 0` for `n ≥ 1`. -/
private theorem isZero_H_unitObj (k : Type u) [Field k] (n : ℕ) (hn : 0 < n) :
    IsZero (H k n (unitObj (Spec (CommRingCat.of k)).toRingedSpace)) :=
  (isZero_homology_baseSections_spec_field k n hn).of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso
      ((Stacks.Cohomology.GlobalKunneth.baseSections _).mapIso
        ((Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardIdIso _).app
          (unitObj _)).symm))

private theorem finrank_le_kunneth (k : Type u) [Field k]
    {X₀ X₁ : Scheme.{u}} (a : X₀ ⟶ Spec (CommRingCat.of k)) (b : X₁ ⟶ Spec (CommRingCat.of k))
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      (Spec (CommRingCat.of k)).toRingedSpace)))
    (eE : ((derivedTensorProductFunctor (Spec (CommRingCat.of k)).sheaf).obj
        ((derivedPushforward a.toLRSHom.toShHom).obj (unitObj X₀.toRingedSpace))).obj
      ((derivedPushforward b.toLRSHom.toShHom).obj (unitObj X₁.toRingedSpace)) ≅ E)
    (ha : IsIso (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom a.toLRSHom.toShHom)))
    (hb : IsIso (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom b.toLRSHom.toShHom)))
    [Module.Finite (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
      (H k 1 ((derivedPushforward a.toLRSHom.toShHom).obj (unitObj X₀.toRingedSpace)))]
    [Module.Finite (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
      (H k 1 ((derivedPushforward b.toLRSHom.toShHom).obj (unitObj X₁.toRingedSpace)))] :
    Module.Finite (baseRing (Spec (CommRingCat.of k)).toRingedSpace) (H k 1 E) ∧
      Module.finrank (baseRing (Spec (CommRingCat.of k)).toRingedSpace) (H k 1 E) ≤
        Module.finrank (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
          (H k 1 ((derivedPushforward a.toLRSHom.toShHom).obj (unitObj X₀.toRingedSpace))) +
        Module.finrank (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
          (H k 1 ((derivedPushforward b.toLRSHom.toShHom).obj (unitObj X₁.toRingedSpace))) := by
  let K := (Spec (CommRingCat.of k)).toRingedSpace
  let Γ := baseRing K
  let : Field Γ := IsField.toField <|
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)
  let A := (derivedPushforward a.toLRSHom.toShHom).obj (unitObj X₀.toRingedSpace)
  let B := (derivedPushforward b.toLRSHom.toShHom).obj (unitObj X₁.toRingedSpace)
  let t := derivedTensorProductFunctor (Spec (CommRingCat.of k)).sheaf
  obtain ⟨A', gA, hA, hTA⟩ := distinguished_cocone_triangle (structureUnit a.toLRSHom.toShHom)
  obtain ⟨B', gB, hB, hTB⟩ := distinguished_cocone_triangle (structureUnit b.toLRSHom.toShHom)
  have hunit : ∀ j : ℤ, j ≠ 0 → IsZero ((DerivedCategory.homologyFunctor _ j).obj (unitObj K)) := by
    intro j hj
    rcases lt_or_gt_of_ne hj with h | h
    · exact DerivedCategory.isZero_of_isGE (unitObj K) 0 j h
    · exact DerivedCategory.isZero_of_isLE (unitObj K) 0 j h
  have hGE : ∀ {Z : Scheme.{u}} (c : Z ⟶ Spec (CommRingCat.of k))
      (hc : IsIso (SheafOfModules.unitToPushforwardObjUnit (structureSheafHom c.toLRSHom.toShHom)))
      {C' : DerivedCategory (SheafOfModules.{u} (structureSheafRing K))} (g h),
      Triangle.mk (structureUnit c.toLRSHom.toShHom) g h ∈ distTriang _ → C'.IsGE 1 :=
    fun {Z} c hc _ _ _ hT => isGE_one_obj₃_of_isIso_homology_zero_mor₁ _ hT hunit
      (fun j hj => DerivedCategory.isZero_of_isGE _ 0 j hj
        (hX := isGE_derivedPushforward_obj_modules c _ 0
          (show (unitObj Z.toRingedSpace).IsGE 0 from inferInstance)))
      ((Stacks.Cohomology.DerivedStructureUnit.isIso_homology_structureUnit_iff _).2 hc)
  have hA' : A'.IsGE 1 := hGE a ha gA hA hTA
  have hB' : B'.IsGE 1 := hGE b hb gB hB hTB
  let D := canonicalDerivedTensorProduct (Spec (CommRingCat.of k)).sheaf
  let := D.commShift₂.commShiftFlipObj B
  have := D.exact_left B
  have hT₁ := (t.flip.obj B).map_distinguished _ hTA
  let := D.commShift₂.commShiftObj A'
  have := D.exact_right A'
  have hT₂ := (t.obj A').map_distinguished _ hTB
  let := Functor.IsRightDerivedFunctor.commShift (Stacks.Cohomology.GlobalKunneth.baseSections K)
    (derivedSectionsOverOpenUnit K ⊤)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing K)) (ComplexShape.up ℤ)) ℤ
  have : (Stacks.Cohomology.GlobalKunneth.baseSections K).IsTriangulated := by
    have _ := SheafOfModules.isGrothendieckAbelianU (structureSheafRing K)
    exact Stacks.Injectives.rightDerivedFunctor_isTriangulated (sectionsOverOpen K ⊤)
      (Stacks.Cohomology.GlobalKunneth.baseSections K) (derivedSectionsOverOpenUnit K ⊤)
  have hz₂ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ) 1).obj
      ((Stacks.Cohomology.GlobalKunneth.baseSections K).obj ((t.obj A').obj B'))) := by
    have h2 := isGE_derivedTensor_of_isField_stalks K (isField_stalk_Spec_field k) A' B' 1 1 hA' hB'
    have h3 := isGE_derivedSectionsOverOpen_obj K ⊤ _ 2 h2
    exact DerivedCategory.isZero_of_isGE _ 2 1 (by omega) (hX := h3)
  have hz₃ : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ) 2).obj
      ((Stacks.Cohomology.GlobalKunneth.baseSections K).obj (unitObj K))) := by
    exact isZero_H_unitObj k 2 (by omega)
  have : Module.Finite Γ ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ) 1).obj
      ((Stacks.Cohomology.GlobalKunneth.baseSections K).obj ((t.obj (unitObj K)).obj B))) :=
    Module.Finite.equiv ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ) 1).mapIso
      ((Stacks.Cohomology.GlobalKunneth.baseSections K).mapIso
        (Stacks.RingedSpace.derivedTensorLeftUnitIso K B))).toLinearEquiv.symm
  have i₁ : FiniteDimensional Γ ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ) 1).obj
      ((Stacks.Cohomology.GlobalKunneth.baseSections K).obj ((t.flip.obj B).mapTriangle.obj
        (Triangle.mk (structureUnit a.toLRSHom.toShHom) gA hA)).obj₁)) := by assumption
  have i₂ : FiniteDimensional Γ ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ) 1).obj
      ((Stacks.Cohomology.GlobalKunneth.baseSections K).obj
        (Triangle.mk (structureUnit a.toLRSHom.toShHom) gA hA).obj₂)) := by
    assumption
  obtain ⟨hfin, hle⟩ := finiteDimensional_and_finrank_le_of_three_triangles
    (Stacks.Cohomology.GlobalKunneth.baseSections K)
    ((t.flip.obj B).mapTriangle.obj (Triangle.mk (structureUnit a.toLRSHom.toShHom) gA hA))
    ((t.obj A').mapTriangle.obj (Triangle.mk (structureUnit b.toLRSHom.toShHom) gB hB))
    (Triangle.mk (structureUnit a.toLRSHom.toShHom) gA hA) hT₁ hT₂ hTA (Iso.refl _)
    (Stacks.RingedSpace.derivedTensorRightUnitIso K A').symm hz₂ hz₃
  let εE := ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ) 1).mapIso
    ((Stacks.Cohomology.GlobalKunneth.baseSections K).mapIso eE)).toLinearEquiv
  let εB := ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ) 1).mapIso
    ((Stacks.Cohomology.GlobalKunneth.baseSections K).mapIso
      (Stacks.RingedSpace.derivedTensorLeftUnitIso K B))).toLinearEquiv
  have : FiniteDimensional Γ ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ) 1).obj
      ((Stacks.Cohomology.GlobalKunneth.baseSections K).obj ((t.obj A).obj B))) := hfin
  refine ⟨Module.Finite.equiv εE, ?_⟩
  calc Module.finrank Γ (H k 1 E)
      = Module.finrank Γ (H k 1 ((t.obj A).obj B)) := εE.finrank_eq.symm
    _ ≤ Module.finrank Γ (H k 1 ((t.obj (unitObj K)).obj B)) + Module.finrank Γ (H k 1 A) := hle
    _ = Module.finrank Γ (H k 1 B) + Module.finrank Γ (H k 1 A) :=
      congrArg (· + Module.finrank Γ (H k 1 A)) εB.finrank_eq
    _ = _ := add_comm _ _

/-- A module whose restriction of scalars along a ring map is finite is finite. -/
private theorem moduleFinite_of_restrictScalars {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S)
    (M : ModuleCat.{u} S) [Module.Finite R ((ModuleCat.restrictScalars f).obj M)] :
    Module.Finite S M := by
  let : Algebra R S := f.toAlgebra
  let : Module R M := Module.compHom M f
  have : IsScalarTower R S M := ⟨fun c x m => mul_smul (f c) x m⟩
  have : Module.Finite R M := ‹Module.Finite R ((ModuleCat.restrictScalars f).obj M)›
  exact Module.Finite.of_restrictScalars_finite R S M

/-- **`H¹(X, 𝒪_X)` is finite dimensional** for `X` proper over a field, in the spelling of the
derived global sections of `Rq_* 𝒪_X` on the point. -/
private theorem finite_H_derivedPushforward_unit (k : Type u) [Field k] {Y : Scheme.{u}}
    (q : Y ⟶ Spec (CommRingCat.of k)) [IsProper q] (n : ℕ) :
    Module.Finite (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
      (H k n ((derivedPushforward q.toLRSHom.toShHom).obj (unitObj Y.toRingedSpace))) := by
  obtain ⟨e⟩ := nonempty_homology_baseSections_derivedPushforward_iso q
    (SheafOfModules.unit Y.ringCatSheaf) n
  have : IsLocallyNoetherian Y :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k q
  have : (SheafOfModules.unit Y.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_unit Y
  have hfin := finiteDimensional_cohomologyOverField_of_isProper k q
    (SheafOfModules.unit Y.ringCatSheaf) n
  replace hfin : Module.Finite k ((ModuleCat.restrictScalars (Stacks.Cech.globalRingHom q).hom).obj
      (((moduleGlobalSections Y).rightDerived n).obj (SheafOfModules.unit Y.ringCatSheaf))) :=
    cohomologyOverField_eq_restrictScalars_appTop k q (SheafOfModules.unit Y.ringCatSheaf) n ▸ hfin
  have : Module.Finite k
      ((ModuleCat.restrictScalars (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom).obj
        (H k n ((derivedPushforward q.toLRSHom.toShHom).obj (unitObj Y.toRingedSpace)))) :=
    Module.Finite.equiv e.toLinearEquiv.symm
  exact moduleFinite_of_restrictScalars (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom _

/-- The pushed-forward unit `Rc_*K ⟶ R(i ≫ c)_* Li^*K`. -/
private abbrev pm {T V W : RingedSpace.{u, u}} (c : V ⟶ T) (i : W ⟶ V)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) :
    (derivedPushforward c).obj K ⟶ (derivedPushforward (i ≫ c)).obj ((derivedPullback i).obj K) :=
  (derivedPushforward c).map ((derivedAdjunction i).unit.app K) ≫
    (derivedPushforwardCompIso i c).hom.app _

private theorem isIso_pm {T V W : RingedSpace.{u, u}} (c : V ⟶ T) (i : W ⟶ V) [IsIso i]
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) : IsIso (pm c i K) := by
  have := Stacks.DerivedPullback.isEquivalence_derivedPullback i (inv i) (IsIso.hom_inv_id i)
    (IsIso.inv_hom_id i)
  infer_instance

private theorem pm_naturality {T V W : RingedSpace.{u, u}} (c : V ⟶ T) (i : W ⟶ V)
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))} (φ : K ⟶ K') :
    (derivedPushforward c).map φ ≫ pm c i K' =
      pm c i K ≫ (derivedPushforward (i ≫ c)).map ((derivedPullback i).map φ) := by
  have h₂ := (derivedAdjunction i).unit.naturality φ
  have h₃ := (derivedPushforwardCompIso i c).hom.naturality ((derivedPullback i).map φ)
  simp only [Functor.comp_map, Functor.id_map] at h₂ h₃
  have s₂ := congrArg (derivedPushforward c).map h₂
  simp only [Functor.map_comp] at s₂
  simp only [pm, ← Category.assoc, s₂]
  simp only [Category.assoc, h₃]

private theorem pm_comp {T V W Z : RingedSpace.{u, u}} (c : V ⟶ T) (i : W ⟶ V) (j : Z ⟶ W)
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) :
    pm c i K ≫ pm (i ≫ c) j ((derivedPullback i).obj K) =
      pm c (j ≫ i) K ≫
        (derivedPushforward ((j ≫ i) ≫ c)).map ((derivedPullbackCompIsoCanonical j i).inv.app K) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.map_unit_comp_derivedPushforwardCompIso_comp
    c i j K

/-- The map `R(c₀)_* 𝒪 ⟶ Rc_* 𝒪` pulling back along `π : P ⟶ X₀` over `π ≫ c₀ = c`. -/
private abbrev pullUnit {T P X₀ : RingedSpace.{u, u}} (c : P ⟶ T) (c₀ : X₀ ⟶ T) (π : P ⟶ X₀)
    (hc : π ≫ c₀ = c) :
    (derivedPushforward c₀).obj (unitObj X₀) ⟶ (derivedPushforward c).obj (unitObj P) :=
  pm c₀ π (unitObj X₀) ≫ (derivedPushforward (π ≫ c₀)).map (derivedPullbackUnitIso π).hom ≫
    eqToHom (by rw [hc])

private theorem pullUnit_comp_pm {T P X₀ Z : RingedSpace.{u, u}} (c₀ : X₀ ⟶ T) (π : P ⟶ X₀)
    (j : Z ⟶ P) :
    pullUnit (π ≫ c₀) c₀ π rfl ≫ pm (π ≫ c₀) j (unitObj P) =
      (pm c₀ (j ≫ π) (unitObj X₀) ≫
        (derivedPushforward ((j ≫ π) ≫ c₀)).map
          ((derivedPullbackCompIsoCanonical j π).inv.app (unitObj X₀))) ≫
      (derivedPushforward (j ≫ π ≫ c₀)).map
        ((derivedPullback j).map (derivedPullbackUnitIso π).hom) := by
  calc pullUnit (π ≫ c₀) c₀ π rfl ≫ pm (π ≫ c₀) j (unitObj P)
      = pm c₀ π (unitObj X₀) ≫ ((derivedPushforward (π ≫ c₀)).map (derivedPullbackUnitIso π).hom ≫
          pm (π ≫ c₀) j (unitObj P)) := by
        simp only [pullUnit, eqToHom_refl, Category.comp_id, Category.assoc]
    _ = pm c₀ π (unitObj X₀) ≫ (pm (π ≫ c₀) j ((derivedPullback π).obj (unitObj X₀)) ≫
          (derivedPushforward (j ≫ π ≫ c₀)).map ((derivedPullback j).map
            (derivedPullbackUnitIso π).hom)) := congrArg _ (pm_naturality _ _ _)
    _ = (pm c₀ π (unitObj X₀) ≫ pm (π ≫ c₀) j ((derivedPullback π).obj (unitObj X₀))) ≫
          (derivedPushforward (j ≫ π ≫ c₀)).map ((derivedPullback j).map
            (derivedPullbackUnitIso π).hom) := (Category.assoc _ _ _).symm
    _ = _ := congrArg (· ≫ _) (pm_comp c₀ π j (unitObj X₀))

private theorem isIso_pullUnit_comp_pm {T P X₀ : RingedSpace.{u, u}} (c : P ⟶ T) (c₀ : X₀ ⟶ T)
    (π : P ⟶ X₀) (hc : π ≫ c₀ = c) (j : X₀ ⟶ P) [IsIso (j ≫ π)] :
    IsIso (pullUnit c c₀ π hc ≫ pm c j (unitObj P)) := by
  subst hc
  rw [pullUnit_comp_pm]
  have := isIso_pm c₀ (j ≫ π) (unitObj X₀)
  refine @IsIso.comp_isIso _ _ _ _ _ _ _ (@IsIso.comp_isIso _ _ _ _ _ _ _ this ?_) ?_
  · exact Functor.map_isIso _ _
  · exact Functor.map_isIso _ _

open Stacks.Cohomology.GlobalKunneth (baseRing)

/-- `H¹(Spec k, R d_* E) = 0` for `d = 𝟙` and `E ≅ 𝒪`. -/
private theorem isZero_H_derivedPushforward_of_eq_id (k : Type u) [Field k]
    (d : (Spec (CommRingCat.of k)).toRingedSpace ⟶ (Spec (CommRingCat.of k)).toRingedSpace)
    (hd : d = 𝟙 _) (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing
      (Spec (CommRingCat.of k)).toRingedSpace)))
    (eE : E ≅ unitObj (Spec (CommRingCat.of k)).toRingedSpace) :
    IsZero (H k 1 ((derivedPushforward d).obj E)) := by
  subst hd
  exact (isZero_H_unitObj k 1 (by omega)).of_iso
    ((DerivedCategory.homologyFunctor _ 1).mapIso
      ((Stacks.Cohomology.GlobalKunneth.baseSections _).mapIso
        ((Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardIdIso _).app E ≪≫
          eE)))

/-- **Pulling back along a map that factors through the point kills `H¹`.** -/
private theorem homology_map_pm_eq_zero (k : Type u) [Field k] {X₀ X' : RingedSpace.{u, u}}
    (c₀ : X₀ ⟶ (Spec (CommRingCat.of k)).toRingedSpace)
    (e : (Spec (CommRingCat.of k)).toRingedSpace ⟶ X₀) (he : e ≫ c₀ = 𝟙 _)
    (c' : X' ⟶ (Spec (CommRingCat.of k)).toRingedSpace) (d : X' ⟶ X₀) (hd : d = c' ≫ e) :
    (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (CommRingCat.of k)).toRingedSpace)) 1).map
        ((Stacks.Cohomology.GlobalKunneth.baseSections _).map (pm c₀ d (unitObj X₀))) = 0 := by
  subst hd
  let F := Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of k)).toRingedSpace ⋙
    DerivedCategory.homologyFunctor _ 1
  have h := congrArg F.map (pm_comp c₀ e c' (unitObj X₀))
  have hz : F.map (pm c₀ e (unitObj X₀)) = 0 :=
    (isZero_H_derivedPushforward_of_eq_id k (e ≫ c₀) he _ (derivedPullbackUnitIso e)).eq_of_tgt _ _
  have h2 : F.map (pm c₀ (c' ≫ e) (unitObj X₀)) ≫
      F.map ((derivedPushforward ((c' ≫ e) ≫ c₀)).map
        ((derivedPullbackCompIsoCanonical c' e).inv.app (unitObj X₀))) = 0 :=
    (F.map_comp _ _).symm.trans (h.symm.trans ((F.map_comp _ _).trans
      (by rw [hz]; exact zero_comp)))
  exact (Preadditive.IsIso.comp_right_eq_zero _ _).1 h2

private theorem homology_map_pullUnit_comp_pm_eq_zero (k : Type u) [Field k]
    {P X₀ X' : RingedSpace.{u, u}} (c : P ⟶ (Spec (CommRingCat.of k)).toRingedSpace)
    (c₀ : X₀ ⟶ (Spec (CommRingCat.of k)).toRingedSpace) (π : P ⟶ X₀) (hc : π ≫ c₀ = c)
    (e : (Spec (CommRingCat.of k)).toRingedSpace ⟶ X₀) (he : e ≫ c₀ = 𝟙 _)
    (c' : X' ⟶ (Spec (CommRingCat.of k)).toRingedSpace) (j : X' ⟶ P) (hj : j ≫ π = c' ≫ e) :
    (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (CommRingCat.of k)).toRingedSpace)) 1).map
        ((Stacks.Cohomology.GlobalKunneth.baseSections _).map
          (pullUnit c c₀ π hc ≫ pm c j (unitObj P))) = 0 := by
  subst hc
  let F := Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of k)).toRingedSpace ⋙
    DerivedCategory.homologyFunctor _ 1
  change F.map _ = 0
  have hz : F.map (pm c₀ (j ≫ π) (unitObj X₀)) = 0 :=
    homology_map_pm_eq_zero k c₀ e he c' (j ≫ π) hj
  rw [pullUnit_comp_pm]
  refine (F.map_comp _ _).trans ?_
  refine (congrArg (· ≫ _) (F.map_comp _ _)).trans ?_
  rw [hz, zero_comp, zero_comp]

private theorem eq_zero_of_pm (k : Type u) [Field k] {P X₀ X₁ : RingedSpace.{u, u}}
    (c : P ⟶ (Spec (CommRingCat.of k)).toRingedSpace)
    (c₀ : X₀ ⟶ (Spec (CommRingCat.of k)).toRingedSpace)
    (c₁ : X₁ ⟶ (Spec (CommRingCat.of k)).toRingedSpace)
    (π₀ : P ⟶ X₀) (π₁ : P ⟶ X₁) (hπ₀ : π₀ ≫ c₀ = c) (hπ₁ : π₁ ≫ c₁ = c)
    (j₀ : X₀ ⟶ P) (j₁ : X₁ ⟶ P) [IsIso (j₀ ≫ π₀)] [IsIso (j₁ ≫ π₁)]
    (e₀ : (Spec (CommRingCat.of k)).toRingedSpace ⟶ X₀)
    (e₁ : (Spec (CommRingCat.of k)).toRingedSpace ⟶ X₁)
    (he₀ : e₀ ≫ c₀ = 𝟙 _) (he₁ : e₁ ≫ c₁ = 𝟙 _)
    (h₁₀ : j₁ ≫ π₀ = c₁ ≫ e₀) (h₀₁ : j₀ ≫ π₁ = c₀ ≫ e₁)
    [Module.Finite (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
      (H k 1 ((derivedPushforward c₀).obj (unitObj X₀)))]
    [Module.Finite (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
      (H k 1 ((derivedPushforward c₁).obj (unitObj X₁)))]
    [Module.Finite (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
      (H k 1 ((derivedPushforward c).obj (unitObj P)))]
    (hdim : Module.finrank (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
        (H k 1 ((derivedPushforward c).obj (unitObj P))) ≤
      Module.finrank (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
          (H k 1 ((derivedPushforward c₀).obj (unitObj X₀))) +
        Module.finrank (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
          (H k 1 ((derivedPushforward c₁).obj (unitObj X₁))))
    (y : H k 1 ((derivedPushforward c).obj (unitObj P)))
    (hy₀ : ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (CommRingCat.of k)).toRingedSpace)) 1).map
      ((Stacks.Cohomology.GlobalKunneth.baseSections _).map (pm c j₀ (unitObj P)))).hom y = 0)
    (hy₁ : ((DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (CommRingCat.of k)).toRingedSpace)) 1).map
      ((Stacks.Cohomology.GlobalKunneth.baseSections _).map (pm c j₁ (unitObj P)))).hom y = 0) :
    y = 0 := by
  let : Field (baseRing (Spec (CommRingCat.of k)).toRingedSpace) := IsField.toField <|
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv.toMulEquiv.isField (Field.toIsField k)
  let F := Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of k)).toRingedSpace ⋙
    DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (CommRingCat.of k)).toRingedSpace)) 1
  have d : ∀ {Z : RingedSpace.{u, u}} (c' : Z ⟶ (Spec (CommRingCat.of k)).toRingedSpace)
      (π : P ⟶ Z) (hπ : π ≫ c' = c) (j : Z ⟶ P) [IsIso (j ≫ π)],
      IsIso (F.map (pullUnit c c' π hπ) ≫ F.map (pm c j (unitObj P))) := by
    intro Z c' π hπ j _
    rw [← F.map_comp]
    have := isIso_pullUnit_comp_pm c c' π hπ j
    exact Functor.map_isIso F _
  have x₁₀ : F.map (pullUnit c c₁ π₁ hπ₁) ≫ F.map (pm c j₀ (unitObj P)) = 0 :=
    (F.map_comp _ _).symm.trans
      (homology_map_pullUnit_comp_pm_eq_zero k c c₁ π₁ hπ₁ e₁ he₁ c₀ j₀ h₀₁)
  have x₀₁ : F.map (pullUnit c c₀ π₀ hπ₀) ≫ F.map (pm c j₁ (unitObj P)) = 0 :=
    (F.map_comp _ _).symm.trans
      (homology_map_pullUnit_comp_pm_eq_zero k c c₀ π₀ hπ₀ e₀ he₀ c₁ j₁ h₁₀)
  have : FiniteDimensional (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
      (F.obj ((derivedPushforward c₀).obj (unitObj X₀))) := by assumption
  have : FiniteDimensional (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
      (F.obj ((derivedPushforward c₁).obj (unitObj X₁))) := by assumption
  have : FiniteDimensional (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
      (F.obj ((derivedPushforward c).obj (unitObj P))) := by assumption
  exact eq_zero_of_split (F.map (pm c j₀ (unitObj P))) (F.map (pm c j₁ (unitObj P)))
    (F.map (pullUnit c c₀ π₀ hπ₀)) (F.map (pullUnit c c₁ π₁ hπ₁)) (d c₀ π₀ hπ₀ j₀)
    (d c₁ π₁ hπ₁ j₁) x₁₀ x₀₁ hdim y hy₀ hy₁

/-- The structure sheaf map of an isomorphism of schemes is an isomorphism. -/
private theorem isIso_structureSheafHom_of_isIso {X Y : Scheme.{u}} (e : X ⟶ Y) [IsIso e] :
    IsIso (structureSheafHom e.toLRSHom.toShHom) := by
  have := PresheafedSpace.c_isIso_of_iso e.toPshHom
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
  change IsIso (Functor.whiskerRight e.toLRSHom.toHom.c (forget₂ CommRingCat RingCat))
  infer_instance

private theorem isIso_structureSheafHom_comp {X Y Z : RingedSpace.{u, u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIso (structureSheafHom f)) (hg : IsIso (structureSheafHom g)) :
    IsIso (structureSheafHom (f ≫ g)) := by
  rw [structureSheafHom_comp]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hg (@Functor.map_isIso _ _ _ _ _ _ _ _ hf)

private theorem isIso_structureSheafHom_congr {X Y : Scheme.{u}} {φ ψ : X ⟶ Y} (h : φ = ψ)
    (hψ : IsIso (structureSheafHom ψ.toLRSHom.toShHom)) :
    IsIso (structureSheafHom φ.toLRSHom.toShHom) :=
  h ▸ hψ

/-- The universal invariance of the structure sheaf, `𝒪_T ≅ h_{T,*}𝒪`. -/
private abbrev UniversallyStructural {X S : Scheme.{u}} (h : X ⟶ S) : Prop :=
  ∀ {T : Scheme.{u}} (a : T ⟶ S), IsIso (structureSheafHom (pullback.snd h a).toLRSHom.toShHom)

private theorem isIso_structureSheafHom_comp_scheme {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsIso (structureSheafHom f.toLRSHom.toShHom))
    (hg : IsIso (structureSheafHom g.toLRSHom.toShHom)) :
    IsIso (structureSheafHom (f ≫ g).toLRSHom.toShHom) :=
  isIso_structureSheafHom_comp f.toLRSHom.toShHom g.toLRSHom.toShHom hf hg

private theorem universallyStructural_comp {X Y S : Scheme.{u}} (u : X ⟶ Y) (v : Y ⟶ S)
    (hu : UniversallyStructural u) (hv : UniversallyStructural v) :
    UniversallyStructural (u ≫ v) := by
  intro T a
  have h := (IsPullback.of_hasPullback u (pullback.fst v a)).paste_vert
    (IsPullback.of_hasPullback v a)
  have e : pullback.snd (u ≫ v) a = h.isoPullback.inv ≫
      (pullback.snd u (pullback.fst v a) ≫ pullback.snd v a) := h.isoPullback_inv_snd.symm
  refine isIso_structureSheafHom_congr e ?_
  refine isIso_structureSheafHom_comp_scheme _ _ (isIso_structureSheafHom_of_isIso _) ?_
  exact isIso_structureSheafHom_comp_scheme _ _ (hu _) (hv _)

private theorem universallyStructural_fst {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)
    (hg : UniversallyStructural g) : UniversallyStructural (pullback.fst f g) := by
  intro T a
  have h := (IsPullback.of_hasPullback (pullback.fst f g) a).paste_horiz
    (IsPullback.of_hasPullback f g).flip
  have e : pullback.snd (pullback.fst f g) a = h.isoPullback.hom ≫ pullback.snd g (a ≫ f) :=
    h.isoPullback_hom_snd.symm
  refine isIso_structureSheafHom_congr e ?_
  exact isIso_structureSheafHom_comp_scheme _ _ (isIso_structureSheafHom_of_isIso _) (hg _)

section Cube

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S)
  (τ : S ⟶ Y) (hτ : τ ≫ g = 𝟙 S) {K : Scheme.{u}} (κ : K ⟶ S)
  (i₀ : X ⟶ pullback f g) (h₀₁ : i₀ ≫ pullback.fst f g = 𝟙 X)
  (h₀₂ : i₀ ≫ pullback.snd f g = f ≫ τ)
  (i₁ : Y ⟶ pullback f g) (h₁₁ : i₁ ≫ pullback.fst f g = g ≫ σ)
  (h₁₂ : i₁ ≫ pullback.snd f g = 𝟙 Y)

include h₀₁ in
private theorem i₀_p : i₀ ≫ (pullback.fst f g ≫ f) = f :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) h₀₁).trans (Category.id_comp f))

include h₁₁ hσ in
private theorem i₁_p : i₁ ≫ (pullback.fst f g ≫ f) = g :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) h₁₁).trans
    ((Category.assoc _ _ _).trans ((congrArg (g ≫ ·) hσ).trans (Category.comp_id g))))

/-- The projection `P_s ⟶ X_{0,s}`. -/
private abbrev π₀ : pullback (pullback.fst f g ≫ f) κ ⟶ pullback (i₀ ≫ (pullback.fst f g ≫ f)) κ :=
  pullback.lift (pullback.fst _ κ ≫ pullback.fst f g) (pullback.snd _ κ)
    ((congrArg (_ ≫ ·) (i₀_p f g i₀ h₀₁)).trans
      ((Category.assoc _ _ _).trans pullback.condition))

/-- The projection `P_s ⟶ X_{1,s}`. -/
private abbrev π₁ : pullback (pullback.fst f g ≫ f) κ ⟶ pullback (i₁ ≫ (pullback.fst f g ≫ f)) κ :=
  pullback.lift (pullback.fst _ κ ≫ pullback.snd f g) (pullback.snd _ κ)
    ((congrArg (_ ≫ ·) (i₁_p f g σ hσ i₁ h₁₁)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg (pullback.fst (pullback.fst f g ≫ f) κ ≫ ·) pullback.condition.symm).trans
          pullback.condition)))

/-- The section `Spec κ(s) ⟶ X_{0,s}` induced by `σ`. -/
private abbrev e₀ : K ⟶ pullback (i₀ ≫ (pullback.fst f g ≫ f)) κ :=
  pullback.lift (κ ≫ σ) (𝟙 K) ((congrArg (_ ≫ ·) (i₀_p f g i₀ h₀₁)).trans
    ((Category.assoc _ _ _).trans ((congrArg (κ ≫ ·) hσ).trans
      ((Category.comp_id κ).trans (Category.id_comp κ).symm))))

/-- The section `Spec κ(s) ⟶ X_{1,s}` induced by `τ`. -/
private abbrev e₁ : K ⟶ pullback (i₁ ≫ (pullback.fst f g ≫ f)) κ :=
  pullback.lift (κ ≫ τ) (𝟙 K) ((congrArg (_ ≫ ·) (i₁_p f g σ hσ i₁ h₁₁)).trans
    ((Category.assoc _ _ _).trans ((congrArg (κ ≫ ·) hτ).trans
      ((Category.comp_id κ).trans (Category.id_comp κ).symm))))

/-- The face `X_{0,s} ⟶ P_s`. -/
private abbrev j₀ : pullback (i₀ ≫ (pullback.fst f g ≫ f)) κ ⟶ pullback (pullback.fst f g ≫ f) κ :=
  pullback.map _ κ _ κ i₀ (𝟙 _) (𝟙 _) (by simp) (by simp)

/-- The face `X_{1,s} ⟶ P_s`. -/
private abbrev j₁ : pullback (i₁ ≫ (pullback.fst f g ≫ f)) κ ⟶ pullback (pullback.fst f g ≫ f) κ :=
  pullback.map _ κ _ κ i₁ (𝟙 _) (𝟙 _) (by simp) (by simp)

private theorem j₀_fst : j₀ f g κ i₀ ≫ pullback.fst _ κ = pullback.fst _ κ ≫ i₀ :=
  pullback.lift_fst _ _ _

private theorem j₀_snd : j₀ f g κ i₀ ≫ pullback.snd _ κ = pullback.snd _ κ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

private theorem j₁_fst : j₁ f g κ i₁ ≫ pullback.fst _ κ = pullback.fst _ κ ≫ i₁ :=
  pullback.lift_fst _ _ _

private theorem j₁_snd : j₁ f g κ i₁ ≫ pullback.snd _ κ = pullback.snd _ κ :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

include h₀₁ in
private theorem j₀_π₀ : j₀ f g κ i₀ ≫ π₀ f g κ i₀ h₀₁ = 𝟙 _ := by
  apply pullback.hom_ext
  · calc (j₀ f g κ i₀ ≫ π₀ f g κ i₀ h₀₁) ≫ pullback.fst _ κ
        = j₀ f g κ i₀ ≫ (pullback.fst _ κ ≫ pullback.fst f g) :=
          (Category.assoc _ _ _).trans (congrArg _ (pullback.lift_fst _ _ _))
      _ = (pullback.fst _ κ ≫ i₀) ≫ pullback.fst f g :=
          (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (j₀_fst f g κ i₀))
      _ = 𝟙 _ ≫ pullback.fst _ κ :=
          (Category.assoc _ _ _).trans ((congrArg _ h₀₁).trans
            ((Category.comp_id _).trans (Category.id_comp _).symm))
  · calc (j₀ f g κ i₀ ≫ π₀ f g κ i₀ h₀₁) ≫ pullback.snd _ κ
        = j₀ f g κ i₀ ≫ pullback.snd _ κ :=
          (Category.assoc _ _ _).trans (congrArg _ (pullback.lift_snd _ _ _))
      _ = 𝟙 _ ≫ pullback.snd _ κ := (j₀_snd f g κ i₀).trans (Category.id_comp _).symm

include h₁₂ in
private theorem j₁_π₁ : j₁ f g κ i₁ ≫ π₁ f g σ hσ κ i₁ h₁₁ = 𝟙 _ := by
  apply pullback.hom_ext
  · calc (j₁ f g κ i₁ ≫ π₁ f g σ hσ κ i₁ h₁₁) ≫ pullback.fst _ κ
        = j₁ f g κ i₁ ≫ (pullback.fst _ κ ≫ pullback.snd f g) :=
          (Category.assoc _ _ _).trans (congrArg _ (pullback.lift_fst _ _ _))
      _ = (pullback.fst _ κ ≫ i₁) ≫ pullback.snd f g :=
          (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (j₁_fst f g κ i₁))
      _ = 𝟙 _ ≫ pullback.fst _ κ :=
          (Category.assoc _ _ _).trans ((congrArg _ h₁₂).trans
            ((Category.comp_id _).trans (Category.id_comp _).symm))
  · calc (j₁ f g κ i₁ ≫ π₁ f g σ hσ κ i₁ h₁₁) ≫ pullback.snd _ κ
        = j₁ f g κ i₁ ≫ pullback.snd _ κ :=
          (Category.assoc _ _ _).trans (congrArg _ (pullback.lift_snd _ _ _))
      _ = 𝟙 _ ≫ pullback.snd _ κ := (j₁_snd f g κ i₁).trans (Category.id_comp _).symm

include h₀₁ h₁₁ in
private theorem j₁_π₀ : j₁ f g κ i₁ ≫ π₀ f g κ i₀ h₀₁ =
    pullback.snd _ κ ≫ e₀ f g σ hσ κ i₀ h₀₁ := by
  apply pullback.hom_ext
  · calc (j₁ f g κ i₁ ≫ π₀ f g κ i₀ h₀₁) ≫ pullback.fst _ κ
        = j₁ f g κ i₁ ≫ (pullback.fst _ κ ≫ pullback.fst f g) :=
          (Category.assoc _ _ _).trans (congrArg _ (pullback.lift_fst _ _ _))
      _ = (pullback.fst _ κ ≫ i₁) ≫ pullback.fst f g :=
          (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (j₁_fst f g κ i₁))
      _ = (pullback.fst _ κ ≫ g) ≫ σ :=
          (Category.assoc _ _ _).trans ((congrArg _ h₁₁).trans (Category.assoc _ _ _).symm)
      _ = (pullback.fst _ κ ≫ (i₁ ≫ (pullback.fst f g ≫ f))) ≫ σ :=
          congrArg (fun z => (pullback.fst (i₁ ≫ (pullback.fst f g ≫ f)) κ ≫ z) ≫ σ)
            (i₁_p f g σ hσ i₁ h₁₁).symm
      _ = (pullback.snd _ κ ≫ κ) ≫ σ := congrArg (· ≫ σ) pullback.condition
      _ = (pullback.snd _ κ ≫ e₀ f g σ hσ κ i₀ h₀₁) ≫ pullback.fst _ κ :=
          (Category.assoc _ _ _).trans ((congrArg _ (pullback.lift_fst _ _ _).symm).trans
            (Category.assoc _ _ _).symm)
  · calc (j₁ f g κ i₁ ≫ π₀ f g κ i₀ h₀₁) ≫ pullback.snd _ κ
        = j₁ f g κ i₁ ≫ pullback.snd _ κ :=
          (Category.assoc _ _ _).trans (congrArg _ (pullback.lift_snd _ _ _))
      _ = (pullback.snd _ κ ≫ e₀ f g σ hσ κ i₀ h₀₁) ≫ pullback.snd _ κ :=
          (j₁_snd f g κ i₁).trans ((Category.comp_id _).symm.trans
            ((congrArg _ (pullback.lift_snd _ _ _).symm).trans (Category.assoc _ _ _).symm))

include h₀₁ h₀₂ h₁₁ in
private theorem j₀_π₁ : j₀ f g κ i₀ ≫ π₁ f g σ hσ κ i₁ h₁₁ =
    pullback.snd _ κ ≫ e₁ f g σ hσ τ hτ κ i₁ h₁₁ := by
  apply pullback.hom_ext
  · calc (j₀ f g κ i₀ ≫ π₁ f g σ hσ κ i₁ h₁₁) ≫ pullback.fst _ κ
        = j₀ f g κ i₀ ≫ (pullback.fst _ κ ≫ pullback.snd f g) :=
          (Category.assoc _ _ _).trans (congrArg _ (pullback.lift_fst _ _ _))
      _ = (pullback.fst _ κ ≫ i₀) ≫ pullback.snd f g :=
          (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (j₀_fst f g κ i₀))
      _ = (pullback.fst _ κ ≫ f) ≫ τ :=
          (Category.assoc _ _ _).trans ((congrArg _ h₀₂).trans (Category.assoc _ _ _).symm)
      _ = (pullback.fst _ κ ≫ (i₀ ≫ (pullback.fst f g ≫ f))) ≫ τ :=
          congrArg (fun z => (pullback.fst (i₀ ≫ (pullback.fst f g ≫ f)) κ ≫ z) ≫ τ)
            (i₀_p f g i₀ h₀₁).symm
      _ = (pullback.snd _ κ ≫ κ) ≫ τ := congrArg (· ≫ τ) pullback.condition
      _ = (pullback.snd _ κ ≫ e₁ f g σ hσ τ hτ κ i₁ h₁₁) ≫ pullback.fst _ κ :=
          (Category.assoc _ _ _).trans ((congrArg _ (pullback.lift_fst _ _ _).symm).trans
            (Category.assoc _ _ _).symm)
  · calc (j₀ f g κ i₀ ≫ π₁ f g σ hσ κ i₁ h₁₁) ≫ pullback.snd _ κ
        = j₀ f g κ i₀ ≫ pullback.snd _ κ :=
          (Category.assoc _ _ _).trans (congrArg _ (pullback.lift_snd _ _ _))
      _ = (pullback.snd _ κ ≫ e₁ f g σ hσ τ hτ κ i₁ h₁₁) ≫ pullback.snd _ κ :=
          (j₀_snd f g κ i₀).trans ((Category.comp_id _).symm.trans
            ((congrArg _ (pullback.lift_snd _ _ _).symm).trans (Category.assoc _ _ _).symm))

/-- `P_s ⟶ X_{0,s} ×_{κ(s)} X_{1,s}`. -/
private abbrev toProd :
    pullback (pullback.fst f g ≫ f) κ ⟶
      pullback (pullback.snd (i₀ ≫ (pullback.fst f g ≫ f)) κ)
        (pullback.snd (i₁ ≫ (pullback.fst f g ≫ f)) κ) :=
  pullback.lift (π₀ f g κ i₀ h₀₁) (π₁ f g σ hσ κ i₁ h₁₁)
    ((pullback.lift_snd _ _ _).trans (pullback.lift_snd _ _ _).symm)

include h₀₁ h₁₁ hσ in
private theorem prod_cond :
    (pullback.fst (pullback.snd (i₀ ≫ (pullback.fst f g ≫ f)) κ)
        (pullback.snd (i₁ ≫ (pullback.fst f g ≫ f)) κ) ≫
      pullback.fst (i₀ ≫ (pullback.fst f g ≫ f)) κ) ≫ f =
    (pullback.snd (pullback.snd (i₀ ≫ (pullback.fst f g ≫ f)) κ)
        (pullback.snd (i₁ ≫ (pullback.fst f g ≫ f)) κ) ≫
      pullback.fst (i₁ ≫ (pullback.fst f g ≫ f)) κ) ≫ g :=
  (Category.assoc _ _ _).trans
    ((congrArg (_ ≫ ·) ((congrArg (_ ≫ ·) (i₀_p f g i₀ h₀₁).symm).trans pullback.condition)).trans
      ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ κ) pullback.condition).trans
        ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
          (pullback.condition.symm.trans (congrArg (_ ≫ ·) (i₁_p f g σ hσ i₁ h₁₁)))).trans
            (Category.assoc _ _ _).symm)))))

/-- The inverse `X_{0,s} ×_{κ(s)} X_{1,s} ⟶ P_s`. -/
private abbrev fromProd :
    pullback (pullback.snd (i₀ ≫ (pullback.fst f g ≫ f)) κ)
        (pullback.snd (i₁ ≫ (pullback.fst f g ≫ f)) κ) ⟶
      pullback (pullback.fst f g ≫ f) κ :=
  pullback.lift (pullback.lift _ _ (prod_cond f g σ hσ κ i₀ h₀₁ i₁ h₁₁))
    (pullback.fst _ _ ≫ pullback.snd (i₀ ≫ (pullback.fst f g ≫ f)) κ)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ f) (pullback.lift_fst _ _ _)).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·)
        ((congrArg (_ ≫ ·) (i₀_p f g i₀ h₀₁).symm).trans pullback.condition)).trans
          (Category.assoc _ _ _).symm))))

private theorem toProd_fromProd :
    toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · calc ((toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁) ≫
            pullback.fst _ κ) ≫ pullback.fst f g
          = toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ (pullback.fst _ _ ≫
              pullback.fst (i₀ ≫ (pullback.fst f g ≫ f)) κ) := by
            rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst]
        _ = π₀ f g κ i₀ h₀₁ ≫ pullback.fst (i₀ ≫ (pullback.fst f g ≫ f)) κ :=
            (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_fst _ _ _))
        _ = (𝟙 _ ≫ pullback.fst _ κ) ≫ pullback.fst f g := by
            rw [pullback.lift_fst, Category.id_comp]
    · calc ((toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁) ≫
            pullback.fst _ κ) ≫ pullback.snd f g
          = toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ (pullback.snd _ _ ≫
              pullback.fst (i₁ ≫ (pullback.fst f g ≫ f)) κ) := by
            rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd]
        _ = π₁ f g σ hσ κ i₁ h₁₁ ≫ pullback.fst (i₁ ≫ (pullback.fst f g ≫ f)) κ :=
            (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_snd _ _ _))
        _ = (𝟙 _ ≫ pullback.fst _ κ) ≫ pullback.snd f g := by
            rw [pullback.lift_fst, Category.id_comp]
  · calc (toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁) ≫
          pullback.snd _ κ
        = toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ (pullback.fst _ _ ≫
            pullback.snd (i₀ ≫ (pullback.fst f g ≫ f)) κ) := by
          rw [Category.assoc, pullback.lift_snd]
      _ = π₀ f g κ i₀ h₀₁ ≫ pullback.snd (i₀ ≫ (pullback.fst f g ≫ f)) κ :=
          (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) (pullback.lift_fst _ _ _))
      _ = 𝟙 _ ≫ pullback.snd _ κ := by rw [pullback.lift_snd, Category.id_comp]

private theorem fromProd_toProd :
    fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ = 𝟙 _ := by
  apply pullback.hom_ext
  · apply pullback.hom_ext
    · calc ((fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁) ≫
            pullback.fst _ _) ≫ pullback.fst (i₀ ≫ (pullback.fst f g ≫ f)) κ
          = fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ (pullback.fst _ κ ≫ pullback.fst f g) := by
            rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc, pullback.lift_fst]
        _ = (𝟙 _ ≫ pullback.fst _ _) ≫ pullback.fst (i₀ ≫ (pullback.fst f g ≫ f)) κ :=
            (Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ pullback.fst f g) (pullback.lift_fst _ _ _)).trans
                ((pullback.lift_fst _ _ _).trans
                  (congrArg (· ≫ pullback.fst (i₀ ≫ (pullback.fst f g ≫ f)) κ)
                    (Category.id_comp _).symm)))
    · calc ((fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁) ≫
            pullback.fst _ _) ≫ pullback.snd (i₀ ≫ (pullback.fst f g ≫ f)) κ
          = fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ pullback.snd _ κ := by
            rw [Category.assoc, Category.assoc, pullback.lift_fst_assoc, pullback.lift_snd]
        _ = (𝟙 _ ≫ pullback.fst _ _) ≫ pullback.snd (i₀ ≫ (pullback.fst f g ≫ f)) κ := by
            rw [pullback.lift_snd, Category.id_comp]
  · apply pullback.hom_ext
    · calc ((fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁) ≫
            pullback.snd _ _) ≫ pullback.fst (i₁ ≫ (pullback.fst f g ≫ f)) κ
          = fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ (pullback.fst _ κ ≫ pullback.snd f g) := by
            rw [Category.assoc, Category.assoc, pullback.lift_snd_assoc, pullback.lift_fst]
        _ = (𝟙 _ ≫ pullback.snd _ _) ≫ pullback.fst (i₁ ≫ (pullback.fst f g ≫ f)) κ :=
            (Category.assoc _ _ _).symm.trans
              ((congrArg (· ≫ pullback.snd f g) (pullback.lift_fst _ _ _)).trans
                ((pullback.lift_snd _ _ _).trans
                  (congrArg (· ≫ pullback.fst (i₁ ≫ (pullback.fst f g ≫ f)) κ)
                    (Category.id_comp _).symm)))
    · calc ((fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁) ≫
            pullback.snd _ _) ≫ pullback.snd (i₁ ≫ (pullback.fst f g ≫ f)) κ
          = fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁ ≫ pullback.snd _ κ := by
            rw [Category.assoc, Category.assoc, pullback.lift_snd_assoc, pullback.lift_snd]
        _ = pullback.fst _ _ ≫ pullback.snd (i₀ ≫ (pullback.fst f g ≫ f)) κ :=
            pullback.lift_snd _ _ _
        _ = (𝟙 _ ≫ pullback.snd _ _) ≫ pullback.snd (i₁ ≫ (pullback.fst f g ≫ f)) κ :=
            pullback.condition.trans (congrArg (· ≫ pullback.snd (i₁ ≫ (pullback.fst f g ≫ f)) κ)
              (Category.id_comp _).symm)

private theorem isIso_toProd : IsIso (toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁) :=
  ⟨fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁, toProd_fromProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁,
    fromProd_toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁⟩

end Cube

/-! ### The pullback map on derived global sections through the pushed-forward unit -/

open Stacks.Cohomology.GlobalKunneth (sectionsOverBase lerayIso sectionsPullbackMap) in
private theorem homology_map_sectionsPullbackMap {T V W : RingedSpace.{u, u}} (c : V ⟶ T)
    (i : W ⟶ V) (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V))) (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing T)) n).map
        (sectionsPullbackMap c i K) =
      (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing T)) n).map
          ((lerayIso c).inv.app K) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing T)) n).map
          ((Stacks.Cohomology.GlobalKunneth.baseSections T).map (pm c i K)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing T)) n).map
          ((lerayIso (i ≫ c)).hom.app ((derivedPullback i).obj K)) := by
  simp only [sectionsPullbackMap, pm, Functor.map_comp, Category.assoc]

open Stacks.Cohomology.GlobalKunneth (sectionsOverBase lerayIso sectionsPullbackMap) in
private theorem homology_map_pm_apply_eq_zero {T V W : RingedSpace.{u, u}} (c : V ⟶ T)
    (j : W ⟶ V) (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V)))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing T)) 1).obj
      ((sectionsOverBase c).obj K))
    (hj : ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing T)) 1).map
      (sectionsPullbackMap c j K)).hom x = 0) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing T)) 1).map
      ((Stacks.Cohomology.GlobalKunneth.baseSections T).map (pm c j K))).hom
        (((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing T)) 1).map
          ((lerayIso c).inv.app K)).hom x) = 0 := by
  rw [homology_map_sectionsPullbackMap, ModuleCat.hom_comp, ModuleCat.hom_comp,
    LinearMap.comp_apply, LinearMap.comp_apply] at hj
  have hinj : Function.Injective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing T)) 1).map
        ((lerayIso (j ≫ c)).hom.app ((derivedPullback j).obj K))).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  exact hinj (by rwa [map_zero])

open Stacks.Cohomology.GlobalKunneth (sectionsOverBase lerayIso) in
private theorem eq_zero_of_homology_lerayIso_inv_apply_eq_zero {T V : RingedSpace.{u, u}}
    (c : V ⟶ T) (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing V)))
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing T)) 1).obj
      ((sectionsOverBase c).obj K))
    (hx : ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing T)) 1).map
          ((lerayIso c).inv.app K)).hom x = 0) : x = 0 := by
  have hinj : Function.Injective
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing T)) 1).map
        ((lerayIso c).inv.app K)).hom :=
    (ConcreteCategory.bijective_of_isIso _).1
  exact hinj (by rwa [map_zero])

/-- If `a ≫ b = 𝟙` for scheme maps, the composite of the underlying ringed-space maps is an
isomorphism. -/
private theorem isIso_toShHom_comp_of_comp_eq_id {X Y : Scheme.{u}} (a : X ⟶ Y) (b : Y ⟶ X)
    (h : a ≫ b = 𝟙 X) : IsIso (a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom) :=
  show IsIso ((a ≫ b).toLRSHom.toShHom) by
    rw [h]
    exact inferInstanceAs (IsIso (𝟙 _))

/-- The Künneth bound on `H¹` of a fibre product of proper schemes over a field, transported
along an isomorphism `ψ : P ≅ X₀ ×_k X₁`. -/
private theorem finite_and_finrank_le_of_isIso (k : Type u) [Field k] {P X₀ X₁ : Scheme.{u}}
    (a : X₀ ⟶ Spec (CommRingCat.of k)) (b : X₁ ⟶ Spec (CommRingCat.of k)) [IsProper a]
    [IsProper b] (ψ : P ⟶ pullback a b) [IsIso ψ] (c : P ⟶ Spec (CommRingCat.of k))
    (hψ : ψ ≫ pullback.fst a b ≫ a = c)
    (ha : IsIso (_root_.SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom a.toLRSHom.toShHom)))
    (hb : IsIso (_root_.SheafOfModules.unitToPushforwardObjUnit
      (structureSheafHom b.toLRSHom.toShHom))) :
    Module.Finite (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
        (H k 1 ((derivedPushforward c.toLRSHom.toShHom).obj (unitObj P.toRingedSpace))) ∧
      Module.finrank (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
          (H k 1 ((derivedPushforward c.toLRSHom.toShHom).obj (unitObj P.toRingedSpace))) ≤
        Module.finrank (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
            (H k 1 ((derivedPushforward a.toLRSHom.toShHom).obj (unitObj X₀.toRingedSpace))) +
          Module.finrank (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
            (H k 1 ((derivedPushforward b.toLRSHom.toShHom).obj (unitObj X₁.toRingedSpace))) := by
  have := finite_H_derivedPushforward_unit k a 1
  have := finite_H_derivedPushforward_unit k b 1
  obtain ⟨hfinE, hleE⟩ := finrank_le_kunneth k a b _
    (kunnethUnitIso a b (torIndependent_of_isField_stalk _ _ (isField_stalk_Spec_field k))) ha hb
  have hψ' : ψ.toLRSHom.toShHom ≫ (pullback.fst a b ≫ a).toLRSHom.toShHom = c.toLRSHom.toShHom :=
    congrArg (fun z => (Scheme.Hom.toLRSHom z).toShHom) hψ
  have : IsIso ψ.toLRSHom.toShHom := Functor.map_isIso LocallyRingedSpace.forgetToSheafedSpace _
  let F := Stacks.Cohomology.GlobalKunneth.baseSections (Spec (CommRingCat.of k)).toRingedSpace ⋙
    DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (CommRingCat.of k)).toRingedSpace)) 1
  have : IsIso (pullUnit _ _ _ hψ') := by
    have := isIso_pm (pullback.fst a b ≫ a).toLRSHom.toShHom ψ.toLRSHom.toShHom
      (unitObj (pullback a b).toRingedSpace)
    infer_instance
  let εV := (asIso (F.map (pullUnit _ _ _ hψ'))).toLinearEquiv
  have : Module.Finite (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
      (F.obj ((derivedPushforward (pullback.fst a b ≫ a).toLRSHom.toShHom).obj
        (unitObj (pullback a b).toRingedSpace))) := hfinE
  exact ⟨Module.Finite.equiv εV, εV.finrank_eq.symm.trans_le hleE⟩

/-! ### The injectivity over a field -/

open Stacks.Cohomology.GlobalKunneth (sectionsOverBase lerayIso sectionsPullbackMap) in
private theorem eq_zero_of_faces_aux
    (k : Type u) [Field k] {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsProper f]
    [IsProper g]
    (hfO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f a).toLRSHom.toShHom))
    (hgO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd g a).toLRSHom.toShHom))
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (τ : S ⟶ Y) (hτ : τ ≫ g = 𝟙 S)
    (κ : Spec (CommRingCat.of k) ⟶ S)
    (i₀ : X ⟶ pullback f g) (h₀₁ : i₀ ≫ pullback.fst f g = 𝟙 X)
    (h₀₂ : i₀ ≫ pullback.snd f g = f ≫ τ)
    (i₁ : Y ⟶ pullback f g) (h₁₁ : i₁ ≫ pullback.fst f g = g ≫ σ)
    (h₁₂ : i₁ ≫ pullback.snd f g = 𝟙 Y)
    (x : (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (CommRingCat.of k)).toRingedSpace)) 1).obj
        ((sectionsOverBase (pullback.snd (pullback.fst f g ≫ f) κ).toLRSHom.toShHom).obj
          (unitObj (pullback (pullback.fst f g ≫ f) κ).toRingedSpace)))
    (hx₀ : ((DerivedCategory.homologyFunctor _ 1).map
      (sectionsPullbackMap (pullback.snd (pullback.fst f g ≫ f) κ).toLRSHom.toShHom
        (j₀ f g κ i₀).toLRSHom.toShHom
        (unitObj (pullback (pullback.fst f g ≫ f) κ).toRingedSpace))).hom x = 0)
    (hx₁ : ((DerivedCategory.homologyFunctor _ 1).map
      (sectionsPullbackMap (pullback.snd (pullback.fst f g ≫ f) κ).toLRSHom.toShHom
        (j₁ f g κ i₁).toLRSHom.toShHom
        (unitObj (pullback (pullback.fst f g ≫ f) κ).toRingedSpace))).hom x = 0) :
    x = 0 := by
  let p := pullback.fst f g ≫ f
  let c := (pullback.snd p κ).toLRSHom.toShHom
  let c₀ := (pullback.snd (i₀ ≫ p) κ).toLRSHom.toShHom
  let c₁ := (pullback.snd (i₁ ≫ p) κ).toLRSHom.toShHom
  have hπ₀ : (π₀ f g κ i₀ h₀₁).toLRSHom.toShHom ≫ c₀ = c :=
    congrArg (fun z => (Scheme.Hom.toLRSHom z).toShHom)
      (show π₀ f g κ i₀ h₀₁ ≫ pullback.snd _ κ = pullback.snd p κ from pullback.lift_snd _ _ _)
  have hπ₁ : (π₁ f g σ hσ κ i₁ h₁₁).toLRSHom.toShHom ≫ c₁ = c :=
    congrArg (fun z => (Scheme.Hom.toLRSHom z).toShHom)
      (show π₁ f g σ hσ κ i₁ h₁₁ ≫ pullback.snd _ κ = pullback.snd p κ from
        pullback.lift_snd _ _ _)
  have he₀ : (e₀ f g σ hσ κ i₀ h₀₁).toLRSHom.toShHom ≫ c₀ = 𝟙 _ :=
    congrArg (fun z => (Scheme.Hom.toLRSHom z).toShHom)
      (show e₀ f g σ hσ κ i₀ h₀₁ ≫ pullback.snd _ κ = 𝟙 _ from pullback.lift_snd _ _ _)
  have he₁ : (e₁ f g σ hσ τ hτ κ i₁ h₁₁).toLRSHom.toShHom ≫ c₁ = 𝟙 _ :=
    congrArg (fun z => (Scheme.Hom.toLRSHom z).toShHom)
      (show e₁ f g σ hσ τ hτ κ i₁ h₁₁ ≫ pullback.snd _ κ = 𝟙 _ from pullback.lift_snd _ _ _)
  have h₁₀ : (j₁ f g κ i₁).toLRSHom.toShHom ≫ (π₀ f g κ i₀ h₀₁).toLRSHom.toShHom =
      c₁ ≫ (e₀ f g σ hσ κ i₀ h₀₁).toLRSHom.toShHom :=
    congrArg (fun z => (Scheme.Hom.toLRSHom z).toShHom) (j₁_π₀ f g σ hσ κ i₀ h₀₁ i₁ h₁₁) |>.trans
      rfl
  have h₀₁' : (j₀ f g κ i₀).toLRSHom.toShHom ≫ (π₁ f g σ hσ κ i₁ h₁₁).toLRSHom.toShHom =
      c₀ ≫ (e₁ f g σ hσ τ hτ κ i₁ h₁₁).toLRSHom.toShHom :=
    congrArg (fun z => (Scheme.Hom.toLRSHom z).toShHom) (j₀_π₁ f g σ hσ τ hτ κ i₀ h₀₁ h₀₂ i₁ h₁₁)
  have := isIso_toShHom_comp_of_comp_eq_id _ _ (j₀_π₀ f g κ i₀ h₀₁)
  have := isIso_toShHom_comp_of_comp_eq_id _ _ (j₁_π₁ f g σ hσ κ i₁ h₁₁ h₁₂)
  have face : ∀ {Z : Scheme.{u}} (q : Z ⟶ S) [IsProper q], UniversallyStructural q →
      Module.Finite (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
        (H k 1 ((derivedPushforward (pullback.snd q κ).toLRSHom.toShHom).obj
          (unitObj (pullback q κ).toRingedSpace))) ∧
      IsIso (_root_.SheafOfModules.unitToPushforwardObjUnit
        (structureSheafHom (pullback.snd q κ).toLRSHom.toShHom)) := by
    intro Z q _ hO
    have := hO κ
    exact ⟨finite_H_derivedPushforward_unit k (pullback.snd q κ) 1,
      Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit _⟩
  have : IsProper (i₀ ≫ p) := by
    rw [i₀_p f g i₀ h₀₁]
    infer_instance
  have : IsProper (i₁ ≫ p) := by
    rw [i₁_p f g σ hσ i₁ h₁₁]
    infer_instance
  obtain ⟨fin₀, ha⟩ := face (i₀ ≫ p) (by rwa [i₀_p f g i₀ h₀₁])
  obtain ⟨fin₁, hb⟩ := face (i₁ ≫ p) (by rwa [i₁_p f g σ hσ i₁ h₁₁])
  have := isIso_toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁
  obtain ⟨hfin, hdim⟩ := finite_and_finrank_le_of_isIso k (pullback.snd (i₀ ≫ p) κ)
    (pullback.snd (i₁ ≫ p) κ) (toProd f g σ hσ κ i₀ h₀₁ i₁ h₁₁) (pullback.snd p κ)
    ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ pullback.snd (i₀ ≫ p) κ)
      (pullback.lift_fst _ _ _)).trans (pullback.lift_snd _ _ _))) ha hb
  have : Module.Finite (baseRing (Spec (CommRingCat.of k)).toRingedSpace)
      (H k 1 ((derivedPushforward c).obj (unitObj (pullback p κ).toRingedSpace))) := hfin
  have hy := eq_zero_of_pm k c c₀ c₁ _ _ hπ₀ hπ₁ _ _ _ _ he₀ he₁ h₁₀ h₀₁' hdim _
    (homology_map_pm_apply_eq_zero c _ _ x hx₀) (homology_map_pm_apply_eq_zero c _ _ x hx₁)
  exact eq_zero_of_homology_lerayIso_inv_apply_eq_zero c _ x hy

open Stacks.Cohomology.GlobalKunneth (sectionsOverBase sectionsPullbackMap) in
/-- **`H¹` of the fibre of a product injects into the faces.** Let `f : X ⟶ S` and `g : Y ⟶ S`
be proper with `𝒪_T ≅ f_{T,*}𝒪` and `𝒪_T ≅ g_{T,*}𝒪` after every base change, with sections `σ`
of `f` and `τ` of `g`, let `p : X ×_S Y ⟶ S` and let `s ∈ S`. Then a class in
`H¹(P_s, 𝒪)`, `P_s` the fibre of `p` over `s`, which pulls back to zero on both faces
`X_s ⟶ P_s` (from `x ↦ (x, τ(f(x)))`) and `Y_s ⟶ P_s` (from `y ↦ (σ(g(y)), y)`) is zero.

This is the injectivity `H¹(X_s ×_{κ(s)} Y_s, 𝒪) ⟶ H¹(X_s, 𝒪) ⊕ H¹(Y_s, 𝒪)` in the proof of
[Stacks, Tag 0BF3], with `H¹` the degree-one cohomology of
`Stacks.Cohomology.GlobalKunneth.sectionsOverBase` and the pullback maps
`Stacks.Cohomology.GlobalKunneth.sectionsPullbackMap`. -/
theorem eq_zero_of_sectionsPullbackMap_faces
    {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) [IsProper f] [IsProper g]
    (hfO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f a).toLRSHom.toShHom))
    (hgO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd g a).toLRSHom.toShHom))
    (σ : S ⟶ X) (hσ : σ ≫ f = 𝟙 S) (τ : S ⟶ Y) (hτ : τ ≫ g = 𝟙 S) (s : S)
    (x : (DerivedCategory.homologyFunctor
      (ModuleCat.{u} (baseRing (Spec (S.residueField s)).toRingedSpace)) 1).obj
        ((sectionsOverBase (pullback.snd (pullback.fst f g ≫ f)
          (S.fromSpecResidueField s)).toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (_root_.SheafOfModules.unit (structureSheafRing
              (pullback (pullback.fst f g ≫ f) (S.fromSpecResidueField s)).toRingedSpace))))))
    (hx₀ : ((DerivedCategory.homologyFunctor _ 1).map
      (sectionsPullbackMap (pullback.snd (pullback.fst f g ≫ f)
          (S.fromSpecResidueField s)).toLRSHom.toShHom
        (pullback.map (pullback.lift (𝟙 X) (f ≫ τ) ((Category.id_comp f).trans
            ((Category.comp_id f).symm.trans
              ((congrArg (f ≫ ·) hτ).symm.trans (Category.assoc f τ g).symm))) ≫
            (pullback.fst f g ≫ f)) (S.fromSpecResidueField s) (pullback.fst f g ≫ f)
          (S.fromSpecResidueField s) (pullback.lift (𝟙 X) (f ≫ τ) ((Category.id_comp f).trans
            ((Category.comp_id f).symm.trans
              ((congrArg (f ≫ ·) hτ).symm.trans (Category.assoc f τ g).symm))))
          (𝟙 _) (𝟙 _) (Category.comp_id _)
          ((Category.comp_id _).trans (Category.id_comp _).symm)).toLRSHom.toShHom
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (structureSheafRing
            (pullback (pullback.fst f g ≫ f) (S.fromSpecResidueField s)).toRingedSpace)))))).hom
        x = 0)
    (hx₁ : ((DerivedCategory.homologyFunctor _ 1).map
      (sectionsPullbackMap (pullback.snd (pullback.fst f g ≫ f)
          (S.fromSpecResidueField s)).toLRSHom.toShHom
        (pullback.map (pullback.lift (g ≫ σ) (𝟙 Y) ((Category.assoc g σ f).trans
            ((congrArg (g ≫ ·) hσ).trans
              ((Category.comp_id g).trans (Category.id_comp g).symm))) ≫
            (pullback.fst f g ≫ f)) (S.fromSpecResidueField s) (pullback.fst f g ≫ f)
          (S.fromSpecResidueField s) (pullback.lift (g ≫ σ) (𝟙 Y) ((Category.assoc g σ f).trans
            ((congrArg (g ≫ ·) hσ).trans
              ((Category.comp_id g).trans (Category.id_comp g).symm))))
          (𝟙 _) (𝟙 _) (Category.comp_id _)
          ((Category.comp_id _).trans (Category.id_comp _).symm)).toLRSHom.toShHom
        (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
          (_root_.SheafOfModules.unit (structureSheafRing
            (pullback (pullback.fst f g ≫ f) (S.fromSpecResidueField s)).toRingedSpace)))))).hom
        x = 0) :
    x = 0 :=
  eq_zero_of_faces_aux (S.residueField s) f g hfO hgO σ hσ τ hτ
    (S.fromSpecResidueField s) _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
    _ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) x hx₀ hx₁

/-- **The universal invariance of the structure sheaf passes to a fibre product.** If
`𝒪_T ≅ f_{T,*}𝒪` and `𝒪_T ≅ g_{T,*}𝒪` after every base change `T ⟶ S`, then the same holds for
`X ×_S Y ⟶ S`. -/
theorem isIso_structureSheafHom_pullback_snd_fst_comp {S X Y : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ S)
    (hfO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f a).toLRSHom.toShHom))
    (hgO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd g a).toLRSHom.toShHom))
    {T : Scheme.{u}} (a : T ⟶ S) :
    IsIso (structureSheafHom (pullback.snd (pullback.fst f g ≫ f) a).toLRSHom.toShHom) :=
  universallyStructural_comp _ _ (universallyStructural_fst f g hgO) hfO a

end AlgebraicGeometry.KunnethFirstCohomology

end
