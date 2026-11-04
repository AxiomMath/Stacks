module

public import Mathlib.RingTheory.Flat.Stability
public import StacksFrontier.Homology.Perfect.Defs
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
public import StacksFrontier.Homology.TorAmplitude.DerivedComparison
public import StacksFrontier.Homology.TorAmplitude.Module
public import StacksFrontier.Homology.TorAmplitude.Triangle
public import StacksFrontier.RingTheory.CompleteIntersection.FieldExtension
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Defs
public import StacksFrontier.RingTheory.Ideal.RegularIdealOfLocallyFreeConormal
public import StacksFrontier.RingTheory.NaiveCotangent.Cocartesian
public import StacksFrontier.RingTheory.NaiveCotangent.Defs
public import StacksFrontier.RingTheory.PseudoCoherentMap.Flat
public import StacksFrontier.RingTheory.PseudoCoherentMap.PerfectPresentation
public import StacksFrontier.RingTheory.Regular.Quasiregular
public import StacksFrontier.RingTheory.NaiveCotangent.ConormalFiniteProjective
public import StacksFrontier.RingTheory.Syntomic.Defs
import all StacksFrontier.RingTheory.NaiveCotangent.Cocartesian
import all StacksFrontier.RingTheory.NaiveCotangent.DerivedBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The naive cotangent complex of a local complete intersection

Let `A → B` be a local complete intersection. This file proves that the naive cotangent complex
`NL_{B/A}`, regarded as an object of the derived category of `B`-modules, is perfect and has
Tor amplitude in `[-1, 0]`.

For a *perfect* homomorphism of Noetherian rings this is a characterization: `NL_{B/A}` has Tor
amplitude in `[-1, 0]` exactly when it is a perfect object of `D(B)` with that Tor amplitude, and
exactly when `A → B` is a local complete intersection.

For a *flat* homomorphism of finite presentation the same four conditions are equivalent, with
no Noetherian hypothesis, and they say that `A → B` is syntomic.

## Main results

* `NaiveCotangent.naiveCotangentComplex_isPerfect_and_hasTorAmplitude`: the naive cotangent
  complex of a local complete intersection is perfect with Tor amplitude in `[-1, 0]`.
* `NaiveCotangent.hasTorAmplitude_tfae_isLocalCompleteIntersection`: the characterization for a
  perfect homomorphism of Noetherian rings.
* `NaiveCotangent.hasTorAmplitude_tfae_syntomic`: the characterization for a flat homomorphism of
  finite presentation.

## Implementation notes

The two-term complex `I/I² → Ω` is represented cohomologically by the mapping cone of the same
map between complexes concentrated in degree zero, so that its conormal term sits in degree `-1`
and its cotangent-space term in degree `0`; that object of the derived category is
`NaiveCotangent.naiveCotangentObject`.

Tor amplitude is taken relative to a derived tensor product supplied together with a comparison to
termwise tensoring and the universal property making each `- ⊗ᴸ M[0]` a total left derived functor.
The modules of `NL_{B/A}` live in `Type (max u v)` while `B` lives in `Type v`; the comparison is
moved to `ULift.{u} B`, which shares a universe with its modules, along the change of coefficient
ring `StacksDraft.TorAmplitude.scalarLift`.

In `NaiveCotangent.hasTorAmplitude_tfae_isLocalCompleteIntersection` and
`NaiveCotangent.hasTorAmplitude_tfae_syntomic`, Tor amplitude and perfectness of the ring map are
evaluated at the canonical derived tensor product, so source and target share a universe.

## References

* [The Stacks Project, Lemma 15.88.1 (0FV0)](https://stacks.math.columbia.edu/tag/0FV0)
* [The Stacks Project, Lemma 23.9.4 (0FJT)](https://stacks.math.columbia.edu/tag/0FJT)
* [The Stacks Project, Lemma 23.11.5 (0FJV)](https://stacks.math.columbia.edu/tag/0FJV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits CategoryTheory.Functor
open StacksDraft.TorAmplitude
open scoped TensorProduct

namespace NaiveCotangent

universe u v u₁ w

attribute [local instance] HasDerivedCategory.standard

/-! ### The naive cotangent complex as an object of the derived category -/

/-- The naive cotangent complex `NL_{B/A}`, regarded as an object of `D(B)`, with the conormal
module in cohomological degree `-1` and the cotangent-space module in degree `0`. -/
public noncomputable abbrev naiveCotangentObject (A : Type u) (B : Type v)
    [CommRing A] [CommRing B] [Algebra A B] :
    DerivedCategory (ModuleCat.{max u v} B) :=
  DerivedCategory.Q.obj
    (CochainComplex.mappingCone
      ((CochainComplex.singleFunctor (ModuleCat.{max u v} B) 0).map
        (ModuleCat.ofHom (NL (canonicalGenerators A B)).d)))

/-! ### Comparison with the termwise tensor product at independent universes -/

section Comparison

variable {R : Type u} [CommRing R]

private instance :
    ((scalarLift.{u, v} (R := R)).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
      (ComplexShape.up ℤ)).functor.IsEquivalence :=
  inferInstanceAs
    ((scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ)).IsEquivalence

private instance : ((scalarLift.{u, v} (R := R)).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).IsInduced where
  inverseImage_eq := by
    ext K L f
    exact HomologicalComplex.quasiIso_map_iff_of_preservesHomology f (scalarLift.{u, v} (R := R))

private instance : ((scalarLift.{u, v} (R := R)).mapHomologicalComplexUpToQuasiIsoLocalizerMorphism
    (ComplexShape.up ℤ)).IsLocalizedEquivalence :=
  LocalizerMorphism.isLocalizedEquivalence_of_isInduced _

/-- Termwise tensoring by `M` commutes with the change of coefficient ring, on complexes and
after localization: the left-hand side is termwise tensoring over the lifted ring applied to the
transported complex, the right-hand side the transport of termwise tensoring over `R`. -/
private noncomputable def tensorScalarLiftComplexIso (M : ModuleCat.{max u v} R) :
    (scalarLift.{u, v} (R := R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        ((tensorModuleRight ((scalarLift.{u, v} (R := R)).obj M)).mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ≅
      ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙
        (scalarLift.{u, v} (R := R)).mapDerivedCategory :=
  isoWhiskerRight
      ((Functor.mapHomologicalComplexCompIso
          (Iso.refl (scalarLift.{u, v} (R := R) ⋙
            tensorModuleRight ((scalarLift.{u, v} (R := R)).obj M))) (ComplexShape.up ℤ)) ≪≫
        NatIso.mapHomologicalComplex (tensorScalarLiftIso M).symm (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso
          (Iso.refl (tensorModuleRight M ⋙ scalarLift.{u, v} (R := R)))
          (ComplexShape.up ℤ)).symm)
      DerivedCategory.Q ≪≫
    isoWhiskerLeft ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ))
      (scalarLift.{u, v} (R := R)).mapDerivedCategoryFactors.symm

variable
  {derivedTensor : DerivedCategory (ModuleCat.{max u v} R) ⥤
      DerivedCategory (ModuleCat.{max u v} R) ⥤ DerivedCategory (ModuleCat.{max u v} R)}

/-- The comparison map of a certified derived tensor product is invertible at a bounded above
complex of flat modules, with the ring universe and the module universe independent. -/
private theorem isIso_comparison_app_of_bounded_flat
    (comparison : ∀ M : ModuleCat.{max u v} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{max u v} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)))
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ)
    (hbounded : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (K.X i))
    (hflat : ∀ i : ℤ, Module.Flat R (K.X i)) (M : ModuleCat.{max u v} R) :
    IsIso ((comparison M).app K) := by
  have := isLeftDerived M
  let G := scalarLift.{u, v} (R := R)
  let Gd := G.mapDerivedCategory
  let Φ := G.mapHomologicalComplexUpToQuasiIsoLocalizerMorphism (ComplexShape.up ℤ)
  let N := G.obj M
  let L := derivedTensor.flip.obj
    ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)
  let W := HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)
  let F₂ := (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q
  let α₂ := termwiseDerivedCounit N
  let iso : Φ.functor ⋙ DerivedCategory.Q ≅ DerivedCategory.Q ⋙ Gd :=
    G.mapDerivedCategoryFactors.symm
  let α₁ : DerivedCategory.Q ⋙ (Gd ⋙ termwiseDerived N) ⟶ Φ.functor ⋙ F₂ :=
    whiskerRight iso.inv (termwiseDerived N) ≫ whiskerLeft Φ.functor α₂
  let αL : DerivedCategory.Q ⋙ (L ⋙ Gd) ⟶
      ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ Gd :=
    (Functor.associator _ _ _).inv ≫ whiskerRight (comparison M) Gd
  have h₁ : (Gd ⋙ termwiseDerived N).IsLeftDerivedFunctor α₁ W :=
    (Φ.isLeftDerivedFunctor_iff_precomp DerivedCategory.Q DerivedCategory.Q Gd iso α₁ α₂
      (Iso.refl _) (Iso.refl _) (by ext X; simp [α₁])).mp inferInstance
  have hL : (L ⋙ Gd).IsLeftDerivedFunctor αL W := inferInstance
  have hα₂ : IsIso (α₂.app ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) := by
    have hflat' : ∀ i : ℤ, Module.Flat (ULift.{v} R)
        (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X i) := by
      intro i
      show Module.Flat (ULift.{v} R) (K.X i)
      rw [Module.Flat.ulift_left_iff]
      exact hflat i
    have hbounded' : ∃ n : ℤ, ∀ i : ℤ, n < i →
        IsZero (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).X i) := by
      obtain ⟨n, hn⟩ := hbounded
      exact ⟨n, fun i hi => G.map_isZero (hn i hi)⟩
    exact isIso_termwiseDerivedCounit_app_of_flat N _ hbounded' hflat'
  have hα₁ : IsIso (α₁.app K) := by
    have : IsIso (α₂.app (Φ.functor.obj K)) := hα₂
    exact inferInstanceAs
      (IsIso ((termwiseDerived N).map (iso.inv.app K) ≫ α₂.app (Φ.functor.obj K)))
  let τ : (Φ.functor ⋙ F₂) ≅
      ((tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q) ⋙ Gd :=
    tensorScalarLiftComplexIso M
  let e := Functor.leftDerivedNatIso (Gd ⋙ termwiseDerived N) (L ⋙ Gd) α₁ αL W τ
  have he : e.hom.app (DerivedCategory.Q.obj K) ≫ αL.app K = α₁.app K ≫ τ.hom.app K := by
    simp [e, Functor.leftDerivedNatIso]
  have hcomp : IsIso (e.hom.app (DerivedCategory.Q.obj K) ≫ αL.app K) := by
    rw [he]
    have := hα₁
    infer_instance
  have hαL : IsIso (αL.app K) :=
    IsIso.of_isIso_comp_left (e.hom.app (DerivedCategory.Q.obj K)) (αL.app K)
  have hmap : IsIso (Gd.map ((comparison M).app K)) := by
    have hrw : αL.app K = Gd.map ((comparison M).app K) := by simp [αL]
    rw [← hrw]
    exact hαL
  exact isIso_of_reflects_iso ((comparison M).app K) Gd

/-- A bounded complex of flat modules has Tor amplitude in the interval given by its strict
bounds, for any certified derived tensor product and at independent universes. -/
@[sga "6 I 5.8.4" "special case"]
private theorem hasTorAmplitude_of_bounded_flat
    (comparison : ∀ M : ModuleCat.{max u v} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{max u v} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (ComplexShape.up ℤ)))
    (K : CochainComplex (ModuleCat.{max u v} R) ℤ) (a b : ℤ)
    (hGE : K.IsStrictlyGE a) (hLE : K.IsStrictlyLE b)
    (hflat : ∀ i : ℤ, Module.Flat R (K.X i)) :
    HasTorAmplitude derivedTensor comparison isLeftDerived (DerivedCategory.Q.obj K) a b := by
  intro M i hi
  have hi' : i < a ∨ b < i := by simpa only [Set.mem_Icc, not_and_or, not_le] using hi
  have hz : IsZero (K.X i) := by
    rcases hi' with hi' | hi'
    · exact (CochainComplex.isStrictlyGE_iff K a).1 hGE i hi'
    · exact (CochainComplex.isStrictlyLE_iff K b).1 hLE i hi'
  have hbounded : ∃ n : ℤ, ∀ j : ℤ, n < j → IsZero (K.X j) :=
    ⟨b, (CochainComplex.isStrictlyLE_iff K b).1 hLE⟩
  have hiso := isIso_comparison_app_of_bounded_flat comparison isLeftDerived K hbounded hflat M
  have hzt : IsZero ((((tensorModuleRight M).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj K).homology i) :=
    ((HomologicalComplex.ExactAt.of_isZero
      ((tensorModuleRight M).map_isZero hz)).isZero_homology)
  refine (hzt.of_iso ?_)
  exact (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).mapIso
      (asIso ((comparison M).app K)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{max u v} R) i).app _

end Comparison

/-! ### Mapping cones of two-term complexes -/

section MappingCones

open CochainComplex CochainComplex.HomComplex

variable {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
  {F G F' G' : CochainComplex C ℤ}

/-- A homotopy of arrows induces a homotopy of their mapping-cone maps. -/
private noncomputable def mappingConeMapHomotopy
    (φ : F ⟶ G) (ψ : F' ⟶ G')
    (a a' : F ⟶ F') (b b' : G ⟶ G')
    (w : φ ≫ b = a ≫ ψ) (w' : φ ≫ b' = a' ≫ ψ)
    (h : G ⟶ F') (ha : a - a' = φ ≫ h) (hb : b - b' = h ≫ ψ) :
    Homotopy (mappingCone.map φ ψ a b w) (mappingCone.map φ ψ a' b' w') := by
  apply mappingCone.descHomotopy _ _ _ 0
    ((Cochain.ofHom h).comp (mappingCone.inl ψ) (zero_add _))
  · rw [sub_eq_iff_eq_add] at ha
    simp [mappingCone.map, ha, Cochain.ofHom_comp]
  · rw [sub_eq_iff_eq_add] at hb
    simp [mappingCone.map, hb, Cochain.ofHom_comp]

/-- Homotopy inverse squares give homotopy equivalent mapping cones. -/
private noncomputable def mappingConeHomotopyEquiv
    (φ : F ⟶ G) (ψ : F' ⟶ G')
    (a : F ⟶ F') (b : G ⟶ G') (a' : F' ⟶ F) (b' : G' ⟶ G)
    (w : φ ≫ b = a ≫ ψ) (w' : ψ ≫ b' = a' ≫ φ)
    (h : G ⟶ F) (k : G' ⟶ F')
    (ha : a ≫ a' - 𝟙 F = φ ≫ h) (hb : b ≫ b' - 𝟙 G = h ≫ φ)
    (ha' : a' ≫ a - 𝟙 F' = ψ ≫ k) (hb' : b' ≫ b - 𝟙 G' = k ≫ ψ) :
    HomotopyEquiv (mappingCone φ) (mappingCone ψ) where
  hom := mappingCone.map φ ψ a b w
  inv := mappingCone.map ψ φ a' b' w'
  homotopyHomInvId :=
    (Homotopy.ofEq (mappingCone.map_comp φ ψ φ a b w a' b' w').symm).trans
      ((mappingConeMapHomotopy φ φ (a ≫ a') (𝟙 F) (b ≫ b') (𝟙 G)
        _ (by simp) h ha hb).trans (Homotopy.ofEq (mappingCone.map_id φ)))
  homotopyInvHomId :=
    (Homotopy.ofEq (mappingCone.map_comp ψ φ ψ a' b' w' a b w).symm).trans
      ((mappingConeMapHomotopy ψ ψ (a' ≫ a) (𝟙 F') (b' ≫ b) (𝟙 G')
        _ (by simp) k ha' hb').trans (Homotopy.ofEq (mappingCone.map_id ψ)))

end MappingCones

/-! ### The two-term cochain model -/

/-- The cohomological realization of a differential of modules, as the mapping cone of that map
between complexes concentrated in degree zero. -/
private noncomputable abbrev twoTermComplex {R : Type*} [Ring R]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (d : M →ₗ[R] N) : CochainComplex (ModuleCat.{v} R) ℤ :=
  CochainComplex.mappingCone
    ((CochainComplex.singleFunctor (ModuleCat.{v} R) 0).map (ModuleCat.ofHom d))

set_option backward.isDefEq.respectTransparency false in
/-- Realizing a two-term homotopy equivalence, allowing a smaller source module. -/
private theorem twoTermComplex_iso_of_homotopyEquiv
    {R : Type u} [CommRing R]
    (T : TwoTerm.{u, u₁, max u₁ w} R)
    (T' : TwoTerm.{u, max u₁ w, max u₁ w} R)
    (f : ChainMap T T') (hf : IsHomotopyEquiv f) :
    Nonempty (DerivedCategory.Q.obj
      (twoTermComplex (T.d.comp
        (ULift.moduleEquiv : ULift.{w} T.X₁ ≃ₗ[R] T.X₁).toLinearMap)) ≅
      DerivedCategory.Q.obj (twoTermComplex T'.d)) := by
  obtain ⟨g, ⟨h, h₁, h₀⟩, ⟨k, k₁, k₀⟩⟩ := hf
  let E : ULift.{w} T.X₁ ≃ₗ[R] T.X₁ := ULift.moduleEquiv
  let S := CochainComplex.singleFunctor (ModuleCat.{max u₁ w} R) 0
  let φ := S.map (ModuleCat.ofHom (T.d.comp E.toLinearMap))
  let ψ := S.map (ModuleCat.ofHom T'.d)
  let a := S.map (ModuleCat.ofHom (f.f₁.comp E.toLinearMap))
  let b := S.map (ModuleCat.ofHom f.f₀)
  let a' := S.map (ModuleCat.ofHom (E.symm.toLinearMap.comp g.f₁))
  let b' := S.map (ModuleCat.ofHom g.f₀)
  let H := S.map (ModuleCat.ofHom (E.symm.toLinearMap.comp h))
  let K := S.map (ModuleCat.ofHom k)
  have he : HomotopyEquiv (CochainComplex.mappingCone φ)
      (CochainComplex.mappingCone ψ) := by
    refine mappingConeHomotopyEquiv φ ψ a b a' b' ?_ ?_ H K ?_ ?_ ?_ ?_
    all_goals dsimp [φ, ψ, a, b, a', b', H, K]
    all_goals simp only [← S.map_comp, ← S.map_sub, ← S.map_id]
    all_goals congr 1; apply ModuleCat.hom_ext; ext x
    · simpa [E, LinearMap.comp_apply] using (LinearMap.congr_fun f.comm (E x)).symm
    · simpa [E, LinearMap.comp_apply] using (LinearMap.congr_fun g.comm x).symm
    · simpa [E, ChainMap.comp, ChainMap.id] using
        congrArg ULift.up.{w} (LinearMap.congr_fun h₁ (E x))
    · simpa [E, ChainMap.comp, ChainMap.id] using LinearMap.congr_fun h₀ x
    · simpa [E, ChainMap.comp, ChainMap.id] using LinearMap.congr_fun k₁ x
    · simpa [E, ChainMap.comp, ChainMap.id] using LinearMap.congr_fun k₀ x
  exact ⟨(DerivedCategory.quotientCompQhIso _).symm.app _ ≪≫
    DerivedCategory.Qh.mapIso (HomotopyCategory.isoOfHomotopyEquiv he) ≪≫
    (DerivedCategory.quotientCompQhIso _).app _⟩

/-- Every term of a single complex inherits finite projectivity. -/
private theorem single_finite_projective {R : Type u} [Ring R]
    (M : ModuleCat.{v} R) [Module.Finite R M] [Module.Projective R M] (j i : ℤ) :
    Module.Finite R (((CochainComplex.singleFunctor (ModuleCat.{v} R) j).obj M).X i) ∧
      Module.Projective R (((CochainComplex.singleFunctor (ModuleCat.{v} R) j).obj M).X i) := by
  by_cases hi : i = j
  · subst i
    let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) j M).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Projective.of_equiv e.symm⟩
  · have hz := HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) j M i hi
    let : Subsingleton (((CochainComplex.singleFunctor (ModuleCat.{v} R) j).obj M).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    exact ⟨inferInstance, inferInstance⟩

/-- A two-term complex is concentrated in degrees `-1` and `0`. -/
private theorem twoTermComplex_isStrictlyGE_and_isStrictlyLE {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (d : M →ₗ[R] N) :
    (twoTermComplex d).IsStrictlyGE (-1) ∧ (twoTermComplex d).IsStrictlyLE 0 := by
  have hz (i : ℤ) (hi : i < -1 ∨ 0 < i) : IsZero ((twoTermComplex d).X i) :=
    (CochainComplex.mappingCone.isZero_X_iff _ i).2
      ⟨HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega),
        HomologicalComplex.isZero_single_obj_X _ _ _ _ (by omega)⟩
  exact ⟨(CochainComplex.isStrictlyGE_iff _ _).2 (fun i hi => hz i (.inl hi)),
    (CochainComplex.isStrictlyLE_iff _ _).2 (fun i hi => hz i (.inr hi))⟩

/-- A two-term complex of finite projective modules is bounded and termwise finite projective. -/
private theorem twoTermComplex_finite_projective {R : Type u} [Ring R]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (d : M →ₗ[R] N) :
    (twoTermComplex d).IsStrictlyGE (-1) ∧ (twoTermComplex d).IsStrictlyLE 0 ∧
      (∀ i, Module.Finite R ((twoTermComplex d).X i)) ∧
      (∀ i, Module.Projective R ((twoTermComplex d).X i)) := by
  let S := CochainComplex.singleFunctor (ModuleCat.{v} R) 0
  have ht (i : ℤ) : Module.Finite R ((twoTermComplex d).X i) ∧
      Module.Projective R ((twoTermComplex d).X i) := by
    obtain ⟨_, _⟩ := single_finite_projective (ModuleCat.of R M) 0 (i + 1)
    obtain ⟨_, _⟩ := single_finite_projective (ModuleCat.of R N) 0 i
    let e := (HomologicalComplex.homotopyCofiber.XIsoBiprod
      (S.map (ModuleCat.ofHom d)) i (i + 1) rfl) ≪≫
        ModuleCat.biprodIsoProd _ _
    exact ⟨Module.Finite.equiv e.toLinearEquiv.symm,
      Module.Projective.of_equiv e.toLinearEquiv.symm⟩
  exact ⟨(twoTermComplex_isStrictlyGE_and_isStrictlyLE d).1,
    (twoTermComplex_isStrictlyGE_and_isStrictlyLE d).2, fun i => (ht i).1, fun i => (ht i).2⟩

/-- The two-term complex of a presentation is isomorphic in the derived category to the naive
cotangent complex. -/
private theorem twoTermComplex_cotangentComplex_iso
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    {ι : Type} (P : Algebra.Generators A B ι) :
    Nonempty (DerivedCategory.Q.obj (twoTermComplex (P.toExtension.cotangentComplex.comp
      (ULift.moduleEquiv :
        ULift.{v} P.toExtension.Cotangent ≃ₗ[B] P.toExtension.Cotangent).toLinearMap)) ≅
      naiveCotangentObject A B) :=
  twoTermComplex_iso_of_homotopyEquiv (NL P) (NL (canonicalGenerators A B))
    (nlMap P _ (P.defaultHom _))
    (nlMap_isHomotopyEquiv_and_isQuasiIso
      (R := A) (R' := A) (S := B) (S' := B)
      (by simpa using Function.bijective_id) (by simpa using Function.bijective_id)
      P _ (P.defaultHom _)).1

/-! ### Perfectness of the naive cotangent complex -/

/-- The naive cotangent complex of a local complete intersection is perfect and
has Tor-amplitude in `[-1, 0]`. -/
@[stacks 0FV0, sga "6 0 4.4" "affine case"]
public theorem naiveCotangentComplex_isPerfect_and_hasTorAmplitude
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (h : RingHom.IsLocalCompleteIntersection (algebraMap A B))
    (derivedTensor :
      DerivedCategory (ModuleCat.{max u v} B) ⥤
        DerivedCategory (ModuleCat.{max u v} B) ⥤
          DerivedCategory (ModuleCat.{max u v} B))
    (comparison : ∀ M : ModuleCat.{max u v} B,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{max u v} B,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{max u v} B) (ComplexShape.up ℤ))) :
    StacksDraft.Perfect.IsPerfect (naiveCotangentObject A B) ∧
      HasTorAmplitude derivedTensor comparison isLeftDerived
        (naiveCotangentObject A B) (-1) 0 := by
  classical
  rw [RingHom.IsLocalCompleteIntersection, toAlgebra_algebraMap] at h
  obtain ⟨_, n, p, hp, hreg⟩ := h
  have heval : MvPolynomial.aeval (fun i => p (MvPolynomial.X i)) = p := by
    ext i
    simp
  let P : Algebra.Generators A B (Fin n) :=
    Algebra.Generators.ofSurjective (fun i => p (MvPolynomial.X i)) (by rwa [heval])
  have hP : Quasiregular.IsQuasiregularIdeal' P.toExtension.ker := by
    apply Ideal.IsKoszulRegular.isQuasiregular
    show Ideal.IsKoszulRegular P.ker
    rw [Algebra.Generators.ker_eq_ker_aeval_val]
    show Ideal.IsKoszulRegular
      (RingHom.ker (MvPolynomial.aeval (R := A) (fun i => p (MvPolynomial.X i))).toRingHom)
    rwa [heval]
  obtain ⟨hfin, hproj⟩ :=
    Algebra.Extension.cotangent_finite_projective_of_quasiregular P.toExtension hP
  let : Module.Finite B P.toExtension.Cotangent := hfin
  let : Module.Projective B P.toExtension.Cotangent := hproj
  let : Module.Finite B P.toExtension.CotangentSpace :=
    Module.Finite.of_basis P.cotangentSpaceBasis
  let : Module.Projective B P.toExtension.CotangentSpace :=
    Module.Projective.of_basis P.cotangentSpaceBasis
  let E : ULift.{v} P.toExtension.Cotangent ≃ₗ[B] P.toExtension.Cotangent :=
    ULift.moduleEquiv
  let d := P.toExtension.cotangentComplex.comp E.toLinearMap
  let K := twoTermComplex d
  obtain ⟨hGE, hLE, hfinite, hprojective⟩ := twoTermComplex_finite_projective d
  obtain ⟨e⟩ := twoTermComplex_cotangentComplex_iso P
  have e' : naiveCotangentObject A B ≅ DerivedCategory.Q.obj K := e.symm
  refine ⟨⟨K, -1, 0, hGE, hLE, hfinite, hprojective, ⟨e'⟩⟩, ?_⟩
  have hflat (i : ℤ) : Module.Flat B (K.X i) := by
    let := hprojective i
    infer_instance
  have hamp := hasTorAmplitude_of_bounded_flat comparison isLeftDerived K (-1) 0 hGE hLE hflat
  intro M i hi
  exact (hamp M i hi).of_iso ((DerivedCategory.homologyFunctor _ i).mapIso
    ((derivedTensor.flip.obj ((DerivedCategory.singleFunctor _ 0).obj M)).mapIso e'))

/-! ### Tor amplitude of a two-term complex

For a map of modules `d : X₁ ⟶ X₀` with `X₀` flat, if the cone of `d[0]` has Tor amplitude in
`[-1, 0]`, then `X₁` is flat. -/

section TorAmplitudeTwoTerm

open CategoryTheory.Pretriangulated

variable {R : Type u} [CommRing R]
  (derivedTensor : DerivedCategory (ModuleCat.{u} R) ⥤
    DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R))
  (comparison : ∀ M : ModuleCat.{u} R,
    DerivedCategory.Q ⋙ derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M) ⟶
      (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  (isLeftDerived : ∀ M : ModuleCat.{u} R,
    (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsLeftDerivedFunctor
      (comparison M)
      (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))

/-- Tor amplitude with the endofunctor `- ⊗ᴸ N[0]` in flipped form and the excluded degrees
spelled `i < a ∨ b < i`. -/
private lemma hasTorAmplitude_iff_flipped (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    HasTorAmplitude derivedTensor comparison isLeftDerived K a b ↔
      ∀ (N : ModuleCat.{u} R) (i : ℤ), (i < a ∨ b < i) →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
          ((derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).obj K)) := by
  simp only [HasTorAmplitude, Set.mem_Icc, not_and_or, not_le, Functor.flip_obj_obj]

/-- Shifting an object shifts its Tor amplitude: if `X` has Tor amplitude in `[a' + n, b' + n]`
then `X⟦n⟧` has Tor amplitude in `[a', b']`. -/
private lemma hasTorAmplitude_shift
    (tensorCommShift : ∀ M : ModuleCat.{u} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).CommShift ℤ)
    (X : DerivedCategory (ModuleCat.{u} R)) (a b n a' b' : ℤ)
    (ha : a = a' + n) (hb : b = b' + n)
    (h : HasTorAmplitude derivedTensor comparison isLeftDerived X a b) :
    HasTorAmplitude derivedTensor comparison isLeftDerived (X⟦n⟧) a' b' := by
  rw [hasTorAmplitude_iff_flipped derivedTensor comparison isLeftDerived] at h ⊢
  intro N j hj
  let := tensorCommShift N
  have hz := h N (n + j) (by omega)
  exact hz.of_iso (((DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).mapIso
      (((derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).commShiftIso n).app X)) ≪≫
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) 0).shiftIso n j (n + j) rfl).app _)

/-- A module placed in degree zero whose Tor amplitude is bounded below by `0` is flat. -/
private lemma flat_of_hasTorAmplitude_single (X : ModuleCat.{u} R) (b : ℤ)
    (h : HasTorAmplitude derivedTensor comparison isLeftDerived
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj X) 0 b) : Module.Flat R X := by
  have hsingle (i : ℤ) (hi : i ≠ 0) :
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj X)) :=
    (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 X i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app X) ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app _)
  obtain ⟨P, hproj, hPLE, ⟨eP⟩⟩ :=
    exists_projective_representative_of_isLE
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj X) 0
      (fun i hi => hsingle i (by omega))
  have hflat (i : ℤ) : Module.Flat R (P.X i) := by
    have := hproj i
    infer_instance
  have hbdd : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
    ⟨0, (CochainComplex.isStrictlyLE_iff P 0).1 hPLE⟩
  have hP := (hasTorAmplitude_iff_termwise_of_flat
    comparison isLeftDerived P hbdd hflat 0 b).mp
      ((hasTorAmplitude_of_iso eP 0 b).mp h)
  refine (hasTorDimensionLE_iff_hasFlatRepresentative
    comparison isLeftDerived X 0).2.mp
      ((hasTorAmplitude_of_iso eP 0 0).mpr
        ((hasTorAmplitude_iff_termwise_of_flat
          comparison isLeftDerived P hbdd hflat 0 0).mpr ?_))
  intro M i hi
  rcases hi with hi | hi
  · exact hP M i (Or.inl hi)
  · rcases lt_or_ge b i with hib | hib
    · exact hP M i (Or.inr hib)
    · exact (HomologicalComplex.ExactAt.of_isZero
        ((MonoidalCategory.tensorRight M).map_isZero
          ((CochainComplex.isStrictlyLE_iff P 0).1 hPLE i hi))).isZero_homology

/-- **The two-term criterion.** Let `d : X₁ ⟶ X₀` be a map of `R`-modules with `X₀` flat. If the
mapping cone of `d`, placed in degrees `-1` and `0`, has Tor amplitude in `[-1, 0]`, then `X₁` is
flat. -/
private lemma flat_of_mappingCone_hasTorAmplitude
    (tensorCommShift : ∀ M : ModuleCat.{u} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).CommShift ℤ)
    (tensorTriangulated : ∀ M : ModuleCat.{u} R, letI := tensorCommShift M;
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj M)).IsTriangulated)
    {X₁ X₀ : ModuleCat.{u} R} (d : X₁ ⟶ X₀) [Module.Flat R X₀]
    (h : HasTorAmplitude derivedTensor comparison isLeftDerived
      (DerivedCategory.Q.obj (CochainComplex.mappingCone
        ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map d))) (-1) 0) :
    Module.Flat R X₁ := by
  set φ := (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).map d with hφ
  set T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle φ) with hT
  have hTd : T.rotate ∈ distTriang _ :=
    rot_of_distTriang _
      (DerivedCategory.mappingCone_triangle_distinguished φ)
  have h₀ : HasTorAmplitude derivedTensor comparison isLeftDerived
      T.rotate.obj₁ (-1 + 1) (0 + 1) := by
    have h₀₀ : HasTorAmplitude derivedTensor comparison isLeftDerived
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj X₀) 0 0 :=
      (hasTorDimensionLE_iff_hasFlatRepresentative
        comparison isLeftDerived X₀ 0).2.mpr inferInstance
    intro M j hj
    exact h₀₀ M j (by simp only [Set.mem_Icc, not_and_or, not_le] at hj ⊢; omega)
  have h₂ : HasTorAmplitude derivedTensor comparison isLeftDerived T.rotate.obj₂ (-1) 0 := h
  have h₃ := hasTorAmplitude_obj₃_of_obj₁_obj₂ derivedTensor comparison isLeftDerived
    tensorCommShift tensorTriangulated T.rotate hTd (-1) 0 h₀ h₂
  have hs : HasTorAmplitude derivedTensor comparison isLeftDerived
      (((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj X₁)⟦(1 : ℤ)⟧⟦(-1 : ℤ)⟧) 0 1 :=
    hasTorAmplitude_shift derivedTensor comparison isLeftDerived tensorCommShift
      T.rotate.obj₃ (-1) 0 (-1) 0 1 (by omega) (by omega) h₃
  refine flat_of_hasTorAmplitude_single derivedTensor comparison isLeftDerived X₁ 1 ?_
  exact (hasTorAmplitude_of_iso
    ((CategoryTheory.shiftFunctorCompIsoId (DerivedCategory (ModuleCat.{u} R))
      (1 : ℤ) (-1) (by omega)).app
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj X₁)) 0 1).mp hs

end TorAmplitudeTwoTerm

/-! ### The local complete intersection criterion

For a perfect ring map of Noetherian rings, Tor amplitude of `NL_{B/A}` in `[-1, 0]`, perfectness
of `NL_{B/A}` with that Tor amplitude, and the local complete intersection property are all
equivalent. -/

section Criterion

open CategoryTheory.Pretriangulated

/-- If the naive cotangent complex has Tor amplitude in `[-1, 0]`, then the conormal module of
every presentation is flat. -/
private theorem cotangent_flat_of_hasTorAmplitude
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (derivedTensor : DerivedCategory (ModuleCat.{u} B) ⥤
      DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B))
    (comparison : ∀ M : ModuleCat.{u} B,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{u} B,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)))
    (tensorCommShift : ∀ M : ModuleCat.{u} B,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).CommShift ℤ)
    (tensorTriangulated : ∀ M : ModuleCat.{u} B, letI := tensorCommShift M;
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).IsTriangulated)
    {ι : Type} (P : Algebra.Generators A B ι)
    (h : HasTorAmplitude derivedTensor comparison isLeftDerived
      (naiveCotangentObject A B) (-1) 0) :
    Module.Flat B P.toExtension.Cotangent := by
  obtain ⟨e⟩ := twoTermComplex_cotangentComplex_iso P
  have hsrc := (hasTorAmplitude_of_iso e (-1) 0).mpr h
  let : Module.Projective B P.toExtension.CotangentSpace :=
    Module.Projective.of_basis P.cotangentSpaceBasis
  have hflat : Module.Flat B (ULift.{u} P.toExtension.Cotangent) :=
    flat_of_mappingCone_hasTorAmplitude derivedTensor comparison isLeftDerived
      tensorCommShift tensorTriangulated
      (ModuleCat.ofHom (P.toExtension.cotangentComplex.comp
        (ULift.moduleEquiv :
          ULift.{u} P.toExtension.Cotangent ≃ₗ[B] P.toExtension.Cotangent).toLinearMap))
      hsrc
  exact Module.Flat.of_linearEquiv
    (ULift.moduleEquiv : ULift.{u} P.toExtension.Cotangent ≃ₗ[B] P.toExtension.Cotangent).symm

/-- A finite resolution by projective modules bounds the projective dimension. -/
private lemma hasProjectiveDimensionLE_of_moduleResolution
    {R : Type u} [Ring R] {M : Type u} [AddCommGroup M] [Module R M]
    (F : ModuleResolution R M) (d : ℕ)
    (hproj : ∀ i, Projective (F.complex.X i))
    (hzero : ∀ i, d < i → IsZero (F.complex.X i)) :
    HasProjectiveDimensionLE (ModuleCat.of R M) d := by
  have hres : ∃ G : CategoryTheory.ObjectProperty.LeftResolution
      (CategoryTheory.isProjective (ModuleCat.{u} R)) (ModuleCat.of R M),
      ∀ i, d < i → IsZero (G.complex.X i) :=
    ⟨{ complex := F.complex, property := hproj, hasHomology := F.hasHomology,
       π := F.π, quasiIso := F.quasiIso }, hzero⟩
  exact ((CategoryTheory.hasProjectiveDimensionLE_tfae_leftResolution
    (ModuleCat.of R M) d).out 2 1).mp hres

/-- The conormal module of a presentation and the conormal module of its kernel ideal correspond
along the ring isomorphism `P.Ring / P.ker ≅ S`: finiteness transfers from the latter to the
former, and projectivity from the former to the latter. -/
private lemma cotangent_ker_transfer
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (P : Algebra.Extension R S) :
    (Module.Finite (P.Ring ⧸ P.ker) P.ker.Cotangent → Module.Finite S P.Cotangent) ∧
      (Module.Projective S P.Cotangent →
        Module.Projective (P.Ring ⧸ P.ker) P.ker.Cotangent) := by
  let e := (algebraMap P.Ring S).quotientKerEquivOfSurjective P.algebraMap_surjective
  let : RingHomInvPair e.toRingHom e.symm.toRingHom :=
    ⟨RingHom.ext e.symm_apply_apply, RingHom.ext e.apply_symm_apply⟩
  let : RingHomInvPair e.symm.toRingHom e.toRingHom :=
    ⟨RingHom.ext e.apply_symm_apply, RingHom.ext e.symm_apply_apply⟩
  let E : P.ker.Cotangent ≃ₛₗ[e.toRingHom] P.Cotangent :=
    { P.cotangentEquivCotangentKer.symm.toAddEquiv with
      map_smul' := by
        intro r x
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
        apply Algebra.Extension.Cotangent.ext
        show r • x = (r • (Algebra.Extension.Cotangent.of x : P.Cotangent)).val
        exact (Algebra.Extension.Cotangent.val_smul' r _).symm }
  refine ⟨fun h => ?_, fun h => ?_⟩
  · let := h
    exact Module.Finite.of_surjective E.toLinearMap E.surjective
  · let := h
    exact Module.Projective.of_equiv E.symm

/-- Let `A → B` be a perfect ring homomorphism of Noetherian rings. Then the
naive cotangent complex `NL_{B/A}` has Tor amplitude in `[-1, 0]` if and only if it is a perfect
object of `D(B)` with Tor amplitude in `[-1, 0]`, if and only if `A → B` is a local complete
intersection. -/
@[stacks 0FJT]
public theorem hasTorAmplitude_tfae_isLocalCompleteIntersection
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsNoetherianRing B]
    (hperfect : RingHom.IsPerfectRingMap A B
      (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
      (canonicalTensorComparison A) (canonicalTensorIsLeftDerived A)) :
    List.TFAE
      [HasTorAmplitude
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct B).tensor
          (canonicalTensorComparison B) (canonicalTensorIsLeftDerived B)
          (naiveCotangentObject A B) (-1) 0,
        StacksDraft.Perfect.IsPerfect (naiveCotangentObject A B) ∧
          HasTorAmplitude
            (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct B).tensor
            (canonicalTensorComparison B) (canonicalTensorIsLeftDerived B)
            (naiveCotangentObject A B) (-1) 0,
        RingHom.IsLocalCompleteIntersection (algebraMap A B)] := by
  classical
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct B
  let hshift : ∀ M : ModuleCat.{u} B,
      (T.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).CommShift ℤ :=
    fun M => T.commShift_left _
  have htri : ∀ M : ModuleCat.{u} B, let := hshift M;
      (T.tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).IsTriangulated :=
    fun M => T.exact_left _
  tfae_have 3 → 2 := fun hlci =>
    naiveCotangentComplex_isPerfect_and_hasTorAmplitude hlci T.tensor
      (canonicalTensorComparison B) (canonicalTensorIsLeftDerived B)
  tfae_have 2 → 1 := fun h => h.2
  tfae_have 1 → 3 := by
    intro h
    obtain ⟨n, α, hα, d, F, hterms, hvanish⟩ :=
      (RingHom.isPerfectRingMap_iff_exists_finite_projective_resolution
        A B (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct A).tensor
        (canonicalTensorComparison A) (canonicalTensorIsLeftDerived A)).mp hperfect
    let R := MvPolynomial (Fin n) A
    let : Module R B := Module.compHom B α.toRingHom
    have heval : MvPolynomial.aeval (fun i : Fin n => α (MvPolynomial.X i)) = α := by
      ext i
      simp
    let P : Algebra.Generators A B (Fin n) :=
      Algebra.Generators.ofSurjective (fun i => α (MvPolynomial.X i)) (by rwa [heval])
    have hflat : Module.Flat B P.toExtension.Cotangent :=
      cotangent_flat_of_hasTorAmplitude T.tensor (canonicalTensorComparison B)
        (canonicalTensorIsLeftDerived B) hshift htri P h
    let g : R →ₗ[R] B :=
      { toFun := α
        map_add' := fun x y => map_add α x y
        map_smul' := fun r x => map_mul α r x }
    have hS : g.shortComplexKer.ShortExact :=
      LinearMap.shortExact_shortComplexKer (by simpa [g] using hα)
    have hpdB : HasProjectiveDimensionLE (ModuleCat.of R B) d :=
      hasProjectiveDimensionLE_of_moduleResolution F d
        (fun i => by
          let : Module.Projective R (F.complex.X i) := (hterms i).2
          infer_instance) hvanish
    have h₂ : HasProjectiveDimensionLT g.shortComplexKer.X₂ (d + 1) :=
      hasProjectiveDimensionLT_of_ge _ 1 (d + 1) (by omega)
    have h₃ : HasProjectiveDimensionLT g.shortComplexKer.X₃ (d + 1 + 1) :=
      hasProjectiveDimensionLT_of_ge _ (d + 1) (d + 1 + 1) (by omega)
    have hpdKer : HasProjectiveDimensionLE
        (ModuleCat.of R (LinearMap.ker g)) d :=
      hS.hasProjectiveDimensionLT_X₁ (d + 1) h₂ h₃
    let I : Ideal R := P.toExtension.ker
    have hI : I = LinearMap.ker g := by
      ext x
      show x ∈ RingHom.ker (algebraMap P.toExtension.Ring B) ↔ x ∈ LinearMap.ker g
      simp only [LinearMap.mem_ker]
      show MvPolynomial.aeval (fun i : Fin n => α (MvPolynomial.X i)) x = 0 ↔ α x = 0
      rw [heval]
    have hpdI : Module.projectiveDimension R I ≠ ⊤ := by
      refine (CategoryTheory.projectiveDimension_ne_top_iff (ModuleCat.of R I)).2 ⟨d, ?_⟩
      let : HasProjectiveDimensionLE (ModuleCat.of R (LinearMap.ker g)) d := hpdKer
      exact ModuleCat.hasProjectiveDimensionLE_of_linearEquiv
        (M := ModuleCat.of R (LinearMap.ker g)) (N := ModuleCat.of R I)
        (LinearEquiv.ofEq I (LinearMap.ker g) hI).symm d
    have hfinR : Module.Finite R I.Cotangent :=
      Module.Finite.of_surjective I.toCotangent I.toCotangent_surjective
    have hfinQ : Module.Finite (R ⧸ I) I.Cotangent :=
      Module.Finite.of_restrictScalars_finite R (R ⧸ I) I.Cotangent
    have hfinB : Module.Finite B P.toExtension.Cotangent :=
      (cotangent_ker_transfer P.toExtension).1 hfinQ
    have hprojB : Module.Projective B P.toExtension.Cotangent := by
      let : Module.Finite B P.toExtension.Cotangent := hfinB
      let : Module.FinitePresentation B P.toExtension.Cotangent :=
        Module.finitePresentation_of_finite B P.toExtension.Cotangent
      let : Module.Flat B P.toExtension.Cotangent := hflat
      exact Module.Flat.projective_of_finitePresentation
    have hprojQ : Module.Projective (R ⧸ I) I.Cotangent :=
      (cotangent_ker_transfer P.toExtension).2 hprojB
    have hlocQ : Module.IsFiniteLocallyFree (R ⧸ I) I.Cotangent := by
      have hfp : Module.Finite (R ⧸ I) I.Cotangent ∧ Module.Projective (R ⧸ I) I.Cotangent :=
        ⟨hfinQ, hprojQ⟩
      obtain ⟨s, hs, hlocal⟩ :=
        ((Module.finite_projective_tfae (R ⧸ I) I.Cotangent).out 2 7).mp hfp
      refine ⟨s, ((↑) : s → R ⧸ I), ?_, fun x => hlocal x.1 x.2⟩
      simpa only [Subtype.range_coe] using hs
    have hregI :=
      Ideal.isRegular_of_projectiveDimension_ne_top_of_isFiniteLocallyFree_cotangent
        I hpdI hlocQ
    have hker : RingHom.ker α.toRingHom = I := by
      rw [hI]
      ext x
      simp [g, LinearMap.mem_ker]
    rw [RingHom.IsLocalCompleteIntersection, toAlgebra_algebraMap]
    refine ⟨RingHom.finiteType_algebraMap.mpr
      ((Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mpr ⟨n, α, hα⟩),
      n, α, hα, ?_⟩
    exact (hker.symm ▸ hregI : (RingHom.ker α.toRingHom).IsRegular).isKoszulRegular
  tfae_finish

end Criterion

/-! ### The syntomic criterion

For a flat ring map of finite presentation, Tor amplitude of `NL_{B/A}` in `[-1, 0]`, perfectness
of `NL_{B/A}` with that Tor amplitude, syntomicity and the local complete intersection property
are all equivalent. -/

section Syntomic

/-- A two-term complex of flat modules is concentrated in degrees `-1` and `0` and is termwise
flat. -/
private theorem twoTermComplex_flat {R : Type u} [CommRing R]
    {M N : Type v} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    [Module.Flat R M] [Module.Flat R N] (d : M →ₗ[R] N) :
    (twoTermComplex d).IsStrictlyGE (-1) ∧ (twoTermComplex d).IsStrictlyLE 0 ∧
      ∀ i, Module.Flat R ((twoTermComplex d).X i) := by
  let S := CochainComplex.singleFunctor (ModuleCat.{v} R) 0
  obtain ⟨hGE, hLE⟩ := twoTermComplex_isStrictlyGE_and_isStrictlyLE d
  refine ⟨hGE, hLE, fun i => ?_⟩
  by_cases h₁ : i = -1
  · subst i
    exact Module.Flat.of_linearEquiv
      ((HomologicalComplex.homotopyCofiber.XIsoBiprod
        (S.map (ModuleCat.ofHom d)) (-1) 0 (by decide) ≪≫
        (isoBiprodZero (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) 0 (ModuleCat.of R N) (-1) (by decide))).symm ≪≫
        HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of R M)).toLinearEquiv)
  by_cases h₀ : i = 0
  · subst i
    exact Module.Flat.of_linearEquiv
      ((HomologicalComplex.homotopyCofiber.XIsoBiprod
        (S.map (ModuleCat.ofHom d)) 0 1 (by decide) ≪≫
        (isoZeroBiprod (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) 0 (ModuleCat.of R M) 1 (by decide))).symm ≪≫
        HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
          (ModuleCat.of R N)).toLinearEquiv)
  · have : Subsingleton ((twoTermComplex d).X i) :=
      ModuleCat.isZero_iff_subsingleton.mp (by
        rcases lt_or_ge i (-1) with hi | hi
        · exact (CochainComplex.isStrictlyGE_iff _ _).1 hGE i hi
        · exact (CochainComplex.isStrictlyLE_iff _ _).1 hLE i (by omega))
    infer_instance

/-- If the conormal module of one finite polynomial presentation of `B` over `A` is flat, then
`NL_{B/A}` has Tor amplitude in `[-1, 0]`. -/
private theorem hasTorAmplitude_of_flat_cotangent
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]
    (derivedTensor : DerivedCategory (ModuleCat.{u} B) ⥤
      DerivedCategory (ModuleCat.{u} B) ⥤ DerivedCategory (ModuleCat.{u} B))
    (comparison : ∀ M : ModuleCat.{u} B,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ M : ModuleCat.{u} B,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{u} B) (ComplexShape.up ℤ)))
    {ι : Type} (P : Algebra.Generators A B ι)
    (hflat : Module.Flat B P.toExtension.Cotangent) :
    HasTorAmplitude derivedTensor comparison isLeftDerived (naiveCotangentObject A B) (-1) 0 := by
  let : Module.Flat B P.toExtension.Cotangent := hflat
  let : Module.Free B P.toExtension.CotangentSpace :=
    Module.Free.of_basis P.cotangentSpaceBasis
  let E : ULift.{u} P.toExtension.Cotangent ≃ₗ[B] P.toExtension.Cotangent := ULift.moduleEquiv
  let : Module.Flat B (ULift.{u} P.toExtension.Cotangent) := Module.Flat.of_linearEquiv E
  let d := P.toExtension.cotangentComplex.comp E.toLinearMap
  obtain ⟨hGE, hLE, hflatK⟩ := twoTermComplex_flat d
  obtain ⟨e⟩ := twoTermComplex_cotangentComplex_iso P
  exact (hasTorAmplitude_of_iso e.symm (-1) 0).mpr
    (hasTorAmplitude_of_bounded_flat comparison isLeftDerived (twoTermComplex d) (-1) 0
      hGE hLE hflatK)

attribute [local instance] Algebra.TensorProduct.rightAlgebra in
/-- Along a flat ring map `A → B`, the conormal module of a presentation of `B` over `A` stays
flat after an arbitrary base change `A → A'`. -/
private theorem flat_cotangent_baseChange
    {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
    [Algebra A B] [Algebra A A'] [Module.Flat A B] {ι : Type*}
    (P : Algebra.Generators A B ι)
    (hflat : Module.Flat B P.toExtension.Cotangent) :
    Module.Flat (A' ⊗[A] B) (P.baseChange A').toExtension.Cotangent := by
  have hinj := cotangent_generators_liftBaseChange_injective_of_flat_target (T := A') P
  have hsurj := cotangent_generators_baseChange_surjective (T := A') P
  let h := (P.baseChangeFromBaseChange A').comp (P.toExtension.toBaseChange A')
  let e := LinearEquiv.ofBijective
    ((Algebra.Extension.Cotangent.map h).liftBaseChange (A' ⊗[A] B)) ⟨hinj, hsurj⟩
  have : Module.Flat (A' ⊗[A] B) ((A' ⊗[A] B) ⊗[B] P.toExtension.Cotangent) := by
    have := hflat
    infer_instance
  exact Module.Flat.of_linearEquiv e.symm

/-- A syntomic algebra over a field is a local complete intersection over that field. -/
private theorem isLocalCompleteIntersection_of_syntomic_field
    {k S : Type u} [Field k] [CommRing S] [Algebra k S] (h : Algebra.Syntomic k S) :
    IsLocalCompleteIntersection k S := by
  let p : Ideal k := ⊥
  let : Algebra S (p.Fiber S) := Algebra.TensorProduct.rightAlgebra
  exact (Algebra.IsPushout.isLocalCompleteIntersection_iff k p.ResidueField S
    (p.Fiber S)).mp (h.isLocalCompleteIntersection_fiber p)

/-- Let `A → B` be a flat ring homomorphism of finite presentation. Then the
naive cotangent complex `NL_{B/A}` has Tor amplitude in `[-1, 0]` if and only if it is a perfect
object of `D(B)` with Tor amplitude in `[-1, 0]`, if and only if `A → B` is syntomic, if and only
if `A → B` is a local complete intersection. -/
@[stacks 0FJV]
public theorem hasTorAmplitude_tfae_syntomic
    (A B : Type u) [CommRing A] [CommRing B] [Algebra A B]
    [Module.Flat A B] [Algebra.FinitePresentation A B] :
    List.TFAE
      [HasTorAmplitude
          (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct B).tensor
          (canonicalTensorComparison B) (canonicalTensorIsLeftDerived B)
          (naiveCotangentObject A B) (-1) 0,
        StacksDraft.Perfect.IsPerfect (naiveCotangentObject A B) ∧
          HasTorAmplitude
            (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct B).tensor
            (canonicalTensorComparison B) (canonicalTensorIsLeftDerived B)
            (naiveCotangentObject A B) (-1) 0,
        Algebra.Syntomic A B,
        RingHom.IsLocalCompleteIntersection (algebraMap A B)] := by
  classical
  let T := CochainComplex.DerivedTensor.canonicalDerivedTensorProduct B
  let hshift : ∀ M : ModuleCat.{u} B,
      (T.tensor.flip.obj ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).CommShift ℤ :=
    fun M => T.commShift_left _
  have htri : ∀ M : ModuleCat.{u} B, let := hshift M;
      (T.tensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} B) 0).obj M)).IsTriangulated :=
    fun M => T.exact_left _
  have h34 : Algebra.Syntomic A B ↔ RingHom.IsLocalCompleteIntersection (algebraMap A B) := by
    have h := RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection (algebraMap A B)
    rw [toAlgebra_algebraMap] at h
    refine h.trans ⟨fun hx => hx.2, fun hx => ⟨?_, hx⟩⟩
    exact RingHom.flat_algebraMap_iff.mpr inferInstance
  tfae_have 4 → 2 := fun hlci =>
    naiveCotangentComplex_isPerfect_and_hasTorAmplitude hlci T.tensor
      (canonicalTensorComparison B) (canonicalTensorIsLeftDerived B)
  tfae_have 2 → 1 := fun hx => hx.2
  tfae_have 3 → 4 := h34.mp
  tfae_have 1 → 3 := by
    intro h
    obtain ⟨n, α, hα⟩ :=
      (Algebra.FiniteType.iff_quotient_mvPolynomial'' (R := A) (S := B)).mp inferInstance
    let P : Algebra.Generators A B (Fin n) := Algebra.Generators.ofAlgHom α hα
    have hflatP : Module.Flat B P.toExtension.Cotangent :=
      cotangent_flat_of_hasTorAmplitude T.tensor (canonicalTensorComparison B)
        (canonicalTensorIsLeftDerived B) hshift htri P h
    refine ⟨inferInstance, inferInstance, fun p _ => ?_⟩
    have hflatk : Module.Flat (p.Fiber B) (P.baseChange p.ResidueField).toExtension.Cotangent :=
      flat_cotangent_baseChange (A' := p.ResidueField) P hflatP
    have hampk : HasTorAmplitude
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct (p.Fiber B)).tensor
        (canonicalTensorComparison (p.Fiber B))
        (canonicalTensorIsLeftDerived (p.Fiber B))
        (naiveCotangentObject p.ResidueField (p.Fiber B)) (-1) 0 :=
      hasTorAmplitude_of_flat_cotangent _ _ _ (P.baseChange p.ResidueField) hflatk
    have hNoeth : IsNoetherianRing (p.Fiber B) :=
      Algebra.FiniteType.isNoetherianRing p.ResidueField _
    have hperf : RingHom.IsPerfectRingMap p.ResidueField (p.Fiber B)
        (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct p.ResidueField).tensor
        (canonicalTensorComparison p.ResidueField)
        (canonicalTensorIsLeftDerived p.ResidueField) :=
      (RingHom.isPerfectRingMap_of_flat_of_finitePresentation p.ResidueField (p.Fiber B)).2 _ _ _
    have hlcik : RingHom.IsLocalCompleteIntersection (algebraMap p.ResidueField (p.Fiber B)) :=
      ((hasTorAmplitude_tfae_isLocalCompleteIntersection p.ResidueField (p.Fiber B)
        hperf).out 1 3).mp hampk
    have hsynk : Algebra.Syntomic p.ResidueField (p.Fiber B) := by
      have hx := RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection
        (algebraMap p.ResidueField (p.Fiber B))
      rw [toAlgebra_algebraMap] at hx
      exact hx.mpr ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, hlcik⟩
    exact isLocalCompleteIntersection_of_syntomic_field hsynk
  tfae_finish

end Syntomic

end NaiveCotangent
