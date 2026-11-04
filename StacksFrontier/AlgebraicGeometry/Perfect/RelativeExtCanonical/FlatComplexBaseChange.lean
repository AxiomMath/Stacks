module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.FlatPullbackTensor
public import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparison
public import StacksFrontier.Topology.Sheaves.Functors.Module.PullbackComp

/-!
# A bounded complex flat over the base stays so after base change

Let `X' → X` over `S' → S` be a cartesian square of schemes and `𝒢^•` a bounded complex of
quasi-coherent `𝒪_X`-modules, each flat over `S`. Then the degreewise pullback `(g')^*𝒢^•` is a
bounded complex of `𝒪_{X'}`-modules each flat over `S'`. This is [Stacks, Tag 01U8] in every
degree, and it is the hypothesis under which the functor `ℳ ↦ (g')^*𝒢^• ⊗ (f')^*ℳ` of the
right-hand side of [Stacks, Tag 0DJS] descends to derived categories without deriving `(g')^*`.

## Main results

* `Stacks.Cohomology.RelativeExtCanonical.isBoundedFlatOver_pullbackComplex`
* `Stacks.Cohomology.RelativeExtCanonical.isGE_pullbackTensorDerivedFunctor_obj`: the functor
  `K ↦ Tot(f^*K ⊗ 𝒢^•)` carries objects in degrees `≥ m` to objects in degrees `≥ m + a` when
  `𝒢^•` vanishes below `a`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Cohomology.RelativeExtCanonical

open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)

/-- **Base change of a bounded complex flat over the base.** For a cartesian square
`X' → X` over `S' → S` and a bounded complex `𝒢^•` of quasi-coherent `𝒪_X`-modules flat over
`S`, the degreewise pullback `(g')^*𝒢^•` is bounded and flat over `S'`. -/
theorem isBoundedFlatOver_pullbackComplex {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S}
    {g' : X' ⟶ X} {f' : X' ⟶ S'} (h : IsPullback g' f' f g)
    (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) ℤ)
    (hGq : ∀ i : ℤ, (G.X i).IsQuasicoherent)
    (hG : Stacks.Cohomology.RelativeExt.IsBoundedFlatOver f.toLRSHom.toShHom G) :
    Stacks.Cohomology.RelativeExt.IsBoundedFlatOver f'.toLRSHom.toShHom
      ((pullbackComplex g'.toLRSHom.toShHom).obj G) where
  bounded := by
    have := RingedSpaceModuleAdjunction.modulePullback_additive g'.toLRSHom.toShHom
    obtain ⟨a, b, ha, hb⟩ := hG.bounded
    refine ⟨a, b, ?_, ?_⟩
    · exact (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi ↦
        Functor.map_isZero (RingedSpaceModuleAdjunction.modulePullback g'.toLRSHom.toShHom)
          ((CochainComplex.isStrictlyGE_iff G a).1 ha i hi)
    · exact (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi ↦
        Functor.map_isZero (RingedSpaceModuleAdjunction.modulePullback g'.toLRSHom.toShHom)
          ((CochainComplex.isStrictlyLE_iff G b).1 hb i hi)
  isFlatOver i := by
    have := hGq i
    exact modulePullback_isFlatOver h (G.X i) (hG.isFlatOver i)

section Bound

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- The total complex of `f^*K ⊗ 𝒢^•` vanishes below `m + a` when `K` vanishes below `m` and `𝒢^•`
below `a`: every summand `f^*K^p ⊗ 𝒢^q` in a degree `< m + a` has a vanishing factor. -/
theorem isStrictlyGE_pullbackTensorComplexFunctor_obj
    (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (K : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ) (m a : ℤ)
    [K.IsStrictlyGE m] [G.IsStrictlyGE a] :
    ((Stacks.Cohomology.RelativeExt.pullbackTensorComplexFunctor f G).obj K).IsStrictlyGE
      (m + a) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  refine (IsZero.iff_id_eq_zero _).mpr ?_
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro p q hpq
  have hz : IsZero (((Stacks.Cohomology.RelativeExt.pullbackTensorBifunctor f).obj (K.X p)).obj
      (G.X q)) := by
    by_cases hp : p < m
    · exact ((Stacks.Cohomology.RelativeExt.pullbackTensorBifunctor f).map_isZero
        (K.isZero_of_isStrictlyGE m p hp)).obj _
    · exact ((Stacks.Cohomology.RelativeExt.pullbackTensorBifunctor f).obj (K.X p)).map_isZero
        (G.isZero_of_isStrictlyGE a q (by dsimp at hpq; omega))
  exact hz.eq_of_src _ _

/-- **`K ↦ 𝒢^• ⊗ f^*K` raises lower bounds by the lower bound of `𝒢^•`.** For `𝒢^•` bounded,
flat over `Y` and vanishing below `a`, the functor of
`Stacks.Cohomology.RelativeExt.pullbackTensorDerivedFunctor` carries an object in degrees `≥ m`
to an object in degrees `≥ m + a`. Stated at the standard model, the model of that functor. -/
theorem isGE_pullbackTensorDerivedFunctor_obj
    {G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (hG : Stacks.Cohomology.RelativeExt.IsBoundedFlatOver f G) (a : ℤ) [G.IsStrictlyGE a] :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X))
    ∀ (N : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) (m : ℤ), N.IsGE m →
      ((Stacks.Cohomology.RelativeExt.pullbackTensorDerivedFunctor hG).obj N).IsGE (m + a) := by
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y))
  let := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X))
  intro N m hN
  obtain ⟨K, hK, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isGE N m
  have := isStrictlyGE_pullbackTensorComplexFunctor_obj f G K m a
  have hQ : (DerivedCategory.Q.obj
      ((Stacks.Cohomology.RelativeExt.pullbackTensorComplexFunctor f G).obj K)).IsGE (m + a) := by
    rw [DerivedCategory.isGE_Q_obj_iff]; infer_instance
  exact @DerivedCategory.TStructure.t.isGE_of_iso _ _ _ _ _ _ _ _ _
    (((Stacks.Cohomology.RelativeExt.pullbackTensorDerivedFunctorFactors hG).app K).symm ≪≫
      (Stacks.Cohomology.RelativeExt.pullbackTensorDerivedFunctor hG).mapIso e.symm) (m + a) hQ

/-- **An isomorphism of complexes flat over `Y` gives an isomorphism of the functors
`K ↦ Tot(f^*K ⊗ 𝒢)`**, on derived categories. Stated at the standard model. -/
def pullbackTensorDerivedFunctorIsoOfIso
    {G₁ G₂ : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ}
    (hG₁ : Stacks.Cohomology.RelativeExt.IsBoundedFlatOver f G₁)
    (hG₂ : Stacks.Cohomology.RelativeExt.IsBoundedFlatOver f G₂) (e : G₁ ≅ G₂) :
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y))
    letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X))
    Stacks.Cohomology.RelativeExt.pullbackTensorDerivedFunctor hG₁ ≅
      Stacks.Cohomology.RelativeExt.pullbackTensorDerivedFunctor hG₂ :=
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing Y))
  letI := HasDerivedCategory.standard (SheafOfModules.{u} (structureSheafRing X))
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso (SheafOfModules.{u} (structureSheafRing Y)) (ComplexShape.up ℤ))
    (Stacks.Cohomology.RelativeExt.pullbackTensorComplexFunctor f G₁ ⋙ DerivedCategory.Q)
    (Stacks.Cohomology.RelativeExt.pullbackTensorComplexFunctor f G₂ ⋙ DerivedCategory.Q) _ _
    (Functor.isoWhiskerRight
      ((((Stacks.Cohomology.RelativeExt.pullbackTensorBifunctor f).map₂CochainComplex).flip).mapIso
        e) DerivedCategory.Q)

end Bound

section Square

variable {A B C D : RingedSpace.{u, u}} (a : A ⟶ B) (b : B ⟶ D) (c : A ⟶ C) (d : C ⟶ D)
  (w : a ≫ b = c ≫ d)

/-- **Degreewise pullback around a commutative square**: `a^*(b^*K) ≅ c^*(d^*K)` for
`a ≫ b = c ≫ d`, from `(a ≫ b)^* ≅ b^* ⋙ a^*`. -/
def pullbackComplexSquareIso (K : CochainComplex (SheafOfModules.{u} (structureSheafRing D)) ℤ) :
    ((RingedSpaceModuleAdjunction.modulePullback a).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((RingedSpaceModuleAdjunction.modulePullback b).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) ≅
      ((RingedSpaceModuleAdjunction.modulePullback c).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((RingedSpaceModuleAdjunction.modulePullback d).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K) :=
  let e : RingedSpaceModuleAdjunction.modulePullback b ⋙
      RingedSpaceModuleAdjunction.modulePullback a ≅
      RingedSpaceModuleAdjunction.modulePullback d ⋙ RingedSpaceModuleAdjunction.modulePullback c :=
    (RingedSpaceModuleAdjunction.modulePullbackComp a b).symm ≪≫
      RingedSpaceModuleAdjunction.modulePullbackCongr w ≪≫
        RingedSpaceModuleAdjunction.modulePullbackComp c d
  HomologicalComplex.Hom.isoOfComponents (fun i ↦ e.app (K.X i)) fun i j _ ↦
    (e.hom.naturality (K.d i j)).symm

end Square

end Stacks.Cohomology.RelativeExtCanonical

end
