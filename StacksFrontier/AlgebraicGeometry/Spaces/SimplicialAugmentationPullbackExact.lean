module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackModulesOfIsoStructureMap
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsReflectsIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposTwoMorphismModules
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Simplicial.SemiRepresentableRingedAugmentation
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.IdentityMorphismProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialQuasicoherentWeakSerreOfExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleBigFppfUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleDegree
public import StacksFrontier.AlgebraicGeometry.Spaces.SimplicialSmallEtaleQuasicoherentPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SpacesEtaleModulePullbackFlatExact
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfPretopology
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.MorphismPropertyCovering
public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModulesComparison
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject

/-!
# Exactness of the pullback along the augmentation of an fppf hypercovering

Let `a : U → X` be a hypercovering of an algebraic space in `(Spaces/S)_fppf` and
`a : (Sh(U_{spaces,étale}), 𝒪_U) ⟶ (Sh(X_{spaces,étale}), 𝒪_X)` the morphism of ringed topoi of
Stacks 0DE7. The pullback `a^*` of modules is exact.

Every level `a_n : U_n ⟶ X` is flat (Stacks 0DER), so pullback along `a_n` on the spaces-étale
sites is exact. The pullback `d_n^*` along the inclusion of degree `n` is restriction to degree
`n`, up to restrictions of scalars along isomorphisms; these are exact and jointly conservative,
and `a^*` followed by `d_n^*` is the pullback along `a_n`.

## Main results

In the namespace `AlgebraicGeometry.Space.SimplicialSpacesEtaleSite`:

* `isFlat_app_of_isHypercoveringAugmentation`: every level `a_n : U_n ⟶ X` is flat.
* `preservesFiniteLimits_augmentationRingedToposHom_pullbackModules`: `a^*` preserves finite
  limits.
* `isWeakSerreClass_isQuasicoherentOnSite_ringedSite`: the quasi-coherent `𝒪_U`-modules form a
  weak Serre subcategory.

## References

* [Stacks Project, Tag 0DER](https://stacks.math.columbia.edu/tag/0DER)
* [Stacks Project, Tag 0DE7](https://stacks.math.columbia.edu/tag/0DE7)
* [Stacks Project, Tag 0DHF](https://stacks.math.columbia.edu/tag/0DHF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.CategoryTheory.Hypercovering

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  {ι : Type*} {E : ι → Type*} [∀ i, Category* (E i)] [∀ i, Abelian (E i)]

/-- A short complex is exact once its images under a jointly conservative family of exact
functors are. -/
private theorem shortComplex_exact_of_forall_exact_map (G : ∀ i, D ⥤ E i)
    (hGl : ∀ i, PreservesFiniteLimits (G i)) (hGc : ∀ i, PreservesFiniteColimits (G i))
    (hG : ∀ {M N : D} (φ : M ⟶ N), (∀ i, IsIso ((G i).map φ)) → IsIso φ)
    (Sc : ShortComplex D) (hS : ∀ i, (Sc.map (G i)).Exact) : Sc.Exact := by
  rw [Sc.exact_iff_isZero_homology]
  have hz : ∀ i, IsZero ((G i).obj Sc.homology) := fun i =>
    ((Sc.map (G i)).exact_iff_isZero_homology.1 (hS i)).of_iso
      (Sc.mapHomologyIso (G i)).symm
  have : IsIso (0 : Sc.homology ⟶ Sc.homology) := hG _ fun i => by
    rw [Functor.map_zero, ← (IsZero.iff_id_eq_zero _).1 (hz i)]
    infer_instance
  exact IsZero.of_mono_zero _ Sc.homology

/-- **Left exactness tested on a jointly conservative family of exact functors.** A right exact
functor `F` between abelian categories preserves finite limits when its composite with each
member of a jointly conservative family of exact functors does. -/
private theorem preservesFiniteLimits_of_comp_jointlyConservative (F : C ⥤ D) [F.Additive]
    [PreservesFiniteColimits F] (G : ∀ i, D ⥤ E i)
    (hGl : ∀ i, PreservesFiniteLimits (G i)) (hGc : ∀ i, PreservesFiniteColimits (G i))
    (hG : ∀ {M N : D} (φ : M ⟶ N), (∀ i, IsIso ((G i).map φ)) → IsIso φ)
    (hFG : ∀ i, PreservesFiniteLimits (F ⋙ G i)) : PreservesFiniteLimits F := by
  refine (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).2 fun σ hσ => ?_
  have hc : ∀ i, PreservesFiniteColimits (F ⋙ G i) := fun i => comp_preservesFiniteColimits _ _
  have hmono := hσ.mono_f
  refine ⟨shortComplex_exact_of_forall_exact_map G hGl hGc hG _ fun i => ?_, ?_⟩
  · have := hFG i
    have := hc i
    exact hσ.exact.map (F ⋙ G i)
  · let Tc : ShortComplex D := ShortComplex.mk (0 : F.obj σ.X₁ ⟶ F.obj σ.X₁) (F.map σ.f) zero_comp
    refine (Tc.exact_iff_mono rfl).1 (shortComplex_exact_of_forall_exact_map G hGl hGc hG _
      fun i => ?_)
    have := hFG i
    exact (ShortComplex.exact_iff_mono _ ((G i).map_zero _ _)).2
      (inferInstanceAs (Mono ((F ⋙ G i).map σ.f)))

end CategoryTheory.Functor

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S}

/-- A morphism forming by itself a covering of the big fppf site of algebraic spaces is flat. -/
theorem isFlat_of_singleton_mem_pretopology {X Z : T.Spaces} (g : Z ⟶ X)
    (hg : Presieve.singleton g ∈ T.pretopologyBigFppfPretopology X) :
    IsFlat T.schemeSite S T.scheme_mem g.hom := by
  obtain ⟨E, hE, hcov⟩ := (T.mem_precoverage_iff).1 hg
  obtain ⟨i⟩ : E.presieve₀ g := by
    rw [← hE]
    exact Presieve.singleton.mk
  exact hcov.1.flat i

variable {U : SimplicialObject T.Spaces} {X : T.Spaces}
  {a : U ⟶ (SimplicialObject.const T.Spaces).obj X}

/-- **Stacks 0DER, `levels_in_p`, for an fppf hypercovering**: every level `a_n : U_n ⟶ X` of an
fppf hypercovering of algebraic spaces is flat. -/
theorem isFlat_app_of_isHypercoveringAugmentation
    (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a) (n : ℕ) :
    IsFlat T.schemeSite S T.scheme_mem (a.app (op (SimplexCategory.mk n))).hom := by
  let P : MorphismProperty T.Spaces := fun _ _ f => IsFlat T.schemeSite S T.scheme_mem f.hom
  have : P.IsStableUnderBaseChange := isFlat_isStableUnderBaseChange _ _ _
  have : P.IsMultiplicative :=
    { id_mem := fun Z => isFlat_id _ _ _ Z.2
      comp_mem := fun {Z₁ Z₂ Z₃} f g hf hg => isFlat_comp _ _ _ Z₁.2 Z₂.2 Z₃.2 f.hom g.hom hf hg }
  let A : SimplicialObject.Augmented T.Spaces := { left := U, right := X, hom := a }
  have hA : P.IsHypercovering A :=
    { map_zero := isFlat_of_singleton_mem_pretopology _ h.1
      map_one := isFlat_of_singleton_mem_pretopology _ h.2.1
      matching := fun n hn => isFlat_of_singleton_mem_pretopology _ (h.2.2 n hn) }
  exact MorphismProperty.IsHypercovering.hom_app hA n

variable (U) in
/-- The structure map of the inclusion of degree `n` is invertible. -/
instance isIso_degreeRingedToposHom_fSharpInverseImage (n : SimplexCategory) :
    IsIso (degreeRingedToposHom U n).fSharpInverseImage :=
  RingedToposHom.isIso_fSharpInverseImage_ofInverseImageIso
    (X := spacesEtaleRingedTopos T.schemeSite S T.scheme_mem (U.obj (op n)))
    (Y := ringedTopos U) _ _

variable (U) in
/-- The structure map of the inclusion of degree `n`, at the spelling of the modules
development, is invertible. -/
instance isIso_degreeRingedToposHom_toModulesHom_fSharpInverseImage (n : SimplexCategory) :
    IsIso (degreeRingedToposHom U n).toModulesHom.fSharpInverseImage :=
  RingedToposHom.isIso_toModulesHom_fSharpInverseImage (degreeRingedToposHom U n)

variable (U) in
/-- **Pullback to degree `n` is restriction to degree `n`**, read through restrictions of scalars
along the two identifications of structure sheaves. -/
def degreeRingedToposHomPullbackIso (n : SimplexCategory) :
    (degreeRingedToposHom U n).toModulesHom.pullbackModules ≅
      degreeRestrictModules (U := U) n ⋙
        SheafOfModules.restrictScalars (Stacks.Sheaves.ToposPullback.restrictionRingIso
          (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n))) (topology U)
          (degreeInclusion U n)
          (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O)).hom ⋙
        SheafOfModules.restrictScalars
          (asIso (degreeRingedToposHom U n).toModulesHom.fSharpInverseImage).inv :=
  Functor.isoWhiskerRight (Stacks.Sheaves.ToposPullback.restrictionModuleIso
      (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n))) (topology U)
      (degreeInclusion U n) (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O))
      (Stacks.Sheaves.RingedToposModules.extendScalarsFSharp
        (degreeRingedToposHom U n).toModulesHom) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.extendScalarsFSharpIsoRestrictScalarsOfIsIso
        (degreeRingedToposHom U n).toModulesHom))

/-- **The pullback `a^*` along the augmentation of an fppf hypercovering is exact.** In degree
`n` it is the pullback along `a_n : U_n ⟶ X` on the spaces-étale sites, which is flat (Stacks
0DER), and the pullbacks to the degrees are exact and jointly conservative. -/
theorem preservesFiniteLimits_augmentationRingedToposHom_pullbackModules
    (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a) :
    PreservesFiniteLimits
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules.{u + 1, u + 1, u + 1,
        u + 1, u + 1, u + 1} (augmentationRingedToposHom a).toModulesHom) := by
  have := RingedToposHom.pullbackModules_additive (augmentationRingedToposHom a)
  have : PreservesFiniteColimits (augmentationRingedToposHom a).toModulesHom.pullbackModules :=
    have : PreservesColimitsOfSize.{0, 0}
        (augmentationRingedToposHom a).toModulesHom.pullbackModules :=
      (RingedToposHom.pullbackAdjPushforwardModules
        (augmentationRingedToposHom a)).leftAdjoint_preservesColimits
    inferInstance
  have hex : ∀ n : SimplexCategory, PreservesFiniteLimits
        (degreeRingedToposHom U n).toModulesHom.pullbackModules ∧
      PreservesFiniteColimits (degreeRingedToposHom U n).toModulesHom.pullbackModules :=
    fun n => (exactFunctor_iff _).mp (RingedToposHom.pullbackModules_exact_of_isFlat
      (degreeRingedToposHom U n) (AlgebraicGeometry.SheafOfModules.isFlatMapULift_of_isIso
        (degreeRingedToposHom U n).fSharpInverseImage inferInstance))
  have hflat := fun n : SimplexCategory ↦
  preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact
    (a.app (op n)) (isFlat_app_of_isHypercoveringAugmentation h n.len)
  refine Functor.preservesFiniteLimits_of_comp_jointlyConservative _
    (fun n : SimplexCategory => (degreeRingedToposHom U n).toModulesHom.pullbackModules)
    (fun n => (hex n).1) (fun n => (hex n).2) ?_ ?_
  · intro M N φ hφ
    refine isIso_of_forall_isIso_degreeRestrictModules_map φ fun n => ?_
    have h1 := (NatIso.isIso_map_iff (degreeRingedToposHomPullbackIso U n) φ).1 (hφ n)
    have h2 := @isIso_of_reflects_iso _ _ _ _ _ _ _ (SheafOfModules.restrictScalars.{u + 1}
      (asIso (degreeRingedToposHom U n).toModulesHom.fSharpInverseImage).inv) h1 inferInstance
    exact @isIso_of_reflects_iso _ _ _ _ _ _ _ (SheafOfModules.restrictScalars.{u + 1}
      (Stacks.Sheaves.ToposPullback.restrictionRingIso
        (SpacesEtale.topology T.schemeSite S T.scheme_mem (U.obj (op n))) (topology U)
        (degreeInclusion U n) (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos U).O)).hom)
      h2 (Stacks.SheafOfModules.ChangeOfRings.reflectsIsomorphisms_restrictScalars _)
  · intro n
    have hn := hflat n
    exact preservesFiniteLimits_of_natIso
      ((RingedToposHom.TwoIso.pullbackModulesIso (augmentationDegreeTwoIso a n)).symm ≪≫
        RingedToposHom.pullbackModulesCompIso (degreeRingedToposHom U n)
          (augmentationRingedToposHom a))

/-- **Quasi-coherent modules on an fppf hypercovering form a weak Serre subcategory** of the
`𝒪_U`-modules on `U_{spaces,étale}`. -/
theorem isWeakSerreClass_isQuasicoherentOnSite_ringedSite
    (h : IsHypercoveringAugmentation T.pretopologyBigFppfPretopology U a) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u + 1, u + 1, u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u + 1, u + 1, u + 1} (J := (ringedSite U).J)
        (ringedSite U).O)).IsWeakSerreClass :=
  have := preservesFiniteLimits_augmentationRingedToposHom_pullbackModules h
  isWeakSerreClass_isQuasicoherentOnSite_ringedSite_of_preservesFiniteLimits h

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

end
