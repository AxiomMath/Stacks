module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.TensorPullbackComplexDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ComplexSupport
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackSupport

/-!
# The complex `𝒢^• ⊗ f^*ℱ` for a module `ℱ`: degrees and support

Let `f : X ⟶ Y` be a morphism of algebraic spaces, `𝒢^•` a complex of `𝒪_X`-modules and `ℱ` an
`𝒪_Y`-module.  The complex `𝒢^• ⊗ f^*ℱ` (`AlgebraicGeometry.Space.tensorPullbackComplex` at
`ℱ[0]`) has `𝒢ⁿ ⊗ f^*ℱ` in degree `n`.  Hence

* it vanishes in the degrees where `𝒢^•` does, so its class in `D(𝒪_X)` lies in degrees `≥ a`
  when `𝒢ⁿ = 0` for `n < a`;
* its cohomology is supported on any `T ⊆ |X|` containing the supports of the `𝒢ⁿ`
  (Stacks 08GF), the stalk of `𝒢ⁿ ⊗ f^*ℱ` vanishing where that of `𝒢ⁿ` does.

These are the degree and support statements used in the proof of Stacks 08JR.

## References

* [Stacks Project, Tag 08JR](https://stacks.math.columbia.edu/tag/08JR)
* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {X Y : AlgebraicSpaces B S hS}

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] hasMapBifunctor_sheafTensor_smallEtaleRingedTopos

variable (f : X ⟶ Y)
  (G : CochainComplex (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) ℤ)

/-- The term of degree `n` of `𝒢^• ⊗ f^*ℱ` is `𝒢ⁿ ⊗ f^*ℱ`. -/
def tensorPullbackComplexSingleXIso
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (n : ℤ) :
    ((tensorPullbackComplex f G).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).X n ≅
      ((tensorPullbackBifunctor f).obj (G.X n)).obj F :=
  (HomologicalComplex.eval _ _ n).mapIso
    (CochainComplex.KFlatBifunctor.totalSingleIso (tensorPullbackBifunctor f) G F)

/-- **`𝒢^• ⊗ f^*ℱ` vanishes in the degrees where `𝒢^•` does.** -/
theorem isZero_tensorPullbackComplex_single_X
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) (n : ℤ)
    (hn : IsZero (G.X n)) :
    IsZero (((tensorPullbackComplex f G).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).X n) :=
  (CochainComplex.KFlatBifunctor.isZero_obj_obj_of_isZero (tensorPullbackBifunctor f) hn F).of_iso
    (tensorPullbackComplexSingleXIso f G F n)

/-- **`𝒢^• ⊗ f^*ℱ` lies in degrees `≥ a`** when `𝒢ⁿ = 0` for `n < a`. -/
theorem isGE_Q_obj_tensorPullbackComplex_single (a : ℤ) (hG : ∀ n : ℤ, n < a → IsZero (G.X n))
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    (DerivedCategory.Q.obj ((tensorPullbackComplex f G).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))).IsGE a := by
  have : ((tensorPullbackComplex f G).obj
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)).IsStrictlyGE a :=
    (CochainComplex.isStrictlyGE_iff _ a).2 fun n hn =>
      isZero_tensorPullbackComplex_single_X f G F n (hG n hn)
  infer_instance

/-- **The stalk of `M ⊗ N` vanishes where that of `M` does**: the support of `M ⊗ N` lies in the
support of `M`. -/
theorem supportOfSheaf_sheafTensor_subset_left
    (M N : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X)) :
    supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (smallEtaleRingedTopos B S hS X).O).obj M).obj N)) ⊆
      supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj M) := by
  intro x hx
  by_contra h
  refine (notMem_supportOfSheaf_iff_forall_isZero_sheafFiber B S hS X.1 X.2 _ x).2
    (fun p hp => ?_) hx
  exact Stacks.isZero_sheafFiber_sheafTensor_of_left (etaleSitePoint B S hS X.1 p X.2)
    (smallEtaleRingedTopos B S hS X).O M N (isZero_moduleSheafFiber_of_notMem B S hS X M x h p hp)

/-- **The cohomology of `𝒢^• ⊗ f^*ℱ` is supported on `T`** if the supports of the `𝒢ⁿ` are
(Stacks 08GF). -/
theorem cohomologySupportedOn_Q_obj_tensorPullbackComplex_single (T : Set (points B S hS X.1))
    (hG : ∀ n : ℤ, supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj (G.X n)) ⊆ T)
    (F : SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS Y)) :
    CohomologySupportedOn.{u, u} B S hS X.1 X.2 T (DerivedCategory.Q.obj
      ((tensorPullbackComplex f G).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F))) :=
  cohomologySupportedOn_Q_obj_of_supportOfSheaf_X_subset X _ T fun n =>
    (supportOfSheaf_eq_of_iso B S hS X (tensorPullbackComplexSingleXIso f G F n)).le.trans <|
      (supportOfSheaf_sheafTensor_subset_left _ _).trans (hG n)

end AlgebraicGeometry.Space

end
