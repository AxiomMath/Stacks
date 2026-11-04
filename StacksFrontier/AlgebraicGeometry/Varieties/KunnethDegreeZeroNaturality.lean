module

public import StacksFrontier.Homology.Tor.ProductNaturality
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents
public import StacksFrontier.AlgebraicGeometry.Varieties.KunnethDegreeZeroGlobal

/-!
# Naturality of the degree-zero Künneth map

* `RingTheory.TorProducts.cohomologyTensorProduct_naturality`: the tensoring of classes of
  [Stacks, Tag 068H] is natural in both variables, at arbitrary objects of `D(R)`. The base proves
  it at K-projective K-flat sources; every class is the image of the generator of `Hⁱ(R[-i])`
  under a morphism `R[-i] ⟶ K` ([Stacks, Tag 06XS]), and `R[-i]` is such a source.
* `AlgebraicGeometry.degreeZeroKunnethMap_naturality`: the degree-zero Künneth map
  `H⁰RΓ(X, K) ⊗ H⁰RΓ(Y, M) ⟶ H⁰RΓ(X ×_k Y, Lp^*K ⊗^𝐋 Lq^*M)` is natural in `K` and `M`.

## References

* [Stacks Project, Tag 068H](https://stacks.math.columbia.edu/tag/068H)
* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
* [Stacks Project, Tag 0FLQ](https://stacks.math.columbia.edu/tag/0FLQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace RingTheory.TorProducts

open CochainComplex.DerivedTensor

variable {R : Type u} [CommRing R]

private abbrev singleR (n : ℤ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (CochainComplex.singleFunctor (ModuleCat.{u} R) n).obj (ModuleCat.of R R)

private instance projective_self : Projective (ModuleCat.of R R) := by
  haveI : Module.Projective R (ModuleCat.of R R) := inferInstanceAs (Module.Projective R R)
  exact ModuleCat.projective_of_categoryTheory_projective _

private theorem kFlat_singleR (n : ℤ) : (singleR (R := R) n).KFlat := by
  have h (m : ℤ) : Module.Flat R ((singleR (R := R) n).X m) := by
    by_cases hm : m = n
    · exact Module.Flat.of_linearEquiv
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) n
          (ModuleCat.of R R) m hm).toLinearEquiv
    · exact Module.Flat.of_linearEquiv
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n
          (ModuleCat.of R R) m hm).isoZero.toLinearEquiv
  exact CochainComplex.KFlat.kFlat_of_flat (singleR n) n

private instance isKProjective_singleR (n : ℤ) : (singleR (R := R) n).IsKProjective := by
  haveI : ∀ m : ℤ, Projective ((singleR (R := R) n).X m) := by
    intro m
    by_cases hm : m = n
    · exact Projective.of_iso
        (HomologicalComplex.singleObjXIsoOfEq (ComplexShape.up ℤ) n
          (ModuleCat.of R R) m hm).symm inferInstance
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) n
        (ModuleCat.of R R) m hm).projective
  exact CochainComplex.isKProjective_of_projective (singleR n) n

/-- The generator of `Hⁿ(R[-n])`. -/
private abbrev singleGenerator (n : ℤ) :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj
      (DerivedCategory.Q.obj (singleR (R := R) n)) :=
  (DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of R R)
    (DerivedCategory.Q.obj (singleR (R := R) n)) n R (𝟙 _)).hom (1 : R)

/-- Every class in `Hⁿ(Y)` is the image of the generator of `Hⁿ(R[-n])` under a morphism. -/
private theorem exists_rep (n : ℤ) (Y : DObj R)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj Y) :
    ∃ x' : DerivedCategory.Q.obj (singleR (R := R) n) ⟶ Y,
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).map x').hom
        (singleGenerator n) = x := by
  let ξ : ModuleCat.of R R ⟶ (DerivedCategory.homologyFunctor (ModuleCat.{u} R) n).obj Y :=
    ModuleCat.ofHom (LinearMap.toSpanSingleton R _ x)
  refine ⟨(DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of R R) Y n R).symm ξ, ?_⟩
  have h := DerivedCategory.homologyFromSingleLinearEquiv_comp (ModuleCat.of R R) _ n R (𝟙 _)
    ((DerivedCategory.homologyFromSingleLinearEquiv (ModuleCat.of R R) Y n R).symm ξ)
  rw [Category.id_comp, LinearEquiv.apply_symm_apply] at h
  have h₁ := congrArg (fun φ => φ.hom (1 : R)) h
  simp only [ξ, ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul,
    ModuleCat.hom_comp, LinearMap.comp_apply] at h₁
  exact h₁.symm

/-- **The tensoring of classes of [Stacks, Tag 068H] is natural in both variables.** -/
theorem cohomologyTensorProduct_naturality {K K' L L' : DObj R} (u : K ⟶ K') (v : L ⟶ L')
    (i j : ℤ) :
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map u ⊗ₘ
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map v) ≫
        (cohomologyTensorProduct K' L' i j).map =
      (cohomologyTensorProduct K L i j).map ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
          (((canonicalDerivedTensorProductFunctor R).map u).app L ≫
            ((canonicalDerivedTensorProductFunctor R).obj K').map v) := by
  apply ModuleCat.MonoidalCategory.tensor_ext
  intro x y
  obtain ⟨x', rfl⟩ := exists_rep i K x
  obtain ⟨y', rfl⟩ := exists_rep j L y
  have N1 := cohomologyTensorProduct_naturality_of_isKProjective (singleR i) (singleR j)
    (kFlat_singleR i) (kFlat_singleR j) x' y' i j
  have N2 := cohomologyTensorProduct_naturality_of_isKProjective (singleR i) (singleR j)
    (kFlat_singleR i) (kFlat_singleR j) (x' ≫ u) (y' ≫ v) i j
  have hT : ((canonicalDerivedTensorProductFunctor R).map (x' ≫ u)).app
        (DerivedCategory.Q.obj (singleR j)) ≫
        ((canonicalDerivedTensorProductFunctor R).obj K').map (y' ≫ v) =
      (((canonicalDerivedTensorProductFunctor R).map x').app (DerivedCategory.Q.obj (singleR j)) ≫
        ((canonicalDerivedTensorProductFunctor R).obj K).map y') ≫
      (((canonicalDerivedTensorProductFunctor R).map u).app L ≫
        ((canonicalDerivedTensorProductFunctor R).obj K').map v) := by
    simp only [Functor.map_comp, NatTrans.comp_app, Category.assoc]
    rw [← NatTrans.naturality_assoc]
  have hmor : ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map x' ⊗ₘ
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map y') ≫
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map u ⊗ₘ
          (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map v) ≫
        (cohomologyTensorProduct K' L' i j).map =
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map x' ⊗ₘ
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) j).map y') ≫
      (cohomologyTensorProduct K L i j).map ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) (i + j)).map
          (((canonicalDerivedTensorProductFunctor R).map u).app L ≫
            ((canonicalDerivedTensorProductFunctor R).obj K').map v) := by
    rw [tensorHom_comp_tensorHom_assoc, ← Functor.map_comp, ← Functor.map_comp, N2, hT,
      Functor.map_comp, reassoc_of% N1]
  exact congrArg (fun φ => φ.hom (singleGenerator i ⊗ₜ singleGenerator j)) hmor

end RingTheory.TorProducts

namespace AlgebraicGeometry

open Stacks.Cohomology.GlobalKunneth (baseRing sectionsOverBase)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor)

variable (k : Type u) [Field k] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of k)) (g : Y ⟶ Spec (.of k))

/-- **The degree-zero Künneth map is natural in both variables.** -/
theorem degreeZeroKunnethMap_naturality {K K' : DerivedCategory X.Modules}
    {M M' : DerivedCategory Y.Modules} (u : K ⟶ K') (v : M ⟶ M') :
    ((DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0).map
          ((sectionsOverBase f.toLRSHom.toShHom).map u) ⊗ₘ
        (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0).map
          ((sectionsOverBase g.toLRSHom.toShHom).map v)) ≫ degreeZeroKunnethMap k f g K' M' =
      degreeZeroKunnethMap k f g K M ≫
        (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (.of k)).toRingedSpace)) 0).map
          ((sectionsOverBase (Limits.pullback.fst f g ≫ f).toLRSHom.toShHom).map
            (((derivedTensorProductFunctor (Limits.pullback f g).toRingedSpace.sheaf).map
                ((derivedPullback (Limits.pullback.fst f g).toLRSHom.toShHom).map u)).app
                  ((derivedPullback (Limits.pullback.snd f g).toLRSHom.toShHom).obj M) ≫
              ((derivedTensorProductFunctor (Limits.pullback f g).toRingedSpace.sheaf).obj
                ((derivedPullback (Limits.pullback.fst f g).toLRSHom.toShHom).obj K')).map
                ((derivedPullback (Limits.pullback.snd f g).toLRSHom.toShHom).map v))) := by
  have hk := Stacks.Cohomology.GlobalKunneth.kunnethGlobalMapScheme_naturality f g
    (canonicalGlobalCupProduct k) u v
  simp only [Functor.uncurry_obj_map] at hk
  unfold degreeZeroKunnethMap
  rw [reassoc_of% (RingTheory.TorProducts.cohomologyTensorProduct_naturality
    ((sectionsOverBase f.toLRSHom.toShHom).map u) ((sectionsOverBase g.toLRSHom.toShHom).map v)
    0 0), Category.assoc]
  refine congrArg (fun φ => (RingTheory.TorProducts.cohomologyTensorProduct
    ((sectionsOverBase f.toLRSHom.toShHom).obj K) ((sectionsOverBase g.toLRSHom.toShHom).obj M)
      0 0).map ≫ φ) ?_
  rw [← Functor.map_comp]
  exact (congrArg (DerivedCategory.homologyFunctor _ (0 + 0)).map hk).trans (Functor.map_comp _ _ _)

end AlgebraicGeometry
