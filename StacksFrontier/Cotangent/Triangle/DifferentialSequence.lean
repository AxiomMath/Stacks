module

public import Mathlib.Algebra.Category.CommAlgCat.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Exact
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Cotangent.Complex
public import StacksFrontier.Cotangent.ExtendScalars
public import StacksFrontier.Cotangent.Triangle.BaseChange
public import StacksFrontier.RingTheory.Kaehler.BaseChange

/-!
# The differential sequence of the fundamental triangle

For an injective map of commutative algebras `B → C` over `A`, the differentials of the two
standard resolutions and of the base-changed relative resolution form a short exact sequence of
simplicial modules over `C`. This is the sequence whose associated triangle is the fundamental
triangle of the cotangent complex.

## Main definitions

* `CommAlgCat.canonicalBaseChangeMap`: the pushout leg from the standard resolution of `C` to
  the base-changed resolution.
* `CommAlgCat.relativeCotangentTerm`, `CommAlgCat.relativeCotangentMap` and
  `CommAlgCat.relativeCotangentSimplicialObject`: the third term of the sequence, degreewise the
  base-changed relative differentials of the base-changed resolution.
* `CommAlgCat.differentialSequenceFirstMap` and `CommAlgCat.differentialSequenceSecondMap`: the
  two maps of the sequence.
* `CommAlgCat.DifferentialSequenceData` and
  `CommAlgCat.standardResolutionDifferentialSequence`: the differential short complex together
  with the identifications of its three terms.

## Main results

* `CommAlgCat.standardResolution_differentials_shortExact`: the complex is short exact.
* `CommAlgCat.standardResolution_differentials_firstMap`,
  `CommAlgCat.standardResolution_differentials_secondMap`,
  `CommAlgCat.standardResolution_differentials_third_naturality`,
  `CommAlgCat.standardResolution_differentials_pushout`,
  `CommAlgCat.standardResolution_differentials_toBaseChange_naturality` and
  `CommAlgCat.standardResolution_differentials_toBaseChange_augmentation` specify the maps on
  differentials, the pushout property of the base-change leg and their naturality.

## Implementation notes

The first two terms are the canonical cotangent simplicial modules of
`StacksFrontier.Cotangent.Complex`, with the first extended from `B` to `C`. The third term is
identified degreewise with the differentials of the base-changed resolution. The differential
maps and the third simplicial structure are specified on pure differentials.

Short exactness is checked degreewise: in each simplicial degree the sequence is the scalar
extension to `C` of the differential sequence of the tower `A → Pₙ → Qₙ`, which is split
because `Pₙ → Qₙ` is a polynomial extension, hence formally smooth.

## References

* [Stacks Project, Tag 08SD](https://stacks.math.columbia.edu/tag/08SD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Simplicial
open scoped ChangeOfRings TensorProduct

universe u v

namespace CommAlgCat


/-- The canonical map from a term of the standard resolution of `C` to the corresponding term
of the base-changed resolution: the first leg of the degreewise pushout. -/
noncomputable def canonicalBaseChangeMap
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    (standardResolution A C).left.obj n →+*
      (baseChangedStandardResolution A f).left.obj n := by
  let F : CommAlgCat.{max u v} A ⥤ CommRingCat.{max u v} :=
    forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}
  let E := (commAlgCatEquivUnder (CommRingCat.of B)).inverse
  let P := standardResolution A B
  let Q := standardResolution A C
  let g := whiskerRight (((standardResolutionFunctor A).map f).left) F
  let h := whiskerRight P.hom F
  let k := whiskerRight Q.hom F
  let l := whiskerRight ((SimplicialObject.const _).map f) F
  let w : g ≫ k = h ≫ l := by
    dsimp [g, h, k, l, P, Q]
    exact congrArg (fun η => whiskerRight η F)
      (((standardResolutionFunctor A).map f).w)
  let X : SimplexCategoryᵒᵖ ⥤ CommRingCat.{max u v} := pushout g h
  let s : (Functor.const SimplexCategoryᵒᵖ).obj (CommRingCat.of B) ⟶ X := pushout.inr g h
  let U : SimplexCategoryᵒᵖ ⥤ Under (CommRingCat.of B) := Under.lift X s
  change (standardResolution A C).left.obj n →+* E.obj (U.obj n)
  exact ((pushout.inl g h).app n).hom

private theorem canonicalBaseChangeMap_naturality
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    {i j : SimplexCategoryᵒᵖ} (h : i ⟶ j) :
    (((baseChangedStandardResolution A f).left.map h).hom.toRingHom).comp
      (canonicalBaseChangeMap A f i) =
    (canonicalBaseChangeMap A f j).comp
      ((((standardResolution A C).left.map h).hom).toRingHom) := by
  let F : CommAlgCat.{max u v} A ⥤ CommRingCat.{max u v} :=
    forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}
  let P := standardResolution A B
  let g := whiskerRight (((standardResolutionFunctor A).map f).left) F
  let d := whiskerRight P.hom F
  have hn := (pushout.inl g d).naturality h
  ext q
  show ((pushout g d).map h).hom (((pushout.inl g d).app i).hom q) =
    ((pushout.inl g d).app j).hom ((((standardResolution A C).left.map h).hom) q)
  exact congrArg (fun φ : CommRingCat.Hom _ _ => φ.hom q) hn.symm

private theorem canonicalBaseChangeMap_augmentation
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    (((baseChangedStandardResolution A f).hom.app n).hom.toRingHom).comp
      (canonicalBaseChangeMap A f n) = standardResolutionAugmentationHom A C n := by
  let F : CommAlgCat.{max u v} A ⥤ CommRingCat.{max u v} :=
    forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}
  let P := standardResolution A B
  let Q := standardResolution A C
  let g := whiskerRight (((standardResolutionFunctor A).map f).left) F
  let h := whiskerRight P.hom F
  let k := whiskerRight Q.hom F
  let l := whiskerRight ((SimplicialObject.const _).map f) F
  let w : g ≫ k = h ≫ l := by
    dsimp [g, h, k, l, P, Q]
    exact congrArg (fun η => whiskerRight η F)
      (((standardResolutionFunctor A).map f).w)
  let X := pushout g h
  let a : X ⟶ (SimplicialObject.const _).obj C ⋙ F := pushout.desc k l w
  ext q
  show (a.app n).hom (((pushout.inl g h).app n).hom q) =
    (F.map ((standardResolution A C).hom.app n)).hom q
  have hdesc := congrArg (fun η => η.app n) (pushout.inl_desc k l w)
  change ((pushout.inl g h).app n ≫ a.app n) = k.app n at hdesc
  have hq := congrArg (fun φ : CommRingCat.Hom _ _ => φ.hom q) hdesc
  simpa [X, k, whiskerRight_app] using hq

private theorem canonicalBaseChangeMap_isPushout
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    CategoryTheory.IsPushout
      (CommRingCat.ofHom
        (((standardResolutionFunctor A).map f).left.app n).hom.toRingHom)
      (CommRingCat.ofHom (standardResolutionAugmentationHom A B n))
      (CommRingCat.ofHom (canonicalBaseChangeMap A f n))
      (CommRingCat.ofHom
        (algebraMap B
          ((baseChangedStandardResolution A f).left.obj n))) := by
  let F : CommAlgCat.{max u v} A ⥤ CommRingCat.{max u v} :=
    forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}
  let P := standardResolution A B
  let g := whiskerRight (((standardResolutionFunctor A).map f).left) F
  let h := whiskerRight P.hom F
  exact (IsPushout.of_hasPushout g h).app n

/-- The pushout leg and the map of standard resolutions agree on the augmentation square. -/
private theorem canonicalBaseChangeMap_comp_eq
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    (canonicalBaseChangeMap A f n).comp
        (((standardResolutionFunctor A).map f).left.app n).hom.toRingHom =
      (algebraMap B ((baseChangedStandardResolution A f).left.obj n)).comp
        (standardResolutionAugmentationHom A B n) :=
  RingHom.ext fun p =>
    congrArg (fun z : CommRingCat.Hom _ _ => z.hom p) (canonicalBaseChangeMap_isPushout A f n).w

/-- For a tower `R → A → B` with `B` formally smooth over `A`, the differentials form a short
exact sequence `0 → B ⊗[A] Ω[A⁄R] → Ω[B⁄R] → Ω[B⁄A] → 0`, split by a retraction. -/
theorem towerDifferential_shortExact (R : Type u) (A B : Type (max u v)) [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra A B] [Algebra R B]
    [IsScalarTower R A B] [Algebra.FormallySmooth A B] :
    ShortComplex.ShortExact (ShortComplex.moduleCatMk (KaehlerDifferential.mapBaseChange R A B)
      (KaehlerDifferential.map R A B B) (by
        apply LinearMap.ext
        intro x
        exact (KaehlerDifferential.exact_mapBaseChange_map R A B).apply_apply_eq_zero x)) := by
  obtain ⟨r, hr⟩ := KaehlerDifferential.exists_retraction_mapBaseChange R A B
  exact .mk' ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).2
      (KaehlerDifferential.exact_mapBaseChange_map R A B))
    ((ModuleCat.mono_iff_injective _).2 (Function.LeftInverse.injective (g := r)
      fun z => LinearMap.congr_fun hr z))
    ((ModuleCat.epi_iff_surjective _).2 (KaehlerDifferential.map_surjective R A B))

private theorem standardResolution_map_formallySmooth
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (hf : Function.Injective f.hom) (n : SimplexCategoryᵒᵖ) :
    let P := (standardResolution A B).left.obj n
    let Q := (standardResolution A C).left.obj n
    letI : Algebra P Q :=
      (((standardResolutionFunctor A).map f).left.app n).hom.toAlgebra
    Algebra.FormallySmooth P Q := by
  let P := (standardResolution A B).left.obj n
  let Q := (standardResolution A C).left.obj n
  let g := ((standardResolutionFunctor A).map f).left.app n
  let _ : Algebra P Q := g.hom.toRingHom.toAlgebra
  obtain ⟨ι, ⟨e⟩⟩ := standardResolution_isPolynomialAlgebra A f hf n
  exact Algebra.FormallySmooth.of_equiv e

private theorem standardResolution_towerDifferential_shortExact
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (hf : Function.Injective f.hom) (n : SimplexCategoryᵒᵖ) :
    let P := (standardResolution A B).left.obj n
    let Q := (standardResolution A C).left.obj n
    letI : Algebra P Q :=
      (((standardResolutionFunctor A).map f).left.app n).hom.toAlgebra
    ShortComplex.ShortExact (ShortComplex.moduleCatMk
      (KaehlerDifferential.mapBaseChange A P Q)
      (KaehlerDifferential.map A P Q Q) (by
        apply LinearMap.ext
        intro x
        exact (KaehlerDifferential.exact_mapBaseChange_map A P Q).apply_apply_eq_zero x)) := by
  let P := (standardResolution A B).left.obj n
  let Q := (standardResolution A C).left.obj n
  let g := ((standardResolutionFunctor A).map f).left.app n
  let _ : Algebra P Q := g.hom.toRingHom.toAlgebra
  have : IsScalarTower A P Q :=
    IsScalarTower.of_algebraMap_eq (fun a => (g.hom.commutes a).symm)
  have : Algebra.FormallySmooth P Q :=
    standardResolution_map_formallySmooth A f hf n
  exact towerDifferential_shortExact A P Q

/-- Extension of scalars along a ring map is additive. -/
private theorem extendScalars_additive.{w} {R S : Type w} [CommRing R] [CommRing S]
    (ε : R →+* S) : (ModuleCat.extendScalars.{w, w, w} ε).Additive := by
  have : (ModuleCat.extendScalars ε).IsLeftAdjoint :=
    (ModuleCat.extendRestrictScalarsAdj ε).isLeftAdjoint
  have : PreservesBinaryBiproducts (ModuleCat.extendScalars ε) :=
    preservesBinaryBiproducts_of_preservesBinaryCoproducts _
  exact Functor.additive_of_preservesBinaryBiproducts _

private theorem standardResolution_towerDifferential_shortExact_extendScalars
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (hf : Function.Injective f.hom) (n : SimplexCategoryᵒᵖ) :
    let P := (standardResolution A B).left.obj n
    let Q := (standardResolution A C).left.obj n
    letI : Algebra P Q :=
      (((standardResolutionFunctor A).map f).left.app n).hom.toAlgebra
    letI : Algebra Q C := (standardResolutionAugmentationHom A C n).toAlgebra
    ((ShortComplex.moduleCatMk (KaehlerDifferential.mapBaseChange A P Q)
      (KaehlerDifferential.map A P Q Q) (by
        apply LinearMap.ext
        intro x
        exact (KaehlerDifferential.exact_mapBaseChange_map A P Q).apply_apply_eq_zero x)).map
      (ModuleCat.extendScalars (standardResolutionAugmentationHom A C n))).ShortExact := by
  let P := (standardResolution A B).left.obj n
  let Q := (standardResolution A C).left.obj n
  let ε := standardResolutionAugmentationHom A C n
  let g := ((standardResolutionFunctor A).map f).left.app n
  let _ : Algebra P Q := g.hom.toRingHom.toAlgebra
  have : IsScalarTower A P Q :=
    IsScalarTower.of_algebraMap_eq (fun a => (g.hom.commutes a).symm)
  have : Algebra.FormallySmooth P Q :=
    standardResolution_map_formallySmooth A f hf n
  let _ : Algebra Q C := ε.toAlgebra
  let S := ShortComplex.moduleCatMk (KaehlerDifferential.mapBaseChange A P Q)
    (KaehlerDifferential.map A P Q Q)
    (LinearMap.ext (KaehlerDifferential.exact_mapBaseChange_map A P Q).apply_apply_eq_zero)
  have hS := standardResolution_towerDifferential_shortExact A f hf n
  obtain ⟨r, hr⟩ := KaehlerDifferential.exists_retraction_mapBaseChange A P Q
  have s : S.Splitting := ShortComplex.Splitting.ofExactOfRetraction S hS.exact
    (ModuleCat.ofHom r) (by ext x; exact LinearMap.congr_fun hr x) hS.epi_g
  let F := ModuleCat.extendScalars ε
  have : F.Additive := extendScalars_additive ε
  exact (s.map F).shortExact

/-- The `n`th term of the third member of the differential sequence: the differentials of the
base-changed resolution over `B`, base changed to `C`. -/
noncomputable def relativeCotangentTerm
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) : ModuleCat.{max u v} C := by
  let R := baseChangedStandardResolution A f
  let T := R.left.obj n
  let ε := (R.hom.app n).hom.toRingHom
  letI : Algebra T C := ε.toAlgebra
  exact ModuleCat.of C (C ⊗[T] KaehlerDifferential B T)

/-- The pure differential `1 ⊗ d t` in the `n`th term of the third member of the sequence. -/
noncomputable def relativeCotangentTermDifferential
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ)
    (t : (baseChangedStandardResolution A f).left.obj n) :
    relativeCotangentTerm A f n := by
  let R := baseChangedStandardResolution A f
  let T := R.left.obj n
  letI : Algebra T C := ((R.hom.app n).hom.toRingHom).toAlgebra
  exact (1 : C) ⊗ₜ[T] KaehlerDifferential.D B T t

/-- The identification of `C ⊗[Qₙ] Ω[Qₙ⁄Pₙ]` with the base-changed relative differentials
`C ⊗[Tₙ] Ω[Tₙ⁄B]` of the base-changed resolution, coming from the pushout square. -/
noncomputable def relativeCotangentBaseChangeEquiv
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    let P := (standardResolution A B).left.obj n
    let Q := (standardResolution A C).left.obj n
    letI : Algebra P Q :=
      (((standardResolutionFunctor A).map f).left.app n).hom.toAlgebra
    letI : Algebra Q C := (standardResolutionAugmentationHom A C n).toAlgebra
    ModuleCat.of C (C ⊗[Q] KaehlerDifferential P Q) ≅
      relativeCotangentTerm A f n :=
  let hpushout :
    CategoryTheory.IsPushout
      (CommRingCat.ofHom
        (((standardResolutionFunctor A).map f).left.app n).hom.toRingHom)
      (CommRingCat.ofHom (standardResolutionAugmentationHom A B n))
      (CommRingCat.ofHom (canonicalBaseChangeMap A f n))
      (CommRingCat.ofHom
        (algebraMap B
          ((baseChangedStandardResolution A f).left.obj n))) := by
    exact canonicalBaseChangeMap_isPushout A f n
  let hscalar_compat :
    (((baseChangedStandardResolution A f).hom.app n).hom.toRingHom).comp
      (canonicalBaseChangeMap A f n) = standardResolutionAugmentationHom A C n := by
    exact canonicalBaseChangeMap_augmentation A f n
  by
    let P := (standardResolution A B).left.obj n
    let Q := (standardResolution A C).left.obj n
    let T := (baseChangedStandardResolution A f).left.obj n
    let η : P →ₐ[A] Q := (((standardResolutionFunctor A).map f).left.app n).hom
    let ι : P →+* B := standardResolutionAugmentationHom A B n
    let δ : Q →+* T := canonicalBaseChangeMap A f n
    let ε : B →+* T := algebraMap B T
    letI : Algebra P Q := η.toRingHom.toAlgebra
    letI : Algebra P B := ι.toAlgebra
    letI : Algebra Q T := δ.toAlgebra
    letI : Algebra B T := ε.toAlgebra
    letI : Algebra P T := (δ.comp η.toRingHom).toAlgebra
    have hcomm : δ.comp η.toRingHom = ε.comp ι :=
      RingHom.ext fun p => congrArg (fun k : CommRingCat.Hom _ _ => k.hom p) hpushout.w
    letI : IsScalarTower P Q T := IsScalarTower.of_algebraMap_eq' rfl
    letI : IsScalarTower P B T := IsScalarTower.of_algebraMap_eq' hcomm
    letI : Algebra.IsPushout P B Q T := CommRingCat.isPushout_iff_isPushout.mp hpushout.flip
    letI : Algebra T C :=
      (((baseChangedStandardResolution A f).hom.app n).hom.toRingHom).toAlgebra
    letI : Algebra Q C := (standardResolutionAugmentationHom A C n).toAlgebra
    letI : IsScalarTower Q T C := IsScalarTower.of_algebraMap_eq' hscalar_compat.symm
    let E := KaehlerDifferential.tensorKaehlerEquiv P B Q T
    let e₁ : C ⊗[T] KaehlerDifferential B T ≃ₗ[C]
        C ⊗[T] (T ⊗[Q] KaehlerDifferential P Q) :=
      TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) E.symm
    let e₂ : C ⊗[T] (T ⊗[Q] KaehlerDifferential P Q) ≃ₗ[C]
        C ⊗[Q] KaehlerDifferential P Q :=
      TensorProduct.AlgebraTensorModule.cancelBaseChange Q T C C
        (KaehlerDifferential P Q)
    let e := e₁.trans e₂
    exact e.symm.toModuleIso

/-- The `B`-linear map whose associated extension of scalars is the simplicial structure map
of the third member of the sequence. -/
noncomputable def relativeCotangentMapAdjoint
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    {i j : SimplexCategoryᵒᵖ} (h : i ⟶ j) :
    ModuleCat.of ((baseChangedStandardResolution A f).left.obj i)
        (KaehlerDifferential B ((baseChangedStandardResolution A f).left.obj i)) ⟶
      (ModuleCat.restrictScalars
        (((baseChangedStandardResolution A f).hom.app i).hom.toRingHom)).obj
        (relativeCotangentTerm A f j) := by
  let R := baseChangedStandardResolution A f
  let Ti := R.left.obj i
  let Tj := R.left.obj j
  let η : Ti →ₐ[B] Tj := (R.left.map h).hom
  letI : Algebra Ti Tj := η.toRingHom.toAlgebra
  let εi : Ti →+* C := (R.hom.app i).hom.toRingHom
  let εj : Tj →+* C := (R.hom.app j).hom.toRingHom
  letI : Algebra Ti C := εi.toAlgebra
  letI : Algebra Tj C := εj.toAlgebra
  haveI : IsScalarTower B Ti Tj :=
    IsScalarTower.of_algebraMap_eq (fun b => (η.commutes b).symm)
  have hscalar : εi = εj.comp η.toRingHom :=
    (congrArg (fun k => k.hom.toRingHom) (by simp : R.left.map h ≫ R.hom.app j = R.hom.app i)).symm
  haveI : IsScalarTower Ti Tj C := IsScalarTower.of_algebraMap_eq' hscalar
  letI : Module Ti (relativeCotangentTerm A f j) := Module.compHom _ εi
  let M := ModuleCat.of Ti (KaehlerDifferential B Ti)
  let d : M ⟶ (ModuleCat.restrictScalars εi).obj (relativeCotangentTerm A f j) :=
    ModuleCat.ofHom {
      toFun := fun ω => (1 : C) ⊗ₜ[Tj] KaehlerDifferential.map B B Ti Tj ω
      map_add' := by
        intro x y
        change (TensorProduct.mk Tj C (KaehlerDifferential B Tj) (1 : C))
            (KaehlerDifferential.map B B Ti Tj (x + y)) = _
        rw [map_add (KaehlerDifferential.map B B Ti Tj) x y]
        exact (TensorProduct.mk Tj C (KaehlerDifferential B Tj) (1 : C)).map_add _ _
      map_smul' := by
        intro r x
        change (1 : C) ⊗ₜ[Tj]
            KaehlerDifferential.map B B Ti Tj (r • x) =
          εi r • ((1 : C) ⊗ₜ[Tj] KaehlerDifferential.map B B Ti Tj x)
        rw [map_smul (KaehlerDifferential.map B B Ti Tj) r x,
          TensorProduct.tmul_smul, TensorProduct.smul_tmul']
        congr 1 }
  exact d

/-- The simplicial structure map of the third member of the sequence. -/
noncomputable def relativeCotangentMap
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    {i j : SimplexCategoryᵒᵖ} (h : i ⟶ j) :
    relativeCotangentTerm A f i ⟶ relativeCotangentTerm A f j := by
  let R := baseChangedStandardResolution A f
  let εi := (R.hom.app i).hom.toRingHom
  change (ModuleCat.extendScalars εi).obj (ModuleCat.of (R.left.obj i)
      (KaehlerDifferential B (R.left.obj i))) ⟶ _
  exact ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars εi
    (relativeCotangentMapAdjoint A f h)

private theorem relativeCotangentMap_differential
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    {i j : SimplexCategoryᵒᵖ} (h : i ⟶ j)
    (t : (baseChangedStandardResolution A f).left.obj i) :
    relativeCotangentMap A f h (relativeCotangentTermDifferential A f i t) =
      relativeCotangentTermDifferential A f j
        ((baseChangedStandardResolution A f).left.map h t) := by
  let R := baseChangedStandardResolution A f
  let Ti := R.left.obj i
  let Tj := R.left.obj j
  let η : Ti →ₐ[B] Tj := (R.left.map h).hom
  let _ : Algebra Ti Tj := η.toRingHom.toAlgebra
  let εi : Ti →+* C := (R.hom.app i).hom.toRingHom
  let εj : Tj →+* C := (R.hom.app j).hom.toRingHom
  let _ : Algebra Ti C := εi.toAlgebra
  let _ : Algebra Tj C := εj.toAlgebra
  have : IsScalarTower B Ti Tj :=
    IsScalarTower.of_algebraMap_eq (fun b => (η.commutes b).symm)
  have hscalar : εi = εj.comp η.toRingHom :=
    (congrArg (fun k => k.hom.toRingHom) (by simp : R.left.map h ≫ R.hom.app j = R.hom.app i)).symm
  have : IsScalarTower Ti Tj C := IsScalarTower.of_algebraMap_eq' hscalar
  let _ : Module Ti (relativeCotangentTerm A f j) := Module.compHom _ εi
  refine (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul εi
    (relativeCotangentMapAdjoint A f h) (1 : C) (KaehlerDifferential.D B Ti t)).trans ?_
  rw [one_smul]
  show (1 : C) ⊗ₜ[Tj]
      (KaehlerDifferential.map B B Ti Tj (KaehlerDifferential.D B Ti t)) = _
  rw [KaehlerDifferential.map_D]
  rfl

private theorem relativeCotangentHom_ext
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (i : SimplexCategoryᵒᵖ) {N : ModuleCat.{max u v} C}
    (α β : relativeCotangentTerm A f i ⟶ N)
    (h : ∀ t : (baseChangedStandardResolution A f).left.obj i,
      α (relativeCotangentTermDifferential A f i t) =
        β (relativeCotangentTermDifferential A f i t)) : α = β := by
  let R := baseChangedStandardResolution A f
  let T := R.left.obj i
  let _ : Algebra T C := ((R.hom.app i).hom.toRingHom).toAlgebra
  exact ModuleCat.baseChange_kaehlerDifferential_hom_ext
    (A := (B : Type (max u v))) (R := (T : Type (max u v))) α β h

/-- The third member of the differential sequence as a simplicial `C`-module. -/
noncomputable def relativeCotangentSimplicialObject
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) :
    SimplicialObject (ModuleCat.{max u v} C) :=
  { obj := relativeCotangentTerm A f
    map := fun h => relativeCotangentMap A f h
    map_id := by
      intro i
      apply relativeCotangentHom_ext A f i
      intro t
      simp [relativeCotangentMap_differential]
    map_comp := by
      intro i j k h g
      apply relativeCotangentHom_ext A f i
      intro t
      simp [relativeCotangentMap_differential] }

private theorem standardResolution_augmentation_map_naturality
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    (standardResolutionAugmentationHom A C n).comp
        (((standardResolutionFunctor A).map f).left.app n).hom.toRingHom =
      f.hom.toRingHom.comp (standardResolutionAugmentationHom A B n) := by
  let F : CommAlgCat.{max u v} A ⥤ CommRingCat.{max u v} :=
    forget₂ (CommAlgCat.{max u v} A) CommRingCat.{max u v}
  let P := standardResolution A B
  let Q := standardResolution A C
  let g := whiskerRight (((standardResolutionFunctor A).map f).left) F
  let h := whiskerRight P.hom F
  let k := whiskerRight Q.hom F
  let l := whiskerRight ((SimplicialObject.const _).map f) F
  have w : g ≫ k = h ≫ l := by
    dsimp [g, h, k, l, P, Q]
    exact congrArg (fun η => whiskerRight η F)
      (((standardResolutionFunctor A).map f).w)
  ext p
  exact congrArg (fun η : CommRingCat.Hom _ _ => η.hom p) (congrArg (fun η => η.app n) w)

private theorem standardResolution_augmentation_commutes
    (A : Type u) [CommRing A] (B : CommAlgCat.{max u v} A)
    (n : SimplexCategoryᵒᵖ) (a : A) :
    standardResolutionAugmentationHom A B n
        (algebraMap A ((standardResolution A B).left.obj n) a) =
      algebraMap A B a :=
  ((standardResolution A B).hom.app n).hom.commutes a

/-- The degreewise first map of the differential sequence: the differentials of the standard
resolution of `B`, extended to `C`, mapped to the differentials of the standard resolution
of `C`. -/
noncomputable def differentialSequenceFirstComponent
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    (ModuleCat.extendScalars f.hom.toRingHom).obj (cotangentTerm A B n) ⟶
      cotangentTerm A C n :=
  let hcomm_compat :
    (standardResolutionAugmentationHom A C n).comp
        (((standardResolutionFunctor A).map f).left.app n).hom.toRingHom =
      f.hom.toRingHom.comp (standardResolutionAugmentationHom A B n) := by
    exact standardResolution_augmentation_map_naturality A f n
  by
    let P := (standardResolution A B).left.obj n
    let Q := (standardResolution A C).left.obj n
    let η : P →ₐ[A] Q := ((standardResolutionFunctor A).map f).left.app n |>.hom
    let εB := standardResolutionAugmentationHom A B n
    let εC := standardResolutionAugmentationHom A C n
    letI : Algebra P B := εB.toAlgebra
    letI : Algebra B C := f.hom.toRingHom.toAlgebra
    letI : Algebra Q C := εC.toAlgebra
    letI : Algebra P Q := η.toRingHom.toAlgebra
    letI : Algebra P C := (εC.comp η.toRingHom).toAlgebra
    letI : Module P (cotangentTerm A C n) :=
      Module.compHom _ (εC.comp η.toRingHom)
    letI : Module Q (cotangentTerm A C n) := Module.compHom _ εC
    letI : Module P (KaehlerDifferential A Q) := Module.compHom _ η.toRingHom
    haveI : IsScalarTower P Q (KaehlerDifferential A Q) :=
      ⟨fun p q x => mul_smul (algebraMap P Q p) q x⟩
    haveI : IsScalarTower P Q C := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower P Q (cotangentTerm A C n) :=
      ⟨fun p q x => mul_smul (algebraMap P Q p) q x⟩
    haveI : IsScalarTower P B C := IsScalarTower.of_algebraMap_eq' hcomm_compat
    haveI : IsScalarTower Q C C := IsScalarTower.of_algebraMap_eq' rfl
    let mk : KaehlerDifferential A Q →ₗ[Q] cotangentTerm A C n :=
      TensorProduct.mk Q C (KaehlerDifferential A Q) 1
    let k : KaehlerDifferential A P →ₗ[P] cotangentTerm A C n :=
      { toFun := fun x => mk (KaehlerDifferential.map A A P Q x)
        map_add' := by simp
        map_smul' := by
          intro p x
          change mk (KaehlerDifferential.map A A P Q (p • x)) =
            (εC.comp η.toRingHom) p • mk (KaehlerDifferential.map A A P Q x)
          rw [(KaehlerDifferential.map A A P Q).map_smul]
          change mk ((algebraMap P Q p) • _) = _
          rw [mk.map_smul]
          rfl }
    let e := TensorProduct.AlgebraTensorModule.cancelBaseChange P B C C
      (KaehlerDifferential A P)
    let d : ModuleCat.of P (KaehlerDifferential A P) ⟶
        (ModuleCat.restrictScalars (εC.comp η.toRingHom)).obj
          (cotangentTerm A C n) := ModuleCat.ofHom k
    let m := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
      (εC.comp η.toRingHom) d
    change ModuleCat.of C (C ⊗[B] cotangentTerm A B n) ⟶
      cotangentTerm A C n
    exact ModuleCat.ofHom e.toLinearMap ≫ m

/-- The degreewise second map of the differential sequence: the canonical map to the
base-changed relative differentials. -/
noncomputable def differentialSequenceSecondComponent
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    cotangentTerm A C n ⟶ relativeCotangentTerm A f n :=
  let hpushout :
    CategoryTheory.IsPushout
      (CommRingCat.ofHom
        (((standardResolutionFunctor A).map f).left.app n).hom.toRingHom)
      (CommRingCat.ofHom (standardResolutionAugmentationHom A B n))
      (CommRingCat.ofHom (canonicalBaseChangeMap A f n))
      (CommRingCat.ofHom
        (algebraMap B
          ((baseChangedStandardResolution A f).left.obj n))) := by
    exact canonicalBaseChangeMap_isPushout A f n
  let hscalar_compat :
    (((baseChangedStandardResolution A f).hom.app n).hom.toRingHom).comp
      (canonicalBaseChangeMap A f n) = standardResolutionAugmentationHom A C n := by
    exact canonicalBaseChangeMap_augmentation A f n
  by
    let R := baseChangedStandardResolution A f
    let Q := (standardResolution A C).left.obj n
    let T := R.left.obj n
    let δ := canonicalBaseChangeMap A f n
    let P := (standardResolution A B).left.obj n
    let η : P →ₐ[A] Q := ((standardResolutionFunctor A).map f).left.app n |>.hom
    let εB := standardResolutionAugmentationHom A B n
    let εQ := standardResolutionAugmentationHom A C n
    let εT := (R.hom.app n).hom.toRingHom
    letI : Algebra P B := εB.toAlgebra
    letI : Algebra P Q := η.toRingHom.toAlgebra
    letI : Algebra B T := (algebraMap B T).toAlgebra
    letI : Algebra Q T := δ.toAlgebra
    letI : Algebra T C := εT.toAlgebra
    letI : Algebra Q C := εQ.toAlgebra
    letI : Algebra A T := ((algebraMap B T).comp (algebraMap A B)).toAlgebra
    haveI : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower Q T C := IsScalarTower.of_algebraMap_eq' hscalar_compat.symm
    letI : Algebra P T := (δ.comp η.toRingHom).toAlgebra
    have hcomm : δ.comp η.toRingHom = (algebraMap B T).comp εB :=
      RingHom.ext fun p => congrArg (fun z : CommRingCat.Hom _ _ => z.hom p) hpushout.w
    haveI : IsScalarTower P B T := IsScalarTower.of_algebraMap_eq' hcomm
    haveI : IsScalarTower P Q T := IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower A P Q :=
      IsScalarTower.of_algebraMap_eq (fun a => (η.commutes a).symm)
    haveI : IsScalarTower A P B := IsScalarTower.of_algebraMap_eq fun a => by
      exact (standardResolution_augmentation_commutes A B n a).symm
    haveI : IsScalarTower A Q T := IsScalarTower.of_algebraMap_eq fun a => by
      exact
        (congrArg (algebraMap B T) (standardResolution_augmentation_commutes A B n a).symm).trans
          ((RingHom.congr_fun hcomm _).symm.trans (congrArg δ (η.commutes a)))
    letI : Module Q (relativeCotangentTerm A f n) := Module.compHom _ εQ
    haveI : IsScalarTower Q C C := IsScalarTower.of_algebraMap_eq' rfl
    have hpo :
        CategoryTheory.IsPushout (CommRingCat.ofHom (algebraMap P B))
          (CommRingCat.ofHom (algebraMap P Q))
          (CommRingCat.ofHom (algebraMap B T))
          (CommRingCat.ofHom (algebraMap Q T)) := by
      simpa only [RingHom.algebraMap_toAlgebra] using
        hpushout.flip
    letI : Algebra.IsPushout
        P B Q T := (CommRingCat.isPushout_iff_isPushout).mp hpo
    let k : KaehlerDifferential A Q →ₗ[Q] relativeCotangentTerm A f n :=
      (TensorProduct.mk T C (KaehlerDifferential B T) 1).restrictScalars Q ∘ₗ
        KaehlerDifferential.map A B Q T
    let d : ModuleCat.of Q (KaehlerDifferential A Q) ⟶
        (ModuleCat.restrictScalars εQ).obj (relativeCotangentTerm A f n) :=
      ModuleCat.ofHom k
    exact ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars εQ d

private theorem differentialSequenceSecondComponent_differential
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) (q : (standardResolution A C).left.obj n) :
    differentialSequenceSecondComponent A f n
      (cotangentTermDifferential A C n q) =
    relativeCotangentTermDifferential A f n (canonicalBaseChangeMap A f n q) := by
  let R := baseChangedStandardResolution A f
  let Q := (standardResolution A C).left.obj n
  let T := R.left.obj n
  let δ := canonicalBaseChangeMap A f n
  let εQ := standardResolutionAugmentationHom A C n
  let εT := (R.hom.app n).hom.toRingHom
  let P := (standardResolution A B).left.obj n
  let η : P →ₐ[A] Q := ((standardResolutionFunctor A).map f).left.app n |>.hom
  let εB := standardResolutionAugmentationHom A B n
  let _ : Algebra P Q := η.toRingHom.toAlgebra
  let _ : Algebra P B := εB.toAlgebra
  let _ : Algebra B T := (algebraMap B T).toAlgebra
  let _ : Algebra Q T := δ.toAlgebra
  let _ : Algebra T C := εT.toAlgebra
  let _ : Algebra Q C := εQ.toAlgebra
  let _ : Algebra A T := ((algebraMap B T).comp (algebraMap A B)).toAlgebra
  have : IsScalarTower A B T := IsScalarTower.of_algebraMap_eq' rfl
  have hcomm : δ.comp η.toRingHom = (algebraMap B T).comp εB :=
    canonicalBaseChangeMap_comp_eq A f n
  have : IsScalarTower A Q T := IsScalarTower.of_algebraMap_eq fun a =>
    (congrArg (algebraMap B T) (standardResolution_augmentation_commutes A B n a).symm).trans
      ((RingHom.congr_fun hcomm _).symm.trans (congrArg δ (η.commutes a)))
  have : IsScalarTower Q T C :=
    IsScalarTower.of_algebraMap_eq' (canonicalBaseChangeMap_augmentation A f n).symm
  let _ : Module Q (relativeCotangentTerm A f n) := Module.compHom _ εQ
  let k : KaehlerDifferential A Q →ₗ[Q] relativeCotangentTerm A f n :=
    (TensorProduct.mk T C (KaehlerDifferential B T) 1).restrictScalars Q ∘ₗ
      KaehlerDifferential.map A B Q T
  let d : ModuleCat.of Q (KaehlerDifferential A Q) ⟶
      (ModuleCat.restrictScalars εQ).obj (relativeCotangentTerm A f n) :=
    ModuleCat.ofHom k
  refine (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul εQ d (1 : C)
    (KaehlerDifferential.D A Q q)).trans ?_
  rw [one_smul]
  show (1 : C) ⊗ₜ[T]
      (KaehlerDifferential.map A B Q T (KaehlerDifferential.D A Q q)) = _
  rw [KaehlerDifferential.map_D]
  rfl

private theorem differentialSequenceFirstHom_ext
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) {N : ModuleCat.{max u v} C}
    (α β : (ModuleCat.extendScalars f.hom.toRingHom).obj (cotangentTerm A B n) ⟶ N)
    (h : ∀ p : (standardResolution A B).left.obj n,
      α ((1 : C) ⊗ₜ[B] cotangentTermDifferential A B n p) =
        β ((1 : C) ⊗ₜ[B] cotangentTermDifferential A B n p)) : α = β := by
  let P := (standardResolution A B).left.obj n
  let _ : Algebra P B := (standardResolutionAugmentationHom A B n).toAlgebra
  exact ModuleCat.extendScalars_baseChange_kaehlerDifferential_hom_ext
    (A := (A : Type u)) (P := (P : Type (max u v))) f.hom.toRingHom α β h

private theorem differentialSequenceFirstComponent_differential
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) (p : (standardResolution A B).left.obj n) :
    differentialSequenceFirstComponent A f n
      ((1 : C) ⊗ₜ[B] cotangentTermDifferential A B n p) =
      cotangentTermDifferential A C n
        (((standardResolutionFunctor A).map f).left.app n p) := by
  let P := (standardResolution A B).left.obj n
  let Q := (standardResolution A C).left.obj n
  let η : P →ₐ[A] Q := ((standardResolutionFunctor A).map f).left.app n |>.hom
  let εB := standardResolutionAugmentationHom A B n
  let εC := standardResolutionAugmentationHom A C n
  let _ : Algebra P B := εB.toAlgebra
  let _ : Algebra B C := f.hom.toRingHom.toAlgebra
  let _ : Algebra Q C := εC.toAlgebra
  let _ : Algebra P Q := η.toRingHom.toAlgebra
  have hcomm : εC.comp η.toRingHom = f.hom.toRingHom.comp εB :=
    standardResolution_augmentation_map_naturality A f n
  let _ : Algebra P C := (εC.comp η.toRingHom).toAlgebra
  let _ : Module P (cotangentTerm A C n) :=
    Module.compHom _ (εC.comp η.toRingHom)
  let _ : Module Q (cotangentTerm A C n) := Module.compHom _ εC
  let _ : Module P (KaehlerDifferential A Q) := Module.compHom _ η.toRingHom
  have : IsScalarTower A P B := IsScalarTower.of_algebraMap_eq fun a =>
    (standardResolution_augmentation_commutes A B n a).symm
  have : IsScalarTower P B C := IsScalarTower.of_algebraMap_eq' hcomm
  have : IsScalarTower P Q C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P Q (KaehlerDifferential A Q) :=
    ⟨fun p q x => mul_smul (algebraMap P Q p) q x⟩
  have : IsScalarTower P Q (cotangentTerm A C n) := ⟨fun p q x => mul_smul (algebraMap P Q p) q x⟩
  let e := TensorProduct.AlgebraTensorModule.cancelBaseChange P B C C
    (KaehlerDifferential A P)
  let mk : KaehlerDifferential A Q →ₗ[Q] cotangentTerm A C n :=
    TensorProduct.mk Q C (KaehlerDifferential A Q) 1
  let k : KaehlerDifferential A P →ₗ[P] cotangentTerm A C n :=
    { toFun := fun x => mk (KaehlerDifferential.map A A P Q x)
      map_add' := by simp
      map_smul' := by
        intro p x
        show mk (KaehlerDifferential.map A A P Q (p • x)) =
          (εC.comp η.toRingHom) p • mk (KaehlerDifferential.map A A P Q x)
        rw [(KaehlerDifferential.map A A P Q).map_smul]
        show mk ((algebraMap P Q p) • _) = _
        rw [mk.map_smul]
        rfl }
  let d : ModuleCat.of P (KaehlerDifferential A P) ⟶
      (ModuleCat.restrictScalars (εC.comp η.toRingHom)).obj
        (cotangentTerm A C n) := ModuleCat.ofHom k
  let m := ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars
    (εC.comp η.toRingHom) d
  show m (e ((1 : C) ⊗ₜ[B]
      ((1 : B) ⊗ₜ[P] KaehlerDifferential.D A P p))) = _
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul]
  refine (ModuleCat.ExtendRestrictScalarsAdj.HomEquiv.fromExtendScalars_tmul
    (εC.comp η.toRingHom) d (1 : C) (KaehlerDifferential.D A P p)).trans ?_
  rw [one_smul]
  show mk (KaehlerDifferential.map A A P Q
      (KaehlerDifferential.D A P p)) = _
  rw [KaehlerDifferential.map_D]
  show (1 : C) ⊗ₜ[Q] KaehlerDifferential.D A Q (algebraMap P Q p) = _
  congr 2

/-- The first map of the differential sequence, as a morphism of simplicial `C`-modules. -/
noncomputable def differentialSequenceFirstMap
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) :
    ((cotangentSimplicialModule A B).object ⋙
      ModuleCat.extendScalars f.hom.toRingHom) ⟶
      (cotangentSimplicialModule A C).object :=
  {
    app := fun n => differentialSequenceFirstComponent A f n
    naturality := by
      intro i j h
      apply differentialSequenceFirstHom_ext A f i
      intro p
      let ηi := ((standardResolutionFunctor A).map f).left.app i
      let ηj := ((standardResolutionFunctor A).map f).left.app j
      have hη : ηj (((standardResolution A B).left.map h) p) =
          ((standardResolution A C).left.map h) (ηi p) :=
        congrArg (fun k : CommAlgCat.Hom _ _ => k.hom p)
          (((standardResolutionFunctor A).map f).left.naturality h)
      have hB : (cotangentSimplicialModule A B).object.map h
          (cotangentTermDifferential A B i p) =
          cotangentTermDifferential A B j
            ((standardResolution A B).left.map h p) :=
        (cotangentSimplicialModule A B).map_differential h p
      have hC : (cotangentSimplicialModule A C).object.map h
          (cotangentTermDifferential A C i (ηi.hom p)) =
          cotangentTermDifferential A C j
            ((standardResolution A C).left.map h (ηi.hom p)) :=
        (cotangentSimplicialModule A C).map_differential h (ηi.hom p)
      change differentialSequenceFirstComponent A f j
          ((1 : C) ⊗ₜ[B]
            ((cotangentSimplicialModule A B).object.map h
              (cotangentTermDifferential A B i p))) =
        (cotangentSimplicialModule A C).object.map h
          (differentialSequenceFirstComponent A f i
            ((1 : C) ⊗ₜ[B] cotangentTermDifferential A B i p))
      rw [hB, differentialSequenceFirstComponent_differential,
        differentialSequenceFirstComponent_differential, hC]
      exact congrArg (cotangentTermDifferential A C j) hη }

/-- The second map of the differential sequence, as a morphism of simplicial `C`-modules. -/
noncomputable def differentialSequenceSecondMap
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) :
    (cotangentSimplicialModule A C).object ⟶
      relativeCotangentSimplicialObject A f :=
  {
    app := fun n => differentialSequenceSecondComponent A f n
    naturality := by
      intro i j h
      let Qi := (standardResolution A C).left.obj i
      let δi := canonicalBaseChangeMap A f i
      let _ : Algebra Qi C := (standardResolutionAugmentationHom A C i).toAlgebra
      apply ModuleCat.baseChange_kaehlerDifferential_hom_ext (A := (A : Type u))
        (R := (Qi : Type (max u v)))
      intro q
      have hδ := congrArg (fun g => g q) (canonicalBaseChangeMap_naturality A f h)
      change differentialSequenceSecondComponent A f j
          ((cotangentSimplicialModule A C).object.map h
            (cotangentTermDifferential A C i q)) =
        relativeCotangentMap A f h
          (differentialSequenceSecondComponent A f i (cotangentTermDifferential A C i q))
      rw [cotangentSimplicialModule_map_differential A C h q,
        differentialSequenceSecondComponent_differential A f j
          ((standardResolution A C).left.map h q),
        differentialSequenceSecondComponent_differential A f i q,
        relativeCotangentMap_differential]
      exact (congrArg (relativeCotangentTermDifferential A f j) hδ).symm }

private theorem relativeCotangentBaseChangeEquiv_differential
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) (q : (standardResolution A C).left.obj n) :
    let P := (standardResolution A B).left.obj n
    let Q := (standardResolution A C).left.obj n
    letI : Algebra P Q :=
      (((standardResolutionFunctor A).map f).left.app n).hom.toAlgebra
    letI : Algebra Q C := (standardResolutionAugmentationHom A C n).toAlgebra
    (relativeCotangentBaseChangeEquiv A f n).hom
      ((1 : C) ⊗ₜ[Q] KaehlerDifferential.D P Q q) =
        relativeCotangentTermDifferential A f n (canonicalBaseChangeMap A f n q) := by
  let P := (standardResolution A B).left.obj n
  let Q := (standardResolution A C).left.obj n
  let T := (baseChangedStandardResolution A f).left.obj n
  let η : P →ₐ[A] Q := (((standardResolutionFunctor A).map f).left.app n).hom
  let ι : P →+* B := standardResolutionAugmentationHom A B n
  let δ : Q →+* T := canonicalBaseChangeMap A f n
  let ε : B →+* T := algebraMap B T
  let _ : Algebra P Q := η.toRingHom.toAlgebra
  let _ : Algebra P B := ι.toAlgebra
  let _ : Algebra Q T := δ.toAlgebra
  let _ : Algebra B T := ε.toAlgebra
  let _ : Algebra P T := (δ.comp η.toRingHom).toAlgebra
  have hcomm : δ.comp η.toRingHom = ε.comp ι := canonicalBaseChangeMap_comp_eq A f n
  have : IsScalarTower P Q T := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P B T := IsScalarTower.of_algebraMap_eq' hcomm
  have : Algebra.IsPushout P B Q T :=
    CommRingCat.isPushout_iff_isPushout.mp (canonicalBaseChangeMap_isPushout A f n).flip
  let _ : Algebra T C :=
    (((baseChangedStandardResolution A f).hom.app n).hom.toRingHom).toAlgebra
  let _ : Algebra Q C := (standardResolutionAugmentationHom A C n).toAlgebra
  have : IsScalarTower Q T C :=
    IsScalarTower.of_algebraMap_eq' (canonicalBaseChangeMap_augmentation A f n).symm
  let E := KaehlerDifferential.tensorKaehlerEquiv P B Q T
  let e₁ : C ⊗[T] KaehlerDifferential B T ≃ₗ[C]
      C ⊗[T] (T ⊗[Q] KaehlerDifferential P Q) :=
    TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl C C) E.symm
  let e₂ : C ⊗[T] (T ⊗[Q] KaehlerDifferential P Q) ≃ₗ[C]
      C ⊗[Q] KaehlerDifferential P Q :=
    TensorProduct.AlgebraTensorModule.cancelBaseChange Q T C C
      (KaehlerDifferential P Q)
  show e₁.symm (e₂.symm ((1 : C) ⊗ₜ[Q] KaehlerDifferential.D P Q q)) = _
  rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
  show (1 : C) ⊗ₜ[T] (E ((1 : T) ⊗ₜ[Q] KaehlerDifferential.D P Q q)) = _
  rw [KaehlerDifferential.tensorKaehlerEquiv_tmul_D, one_smul]
  rfl

/-- The data of the canonical short complex of differential simplicial modules. -/
structure DifferentialSequenceData
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) where
  complex : ShortComplex (SimplicialObject (ModuleCat.{max u v} C))
  firstIso : complex.X₁ ≅
    (cotangentSimplicialModule A B).object ⋙ ModuleCat.extendScalars f.hom.toRingHom
  secondIso : complex.X₂ ≅ (cotangentSimplicialModule A C).object
  thirdIso : ∀ n : SimplexCategoryᵒᵖ,
    let R := baseChangedStandardResolution A f
    let T := R.left.obj n
    letI : Algebra T C := ((R.hom.app n).hom.toRingHom).toAlgebra
    complex.X₃.obj n ≅ ModuleCat.of C (C ⊗[T] KaehlerDifferential B T)
  toBaseChange : ∀ n : SimplexCategoryᵒᵖ,
    (standardResolution A C).left.obj n →+*
      (baseChangedStandardResolution A f).left.obj n

/-- The specific canonical differential short complex for `A → B → C`. -/
@[stacks 08SD "differential_sequence construction"]
noncomputable def standardResolutionDifferentialSequence
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C) :
    DifferentialSequenceData A f :=
  { complex :=
      { X₁ := (cotangentSimplicialModule A B).object ⋙
          ModuleCat.extendScalars f.hom.toRingHom
        X₂ := (cotangentSimplicialModule A C).object
        X₃ := relativeCotangentSimplicialObject A f
        f := differentialSequenceFirstMap A f
        g := differentialSequenceSecondMap A f
        zero := by
          apply NatTrans.ext
          funext n
          dsimp only [differentialSequenceFirstMap, differentialSequenceSecondMap,
            cotangentSimplicialModule]
          change differentialSequenceFirstComponent A f n ≫
            differentialSequenceSecondComponent A f n = 0
          apply differentialSequenceFirstHom_ext A f n
          intro p
          change differentialSequenceSecondComponent A f n
            (differentialSequenceFirstComponent A f n
              ((1 : C) ⊗ₜ[B] cotangentTermDifferential A B n p)) = 0
          rw [differentialSequenceFirstComponent_differential,
            differentialSequenceSecondComponent_differential]
          let P := (standardResolution A B).left.obj n
          let Q := (standardResolution A C).left.obj n
          let T := (baseChangedStandardResolution A f).left.obj n
          let η := ((standardResolutionFunctor A).map f).left.app n
          let εB := standardResolutionAugmentationHom A B n
          have hp : canonicalBaseChangeMap A f n (η.hom p) =
              algebraMap B T (εB p) :=
            congrArg (fun z : CommRingCat.Hom _ _ => z.hom p)
              (canonicalBaseChangeMap_isPushout A f n).w
          rw [hp]
          let _ : Algebra T C :=
            (((baseChangedStandardResolution A f).hom.app n).hom.toRingHom).toAlgebra
          change (1 : C) ⊗ₜ[T] KaehlerDifferential.D B T (algebraMap B T (εB p)) = 0
          rw [Derivation.map_algebraMap, TensorProduct.tmul_zero]
      }
    firstIso := Iso.refl _
    secondIso := Iso.refl _
    thirdIso := fun n => Iso.refl _
    toBaseChange := canonicalBaseChangeMap A f }

/-- The canonical differential complex is short exact. -/
@[stacks 08SD "differential_sequence"]
theorem standardResolution_differentials_shortExact
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (hf : Function.Injective f.hom) :
    (standardResolutionDifferentialSequence A f).complex.ShortExact := by
  let _ : HasZeroMorphisms (SimplicialObject (ModuleCat.{max u v} C)) :=
    instHasZeroMorphismsFunctor (ModuleCat.{max u v} C)
  let D := standardResolutionDifferentialSequence A f
  let ev : ∀ n : SimplexCategoryᵒᵖ,
      SimplicialObject (ModuleCat.{max u v} C) ⥤ ModuleCat.{max u v} C :=
    fun n => (evaluation (SimplexCategoryᵒᵖ) (ModuleCat.{max u v} C)).obj n
  have hEval : JointlyReflectIsomorphisms ev := by
    refine ⟨fun α hα => ?_⟩
    have (n : SimplexCategoryᵒᵖ) : IsIso (α.app n) := hα n
    exact NatIso.isIso_of_isIso_app α
  apply (hEval.shortExact_iff D.complex).2
  intro n
  let P := (standardResolution A B).left.obj n
  let Q := (standardResolution A C).left.obj n
  let η := ((standardResolutionFunctor A).map f).left.app n
  let εB := standardResolutionAugmentationHom A B n
  let εQ := standardResolutionAugmentationHom A C n
  let _ : Algebra P B := εB.toAlgebra
  let _ : Algebra B C := f.hom.toRingHom.toAlgebra
  let _ : Algebra P Q := η.hom.toRingHom.toAlgebra
  let _ : Algebra Q C := εQ.toAlgebra
  have hcomm : εQ.comp η.hom.toRingHom = f.hom.toRingHom.comp εB :=
    standardResolution_augmentation_map_naturality A f n
  let _ : Algebra P C := (εQ.comp η.hom.toRingHom).toAlgebra
  have : IsScalarTower P Q C := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower P B C := IsScalarTower.of_algebraMap_eq' hcomm
  have : IsScalarTower A P Q :=
    IsScalarTower.of_algebraMap_eq (fun a => (η.hom.commutes a).symm)
  let F := ModuleCat.extendScalars εQ
  let S := ShortComplex.moduleCatMk (KaehlerDifferential.mapBaseChange A P Q)
    (KaehlerDifferential.map A P Q Q)
    (LinearMap.ext (KaehlerDifferential.exact_mapBaseChange_map A P Q).apply_apply_eq_zero)
  let SI := S.map F
  have : F.Additive := extendScalars_additive εQ
  have hSI : SI.ShortExact := standardResolution_towerDifferential_shortExact_extendScalars A f hf n
  let ePB := TensorProduct.AlgebraTensorModule.cancelBaseChange P B C C
    (KaehlerDifferential A P)
  let ePQ := TensorProduct.AlgebraTensorModule.cancelBaseChange P Q C C
    (KaehlerDifferential A P)
  let e₁ := ePB.trans ePQ.symm
  let e₃ := relativeCotangentBaseChangeEquiv A f n
  let target := D.complex.map (ev n)
  have hIso : target ≅ SI := by
    refine ShortComplex.isoMk e₁.toModuleIso (Iso.refl _) e₃.symm ?_ ?_
    · apply differentialSequenceFirstHom_ext A f n
      intro p
      show SI.f (e₁ ((1 : C) ⊗ₜ[B]
        cotangentTermDifferential A B n p)) =
          differentialSequenceFirstComponent A f n
            ((1 : C) ⊗ₜ[B] cotangentTermDifferential A B n p)
      rw [differentialSequenceFirstComponent_differential]
      show SI.f (ePQ.symm (ePB ((1 : C) ⊗ₜ[B]
        ((1 : B) ⊗ₜ[P] KaehlerDifferential.D A P p)))) = _
      rw [TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul, one_smul,
        TensorProduct.AlgebraTensorModule.cancelBaseChange_symm_tmul]
      show (1 : C) ⊗ₜ[Q] (KaehlerDifferential.mapBaseChange A P Q
        ((1 : Q) ⊗ₜ[P] KaehlerDifferential.D A P p)) = _
      rw [KaehlerDifferential.mapBaseChange_tmul, one_smul,
        KaehlerDifferential.map_D]
      rfl
    · apply ModuleCat.baseChange_kaehlerDifferential_hom_ext (A := (A : Type u))
        (R := (Q : Type (max u v)))
      intro q
      show (1 : C) ⊗ₜ[Q]
        (KaehlerDifferential.map A P Q Q (KaehlerDifferential.D A Q q)) =
          e₃.inv (differentialSequenceSecondComponent A f n
            (cotangentTermDifferential A C n q))
      rw [KaehlerDifferential.map_D, differentialSequenceSecondComponent_differential]
      have he := relativeCotangentBaseChangeEquiv_differential A f n q
      change e₃.hom ((1 : C) ⊗ₜ[Q] KaehlerDifferential.D P Q q) = _ at he
      rw [← he]
      simp
  exact (ShortComplex.shortExact_iff_of_iso hIso).2 hSI

/-- The first map sends a differential to the differential of its image. -/
@[stacks 08SD "differential_sequence first map"]
theorem standardResolution_differentials_firstMap
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) (p : (standardResolution A B).left.obj n) :
    let D := standardResolutionDifferentialSequence A f
    ((D.firstIso.inv.app n) ≫ (D.complex.f.app n) ≫ (D.secondIso.hom.app n))
      ((1 : C) ⊗ₜ[B] cotangentTermDifferential A B n p) =
      cotangentTermDifferential A C n
        (((standardResolutionFunctor A).map f).left.app n p) :=
  differentialSequenceFirstComponent_differential A f n p

/-- The second map is the canonical map to base-changed relative differentials. -/
@[stacks 08SD "differential_sequence second map"]
theorem standardResolution_differentials_secondMap
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) (q : (standardResolution A C).left.obj n) :
    let D := standardResolutionDifferentialSequence A f
    let R := baseChangedStandardResolution A f
    let T := R.left.obj n
    letI : Algebra T C := ((R.hom.app n).hom.toRingHom).toAlgebra
    ((D.secondIso.inv.app n) ≫ (D.complex.g.app n) ≫ (D.thirdIso n).hom)
      (cotangentTermDifferential A C n q) =
      ((1 : C) ⊗ₜ[T] KaehlerDifferential.D B T (D.toBaseChange n q)) :=
  differentialSequenceSecondComponent_differential A f n q

/-- The identification of the third term respects every simplicial map. -/
@[stacks 08SD "differential_sequence naturality"]
theorem standardResolution_differentials_third_naturality
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    {i j : SimplexCategoryᵒᵖ} (h : i ⟶ j)
    (t : (baseChangedStandardResolution A f).left.obj
      i) :
    let D := standardResolutionDifferentialSequence A f
    let R := baseChangedStandardResolution A f
    let Ti := R.left.obj i
    let Tj := R.left.obj j
    letI : Algebra Ti C := ((R.hom.app i).hom.toRingHom).toAlgebra
    letI : Algebra Tj C := ((R.hom.app j).hom.toRingHom).toAlgebra
    ((D.thirdIso i).inv ≫ D.complex.X₃.map h ≫ (D.thirdIso j).hom)
      ((1 : C) ⊗ₜ[Ti] KaehlerDifferential.D B Ti t) =
      ((1 : C) ⊗ₜ[Tj] KaehlerDifferential.D B Tj (R.left.map h t)) :=
  relativeCotangentMap_differential A f h t

/-- The map to the base-changed resolution is its canonical pushout leg. -/
@[stacks 08SD "differential_sequence base change"]
theorem standardResolution_differentials_pushout
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    let D := standardResolutionDifferentialSequence A f
    let R := baseChangedStandardResolution A f
    CategoryTheory.IsPushout
      (CommRingCat.ofHom
        (((standardResolutionFunctor A).map f).left.app n).hom.toRingHom)
      (CommRingCat.ofHom (standardResolutionAugmentationHom A B n))
      (CommRingCat.ofHom (D.toBaseChange n))
      (CommRingCat.ofHom (algebraMap B (R.left.obj n))) :=
  canonicalBaseChangeMap_isPushout A f n

/-- The pushout leg is simplicially natural. -/
@[stacks 08SD "differential_sequence base change naturality"]
theorem standardResolution_differentials_toBaseChange_naturality
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    {i j : SimplexCategoryᵒᵖ} (h : i ⟶ j)
    (q : (standardResolution A C).left.obj i) :
    let D := standardResolutionDifferentialSequence A f
    let R := baseChangedStandardResolution A f
    R.left.map h (D.toBaseChange i q) =
      D.toBaseChange j ((standardResolution A C).left.map h q) :=
  congrArg (fun e => e q) (canonicalBaseChangeMap_naturality A f h)

/-- The pushout leg is compatible with augmentation to `C`. -/
@[stacks 08SD "differential_sequence augmentation"]
theorem standardResolution_differentials_toBaseChange_augmentation
    (A : Type u) [CommRing A] {B C : CommAlgCat.{max u v} A} (f : B ⟶ C)
    (n : SimplexCategoryᵒᵖ) :
    let D := standardResolutionDifferentialSequence A f
    let R := baseChangedStandardResolution A f
    ((R.hom.app n).hom.toRingHom).comp (D.toBaseChange n) =
      standardResolutionAugmentationHom A C n :=
  canonicalBaseChangeMap_augmentation A f n

/-- The second component of the differential sequence sends the differential `d q` of an element
of the standard resolution of `C` to the relative differential of its image under the canonical
base-change map. -/
alias differentialSequenceSecondComponent_differential' := differentialSequenceSecondComponent_differential

/-- Two maps out of the base change of a term of the cotangent complex of `B` agree once they
agree on the elements `1 ⊗ d p`. -/
alias differentialSequenceFirstHom_ext' := differentialSequenceFirstHom_ext

/-- The first component of the differential sequence sends `1 ⊗ d p` to the differential of the
image of `p` under the map of standard resolutions induced by `f`. -/
alias differentialSequenceFirstComponent_differential' := differentialSequenceFirstComponent_differential

end CommAlgCat

end
