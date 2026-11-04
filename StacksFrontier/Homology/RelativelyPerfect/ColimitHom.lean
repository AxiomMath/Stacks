module

public import StacksFrontier.Homology.RelativelyPerfect.Colimit
public import StacksFrontier.Homology.TorAmplitude.CanonicalCertificate
import all StacksFrontier.Homology.TorAmplitude.CanonicalCertificate

/-!
# Relatively perfect objects and derived morphism sets over a filtered colimit of rings

Let `R` be the filtered colimit of a diagram `i ↦ Rᵢ` of `R₀`-algebras, let `R₀ → A₀` be flat of
finite presentation, and put `Aᵢ = Rᵢ ⊗[R₀] A₀` and `A = R ⊗[R₀] A₀`. Every object of `D(A)`
perfect relative to `R` is the derived extension of scalars of an object of `D(Aᵢ)` perfect
relative to `Rᵢ`, for some stage `i`. For `K₀` pseudo-coherent and `L₀` of finite Tor dimension
over `R₀`, the set of morphisms `K ⟶ L` in `D(A)` between the
extensions of scalars of `K₀` and `L₀` is the filtered colimit of the sets of morphisms
`Kᵢ ⟶ Lᵢ` in `D(Aᵢ)`: every morphism over `A` is the extension of scalars of a morphism at some
stage, and two morphisms at a stage with the same extension to `A` already agree at some later
stage.

## Main definitions

* `PseudoCoherence.canonicalDerivedTensoringDatum`: the derived tensoring datum of Stacks 0655
  built from the canonical derived tensor product of Stacks 0BYI.
* `PseudoCoherence.derivedExtensionScalarsComp`: the canonical composition isomorphism
  `L f^* ∘ L g^* ≅ L (g ∘ f)^*` for total derived extension of scalars.
* `PseudoCoherence.stageDerivedObj`, `PseudoCoherence.limitDerivedObj`: the extension of scalars
  of an object of `D(A₀)` to a stage and to the colimit.
* `PseudoCoherence.stageDerivedHomTransition`, `PseudoCoherence.stageDerivedHomComparison`: the
  transition map between the morphism sets at two stages and the comparison map from the
  morphism set at a stage to the morphism set over the colimit.

## Main results

* `PseudoCoherence.isColimit_mapCocone_commAlgCat_uliftFunctor`: a colimit cocone of
  `R₀`-algebras stays a colimit cocone after the universe lift, since that functor is an
  equivalence when the lift is by the algebras' own universe.
* `PseudoCoherence.derivedExtensionScalarsCompHom_eq`: the composition comparison is the unique
  natural transformation compatible with the comparisons to termwise extension of scalars.
* `PseudoCoherence.stageDerivedHom_descent`, and its two halves
  `PseudoCoherence.exists_stageDerivedHom` and
  `PseudoCoherence.exists_stageDerivedHomTransition_eq`: Stacks 0DHX's morphism-set assertion,
  as the surjectivity of the comparison maps and the injectivity of the induced map out of the
  filtered colimit.
* `PseudoCoherence.exists_relativelyPerfect_stage`: Stacks 0DHX's object assertion, that a
  relatively perfect object over the colimit descends to a relatively perfect object at a
  finite stage.

## Implementation notes

Stacks 0DHX is formalized in `StacksFrontier.Homology.RelativelyPerfect.Colimit` as the single
theorem `PseudoCoherence.relativelyPerfectComplexes_filteredColimit`, whose conclusion
existentially quantifies the composition and unit comparisons of derived extension of scalars
together with an abstract diagram of morphism sets and a colimit cocone on it. The composition
comparison is not in fact a choice: the compatibility clause accompanying it determines it
uniquely, because a total left derived functor is a right Kan extension. So
`derivedExtensionScalarsComp` is constructed here, the extracted comparison is identified with
it by `derivedExtensionScalarsCompHom_eq`, and the abstract diagram is eliminated in favour of
the two concrete clauses, which mention only the comparison maps built from it.

The three derived tensoring data that 0DHX takes as arguments are supplied by
`canonicalDerivedTensoringDatum`, so nothing here is quantified over an unexhibited structure.
Its two universe parameters are forced equal: the canonical derived tensor product of Stacks
0BYI is a bifunctor on `D(ModuleCat.{u} R)` for `R : Type u`, because Mathlib's monoidal
structure on `ModuleCat` requires the module universe to agree with the ring's. Consequently
the module universe of 0DHX collapses onto its ring universe, and the statements below place
`R₀`, `A₀` and the module carriers in one universe. The index category keeps its own two
universes, except in `isColimit_mapCocone_commAlgCat_uliftFunctor`, where the universe lift is
an equivalence only when it lifts by the algebras' own universe.

## References

* [The Stacks Project, Tag 0DHX](https://stacks.math.columbia.edu/tag/0DHX)
* [The Stacks Project, Tag 0655](https://stacks.math.columbia.edu/tag/0655)
* [The Stacks Project, Tag 0BYI](https://stacks.math.columbia.edu/tag/0BYI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open StacksDraft.TorAmplitude
open scoped TensorProduct

namespace PseudoCoherence

universe uI uJ uR

attribute [local instance] HasDerivedCategory.standard

/-! ### The canonical derived tensoring datum -/

/-- The derived tensoring datum of Stacks 0655 carried by the canonical derived tensor product
of Stacks 0BYI: its bifunctor, the comparison with termwise tensoring by a module in degree
zero, and the exactness data. -/
public def canonicalDerivedTensoringDatum (R : Type uR) [CommRing R] :
    DerivedTensoringDatum.{uR, uR} R where
  tensor := (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).tensor
  comparison := canonicalTensorComparison R
  isLeftDerived := canonicalTensorIsLeftDerived R
  commShift _ :=
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).commShift_left _
  triangulated _ :=
    (CochainComplex.DerivedTensor.canonicalDerivedTensorProduct R).exact_left _

/-- Finite Tor dimension against the canonical derived tensoring datum is the canonical finite
Tor dimension of Stacks 0652. -/
public theorem hasFiniteTorDimension_canonicalDerivedTensoringDatum_iff (R : Type uR)
    [CommRing R] (K : DerivedCategory (ModuleCat.{uR} R)) :
    HasFiniteTorDimension (canonicalDerivedTensoringDatum R).tensor
        (canonicalDerivedTensoringDatum R).comparison
        (canonicalDerivedTensoringDatum R).isLeftDerived K ↔
      HasFiniteTorDimensionCanonical R K :=
  Iff.rfl

/-! ### The universe lift of commutative algebras -/

/-- A commutative algebra is isomorphic to its own universe lift, so lifting by the algebras'
own universe is essentially surjective. -/
public theorem essSurj_commAlgCat_uliftFunctor (R : Type uR) [CommRing R] :
    (CommAlgCat.uliftFunctor.{uR, uR, uR} R).EssSurj where
  mem_essImage A := ⟨A, ⟨CommAlgCat.isoMk ULift.algEquiv⟩⟩

/-- Lifting commutative algebras by their own universe is an equivalence: it is fully faithful
and, by `essSurj_commAlgCat_uliftFunctor`, essentially surjective. -/
public theorem isEquivalence_commAlgCat_uliftFunctor (R : Type uR) [CommRing R] :
    (CommAlgCat.uliftFunctor.{uR, uR, uR} R).IsEquivalence :=
  let := essSurj_commAlgCat_uliftFunctor R
  Functor.IsEquivalence.mk

/-- A colimit cocone of `R₀`-algebras remains a colimit cocone after lifting the algebras by
their own universe, which is the form in which Stacks 0DHX asks for the colimit hypothesis. -/
public def isColimit_mapCocone_commAlgCat_uliftFunctor {R₀ : Type uR} [CommRing R₀]
    {I : Type uR} [Category.{uR} I] {F : I ⥤ CommAlgCat.{uR} R₀} {c : Cocone F}
    (hc : IsColimit c) :
    IsColimit ((CommAlgCat.uliftFunctor.{uR, uR, uR} R₀).mapCocone c) :=
  letI := isEquivalence_commAlgCat_uliftFunctor R₀
  isColimitOfPreserves _ hc

/-! ### The composition comparison for derived extension of scalars -/

section Composition

universe u v

/-- Any natural transformation factoring `derivedExtensionScalarsCompComparison` through the
comparison of the total derived extension of scalars along the composed ring map is
`derivedExtensionScalarsCompHom`; a total left derived functor is a right Kan extension, so the
factorization determines it. -/
public theorem derivedExtensionScalarsCompHom_eq {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (g : B →+* C)
    (τ : (totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, v} g).functor ⟶
      (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor)
    (hτ : ∀ P : CochainComplex (ModuleCat.{max u v} A) ℤ,
      τ.app (DerivedCategory.Q.obj P) ≫
          (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison.app P =
        (derivedExtensionScalarsCompComparison.{u, v} f g).app P) :
    τ = derivedExtensionScalarsCompHom.{u, v} f g := by
  refine Functor.leftDerived_ext (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor
    (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) _ τ _ ?_
  ext P
  exact (hτ P).trans (derivedExtensionScalarsCompHom_fac.{u, v} f g P).symm

/-- **The composition isomorphism for derived extension of scalars.** Extending scalars along
`f` and then along `g` is extending scalars along `g ∘ f`, by the comparison
`derivedExtensionScalarsCompHom`, which is invertible. -/
public def derivedExtensionScalarsComp {A B C : Type u} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C) :
    (totalDerivedExtensionScalars.{u, u, v} f).functor ⋙
        (totalDerivedExtensionScalars.{u, u, v} g).functor ≅
      (totalDerivedExtensionScalars.{u, u, v} (g.comp f)).functor :=
  @asIso _ _ _ _ (derivedExtensionScalarsCompHom.{u, v} f g)
    (by
      have := fun X => isIso_derivedExtensionScalarsCompHom_app.{u, v} f g X
      exact NatIso.isIso_of_isIso_app _)

/-- The forward map of `derivedExtensionScalarsComp` is
`derivedExtensionScalarsCompHom`. -/
@[simp]
public theorem derivedExtensionScalarsComp_hom {A B C : Type u} [CommRing A] [CommRing B]
    [CommRing C] (f : A →+* B) (g : B →+* C) :
    (derivedExtensionScalarsComp.{u, v} f g).hom =
      derivedExtensionScalarsCompHom.{u, v} f g :=
  rfl

end Composition

/-! ### Extension of scalars from the starting algebra to the stages -/

section Stages

variable {R₀ : Type uR} [CommRing R₀] {I : Type uI} [Category.{uJ} I]

/-- The isomorphism `ULift A₀ ≃+* A₀`, read as a ring map; the two starting objects are
restricted along it before extension of scalars is applied, which is what moves them into the
universe of the algebras `Aᵢ`. -/
public abbrev liftBaseRingHom (A₀ : Type uR) [CommRing A₀] : ULift.{uR} A₀ →+* A₀ :=
  ULift.ringEquiv.toRingHom

/-- Restriction of scalars along `ULift A₀ ≃+* A₀` on derived categories. -/
public abbrev baseLiftRestriction (A₀ : Type uR) [CommRing A₀] :
    DerivedCategory (ModuleCat.{uR} A₀) ⥤
      DerivedCategory (ModuleCat.{uR} (ULift.{uR} A₀)) :=
  (ModuleCat.restrictScalars.{uR} (liftBaseRingHom A₀)).mapDerivedCategory

/-- The map `ULift A₀ → Aᵢ` whose derived extension of scalars produces the object at stage
`i`. -/
public abbrev liftBaseToStageMap (F : I ⥤ CommAlgCat.{uR} R₀) (A₀ : Type uR) [CommRing A₀]
    [Algebra R₀ A₀] (i : I) : ULift.{uR} A₀ →+* stageAlgebra F A₀ i :=
  (baseToStageMap F A₀ i).comp (liftBaseRingHom A₀)

/-- The map `ULift A₀ → A` whose derived extension of scalars produces the object over the
colimit. -/
public abbrev liftBaseToLimitMap {F : I ⥤ CommAlgCat.{uR} R₀} (c : Cocone F) (A₀ : Type uR)
    [CommRing A₀] [Algebra R₀ A₀] : ULift.{uR} A₀ →+* c.pt ⊗[R₀] A₀ :=
  (baseToLimitMap c A₀).comp (liftBaseRingHom A₀)

/-- The extension of scalars of an object of `D(A₀)` to the algebra `Aᵢ = Rᵢ ⊗[R₀] A₀` at stage
`i`. -/
public abbrev stageDerivedObj (F : I ⥤ CommAlgCat.{uR} R₀) (A₀ : Type uR) [CommRing A₀]
    [Algebra R₀ A₀] (i : I) (K : DerivedCategory (ModuleCat.{uR} A₀)) :
    DerivedCategory (ModuleCat.{uR} (stageAlgebra F A₀ i)) :=
  (totalDerivedExtensionScalars.{uR, uR, uR} (liftBaseToStageMap F A₀ i)).functor.obj
    ((baseLiftRestriction A₀).obj K)

/-- The extension of scalars of an object of `D(A₀)` to the algebra `A = R ⊗[R₀] A₀` over the
colimit. -/
public abbrev limitDerivedObj {F : I ⥤ CommAlgCat.{uR} R₀} (c : Cocone F) (A₀ : Type uR)
    [CommRing A₀] [Algebra R₀ A₀] (K : DerivedCategory (ModuleCat.{uR} A₀)) :
    DerivedCategory (ModuleCat.{uR} (c.pt ⊗[R₀] A₀)) :=
  (totalDerivedExtensionScalars.{uR, uR, uR} (liftBaseToLimitMap c A₀)).functor.obj
    ((baseLiftRestriction A₀).obj K)

/-- The scalar tower `ULift A₀ → Aᵢ → Aⱼ` composes to `ULift A₀ → Aⱼ`. -/
public theorem stageMap_comp_liftBaseToStageMap (F : I ⥤ CommAlgCat.{uR} R₀) (A₀ : Type uR)
    [CommRing A₀] [Algebra R₀ A₀] {i j : I} (f : i ⟶ j) :
    (stageMap F A₀ f).comp (liftBaseToStageMap F A₀ i) = liftBaseToStageMap F A₀ j := by
  ext a
  simp [stageMap, baseToStageMap, Algebra.TensorProduct.includeRight_apply,
    Algebra.TensorProduct.map_tmul]

/-- The scalar tower `ULift A₀ → Aᵢ → A` composes to `ULift A₀ → A`. -/
public theorem stageToLimitMap_comp_liftBaseToStageMap {F : I ⥤ CommAlgCat.{uR} R₀}
    (c : Cocone F) (A₀ : Type uR) [CommRing A₀] [Algebra R₀ A₀] (i : I) :
    (stageToLimitMap c A₀ i).comp (liftBaseToStageMap F A₀ i) = liftBaseToLimitMap c A₀ := by
  ext a
  simp [stageToLimitMap, baseToStageMap, baseToLimitMap,
    Algebra.TensorProduct.includeRight_apply, Algebra.TensorProduct.map_tmul]

/-- Extending scalars to the stage `i` and then to the stage `j` is extending scalars to the
stage `j`. -/
public def stageDerivedExtensionIso (F : I ⥤ CommAlgCat.{uR} R₀) (A₀ : Type uR) [CommRing A₀]
    [Algebra R₀ A₀] {i j : I} (f : i ⟶ j) :
    (totalDerivedExtensionScalars.{uR, uR, uR} (liftBaseToStageMap F A₀ i)).functor ⋙
        (totalDerivedExtensionScalars.{uR, uR, uR} (stageMap F A₀ f)).functor ≅
      (totalDerivedExtensionScalars.{uR, uR, uR} (liftBaseToStageMap F A₀ j)).functor :=
  derivedExtensionScalarsComp.{uR, uR} (liftBaseToStageMap F A₀ i) (stageMap F A₀ f) ≪≫
    derivedExtensionScalarsCongr.{uR, uR} (stageMap_comp_liftBaseToStageMap F A₀ f)

/-- Extending scalars to the stage `i` and then to the colimit is extending scalars to the
colimit. -/
public def limitDerivedExtensionIso {F : I ⥤ CommAlgCat.{uR} R₀} (c : Cocone F) (A₀ : Type uR)
    [CommRing A₀] [Algebra R₀ A₀] (i : I) :
    (totalDerivedExtensionScalars.{uR, uR, uR} (liftBaseToStageMap F A₀ i)).functor ⋙
        (totalDerivedExtensionScalars.{uR, uR, uR} (stageToLimitMap c A₀ i)).functor ≅
      (totalDerivedExtensionScalars.{uR, uR, uR} (liftBaseToLimitMap c A₀)).functor :=
  derivedExtensionScalarsComp.{uR, uR} (liftBaseToStageMap F A₀ i) (stageToLimitMap c A₀ i) ≪≫
    derivedExtensionScalarsCongr.{uR, uR} (stageToLimitMap_comp_liftBaseToStageMap c A₀ i)

/-- The transition map of the system of derived morphism sets: extension of scalars from the
stage `i` to the stage `j`, read through `stageDerivedExtensionIso`. -/
public def stageDerivedHomTransition (F : I ⥤ CommAlgCat.{uR} R₀) (A₀ : Type uR) [CommRing A₀]
    [Algebra R₀ A₀] {i j : I} (f : i ⟶ j) (K L : DerivedCategory (ModuleCat.{uR} A₀))
    (φ : stageDerivedObj F A₀ i K ⟶ stageDerivedObj F A₀ i L) :
    stageDerivedObj F A₀ j K ⟶ stageDerivedObj F A₀ j L :=
  (stageDerivedExtensionIso F A₀ f).inv.app ((baseLiftRestriction A₀).obj K) ≫
    (totalDerivedExtensionScalars.{uR, uR, uR} (stageMap F A₀ f)).functor.map φ ≫
    (stageDerivedExtensionIso F A₀ f).hom.app ((baseLiftRestriction A₀).obj L)

/-- The comparison map of the system of derived morphism sets: extension of scalars from the
stage `i` to the colimit, read through `limitDerivedExtensionIso`. -/
public def stageDerivedHomComparison {F : I ⥤ CommAlgCat.{uR} R₀} (c : Cocone F)
    (A₀ : Type uR) [CommRing A₀] [Algebra R₀ A₀] (i : I)
    (K L : DerivedCategory (ModuleCat.{uR} A₀))
    (φ : stageDerivedObj F A₀ i K ⟶ stageDerivedObj F A₀ i L) :
    limitDerivedObj c A₀ K ⟶ limitDerivedObj c A₀ L :=
  (limitDerivedExtensionIso c A₀ i).inv.app ((baseLiftRestriction A₀).obj K) ≫
    (totalDerivedExtensionScalars.{uR, uR, uR} (stageToLimitMap c A₀ i)).functor.map φ ≫
    (limitDerivedExtensionIso c A₀ i).hom.app ((baseLiftRestriction A₀).obj L)

end Stages

/-! ### The morphism sets over the colimit -/

section HomDescent

variable {R₀ : Type uR} [CommRing R₀] {I : Type uI} [Category.{uJ} I] [IsFiltered I]
  (F : I ⥤ CommAlgCat.{uR} R₀) (c : Cocone F)
  (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
  (A₀ : Type uR) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
  [Algebra.FinitePresentation R₀ A₀]
  (K₀ L₀ : DerivedCategory (ModuleCat.{uR} A₀))

include hc in
/-- **Stacks 0DHX, the morphism-set assertion.** Every morphism between the extensions of
scalars of `K₀` and `L₀` to `A = R ⊗[R₀] A₀` is the extension of scalars of a morphism at some
stage, and two morphisms at a stage whose extensions to `A` agree already agree after extension
of scalars to some later stage.

This is the conjunction of surjectivity and injectivity for the induced map
`colim_i Hom_{D(Aᵢ)}(Kᵢ, Lᵢ) ⟶ Hom_{D(A)}(K, L)`, phrased without naming the colimit. -/
public theorem stageDerivedHom_descent
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K₀)
    (hL : HasFiniteTorDimensionCanonical R₀
      ((ModuleCat.restrictScalars (algebraMap R₀ A₀)).mapDerivedCategory.obj L₀)) :
    (∀ ψ : limitDerivedObj c A₀ K₀ ⟶ limitDerivedObj c A₀ L₀,
        ∃ (i : I) (φ : stageDerivedObj F A₀ i K₀ ⟶ stageDerivedObj F A₀ i L₀),
          stageDerivedHomComparison c A₀ i K₀ L₀ φ = ψ) ∧
      ∀ (i : I) (φ φ' : stageDerivedObj F A₀ i K₀ ⟶ stageDerivedObj F A₀ i L₀),
        stageDerivedHomComparison c A₀ i K₀ L₀ φ =
            stageDerivedHomComparison c A₀ i K₀ L₀ φ' →
          ∃ (j : I) (f : i ⟶ j),
            stageDerivedHomTransition F A₀ f K₀ L₀ φ =
              stageDerivedHomTransition F A₀ f K₀ L₀ φ' := by
  obtain ⟨comp, -, hcomp, -, -, -, -, hhom, -, -, -⟩ :=
    relativelyPerfectComplexes_filteredColimit.{uI, uJ, uR, uR, uR} F c hc A₀
      (canonicalDerivedTensoringDatum R₀) (fun i => canonicalDerivedTensoringDatum (F.obj i))
      (canonicalDerivedTensoringDatum c.pt)
  have hcompeq : ∀ {A B C : Type uR} [CommRing A] [CommRing B] [CommRing C]
      (f : A →+* B) (g : B →+* C),
      comp f g = derivedExtensionScalarsComp.{uR, uR} f g := fun f g =>
    Iso.ext (derivedExtensionScalarsCompHom_eq.{uR, uR} f g _ fun P => (hcomp f g P).symm)
  obtain ⟨H, eH, s, eTarget, hs, hstage, hlimit⟩ := hhom K₀ L₀ hK hL
  have hstage' : ∀ {i j : I} (f : i ⟶ j)
      (φ : stageDerivedObj F A₀ i K₀ ⟶ stageDerivedObj F A₀ i L₀),
      eH j (H.map f ((eH i).symm φ)) = stageDerivedHomTransition F A₀ f K₀ L₀ φ := by
    intro i j f φ
    rw [hstage f, Equiv.apply_symm_apply]
    simp only [stageDerivedHomTransition, stageDerivedExtensionIso, hcompeq]
  have hlimit' : ∀ (i : I) (φ : stageDerivedObj F A₀ i K₀ ⟶ stageDerivedObj F A₀ i L₀),
      eTarget (s.ι.app i ((eH i).symm φ)) = stageDerivedHomComparison c A₀ i K₀ L₀ φ := by
    intro i φ
    rw [hlimit i φ]
    simp only [stageDerivedHomComparison, limitDerivedExtensionIso, hcompeq]
  refine ⟨fun ψ => ?_, fun i φ φ' hφ => ?_⟩
  · obtain ⟨i, x, hx⟩ := Types.jointly_surjective_of_isColimit hs (eTarget.symm ψ)
    refine ⟨i, eH i x, ?_⟩
    rw [← hlimit' i (eH i x), Equiv.symm_apply_apply, hx, Equiv.apply_symm_apply]
  · rw [← hlimit' i φ, ← hlimit' i φ'] at hφ
    obtain ⟨j, f, hf⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hs ((eH i).symm φ) ((eH i).symm φ')).1
        (eTarget.injective hφ)
    exact ⟨j, f, by rw [← hstage' f φ, ← hstage' f φ', hf]⟩

include hc in
/-- **Stacks 0DHX, surjectivity of the comparison maps.** Every morphism between the extensions
of scalars of a pseudo-coherent `K₀` and an `L₀` of finite Tor dimension to `A = R ⊗[R₀] A₀` is
the extension of scalars of a morphism at some stage. -/
public theorem exists_stageDerivedHom
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K₀)
    (hL : HasFiniteTorDimensionCanonical R₀
      ((ModuleCat.restrictScalars (algebraMap R₀ A₀)).mapDerivedCategory.obj L₀))
    (ψ : limitDerivedObj c A₀ K₀ ⟶ limitDerivedObj c A₀ L₀) :
    ∃ (i : I) (φ : stageDerivedObj F A₀ i K₀ ⟶ stageDerivedObj F A₀ i L₀),
      stageDerivedHomComparison c A₀ i K₀ L₀ φ = ψ :=
  (stageDerivedHom_descent F c hc A₀ K₀ L₀ hK hL).1 ψ

include hc in
/-- **Stacks 0DHX, injectivity of the comparison maps.** Two morphisms at a stage between the
extensions of scalars of a pseudo-coherent `K₀` and an `L₀` of finite Tor dimension whose
extensions to `A = R ⊗[R₀] A₀` agree already agree after extension of scalars to some later
stage. -/
public theorem exists_stageDerivedHomTransition_eq
    (hK : StacksDraft.PseudoCoherence.IsPseudoCoherent K₀)
    (hL : HasFiniteTorDimensionCanonical R₀
      ((ModuleCat.restrictScalars (algebraMap R₀ A₀)).mapDerivedCategory.obj L₀))
    (i : I) (φ φ' : stageDerivedObj F A₀ i K₀ ⟶ stageDerivedObj F A₀ i L₀)
    (hφ : stageDerivedHomComparison c A₀ i K₀ L₀ φ =
      stageDerivedHomComparison c A₀ i K₀ L₀ φ') :
    ∃ (j : I) (f : i ⟶ j),
      stageDerivedHomTransition F A₀ f K₀ L₀ φ =
        stageDerivedHomTransition F A₀ f K₀ L₀ φ' :=
  (stageDerivedHom_descent F c hc A₀ K₀ L₀ hK hL).2 i φ φ' hφ

end HomDescent

/-! ### The relatively perfect objects over the colimit -/

section ObjectDescent

variable {R₀ : Type uR} [CommRing R₀] {I : Type uI} [Category.{uJ} I] [IsFiltered I]
  (F : I ⥤ CommAlgCat.{uR} R₀) (c : Cocone F)
  (hc : IsColimit ((CommAlgCat.uliftFunctor.{max uI uJ, uR, uR} R₀).mapCocone c))
  (A₀ : Type uR) [CommRing A₀] [Algebra R₀ A₀] [Module.Flat R₀ A₀]
  [Algebra.FinitePresentation R₀ A₀]

include hc in
/-- **Stacks 0DHX, descent of a relatively perfect object to a stage.** An object of
`D(A)` perfect relative to `R` is isomorphic to the derived extension of scalars of an object
of `D(Aᵢ)` perfect relative to `Rᵢ`, for some stage `i`. -/
public theorem exists_relativelyPerfect_stage
    (K : DerivedCategory (ModuleCat.{uR} (c.pt ⊗[R₀] A₀)))
    (hK : IsRelativelyPerfect.{uR, uR, uR}
      (canonicalDerivedTensoringDatum c.pt).tensor
      (canonicalDerivedTensoringDatum c.pt).comparison
      (canonicalDerivedTensoringDatum c.pt).isLeftDerived K) :
    ∃ (i : I) (Kᵢ : DerivedCategory (ModuleCat.{uR} (stageAlgebra F A₀ i))),
      IsRelativelyPerfect.{uR, uR, uR}
          (canonicalDerivedTensoringDatum (F.obj i)).tensor
          (canonicalDerivedTensoringDatum (F.obj i)).comparison
          (canonicalDerivedTensoringDatum (F.obj i)).isLeftDerived Kᵢ ∧
        Nonempty ((totalDerivedExtensionScalars.{uR, uR, uR}
          (stageToLimitMap c A₀ i)).functor.obj Kᵢ ≅ K) := by
  obtain ⟨-, -, -, -, -, -, hsurj, -, -, -, -⟩ :=
    relativelyPerfectComplexes_filteredColimit.{uI, uJ, uR, uR, uR} F c hc A₀
      (canonicalDerivedTensoringDatum R₀) (fun i => canonicalDerivedTensoringDatum (F.obj i))
      (canonicalDerivedTensoringDatum c.pt)
  exact hsurj K hK

end ObjectDescent

end PseudoCoherence

end
