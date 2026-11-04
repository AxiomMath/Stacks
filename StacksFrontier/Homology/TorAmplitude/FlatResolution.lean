module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Equalizer
public import StacksFrontier.Algebra.Homology.Embedding.TruncLEDegreewise
public import StacksFrontier.Algebra.Homology.QuasiIsoRoof
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Homology.TorAmplitude.Comparison
public import StacksFrontier.Homology.TorAmplitude.Defs
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Flat representatives of objects of the derived category

Let `R` be a commutative ring. An object `K` of `D(R)` is *represented by a complex of flat
modules concentrated in `[a, b]`* when there is a cochain complex `E` of flat `R`-modules with
`E^i = 0` for `i ∉ [a, b]` together with an isomorphism `K ≅ Q E`. Such an object has Tor
amplitude in `[a, b]`, and conversely.

## Main definitions

* `StacksDraft.TorAmplitude.HasFlatRepresentative`: existence of a complex of flat modules
  concentrated in `[a, b]` representing the given object of `D(R)`.

## Main results

* `StacksDraft.TorAmplitude.isZero_homology_of_hasTorAmplitude`: if `Q K` has Tor amplitude in
  `[a, b]`, the cohomology of `K` vanishes outside `[a, b]`.
* `StacksDraft.TorAmplitude.hasTorAmplitude_iff_hasFlatRepresentative`: an object of `D(R)` has
  Tor amplitude in `[a, b]` if and only if it has a flat representative in `[a, b]`.
* `StacksDraft.TorAmplitude.moduleHasFiniteTorDimension_iff_exists_flat_roof`: a module has
  finite Tor dimension if and only if a bounded complex of flat modules is joined to `M[0]` by a
  roof of quasi-isomorphisms, a condition that mentions no derived category.

## Implementation notes

The statements that involve `D(R)` take its model as an instance argument, so they hold for any
model.

## References

* [Stacks Project, Tag 0654](https://stacks.math.columbia.edu/tag/0654)
-/

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.TorAmplitude

universe u v w

@[expose] public section

/-- An object `K` of `D(R)` *has a flat representative in `[a, b]`* if there is a cochain
complex `E` of flat `R`-modules with `E^i = 0` for `i ∉ [a, b]` and an isomorphism
`K ≅ Q E` in the derived category. -/
public def HasFlatRepresentative {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    (K : DerivedCategory (ModuleCat.{max u v} R)) (a b : ℤ) : Prop :=
  ∃ E : CochainComplex (ModuleCat.{max u v} R) ℤ,
    (∀ i : ℤ, Module.Flat R (E.X i)) ∧ E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
      Nonempty (K ≅ DerivedCategory.Q.obj E)

/-- Having a flat representative in `[a, b]` only depends on the isomorphism class in `D(R)`. -/
public theorem hasFlatRepresentative_of_iso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{max u v} R)]
    {K L : DerivedCategory (ModuleCat.{max u v} R)} (e : K ≅ L) {a b : ℤ}
    (h : HasFlatRepresentative K a b) : HasFlatRepresentative L a b := by
  obtain ⟨E, hflat, hGE, hLE, ⟨f⟩⟩ := h
  exact ⟨E, hflat, hGE, hLE, ⟨e.symm ≪≫ f⟩⟩

/-- Tor amplitude in `[a, b]`, for a certified derived tensor product, only depends on the
isomorphism class of the object in `D(R)`. -/
public theorem hasTorAmplitude_of_iso {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{v} R)]
    {derivedTensor :
      DerivedCategory (ModuleCat.{v} R) ⥤
        DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v} R)}
    {comparison : ∀ M : ModuleCat.{v} R,
      DerivedCategory.Q ⋙
          derivedTensor.flip.obj
            ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M) ⟶
        (tensorModuleRight M).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q}
    {isLeftDerived : ∀ M : ModuleCat.{v} R,
      (derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).IsLeftDerivedFunctor
        (comparison M)
        (HomologicalComplex.quasiIso (ModuleCat.{v} R) (ComplexShape.up ℤ))}
    {K L : DerivedCategory (ModuleCat.{v} R)} (e : K ≅ L) (a b : ℤ) :
    HasTorAmplitude derivedTensor comparison isLeftDerived K a b ↔
      HasTorAmplitude derivedTensor comparison isLeftDerived L a b :=
  have key : ∀ {K L : DerivedCategory (ModuleCat.{v} R)}, (K ≅ L) →
      HasTorAmplitude derivedTensor comparison isLeftDerived K a b →
        HasTorAmplitude derivedTensor comparison isLeftDerived L a b :=
    fun e h M i hi ↦ (h M i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} R) i).mapIso
        ((derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{v} R) 0).obj M)).mapIso e.symm))
  ⟨key e, key e.symm⟩

/-- An object of `D(R)` whose cohomology vanishes above `b` is represented by a complex of
projective modules with terms vanishing above `b`. -/
public theorem exists_projective_representative_of_isLE {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : DerivedCategory (ModuleCat.{u} R)) (b : ℤ)
    (hK : ∀ i : ℤ, b < i →
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K)) :
    ∃ P : CochainComplex (ModuleCat.{u} R) ℤ,
      (∀ i, Projective (P.X i)) ∧ P.IsStrictlyLE b ∧
        Nonempty (K ≅ DerivedCategory.Q.obj P) := by
  obtain ⟨L, e, hL⟩ := (DerivedCategory.isLE_iff K b).2 hK
  obtain ⟨P, _⟩ := ProjectiveResolutionLemma.statement3 b L hL
  have : QuasiIso P.α := P.quasiIso
  exact ⟨P.complex, P.projective, P.boundedAbove,
    ⟨e ≪≫ (asIso (DerivedCategory.Q.map P.α)).symm⟩⟩

/-- In a short exact sequence of modules whose middle and right terms are flat, the left term
is flat. -/
public theorem flat_of_shortExact_left {R : Type u} [CommRing R]
    (S : ShortComplex (ModuleCat.{v} R)) (hS : S.ShortExact)
    [Module.Flat R S.X₂] [Module.Flat R S.X₃] :
    Module.Flat R S.X₁ := by
  have hi := (ModuleCat.mono_iff_injective S.f).1 hS.mono_f
  have hs := (ModuleCat.epi_iff_surjective S.g).1 hS.epi_g
  have he := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hS.exact
  rw [Module.Flat.iff_rTensor_preserves_injective_linearMap]
  intro N N' _ _ _ _ f hf
  have hN := LinearMap.lTensor_injective_of_exact_of_flat S.g.hom hs S.f.hom hi he N
  have hcomp := (Module.Flat.rTensor_preserves_injective_linearMap (M := S.X₂) f hf).comp hN
  have hEq : (f.rTensor S.X₂) ∘ₗ (S.f.hom.lTensor N) =
      (S.f.hom.lTensor N') ∘ₗ (f.rTensor S.X₁) := by simp
  rw [← LinearMap.coe_comp, hEq] at hcomp
  exact fun x y hxy ↦ hcomp (congrArg (S.f.hom.lTensor N') hxy)

/-- Above the truncation degree the canonical truncation `τ^{≥ a}` agrees with the complex. -/
@[sga "4 XVII 1.1.13" "clause, special case"]
public theorem isIso_πTruncGE_f {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a i : ℤ) (hi : a < i) :
    IsIso ((K.πTruncGE a).f i) := by
  have h : (ComplexShape.embeddingUpIntGE a).f (i - a).natAbs = i := by
    show a + ((i - a).natAbs : ℤ) = i
    lia
  have hn : ¬ (ComplexShape.embeddingUpIntGE a).BoundaryGE (i - a).natAbs := by
    rw [ComplexShape.boundaryGE_embeddingUpIntGE_iff, Int.natAbs_eq_zero]
    lia
  exact K.isIso_πTruncGE_f _ h hn

/-- The canonical truncation `τ^{≥ a}` of a termwise flat complex is termwise flat as soon as
its degree-`a` opcycles are flat. -/
public theorem flat_truncGE {R : Type u} [CommRing R]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a : ℤ)
    [∀ i, Module.Flat R (K.X i)] [Module.Flat R (K.opcycles a)] :
    ∀ i, Module.Flat R ((K.truncGE a).X i) := by
  intro i
  rcases lt_trichotomy i a with hi | hi | hi
  · have := ModuleCat.isZero_iff_subsingleton.1
      ((K.truncGE a).isZero_of_isStrictlyGE a i hi)
    infer_instance
  · subst i
    exact Module.Flat.of_linearEquiv (K.truncGEXIsoOpcycles a).toLinearEquiv
  · exact Module.Flat.of_linearEquiv (K.truncGEXIso a i hi).toLinearEquiv

/-- The canonical truncation `τ^{≥ a}` of a complex vanishing above `b` again vanishes
above `b`. -/
public theorem truncGE_isStrictlyLE {R : Type u} [CommRing R]
    (P : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ) (hP : P.IsStrictlyLE b) :
    (P.truncGE a).IsStrictlyLE b := by
  rw [CochainComplex.isStrictlyLE_iff] at hP ⊢
  intro i hi
  have : Epi ((P.πTruncGE a).f i) := by
    unfold CochainComplex.πTruncGE
    infer_instance
  exact IsZero.of_epi ((P.πTruncGE a).f i) (hP i hi)

/-! ### Tensoring with the unit -/

/-- Tensoring on the right by `R` itself is the identity functor on `R`-modules. -/
public noncomputable def tensorModuleRightUnitIso {R : Type u} [CommRing R] :
    tensorModuleRight (ModuleCat.of R R) ≅ 𝟭 (ModuleCat.{u} R) :=
  NatIso.ofComponents (fun N => (TensorProduct.rid R N).toModuleIso) (by
    intro X Y f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x
    change (TensorProduct.rid R Y) ((f.hom.rTensor (ModuleCat.of R R)) (x ⊗ₜ 1)) =
      f.hom ((TensorProduct.rid R X) (x ⊗ₜ 1))
    simp)

/-- Termwise tensoring a cochain complex by `R` itself is the identity. -/
public noncomputable def tensorModuleRightUnitComplexIso {R : Type u} [CommRing R] :
    (tensorModuleRight (ModuleCat.of R R)).mapHomologicalComplex (ComplexShape.up ℤ) ≅
      𝟭 (CochainComplex (ModuleCat.{u} R) ℤ) :=
  NatIso.mapHomologicalComplex tensorModuleRightUnitIso (ComplexShape.up ℤ) ≪≫
    Functor.mapHomologicalComplexIdIso _ _

/-- The natural transformation from `Q` to termwise tensoring by `R` itself followed by `Q`,
given at each complex by the localisation of the inverse of the unit isomorphism. -/
public noncomputable def tensorModuleRightUnitComparison {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] :
    DerivedCategory.Q ⋙ 𝟭 (DerivedCategory (ModuleCat.{u} R)) ⟶
      (tensorModuleRight (ModuleCat.of R R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q where
  app K := DerivedCategory.Q.map (tensorModuleRightUnitComplexIso.inv.app K)
  naturality X Y f := by
    dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map]
    rw [← Functor.map_comp, ← Functor.map_comp]
    congr 1

/-- The natural transformation `tensorModuleRightUnitComparison` is an isomorphism at every
complex. -/
public instance {R : Type u} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (K : CochainComplex (ModuleCat.{u} R) ℤ) :
    IsIso ((tensorModuleRightUnitComparison (R := R)).app K) := by
  dsimp only [tensorModuleRightUnitComparison]
  infer_instance

/-- If `Q K` has Tor amplitude in `[a, b]` for some certified derived tensor product, then the
cohomology of `K` vanishes outside `[a, b]`. -/
public theorem isZero_homology_of_hasTorAmplitude {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {derivedTensor : DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R)}
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
          (comparison N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (K : CochainComplex (ModuleCat.{u} R) ℤ) (a b : ℤ)
    (h : HasTorAmplitude derivedTensor comparison isLeftDerived (DerivedCategory.Q.obj K) a b)
    (i : ℤ) (hi : i < a ∨ b < i) : IsZero (K.homology i) := by
  have hLD := isLeftDerived (ModuleCat.of R R)
  have hfac := Functor.leftDerived_fac_app
    (derivedTensor.flip.obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj (ModuleCat.of R R)))
    (comparison (ModuleCat.of R R))
    (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ))
    (𝟭 _) tensorModuleRightUnitComparison K
  have hsplit : IsSplitEpi ((comparison (ModuleCat.of R R)).app K) :=
    ⟨⟨inv ((tensorModuleRightUnitComparison (R := R)).app K) ≫
      (Functor.leftDerivedLift _ (comparison (ModuleCat.of R R)) _ (𝟭 _)
        tensorModuleRightUnitComparison).app (DerivedCategory.Q.obj K),
      by rw [Category.assoc, hfac, IsIso.inv_hom_id]⟩⟩
  have hz0 := h (ModuleCat.of R R) i (by simpa only [Set.mem_Icc, not_and_or, not_le] using hi)
  have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
      (((tensorModuleRight (ModuleCat.of R R)).mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        DerivedCategory.Q).obj K)) := by
    have hsec : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
          (section_ ((comparison (ModuleCat.of R R)).app K)) ≫
        (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
          ((comparison (ModuleCat.of R R)).app K) = 𝟙 _ := by
      rw [← Functor.map_comp, IsSplitEpi.id, CategoryTheory.Functor.map_id]
    have hzero : (DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).map
        (section_ ((comparison (ModuleCat.of R R)).app K)) = 0 := hz0.eq_of_tgt _ _
    rw [IsZero.iff_id_eq_zero, ← hsec, hzero, Limits.zero_comp]
  exact (hz.of_iso ((DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app _).symm).of_iso
    ((HomologicalComplex.homologyFunctor _ _ i).mapIso
      (tensorModuleRightUnitComplexIso.app K)).symm

/-! ### Tor amplitude and flat representatives -/

/-- For a certified derived tensor product, an object `K` of `D(R)` has Tor amplitude in `[a, b]`
if and only if it is represented by a complex of flat `R`-modules concentrated in degrees
`[a, b]`. -/
public theorem hasTorAmplitude_iff_hasFlatRepresentative {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {derivedTensor : DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R)}
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
          (comparison N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (K : DerivedCategory (ModuleCat.{u} R)) (a b : ℤ) :
    HasTorAmplitude derivedTensor comparison isLeftDerived K a b ↔
      HasFlatRepresentative K a b := by
  constructor
  · intro hK
    have hKLE : ∀ i : ℤ, b < i →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) := by
      intro i hi
      have hL := (hasTorAmplitude_of_iso
        (DerivedCategory.Q.objObjPreimageIso K) a b).mpr hK
      exact (isZero_homology_of_hasTorAmplitude comparison isLeftDerived
          (DerivedCategory.Q.objPreimage K) a b hL i (Or.inr hi)).of_iso
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).mapIso
            (DerivedCategory.Q.objObjPreimageIso K).symm ≪≫
          (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} R) i).app _)
    obtain ⟨P, hproj, hBound, ⟨eP⟩⟩ := exists_projective_representative_of_isLE K b hKLE
    have hP := (hasTorAmplitude_of_iso eP a b).mp hK
    have hflat : ∀ i : ℤ, Module.Flat R (P.X i) := fun i => by
      have := hproj i
      infer_instance
    have hbdd : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (P.X i) :=
      ⟨b, (CochainComplex.isStrictlyLE_iff P b).mp hBound⟩
    have htw := (hasTorAmplitude_iff_termwise_of_flat comparison isLeftDerived P hbdd
      hflat a b).mp hP
    have hGE : P.IsGE a := (CochainComplex.isGE_iff P a).2 fun i hi ↦
      (P.exactAt_iff_isZero_homology i).2
        (isZero_homology_of_hasTorAmplitude comparison isLeftDerived P a b hP i (Or.inl hi))
    have hcok : Module.Flat R (cokernel (P.d (a - 1) a) : ModuleCat.{u} R) :=
      StacksDraft.TorAmplitude.Termwise.cokernel_flat_of_termwise_torAmplitude P a b hflat htw
    have hopc : Module.Flat R (P.opcycles a) := by
      have e₂ : P.opcycles a ≅ (cokernel (P.d (a - 1) a) : ModuleCat.{u} R) :=
        IsColimit.coconePointUniqueUpToIso (P.opcyclesIsCokernel (a - 1) a (by simp))
          (colimit.isColimit _)
      exact Module.Flat.of_linearEquiv e₂.toLinearEquiv
    have : QuasiIso (P.πTruncGE a) := inferInstance
    exact ⟨P.truncGE a, flat_truncGE P a, inferInstance,
      truncGE_isStrictlyLE P a b hBound,
      ⟨eP ≪≫ asIso (DerivedCategory.Q.map (P.πTruncGE a))⟩⟩
  · rintro ⟨E, hflat, hGE, hLE, ⟨e⟩⟩
    have hbdd : ∃ n : ℤ, ∀ i : ℤ, n < i → IsZero (E.X i) :=
      ⟨b, (CochainComplex.isStrictlyLE_iff E b).mp hLE⟩
    refine (hasTorAmplitude_of_iso e a b).mpr
      ((hasTorAmplitude_iff_termwise_of_flat comparison isLeftDerived E hbdd hflat a b).mpr ?_)
    intro M i hi
    have hzX : IsZero (E.X i) :=
      hi.elim (E.isZero_of_isStrictlyGE a i ·) (E.isZero_of_isStrictlyLE b i ·)
    exact ShortComplex.isZero_homology_of_isZero_X₂ _
      ((MonoidalCategory.tensorRight M).map_isZero hzX)

/-- Finite Tor dimension of a module, read off any certified derived tensor product on any model
of `D(R)`, is the existence of a bounded complex of flat modules joined to `M[0]` by a roof of
quasi-isomorphisms; the right-hand side mentions no derived category. -/
public theorem moduleHasFiniteTorDimension_iff_exists_flat_roof {R : Type u} [CommRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    {derivedTensor : DerivedCategory (ModuleCat.{u} R) ⥤
      DerivedCategory (ModuleCat.{u} R) ⥤ DerivedCategory (ModuleCat.{u} R)}
    (comparison : ∀ N : ModuleCat.{u} R,
      DerivedCategory.Q ⋙ derivedTensor.flip.obj
          ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N) ⟶
        (tensorModuleRight N).mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
    (isLeftDerived : ∀ N : ModuleCat.{u} R,
      (derivedTensor.flip.obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj N)).IsLeftDerivedFunctor
          (comparison N)
          (HomologicalComplex.quasiIso (ModuleCat.{u} R) (ComplexShape.up ℤ)))
    (M : ModuleCat.{u} R) :
    ModuleHasFiniteTorDimension derivedTensor comparison isLeftDerived M ↔
      ∃ (a b : ℤ) (E : CochainComplex (ModuleCat.{u} R) ℤ), (∀ i, Module.Flat R (E.X i)) ∧
        E.IsStrictlyGE a ∧ E.IsStrictlyLE b ∧
          CochainComplex.QuasiIsoRoof E
            ((CochainComplex.singleFunctor (ModuleCat.{u} R) 0).obj M) := by
  refine exists₂_congr fun a b => ?_
  rw [hasTorAmplitude_iff_hasFlatRepresentative comparison isLeftDerived]
  refine exists_congr fun E => and_congr_right fun _ => and_congr_right fun _ =>
    and_congr_right fun _ => ?_
  rw [CochainComplex.quasiIsoRoof_iff_nonempty_iso]
  let e := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app M
  exact ⟨fun ⟨f⟩ => ⟨f.symm ≪≫ e⟩, fun ⟨f⟩ => ⟨e ≪≫ f.symm⟩⟩

end

end StacksDraft.TorAmplitude
