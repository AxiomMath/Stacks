module

public import StacksFrontier.Homology.PseudoCoherent.Products.Comparison
import all StacksFrontier.Homology.PseudoCoherent.Products.Comparison
import StacksFrontier.Algebra.Homology.DerivedCategory.TriangleApproximation

/-!
# Pseudo-coherence and products: the characterization

The second half of the proof of Stacks 0CYB: the termwise analysis of the comparison morphisms
on complexes with finite free terms, approximation of a pseudo-coherent object by a bounded
complex of finite free modules, the passage through mapping-cone triangles, and pseudo-coherence
from the products of the cohomology of `K ⊗ᴸ R^A`. The file ends with the characterization
itself.

## Main results

* `StacksDraft.PseudoCoherence.pseudoCoherent_iff_derivedTensor_preserves_products`: both
  four-way characterizations, of pseudo-coherence and of `m`-pseudo-coherence.

## References

* [Stacks Project, Tag 0CYB](https://stacks.math.columbia.edu/tag/0CYB)
-/

@[expose] public section

namespace StacksDraft.PseudoCoherence

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated MonoidalCategory
open scoped ZeroObject

-- We use the standard construction of the derived category of an abelian category, which
-- supplies the triangulated structure and the cohomology functors `Hⁱ`.
attribute [local instance] HasDerivedCategory.standard

universe u v w

private lemma isIso_piComparison_tensorWithCochainComplex_f
    (S : Type v) [CommRing S] (E : CochainComplex (ModuleCat.{v} S) ℤ)
    (A : Type v) (Q : A → ModuleCat.{v} S) (i : ℤ)
    [Module.FinitePresentation S (E.X i)] :
    IsIso ((piComparison (tensorWithCochainComplex E) Q).f i) := by
  let ev := HomologicalComplex.eval (ModuleCat S) (ComplexShape.up ℤ) i
  have := isIso_piComparison_tensorLeft_of_finitePresentation S (E.X i) A Q
  have h : IsIso (piComparison (tensorWithCochainComplex E ⋙ ev) Q) :=
    (isIso_map_piComparison_iff_of_natIso (tensorSingleEvalIso E i)
      (𝟭 (ModuleCat S)) Q).mp inferInstance
  rw [Stacks.DerivedProducts.piComparison_comp_eq] at h
  exact (isIso_comp_right_iff _ _).mp h

private lemma epi_piComparison_tensorWithCochainComplex_f
    (S : Type v) [CommRing S] (E : CochainComplex (ModuleCat.{v} S) ℤ)
    (A : Type v) (Q : A → ModuleCat.{v} S) (i : ℤ)
    [Module.Finite S (E.X i)] :
    Epi ((piComparison (tensorWithCochainComplex E) Q).f i) := by
  let ev := HomologicalComplex.eval (ModuleCat S) (ComplexShape.up ℤ) i
  have := epi_piComparison_tensorLeft_of_finite S (E.X i) A Q
  have h : Epi (piComparison (tensorWithCochainComplex E ⋙ ev) Q) :=
    (epi_map_piComparison_iff_of_natIso (tensorSingleEvalIso E i)
      (𝟭 (ModuleCat S)) Q).mp inferInstance
  rw [Stacks.DerivedProducts.piComparison_comp_eq] at h
  exact (epi_comp_iff_of_isIso _ _).mp h

private lemma epi_homologyMap_of_epi_of_mono
    {S : Type v} [Ring S] {L M : ShortComplex (ModuleCat.{v} S)}
    (f : L ⟶ M) [Epi f.τ₂] [Mono f.τ₃] : Epi (ShortComplex.homologyMap f) := by
  apply ShortComplex.epi_homologyMap_of_epi_cyclesMap'
  rw [ModuleCat.epi_iff_surjective]
  intro y
  obtain ⟨x, hx⟩ := (ModuleCat.epi_iff_surjective f.τ₂).mp inferInstance (M.iCycles y)
  have hd : L.g x = 0 := by
    apply (ModuleCat.mono_iff_injective f.τ₃).mp inferInstance
    rw [map_zero, ← ModuleCat.comp_apply, ← f.comm₂₃, ModuleCat.comp_apply, hx]
    exact congrArg (fun g : M.cycles ⟶ M.X₃ => g y) M.iCycles_g
  refine ⟨L.cyclesMk x hd, ?_⟩
  apply (ModuleCat.mono_iff_injective M.iCycles).mp inferInstance
  rw [← ModuleCat.comp_apply, ShortComplex.cyclesMap_i]
  change f.τ₂ (L.iCycles (L.cyclesMk x hd)) = M.iCycles y
  have hx' : L.iCycles (L.cyclesMk x hd) = x := L.i_cyclesMk x hd
  rwa [hx']

private lemma homologyRange_of_termwise
    {S : Type v} [Ring S] {L M : CochainComplex (ModuleCat.{v} S) ℤ}
    (f : L ⟶ M) (m : ℤ) (hi : ∀ i, m < i → IsIso (f.f i)) (hm : Epi (f.f m)) :
    (∀ i, m < i → IsIso (HomologicalComplex.homologyMap f i)) ∧
      Epi (HomologicalComplex.homologyMap f m) := by
  constructor
  · intro i hmi
    apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
    · change Epi (f.f ((ComplexShape.up ℤ).prev i))
      rw [ComplexShape.prev_eq' _ (show (ComplexShape.up ℤ).Rel (i - 1) i by simp)]
      by_cases h : i - 1 = m
      · rw [h]
        exact hm
      · have := hi (i - 1) (by omega)
        infer_instance
    · exact hi i hmi
    · change Mono (f.f ((ComplexShape.up ℤ).next i))
      rw [ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel i (i + 1) from rfl)]
      have := hi (i + 1) (by omega)
      infer_instance
  · have hnext : Mono (f.f ((ComplexShape.up ℤ).next m)) := by
      rw [ComplexShape.next_eq' _ (show (ComplexShape.up ℤ).Rel m (m + 1) from rfl)]
      have := hi (m + 1) (by omega)
      infer_instance
    let : Epi ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) m).map f).τ₂ := hm
    let : Mono ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) m).map f).τ₃ := hnext
    exact epi_homologyMap_of_epi_of_mono
      ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) m).map f)

private lemma homologyRange_tensorProductComparison_of_finite_terms
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R)
    (E : CochainComplex (ModuleCat.{max v w} (SmallRing.{u, v, w} R)) ℤ)
    (hE : E.KFlat) (m : ℤ)
    (hi : ∀ i, m < i → Module.FinitePresentation (SmallRing.{u, v, w} R) (E.X i))
    (hm : Module.Finite (SmallRing.{u, v, w} R) (E.X m))
    (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)) :
    (∀ i, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
      (tensorProductComparison T P (DerivedCategory.Q.obj E) A Q))) ∧
    Epi ((DerivedCategory.homologyFunctor _ m).map
      (tensorProductComparison T P (DerivedCategory.Q.obj E) A Q)) := by
  have h := homologyRange_of_termwise
    (piComparison (tensorWithCochainComplex E) Q) m
    (fun i hmi => by
      have := hi i hmi
      exact isIso_piComparison_tensorWithCochainComplex_f _ E A Q i)
    (epi_piComparison_tensorWithCochainComplex_f _ E A Q m)
  exact ⟨fun i hmi =>
    (homology_tensorProductComparison_iff_of_kFlat R T P E hE A Q i).1.mpr (h.1 i hmi),
    (homology_tensorProductComparison_iff_of_kFlat R T P E hE A Q m).2.mpr h.2⟩

set_option backward.isDefEq.respectTransparency false in
private lemma tensorSingleTermIso_d
    (S : Type v) [CommRing S] (E : CochainComplex (ModuleCat.{v} S) ℤ)
    (N : ModuleCat.{v} S) (i j : ℤ) (h : i + 1 = j) :
    (E.d i j ▷ N) ≫ (tensorSingleTermIso E N j).hom =
      (tensorSingleTermIso E N i).hom ≫
        ((tensorWithCochainComplex E).obj N).d i j := by
  subst j
  dsimp [tensorSingleTermIso, tensorWithCochainComplex]
  change _ = _ ≫ (HomologicalComplex.mapBifunctor E
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj N)
    (curriedTensor (ModuleCat S)) (ComplexShape.up ℤ)).d i (i + 1)
  simp only [id_tensorHom,
    Category.assoc, HomologicalComplex.mapBifunctor.d_eq, Preadditive.comp_add,
    HomologicalComplex.mapBifunctor.ι_D₁, HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq _ _ _ _ (show
    (ComplexShape.up ℤ).Rel i (i + 1) from rfl) _ _ (by simp),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ _ (show
    (ComplexShape.up ℤ).Rel 0 1 from rfl) _ (by simp)]
  simp only [HomologicalComplex.single_obj_d, Functor.map_zero, zero_comp,
    smul_zero, comp_zero, add_zero, ComplexShape.ε₁,
    curriedTensor_map_app]
  rw [← Category.assoc, ← whisker_exchange]
  simp [TotalComplexShape.ε₁, Category.assoc]

private noncomputable def tensorSingleComplexIso
    (S : Type v) [CommRing S] (E : CochainComplex (ModuleCat.{v} S) ℤ)
    (N : ModuleCat.{v} S) :
    ((tensorRight N).mapHomologicalComplex (ComplexShape.up ℤ)).obj E ≅
      (tensorWithCochainComplex E).obj N :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i => tensorSingleTermIso E N i)
    (fun i j h => (tensorSingleTermIso_d S E N i j h).symm)

private noncomputable def productProjection
    (S : Type v) [Ring S] (A : Type v) (a : A) :
    piDiscreteFunctor (fun _ : A => 𝟭 (ModuleCat.{v} S)) ⋙ lim ⟶ 𝟭 (ModuleCat.{v} S) where
  app M := Pi.π (fun _ : A => M) a
  naturality {X Y} f := by
    change Limits.Pi.map (fun _ : A => f) ≫ Pi.π (fun _ : A => Y) a = _
    exact Pi.map_π _ _

set_option backward.isDefEq.respectTransparency false in
private noncomputable def termwiseProductIso
    (S : Type v) [Ring S] (A : Type v) (E : CochainComplex (ModuleCat.{v} S) ℤ) :
    ((piDiscreteFunctor (fun _ : A => 𝟭 (ModuleCat.{v} S)) ⋙ lim).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj E ≅ ∏ᶜ (fun _ : A => E) := by
  let f := Pi.lift (fun a : A =>
    ((productProjection S A a).mapHomologicalComplex (ComplexShape.up ℤ)).app E ≫
      (Functor.mapHomologicalComplexIdIso (ModuleCat S) (ComplexShape.up ℤ)).hom.app E)
  have hf (i : ℤ) : IsIso (f.f i) := by
    let ev := HomologicalComplex.eval (ModuleCat S) (ComplexShape.up ℤ) i
    have heq : f.f i ≫ piComparison ev (fun _ : A => E) = 𝟙 _ := by
      apply Pi.hom_ext
      intro a
      rw [Category.assoc, piComparison_comp_π]
      change ((f ≫ Pi.π (fun _ : A => E) a).f i) = _
      simp [f, productProjection, ev]
    have : IsIso (f.f i ≫ piComparison ev (fun _ : A => E)) := by
      rw [heq]
      infer_instance
    exact IsIso.of_isIso_comp_right (f.f i) (piComparison ev (fun _ : A => E))
  have : IsIso f := HomologicalComplex.Hom.isIso_of_components f
  exact asIso f

private lemma termwiseProductIso_hom_π
    (S : Type v) [Ring S] (A : Type v) (E : CochainComplex (ModuleCat.{v} S) ℤ) (a : A) :
    (termwiseProductIso S A E).hom ≫ Pi.π (fun _ : A => E) a =
      ((productProjection S A a).mapHomologicalComplex (ComplexShape.up ℤ)).app E ≫
        (Functor.mapHomologicalComplexIdIso (ModuleCat S) (ComplexShape.up ℤ)).hom.app E :=
  Pi.lift_comp_π _ _

private noncomputable def tensorSingleUnitIso
    (S : Type v) [CommRing S] (E : CochainComplex (ModuleCat.{v} S) ℤ) :
    (tensorWithCochainComplex E).obj (ModuleCat.of S S) ≅ E :=
  (tensorSingleComplexIso S E (ModuleCat.of S S)).symm ≪≫
    (NatIso.mapHomologicalComplex (rightUnitorNatIso (ModuleCat S)) (ComplexShape.up ℤ)).app E ≪≫
    (Functor.mapHomologicalComplexIdIso (ModuleCat S) (ComplexShape.up ℤ)).app E

set_option backward.isDefEq.respectTransparency false in
private lemma moduleTensorRingPowerComparison_eq
    (S : Type v) [CommRing S] (A : Type v) (E : CochainComplex (ModuleCat.{v} S) ℤ) :
    ((moduleTensorRingPowerComparison S A).mapHomologicalComplex (ComplexShape.up ℤ)).app E ≫
        (termwiseProductIso S A E).hom =
      (tensorSingleComplexIso S E (ModuleCat.of S (A → S))).hom ≫
        (tensorWithCochainComplex E).map
          (ModuleCat.piIsoPi (fun _ : A => ModuleCat.of S S)).inv ≫
        piComparison (tensorWithCochainComplex E) (fun _ : A => ModuleCat.of S S) ≫
        Limits.Pi.map (fun _ : A => (tensorSingleUnitIso S E).hom) := by
  apply Pi.hom_ext
  intro a
  simp only [Category.assoc, termwiseProductIso_hom_π, Pi.map_π, piComparison_comp_π_assoc]
  ext i : 1
  simp only [HomologicalComplex.comp_f, NatTrans.mapHomologicalComplex_app_f]
  change (moduleTensorRingPowerComparison S A).app (E.X i) ≫ Pi.π (fun _ : A => E.X i) a = _
  rw [moduleTensorRingPowerComparison_comp_pi]
  simp only [tensorSingleComplexIso, HomologicalComplex.Hom.isoOfComponents_hom_f]
  let G := tensorWithCochainComplex E
  have hmap : (G.map (ModuleCat.piIsoPi (fun _ : A => ModuleCat.of S S)).inv).f i ≫
      (G.map (Pi.π (fun _ : A => ModuleCat.of S S) a)).f i =
      (G.map (ModuleCat.ofHom (LinearMap.proj a))).f i := by
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, ModuleCat.piIsoPi_inv_kernel_ι]
  rw [← Category.assoc ((G.map (ModuleCat.piIsoPi (fun _ : A => ModuleCat.of S S)).inv).f i)
    ((G.map (Pi.π (fun _ : A => ModuleCat.of S S) a)).f i), hmap, ← Category.assoc,
    ← tensorSingleTermIso_naturality]
  simp only [tensorSingleUnitIso, Iso.trans_hom, HomologicalComplex.comp_f,
    Iso.symm_hom, tensorSingleComplexIso, HomologicalComplex.Hom.isoOfComponents_inv_f,
    NatIso.mapHomologicalComplex, Category.assoc, Iso.hom_inv_id_assoc]
  apply ModuleCat.hom_ext
  apply TensorProduct.ext
  ext x r
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the instance `HasProductsOfShape A (CochainComplex (ModuleCat S) ℤ)` needs a larger
-- instance-synthesis budget than the default
private lemma epi_homology_moduleTensorRingPowerComparison_iff
    (S : Type v) [CommRing S] (A : Type v) (E : CochainComplex (ModuleCat.{v} S) ℤ)
    (i : ℤ) :
    Epi (ShortComplex.homologyMap ((E.sc i).mapNatTrans
      (moduleTensorRingPowerComparison S A))) ↔
      Epi (HomologicalComplex.homologyMap
        (piComparison (tensorWithCochainComplex E)
          (fun _ : A => ModuleCat.of S S)) i) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.up ℤ) i
  have h := congrArg H.map (moduleTensorRingPowerComparison_eq S A E)
  simp only [Functor.map_comp] at h
  change Epi (H.map (((moduleTensorRingPowerComparison S A).mapHomologicalComplex
    (ComplexShape.up ℤ)).app E)) ↔ _
  have : HasLimitsOfShape (Discrete A) (ModuleCat.{v} S) := ModuleCat.hasLimitsOfShape
  have : HasProductsOfShape A (CochainComplex (ModuleCat.{v} S) ℤ) := by
    infer_instance
  rw [← epi_comp_iff_of_isIso _ (H.map (termwiseProductIso S A E).hom), h,
    epi_comp_iff_of_epi, epi_comp_iff_of_epi, epi_comp_iff_of_isIso]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
-- the instance `HasProductsOfShape A (CochainComplex (ModuleCat S) ℤ)` needs a larger
-- instance-synthesis budget than the default
lemma isIso_homology_moduleTensorRingPowerComparison_iff
    (S : Type v) [CommRing S] (A : Type v) (E : CochainComplex (ModuleCat.{v} S) ℤ)
    (i : ℤ) :
    IsIso (ShortComplex.homologyMap ((E.sc i).mapNatTrans
      (moduleTensorRingPowerComparison S A))) ↔
      IsIso (HomologicalComplex.homologyMap
        (piComparison (tensorWithCochainComplex E)
          (fun _ : A => ModuleCat.of S S)) i) := by
  let H := HomologicalComplex.homologyFunctor (ModuleCat S) (ComplexShape.up ℤ) i
  have h := congrArg H.map (moduleTensorRingPowerComparison_eq S A E)
  simp only [Functor.map_comp] at h
  change IsIso (H.map (((moduleTensorRingPowerComparison S A).mapHomologicalComplex
    (ComplexShape.up ℤ)).app E)) ↔ _
  have : HasLimitsOfShape (Discrete A) (ModuleCat.{v} S) := ModuleCat.hasLimitsOfShape
  have : HasProductsOfShape A (CochainComplex (ModuleCat.{v} S) ℤ) := by
    infer_instance
  rw [← isIso_comp_right_iff _ (H.map (termwiseProductIso S A E).hom), h,
    isIso_comp_left_iff, isIso_comp_left_iff, isIso_comp_right_iff]
  rfl

private lemma homologyRange_tensorProductComparison_iff_of_iso
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R)
    {K L : D.{u, v, w} R} (e : K ≅ L) (m : ℤ)
    (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)) :
    ((∀ i, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
      (tensorProductComparison T P K A Q))) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map (tensorProductComparison T P K A Q))) ↔
    ((∀ i, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
      (tensorProductComparison T P L A Q))) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map (tensorProductComparison T P L A Q))) := by
  let := hasProductsOfShape R P A
  change ((∀ i, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
    (piComparison (T.tensor.obj K) _))) ∧ Epi ((DerivedCategory.homologyFunctor _ m).map
    (piComparison (T.tensor.obj K) _))) ↔ _
  exact and_congr (forall₂_congr fun i _ => isIso_map_piComparison_iff_of_natIso
    (T.tensor.mapIso e) (DerivedCategory.homologyFunctor _ i) _)
    (epi_map_piComparison_iff_of_natIso (T.tensor.mapIso e)
      (DerivedCategory.homologyFunctor _ m) _)

private lemma exists_projective_representative_le
    {C : Type*} [Category C] [Abelian C] [EnoughProjectives C]
    (K : DerivedCategory C) (b : ℤ) [K.IsLE b] :
    ∃ E : CochainComplex C ℤ, E.IsStrictlyLE b ∧
      (∀ i, Projective (E.X i)) ∧ Nonempty (DerivedCategory.Q.obj E ≅ K) := by
  obtain ⟨L, e, hL⟩ := (inferInstance : K.IsLE b)
  obtain ⟨P, _⟩ := ProjectiveResolutionLemma.statement3 b L hL
  have : QuasiIso P.α := P.quasiIso
  exact ⟨P.complex, P.boundedAbove, P.projective,
    ⟨asIso (DerivedCategory.Q.map P.α) ≪≫ e.symm⟩⟩

private lemma mappingCone_isStrictlyLE_and_projective
    {S : Type v} [Ring S] {L E : CochainComplex (ModuleCat.{v} S) ℤ} (f : L ⟶ E)
    (a b c : ℤ) [L.IsStrictlyLE a] [E.IsStrictlyLE b] (hac : a ≤ c + 1) (hbc : b ≤ c)
    (hL : ∀ i, Projective (L.X i)) (hE : ∀ i, Projective (E.X i)) :
    (CochainComplex.mappingCone f).IsStrictlyLE c ∧
      ∀ i, Projective ((CochainComplex.mappingCone f).X i) := by
  refine ⟨?_, fun i => ?_⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨CochainComplex.isZero_of_isStrictlyLE L a (i + 1) (by omega),
      CochainComplex.isZero_of_isStrictlyLE E b i (by omega)⟩
  · have := hL (i + 1)
    have := hE i
    exact Projective.of_iso
      (HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp)).symm inferInstance

/-- A finite free module is projective. -/
private lemma projective_of_finiteFree {S : Type v} [Ring S] {M : ModuleCat.{v} S}
    (h : Module.Finite S M ∧ Module.Free S M) : Projective M := by
  have := h.2
  exact ModuleCat.projective_of_free (Module.Free.chooseBasis S M)

/-- A finite free module is finitely presented. -/
private lemma finitePresentation_of_finiteFree {S : Type v} [CommRing S] {M : ModuleCat.{v} S}
    (h : Module.Finite S M ∧ Module.Free S M) : Module.FinitePresentation S M := by
  have := h.1
  have := h.2
  have : Module.Projective S M := Module.Projective.of_free
  exact Module.finitePresentation_of_projective _ _

/-- A zero module is finite and free. -/
private lemma finiteFree_of_isZero {S : Type v} [Ring S] {M : ModuleCat.{v} S} (h : IsZero M) :
    Module.Finite S M ∧ Module.Free S M := by
  have := ModuleCat.isZero_iff_subsingleton.mp h
  exact ⟨Module.Finite.of_finite, Module.Free.of_subsingleton S _⟩

set_option backward.isDefEq.respectTransparency false in
private lemma exists_projective_representative_finiteFree_ge
    {S : Type v} [CommRing S] (K : DerivedCategory (ModuleCat.{v} S)) (m : ℤ)
    (hK : IsPseudoCoherentFrom K m) :
    ∃ E : CochainComplex (ModuleCat.{v} S) ℤ,
      (∃ b, E.IsStrictlyLE b) ∧ (∀ i, Projective (E.X i)) ∧
      (∀ i, m ≤ i → Module.Finite S (E.X i) ∧ Module.Free S (E.X i)) ∧
      Nonempty (DerivedCategory.Q.obj E ≅ K) := by
  obtain ⟨F, hF, α, hiso, hepi⟩ := hK
  obtain ⟨C, β, γ, hT⟩ := distinguished_cocone_triangle α
  let T := Triangle.mk α β γ
  have : C.IsLE (m - 1) :=
    DerivedCategory.triangle_obj₃_isLE_of_approximation T hT m hiso hepi
  obtain ⟨P₀, hP₀, hproj, ⟨e₀⟩⟩ := exists_projective_representative_le C (m - 1)
  let P := P₀⟦(-1 : ℤ)⟧
  have hP : P.IsStrictlyLE m :=
    CochainComplex.isStrictlyLE_shift P₀ (m - 1) (-1) m (by omega)
  have hPproj (i : ℤ) : Projective (P.X i) := hproj (i - 1)
  have : P.IsKProjective := CochainComplex.isKProjective_of_projective P m
  let e : DerivedCategory.Q.obj P ≅ T.invRotate.obj₁ :=
    (DerivedCategory.Q.commShiftIso (-1)).app P₀ ≪≫ (shiftFunctor _ (-1)).mapIso e₀
  obtain ⟨f, hf⟩ := exists_chainMap_of_isKProjective P F (e.hom ≫ T.invRotate.mor₁)
  let U := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  have hU : U ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished f
  have hT' : T.invRotate ∈ distTriang _ := inv_rot_of_distTriang T hT
  have hsq : U.mor₁ ≫ 𝟙 _ = e.hom ≫ T.invRotate.mor₁ := (Category.comp_id _).trans hf
  obtain ⟨g, hg₁, hg₂⟩ := complete_distinguished_triangle_morphism U T.invRotate hU hT'
    e.hom (𝟙 _) hsq
  let φ := Triangle.homMk U T.invRotate e.hom (𝟙 _) g hsq hg₁ hg₂
  have hg : IsIso g := isIso₃_of_isIso₁₂ φ hU hT' (inferInstanceAs (IsIso e.hom))
    (inferInstanceAs (IsIso (𝟙 (DerivedCategory.Q.obj F))))
  let E := CochainComplex.mappingCone f
  obtain ⟨b, hb⟩ := hF.upperBound
  have hFproj (i : ℤ) : Projective (F.X i) := projective_of_finiteFree (hF.finiteFree i)
  have eX (i : ℤ) : E.X i ≅ (P.X (i + 1) ⊞ F.X i) :=
    HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp)
  obtain ⟨hEb, hEp⟩ := mappingCone_isStrictlyLE_and_projective f m b (max (m - 1) b)
    (by omega) (le_max_right _ _) hPproj hFproj
  refine ⟨E, ⟨_, hEb⟩, hEp, fun i hi => ?_, ⟨asIso g⟩⟩
  obtain ⟨_, _⟩ := finiteFree_of_isZero
    (CochainComplex.isZero_of_isStrictlyLE P m (i + 1) (by omega))
  have := (hF.finiteFree i).1
  have := (hF.finiteFree i).2
  let eL := ((eX i) ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
  exact ⟨Module.Finite.equiv eL.symm, Module.Free.of_equiv eL.symm⟩

private lemma homologyRange_tensorProductComparison_of_isPseudoCoherentFrom
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R)
    (K : D.{u, v, w} R) (m : ℤ) (hK : IsPseudoCoherentFrom K m)
    (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)) :
    (∀ i, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
      (tensorProductComparison T P K A Q))) ∧
    Epi ((DerivedCategory.homologyFunctor _ m).map (tensorProductComparison T P K A Q)) := by
  obtain ⟨E, ⟨b, hb⟩, hp, hf, ⟨e⟩⟩ := exists_projective_representative_finiteFree_ge K m hK
  have hflat (i : ℤ) : Module.Flat (SmallRing.{u, v, w} R) (E.X i) := by
    have := hp i
    infer_instance
  have hkflat : E.KFlat := kFlat_of_flat_of_isStrictlyLE E b
  apply (homologyRange_tensorProductComparison_iff_of_iso R T P e m A Q).mp
  apply homologyRange_tensorProductComparison_of_finite_terms R T P E hkflat m
  · exact fun i hi => finitePresentation_of_finiteFree (hf i hi.le)
  · exact (hf m le_rfl).1

private lemma mapHomologicalComplex_commShift
    {C D : Type*} [Category C] [Preadditive C] [Category D] [Preadditive D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G) :
    NatTrans.CommShift (α.mapHomologicalComplex (ComplexShape.up ℤ)) ℤ := by
  constructor
  intro n
  ext E i
  simp [NatTrans.mapHomologicalComplex, CochainComplex.shiftFunctor_map_f']

set_option backward.isDefEq.respectTransparency false in
private noncomputable def triangleMapOfNatTrans
    {C D : Type*} [Category C] [Category D] [HasShift C ℤ] [HasShift D ℤ]
    {F G : C ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]
    (α : F ⟶ G) [NatTrans.CommShift α ℤ] (T : Triangle C) :
    F.mapTriangle.obj T ⟶ G.mapTriangle.obj T :=
  Triangle.homMk _ _ (α.app _) (α.app _) (α.app _)
    (α.naturality _) (α.naturality _) (by
      change (F.map T.mor₃ ≫ (F.commShiftIso (1 : ℤ)).hom.app T.obj₁) ≫
        (α.app T.obj₁)⟦(1 : ℤ)⟧' =
          α.app T.obj₃ ≫ (G.map T.mor₃ ≫ (G.commShiftIso (1 : ℤ)).hom.app T.obj₁)
      simp only [Category.assoc, NatTrans.shift_app_comm α (1 : ℤ) T.obj₁,
        NatTrans.naturality_assoc])

private lemma map_mappingCone_triangle_distinguished
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] {L E : CochainComplex C ℤ} (f : L ⟶ E) :
    DerivedCategory.Q.mapTriangle.obj
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).mapTriangle.obj
        (CochainComplex.mappingCone.triangle f)) ∈ distTriang _ :=
  (distinguished_iff_of_iso
    (DerivedCategory.Q.mapTriangle.mapIso (CochainComplex.mappingCone.mapTriangleIso f F))).mpr
      (DerivedCategory.mappingCone_triangle_distinguished _)

set_option backward.isDefEq.respectTransparency false in
private lemma homologyRange_mapNatTrans_mappingCone
    {S : Type v} [Ring S] {F G : ModuleCat.{v} S ⥤ ModuleCat.{v} S}
    [F.Additive] [G.Additive] (α : F ⟶ G)
    {L E : CochainComplex (ModuleCat.{v} S) ℤ} (f : L ⟶ E) (m : ℤ)
    (hL : ∀ i, IsIso (HomologicalComplex.homologyMap
      ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app L) i))
    (hE : (∀ i, m < i → IsIso (HomologicalComplex.homologyMap
      ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app E) i)) ∧
      Epi (HomologicalComplex.homologyMap
        ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app E) m)) :
    (∀ i, m < i → IsIso (HomologicalComplex.homologyMap
      ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app (CochainComplex.mappingCone f)) i)) ∧
      Epi (HomologicalComplex.homologyMap
        ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app (CochainComplex.mappingCone f)) m) := by
  let a := α.mapHomologicalComplex (ComplexShape.up ℤ)
  let := mapHomologicalComplex_commShift α
  let φ := DerivedCategory.Q.mapTriangle.map
    (triangleMapOfNatTrans a (CochainComplex.mappingCone.triangle f))
  have h₁ := map_mappingCone_triangle_distinguished F f
  have h₂ := map_mappingCone_triangle_distinguished G f
  have hL' (i : ℤ) : IsIso ((DerivedCategory.homologyFunctor _ i).map φ.hom₁) :=
    (isIso_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors _ i) (a.app L)).mpr (hL i)
  have hE' (i : ℤ) (hi : m < i) :
      IsIso ((DerivedCategory.homologyFunctor _ i).map φ.hom₂) :=
    (isIso_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors _ i) (a.app E)).mpr (hE.1 i hi)
  constructor
  · intro i hi
    apply (isIso_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors _ i)
      (a.app (CochainComplex.mappingCone f))).mp
    apply PseudoCoherence.isIso_homology_of_triangleMorphism h₁ h₂ φ i
    · exact IsIso.epi_of_iso _
    · exact hE' i hi
    · exact hL' (i + 1)
    · have := hE' (i + 1) (by omega)
      exact IsIso.mono_of_iso _
  · apply (epi_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors _ m)
      (a.app (CochainComplex.mappingCone f))).mp
    apply PseudoCoherence.epi_homology_of_triangleMorphism h₁ h₂ φ m
    · exact (epi_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors _ m)
        (a.app E)).mpr hE.2
    · exact IsIso.epi_of_iso _
    · have := hE' (m + 1) (by omega)
      exact IsIso.mono_of_iso _

private lemma quasiIso_map_of_isKProjective
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    (F : C ⥤ D) [F.Additive] {K L : CochainComplex C ℤ}
    [K.IsKProjective] [L.IsKProjective] (f : K ⟶ L) [QuasiIso f] :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have hf : HomologicalComplex.homotopyEquivalences C (ComplexShape.up ℤ) f :=
    (CochainComplex.IsKProjective.quasiIso_iff f).1 inferInstance
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms] at hf
  have : IsIso ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f) := hf
  apply homotopyEquivalences_le_quasiIso _ _ _
  rw [← HomotopyCategory.inverseImage_quotient_isomorphisms]
  exact (F.mapHomotopyCategory (ComplexShape.up ℤ)).map_isIso
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map f)

private lemma homology_mapNatTrans_iff_of_quasiIso
    {C D : Type*} [Category C] [Abelian C] [Category D] [Abelian D]
    {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ⟶ G)
    {K L : CochainComplex C ℤ} [K.IsKProjective] [L.IsKProjective]
    (f : K ⟶ L) [QuasiIso f] (i : ℤ) :
    (IsIso (HomologicalComplex.homologyMap
      ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app K) i) ↔
      IsIso (HomologicalComplex.homologyMap
        ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app L) i)) ∧
    (Epi (HomologicalComplex.homologyMap
      ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app K) i) ↔
      Epi (HomologicalComplex.homologyMap
        ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app L) i)) := by
  have := quasiIso_map_of_isKProjective F f
  have := quasiIso_map_of_isKProjective G f
  let H := HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) i
  have hF : IsIso (H.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
    change IsIso (HomologicalComplex.homologyMap _ i)
    infer_instance
  have hG : IsIso (H.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f)) := by
    change IsIso (HomologicalComplex.homologyMap _ i)
    infer_instance
  have h := congrArg H.map ((α.mapHomologicalComplex (ComplexShape.up ℤ)).naturality f)
  simp only [Functor.map_comp] at h
  change (IsIso (H.map ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app K)) ↔
    IsIso (H.map ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app L))) ∧
    (Epi (H.map ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app K)) ↔
      Epi (H.map ((α.mapHomologicalComplex (ComplexShape.up ℤ)).app L)))
  constructor
  · rw [← isIso_comp_right_iff _ (H.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f)),
      ← h, isIso_comp_left_iff]
  · rw [← epi_comp_iff_of_isIso _ (H.map ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map f)),
      ← h, epi_comp_iff_of_epi]

private lemma productFunctor_additive
    (S : Type v) [Ring S] (A : Type v) :
    (piDiscreteFunctor (fun _ : A => 𝟭 (ModuleCat.{v} S)) ⋙ lim).Additive where
  map_add {X Y} f g := by
    change Limits.Pi.map (fun _ : A => f + g) =
      Limits.Pi.map (fun _ : A => f) + Limits.Pi.map (fun _ : A => g)
    apply Pi.hom_ext
    intro a
    simp [Preadditive.add_comp, Preadditive.comp_add]

attribute [local instance] productFunctor_additive

abbrev RingPowerHomologyRange
    {S : Type v} [CommRing S] (E : CochainComplex (ModuleCat.{v} S) ℤ) (m : ℤ) : Prop :=
  ∀ A : Type v,
    (∀ i, m < i → IsIso (HomologicalComplex.homologyMap
      (((moduleTensorRingPowerComparison S A).mapHomologicalComplex
        (ComplexShape.up ℤ)).app E) i)) ∧
    Epi (HomologicalComplex.homologyMap
      (((moduleTensorRingPowerComparison S A).mapHomologicalComplex
        (ComplexShape.up ℤ)).app E) m)

private lemma isIso_homology_ringPowerComparison_of_finiteFree
    {S : Type v} [CommRing S] (E : CochainComplex (ModuleCat.{v} S) ℤ)
    (hE : ∀ i, Module.Finite S (E.X i) ∧ Module.Free S (E.X i)) (A : Type v) (i : ℤ) :
    IsIso (HomologicalComplex.homologyMap
      (((moduleTensorRingPowerComparison S A).mapHomologicalComplex
        (ComplexShape.up ℤ)).app E) i) := by
  have hf (j : ℤ) : Module.FinitePresentation S (E.X j) := finitePresentation_of_finiteFree (hE j)
  have := preservesProducts_tensorWithCochainComplex S E A
  exact (isIso_homology_moduleTensorRingPowerComparison_iff S A E i).mpr inferInstance

private lemma isPseudoCoherentFrom_of_isLE
    {S : Type v} [Ring S] (K : DerivedCategory (ModuleCat.{v} S)) (m : ℤ)
    [K.IsLE (m - 1)] : IsPseudoCoherentFrom K m := by
  refine ⟨0, ⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩, ?_⟩, 0, ?_, ?_⟩
  · exact fun i => finiteFree_of_isZero
      ((HomologicalComplex.eval _ (ComplexShape.up ℤ) i).map_isZero (isZero_zero _))
  · intro i hi
    exact ((DerivedCategory.homologyFunctor _ i).map_isZero
      (DerivedCategory.Q.map_isZero (isZero_zero _))).isIso
        (DerivedCategory.isZero_of_isLE K (m - 1) i (by omega)) _
  · exact (DerivedCategory.isZero_of_isLE K (m - 1) m (by omega)).epi _

private lemma exists_single_finiteFree_top_cover
    {S : Type v} [Ring S] (E : CochainComplex (ModuleCat.{v} S) ℤ) (b : ℤ)
    [Module.Finite S (E.homology b)] :
    ∃ L : CochainComplex (ModuleCat.{v} S) ℤ,
      IsBoundedFiniteFree L ∧ L.IsStrictlyLE b ∧
      ∃ f : L ⟶ E, Epi (HomologicalComplex.homologyMap f b) := by
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' S (E.homology b)
  let P := ModuleCat.of S (Fin n → S)
  let p' : P ⟶ E.homology b := ModuleCat.ofHom p
  let : Epi p' := (ModuleCat.epi_iff_surjective _).mpr hp
  obtain ⟨f, hf⟩ := exists_hom_from_single_of_projective E b P p'
  refine ⟨_, ⟨⟨b, inferInstance⟩, ⟨b, inferInstance⟩, ?_⟩, inferInstance, f, hf⟩
  intro i
  by_cases hi : i = b
  · subst i
    let e := (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) b P).toLinearEquiv
    exact ⟨Module.Finite.equiv e.symm, Module.Free.of_equiv e.symm⟩
  · exact finiteFree_of_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) b P i hi)

private lemma finite_homology_of_ringPowerHomologyRange
    {S : Type v} [CommRing S] {E : CochainComplex (ModuleCat.{v} S) ℤ} {m b : ℤ}
    [E.IsStrictlyLE b] (hmb : m ≤ b) (hE : RingPowerHomologyRange E m) :
    Module.Finite S (E.homology b) := by
  apply finite_homology_of_epi_tensorRingPowerComparison_of_zero_d S E b
    ((CochainComplex.isZero_of_isStrictlyLE E b (b + 1) (by omega)).eq_of_tgt _ _)
  intro A
  change Epi (HomologicalComplex.homologyMap
    (((moduleTensorRingPowerComparison S A).mapHomologicalComplex
      (ComplexShape.up ℤ)).app E) b)
  rcases hmb.eq_or_lt with rfl | hlt
  · exact (hE A).2
  · have := (hE A).1 b hlt
    exact IsIso.epi_of_iso _

private lemma ringPowerHomologyRange_of_quasiIso
    {S : Type v} [CommRing S] {D C : CochainComplex (ModuleCat.{v} S) ℤ}
    [D.IsKProjective] [C.IsKProjective] (q : D ⟶ C) [QuasiIso q] {m : ℤ}
    (hC : RingPowerHomologyRange C m) : RingPowerHomologyRange D m := fun A =>
  ⟨fun i hi => (homology_mapNatTrans_iff_of_quasiIso
    (moduleTensorRingPowerComparison S A) q i).1.mpr ((hC A).1 i hi),
    (homology_mapNatTrans_iff_of_quasiIso
      (moduleTensorRingPowerComparison S A) q m).2.mpr (hC A).2⟩

set_option backward.isDefEq.respectTransparency false in
lemma isPseudoCoherentFrom_of_ringPowerHomologyRange_aux
    {S : Type v} [CommRing S] (m : ℤ) (n : ℕ)
    (E : CochainComplex (ModuleCat.{v} S) ℤ)
    (hb : E.IsStrictlyLE (m + n - 1)) (hp : ∀ i, Projective (E.X i))
    (hE : RingPowerHomologyRange E m) : IsPseudoCoherentFrom (DerivedCategory.Q.obj E) m := by
  induction n generalizing E with
  | zero =>
    have : E.IsStrictlyLE (m - 1) := by simpa using hb
    exact isPseudoCoherentFrom_of_isLE _ m
  | succ n ih =>
    let b : ℤ := m + n
    have hEb : E.IsStrictlyLE b := by
      convert hb using 1
      dsimp [b]
      omega
    have hEk : E.IsKProjective := CochainComplex.isKProjective_of_projective E b
    have hfin : Module.Finite S (E.homology b) :=
      finite_homology_of_ringPowerHomologyRange (by omega) hE
    obtain ⟨L, hL, hLb, f, hf⟩ := exists_single_finiteFree_top_cover E b
    have hLp (i : ℤ) : Projective (L.X i) := projective_of_finiteFree (hL.finiteFree i)
    let C := CochainComplex.mappingCone f
    obtain ⟨hCb, hCp⟩ : C.IsStrictlyLE b ∧ ∀ i, Projective (C.X i) :=
      mappingCone_isStrictlyLE_and_projective f b b b (by omega) le_rfl hLp hp
    have hCk : C.IsKProjective := CochainComplex.isKProjective_of_projective C b
    let T := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
    have hT : T ∈ distTriang _ := DerivedCategory.mappingCone_triangle_distinguished f
    have hCcoh : (DerivedCategory.Q.obj C).IsLE (b - 1) := by
      apply DerivedCategory.triangle_obj₃_isLE_of_approximation T hT b
      · intro i hi
        exact (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj L) b i hi).isIso
          (DerivedCategory.isZero_of_isLE (DerivedCategory.Q.obj E) b i hi) _
      · exact (epi_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors _ b) f).mpr hf
    have hC : RingPowerHomologyRange C m := by
      intro A
      exact homologyRange_mapNatTrans_mappingCone (moduleTensorRingPowerComparison S A) f m
        (fun i => isIso_homology_ringPowerComparison_of_finiteFree L hL.finiteFree A i) (hE A)
    obtain ⟨D, hDb, hDp, ⟨e⟩⟩ := exists_projective_representative_le
      (DerivedCategory.Q.obj C) (b - 1)
    have hDk : D.IsKProjective := CochainComplex.isKProjective_of_projective D (b - 1)
    obtain ⟨q, hq⟩ := exists_chainMap_of_isKProjective D C e.hom
    have hqiso : QuasiIso q := (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).mp (by
      rw [hq]
      infer_instance)
    have hDpc := ih D hDb hDp (ringPowerHomologyRange_of_quasiIso q hC)
    have hCpc : IsPseudoCoherentFrom (DerivedCategory.Q.obj C) m :=
      IsPseudoCoherentFrom.ofIso hDpc e
    have hLpc : IsPseudoCoherentFrom (DerivedCategory.Q.obj L) m :=
      (pseudoCoherent_iff_all _).mp
        ⟨L, ⟨hL.upperBound, hL.finiteFree⟩, ⟨Iso.refl _⟩⟩ m
    exact PseudoCoherence.isPseudoCoherent_of_distinguished_two m T hT hLpc hCpc

private lemma isPseudoCoherentFrom_of_homologyRange_tensorRingPowerComparison
    (R : Type u) [CommRing R] [Small.{max v w} R]
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R)
    (K : DerivedCategory.Minus (ModuleCat.{max v w} (SmallRing.{u, v, w} R))) (m : ℤ)
    (hK : ∀ A : Type (max v w),
      (∀ i, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
        (tensorRingPowerComparison T P K.obj A))) ∧
      Epi ((DerivedCategory.homologyFunctor _ m).map
        (tensorRingPowerComparison T P K.obj A))) : IsPseudoCoherentFrom K.obj m := by
  obtain ⟨b, hb⟩ := K.property
  obtain ⟨E, hEb, hEp, ⟨e⟩⟩ := exists_projective_representative_le K.obj b
  have hEp' (i : ℤ) : Projective (E.X i) := hEp i
  have hEf (i : ℤ) : Module.Flat (SmallRing.{u, v, w} R) (E.X i) := inferInstance
  have hflat : E.KFlat := kFlat_of_flat_of_isStrictlyLE E b
  have hE : RingPowerHomologyRange E m := by
    intro A
    have hβ := (homologyRange_tensorRingPowerComparison_iff R T P K.obj m A).mp (hK A)
    have hβE := (homologyRange_tensorProductComparison_iff_of_iso R T P e m A
      (fun _ => ModuleCat.of (SmallRing.{u, v, w} R) (SmallRing.{u, v, w} R))).mpr hβ
    have hc (i : ℤ) := homology_tensorProductComparison_iff_of_kFlat R T P E hflat A
      (fun _ => ModuleCat.of (SmallRing.{u, v, w} R) (SmallRing.{u, v, w} R)) i
    exact ⟨fun i hi => (isIso_homology_moduleTensorRingPowerComparison_iff _ A E i).mpr
      ((hc i).1.mp (hβE.1 i hi)),
      (epi_homology_moduleTensorRingPowerComparison_iff _ A E m).mpr ((hc m).2.mp hβE.2)⟩
  let n := (b - m + 1).toNat
  have hbound : E.IsStrictlyLE (m + n - 1) := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact CochainComplex.isZero_of_isStrictlyLE E b i (by dsimp [n] at hi; omega)
  exact IsPseudoCoherentFrom.ofIso
    (isPseudoCoherentFrom_of_ringPowerHomologyRange_aux m n E hbound hEp hE) e


/-! ### The characterization -/

variable {R : Type u} [CommRing R] [Small.{max v w} R]

/-- **Stacks 0CYB.** Pseudo-coherence of a bounded-above complex is equivalent to derived
tensor product commuting with arbitrary products; the degreewise variants characterize
`m`-pseudo-coherence. -/
@[stacks 0CYB]
theorem pseudoCoherent_iff_derivedTensor_preserves_products
    (T : DerivedTensorProduct.{u, v, w} R) (P : DerivedProducts.{u, v, w} R)
    (K : DerivedCategory.Minus (ModuleCat.{max v w} (SmallRing.{u, v, w} R))) (m : ℤ) :
    List.TFAE [
      IsPseudoCoherent K.obj,
      ∀ (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
        IsIso (tensorProductComparison T P K.obj A Q),
      ∀ (A : Type (max v w)) (Q : ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
        IsIso (tensorPowerComparison T P K.obj A Q),
      ∀ A : Type (max v w), IsIso (tensorRingPowerComparison T P K.obj A)] ∧
    List.TFAE [
      IsPseudoCoherentFrom K.obj m,
      ∀ (A : Type (max v w)) (Q : A → ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
        (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
          (tensorProductComparison T P K.obj A Q))) ∧
        Epi ((DerivedCategory.homologyFunctor _ m).map
          (tensorProductComparison T P K.obj A Q)),
      ∀ (A : Type (max v w)) (Q : ModuleCat.{max v w} (SmallRing.{u, v, w} R)),
        (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
          (tensorPowerComparison T P K.obj A Q))) ∧
        Epi ((DerivedCategory.homologyFunctor _ m).map
          (tensorPowerComparison T P K.obj A Q)),
      ∀ A : Type (max v w),
        (∀ i : ℤ, m < i → IsIso ((DerivedCategory.homologyFunctor _ i).map
          (tensorRingPowerComparison T P K.obj A))) ∧
        Epi ((DerivedCategory.homologyFunctor _ m).map
          (tensorRingPowerComparison T P K.obj A))] := by
  apply solution_of_core R T P K m
  · exact isIso_tensorProductComparison_of_isPseudoCoherent R T P K.obj
  · intro h
    apply (pseudoCoherent_iff_all K.obj).mpr
    intro n
    apply isPseudoCoherentFrom_of_homologyRange_tensorRingPowerComparison R T P K n
    intro A
    have := h A
    exact ⟨fun i _ => inferInstance, inferInstance⟩
  · exact homologyRange_tensorProductComparison_of_isPseudoCoherentFrom R T P K.obj m
  · exact isPseudoCoherentFrom_of_homologyRange_tensorRingPowerComparison R T P K m

end StacksDraft.PseudoCoherence
