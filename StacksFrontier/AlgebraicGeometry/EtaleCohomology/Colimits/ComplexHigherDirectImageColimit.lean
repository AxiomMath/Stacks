module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplitSequences
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.ComplexHigherDirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitHigherDirectImageColimitTheorem
public import StacksFrontier.CategoryTheory.Limits.SystemColimitExact

/-!
# Higher direct images of a colimit of bounded below complexes along a limit of morphisms

Let `I` be a directed set, let `g_i : X_i ⟶ S_i` be an inverse system of quasi-compact and
quasi-separated morphisms of schemes over `I` with affine transition morphisms `f_{i'i}`,
`h_{i'i}`, and let `g : X ⟶ S` be its limit, with projections `f_i : X ⟶ X_i`, `h_i : S ⟶ S_i`.
Let `(ℱ_i^•, φ_{i'i})` be a system of complexes of abelian sheaves on the `X_{i, étale}` with
`ℱ_i^n = 0` for `n < a`, `a` independent of `i`, and `ℱ^• = colim f_i^{-1}ℱ_i^•`. Then

`R^pg_*(ℱ^•) = colim_i h_i^{-1}R^pg_{i, *}ℱ_i^•` for all `p ∈ ℤ` ([Stacks, Tag 0GIV]).

Here `R^pg_{i, *}ℱ_i^•` is the degree-`p` cohomology sheaf of the total right derived direct image
of the class of `ℱ_i^•` in `D^+(X_{i, étale})`, and the maps are those of
`Stacks.EtaleCohomology.LimitHigherDirectImage.complexHigherDirectImageSystem` and
`Stacks.EtaleCohomology.LimitHigherDirectImage.complexLeg`: the derived base change maps of the
transition and projection squares followed by `R^pg_{i', *}φ_{i'i}` and `R^pg_*ι_i`.

## Main results

* `Stacks.EtaleCohomology.LimitHigherDirectImage.epi_complexColimitDesc_of_shortExact`,
  `Stacks.EtaleCohomology.LimitHigherDirectImage.mono_complexColimitDesc_of_shortExact`: the two
  halves of the five lemma for the colimit comparison, along a degreewise split short exact
  sequence of systems of complexes.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.isComplexHigherDirectImageColimit_single`: the
  colimit assertion for a system of sheaves placed in one degree, which is Stacks 0EYM after a
  shift.
* `Stacks.EtaleCohomology.LimitHigherDirectImage.complexHigherDirectImageColimit`:
  [Stacks, Tag 0GIV].

## Implementation notes

The source proves 0GIV from 0EYM with the two spectral sequences of the complexes and remarks
that the stupid truncations give an alternative argument; the latter is the one used here. For a
fixed degree `p` one shows, by descending induction on `n`, that the comparison map from the
colimit of the `h_i^{-1}R^qg_{i, *}σ^{≥n}ℱ_i^•` to `R^qg_*σ^{≥n}ℱ^•` is an epimorphism for
`q ≤ p` and a monomorphism for `q ≤ p + 1`. For `n > p + 1` all these sheaves vanish; the step
from `n + 1` to `n` is the five lemma (`CategoryTheory.Limits.SystemLift.epi_colimitDesc_of_exact`,
`CategoryTheory.Limits.SystemLift.mono_colimitDesc_of_exact`, which need colimits over a directed
set of abelian sheaves to be exact) applied to the long exact sequences of the derived direct
images of the degreewise split sequences `0 ⟶ σ^{≥n+1} ⟶ σ^{≥n} ⟶ ℱ^n[-n] ⟶ 0`. The connecting
morphisms of those sequences are compatible with the derived base change maps by
`derivedBaseChangeHomologyMap_smallEtaleComplexPullbackComparison_homologySequenceδ`.
The third terms are sheaves placed in one degree; they are moved to degree zero along the
degreewise split sequences `0 ⟶ G[-n] ⟶ (G --𝟙--> G) ⟶ G[-(n-1)] ⟶ 0` with contractible middle
term, and in degree zero they are Stacks 0EYM.

All complexes are placed in `D^+` with one common lower bound `b`; for a system of sheaves the
bound is `min a 0`, so that every shift of it stays above the bound.

## References

* [Stacks Project, Tag 0GIV](https://stacks.math.columbia.edu/tag/0GIV)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry AlgebraicGeometry.Scheme
open CochainComplex (plusDerivedObj)

universe u

namespace CategoryTheory.Limits.IsSystemColimit

variable {𝒞 : Type*} [Category* 𝒞] {K : Type*} [Quiver K] {A A' : K → 𝒞}
  {T : ∀ {i j : K}, (i ⟶ j) → (A j ⟶ A i)} {T' : ∀ {i j : K}, (i ⟶ j) → (A' j ⟶ A' i)}
  {B B' : 𝒞} {ψ : ∀ i, A i ⟶ B} {ψ' : ∀ i, A' i ⟶ B'}

/-- **The colimit of a system is invariant under isomorphism of systems.** -/
theorem iff_of_isoSystem (θ : ∀ i, A i ≅ A' i) (e : B ≅ B')
    (hT : ∀ {i j : K} (a : i ⟶ j), T a ≫ (θ i).hom = (θ j).hom ≫ T' a)
    (hψ : ∀ i, ψ i ≫ e.hom = (θ i).hom ≫ ψ' i) :
    IsSystemColimit A T B ψ ↔ IsSystemColimit A' T' B' ψ' :=
  ⟨fun h => h.of_isoSystem θ e hT hψ, fun h => h.of_isoSystem (fun i => (θ i).symm) e.symm
    (fun a => by
      rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hT a,
        Iso.inv_hom_id_assoc])
    (fun i => by
      rw [Iso.symm_hom, Iso.symm_hom, Iso.comp_inv_eq, Category.assoc, hψ i,
        Iso.inv_hom_id_assoc])⟩

/-- **A system of zero objects has the zero object as colimit.** -/
theorem of_isZero [HasZeroMorphisms 𝒞] (hA : ∀ i, IsZero (A i)) (hB : IsZero B) :
    IsSystemColimit A T B ψ := fun G τ _ =>
  ⟨0, fun i => (hA i).eq_of_src _ _, fun χ _ => hB.eq_of_src _ _⟩

end CategoryTheory.Limits.IsSystemColimit

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

attribute [local instance] HasDerivedCategory.standard Functor.commShiftRightDerivedFunctorPlus
  Functor.isTriangulated_rightDerivedFunctorPlus

/-! ### Maps of complexes in `D^+` -/

/-- The map of `D^+(X_étale)` induced by a map of complexes vanishing in degrees `< a`. -/
abbrev plusComplexMap {X : Scheme.{u}} (a : ℤ)
    {K L : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ} [K.IsStrictlyGE a]
    [L.IsStrictlyGE a] (φ : K ⟶ L) : plusDerivedObj a K ⟶ plusDerivedObj a L :=
  DerivedCategory.Plus.Qh.map (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map φ) :
    CochainComplex.plusHomotopyObj a K ⟶ CochainComplex.plusHomotopyObj a L)

/-- **The comparison `smallEtaleComplexPullbackComparison` is natural in the two complexes.** -/
theorem smallEtaleComplexPullbackComparison_naturality (a : ℤ) {X Y : Scheme.{u}} (f : X ⟶ Y)
    {F F' : CochainComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1}) ℤ} [F.IsStrictlyGE a]
    [F'.IsStrictlyGE a] {G G' : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ}
    [G.IsStrictlyGE a] [G'.IsStrictlyGE a] (α : F ⟶ F') (β : G ⟶ G')
    (ι : ((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F ⟶ G)
    (ι' : ((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).obj F' ⟶ G')
    (h : ((smallEtalePullbackAb f).mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ ι' =
      ι ≫ β) :
    (derivedPullbackAb f).map (plusComplexMap a α) ≫
        smallEtaleComplexPullbackComparison a f F' G' ι' =
      smallEtaleComplexPullbackComparison a f F G ι ≫ plusComplexMap a β := by
  let : IsIso (smallEtalePullbackAb f).rightDerivedFunctorPlusUnith :=
    (smallEtalePullbackAb f).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  rw [smallEtaleComplexPullbackComparison_eq, smallEtaleComplexPullbackComparison_eq]
  have hnat := (asIso (smallEtalePullbackAb f).rightDerivedFunctorPlusUnith).inv.naturality
    (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map α) :
      CochainComplex.plusHomotopyObj a F ⟶ CochainComplex.plusHomotopyObj a F')
  simp only [Functor.comp_map] at hnat
  have hq : (smallEtalePullbackAb f).mapHomotopyCategoryPlus.map
        (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map α) :
          CochainComplex.plusHomotopyObj a F ⟶ CochainComplex.plusHomotopyObj a F') ≫
      (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map ι') :
        (smallEtalePullbackAb f).mapHomotopyCategoryPlus.obj
            (CochainComplex.plusHomotopyObj a F') ⟶ CochainComplex.plusHomotopyObj a G') =
      (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map ι) :
          (smallEtalePullbackAb f).mapHomotopyCategoryPlus.obj
            (CochainComplex.plusHomotopyObj a F) ⟶ CochainComplex.plusHomotopyObj a G) ≫
        (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map β) :
          CochainComplex.plusHomotopyObj a G ⟶ CochainComplex.plusHomotopyObj a G') := by
    ext
    exact ((HomotopyCategory.quotient _ _).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient _ _).map h).trans
        ((HomotopyCategory.quotient _ _).map_comp _ _))
  rw [reassoc_of% hnat, ← Functor.map_comp, hq, Functor.map_comp, Category.assoc]

/-- **Trivial vanishing**: the derived direct image of a complex vanishing in degrees `< n` has no
cohomology in degrees `< n`. -/
theorem isZero_homologyAb_derivedPushforwardAb {X S : Scheme.{u}} (g : X ⟶ S) (b n q : ℤ)
    (K : CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ) [K.IsStrictlyGE b]
    [K.IsStrictlyGE n] (hq : q < n) :
    IsZero ((homologyAb S q).obj ((derivedPushforwardAb g).obj (plusDerivedObj b K))) := by
  have : (plusDerivedObj b K).IsGE n := by
    rw [← DerivedCategory.Plus.isGE_ι_obj_iff]
    exact DerivedCategory.TStructure.t.isGE_of_iso
      ((DerivedCategory.quotientCompQhIso _).symm.app K) n
  have := Functor.isGE_rightDerivedFunctorPlus_obj (smallEtalePushforwardAb g)
    (plusDerivedObj b K) n
  exact DerivedCategory.Plus.isZero_homology_of_isGE _ n q hq

/-! ### Maps of systems of complexes -/

section Morphism

variable {I : Type u} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS) (q b : ℤ)
  {F F' : EtaleComplexSystem DX} [∀ i, (F.obj i).IsStrictlyGE b] [∀ i, (F'.obj i).IsStrictlyGE b]
  (φ : ∀ i, F.obj i ⟶ F'.obj i)

/-- The map `R^qg_{i, *}ℱ_i^• ⟶ R^qg_{i, *}ℱ'^•_i` induced by a map of complexes. -/
abbrev complexHigherDirectImageMap (i : Iᵒᵖ) :
    (complexHigherDirectImageSystem γ q b F).obj i ⟶
      (complexHigherDirectImageSystem γ q b F').obj i :=
  (homologyAb (DS.obj i) q).map ((derivedPushforwardAb (γ.app i)).map (plusComplexMap b (φ i)))

variable {φ} (hφ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
  ((systemPullback DX Ab.{u + 1} a).mapHomologicalComplex _).map (φ j) ≫ F'.map a =
    F.map a ≫ φ i)

include hφ in
/-- **A map of systems of complexes induces a map of the systems of higher direct images.** -/
theorem complexHigherDirectImageMap_comm {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback DS Ab.{u + 1} a).map (complexHigherDirectImageMap γ q b φ j) ≫
        (complexHigherDirectImageSystem γ q b F').map a =
      (complexHigherDirectImageSystem γ q b F).map a ≫ complexHigherDirectImageMap γ q b φ i :=
  derivedTransitionMap_naturality γ q a _ _ _ _
    (smallEtaleComplexPullbackComparison_naturality b (DX.map a) (φ j) (φ i) (F.map a) (F'.map a)
      (hφ a))

include hφ in
/-- The maps of the pulled back diagrams induced by a map of systems of complexes. -/
theorem pullbackDiagramMap_comp_complexHigherDirectImageMap (cS : Cone DS) {i j : Iᵒᵖ}
    (a : i ⟶ j) :
    (complexHigherDirectImageSystem γ q b F).pullbackDiagramMap cS (i := i) (j := j) a ≫
        (smallEtalePullbackAb (cS.π.app i)).map (complexHigherDirectImageMap γ q b φ i) =
      (smallEtalePullbackAb (cS.π.app j)).map (complexHigherDirectImageMap γ q b φ j) ≫
        (complexHigherDirectImageSystem γ q b F').pullbackDiagramMap cS (i := i) (j := j) a :=
  pullbackDiagramMap_comp_map (fun i => complexHigherDirectImageMap γ q b φ i)
    (fun a => complexHigherDirectImageMap_comm γ q b hφ a) a

variable (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)
  {𝓕 𝓕' : CochainComplex (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) ℤ} [𝓕.IsStrictlyGE b]
  [𝓕'.IsStrictlyGE b]
  (ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕)
  (ι' : ∀ i : Iᵒᵖ,
    ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).obj (F'.obj i) ⟶ 𝓕')
  {β : 𝓕 ⟶ 𝓕'}
  (hβ : ∀ i, ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).map (φ i) ≫ ι' i =
    ι i ≫ β)

include hβ in
/-- **The cocone maps commute with a map of systems of complexes.** -/
theorem complexLeg_comp_map (i : Iᵒᵖ) :
    complexLeg γ q b F cX cS hcS 𝓕 ι i ≫
        (homologyAb cS.pt q).map ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).map
          (plusComplexMap b β)) =
      (smallEtalePullbackAb (cS.π.app i)).map (complexHigherDirectImageMap γ q b φ i) ≫
        complexLeg γ q b F' cX cS hcS 𝓕' ι' i :=
  (derivedProjectionMap_naturality γ cX cS hcS q i _ _ _ _
    (smallEtaleComplexPullbackComparison_naturality b (cX.π.app i) (φ i) β (ι i) (ι' i)
      (hβ i))).symm

end Morphism

/-- Abelian sheaves on a small étale site have colimits of the shape of the systems over a
preordered set. -/
theorem hasColimitsOfShape_systemLift_sheaf {I : Type u} [Preorder I] (X : Scheme.{u}) :
    HasColimitsOfShape (SystemLift I) (Sheaf (smallEtaleTopology X) Ab.{u + 1}) :=
  hasColimitsOfShape_sheaf_smallEtaleTopology.{u, u + 1} X _

attribute [local instance] hasColimitsOfShape_systemLift_sheaf

/-- **The comparison map from the colimit of the pulled back higher direct images** of a system
of complexes to the higher direct image of its colimit. -/
abbrev complexColimitDesc {I : Type u} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)
    (q b : ℤ) {cX : Cone DX} (cS : Cone DS) (hcS : IsLimit cS) (F : EtaleComplexSystem DX)
    [∀ i, (F.obj i).IsStrictlyGE b]
    (𝓕 : CochainComplex (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) ℤ) [𝓕.IsStrictlyGE b]
    (ι : ∀ i : Iᵒᵖ, ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).obj (F.obj i) ⟶ 𝓕)
    (hι : F.IsPullbackCocone cX ι) :
    colimit (SystemLift.functor
        (fun i => (smallEtalePullbackAb (cS.π.app i)).obj
          ((complexHigherDirectImageSystem γ q b F).obj i))
        (fun {i j} a => (complexHigherDirectImageSystem γ q b F).pullbackDiagramMap cS
          (i := i) (j := j) a)
        (fun a c => (complexHigherDirectImageSystem γ q b F).pullbackDiagramMap_comp cS a c)) ⟶
      (homologyAb cS.pt q).obj
        ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).obj (plusDerivedObj b 𝓕)) :=
  SystemLift.colimitDesc
    (fun a c => (complexHigherDirectImageSystem γ q b F).pullbackDiagramMap_comp cS a c)
    (complexLeg γ q b F cX cS hcS 𝓕 ι) (fun a => complexLeg_cocone γ q b F cX cS hcS 𝓕 ι hι a)

/-! ### Degreewise split short exact sequences of systems of complexes -/

section ShortExact

variable {I : Type u} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS) (b : ℤ)
  {F₁ F₂ F₃ : EtaleComplexSystem DX} [∀ i, (F₁.obj i).IsStrictlyGE b]
  [∀ i, (F₂.obj i).IsStrictlyGE b] [∀ i, (F₃.obj i).IsStrictlyGE b]
  {φ₁₂ : ∀ i, F₁.obj i ⟶ F₂.obj i} {φ₂₃ : ∀ i, F₂.obj i ⟶ F₃.obj i}
  (hφ₁₂ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    ((systemPullback DX Ab.{u + 1} a).mapHomologicalComplex _).map (φ₁₂ j) ≫ F₂.map a =
      F₁.map a ≫ φ₁₂ i)
  (hφ₂₃ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
    ((systemPullback DX Ab.{u + 1} a).mapHomologicalComplex _).map (φ₂₃ j) ≫ F₃.map a =
      F₂.map a ≫ φ₂₃ i)
  (w : ∀ i, φ₁₂ i ≫ φ₂₃ i = 0)
  (σ : ∀ i n, ((ShortComplex.mk (φ₁₂ i) (φ₂₃ i) (w i)).map
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).Splitting)

/-- The morphism of short complexes formed by the transition maps of three systems of complexes
related by maps of systems. -/
@[simps]
def shortComplexTransition {i j : Iᵒᵖ} (a : i ⟶ j) :
    (ShortComplex.mk (φ₁₂ j) (φ₂₃ j) (w j)).map
        ((systemPullback DX Ab.{u + 1} a).mapHomologicalComplex _) ⟶
      ShortComplex.mk (φ₁₂ i) (φ₂₃ i) (w i) where
  τ₁ := F₁.map a
  τ₂ := F₂.map a
  τ₃ := F₃.map a
  comm₁₂ := (hφ₁₂ a).symm
  comm₂₃ := (hφ₂₃ a).symm

/-- The connecting morphism `R^qg_{i, *}ℱ₃^• ⟶ R^{q'}g_{i, *}ℱ₁^•`, `q' = q + 1`, of the long
exact sequence of the derived direct image of a degreewise split short exact sequence. -/
abbrev complexHigherDirectImageδ (q q' : ℤ) (hq : q + 1 = q') (i : Iᵒᵖ) :
    (complexHigherDirectImageSystem γ q b F₃).obj i ⟶
      (complexHigherDirectImageSystem γ q' b F₁).obj i :=
  (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
    ((smallEtalePushforwardAb (γ.app i)).rightDerivedFunctorPlus.mapTriangle.obj
      (DerivedCategory.Plus.Qh.mapTriangle.obj
        (CochainComplex.trianglehPlusOfDegreewiseSplit b _ (σ i)))) q q' hq

/-- The triangle of the derived direct image of a degreewise split sequence is distinguished. -/
theorem mapTriangle_trianglehPlusOfDegreewiseSplit_distinguished {X S : Scheme.{u}} (g : X ⟶ S)
    {𝒮 : ShortComplex (CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ)}
    (τ : ∀ n, (𝒮.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).Splitting)
    [𝒮.X₁.IsStrictlyGE b] [𝒮.X₂.IsStrictlyGE b] [𝒮.X₃.IsStrictlyGE b] :
    (smallEtalePushforwardAb g).rightDerivedFunctorPlus.mapTriangle.obj
        (DerivedCategory.Plus.Qh.mapTriangle.obj
          (CochainComplex.trianglehPlusOfDegreewiseSplit b 𝒮 τ)) ∈ distTriang _ :=
  (smallEtalePushforwardAb g).rightDerivedFunctorPlus.map_distinguished _
    (DerivedCategory.Plus.Qh.map_distinguished _
      (CochainComplex.trianglehPlusOfDegreewiseSplit_distinguished b 𝒮 τ))

variable (hZ : ∀ n, (∀ i, IsZero ((F₃.obj i).X n)) ∨ (∀ i, IsZero ((F₁.obj i).X n)))

include hφ₁₂ hφ₂₃ hZ in
/-- **The connecting morphisms commute with the transition maps of the systems of higher direct
images**, by the compatibility of the derived base change map with connecting morphisms. -/
theorem complexHigherDirectImageδ_comm (q q' : ℤ) (hq : q + 1 = q') {i j : Iᵒᵖ} (a : i ⟶ j) :
    (systemPullback DS Ab.{u + 1} a).map (complexHigherDirectImageδ γ b w σ q q' hq j) ≫
        (complexHigherDirectImageSystem γ q' b F₁).map a =
      (complexHigherDirectImageSystem γ q b F₃).map a ≫
        complexHigherDirectImageδ γ b w σ q q' hq i :=
  (derivedBaseChangeHomologyMap_smallEtaleComplexPullbackComparison_homologySequenceδ b (DS.map a)
    (γ.app j) (γ.app i) (DX.map a) (transition_comm γ a) (σ j) (σ i)
    (shortComplexTransition hφ₁₂ hφ₂₃ w a)
    (fun n => CochainComplex.splitting_map_s_comp_of_isZero _ (σ j) (σ i) _ n
      ((hZ n).imp (fun h => h j) (fun h => h i)))
    (fun n => CochainComplex.splitting_map_r_comp_of_isZero _ (σ j) (σ i) _ n
      ((hZ n).imp (fun h => h j) (fun h => h i))) q q' hq).symm

include hφ₁₂ hφ₂₃ hZ in
/-- The connecting morphisms commute with the maps of the pulled back diagrams. -/
theorem pullbackDiagramMap_comp_complexHigherDirectImageδ (cS : Cone DS) (q q' : ℤ)
    (hq : q + 1 = q') {i j : Iᵒᵖ} (a : i ⟶ j) :
    (complexHigherDirectImageSystem γ q b F₃).pullbackDiagramMap cS (i := i) (j := j) a ≫
        (smallEtalePullbackAb (cS.π.app i)).map (complexHigherDirectImageδ γ b w σ q q' hq i) =
      (smallEtalePullbackAb (cS.π.app j)).map (complexHigherDirectImageδ γ b w σ q q' hq j) ≫
        (complexHigherDirectImageSystem γ q' b F₁).pullbackDiagramMap cS (i := i) (j := j) a :=
  pullbackDiagramMap_comp_map (fun i => complexHigherDirectImageδ γ b w σ q q' hq i)
    (fun a => complexHigherDirectImageδ_comm γ b hφ₁₂ hφ₂₃ w σ hZ q q' hq a) a

/-- The pulled back connecting morphism and its neighbours form an exact sequence. -/
theorem exact_map_complexHigherDirectImageδ (cS : Cone DS) (q q' : ℤ) (hq : q + 1 = q')
    (i : Iᵒᵖ) :
    (ShortComplex.mk ((smallEtalePullbackAb (cS.π.app i)).map
        (complexHigherDirectImageMap γ q b φ₂₃ i))
      ((smallEtalePullbackAb (cS.π.app i)).map (complexHigherDirectImageδ γ b w σ q q' hq i))
      ((ShortComplex.mk _ _ ((DerivedCategory.Plus.homologyFunctor _ 0).comp_homologySequenceδ _
        (mapTriangle_trianglehPlusOfDegreewiseSplit_distinguished b (γ.app i) (σ i)) q q' hq)).map
          (smallEtalePullbackAb (cS.π.app i))).zero).Exact :=
  ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₃ _
    (mapTriangle_trianglehPlusOfDegreewiseSplit_distinguished b (γ.app i) (σ i)) q q' hq).map
      (smallEtalePullbackAb (cS.π.app i))

/-- The pulled back neighbours of the middle term form an exact sequence. -/
theorem exact_map_complexHigherDirectImageMap (cS : Cone DS) (q : ℤ) (i : Iᵒᵖ) :
    (ShortComplex.mk ((smallEtalePullbackAb (cS.π.app i)).map
        (complexHigherDirectImageMap γ q b φ₁₂ i))
      ((smallEtalePullbackAb (cS.π.app i)).map (complexHigherDirectImageMap γ q b φ₂₃ i))
      ((ShortComplex.mk _ _ ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_comp _
        (mapTriangle_trianglehPlusOfDegreewiseSplit_distinguished b (γ.app i) (σ i)) q)).map
          (smallEtalePullbackAb (cS.π.app i))).zero).Exact :=
  ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₂ _
    (mapTriangle_trianglehPlusOfDegreewiseSplit_distinguished b (γ.app i) (σ i)) q).map
      (smallEtalePullbackAb (cS.π.app i))

section Limit

variable (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS)
  {𝓕₁ 𝓕₂ 𝓕₃ : CochainComplex (Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}) ℤ}
  [𝓕₁.IsStrictlyGE b] [𝓕₂.IsStrictlyGE b] [𝓕₃.IsStrictlyGE b]
  {ι₁ : ∀ i : Iᵒᵖ,
    ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).obj (F₁.obj i) ⟶ 𝓕₁}
  {ι₂ : ∀ i : Iᵒᵖ,
    ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).obj (F₂.obj i) ⟶ 𝓕₂}
  {ι₃ : ∀ i : Iᵒᵖ,
    ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).obj (F₃.obj i) ⟶ 𝓕₃}
  {φ'₁₂ : 𝓕₁ ⟶ 𝓕₂} {φ'₂₃ : 𝓕₂ ⟶ 𝓕₃}
  (hι₁₂ : ∀ i, ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).map (φ₁₂ i) ≫
    ι₂ i = ι₁ i ≫ φ'₁₂)
  (hι₂₃ : ∀ i, ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).map (φ₂₃ i) ≫
    ι₃ i = ι₂ i ≫ φ'₂₃)
  (w' : φ'₁₂ ≫ φ'₂₃ = 0)
  (σ' : ∀ n, ((ShortComplex.mk φ'₁₂ φ'₂₃ w').map
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).Splitting)

/-- The morphism of short complexes formed by the cocone maps of three systems of complexes. -/
@[simps]
def shortComplexLeg (i : Iᵒᵖ) :
    (ShortComplex.mk (φ₁₂ i) (φ₂₃ i) (w i)).map
        ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _) ⟶
      ShortComplex.mk φ'₁₂ φ'₂₃ w' where
  τ₁ := ι₁ i
  τ₂ := ι₂ i
  τ₃ := ι₃ i
  comm₁₂ := (hι₁₂ i).symm
  comm₂₃ := (hι₂₃ i).symm

/-- The connecting morphism `R^qg_*ℱ₃^• ⟶ R^{q'}g_*ℱ₁^•` on the limit. -/
abbrev complexLimitδ (q q' : ℤ) (hq : q + 1 = q') :
    (homologyAb cS.pt q).obj
        ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).obj (plusDerivedObj b 𝓕₃)) ⟶
      (homologyAb cS.pt q').obj
        ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).obj (plusDerivedObj b 𝓕₁)) :=
  (DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
    ((smallEtalePushforwardAb (limitMorphism γ cX cS hcS)).rightDerivedFunctorPlus.mapTriangle.obj
      (DerivedCategory.Plus.Qh.mapTriangle.obj
        (CochainComplex.trianglehPlusOfDegreewiseSplit b _ σ'))) q q' hq

variable (hZ' : ∀ i n, IsZero ((F₃.obj i).X n) ∨ IsZero (𝓕₁.X n))

include hι₁₂ hι₂₃ hZ' in
/-- **The connecting morphisms commute with the cocone maps**, by the compatibility of the
derived base change map with connecting morphisms. -/
theorem complexLeg_comp_complexLimitδ (q q' : ℤ) (hq : q + 1 = q') (i : Iᵒᵖ) :
    complexLeg γ q b F₃ cX cS hcS 𝓕₃ ι₃ i ≫ complexLimitδ γ b cX cS hcS w' σ' q q' hq =
      (smallEtalePullbackAb (cS.π.app i)).map (complexHigherDirectImageδ γ b w σ q q' hq i) ≫
        complexLeg γ q' b F₁ cX cS hcS 𝓕₁ ι₁ i :=
  derivedBaseChangeHomologyMap_smallEtaleComplexPullbackComparison_homologySequenceδ b (cS.π.app i)
    (γ.app i) (limitMorphism γ cX cS hcS) (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i)
    (σ i) σ' (shortComplexLeg w cX hι₁₂ hι₂₃ w' i)
    (fun n => CochainComplex.splitting_map_s_comp_of_isZero _ (σ i) σ' _ n (hZ' i n))
    (fun n => CochainComplex.splitting_map_r_comp_of_isZero _ (σ i) σ' _ n (hZ' i n)) q q' hq

/-! ### The five lemma for the colimit comparison -/

variable [IsDirected I (· ≤ ·)] [Nonempty I]

variable {cX} (hι₁ : F₁.IsPullbackCocone cX ι₁) (hι₂ : F₂.IsPullbackCocone cX ι₂)
  (hι₃ : F₃.IsPullbackCocone cX ι₃)

include hφ₁₂ hφ₂₃ w σ hZ hι₁₂ hι₂₃ w' σ' hZ' in
/-- **The four lemma for the colimit comparison, epimorphism half.** Along a degreewise split
short exact sequence `0 ⟶ ℱ₁^• ⟶ ℱ₂^• ⟶ ℱ₃^• ⟶ 0` of systems of complexes and of their colimits,
if the comparison maps in degree `q` of `ℱ₁^•` and `ℱ₃^•` are epimorphisms and the one in degree
`q + 1` of `ℱ₁^•` is a monomorphism, then the comparison map in degree `q` of `ℱ₂^•` is an
epimorphism. -/
theorem epi_complexColimitDesc_of_shortExact (q q' : ℤ) (hq : q + 1 = q')
    (h₁ : Epi (complexColimitDesc γ q b cS hcS F₁ 𝓕₁ ι₁ hι₁))
    (h₃ : Epi (complexColimitDesc γ q b cS hcS F₃ 𝓕₃ ι₃ hι₃))
    (h₄ : Mono (complexColimitDesc γ q' b cS hcS F₁ 𝓕₁ ι₁ hι₁)) :
    Epi (complexColimitDesc γ q b cS hcS F₂ 𝓕₂ ι₂ hι₂) := by
  have := hasExactColimitsOfShape_systemLift_sheaf (I := I) cS.pt
  have hT' := mapTriangle_trianglehPlusOfDegreewiseSplit_distinguished b
    (limitMorphism γ cX cS hcS) σ'
  exact SystemLift.epi_colimitDesc_of_exact
    (fun a c => (complexHigherDirectImageSystem γ q b F₁).pullbackDiagramMap_comp cS a c)
    (fun a c => (complexHigherDirectImageSystem γ q b F₂).pullbackDiagramMap_comp cS a c)
    (fun a c => (complexHigherDirectImageSystem γ q b F₃).pullbackDiagramMap_comp cS a c)
    (fun a c => (complexHigherDirectImageSystem γ q' b F₁).pullbackDiagramMap_comp cS a c)
    (fun a => complexLeg_cocone γ q b F₁ cX cS hcS 𝓕₁ ι₁ hι₁ a)
    (fun a => complexLeg_cocone γ q b F₂ cX cS hcS 𝓕₂ ι₂ hι₂ a)
    (fun a => complexLeg_cocone γ q b F₃ cX cS hcS 𝓕₃ ι₃ hι₃ a)
    (fun a => complexLeg_cocone γ q' b F₁ cX cS hcS 𝓕₁ ι₁ hι₁ a)
    (fun i => (smallEtalePullbackAb (cS.π.app i)).map (complexHigherDirectImageMap γ q b φ₁₂ i))
    (fun i => (smallEtalePullbackAb (cS.π.app i)).map (complexHigherDirectImageMap γ q b φ₂₃ i))
    (fun i => (smallEtalePullbackAb (cS.π.app i)).map
      (complexHigherDirectImageδ γ b w σ q q' hq i))
    (fun a => pullbackDiagramMap_comp_complexHigherDirectImageMap γ q b hφ₁₂ cS a)
    (fun a => pullbackDiagramMap_comp_complexHigherDirectImageMap γ q b hφ₂₃ cS a)
    (fun a => pullbackDiagramMap_comp_complexHigherDirectImageδ γ b hφ₁₂ hφ₂₃ w σ hZ cS q q' hq a)
    ((homologyAb cS.pt q).map ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).map
      (plusComplexMap b φ'₁₂)))
    ((homologyAb cS.pt q).map ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).map
      (plusComplexMap b φ'₂₃)))
    (complexLimitδ γ b cX cS hcS w' σ' q q' hq)
    (fun i => complexLeg_comp_map γ q b cX cS hcS ι₁ ι₂ hι₁₂ i)
    (fun i => complexLeg_comp_map γ q b cX cS hcS ι₂ ι₃ hι₂₃ i)
    (fun i => complexLeg_comp_complexLimitδ γ b w σ cX cS hcS hι₁₂ hι₂₃ w' σ' hZ' q q' hq i)
    (fun i => ((ShortComplex.mk _ _
      ((DerivedCategory.Plus.homologyFunctor _ 0).comp_homologySequenceδ
        _ (mapTriangle_trianglehPlusOfDegreewiseSplit_distinguished b (γ.app i) (σ i)) q q' hq)).map
          (smallEtalePullbackAb (cS.π.app i))).zero)
    (fun i => exact_map_complexHigherDirectImageδ γ b w σ cS q q' hq i)
    ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_comp _ hT' q)
    ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₂ _ hT' q)
    ((DerivedCategory.Plus.homologyFunctor _ 0).comp_homologySequenceδ _ hT' q q' hq) h₁ h₃ h₄

include hφ₁₂ hφ₂₃ w σ hZ hι₁₂ hι₂₃ w' σ' hZ' in
/-- **The four lemma for the colimit comparison, monomorphism half.** Along a degreewise split
short exact sequence `0 ⟶ ℱ₁^• ⟶ ℱ₂^• ⟶ ℱ₃^• ⟶ 0` of systems of complexes and of their colimits,
if the comparison map in degree `q - 1` of `ℱ₃^•` is an epimorphism and those in degree `q` of
`ℱ₁^•` and `ℱ₃^•` are monomorphisms, then the comparison map in degree `q` of `ℱ₂^•` is a
monomorphism. -/
theorem mono_complexColimitDesc_of_shortExact (q₀ q : ℤ) (hq : q₀ + 1 = q)
    (h₁ : Epi (complexColimitDesc γ q₀ b cS hcS F₃ 𝓕₃ ι₃ hι₃))
    (h₂ : Mono (complexColimitDesc γ q b cS hcS F₁ 𝓕₁ ι₁ hι₁))
    (h₄ : Mono (complexColimitDesc γ q b cS hcS F₃ 𝓕₃ ι₃ hι₃)) :
    Mono (complexColimitDesc γ q b cS hcS F₂ 𝓕₂ ι₂ hι₂) := by
  have := hasExactColimitsOfShape_systemLift_sheaf (I := I) cS.pt
  have hT' := mapTriangle_trianglehPlusOfDegreewiseSplit_distinguished b
    (limitMorphism γ cX cS hcS) σ'
  exact SystemLift.mono_colimitDesc_of_exact
    (fun a c => (complexHigherDirectImageSystem γ q₀ b F₃).pullbackDiagramMap_comp cS a c)
    (fun a c => (complexHigherDirectImageSystem γ q b F₁).pullbackDiagramMap_comp cS a c)
    (fun a c => (complexHigherDirectImageSystem γ q b F₂).pullbackDiagramMap_comp cS a c)
    (fun a c => (complexHigherDirectImageSystem γ q b F₃).pullbackDiagramMap_comp cS a c)
    (fun a => complexLeg_cocone γ q₀ b F₃ cX cS hcS 𝓕₃ ι₃ hι₃ a)
    (fun a => complexLeg_cocone γ q b F₁ cX cS hcS 𝓕₁ ι₁ hι₁ a)
    (fun a => complexLeg_cocone γ q b F₂ cX cS hcS 𝓕₂ ι₂ hι₂ a)
    (fun a => complexLeg_cocone γ q b F₃ cX cS hcS 𝓕₃ ι₃ hι₃ a)
    (fun i => (smallEtalePullbackAb (cS.π.app i)).map
      (complexHigherDirectImageδ γ b w σ q₀ q hq i))
    (fun i => (smallEtalePullbackAb (cS.π.app i)).map (complexHigherDirectImageMap γ q b φ₁₂ i))
    (fun i => (smallEtalePullbackAb (cS.π.app i)).map (complexHigherDirectImageMap γ q b φ₂₃ i))
    (fun a => pullbackDiagramMap_comp_complexHigherDirectImageδ γ b hφ₁₂ hφ₂₃ w σ hZ cS q₀ q hq a)
    (fun a => pullbackDiagramMap_comp_complexHigherDirectImageMap γ q b hφ₁₂ cS a)
    (fun a => pullbackDiagramMap_comp_complexHigherDirectImageMap γ q b hφ₂₃ cS a)
    (complexLimitδ γ b cX cS hcS w' σ' q₀ q hq)
    ((homologyAb cS.pt q).map ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).map
      (plusComplexMap b φ'₁₂)))
    ((homologyAb cS.pt q).map ((derivedPushforwardAb (limitMorphism γ cX cS hcS)).map
      (plusComplexMap b φ'₂₃)))
    (fun i => complexLeg_comp_complexLimitδ γ b w σ cX cS hcS hι₁₂ hι₂₃ w' σ' hZ' q₀ q hq i)
    (fun i => complexLeg_comp_map γ q b cX cS hcS ι₁ ι₂ hι₁₂ i)
    (fun i => complexLeg_comp_map γ q b cX cS hcS ι₂ ι₃ hι₂₃ i)
    (fun i => ((ShortComplex.mk _ _
      ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ_comp
        _ (mapTriangle_trianglehPlusOfDegreewiseSplit_distinguished b (γ.app i) (σ i)) q₀ q hq)).map
          (smallEtalePullbackAb (cS.π.app i))).zero)
    (fun i => ((ShortComplex.mk _ _
      ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_comp
        _ (mapTriangle_trianglehPlusOfDegreewiseSplit_distinguished b (γ.app i) (σ i)) q)).map
          (smallEtalePullbackAb (cS.π.app i))).zero)
    (fun i => exact_map_complexHigherDirectImageMap γ b w σ cS q i)
    ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ_comp _ hT' q₀ q hq)
    ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₁ _ hT' q₀ q hq) h₁ h₂ h₄

end Limit

end ShortExact

/-! ### Sheaves placed in one degree, moved to the next degree -/

/-- An isomorphism between the two middle terms of an exact sequence `0 ⟶ X₂ ⟶ X₃ ⟶ 0`, read
off two exact sequences with vanishing outer terms. -/
theorem isIso_of_exact_of_isZero {𝒜 : Type*} [Category* 𝒜] [Abelian 𝒜] {X₁ X₂ X₃ X₄ : 𝒜}
    {f : X₁ ⟶ X₂} {δ : X₂ ⟶ X₃} {g : X₃ ⟶ X₄} {w₁ : f ≫ δ = 0} {w₂ : δ ≫ g = 0}
    (h₁ : (ShortComplex.mk f δ w₁).Exact) (h₂ : (ShortComplex.mk δ g w₂).Exact)
    (hX₁ : IsZero X₁) (hX₄ : IsZero X₄) : IsIso δ := by
  have := h₁.mono_g (hX₁.eq_of_src f 0)
  have := h₂.epi_f (hX₄.eq_of_tgt g 0)
  exact isIso_of_mono_of_epi δ

end Stacks.EtaleCohomology.LimitHigherDirectImage

namespace Stacks.EtaleCohomology.EtaleComplexSystem

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}}

variable (D) in
/-- **The system of two-term complexes `𝒢_i --𝟙--> 𝒢_i`** in degrees `i₀`, `i₁ = i₀ + 1` of a
system of sheaves `𝒢`. -/
abbrev double (G : EtaleSheafSystem D Ab.{u + 1}) {i₀ i₁ : ℤ} (hi : (ComplexShape.up ℤ).Rel i₀ i₁) :
    EtaleComplexSystem D where
  obj i := HomologicalComplex.double (𝟙 (G.obj i)) hi
  map {i j} a := CochainComplex.doubleIdMap hi (systemPullback D Ab.{u + 1} a) (G.map a)
  map_comp {i j k} a c := by
    have h := G.map_comp a c
    refine HomologicalComplex.to_double_hom_ext (hi₀₁ := hi) ?_ ?_
    · have hnat := (systemPullbackComp D Ab.{u + 1} a c).inv.naturality
        (HomologicalComplex.doubleXIso₀ (𝟙 (G.obj k)) hi).hom
      simp only [Functor.comp_map] at hnat
      simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
        Functor.mapHomologicalComplex_map_f, CochainComplex.doubleIdMap_f₀, Functor.map_comp,
        Category.assoc, Iso.map_inv_hom_id_assoc, ← h, reassoc_of% hnat]
    · have hnat := (systemPullbackComp D Ab.{u + 1} a c).inv.naturality
        (HomologicalComplex.doubleXIso₁ (𝟙 (G.obj k)) hi (CochainComplex.ne_of_rel_up hi)).hom
      simp only [Functor.comp_map] at hnat
      simp only [HomologicalComplex.comp_f, NatIso.mapHomologicalComplex_inv_app_f,
        Functor.mapHomologicalComplex_map_f, CochainComplex.doubleIdMap_f₁, Functor.map_comp,
        Category.assoc, Iso.map_inv_hom_id_assoc, ← h, reassoc_of% hnat]

end Stacks.EtaleCohomology.EtaleComplexSystem

namespace Stacks.EtaleCohomology.LimitHigherDirectImage

attribute [local instance] HasDerivedCategory.standard Functor.commShiftRightDerivedFunctorPlus
  Functor.isTriangulated_rightDerivedFunctorPlus
  LimitHigherDirectImage.hasColimitsOfShape_systemLift_sheaf

/-- The connecting morphism of the derived direct image of a degreewise split sequence is an
isomorphism if the middle term vanishes in the bounded below homotopy category. -/
private theorem isIso_homologySequenceδ_of_isZero_X₂ (b : ℤ) {X S : Scheme.{u}} (g : X ⟶ S)
    {𝒮 : ShortComplex (CochainComplex (Sheaf (smallEtaleTopology X) Ab.{u + 1}) ℤ)}
    (τ : ∀ n, (𝒮.map (HomologicalComplex.eval _ (ComplexShape.up ℤ) n)).Splitting)
    [𝒮.X₁.IsStrictlyGE b] [𝒮.X₂.IsStrictlyGE b] [𝒮.X₃.IsStrictlyGE b]
    (h : IsZero (CochainComplex.plusHomotopyObj b 𝒮.X₂)) (q q' : ℤ) (hq : q + 1 = q') :
    IsIso ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequenceδ
      ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.mapTriangle.obj
        (DerivedCategory.Plus.Qh.mapTriangle.obj
          (CochainComplex.trianglehPlusOfDegreewiseSplit b 𝒮 τ))) q q' hq) :=
  have hz (r : ℤ) := Functor.map_isZero (homologyAb S r)
    (Functor.map_isZero (derivedPushforwardAb g) (Functor.map_isZero DerivedCategory.Plus.Qh h))
  isIso_of_exact_of_isZero
    ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₃ _
      (mapTriangle_trianglehPlusOfDegreewiseSplit_distinguished b g τ) q q' hq)
    ((DerivedCategory.Plus.homologyFunctor _ 0).homologySequence_exact₁ _
      (mapTriangle_trianglehPlusOfDegreewiseSplit_distinguished b g τ) q q' hq) (hz q) (hz q')

section Shift

open EtaleComplexSystem

variable {I : Type u} [Preorder I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}} (γ : DX ⟶ DS)
  (cX : Cone DX) (cS : Cone DS) (hcS : IsLimit cS) (b : ℤ)
  (G : EtaleSheafSystem DX Ab.{u + 1}) {𝓖 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}}
  (ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (G.obj i) ⟶ 𝓖)
  {i₀ i₁ : ℤ} (hi : (ComplexShape.up ℤ).Rel i₀ i₁)

include hi in
/-- **A system of sheaves may be moved from degree `i₀` to degree `i₁ = i₀ + 1`**: the colimit
assertion in degree `q` for the system placed in degree `i₀` is equivalent to the one in degree
`q + 1` for the system placed in degree `i₁`. -/
theorem isComplexHigherDirectImageColimit_single_iff (hb : b ≤ i₀) (q q' : ℤ) (hq : q + 1 = q')
    [∀ i, ((single DX G i₀).obj i).IsStrictlyGE b] [∀ i, ((single DX G i₁).obj i).IsStrictlyGE b]
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) i₀).obj 𝓖) b]
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) i₁).obj 𝓖) b] :
    IsComplexHigherDirectImageColimit γ q b (single DX G i₀) cX cS hcS
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i₀).obj 𝓖) (singleι G ιG i₀) ↔
      IsComplexHigherDirectImageColimit γ q' b (single DX G i₁) cX cS hcS
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) i₁).obj 𝓖) (singleι G ιG i₁) := by
  have : ∀ i, CochainComplex.IsStrictlyGE (HomologicalComplex.double (𝟙 (G.obj i)) hi) b :=
    fun i => CochainComplex.isStrictlyGE_double (G.obj i) hi b hb
  have : CochainComplex.IsStrictlyGE (HomologicalComplex.double (𝟙 𝓖) hi) b :=
    CochainComplex.isStrictlyGE_double 𝓖 hi b hb
  have hφ₁₂ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      ((systemPullback DX Ab.{u + 1} a).mapHomologicalComplex _).map
          (CochainComplex.doubleShortComplex (G.obj j) hi).f ≫ (double DX G hi).map a =
        (single DX G i₁).map a ≫ (CochainComplex.doubleShortComplex (G.obj i) hi).f :=
    fun a => (CochainComplex.doubleShortComplexMap hi (systemPullback DX Ab.{u + 1} a)
      (G.map a)).comm₁₂.symm
  have hφ₂₃ : ∀ {i j : Iᵒᵖ} (a : i ⟶ j),
      ((systemPullback DX Ab.{u + 1} a).mapHomologicalComplex _).map
          (CochainComplex.doubleShortComplex (G.obj j) hi).g ≫ (single DX G i₀).map a =
        (double DX G hi).map a ≫ (CochainComplex.doubleShortComplex (G.obj i) hi).g :=
    fun a => (CochainComplex.doubleShortComplexMap hi (systemPullback DX Ab.{u + 1} a)
      (G.map a)).comm₂₃.symm
  have hι₁₂ : ∀ i, ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).map
        (CochainComplex.doubleShortComplex (G.obj i) hi).f ≫
          CochainComplex.doubleIdMap hi (smallEtalePullbackAb (cX.π.app i)) (ιG i) =
        singleι G ιG i₁ i ≫ (CochainComplex.doubleShortComplex 𝓖 hi).f :=
    fun i => (CochainComplex.doubleShortComplexMap hi (smallEtalePullbackAb (cX.π.app i))
      (ιG i)).comm₁₂.symm
  have hι₂₃ : ∀ i, ((smallEtalePullbackAb (cX.π.app i)).mapHomologicalComplex _).map
        (CochainComplex.doubleShortComplex (G.obj i) hi).g ≫ singleι G ιG i₀ i =
        CochainComplex.doubleIdMap hi (smallEtalePullbackAb (cX.π.app i)) (ιG i) ≫
          (CochainComplex.doubleShortComplex 𝓖 hi).g :=
    fun i => (CochainComplex.doubleShortComplexMap hi (smallEtalePullbackAb (cX.π.app i))
      (ιG i)).comm₂₃.symm
  let σ := fun i k => CochainComplex.doubleShortComplexSplitting (G.obj i) hi k
  let σ' := fun k => CochainComplex.doubleShortComplexSplitting 𝓖 hi k
  have hZ : ∀ k, (∀ i, IsZero (((single DX G i₀).obj i).X k)) ∨
      (∀ i, IsZero (((single DX G i₁).obj i).X k)) := fun k => by
    rcases eq_or_ne k i₁ with rfl | hk
    · exact Or.inl fun _ => HomologicalComplex.isZero_single_obj_X _ _ _ _
        (CochainComplex.ne_of_rel_up hi).symm
    · exact Or.inr fun _ => HomologicalComplex.isZero_single_obj_X _ _ _ _ hk
  have hZ' : ∀ i k, IsZero (((single DX G i₀).obj i).X k) ∨
      IsZero (((HomologicalComplex.single _ (ComplexShape.up ℤ) i₁).obj 𝓖).X k) := fun i k =>
    CochainComplex.isZero_doubleShortComplex_X₃_or_X₁ (X := G.obj i) hi 𝓖 k
  exact IsSystemColimit.iff_of_isoSystem
    (fun i => (smallEtalePullbackAb (cS.π.app i)).mapIso (@asIso _ _ _ _ _
      (isIso_homologySequenceδ_of_isZero_X₂ b (γ.app i) (σ i)
        (CochainComplex.isZero_plusHomotopyObj_double_id (G.obj i) hi b) q q' hq)))
    (@asIso _ _ _ _ _ (isIso_homologySequenceδ_of_isZero_X₂ b (limitMorphism γ cX cS hcS) σ'
      (CochainComplex.isZero_plusHomotopyObj_double_id 𝓖 hi b) q q' hq))
    (fun a => pullbackDiagramMap_comp_complexHigherDirectImageδ (F₁ := single DX G i₁)
      (F₂ := double DX G hi) (F₃ := single DX G i₀)
      (φ₁₂ := fun i => (CochainComplex.doubleShortComplex (G.obj i) hi).f)
      (φ₂₃ := fun i => (CochainComplex.doubleShortComplex (G.obj i) hi).g) γ b hφ₁₂ hφ₂₃
      (fun i => (CochainComplex.doubleShortComplex (G.obj i) hi).zero) σ hZ cS q q' hq a)
    (fun i => complexLeg_comp_complexLimitδ (F₁ := single DX G i₁) (F₂ := double DX G hi)
      (F₃ := single DX G i₀)
      (φ₁₂ := fun i => (CochainComplex.doubleShortComplex (G.obj i) hi).f)
      (φ₂₃ := fun i => (CochainComplex.doubleShortComplex (G.obj i) hi).g) γ b
      (fun i => (CochainComplex.doubleShortComplex (G.obj i) hi).zero) σ cX cS hcS hι₁₂ hι₂₃
      (CochainComplex.doubleShortComplex 𝓖 hi).zero σ' hZ' q q' hq i)

end Shift


/-! ### Sheaves placed in degree zero: Stacks 0EYM -/

section SingleZero

private theorem key_d_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ o₇ : 𝒳}
    {a : o₀ ⟶ o₁} {c : o₁ ⟶ o₂} {s : o₃ ⟶ o₀} {si : o₀ ⟶ o₃} {x : o₃ ⟶ o₄} {m : o₄ ⟶ o₅}
    {uu : o₅ ⟶ o₁} {ri : o₁ ⟶ o₀} {ui : o₁ ⟶ o₅} {k : o₅ ⟶ o₂} {y : o₃ ⟶ o₇} {z : o₇ ⟶ o₂}
    {n : o₄ ⟶ o₂}
    (h1 : s = x ≫ m ≫ uu ≫ ri) (h2 : c = ui ≫ k) (h3 : m ≫ k = n) (h4 : y ≫ z = x ≫ n)
    (hu : uu ≫ ui = 𝟙 _) (hri : ri ≫ a = 𝟙 _) (hs : si ≫ s = 𝟙 _) :
    a ≫ c = si ≫ y ≫ z := by
  rw [← Category.id_comp (a ≫ c), ← hs, h1, h2, h4, ← h3]
  simp only [Category.assoc]
  rw [reassoc_of% hri, reassoc_of% hu]

/-- **The comparison of the derived inverse image of a single complex with the single complex of
the inverse image is the identification of single functors.** For `e : Y ⟶ T`, a sheaf `𝒢` on
`T`, a sheaf `𝒢'` on `Y` and `φ : e^{-1}𝒢 ⟶ 𝒢'`, the comparison
`smallEtaleComplexPullbackComparison` of the map of single complexes induced by `φ`, read through
the identifications of `𝒢[0]` with the class of the single complex, is the comparison
`Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso` followed by `φ[0]`. -/
theorem derivedPullback_map_singleFunctorPlusIsoCompQh_comp {Y T : Scheme.{u}} (e : Y ⟶ T)
    (b : ℤ) (G : Sheaf (smallEtaleTopology T) Ab.{u + 1})
    (G' : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    (φ : (smallEtalePullbackAb e).obj G ⟶ G')
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) b]
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G') b] :
    (derivedPullbackAb e).map ((Functor.singleFunctorPlusIsoCompQh 0).hom.app G) ≫
        smallEtaleComplexPullbackComparison b e
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G')
          (((smallEtalePullbackAb e).mapCochainComplexSingleFunctor 0).hom.app G ≫
            (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ) =
      (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (smallEtalePullbackAb e) 0).inv.app G ≫
        (DerivedCategory.Plus.singleFunctor _ 0).map φ ≫
          (Functor.singleFunctorPlusIsoCompQh 0).hom.app G' := by
  let : IsIso (smallEtalePullbackAb e).rightDerivedFunctorPlusUnith :=
    (smallEtalePullbackAb e).isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
  have h1 := Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso_hom_app
    (smallEtalePullbackAb e) G
  have h2 := smallEtaleComplexPullbackComparison_eq b e
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)
    ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G')
    (((smallEtalePullbackAb e).mapCochainComplexSingleFunctor 0).hom.app G ≫
      (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ)
  have h3 : (Functor.mapHomotopyCategoryPlusSingleFunctor (smallEtalePullbackAb e) 0).inv.app G ≫
      (ObjectProperty.homMk ((HomotopyCategory.quotient _ _).map
        (((smallEtalePullbackAb e).mapCochainComplexSingleFunctor 0).hom.app G ≫
          (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ)) :
        (smallEtalePullbackAb e).mapHomotopyCategoryPlus.obj (CochainComplex.plusHomotopyObj b
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G)) ⟶
            CochainComplex.plusHomotopyObj b
              ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G')) =
      (HomotopyCategory.Plus.singleFunctor _ 0).map φ := by
    apply (HomotopyCategory.Plus.ι _).map_injective
    refine ((HomotopyCategory.Plus.ι _).map_comp _ _).trans ?_
    refine (congrArg (fun z => z ≫ _)
      (Stacks.DerivedFunctor.ι_map_mapHomotopyCategoryPlusSingleFunctor_inv_app
        (smallEtalePullbackAb e) G)).trans ?_
    refine ((HomotopyCategory.quotient _ _).map_comp _ _).symm.trans ?_
    exact congrArg (HomotopyCategory.quotient _ _).map
      (Iso.inv_hom_id_app_assoc
        (HomologicalComplex.singleMapHomologicalComplex (smallEtalePullbackAb e) _ 0) G _)
  have h4 := (Functor.singleFunctorPlusIsoCompQh (A := Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    0).hom.naturality φ
  simp only [Functor.comp_map] at h4
  exact key_d_chain h1 h2 ((Functor.map_comp _ _ _).symm.trans (congrArg _ h3)) h4
    ((asIso (smallEtalePullbackAb e).rightDerivedFunctorPlusUnith).hom_inv_id_app _)
    ((Functor.map_comp _ _ _).symm.trans
      ((congrArg (smallEtalePullbackAb e).rightDerivedFunctorPlus.map
        (Iso.inv_hom_id_app (Functor.singleFunctorPlusIsoCompQh 0) G)).trans
          (CategoryTheory.Functor.map_id _ _)))
    ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso (smallEtalePullbackAb e)
      0).inv_hom_id_app G)

/-- **The higher direct images of a sheaf, as cohomology of the derived direct image of a single
complex**: `R^qg_*𝒢 ≅ H^q(Rg_*𝒢[0])`, the comparison `Stacks.DerivedIndexing.rightDerivedIso` of
the two indexings followed by the identification of `𝒢[0]` with the class of the single
complex. -/
def singleHigherDirectImageIso {X S : Scheme.{u}} (g : X ⟶ S) (b : ℤ) (q : ℕ)
    (G : Sheaf (smallEtaleTopology X) Ab.{u + 1})
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) b] :
    ((smallEtalePushforwardAb g).rightDerived q).obj G ≅
      (homologyAb S q).obj ((derivedPushforwardAb g).obj
        (plusDerivedObj b ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))) :=
  (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).app G ≪≫
    (homologyAb S q).mapIso ((derivedPushforwardAb g).mapIso
      ((Functor.singleFunctorPlusIsoCompQh 0).app G))

private theorem key_zero_chain {𝒳 : Type*} [Category* 𝒳]
    {P₀ P₁ P₂ P₃ P₄ P₅ P₆ P₇ P₈ Q₁ Q₂ Q₃ : 𝒳} {T : P₀ ⟶ P₅} {r₁ : P₀ ⟶ P₁} {A₂ : P₁ ⟶ P₂}
    {Ds : P₂ ⟶ P₃} {E : P₃ ⟶ P₄} {ri : P₄ ⟶ P₅} {Rφ : P₅ ⟶ P₆} {θh : P₆ ⟶ P₈}
    {rh' : P₆ ⟶ P₇} {Hε' : P₇ ⟶ P₈} {rh : P₅ ⟶ P₄} {Pφ : P₄ ⟶ P₇} {θg : P₀ ⟶ Q₁}
    {fH : P₁ ⟶ Q₁} {Dbc : Q₁ ⟶ P₈} {A₂Q : Q₁ ⟶ Q₂} {DQ : Q₂ ⟶ Q₃} {C : Q₃ ⟶ P₈}
    {HRε : P₂ ⟶ Q₂} {HReε : P₃ ⟶ Q₃}
    (hdef : T = (r₁ ≫ A₂) ≫ Ds ≫ (E ≫ ri)) (hθh : θh = rh' ≫ Hε') (hθg : θg = r₁ ≫ fH)
    (hdb : Dbc = A₂Q ≫ DQ ≫ C) (n₁ : Rφ ≫ rh' = rh ≫ Pφ) (n₂ : ri ≫ rh = 𝟙 _)
    (n₃ : fH ≫ A₂Q = A₂ ≫ HRε) (n₄ : HRε ≫ DQ = Ds ≫ HReε) (n₅ : HReε ≫ C = E ≫ Pφ ≫ Hε') :
    (T ≫ Rφ) ≫ θh = θg ≫ Dbc := by
  rw [hdef, hθh, hθg, hdb]
  simp only [Category.assoc]
  rw [reassoc_of% n₁, reassoc_of% n₂, reassoc_of% n₃, reassoc_of% n₄, n₅]

/-- **The base change map on higher direct images is the derived base change map on single
complexes.** For a commutative square `h ≫ f' = e ≫ g`, a sheaf `𝒢` on `T`, a sheaf `𝒢'` on `Y`
and `φ : e^{-1}𝒢 ⟶ 𝒢'`, the base change map `(f')^{-1}R^qg_*𝒢 ⟶ R^qh_*e^{-1}𝒢` followed by
`R^qh_*φ` is, through the identifications `singleHigherDirectImageIso`, the derived base change
map on cohomology sheaves at the single complexes `𝒢[0]` and `𝒢'[0]`. -/
theorem higherBaseChangeMapAb_comp_singleHigherDirectImageIso {X' Y S T : Scheme.{u}}
    (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g) (b : ℤ) (q : ℕ)
    (G : Sheaf (smallEtaleTopology T) Ab.{u + 1}) (G' : Sheaf (smallEtaleTopology Y) Ab.{u + 1})
    (φ : (smallEtalePullbackAb e).obj G ⟶ G')
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G) b]
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G') b] :
    ((higherBaseChangeMapAb f' g h e w q).app G ≫
        ((smallEtalePushforwardAb h).rightDerived q).map φ) ≫
          (singleHigherDirectImageIso h b q G').hom =
      (smallEtalePullbackAb f').map (singleHigherDirectImageIso g b q G).hom ≫
        derivedBaseChangeHomologyMap f' g h e w q
          (plusDerivedObj b ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G))
          (plusDerivedObj b ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj G'))
          (smallEtaleComplexPullbackComparison b e _ _
            (((smallEtalePullbackAb e).mapCochainComplexSingleFunctor 0).hom.app G ≫
              (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map φ)) := by
  have n₄ := (Functor.map_comp _ _ _).symm.trans ((congrArg (homologyAb X' q).map
    ((smallEtaleDerivedBaseChangeAb f' g h e w).naturality
      ((Functor.singleFunctorPlusIsoCompQh 0).hom.app G))).trans (Functor.map_comp _ _ _))
  have n₅ := ((derivedPushforwardAb h ⋙ homologyAb X' q).map_comp _ _).symm.trans
    ((congrArg (derivedPushforwardAb h ⋙ homologyAb X' q).map
      (derivedPullback_map_singleFunctorPlusIsoCompQh_comp e b G G' φ)).trans
        (((derivedPushforwardAb h ⋙ homologyAb X' q).map_comp _ _).trans
          (congrArg _ ((derivedPushforwardAb h ⋙ homologyAb X' q).map_comp _ _))))
  have hθh : (singleHigherDirectImageIso h b q G').hom =
      (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) q).hom.app G' ≫
        (homologyAb X' q).map ((derivedPushforwardAb h).map
          ((Functor.singleFunctorPlusIsoCompQh 0).hom.app G')) := rfl
  have hθg : (smallEtalePullbackAb f').map (singleHigherDirectImageIso g b q G).hom =
      (smallEtalePullbackAb f').map
          ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).hom.app G) ≫
        (smallEtalePullbackAb f').map ((homologyAb S q).map ((derivedPushforwardAb g).map
          ((Functor.singleFunctorPlusIsoCompQh 0).hom.app G))) :=
    Functor.map_comp _ _ _
  have hdef : (higherBaseChangeMapAb f' g h e w q).app G =
      ((smallEtalePullbackAb f').map
          ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) q).hom.app G) ≫
        (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb f') q).inv.app
          ((smallEtalePushforwardAb g).rightDerivedFunctorPlus.obj
            ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj
              G))) ≫
      (DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1}) q).map
        ((smallEtaleDerivedBaseChangeAb f' g h e w).app
          ((DerivedCategory.Plus.singleFunctor (Sheaf (smallEtaleTopology T) Ab.{u + 1}) 0).obj
            G)) ≫
      ((DerivedCategory.Plus.homologyFunctor (Sheaf (smallEtaleTopology X') Ab.{u + 1}) q).map
          ((smallEtalePushforwardAb h).rightDerivedFunctorPlus.map
            ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
              (smallEtalePullbackAb e) 0).inv.app G)) ≫
        (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) q).inv.app
          ((smallEtalePullbackAb e).obj G)) := rfl
  exact key_zero_chain hdef hθh hθg rfl
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) q).hom.naturality φ)
    ((Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) q).inv_hom_id_app
      ((smallEtalePullbackAb e).obj G))
    ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso (smallEtalePullbackAb f')
      q).inv.naturality
        ((derivedPushforwardAb g).map ((Functor.singleFunctorPlusIsoCompQh 0).hom.app G)))
    n₄ n₅

end SingleZero


/-! ### Sheaves placed in one degree: Stacks 0EYM after a shift -/

section Single

/-- Pasting of two commutative squares sharing the edge `P`. -/
theorem comp_comp_eq_of_comp_eq {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ : 𝒳}
    {c₁ : o₀ ⟶ o₁} {M₀ : o₁ ⟶ o₂} {M₁ : o₂ ⟶ o₃} {N₀ : o₀ ⟶ o₄} {c₂ : o₄ ⟶ o₅}
    {N₁ : o₅ ⟶ o₃} {P : o₁ ⟶ o₅} (hk : M₀ ≫ M₁ = P ≫ N₁) (hn : N₀ ≫ c₂ = c₁ ≫ P) :
    (c₁ ≫ M₀) ≫ M₁ = N₀ ≫ c₂ ≫ N₁ := by
  rw [Category.assoc, hk, ← reassoc_of% hn]

open EtaleComplexSystem

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I] {DX DS : Iᵒᵖ ⥤ Scheme.{u}}
  (γ : DX ⟶ DS) [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] {cX : Cone DX} {cS : Cone DS} (hcX : IsLimit cX)
  (hcS : IsLimit cS) (G : EtaleSheafSystem DX Ab.{u + 1})
  {𝓖 : Sheaf (smallEtaleTopology cX.pt) Ab.{u + 1}}
  {ιG : ∀ i : Iᵒᵖ, (smallEtalePullbackAb (cX.π.app i)).obj (G.obj i) ⟶ 𝓖}
  (hιG : IsPullbackCocone cX G ιG) (hpres : IsPullbackColimitPresentation cX 𝓖 G ιG)

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] in
/-- The identifications `singleHigherDirectImageIso` commute with the transition maps. -/
theorem higherDirectImageDiagramMap_comp_singleHigherDirectImageIso (b : ℤ) (q : ℕ)
    [∀ i, ((single DX G 0).obj i).IsStrictlyGE b] {i j : Iᵒᵖ} (a : i ⟶ j) :
    higherDirectImageDiagramMap γ q cS G (i := i) (j := j) a ≫
        (smallEtalePullbackAb (cS.π.app i)).map
        (singleHigherDirectImageIso (γ.app i) b q (G.obj i)).hom =
      (smallEtalePullbackAb (cS.π.app j)).map
          (singleHigherDirectImageIso (γ.app j) b q (G.obj j)).hom ≫
        (complexHigherDirectImageSystem γ q b (single DX G 0)).pullbackDiagramMap cS
          (i := i) (j := j) a := by
  have k := higherBaseChangeMapAb_comp_singleHigherDirectImageIso (DS.map a) (γ.app j)
    (γ.app i) (DX.map a) (transition_comm γ a) b q (G.obj j) (G.obj i) (G.map a)
  have hk := ((smallEtalePullbackAb (cS.π.app i)).map_comp _ _).symm.trans
    ((congrArg (smallEtalePullbackAb (cS.π.app i)).map k).trans
      ((smallEtalePullbackAb (cS.π.app i)).map_comp _ _))
  have hn := (conePullbackComp cS a).inv.naturality
    (singleHigherDirectImageIso (γ.app j) b q (G.obj j)).hom
  simp only [Functor.comp_map] at hn
  exact comp_comp_eq_of_comp_eq hk hn

omit [IsDirected I (· ≤ ·)] [Nonempty I] [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)] [∀ i, QuasiCompact (γ.app i)]
  [∀ i, QuasiSeparated (γ.app i)] in
/-- The identifications `singleHigherDirectImageIso` commute with the cocone maps. -/
theorem projectionMap_comp_singleHigherDirectImageIso (b : ℤ) (q : ℕ)
    [∀ i, ((single DX G 0).obj i).IsStrictlyGE b]
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj 𝓖) b]
    (i : Iᵒᵖ) :
    projectionMap γ cX cS hcS q 𝓖 G ιG i ≫
        (singleHigherDirectImageIso (limitMorphism γ cX cS hcS) b q 𝓖).hom =
      (smallEtalePullbackAb (cS.π.app i)).map
          (singleHigherDirectImageIso (γ.app i) b q (G.obj i)).hom ≫
        complexLeg γ q b (single DX G 0) cX cS hcS
          ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj 𝓖) (singleι G ιG 0) i :=
  higherBaseChangeMapAb_comp_singleHigherDirectImageIso (cS.π.app i) (γ.app i)
    (limitMorphism γ cX cS hcS) (cX.π.app i) (limitMorphism_comp_π γ cX cS hcS i) b q
    (G.obj i) 𝓖 (ιG i)

include hcX hιG hpres in
/-- **The colimit assertion for a system of sheaves placed in degree zero**, in every degree
`q ≥ 0`: it is [Stacks, Tag 0EYM], read through the identifications
`singleHigherDirectImageIso` of `R^qg_*𝒢` with `H^q(Rg_*𝒢[0])`. -/
theorem isComplexHigherDirectImageColimit_single_zero (b : ℤ) (q : ℕ)
    [∀ i, ((single DX G 0).obj i).IsStrictlyGE b]
    [CochainComplex.IsStrictlyGE ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj 𝓖) b] :
    IsComplexHigherDirectImageColimit γ q b (single DX G 0) cX cS hcS
      ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj 𝓖) (singleι G ιG 0) :=
  (IsSystemColimit.iff_of_isoSystem
    (fun i => (smallEtalePullbackAb (cS.π.app i)).mapIso
      (singleHigherDirectImageIso (γ.app i) b q (G.obj i)))
    (singleHigherDirectImageIso (limitMorphism γ cX cS hcS) b q 𝓖)
    (fun a => higherDirectImageDiagramMap_comp_singleHigherDirectImageIso γ G b q a)
    (fun i => projectionMap_comp_singleHigherDirectImageIso γ hcS G b q i)).1
    (isHigherDirectImageColimit γ hcX hcS q G 𝓖 ιG hιG hpres).isSystemColimit

end Single

end Stacks.EtaleCohomology.LimitHigherDirectImage

end
