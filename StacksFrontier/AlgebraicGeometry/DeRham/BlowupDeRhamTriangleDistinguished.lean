module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangleChain
public import StacksFrontier.Homology.Injectives.Sheaf.ModulesOnRingedSite

/-!
# The blowup triangle of de Rham complexes is distinguished

In the situation of `StacksFrontier.AlgebraicGeometry.DeRham.BlowupDeRhamTriangle`, the four canonical
maps

`Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S}`, `Ω^•_{X/S} ⟶ i_*Ω^•_{Z/S}`, `Rb_*Ω^•_{X'/S} ⟶ i_*Rp_*Ω^•_{E/S}`,
`i_*Ω^•_{Z/S} ⟶ i_*Rp_*Ω^•_{E/S}`

of Section 07HX, with the sign of the last one reversed, form a distinguished triangle

`Ω^•_{X/S} ⟶ Rb_*Ω^•_{X'/S} ⊕ i_*Ω^•_{Z/S} ⟶ i_*Rp_*Ω^•_{E/S} ⟶ Ω^•_{X/S}[1]`

in `D(X, f^{-1}𝒪_S)` ([Stacks, Tag 0FUV]) as soon as the three clauses of [Stacks, Tag 0FUU] hold.
The proof is the source's: the derived unit square of `b_*` along `Ω^•_{X'/S} ⟶ j_*Ω^•_{E/S}` is
homotopy cartesian by clause (3) (`StacksDraft.DerivedUnitSquare.exists_distTriang`, which is the
triangulated argument through [Stacks, Tag 05R0]); clause (1) identifies `b_*Ω^•_{X'/S}` with
`Ω^•_{X/S}`, clause (2) identifies `b_*j_*Ω^•_{E/S} = i_*p_*Ω^•_{E/S}` with `i_*Ω^•_{Z/S}`, and
`i_*`, `j_*` compute their derived functors, `i` and `j` being closed immersions. The
compatibility with the canonical maps, which the source omits, is
`Stacks.DeRham.BlowupTriangle.chain_comp_exceptionalSquareIso` for the second map and the
compatibility of the units with composition ([Stacks, Tag 0D5T]) for the fourth.

## Main results

* `Stacks.DeRham.BlowupTriangle.exists_distTriang_of_isIso`: the triangle is distinguished,
  given the three clauses of [Stacks, Tag 0FUU] in the form they enter the proof.
* `Stacks.DeRham.BlowupTriangle.exists_distTriang_of_shortExact`: the triangle is distinguished,
  given clause (3) of [Stacks, Tag 0FUU] and the short exactness of
  `0 ⟶ Ω^•_{X/S} ⟶ b_*Ω^•_{X'/S} ⊕ i_*Ω^•_{Z/S} ⟶ b_*j_*Ω^•_{E/S} ⟶ 0`; clauses (1) and (2),
  which fail for a centre containing an open subset of `X`, are not needed.

## Implementation notes

All statements are for an arbitrary model of each derived category. The source complexes are
spelled with `Modules`, the derived categories with `ModuleSheaves`; instance search does not
identify the two, so `DerivedCategory.Q` is given its category explicitly wherever it is not
determined by unification, lest a global model be chosen.

## References

* [Stacks Project, Tag 0FUV](https://stacks.math.columbia.edu/tag/0FUV)
* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 05R0](https://stacks.math.columbia.edu/tag/05R0)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction Stacks.DeRhamDirectImage Stacks.DeRhamSmooth

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

namespace Stacks.DeRham.BlowupTriangle

section Triangle

variable {𝒯 : Type*} [Category 𝒯] [Preadditive 𝒯] [HasZeroObject 𝒯] [HasShift 𝒯 ℤ]
  [∀ n : ℤ, (shiftFunctor 𝒯 n).Additive] [Pretriangulated 𝒯] [HasBinaryBiproducts 𝒯]

/-- A distinguished triangle `A ⟶ B₁ ⊞ B₂ ⟶ C ⟶ A[1]` whose first two maps are given by their
components stays distinguished when `A`, `B₂` and `C` are replaced by isomorphic objects and the
components by the maps they correspond to. -/
lemma exists_distTriang_lift_desc_of_iso {A B₁ B₂ C A' B₂' C' : 𝒯} {a : A ⟶ B₁} {b : A ⟶ B₂}
    {c : B₁ ⟶ C} {d : B₂ ⟶ C} {δ : C ⟶ A⟦(1 : ℤ)⟧}
    (h : Triangle.mk (biprod.lift a b) (biprod.desc c d) δ ∈ distTriang 𝒯)
    (eA : A ≅ A') (eB : B₂ ≅ B₂') (eC : C ≅ C') {a' : A' ⟶ B₁} {b' : A' ⟶ B₂'} {c' : B₁ ⟶ C'}
    {d' : B₂' ⟶ C'} (ha : eA.hom ≫ a' = a) (hb : eA.hom ≫ b' = b ≫ eB.hom) (hc : c ≫ eC.hom = c')
    (hd : d ≫ eC.hom = eB.hom ≫ d') :
    ∃ δ' : C' ⟶ A'⟦(1 : ℤ)⟧,
      Triangle.mk (biprod.lift a' b') (biprod.desc c' d') δ' ∈ distTriang 𝒯 := by
  refine ⟨eC.inv ≫ δ ≫ eA.hom⟦(1 : ℤ)⟧', isomorphic_distinguished _ h _ ?_⟩
  refine Triangle.isoMk _ _ eA.symm (biprod.mapIso (Iso.refl B₁) eB.symm) eC.symm ?_ ?_ ?_
  · apply biprod.hom_ext
    · simp [← ha]
    · simp [← cancel_epi eA.hom, reassoc_of% hb]
  · apply biprod.hom_ext'
    · simp [← hc]
    · simp [← cancel_epi eB.hom, ← reassoc_of% hd]
  · simp [← Functor.map_comp]

end Triangle

open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase f))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (blowupMap i ≫ f)))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (i ≫ f)))]
  [HasDerivedCategory (ModuleSheaves (inverseImageBase (exceptionalStructure f i)))]

/-- The de Rham complex of the blowup, as a complex of module sheaves, is concentrated in
degrees `≥ 0`. -/
private lemma isStrictlyGE_blowup_deRham {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    [IsClosedImmersion i] :
    CochainComplex.IsStrictlyGE (show CochainComplex
      (ModuleSheaves (inverseImageBase (blowupMap i ≫ f))) ℤ from
        deRhamCochainComplex (blowupMap i ≫ f)) 0 :=
  isStrictlyGE_deRhamCochainComplex _

/-- The pushforward `j_*Ω^•_{E/S}` of the de Rham complex of the exceptional divisor is
concentrated in degrees `≥ 0`. -/
private lemma isStrictlyGE_pushforward_exceptional_deRham {S X Z : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) [IsClosedImmersion i] :
    CochainComplex.IsStrictlyGE (((RingedSpaceModuleAdjunction.modulePushforward
      (coefficientInclusion f i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (deRhamCochainComplex (exceptionalStructure f i))) 0 :=
  ⟨fun n hn => Functor.map_isZero
    (RingedSpaceModuleAdjunction.modulePushforward (coefficientInclusion f i))
    ((isStrictlyGE_deRhamCochainComplex (exceptionalStructure f i)).isZero n hn)⟩

/-- The derived unit square of the blowup along the canonical map `Ω^•_{X'/S} ⟶ j_*Ω^•_{E/S}` is
homotopy cartesian as soon as `Rb_*` of that map is invertible on cohomology sheaves in positive
degrees, termwise. -/
lemma exists_distTriang_inclusionChain
    (h : ∀ p q : ℤ, 0 < q → IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((derivedPushforward (coefficientBlowup f i)).map (DerivedCategory.Q.map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ((inclusionChain f i).f p)))))) :
    ∃ δ, Triangle.mk
        (biprod.lift (unit (coefficientBlowup f i) (deRhamCochainComplex (blowupMap i ≫ f)))
          (DerivedCategory.Q.map (((RingedSpaceModuleAdjunction.modulePushforward
            (coefficientBlowup f i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
              (inclusionChain f i))))
        (biprod.desc ((derivedPushforward (coefficientBlowup f i)).map
            (DerivedCategory.Q.map (inclusionChain f i)))
          (-unit (coefficientBlowup f i) (((RingedSpaceModuleAdjunction.modulePushforward
            (coefficientInclusion f i)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
              (deRhamCochainComplex (exceptionalStructure f i))))) δ ∈ distTriang _ := by
  have := isStrictlyGE_blowup_deRham f i
  have := isStrictlyGE_pushforward_exceptional_deRham f i
  exact StacksDraft.DerivedUnitSquare.exists_distTriang
    (B := RingedSpaceModuleAdjunction.modulePushforward (coefficientBlowup f i))
    (u := derivedPushforwardUnit (coefficientBlowup f i))
    (hu := fun I hI => isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI)
    (Stacks.Injectives.sheafOfModules_hasFunctorialInjectiveEmbeddings _ _) (inclusionChain f i) h

/-- The coefficient-space morphism of a closed immersion is a closed embedding. -/
lemma isClosedEmbedding_relativeBase_base {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) (s : Y ⟶ S)
    [IsClosedImmersion g] : Topology.IsClosedEmbedding (relativeBase g s).hom.base :=
  g.isClosedEmbedding

/-- The coefficient-space morphism of the inclusion of the exceptional divisor is a closed
embedding. -/
lemma isClosedEmbedding_coefficientInclusion_base :
    Topology.IsClosedEmbedding (coefficientInclusion f i).hom.base := by
  have key : ∀ {A A' B : RingedSpace.{u, u}} (h : A = A') (g : A' ⟶ B),
      Topology.IsClosedEmbedding g.hom.base →
        Topology.IsClosedEmbedding (eqToHom h ≫ g).hom.base := by
    rintro A A' B rfl g hg
    simpa using hg
  have : IsClosedImmersion (exceptionalInclusion i) :=
    inferInstanceAs (IsClosedImmersion (Stacks.Blowup.exceptionalIdeal i.ker).subschemeι)
  exact key _ _ (isClosedEmbedding_relativeBase_base _ _)

/-- The comparison `Rb_*j_*L ⟶ Ri_*Rp_*L` of the derived direct images of a complex on the
exceptional divisor along the two sides of the blowup square: `Rb_*` of the unit `j_*L ⟶ Rj_*L`,
followed by `Rb_*Rj_* ≅ R(j ≫ b)_* = R(p ≫ i)_* ≅ Ri_*Rp_*`. -/
def exceptionalDerivedHom
    (L : CochainComplex (ModuleSheaves (inverseImageBase (exceptionalStructure f i))) ℤ) :
    (derivedPushforward (coefficientBlowup f i)).obj (DerivedCategory.Q.obj
        (((RingedSpaceModuleAdjunction.modulePushforward
          (coefficientInclusion f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L)) ⟶
      (derivedPushforward (coefficientCentre f i)).obj
        ((derivedPushforward (coefficientProjection f i)).obj (DerivedCategory.Q.obj L)) :=
  (derivedPushforward (coefficientBlowup f i)).map (unit (coefficientInclusion f i) L) ≫
    (compIso (coefficientInclusion f i) (coefficientBlowup f i)).inv.app (DerivedCategory.Q.obj L) ≫
    eqToHom (congrArg (fun g => (derivedPushforward g).obj (DerivedCategory.Q.obj L))
      (coefficientInclusion_comp_coefficientBlowup f i)) ≫
    (compIso (coefficientProjection f i) (coefficientCentre f i)).hom.app (DerivedCategory.Q.obj L)

/-- `j_*` computes `Rj_*`, `j` being a closed immersion, so `exceptionalDerivedHom` is
invertible. -/
instance isIso_exceptionalDerivedHom
    (L : CochainComplex (ModuleSheaves (inverseImageBase (exceptionalStructure f i))) ℤ) :
    IsIso (exceptionalDerivedHom f i L) := by
  haveI := isIso_unit_of_isClosedEmbedding _ (isClosedEmbedding_coefficientInclusion_base f i) L
  unfold exceptionalDerivedHom
  infer_instance

-- The statements mix the `Modules` and `ModuleSheaves` spellings of the categories of modules,
-- which agree only at default transparency; these make them agree for unification.
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose SheafedSpace.sheaf
  AlgebraicGeometry.RingedSpace.inverseImage in
/-- **The blowup triangle, from the three clauses of [Stacks, Tag 0FUU]**: if the canonical maps
`Ω^•_{X/S} ⟶ b_*Ω^•_{X'/S}` and `Ω^•_{Z/S} ⟶ p_*Ω^•_{E/S}` are isomorphisms of complexes and
`Rb_*` of `Ω^•_{X'/S} ⟶ j_*Ω^•_{E/S}` is invertible on cohomology sheaves in positive degrees,
termwise, then the four canonical maps, with the sign of the last one reversed, form a
distinguished triangle. -/
theorem exists_distTriang_of_isIso (h₁ : IsIso (chain (blowupMap i) f))
    (h₂ : IsIso (chain (exceptionalProjection i) (i ≫ f)))
    (h₃ : ∀ p q : ℤ, 0 < q → IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((derivedPushforward (coefficientBlowup f i)).map (DerivedCategory.Q.map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ((inclusionChain f i).f p)))))) :
    ∃ δ, Triangle.mk (biprod.lift (toBlowUp f i) (toCentre f i))
      (biprod.desc (blowUpToExceptional f i) (-centreToExceptional f i)) δ ∈ distTriang _ := by
  obtain ⟨δ, hδ⟩ := exists_distTriang_inclusionChain f i h₃
  have : IsIso ((DerivedCategory.Q (C := ModuleSheaves (inverseImageBase f))).map
      (chain (blowupMap i) f)) :=
    Functor.map_isIso _ _
  have : IsIso (((RingedSpaceModuleAdjunction.modulePushforward
      (coefficientCentre f i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
        (chain (exceptionalProjection i) (i ≫ f))) :=
    Functor.map_isIso _ _
  have : IsIso ((DerivedCategory.Q (C := ModuleSheaves (inverseImageBase f))).map
      (((RingedSpaceModuleAdjunction.modulePushforward
        (coefficientCentre f i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (chain (exceptionalProjection i) (i ≫ f)))) :=
    Functor.map_isIso _ _
  have := isIso_unit_of_isClosedEmbedding _ (isClosedEmbedding_relativeBase_base i f)
    (deRhamCochainComplex (i ≫ f))
  refine exists_distTriang_lift_desc_of_iso hδ
    (asIso ((DerivedCategory.Q (C := ModuleSheaves (inverseImageBase f))).map
      (chain (blowupMap i) f))).symm
    ((DerivedCategory.Q (C := ModuleSheaves (inverseImageBase f))).mapIso
        (exceptionalSquareIso f i (deRhamCochainComplex (exceptionalStructure f i))) ≪≫
      (asIso ((DerivedCategory.Q (C := ModuleSheaves (inverseImageBase f))).map
        (((RingedSpaceModuleAdjunction.modulePushforward
          (coefficientCentre f i)).mapHomologicalComplex (ComplexShape.up ℤ)).map
            (chain (exceptionalProjection i) (i ≫ f))))).symm ≪≫
      asIso (unit (coefficientCentre f i) (deRhamCochainComplex (i ≫ f))))
    (asIso (exceptionalDerivedHom f i (deRhamCochainComplex (exceptionalStructure f i))))
      ?_ ?_ ?_ ?_
  · exact IsIso.inv_hom_id_assoc _ _
  · refine (IsIso.inv_comp_eq _).2 ?_
    have h2 := congrArg (DerivedCategory.Q (C := ModuleSheaves (inverseImageBase f))).map
      (chain_comp_exceptionalSquareIso f i)
    simp only [Functor.map_comp] at h2
    simp only [Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, asIso_hom, asIso_inv,
      reassoc_of% h2, IsIso.hom_inv_id_assoc, toCentre]
  · simp only [asIso_hom, exceptionalDerivedHom, blowUpToExceptional, Functor.map_comp,
      Category.assoc]
  · simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_inj]
    have hu1 := unit_comp_map_unit (coefficientInclusion f i) (coefficientBlowup f i)
      (deRhamCochainComplex (exceptionalStructure f i))
    have hu2 := unit_comp_map_unit (coefficientProjection f i) (coefficientCentre f i)
      (deRhamCochainComplex (exceptionalStructure f i))
    have ht := unit_comp_eqToHom (coefficientInclusion_comp_coefficientBlowup f i)
      (deRhamCochainComplex (exceptionalStructure f i))
    have hn := StacksDraft.DerivedUnitSquare.unitQ_naturality
      (RingedSpaceModuleAdjunction.modulePushforward (coefficientCentre f i))
      (derivedPushforwardUnit (coefficientCentre f i)) (chain (exceptionalProjection i) (i ≫ f))
    simp only [asIso_hom, exceptionalDerivedHom, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom,
      asIso_inv, centreToExceptional, Functor.map_comp, Category.assoc, reassoc_of% hu1,
      Iso.hom_inv_id_app_assoc, reassoc_of% ht]
    simp only [← reassoc_of% hn, IsIso.inv_hom_id_assoc, reassoc_of% hu2,
      ← Functor.map_comp_assoc, mapHomologicalComplexCompIso_modulePushforwardComp_hom_app,
      exceptionalSquareIso_hom, eqToHom_trans]
    refine Eq.trans ?_ (congrArg (fun t => DerivedCategory.Q.map (eqToHom _) ≫ t) hu2).symm
    simp only [mapHomologicalComplexCompIso_modulePushforwardComp_hom_app,
      ← Functor.map_comp_assoc, eqToHom_trans]

/-- The map `i_*Ω^•_{Z/S} ⟶ i_*p_*Ω^•_{E/S} = b_*j_*Ω^•_{E/S}`. -/
def centreToExceptionalChain :
    ((RingedSpaceModuleAdjunction.modulePushforward (coefficientCentre f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (deRhamCochainComplex (i ≫ f)) ⟶
      ((RingedSpaceModuleAdjunction.modulePushforward (coefficientBlowup f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
      (((RingedSpaceModuleAdjunction.modulePushforward
        (coefficientInclusion f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (deRhamCochainComplex (exceptionalStructure f i))) :=
  ((RingedSpaceModuleAdjunction.modulePushforward (coefficientCentre f i)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (chain (exceptionalProjection i) (i ≫ f)) ≫
    (exceptionalSquareIso f i (deRhamCochainComplex (exceptionalStructure f i))).inv

/-- The square of complexes `Ω^•_{X/S} ⟶ b_*Ω^•_{X'/S} ⟶ b_*j_*Ω^•_{E/S}`,
`Ω^•_{X/S} ⟶ i_*Ω^•_{Z/S} ⟶ b_*j_*Ω^•_{E/S}` commutes. -/
lemma chain_comp_inclusionChain :
    chain (blowupMap i) f ≫
        ((RingedSpaceModuleAdjunction.modulePushforward
          (coefficientBlowup f i)).mapHomologicalComplex
          (ComplexShape.up ℤ)).map (inclusionChain f i) =
      chain i f ≫ centreToExceptionalChain f i :=
  ((Iso.eq_comp_inv _).2 ((Category.assoc _ _ _).trans
    (chain_comp_exceptionalSquareIso f i))).trans (Category.assoc _ _ _)

/-- The short complex `Ω^•_{X/S} ⟶ b_*Ω^•_{X'/S} ⊞ i_*Ω^•_{Z/S} ⟶ b_*j_*Ω^•_{E/S}` of complexes of
`f^{-1}𝒪_S`-modules attached to the blowup square. -/
def blowupShortComplex :
    ShortComplex (CochainComplex (ModuleSheaves (inverseImageBase f)) ℤ) :=
  (CommSq.mk (C := CochainComplex (ModuleSheaves (inverseImageBase f)) ℤ)
    (chain_comp_inclusionChain f i)).shortComplex

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose SheafedSpace.sheaf
  AlgebraicGeometry.RingedSpace.inverseImage in
/-- **The blowup triangle, for a centre of arbitrary codimension**: if the sequence
`0 ⟶ Ω^•_{X/S} ⟶ b_*Ω^•_{X'/S} ⊕ i_*Ω^•_{Z/S} ⟶ b_*j_*Ω^•_{E/S} ⟶ 0` of complexes is short exact
and `Rb_*` of `Ω^•_{X'/S} ⟶ j_*Ω^•_{E/S}` is invertible on cohomology sheaves in positive degrees,
termwise, then the four canonical maps, with the sign of the last one reversed, form a
distinguished triangle. Unlike `exists_distTriang_of_isIso`, this does not ask the maps
`Ω^•_{X/S} ⟶ b_*Ω^•_{X'/S}` and `Ω^•_{Z/S} ⟶ p_*Ω^•_{E/S}` to be invertible, which fails where
the centre contains an open subset of `X`. -/
theorem exists_distTriang_of_shortExact (hG : (blowupShortComplex f i).ShortExact)
    (h₃ : ∀ p q : ℤ, 0 < q → IsIso ((DerivedCategory.homologyFunctor _ q).map
      ((derivedPushforward (coefficientBlowup f i)).map (DerivedCategory.Q.map
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).map ((inclusionChain f i).f p)))))) :
    ∃ δ, Triangle.mk (biprod.lift (toBlowUp f i) (toCentre f i))
      (biprod.desc (blowUpToExceptional f i) (-centreToExceptional f i)) δ ∈ distTriang _ := by
  let sq := CommSq.mk (C := CochainComplex (ModuleSheaves (inverseImageBase f)) ℤ)
    (chain_comp_inclusionChain f i)
  have hsq : IsPushout (chain (blowupMap i) f) (chain i f)
      (((RingedSpaceModuleAdjunction.modulePushforward
        (coefficientBlowup f i)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map (inclusionChain f i)) (centreToExceptionalChain f i) :=
    { toCommSq := sq
      isColimit' := ⟨sq.isColimitEquivIsColimitCokernelCofork.symm hG.gIsCokernel⟩ }
  have := isStrictlyGE_blowup_deRham f i
  have := isStrictlyGE_pushforward_exceptional_deRham f i
  obtain ⟨δ, hδ⟩ := StacksDraft.DerivedUnitSquare.exists_distTriang_of_isPushout
    (B := RingedSpaceModuleAdjunction.modulePushforward (coefficientBlowup f i))
    (u := derivedPushforwardUnit (coefficientBlowup f i))
    (hu := fun I hI => isIso_derivedPushforwardUnit_app_of_isKInjective _ I hI)
    (Stacks.Injectives.sheafOfModules_hasFunctorialInjectiveEmbeddings _ _) (inclusionChain f i) h₃
    _ _ _ hsq hG.mono_f
  have := isIso_unit_of_isClosedEmbedding _ (isClosedEmbedding_relativeBase_base i f)
    (deRhamCochainComplex (i ≫ f))
  refine exists_distTriang_lift_desc_of_iso hδ (Iso.refl _)
    (asIso (unit (coefficientCentre f i) (deRhamCochainComplex (i ≫ f))))
    (asIso (exceptionalDerivedHom f i (deRhamCochainComplex (exceptionalStructure f i))))
    ?_ ?_ ?_ ?_
  · exact Category.id_comp _
  · exact Category.id_comp _
  · simp only [asIso_hom, exceptionalDerivedHom, blowUpToExceptional, Functor.map_comp,
      Category.assoc]
  · simp only [Preadditive.neg_comp, Preadditive.comp_neg, neg_inj]
    have hu1 := unit_comp_map_unit (coefficientInclusion f i) (coefficientBlowup f i)
      (deRhamCochainComplex (exceptionalStructure f i))
    have hu2 := unit_comp_map_unit (coefficientProjection f i) (coefficientCentre f i)
      (deRhamCochainComplex (exceptionalStructure f i))
    have ht := unit_comp_eqToHom (coefficientInclusion_comp_coefficientBlowup f i)
      (deRhamCochainComplex (exceptionalStructure f i))
    have hn := StacksDraft.DerivedUnitSquare.unitQ_naturality
      (RingedSpaceModuleAdjunction.modulePushforward (coefficientCentre f i))
      (derivedPushforwardUnit (coefficientCentre f i)) (chain (exceptionalProjection i) (i ≫ f))
    have hinv : (exceptionalSquareIso f i (deRhamCochainComplex (exceptionalStructure f i))).inv =
        eqToHom (exceptionalSquare_eq f i
          (deRhamCochainComplex (exceptionalStructure f i))).symm := by
      rw [← cancel_epi (exceptionalSquareIso f i _).hom, Iso.hom_inv_id, exceptionalSquareIso_hom,
        eqToHom_trans, eqToHom_refl]
    simp only [asIso_hom, exceptionalDerivedHom, centreToExceptionalChain, centreToExceptional,
      Functor.map_comp, Category.assoc, reassoc_of% hu1, Iso.hom_inv_id_app_assoc, reassoc_of% ht,
      ← reassoc_of% hn, reassoc_of% hu2]
    congr 1
    refine Eq.trans ?_ hu2.symm
    simp only [hinv, mapHomologicalComplexCompIso_modulePushforwardComp_hom_app,
      ← Functor.map_comp_assoc, eqToHom_trans]

end Stacks.DeRham.BlowupTriangle

end
