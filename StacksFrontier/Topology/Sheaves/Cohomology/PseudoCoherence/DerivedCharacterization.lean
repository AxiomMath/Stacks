module

public import StacksFrontier.Topology.Sheaves.Cohomology.StrictlyPerfectRestriction.NestedRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ExactFunctorDerivedHomology
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Pseudo-coherence from local strictly perfect approximations

Tag 08CC compares the two ways a complex of `O_X`-modules can be `m`-pseudo-coherent: by
admitting local strictly perfect approximations through morphisms of complexes, or by admitting
them through morphisms in the derived category. The two agree, and the condition depends only on
the derived object.

## Main results

* `isPseudoCoherentFrom_of_local_derived_approximation` is Tag 08CC part (1): local
  strictly perfect approximations in the derived category make a derived object
  `m`-pseudo-coherent.
* `Stacks.PseudoCoherence.DerivedCharacterization.isPseudoCoherentComplexFrom_of_iso` is Tag 08CC
  part (2): every complex
  representing an `m`-pseudo-coherent derived object is itself `m`-pseudo-coherent.

## Implementation notes

The space, ring and module universes all coincide. This is the universe signature already forced
on Tag 08C6 and Tag 08C7, hence on Tag 08C9, on which both parts rest; at matching universes all
four sheafification instances of the Tag 08CB statement hold automatically and so are not hypotheses.
The derived-category universe of `X` and that of its open restrictions are independent.

Both parts reduce to
  `Stacks.PseudoCoherence.DerivedCharacterization.local_derived_approximation_at`, which turns a
    derived
approximation over `U` into a complex-level one over a smaller open. The engine is Tag 08C9 part
(1) (`Stacks.StrictlyPerfect.LocalRepresentation.exists_local_complex_map`), applied over
  `X.restrict U`; it produces a morphism
of complexes over an open `V` of `X.restrict U`, which
  `AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedRestrictionComplexIso`
carries to the restriction of `X` to the image of `V` in `X`. Part (2) additionally transports
the comparison isomorphism of the two representatives through the restriction functor, which is
exact, so it stays an isomorphism on homology.

The transfer of the two conditions on homology from the derived morphism to its complex-level
representative is `Stacks.PseudoCoherence.DerivedCharacterization.localDerivedMap_homologyBounds`,
  stated over abstract abelian
categories: the content is formal exactness, and elaborated against the ringed-space vocabulary
the same proof costs many times the default heartbeat budget.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08CC](https://stacks.math.columbia.edu/tag/08CC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect
open Stacks.Cohomology.SupportedComplexes (exactFunctorDerivedHomologyIso)

namespace Stacks.PseudoCoherence.DerivedCharacterization

universe u d d'

section Abstract

universe v₁ v₂ u₁ u₂ w₁ w₂

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] {D : Type u₂} [Category.{v₂} D] [Abelian D]

/-- Isomorphic functors agree on epimorphy of images. -/
theorem epi_map_iff_of_natIso {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
    {F G : A ⥤ B} (e : F ≅ G) {M N : A} (f : M ⟶ N) : Epi (F.map f) ↔ Epi (G.map f) := by
  constructor <;> intro
  · rw [← NatIso.naturality_1 e f]
    infer_instance
  · rw [← NatIso.naturality_2 e f]
    infer_instance

/-- An exact functor preserves surjectivity on homology. -/
theorem epi_homologyMap_mapHomologicalComplex (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (i : ℤ)
    (hf : Epi (HomologicalComplex.homologyMap f i)) :
    Epi (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) i) :=
  (epi_map_iff_of_natIso (mapHomologicalComplexHomologyIso F (ComplexShape.up ℤ) i) f).mpr
    (inferInstance : Epi (F.map (HomologicalComplex.homologyMap f i)))

/-- An exact functor preserves isomorphy on homology. -/
theorem isIso_homologyMap_mapHomologicalComplex (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P Q : CochainComplex C ℤ} (f : P ⟶ Q) (i : ℤ)
    (hf : IsIso (HomologicalComplex.homologyMap f i)) :
    IsIso (HomologicalComplex.homologyMap
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) i) :=
  (NatIso.isIso_map_iff (mapHomologicalComplexHomologyIso F (ComplexShape.up ℤ) i) f).mpr
    (inferInstance : IsIso (F.map (HomologicalComplex.homologyMap f i)))

/-- The two homology conditions pass between a complex map and its image in the derived category. -/
private theorem homologyBounds_Q_map_iff [HasDerivedCategory.{w₁} C] {P Q : CochainComplex C ℤ}
    (α : P ⟶ Q) (m j : ℤ) :
    ((m < j → IsIso ((DerivedCategory.homologyFunctor C j).map (DerivedCategory.Q.map α))) ∧
      Epi ((DerivedCategory.homologyFunctor C m).map (DerivedCategory.Q.map α))) ↔
    ((m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
      Epi (HomologicalComplex.homologyMap α m)) :=
  and_congr (imp_congr_right fun _ =>
      NatIso.isIso_map_iff (DerivedCategory.homologyFunctorFactors C j) α)
    (epi_map_iff_of_natIso (DerivedCategory.homologyFunctorFactors C m) α)

/-- **A local representative of a derived morphism inherits its behaviour on homology.** If `β`
realises the image of `α` under an exact functor `F`, then `F` carries the two hypotheses on the
homology of `α` to the corresponding statements about the homology of `β`. -/
theorem localDerivedMap_homologyBounds [HasDerivedCategory.{w₁} C] [HasDerivedCategory.{w₂} D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (P Q : CochainComplex C ℤ)
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj Q)
    (β : ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) ⟶
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q))
    (hβ : F.mapDerivedCategory.map α ≫ F.mapDerivedCategoryFactors.hom.app Q =
      F.mapDerivedCategoryFactors.hom.app P ≫ DerivedCategory.Q.map β)
    (m j : ℤ) :
    (m < j → IsIso ((DerivedCategory.homologyFunctor C j).map α)) →
    Epi ((DerivedCategory.homologyFunctor C m).map α) →
    (m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
      Epi (HomologicalComplex.homologyMap β m) := by
  intro hαj hαm
  have hIso (hj : m < j) : IsIso ((DerivedCategory.homologyFunctor D j).map
        (F.mapDerivedCategory.map α)) := by
    apply (NatIso.isIso_map_iff (exactFunctorDerivedHomologyIso F j) α).mpr
    show IsIso (F.map ((DerivedCategory.homologyFunctor C j).map α))
    have := hαj hj
    exact Functor.map_isIso F _
  have hEpi : Epi ((DerivedCategory.homologyFunctor D m).map (F.mapDerivedCategory.map α)) := by
    apply (epi_map_iff_of_natIso (exactFunctorDerivedHomologyIso F m) α).mpr
    show Epi (F.map ((DerivedCategory.homologyFunctor C m).map α))
    exact preserves_epi_of_preservesColimit F _
  have hcomm (i : ℤ) :
      (DerivedCategory.homologyFunctor D i).map (F.mapDerivedCategory.map α) ≫
          (DerivedCategory.homologyFunctor D i).map
            (F.mapDerivedCategoryFactors.hom.app Q) =
        (DerivedCategory.homologyFunctor D i).map
            (F.mapDerivedCategoryFactors.hom.app P) ≫
          (DerivedCategory.homologyFunctor D i).map (DerivedCategory.Q.map β) := by
    simpa only [Functor.map_comp] using congrArg (DerivedCategory.homologyFunctor D i).map hβ
  have hIsoQ (hj : m < j) :
      IsIso ((DerivedCategory.homologyFunctor D j).map (DerivedCategory.Q.map β)) := by
    have hcomp : IsIso ((DerivedCategory.homologyFunctor D j).map
        (F.mapDerivedCategoryFactors.hom.app P) ≫
        (DerivedCategory.homologyFunctor D j).map (DerivedCategory.Q.map β)) := by
      rw [← hcomm j]
      have := hIso hj
      infer_instance
    exact IsIso.of_isIso_comp_left
      ((DerivedCategory.homologyFunctor D j).map
        (F.mapDerivedCategoryFactors.hom.app P)) _
  have hEpiQ : Epi ((DerivedCategory.homologyFunctor D m).map (DerivedCategory.Q.map β)) := by
    have hcomp : Epi ((DerivedCategory.homologyFunctor D m).map
        (F.mapDerivedCategoryFactors.hom.app P) ≫
        (DerivedCategory.homologyFunctor D m).map (DerivedCategory.Q.map β)) := by
      rw [← hcomm m]
      exact epi_comp' hEpi (IsIso.epi_of_iso _)
    exact (epi_comp_iff_of_epi _ _).mp hcomp
  exact (homologyBounds_Q_map_iff β m j).mp ⟨hIsoQ, hEpiQ⟩

end Abstract

section Clauses

variable {X : RingedSpace.{u, u}}

/-- **A local strictly perfect approximation in the derived category shrinks to one by a
morphism of complexes.** Tag 08C9 part (1), applied over `X.restrict U`, realises `α` by a
morphism of complexes over an open `V` of `X.restrict U`; transporting along
`AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso` lands it over the restriction of `X`
  to the image of `V`. -/
theorem local_derived_approximation_at (m : ℤ) (K : CochainComplex (OXMod.{u} X) ℤ)
    (x : X.carrier) (U : Opens X.carrier) (hxU : x ∈ U)
    [HasDerivedCategory.{d'} (OXMod.{u} (X.restrict U.isOpenEmbedding))]
    (P : CochainComplex (OXMod.{u} (X.restrict U.isOpenEmbedding)) ℤ)
    (hP : IsStrictlyPerfect P)
    (α : DerivedCategory.Q.obj P ⟶ DerivedCategory.Q.obj
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex K U))
    (hαgt : ∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map α))
    (hαepi : Epi ((DerivedCategory.homologyFunctor _ m).map α)) :
    ∃ W : Opens X.carrier, x ∈ W ∧
      ∃ P' : CochainComplex (OXMod.{u} (X.restrict W.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P' ∧
        ∃ β : P' ⟶ AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex K W,
          (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
          Epi (HomologicalComplex.homologyMap β m) := by
  let : ∀ V : Opens (X.restrict U.isOpenEmbedding).carrier,
      HasDerivedCategory
        (OXMod.{u} ((X.restrict U.isOpenEmbedding).restrict V.isOpenEmbedding)) :=
    fun _ => HasDerivedCategory.standard _
  obtain ⟨V, hxV, hadd, hlim, hcolim, β, hβ⟩ :=
    Stacks.StrictlyPerfect.LocalRepresentation.exists_local_complex_map (X := X.restrict
      U.isOpenEmbedding) hP α ⟨x, hxU⟩
  let R := AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u} (X.restrict
    U.isOpenEmbedding) V
  have : R.Additive := hadd
  have : PreservesFiniteLimits R := hlim
  have : PreservesFiniteColimits R := hcolim
  have hb (j : ℤ) : (m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
      Epi (HomologicalComplex.homologyMap β m) :=
    localDerivedMap_homologyBounds (F := R) P
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex K U) α β hβ m j
      (hαgt j) hαepi
  let W : Opens X.carrier := U.isOpenEmbedding.functor.obj V
  let T := (AlgebraicGeometry.RingedSpace.PseudoCoherence.moduleEquivOfIso
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso X U V)).functor
  let Tc := T.mapHomologicalComplex (ComplexShape.up ℤ)
  have : PreservesFiniteLimits T :=
    AlgebraicGeometry.RingedSpace.PseudoCoherence.moduleEquivOfIso_preservesFiniteLimits
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso X U V)
  have : PreservesFiniteColimits T :=
    AlgebraicGeometry.RingedSpace.PseudoCoherence.moduleEquivOfIso_preservesFiniteColimits
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedOpenIso X U V)
  let eK := AlgebraicGeometry.RingedSpace.PseudoCoherence.nestedRestrictionComplexIso X U V K
  have hIsoK (j : ℤ) : IsIso (HomologicalComplex.homologyMap eK.hom j) := by
    show IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map eK.hom)
    exact Functor.map_isIso _ _
  refine ⟨W, ⟨⟨x, hxU⟩, hxV, rfl⟩, Tc.obj
    (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex P V), ?_,
    Tc.map β ≫ eK.hom, ?_, ?_⟩
  · exact AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_moduleEquiv _ _
      (AlgebraicGeometry.RingedSpace.PseudoCoherence.isStrictlyPerfect_restrictComplex (X.restrict
        U.isOpenEmbedding) V hP)
  · intro j hj
    rw [HomologicalComplex.homologyMap_comp]
    have := hIsoK j
    have := isIso_homologyMap_mapHomologicalComplex T β j ((hb j).1 hj)
    infer_instance
  · rw [HomologicalComplex.homologyMap_comp]
    have := hIsoK m
    exact epi_comp' (epi_homologyMap_mapHomologicalComplex T β m (hb m).2)
      (IsIso.epi_of_iso _)

variable [HasDerivedCategory.{d} (OXMod.{u} X)]

/-- **Tag 08CC part (1).** Local strictly perfect approximations in the derived category make a
derived object `m`-pseudo-coherent. -/
@[stacks 08CC "part (1)"]
theorem isPseudoCoherentFrom_of_local_derived_approximation
    [∀ U : Opens X.carrier,
      HasDerivedCategory.{d'} (OXMod.{u} (X.restrict U.isOpenEmbedding))]
    (E : DerivedCategory (OXMod.{u} X)) (m : ℤ) (K : CochainComplex (OXMod.{u} X) ℤ)
    (e : DerivedCategory.Q.obj K ≅ E)
    (h : ∀ x : X.carrier, ∃ U : Opens X.carrier, x ∈ U ∧
      ∃ P : CochainComplex (OXMod.{u} (X.restrict U.isOpenEmbedding)) ℤ,
        IsStrictlyPerfect P ∧
        ∃ α : DerivedCategory.Q.obj P ⟶
          DerivedCategory.Q.obj (AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplex K U),
          (∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map α)) ∧
          Epi ((DerivedCategory.homologyFunctor _ m).map α)) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentFrom (X := X) E m := by
  refine ⟨K, fun x => ?_, ⟨e⟩⟩
  obtain ⟨U, hxU, P, hP, α, hαgt, hαepi⟩ := h x
  exact local_derived_approximation_at m K x U hxU P hP α hαgt hαepi

/-- **Tag 08CC part (2).** Every complex representing an `m`-pseudo-coherent derived object is
`m`-pseudo-coherent. -/
@[stacks 08CC "part (2)", sga "6 I 2.2" "a)"]
theorem isPseudoCoherentComplexFrom_of_iso (E : DerivedCategory (OXMod.{u} X)) (m : ℤ)
    (hE : AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentFrom (X := X) E m)
    (K : CochainComplex (OXMod.{u} X) ℤ) (e : DerivedCategory.Q.obj K ≅ E) :
    AlgebraicGeometry.RingedSpace.PseudoCoherence.IsPseudoCoherentComplexFrom (X := X) K m := by
  obtain ⟨K₀, hK₀, ⟨e₀⟩⟩ := hE
  let δ : DerivedCategory.Q.obj K₀ ⟶ DerivedCategory.Q.obj K := e₀.hom ≫ e.inv
  intro x
  obtain ⟨U, hxU, P, hP, α, hαgt, hαepi⟩ := hK₀ x
  let : HasDerivedCategory (OXMod.{u} (X.restrict U.isOpenEmbedding)) :=
    HasDerivedCategory.standard _
  let R := AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules.{u} X U
  have : PreservesFiniteLimits R :=
    Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteLimits X U
  have : PreservesFiniteColimits R :=
    Stacks.StrictlyPerfect.LocalRepresentation.restrictModules_preservesFiniteColimits X U
  let Rc := R.mapHomologicalComplex (ComplexShape.up ℤ)
  let δU : DerivedCategory.Q.obj (Rc.obj K₀) ⟶ DerivedCategory.Q.obj (Rc.obj K) :=
    R.mapDerivedCategoryFactors.inv.app K₀ ≫
      R.mapDerivedCategory.map δ ≫ R.mapDerivedCategoryFactors.hom.app K
  have : IsIso δU := by
    dsimp only [δU]
    infer_instance
  let αU := DerivedCategory.Q.map α ≫ δU
  have hαQ (j : ℤ) := (homologyBounds_Q_map_iff α m j).mpr ⟨hαgt j, hαepi⟩
  have hαUgt : ∀ j : ℤ, m < j → IsIso ((DerivedCategory.homologyFunctor _ j).map αU) := by
    intro j hj
    have := (hαQ j).1 hj
    simp only [αU, Functor.map_comp]
    infer_instance
  have hαUepi : Epi ((DerivedCategory.homologyFunctor _ m).map αU) := by
    have := (hαQ m).2
    simp only [αU, Functor.map_comp]
    infer_instance
  exact local_derived_approximation_at m K x U hxU P hP αU hαUgt hαUepi

end Clauses

end Stacks.PseudoCoherence.DerivedCharacterization

end
