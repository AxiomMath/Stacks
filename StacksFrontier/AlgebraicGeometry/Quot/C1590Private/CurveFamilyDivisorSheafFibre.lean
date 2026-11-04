module

public import StacksFrontier.AlgebraicGeometry.Spaces.CanonicalSectionRegular
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackLeftUnitality
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackUnitHom
public import StacksFrontier.AlgebraicGeometry.Spaces.IdealSheafMapStructureSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafCoherence
public import StacksFrontier.AlgebraicGeometry.Divisors.SectionContractionPairing
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedIdealModuleComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedTwistedCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.AffineCentre
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleMapClosedFibre
public import StacksFrontier.AlgebraicGeometry.Conormal.IdealSheafDataComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.ConormalModuleBaseChangeEpi
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackComparisonUnit
public import StacksFrontier.AlgebraicGeometry.Quot.PicardFunctor
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.DualizingDivisor.DivisorSections
public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionZeroScheme
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.InternalHomSections
public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsPullbackBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.AssociatedModuleAwayFromSupport
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.RepresentedFirstCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilySectionsLift
public import StacksFrontier.AlgebraicGeometry.InvertibleDual.Evaluation
public import StacksFrontier.AlgebraicGeometry.Picard.AbelMapFibreEuler
public import StacksFrontier.AlgebraicGeometry.Quot.C1590Private.CurveFamilyDivisorSheafComparison

/-!
# The pullback of `𝒪_Y(D)` to a fibre is `𝒪_V(E)`

Let `Y` be an algebraic space, `D ⊆ Y` an effective Cartier divisor, `V` a scheme of the big fppf
site and `q : h_V ⟶ Y` a morphism whose inverse image of `D` is the closed subspace cut out by an
effective Cartier divisor `E` of `V`.  No flatness is assumed.  This file proves piece (c) of step
P3 of the route to Stacks 0E6F, `AlgebraicGeometry.C1590Private.FibreDivisorSheafComparison`:

1. `H¹(V, 𝒪_V(E)) = 0` implies `H¹(h_V, q^*𝒪_Y(D)) = 0`;
2. a global section `t = f · 1_E` on `V ∖ E` of `𝒪_V(E)` gives a global section of
   `q^*𝒪_Y(D)` which is `f · q^*1_D` on every étale chart of `h_V` over `V ∖ E`.

## The route

* The map `q^*𝓘_D ⟶ 𝓘_{q⁻¹D}` of defining ideal sheaves is an epimorphism (Stacks 04CQ, the
  part without flatness) between invertible modules, hence an isomorphism; and on `h_V` the
  defining ideal sheaf of `q⁻¹D = Z_E` is `Φ(ℐ_E)`, `Φ` the associated module of Stacks 03DU (4)
  (`AlgebraicGeometry.Space.representedDefiningIdealSheafIso`).
* The canonical section `1_D` curries to the inclusion `𝓘_D ⟶ 𝒪_Y` under the evaluation pairing
  of Stacks 0841.  The left-unitality coherence of Stacks 03EL
  (`Stacks.SheafOfModules.RingedToposPullback.leftUnitality`) carries this currying identity
  along `q`: `q^*1_D` curries to `q^*𝓘_D ⟶ 𝒪` under the pulled-back pairing.  No tensor power
  and no description of the sections of a sheafified tensor product is needed.
* Under that pairing every morphism `q^*𝓘_D ⟶ 𝒪` is a global section of `q^*𝒪_Y(D)`
  (`AlgebraicGeometry.C1590Private.sectionOfHom`).  For clause (2) the morphism is the one `t`
  induces through `Φ`; that it is `f` times the inclusion over `V ∖ E` is
  `AlgebraicGeometry.C1590Private.associatedModuleMapAwayFromSupport`.
* For clause (1), the two pairings against `q^*𝓘_D` identify `q^*𝒪_Y(D)` with `Φ(𝒪_V(E))`
  (`Stacks.SheafOfModules.Invertible.exists_iso_of_tensorPairing`), and
  `AlgebraicGeometry.C1590Private.representedFirstCohomologyVanishing` compares the cohomology.

## Main results

* `AlgebraicGeometry.C1590Private.fibreDivisorSheafComparison`: the statement.
* `AlgebraicGeometry.C1590Private.curries_pullbackModules`: a currying identity of a pairing is
  preserved by the inverse image along a morphism of ringed topoi.
* `AlgebraicGeometry.C1590Private.exists_pulledIdealIso`: `q^*𝓘_D ≅ 𝓘_{Z_E}`.
* `AlgebraicGeometry.C1590Private.nonempty_pulledInvertibleSheafIso`: `q^*𝒪_Y(D) ≅ Φ(𝒪_V(E))`.

## References

* [Stacks Project, Tag 0E6F](https://stacks.math.columbia.edu/tag/0E6F)
* [Stacks Project, Tag 0841](https://stacks.math.columbia.edu/tag/0841)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 04CQ](https://stacks.math.columbia.edu/tag/04CQ)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Opposite Stacks.SheafOfModules.RingedToposPullback

namespace AlgebraicGeometry.C1590Private

universe w w' v u v' u'

section TensorHomAt

open Stacks.PresheafOfModules.TensorInternalHom

variable {C : Type u} [Category.{w} C] (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (F G H : _root_.PresheafOfModules.{w} (Oforget O))

/-- A morphism out of a tensor product is linear in the left entry of a pure tensor. -/
theorem tensorHomAt_smul_tmul (b : F ⊗ G ⟶ H) (W : Cᵒᵖ) (c : O.obj W) (x : F.obj W)
    (y : G.obj W) :
    tensorHomAt O F G H b W ((c • x) ⊗ₜ y) = c • tensorHomAt O F G H b W (x ⊗ₜ y) := by
  rw [← TensorProduct.smul_tmul', LinearMap.map_smul]

end TensorHomAt

section Generic

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w'})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w'}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **The currying identity of a pairing survives the inverse image along a morphism of ringed
topoi.**  If `ŝ : 𝒪 ⟶ L` curries to `ι : G ⟶ 𝒪` under `ev : L ⊗ G ⟶ 𝒪`, that is
`(ŝ ▷ G) ≫ ev = λ_G ≫ ι`, then `ν⁻¹ ≫ f^*ŝ` curries to `f^*ι ≫ ν` under
`μ⁻¹ ≫ f^*ev ≫ ν`, where `μ` is the comparison of Stacks 03EL and `ν : f^*𝒪 ≅ 𝒪`.  This is the
left-unitality coherence of Stacks 03EL together with the naturality of `μ`. -/
theorem curries_pullbackModules
    {L G : _root_.SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}
    (s : 𝟙_ _ ⟶ L) (ev : L ⊗ G ⟶ 𝟙_ _) (ι : G ⟶ 𝟙_ _)
    (h : (s ▷ G) ≫ ev = (λ_ G).hom ≫ ι) :
    (((pullbackUnitComparison f).inv ≫ f.pullbackModules.map s) ▷ f.pullbackModules.obj G) ≫
        (pullbackTensorComparisonIso f L G).inv ≫ f.pullbackModules.map ev ≫
          (pullbackUnitComparison f).hom =
      (λ_ _).hom ≫ f.pullbackModules.map ι ≫ (pullbackUnitComparison f).hom := by
  have hnat := pullbackTensorComparison_naturality_left f s G
  have hlu := leftUnitality f G
  have h' : f.pullbackModules.map (s ▷ G) ≫ f.pullbackModules.map ev =
      f.pullbackModules.map (λ_ G).hom ≫ f.pullbackModules.map ι := by
    rw [← Functor.map_comp, ← Functor.map_comp, h]
  have h2 : (f.pullbackModules.map s ▷ f.pullbackModules.obj G) ≫
      (pullbackTensorComparisonIso f L G).inv =
      (pullbackTensorComparisonIso f (𝟙_ _) G).inv ≫ f.pullbackModules.map (s ▷ G) := by
    rw [Iso.eq_inv_comp, ← Category.assoc, Iso.comp_inv_eq]
    exact hnat
  rw [comp_whiskerRight, Category.assoc, reassoc_of% h2, reassoc_of% h', hlu]
  simp only [Category.assoc]
  rw [← pullbackTensorComparisonIso_hom, Iso.inv_hom_id_assoc, ← comp_whiskerRight_assoc,
    Iso.inv_hom_id, id_whiskerRight, Category.id_comp]

end Generic


section SpaceLevel

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The strict monoidal structure of Tag 01CA on the modules of an algebraic space. -/
@[instance_reducible]
def spaceStrictMonoidal (Y : AlgebraicSpaces B S hS) :
    MonoidalCategory (SheafOfModules.{u} (Space.structureRingSheaf B S hS Y)) :=
  Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf (Space.smallEtaleRingedTopos B S hS Y).O

attribute [local instance] spaceStrictMonoidal

/-- The left unitor of the strict monoidal structure on the modules of an algebraic space is the
left unit constraint of the tensor product sheaf. -/
theorem leftUnitor_hom_eq_tensorSheafLeftUnitor (Y : AlgebraicSpaces B S hS)
    (M : SheafOfModules.{u} (Space.structureRingSheaf B S hS Y)) :
    (λ_ M).hom = (Stacks.SheafOfModules.tensorSheafLeftUnitor
      (Space.smallEtaleRingedTopos B S hS Y).O.obj
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
        (Space.smallEtaleRingedTopos B S hS Y).O) M).hom :=
  congrArg Iso.hom (Stacks.SheafOfModules.leftUnitor_eq_tensorSheafLeftUnitor
      (Space.smallEtaleRingedTopos B S hS Y).O.obj _ M)

/-- The left unit constraint of the tensor product sheaf at `𝓘_D` is the sheafified unit
constraint of `AlgebraicGeometry.Space.map_canonicalSectionHom_comp_evaluation`. -/
theorem tensorSheafLeftUnitor_hom_eq_unitTensorHom (Y : AlgebraicSpaces B S hS)
    (D : Space.ClosedSubspaces B S hS Y.1) :
    (Stacks.SheafOfModules.tensorSheafLeftUnitor
      (Space.smallEtaleRingedTopos B S hS Y).O.obj
      (Stacks.SheafOfModules.TensorEncodings.isSheaf_structureRingPresheaf
          (Space.smallEtaleRingedTopos B S hS Y).O)
      (Space.idealSheafOfModules B S hS Y D)).hom = Space.unitTensorHom B S hS Y D :=
  rfl

/-- **The canonical section `1_D` curries to the inclusion `𝓘_D ⟶ 𝒪_Y`** under the evaluation
pairing `𝒪_Y(D) ⊗ 𝓘_D ≅ 𝒪_Y`, in the strict monoidal structure of Tag 01CA. -/
theorem curries_canonicalSection (Y : AlgebraicSpaces B S hS)
    (D : Space.ClosedSubspaces B S hS Y.1) (hD : Space.IsEffectiveCartierDivisor B S hS Y D) :
    (Space.canonicalSectionHom B S hS Y D hD ▷ Space.idealSheafOfModules B S hS Y D) ≫
        (Space.associatedInvertibleSheafEvaluation B S hS Y D hD).hom =
      (λ_ (Space.idealSheafOfModules B S hS Y D)).hom ≫ (Space.definingIdealSheaf B S hS Y D).ι :=
          by
  have h := Space.map_canonicalSectionHom_comp_evaluation B S hS Y D hD
  have h1 : Space.canonicalSectionHom B S hS Y D hD ▷ Space.idealSheafOfModules B S hS Y D =
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ⟨Space.structureCommRings B S hS Y, Presheaf.isSheaf_of_isSheaf_comp _
          (Space.structureCommRings B S hS Y) (forget₂ CommRingCat RingCat)
          (Space.structureRingSheaf B S hS Y).property⟩).flip.obj
        (Space.idealSheafOfModules B S hS Y D)).map (Space.canonicalSectionHom B S hS Y D hD) := by
    refine (Stacks.SheafOfModules.Strict.whiskerRight_eq_tensorSheafBifunctor_map
      (Space.smallEtaleRingedTopos B S hS Y).O _ _).trans ?_
    exact (congrArg (fun m => _ ≫ m) (CategoryTheory.Functor.map_id _ _)).trans
      (Category.comp_id _)
  have h2 := (leftUnitor_hom_eq_tensorSheafLeftUnitor B S hS Y
    (Space.idealSheafOfModules B S hS Y D)).trans (tensorSheafLeftUnitor_hom_eq_unitTensorHom B S
        hS Y D)
  rw [h1, h2]
  exact h

section Pullback

variable {Y W : AlgebraicSpaces B S hS} (g : W ⟶ Y) (D : Space.ClosedSubspaces B S hS Y.1)
  (hD : Space.IsEffectiveCartierDivisor B S hS Y D)

/-- The evaluation pairing of `𝒪_Y(D)` pulled back along `g`. -/
def pulledEvaluation :
    (Space.modulePullback B S hS g).obj (Space.associatedInvertibleSheaf B S hS Y D hD) ⊗
        (Space.modulePullback B S hS g).obj (Space.idealSheafOfModules B S hS Y D) ≅
      𝟙_ (SheafOfModules.{u} (Space.structureRingSheaf B S hS W)) :=
  (pullbackTensorComparisonIso (Space.smallEtaleRingedToposModulesHom B S hS g) _ _).symm ≪≫
    (Space.modulePullback B S hS g).mapIso (Space.associatedInvertibleSheafEvaluation B S hS Y D
        hD) ≪≫
    pullbackUnitComparison (Space.smallEtaleRingedToposModulesHom B S hS g)

/-- The inclusion of the ideal sheaf pulled back along `g`, read in `𝒪_W`. -/
def pulledIdealInclusion :
    (Space.modulePullback B S hS g).obj (Space.idealSheafOfModules B S hS Y D) ⟶
      𝟙_ (SheafOfModules.{u} (Space.structureRingSheaf B S hS W)) :=
  (Space.modulePullback B S hS g).map (Space.definingIdealSheaf B S hS Y D).ι ≫
    (pullbackUnitComparison (Space.smallEtaleRingedToposModulesHom B S hS g)).hom

/-- **The pulled-back canonical section `g^*1_D` curries to the pulled-back inclusion** under the
pulled-back evaluation pairing. -/
theorem curries_pulledCanonicalSection :
    ((SheafOfModules.unitHomEquiv ((Space.modulePullback B S hS g).obj
          (Space.associatedInvertibleSheaf B S hS Y D hD))).symm
        ((Space.globalSectionsPullbackMap B S hS g _).hom (Space.canonicalSection B S hS Y D hD)) ▷
        (Space.modulePullback B S hS g).obj (Space.idealSheafOfModules B S hS Y D)) ≫
      (pulledEvaluation B S hS g D hD).hom =
    (λ_ _).hom ≫ pulledIdealInclusion B S hS g D := by
  refine Eq.trans (congrArg (fun m => (m ▷ (Space.modulePullback B S hS g).obj
    (Space.idealSheafOfModules B S hS Y D)) ≫ (pulledEvaluation B S hS g D hD).hom)
    (Space.unitHomEquiv_symm_globalSectionsPullbackMap (B := B) (S := S) (hS := hS) g
      (Space.associatedInvertibleSheaf B S hS Y D hD) (Space.canonicalSection B S hS Y D hD))) ?_
  exact curries_pullbackModules (Space.smallEtaleRingedToposModulesHom B S hS g) _ _ _
    (curries_canonicalSection B S hS Y D hD)

end Pullback

section Curry

open Stacks.SheafOfModules.Invertible Stacks.PresheafOfModules.TensorInternalHom

variable (W : AlgebraicSpaces B S hS)
  {K G : SheafOfModules.{u} (Space.structureRingSheaf B S hS W)}
  (ev : K ⊗ G ≅ 𝟙_ (SheafOfModules.{u} (Space.structureRingSheaf B S hS W)))
  (ι : G ⟶ 𝟙_ (SheafOfModules.{u} (Space.structureRingSheaf B S hS W)))
  (s : K.sections)
  (hs : ((SheafOfModules.unitHomEquiv K).symm s ▷ G) ≫ ev.hom = (λ_ G).hom ≫ ι)

include hs in
/-- A section currying to `ι` under a pairing `ev`, read on sections: the pairing sends
`s ⊗ t` to `ι t`. -/
theorem tensorHomAt_pairing_eq_of_curries (V : (Space.SmallEtale B S hS W.1)ᵒᵖ)
    (t : (Space.modulePresheaf B S hS W G).obj V) :
    tensorHomAt (Space.structureCommRings B S hS W) (Space.modulePresheaf B S hS W K)
        (Space.modulePresheaf B S hS W G)
        (Space.modulePresheaf B S hS W (SheafOfModules.unit (Space.structureRingSheaf B S hS W)))
        (tensorPairing (Space.structureCommRings B S hS W) (Space.structureRingSheaf B S hS
            W).property
          G K (SheafOfModules.unit (Space.structureRingSheaf B S hS W)) ev) V (s.val V ⊗ₜ t) =
      ((valPresheafMap (Space.structureCommRings B S hS W) (Space.structureRingSheaf B S hS
          W).property
        ι).app V).hom t := by
  have h := congrArg (fun m => (m.val.app V).hom
    ((Stacks.SheafOfModules.TensorSheafification.toSheafify (Space.smallEtaleRingedTopos B S hS
        W).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedTopos B S hS W).O).property
      ((𝟙_ (SheafOfModules.{u} (Space.structureRingSheaf B S hS W))).val ⊗ G.val)).app V
      ((1 : (Space.structureRingSheaf B S hS W).obj.obj V) ⊗ₜ t))) hs
  have h1 := whiskerRight_val_app_toSheafify (X := Space.smallEtaleRingedTopos B S hS W)
    ((SheafOfModules.unitHomEquiv K).symm s) (B := G) V (1 : (Space.structureRingSheaf B S hS
        W).obj.obj V) t
  have h2 := CategoryTheory.Sheaf.unitHomEquiv_symm_val_app_one K s V
  have h3 : ∀ x : G.val.obj V, ((λ_ G).hom.val.app V).hom
      ((Stacks.SheafOfModules.TensorSheafification.toSheafify (Space.smallEtaleRingedTopos B S hS
          W).O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedTopos B S hS W).O).property
        ((𝟙_ (SheafOfModules.{u} (Space.structureRingSheaf B S hS W))).val ⊗ G.val)).app V
        ((1 : (Space.structureRingSheaf B S hS W).obj.obj V) ⊗ₜ x)) = x := by
    intro x
    rw [leftUnitor_hom_eq_tensorSheafLeftUnitor B S hS W G]
    exact (Stacks.SheafOfModules.tensorSheafLeftUnitor_hom_val_app_tmul _ _ G V 1 x).trans
      (one_smul ((Space.structureRingSheaf B S hS W).obj.obj V) x)
  refine Eq.trans ?_ (h.trans ?_)
  · refine congrArg (fun z => (ev.hom.val.app V).hom z) ?_
    refine Eq.trans ?_ h1.symm
    exact congrArg (fun z => ((Stacks.SheafOfModules.TensorSheafification.toSheafify
      (Space.smallEtaleRingedTopos B S hS W).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedTopos B S hS W).O).property
      (K.val ⊗ G.val)).app V).hom (z ⊗ₜ t)) h2.symm
  · exact congrArg (fun z => (ι.val.app V).hom z) (h3 t)

variable [hG : AlgebraicGeometry.SheafOfModules.IsInvertible (Space.structureCommRings B S hS W)
  (Space.structureRingSheaf B S hS W).property G]

/-- Currying against the pairing `ev`, over an étale chart. -/
def pairingCurry (U : Space.SmallEtale B S hS W.1) :
    (Space.modulePresheaf B S hS W K).obj (op U) ≃ₗ[(Space.structureCommRings B S hS W).obj (op U)]
      internalHomObj (Space.structureCommRings B S hS W) (Space.modulePresheaf B S hS W G)
        (Space.modulePresheaf B S hS W (SheafOfModules.unit (Space.structureRingSheaf B S hS W)))
            U :=
  tensorCurryLinearEquiv (Space.structureCommRings B S hS W)
    (Space.structureRingSheaf B S hS W).property G K
    (SheafOfModules.unit (Space.structureRingSheaf B S hS W)) ev U

/-- Currying against `ev` commutes with the restriction maps. -/
theorem pairingCurry_natural {U V : (Space.SmallEtale B S hS W.1)ᵒᵖ} (f : U ⟶ V)
    (x : (Space.modulePresheaf B S hS W K).obj U) :
    pairingCurry B S hS W ev V.unop ((Space.modulePresheaf B S hS W K).map f x) =
      (internalHom (Space.structureCommRings B S hS W) (Space.modulePresheaf B S hS W G)
        (Space.modulePresheaf B S hS W
          (SheafOfModules.unit (Space.structureRingSheaf B S hS W)))).map f
        (pairingCurry B S hS W ev U.unop x) :=
  tensorCurryLinearEquiv_natural _ _ G K _ ev f x

/-- A morphism `G ⟶ 𝒪`, read as a section of the internal Hom over an étale chart. -/
def homSectionOf (τ : G ⟶ 𝟙_ (SheafOfModules.{u} (Space.structureRingSheaf B S hS W)))
    (U : Space.SmallEtale B S hS W.1) :
    internalHomObj (Space.structureCommRings B S hS W) (Space.modulePresheaf B S hS W G)
      (Space.modulePresheaf B S hS W (SheafOfModules.unit (Space.structureRingSheaf B S hS W))) U :=
  (restrFun (Space.structureCommRings B S hS W) U).map
    (valPresheafMap (Space.structureCommRings B S hS W) (Space.structureRingSheaf B S hS
        W).property τ)

omit hG in
/-- The sections of the internal Hom read off a morphism form a compatible family. -/
theorem internalHom_map_homSectionOf
    (τ : G ⟶ 𝟙_ (SheafOfModules.{u} (Space.structureRingSheaf B S hS W)))
    {U V : (Space.SmallEtale B S hS W.1)ᵒᵖ} (f : U ⟶ V) :
    (internalHom (Space.structureCommRings B S hS W) (Space.modulePresheaf B S hS W G)
        (Space.modulePresheaf B S hS W
          (SheafOfModules.unit (Space.structureRingSheaf B S hS W)))).map f
        (homSectionOf B S hS W τ U.unop) = homSectionOf B S hS W τ V.unop :=
  internalHom_map_restrFun_map (Space.structureCommRings B S hS W) _ _ f _

/-- The global section of `K` which the pairing `ev` curries to a morphism `τ : G ⟶ 𝒪`. -/
def sectionOfHom (τ : G ⟶ 𝟙_ (SheafOfModules.{u} (Space.structureRingSheaf B S hS W))) :
    K.sections :=
  PresheafOfModules.sectionsMk (M := Space.modulePresheaf B S hS W K)
    (fun U ↦ (pairingCurry B S hS W ev U.unop).symm (homSectionOf B S hS W τ U.unop))
    (fun {U V} f ↦ by
      refine (pairingCurry B S hS W ev V.unop).injective ?_
      rw [pairingCurry_natural, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
        internalHom_map_homSectionOf])

include hs in
/-- **The section attached to `τ` is a multiple of `s` wherever `τ` is that multiple of `ι`.** -/
theorem sectionOfHom_val_eq_smul
    (τ : G ⟶ 𝟙_ (SheafOfModules.{u} (Space.structureRingSheaf B S hS W)))
    (U : Space.SmallEtale B S hS W.1) (r : (Space.structureCommRings B S hS W).obj (op U))
    (h : ∀ (V : (Space.SmallEtale B S hS W.1)ᵒᵖ) (q : V.unop ⟶ U)
      (t : (Space.modulePresheaf B S hS W G).obj V),
      ((valPresheafMap (Space.structureCommRings B S hS W)
          (Space.structureRingSheaf B S hS W).property τ).app V).hom t =
        ((Space.structureCommRings B S hS W).map q.op).hom r •
          ((valPresheafMap (Space.structureCommRings B S hS W)
            (Space.structureRingSheaf B S hS W).property ι).app V).hom t) :
    (show (Space.modulePresheaf B S hS W K).obj (op U) from (sectionOfHom B S hS W ev τ).val (op
        U)) =
      r • (show (Space.modulePresheaf B S hS W K).obj (op U) from s.val (op U)) := by
  refine eq_of_tensorPairing_eq (Space.structureCommRings B S hS W)
    (Space.structureRingSheaf B S hS W).property G K
    (SheafOfModules.unit (Space.structureRingSheaf B S hS W)) ev U _ _ (fun V q t ↦ ?_)
  refine (tensorCurryLinearEquiv_apply (Space.structureCommRings B S hS W)
    (Space.structureRingSheaf B S hS W).property G K
    (SheafOfModules.unit (Space.structureRingSheaf B S hS W)) ev U _ V q t).symm.trans ?_
  have hC : tensorCurryLinearEquiv (Space.structureCommRings B S hS W)
      (Space.structureRingSheaf B S hS W).property G K
      (SheafOfModules.unit (Space.structureRingSheaf B S hS W)) ev U
      ((sectionOfHom B S hS W ev τ).val (op U)) = homSectionOf B S hS W τ U :=
    (pairingCurry B S hS W ev U).apply_symm_apply _
  rw [hC]
  refine (h V q t).trans ?_
  rw [restrictₛₗ_smul]
  refine Eq.trans ?_ (tensorHomAt_smul_tmul _ _ _ _ _ V _ _ t).symm
  refine congrArg (fun z => ((Space.structureCommRings B S hS W).map q.op).hom r • z) ?_
  refine Eq.trans ?_ (congrArg (fun z => tensorHomAt (Space.structureCommRings B S hS W) _ _ _
    (tensorPairing (Space.structureCommRings B S hS W) (Space.structureRingSheaf B S hS W).property
      G K (SheafOfModules.unit (Space.structureRingSheaf B S hS W)) ev) V (z ⊗ₜ t))
    (PresheafOfModules.sections_property s q.op).symm)
  exact (tensorHomAt_pairing_eq_of_curries B S hS W ev ι s hs V t).symm

end Curry

section Ideal

variable (V : BigFppfOver B S hS) (E : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)

/-- The sheaf of ideals cut out on `V` by the closed subspace `Z_E` of `h_V` is `E`. -/
theorem schemeSpaceIdeal_closedSubspaceOfIdeal :
    Space.schemeSpaceIdeal B S hS V (Space.closedSubspaceOfIdeal V E) = E :=
  (Space.schemeSpaceIdeal_eq_ker B S hS V _).trans (Space.ker_rep_snd_closedSubspaceOfIdeal V E)

/-- The sheaf of ideals of an effective Cartier divisor, read as a submodule of `𝒪_V`, is
invertible. -/
theorem isInvertible_unitSubmodule (hE : Stacks.Divisors.IsEffectiveCartierDivisor E) :
    Stacks.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj V).presheaf
      (AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf _) E.unitSubmodule.toSheafOfModules :=
          by
  have : Stacks.SheafOfModules.IsInvertible ((BigFppfOver.toScheme B S hS).obj V).presheaf
      (AlgebraicGeometry.SmallEtale.zariskiStructureIsSheaf _)
      (Stacks.ClosedImmersion.idealSheaf E.subschemeι.toLRSHom.toShHom) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hE
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _ (E.unitSubmoduleIsoIdealSheaf).symm

variable (hF : IsAlgebraicSpace B S hS (yoneda.obj V))

/-- **`Φ` of the sheaf of ideals of `E` is the defining ideal sheaf of the closed subspace of
`h_V` that `E` cuts out**, compatibly with the two inclusions into the structure sheaves. -/
theorem exists_representedIdealIso :
    ∃ γ : (Space.representedAssociatedModule B S hS V hF).obj E.unitSubmodule.toSheafOfModules ≅
      (Space.definingIdealSheaf B S hS ⟨yoneda.obj V, hF⟩
        (Space.closedSubspaceOfIdeal V E)).toSheafOfModules,
      γ.hom ≫ (Space.definingIdealSheaf B S hS ⟨yoneda.obj V, hF⟩
          (Space.closedSubspaceOfIdeal V E)).ι =
        (Space.representedAssociatedModule B S hS V hF).map (Stacks.ClosedSubscheme.idealIota E) ≫
          (Space.representedAssociatedModuleObjUnitIso B S hS V hF).hom := by
  have key : ∀ (Z : Space.ClosedSubspaces B S hS (yoneda.obj V))
      (I : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData),
      Space.schemeSpaceIdeal B S hS V Z = I →
      ∃ γ : (Space.representedAssociatedModule B S hS V hF).obj I.unitSubmodule.toSheafOfModules ≅
        (Space.definingIdealSheaf B S hS ⟨yoneda.obj V, hF⟩ Z).toSheafOfModules,
        γ.hom ≫ (Space.definingIdealSheaf B S hS ⟨yoneda.obj V, hF⟩ Z).ι =
          (Space.representedAssociatedModule B S hS V hF).map (Stacks.ClosedSubscheme.idealIota I) ≫
            (Space.representedAssociatedModuleObjUnitIso B S hS V hF).hom := by
    rintro Z I rfl
    exact ⟨Space.representedDefiningIdealSheafIso B S hS V hF Z,
      Space.representedDefiningIdealSheafIso_hom_comp_ι B S hS V hF Z⟩
  exact key _ E (schemeSpaceIdeal_closedSubspaceOfIdeal B S hS V E)

/-- The defining ideal sheaf of the closed subspace of `h_V` cut out by an effective Cartier
divisor `E` of `V` is an invertible module. -/
theorem isInvertibleModule_definingIdealSheaf_closedSubspaceOfIdeal
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor E) :
    Space.IsInvertibleModule (schemeSpace V)
      (Space.definingIdealSheaf B S hS (schemeSpace V)
        (Space.closedSubspaceOfIdeal V E)).toSheafOfModules := by
  obtain ⟨γ, -⟩ := exists_representedIdealIso B S hS V E (isAlgebraicSpace_yoneda B S hS V)
  have : Stacks.SheafOfModules.IsInvertible (Space.structureSheaf B S hS (schemeSpace V).1
      (schemeSpace V).2).obj (Space.structureRingPresheaf_isSheaf B S hS (schemeSpace V).1
        (schemeSpace V).2)
      ((Space.representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS V)).obj
        E.unitSubmodule.toSheafOfModules) :=
    Space.isInvertible_representedSmallEtaleModuleEquivalence_functor_obj_associatedModule B S hS V
      E.unitSubmodule.toSheafOfModules (isInvertible_unitSubmodule B S hS V E hE)
  exact Stacks.SheafOfModules.isInvertible_of_iso _ _ γ

end Ideal

section PulledIdeal

variable {Y : AlgebraicSpaces B S hS} (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y.1)
  (D : Space.ClosedSubspaces B S hS Y.1) (hD : Space.IsEffectiveCartierDivisor B S hS Y D)
  (E : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)

include hD in
/-- **The pullback of the ideal sheaf of `D` is the ideal sheaf of the inverse image**, when the
inverse image is cut out by an effective Cartier divisor of the scheme `V`: the comparison map
is an epimorphism between invertible modules. -/
theorem exists_pulledIdealIso (hE : Stacks.Divisors.IsEffectiveCartierDivisor E)
    (hpre : D.1.preimage q = (Space.closedSubspaceOfIdeal V E).1) :
    ∃ e : (Space.modulePullback B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
        (Space.idealSheafOfModules B S hS Y D) ≅
      (Space.definingIdealSheaf B S hS (schemeSpace V)
        (Space.closedSubspaceOfIdeal V E)).toSheafOfModules,
      e.hom ≫ (Space.definingIdealSheaf B S hS (schemeSpace V) (Space.closedSubspaceOfIdeal V
          E)).ι =
        pulledIdealInclusion B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y) D := by
  set g : schemeSpace V ⟶ Y := ObjectProperty.homMk q
  have hinvD : Space.IsInvertibleModule Y (Space.idealSheafOfModules B S hS Y D) :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hD
  have hM := Space.modulePullbackInvertible (B := B) (S := S) (hS := hS) g _ hinvD
  have key : ∀ Z : Space.ClosedSubspaces B S hS (schemeSpace V).1,
      Space.preimageSubspace B S hS g D = Z →
      Space.IsInvertibleModule (schemeSpace V)
        (Space.definingIdealSheaf B S hS (schemeSpace V) Z).toSheafOfModules →
      ∃ e : (Space.modulePullback B S hS g).obj (Space.idealSheafOfModules B S hS Y D) ≅
          (Space.definingIdealSheaf B S hS (schemeSpace V) Z).toSheafOfModules,
        e.hom ≫ (Space.definingIdealSheaf B S hS (schemeSpace V) Z).ι =
          pulledIdealInclusion B S hS g D := by
    rintro Z rfl hinv
    have := Space.epi_idealSheafMap B S hS g D
    have := Space.isIso_of_epi_of_isInvertibleModule hM hinv
      (Space.idealSheafMap B S hS (Space.preimageSubspace B S hS g D) D g
        (Space.preimageProjection B S hS g D) (Space.conormalEtaleRestrictionSquare B S hS g D))
    refine ⟨asIso (Space.idealSheafMap B S hS (Space.preimageSubspace B S hS g D) D g
        (Space.preimageProjection B S hS g D) (Space.conormalEtaleRestrictionSquare B S hS g D)),
            ?_⟩
    refine (Space.idealSheafMap_comp_definingIdealSheaf_ι B S hS _ D g _ _).trans ?_
    exact congrArg (fun m => _ ≫ m)
      (Space.structureModulePullbackMap_eq_modulePullbackUnitIso_hom B S hS g)
  exact key _ (Subtype.ext hpre) (isInvertibleModule_definingIdealSheaf_closedSubspaceOfIdeal B S
      hS V E hE)

end PulledIdeal

section Charts

/-- Pulling back a function along a composite of scheme morphisms, through `appLE`. -/
theorem appTop_appLE_eq {X X' Y : Scheme.{u}} (g : X' ⟶ X) (φ : X ⟶ Y) (O : Y.Opens)
    (hU : ⊤ ≤ φ ⁻¹ᵁ O) (ψ : X' ⟶ Y) (hψ : ψ = g ≫ φ) (h' : ⊤ ≤ ψ ⁻¹ᵁ O) (f : Γ(Y, O)) :
    g.appTop (φ.appLE O ⊤ hU f) = ψ.appLE O ⊤ h' f := by
  subst hψ
  have h2 := Scheme.Hom.appLE_comp_appLE g φ O ⊤ (g ⁻¹ᵁ ⊤) hU le_rfl
  have h1 := Scheme.Hom.appLE_eq_app g (U := ⊤)
  rw [h1] at h2
  exact ConcreteCategory.congr_hom h2 f

variable (V : BigFppfOver B S hS)

/-- The structure morphisms of étale charts of `h_V` compose along a morphism of charts. -/
theorem yoneda_preimage_hom_eq_comp {U U' : Space.SmallEtale B S hS (yoneda.obj V)} (q : U' ⟶ U) :
    yoneda.preimage U'.1.hom = q.hom.left ≫ yoneda.preimage U.1.hom := yoneda.map_injective <| by
  rw [Functor.map_preimage, Functor.map_comp, Functor.map_preimage]
  exact (CostructuredArrow.w q.hom).symm

/-- An étale chart of `h_V` mapping to a chart that lands in an open `O` lands in `O`. -/
theorem top_le_preimage_of_hom {U U' : Space.SmallEtale B S hS (yoneda.obj V)} (q : U' ⟶ U)
    {O : ((BigFppfOver.toScheme B S hS).obj V).Opens}
    (hU : ⊤ ≤ (BigFppfOver.toScheme B S hS).map (yoneda.preimage U.1.hom) ⁻¹ᵁ O) :
    ⊤ ≤ (BigFppfOver.toScheme B S hS).map (yoneda.preimage U'.1.hom) ⁻¹ᵁ O := by
  rw [yoneda_preimage_hom_eq_comp B S hS V q, Functor.map_comp, Scheme.Hom.comp_preimage]
  exact fun x _ => hU (Set.mem_univ _)

/-- The restriction map of the structure sheaf of `h_V` along a morphism of étale charts carries
the pullback of a function along the first chart to its pullback along the second. -/
theorem structureCommRings_map_appLE {U U' : Space.SmallEtale B S hS (yoneda.obj V)} (q : U' ⟶ U)
    {O : ((BigFppfOver.toScheme B S hS).obj V).Opens}
    (hU : ⊤ ≤ (BigFppfOver.toScheme B S hS).map (yoneda.preimage U.1.hom) ⁻¹ᵁ O)
    (f : Γ((BigFppfOver.toScheme B S hS).obj V, O)) :
    ((Space.structureCommRings B S hS (schemeSpace V)).map q.op).hom
        (((BigFppfOver.toScheme B S hS).map (yoneda.preimage U.1.hom)).appLE O ⊤ hU f) =
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage U'.1.hom)).appLE O ⊤
        (top_le_preimage_of_hom B S hS V q hU) f :=
  appTop_appLE_eq _ _ O hU _
    (by rw [yoneda_preimage_hom_eq_comp B S hS V q, Functor.map_comp]; rfl) _ f

end Charts

end SpaceLevel

section Zariski

open Stacks.Divisors

variable {X : Scheme.{u}} (E : X.IdealSheafData)

/-- The global section of `𝒪_X(E)` with a prescribed value over `⊤`. -/
def divisorSheafSectionOfTop (t : Γ(divisorSheaf E, ⊤)) : (invertibleSheaf' E).sections :=
  (Space.sectionsEvalAddEquiv (invertibleSheaf' E) Limits.isTerminalTop).symm t

/-- **A global section of `𝒪_X(E) = SheafHom(ℐ_E, 𝒪_X)` is a morphism `ℐ_E ⟶ 𝒪_X`.** -/
def divisorSectionHom (t : Γ(divisorSheaf E, ⊤)) :
    negativeTwist' E ⟶ SheafOfModules.unit (structureSheafRing X.toRingedSpace) :=
  ⟨homOfSections X.presheaf (negativeTwist' E).val
    (SheafOfModules.unit (structureSheafRing X.toRingedSpace)).val
    (divisorSheafSectionOfTop E t)⟩

/-- The value of `divisorSectionHom` on a section of `ℐ_E` is the evaluation of the restricted
section of `𝒪_X(E)`. -/
theorem divisorSectionHom_app (t : Γ(divisorSheaf E, ⊤)) (W : X.Opens)
    (x : (negativeTwist' E).val.obj (op W)) :
    ((divisorSectionHom E t).val.app (op W)).hom x =
      Stacks.SheafOfModules.dualEval (L := negativeTwist' E)
        (((invertibleSheaf' E).val.map (homOfLE (le_top : W ≤ ⊤)).op).hom t) x := by
  have h1 : (divisorSheafSectionOfTop E t).val (op W) =
      ((invertibleSheaf' E).val.map (homOfLE (le_top : W ≤ ⊤)).op).hom
        ((divisorSheafSectionOfTop E t).val (op ⊤)) :=
    (PresheafOfModules.sections_property (divisorSheafSectionOfTop E t)
      (homOfLE (le_top : W ≤ ⊤)).op).symm
  have h2 : (divisorSheafSectionOfTop E t).val (op ⊤) = t :=
    (Space.sectionsEvalAddEquiv (invertibleSheaf' E) Limits.isTerminalTop).apply_symm_apply t
  rw [h2] at h1
  exact congrArg (fun l => Stacks.SheafOfModules.dualEval (L := negativeTwist' E) l x) h1

/-- **A section `t` of `𝒪_X(E)` which is `f · 1_E` off `E` is, as a morphism `ℐ_E ⟶ 𝒪_X`,
multiplication by `f` there.** -/
theorem divisorSectionHom_app_eq_mul (t : Γ(divisorSheaf E, ⊤)) (f : Γ(X, E.support.compl))
    (ht : (divisorSheaf E).presheaf.map (homOfLE (le_top : E.support.compl ≤ ⊤)).op t =
      f • (divisorSheaf E).presheaf.map (homOfLE (le_top : E.support.compl ≤ ⊤)).op
        (divisorSheafGlobalSection E))
    (W : X.Opens) (hW : W ≤ E.support.compl) (x : (negativeTwist' E).val.obj (op W)) :
    (show Γ(X, W) from ((divisorSectionHom E t).val.app (op W)).hom x) =
      X.presheaf.map (homOfLE hW).op f *
        (show Γ(X, W) from ((Stacks.ClosedImmersion.idealSheafι
          E.subschemeι.toLRSHom.toShHom).val.app (op W)).hom x) := by
  refine (divisorSectionHom_app E t W x).trans ?_
  have hcomp := (invertibleSheaf' E).val.map_comp_apply (homOfLE (le_top : E.support.compl ≤ ⊤)).op
    (homOfLE hW).op t
  have ht' : ((invertibleSheaf' E).val.map (homOfLE (le_top : E.support.compl ≤ ⊤)).op).hom t =
      f • ((invertibleSheaf' E).val.map (homOfLE (le_top : E.support.compl ≤ ⊤)).op).hom
        ((canonicalSection' E).val (op ⊤)) := ht
  have hsmul := (invertibleSheaf' E).val.map_smul (homOfLE hW).op f
    (((invertibleSheaf' E).val.map (homOfLE (le_top : E.support.compl ≤ ⊤)).op).hom
        ((canonicalSection' E).val (op ⊤)))
  have hcan := ((invertibleSheaf' E).val.map_comp_apply
    (homOfLE (le_top : E.support.compl ≤ ⊤)).op (homOfLE hW).op
    ((canonicalSection' E).val (op ⊤))).symm.trans
    (PresheafOfModules.sections_property (canonicalSection' E) (homOfLE (le_top : W ≤ ⊤)).op)
  have key : ((invertibleSheaf' E).val.map (homOfLE (le_top : W ≤ ⊤)).op).hom t =
      ((structureSheafRing X.toRingedSpace).obj.map (homOfLE hW).op).hom f •
        (show (invertibleSheaf' E).val.obj (op W) from (canonicalSection' E).val (op W)) := by
    refine hcomp.trans ?_
    rw [ht']
    refine hsmul.trans ?_
    rw [hcan]
    rfl
  rw [key]
  exact Stacks.SheafOfModules.evalSection_smul_left _ _ _ _ _ _ _

/-- The morphism `I ⟶ 𝒪_X` of the sheaf of ideals of `E` which a global section of `𝒪_X(E)` is. -/
def divisorSectionIdealHom (t : Γ(divisorSheaf E, ⊤)) :
    E.unitSubmodule.toSheafOfModules ⟶ SheafOfModules.unit X.ringCatSheaf :=
  (E.unitSubmoduleIsoIdealSheaf).hom ≫ divisorSectionHom E t

/-- `divisorSectionIdealHom` is multiplication by `f` on every open contained in `X ∖ E`. -/
theorem divisorSectionIdealHom_app_eq_mul (t : Γ(divisorSheaf E, ⊤)) (f : Γ(X, E.support.compl))
    (ht : (divisorSheaf E).presheaf.map (homOfLE (le_top : E.support.compl ≤ ⊤)).op t =
      f • (divisorSheaf E).presheaf.map (homOfLE (le_top : E.support.compl ≤ ⊤)).op
        (divisorSheafGlobalSection E))
    (W : X.Opens) (hW : W ≤ E.support.compl) (x : E.unitSubmodule.toSheafOfModules.val.obj (op W)) :
    (show Γ(X, W) from (divisorSectionIdealHom E t).val.app (op W) x) =
      X.presheaf.map (homOfLE hW).op f *
        (show Γ(X, W) from (Stacks.ClosedSubscheme.idealIota E).val.app (op W) x) := by
  have h := divisorSectionHom_app_eq_mul E t f ht W hW
    (((E.unitSubmoduleIsoIdealSheaf).hom.val.app (op W)).hom x)
  refine h.trans ?_
  refine congrArg (fun z => X.presheaf.map (homOfLE hW).op f * z) ?_
  exact congrArg (fun m : E.unitSubmodule.toSheafOfModules ⟶ SheafOfModules.unit X.ringCatSheaf =>
    (m.val.app (op W)).hom x) (E.unitSubmoduleIsoIdealSheaf_hom_comp_idealSheafι)

end Zariski

section Assembly

open Stacks.Cohomology.SiteModules (globalSectionsFunctor)

attribute [local instance] Stacks.SheafOfModules.Strict.monoidalUnderlyingRingSheaf
attribute [local instance] spaceStrictMonoidal

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The pullback of the ideal sheaf of an effective Cartier divisor is invertible. -/
private theorem isInvertible_modulePullback_idealSheafOfModules {Y W : AlgebraicSpaces B S hS}
    (g : W ⟶ Y) (D : Space.ClosedSubspaces B S hS Y.1)
    (hD : Space.IsEffectiveCartierDivisor B S hS Y D) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (Space.structureCommRings B S hS W)
      (Space.structureRingSheaf B S hS W).property
      ((Space.modulePullback B S hS g).obj (Space.idealSheafOfModules B S hS Y D)) :=
  Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry _ _ _
    (Space.modulePullbackInvertible (B := B) (S := S) (hS := hS) g _
      (Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ hD))

/-- **Clause (2) of `AlgebraicGeometry.C1590Private.FibreDivisorSheafComparison`.**  A global
section `t` of `𝒪_V(E)` which is `f · 1_E` on `V ∖ E` gives a global section `σ` of
`q^*𝒪_Y(D)` which is `f · q^*1_D` on every étale chart of `h_V` landing in `V ∖ E`.  The section
`σ` is the one which the pulled-back pairing `q^*𝒪_Y(D) ⊗ q^*𝓘_D ≅ 𝒪` curries to the
morphism `q^*𝓘_D ≅ 𝓘_{Z_E} ≅ Φ(ℐ_E) ⟶ Φ(𝒪_V) ≅ 𝒪` induced by `t`. -/
theorem exists_section_eq_smul_canonicalSection
    (Y : AlgebraicSpaces B S hS) (V : BigFppfOver B S hS)
    (q : yoneda.obj V ⟶ Y.obj) (D : Space.ClosedSubspaces B S hS Y.obj)
    (hD : Space.IsEffectiveCartierDivisor B S hS Y D)
    (E : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor E)
    (hpre : D.1.preimage q = (Space.closedSubspaceOfIdeal V E).1)
    (t : Γ(Stacks.Divisors.divisorSheaf E, ⊤))
    (f : Γ((BigFppfOver.toScheme B S hS).obj V, E.support.compl))
    (ht : (Stacks.Divisors.divisorSheaf E).presheaf.map
          (homOfLE (le_top : E.support.compl ≤ ⊤)).op t =
        f • (Stacks.Divisors.divisorSheaf E).presheaf.map
          (homOfLE (le_top : E.support.compl ≤ ⊤)).op
          (Stacks.Divisors.divisorSheafGlobalSection E)) :
    ∃ σ : (globalSectionsFunctor.{u + 1, u, u, u}
          (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS
            (schemeSpace V).1 (schemeSpace V).2).O)).obj
          ((Space.modulePullback B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
            (Space.associatedInvertibleSheaf B S hS Y D hD)),
        ∀ (U : Space.SmallEtale B S hS (yoneda.obj V))
          (hU : ⊤ ≤ (BigFppfOver.toScheme B S hS).map (yoneda.preimage U.1.hom) ⁻¹ᵁ
            E.support.compl),
          (show ((Space.modulePullback B S hS
                (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
                (Space.associatedInvertibleSheaf B S hS Y D hD)).val.obj (op U) from
            σ.1 (op U)) =
            (show Space.chartRing B S hS (schemeSpace V).1 (schemeSpace V).2 U from
              ((BigFppfOver.toScheme B S hS).map (yoneda.preimage U.1.hom)).appLE
                E.support.compl ⊤ hU f) •
              (show ((Space.modulePullback B S hS
                  (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
                  (Space.associatedInvertibleSheaf B S hS Y D hD)).val.obj (op U) from
                ((Space.globalSectionsPullbackMap B S hS
                  (ObjectProperty.homMk q : schemeSpace V ⟶ Y) _).hom
                  (Space.canonicalSection B S hS Y D hD)).1 (op U)) := by
  obtain ⟨e1, he1⟩ := exists_pulledIdealIso B S hS V q D hD E hE hpre
  obtain ⟨γ, hγ⟩ := exists_representedIdealIso B S hS V E (isAlgebraicSpace_yoneda B S hS V)
  have := isInvertible_modulePullback_idealSheafOfModules B S hS
    (ObjectProperty.homMk q : schemeSpace V ⟶ Y) D hD
  let τ : (Space.modulePullback B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
      (Space.idealSheafOfModules B S hS Y D) ⟶
      𝟙_ (SheafOfModules.{u} (Space.structureRingSheaf B S hS (schemeSpace V))) :=
    e1.hom ≫ γ.inv ≫ (Space.representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS
        V)).map
      (divisorSectionIdealHom E t) ≫ (Space.representedAssociatedModuleObjUnitIso B S hS V
          (isAlgebraicSpace_yoneda B S hS V)).hom
  refine ⟨sectionOfHom B S hS (schemeSpace V)
    (pulledEvaluation B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y) D hD) τ,
    fun U hU => ?_⟩
  refine sectionOfHom_val_eq_smul B S hS (schemeSpace V)
    (pulledEvaluation B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y) D hD)
    (pulledIdealInclusion B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y) D) _
    (curries_pulledCanonicalSection B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y) D hD) τ U _
    (fun V' q' x => ?_)
  have hV' := top_le_preimage_of_hom B S hS V q' hU
  have hr := structureCommRings_map_appLE B S hS V q' hU f
  have hc := associatedModuleMapAwayFromSupport B S hS V E (divisorSectionIdealHom E t) f
    (fun W hW y => divisorSectionIdealHom_app_eq_mul E t f ht W hW y) V'.unop hV'
    ((γ.inv.val.app V').hom ((e1.hom.val.app V').hom x))
  have h2 : ((pulledIdealInclusion B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y) D).val.app
      V').hom x =
      ((Space.representedAssociatedModuleObjUnitIso B S hS V
        (isAlgebraicSpace_yoneda B S hS V)).hom.val.app V').hom
        (((Space.representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS V)).map
          (Stacks.ClosedSubscheme.idealIota E)).val.app V'
          ((γ.inv.val.app V').hom ((e1.hom.val.app V').hom x))) := by
    have ha := congrArg (fun m => (m.val.app V').hom x) he1
    have hb := congrArg (fun m => (m.val.app V').hom
      ((γ.inv.val.app V').hom ((e1.hom.val.app V').hom x))) hγ
    have hc' := congrArg (fun m => (m.val.app V').hom ((e1.hom.val.app V').hom x)) γ.inv_hom_id
    refine ha.symm.trans ?_
    refine (congrArg (fun y => ((Space.definingIdealSheaf B S hS (schemeSpace V)
      (Space.closedSubspaceOfIdeal V E)).ι.val.app V').hom y) hc'.symm).trans ?_
    exact hb
  have hlin := ((Space.representedAssociatedModuleObjUnitIso B S hS V
      (isAlgebraicSpace_yoneda B S hS V)).hom.val.app V').hom.map_smul
    (show Space.chartRing B S hS (yoneda.obj V) (isAlgebraicSpace_yoneda B S hS V) V'.unop from
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage V'.unop.1.hom)).appLE
        E.support.compl ⊤ hV' f)
    (((Space.representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS V)).map
          (Stacks.ClosedSubscheme.idealIota E)).val.app V'
          ((γ.inv.val.app V').hom ((e1.hom.val.app V').hom x)))
  have key := (congrArg (fun w => ((Space.representedAssociatedModuleObjUnitIso B S hS V
      (isAlgebraicSpace_yoneda B S hS V)).hom.val.app V').hom w) hc).trans hlin
  have h2' : ((Stacks.SheafOfModules.Invertible.valPresheafMap
      (Space.structureCommRings B S hS (schemeSpace V))
      (Space.structureRingSheaf B S hS (schemeSpace V)).property
      (pulledIdealInclusion B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y) D)).app V').hom x =
      ((Space.representedAssociatedModuleObjUnitIso B S hS V
        (isAlgebraicSpace_yoneda B S hS V)).hom.val.app V').hom
        (((Space.representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS V)).map
          (Stacks.ClosedSubscheme.idealIota E)).val.app V'
          ((γ.inv.val.app V').hom ((e1.hom.val.app V').hom x))) := h2
  have hr' : ((Space.structureCommRings B S hS (schemeSpace V)).map q'.op).hom
      (show Space.chartRing B S hS (schemeSpace V).1 (schemeSpace V).2 U from
        ((BigFppfOver.toScheme B S hS).map (yoneda.preimage U.1.hom)).appLE
          E.support.compl ⊤ hU f) =
      ((BigFppfOver.toScheme B S hS).map (yoneda.preimage V'.unop.1.hom)).appLE
        E.support.compl ⊤ hV' f := hr
  rw [h2', hr']
  exact key

open Stacks.SheafOfModules.Invertible in
/-- **`q^*𝒪_Y(D) ≅ Φ(𝒪_V(E))`.**  Both modules carry a pairing against the invertible module
`q^*𝓘_D` with values in `𝒪`: the pulled-back evaluation pairing, and the transport along `Φ`
of the evaluation pairing `𝒪_V(E) ⊗ ℐ_E ≅ 𝒪_V` through `q^*𝓘_D ≅ 𝓘_{Z_E} ≅ Φ(ℐ_E)`. -/
theorem nonempty_pulledInvertibleSheafIso (Y : AlgebraicSpaces B S hS) (V : BigFppfOver B S hS)
    (q : yoneda.obj V ⟶ Y.obj) (D : Space.ClosedSubspaces B S hS Y.obj)
    (hD : Space.IsEffectiveCartierDivisor B S hS Y D)
    (E : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor E)
    (hpre : D.1.preimage q = (Space.closedSubspaceOfIdeal V E).1) :
    Nonempty ((Space.modulePullback B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
        (Space.associatedInvertibleSheaf B S hS Y D hD) ≅
      (show SheafOfModules.{u} (Space.structureRingSheaf B S hS (schemeSpace V)) from
        (Space.representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS V)).obj
          (Stacks.Divisors.divisorSheaf E))) := by
  obtain ⟨e1, -⟩ := exists_pulledIdealIso B S hS V q D hD E hE hpre
  obtain ⟨γ, -⟩ := exists_representedIdealIso B S hS V E (isAlgebraicSpace_yoneda B S hS V)
  have := isInvertible_modulePullback_idealSheafOfModules B S hS
    (ObjectProperty.homMk q : schemeSpace V ⟶ Y) D hD
  have : AlgebraicGeometry.SheafOfModules.IsInvertible
      ((BigFppfOver.toScheme B S hS).obj V).presheaf
      (structureSheafRing ((BigFppfOver.toScheme B S hS).obj V).toRingedSpace).property
      (Stacks.Divisors.negativeTwist' E) := hE
  let evE : ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨((BigFppfOver.toScheme B S hS).obj V).presheaf, Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ CommRingCat RingCat)
        (structureSheafRing ((BigFppfOver.toScheme B S hS).obj V).toRingedSpace).property⟩).obj
        (Stacks.Divisors.divisorSheaf E)).obj E.unitSubmodule.toSheafOfModules ≅
      SheafOfModules.unit (structureSheafRing ((BigFppfOver.toScheme B S hS).obj V).toRingedSpace)
          :=
    tensorProductIso _ _ (Iso.refl _) E.unitSubmoduleIsoIdealSheaf ≪≫
      Stacks.SheafOfModules.Scheme.evaluationIso _ (Stacks.Divisors.negativeTwist' E)
  let evN : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ⟨Space.structureCommRings B S hS (schemeSpace V), Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ CommRingCat RingCat)
        (Space.structureRingSheaf B S hS (schemeSpace V)).property⟩).obj
        (show SheafOfModules.{u} (Space.structureRingSheaf B S hS (schemeSpace V)) from
          (Space.representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS V)).obj
            (Stacks.Divisors.divisorSheaf E))).obj
        ((Space.modulePullback B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
          (Space.idealSheafOfModules B S hS Y D)) ≅
      SheafOfModules.unit (Space.structureRingSheaf B S hS (schemeSpace V)) :=
    tensorProductIso (Space.structureCommRings B S hS (schemeSpace V))
        (Space.structureRingSheaf B S hS (schemeSpace V)).property (Iso.refl _) (e1 ≪≫ γ.symm) ≪≫
      (Space.representedAssociatedModuleTensorIso B S hS V (Stacks.Divisors.divisorSheaf E)
        E.unitSubmodule.toSheafOfModules).symm ≪≫
      (Space.representedAssociatedModule B S hS V (isAlgebraicSpace_yoneda B S hS V)).mapIso evE ≪≫
      Space.representedAssociatedModuleObjUnitIso B S hS V (isAlgebraicSpace_yoneda B S hS V)
  obtain ⟨φ, -⟩ := exists_iso_of_tensorPairing (Space.structureCommRings B S hS (schemeSpace V))
    (Space.structureRingSheaf B S hS (schemeSpace V)).property _ _ _ _
    (pulledEvaluation B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y) D hD) evN
  exact ⟨φ⟩

section Cohomology

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [local instance] Space.hasInjectiveResolutions_modules

/-- **Clause (1) of `AlgebraicGeometry.C1590Private.FibreDivisorSheafComparison`.**  If
`H¹(V, 𝒪_V(E)) = 0` then `H¹(h_V, q^*𝒪_Y(D)) = 0`. -/
theorem isZero_rightDerived_one_pulledInvertibleSheaf (Y : AlgebraicSpaces B S hS)
    (V : BigFppfOver B S hS)
    (q : yoneda.obj V ⟶ Y.obj) (D : Space.ClosedSubspaces B S hS Y.obj)
    (hD : Space.IsEffectiveCartierDivisor B S hS Y D)
    (E : ((BigFppfOver.toScheme B S hS).obj V).IdealSheafData)
    (hE : Stacks.Divisors.IsEffectiveCartierDivisor E)
    (hpre : D.1.preimage q = (Space.closedSubspaceOfIdeal V E).1)
    (hH : Limits.IsZero (Hgroup ((BigFppfOver.toScheme B S hS).obj V).ringCatSheaf ⊤ 1
        (Stacks.Divisors.divisorSheaf E))) :
    Limits.IsZero (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS
          (schemeSpace V).1 (schemeSpace V).2).O)).rightDerived 1).obj
          ((Space.modulePullback B S hS (ObjectProperty.homMk q : schemeSpace V ⟶ Y)).obj
            (Space.associatedInvertibleSheaf B S hS Y D hD))) := by
  obtain ⟨φ⟩ := nonempty_pulledInvertibleSheafIso B S hS Y V q D hD E hE hpre
  have := hE
  have hq : SheafOfModules.IsQuasicoherent (Stacks.Divisors.divisorSheaf E) :=
    Stacks.AbelMap.isQuasicoherent_divisorSheaf E
  exact (representedFirstCohomologyVanishing B S hS V _ hq hH).of_iso
    (((globalSectionsFunctor.{u + 1, u, u, u}
        (Stacks.SheafOfModules.Tensor.ringSheaf (Space.smallEtaleRingedSite B S hS
          (schemeSpace V).1 (schemeSpace V).2).O)).rightDerived 1).mapIso φ)

end Cohomology

end Assembly

section Final

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

/-- **Piece (c) of P3 of the route to Stacks 0E6F**, proved:
`AlgebraicGeometry.C1590Private.FibreDivisorSheafComparison`. -/
theorem fibreDivisorSheafComparison : FibreDivisorSheafComparison B hZ :=
  fun Y V q D hD E hE hpre =>
    ⟨isZero_rightDerived_one_pulledInvertibleSheaf B integerBase hZ Y V q D hD E hE hpre,
      fun t f ht => exists_section_eq_smul_canonicalSection B integerBase hZ
        Y V q D hD E hE hpre t f ht⟩

end Final

end AlgebraicGeometry.C1590Private
