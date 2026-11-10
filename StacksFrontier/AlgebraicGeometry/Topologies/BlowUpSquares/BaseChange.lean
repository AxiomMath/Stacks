module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.InverseImageCentre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Topologies.BlowUpSquares.Shrinking

/-!
# Base change of an almost blowup square

An almost blowup square is stable under arbitrary base change: if `b : X' ⟶ X` is the
modification of an almost blowup square with centre the quasi-coherent ideal `I`, and `f : Y ⟶ X`
is any morphism, then the projection `X ×_X' Y ⟶ Y` is the modification of an almost blowup
square with centre `I·𝒪_Y`.

## Main results

* `AlgebraicGeometry.finitePresentation_pullback_fst`: finite presentation is stable under base
  change.
* `AlgebraicGeometry.pullbackOverIso`: an isomorphism of schemes over `X` base changes to an
  isomorphism of schemes over `Y`.
* `AlgebraicGeometry.isIso_restrict_of_ker_comap_eq_bot`: a closed immersion restricts to an
  isomorphism over an open on which its inverse-image kernel vanishes.
* `AlgebraicGeometry.isAlmostBlowUpSquare_baseChange`: an almost blowup square base changes to an
  almost blowup square.

## References

* [Stacks Project, Tag 0EV7](https://stacks.math.columbia.edu/tag/0EV7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- Finite presentation is stable under base change. -/
public theorem finitePresentation_pullback_fst {A B C : Scheme.{u}} (g : B ⟶ C) (f : A ⟶ C)
    (hg : FinitePresentation g) : FinitePresentation (pullback.fst f g) := by
  have := hg.locallyOfFinitePresentation
  have := hg.quasiCompact
  have := hg.quasiSeparated
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- The support of an inverse image of an ideal sheaf is the preimage of its support. -/
private theorem coe_support_comap {A B : Scheme.{u}} (J : B.IdealSheafData) (g : A ⟶ B) :
    ((J.comap g).support : Set A) = g.base ⁻¹' J.support := by
  simp only [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage]

/-- The support of the inverse image of a centre in the base change of a modification is the
preimage of the support of the inverse-image centre, read through the other projection. -/
public theorem exceptionalSupport_baseChange {X X' Y : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) (f : Y ⟶ X) :
    ((I.comap f).comap (pullback.fst f b)).support =
      (I.comap b).support.preimage (pullback.snd f b).continuous := by
  rw [← Scheme.IdealSheafData.comap_comp, Scheme.IdealSheafData.support_comap,
    Scheme.IdealSheafData.support_comap]
  ext x
  change (pullback.fst f b ≫ f).base x ∈ I.support ↔ (pullback.snd f b ≫ b).base x ∈ I.support
  rw [pullback.condition (f := f) (g := b)]

/-- The fibre product `Y ×_X C`, as a scheme over `Y`, is the base change of `C` along `f`
given by `CategoryTheory.Over.pullback`. -/
public noncomputable def pullbackFstIsoOverPullback {X Y C : Scheme.{u}} (f : Y ⟶ X) (h : C ⟶ X) :
    Over.mk (pullback.fst f h) ≅ (Over.pullback f).obj (Over.mk h) :=
  Over.isoMk (pullbackSymmetry f h) (by simp)

/-- An isomorphism of schemes over `X` induces an isomorphism of their base changes to `Y`, as
schemes over `Y`. -/
public noncomputable def pullbackOverIso {X Y A B : Scheme.{u}} (f : Y ⟶ X) (g : A ⟶ X) (k : B ⟶ X)
    (e : Over.mk g ≅ Over.mk k) :
    Over.mk (pullback.fst f g) ≅ Over.mk (pullback.fst f k) :=
  pullbackFstIsoOverPullback f g ≪≫ (Over.pullback f).mapIso e ≪≫
    (pullbackFstIsoOverPullback f k).symm

/-- A closed immersion restricts to an isomorphism over an open whose inverse-image kernel
vanishes. -/
public theorem isIso_restrict_of_ker_comap_eq_bot {P Q : Scheme.{u}} (f : Q ⟶ P)
    [IsClosedImmersion f] (U : P.Opens) (h : f.ker.comap U.ι = ⊥) : IsIso (f ∣_ U) := by
  rw [IsClosedImmersion.isIso_iff_ker_eq_bot, ker_morphismRestrict_eq_comap, h]

/-- An almost blowup square stays an almost blowup square after an arbitrary base change: the new
centre is the inverse image of the old one and the new modification is the base change of the
old one. -/
@[stacks 0EV7]
public theorem isAlmostBlowUpSquare_baseChange {X X' Y : Scheme.{u}} (I : X.IdealSheafData)
    (b : X' ⟶ X) (f : Y ⟶ X) (h : IsAlmostBlowUpSquare I b) :
    IsAlmostBlowUpSquare (I.comap f) (pullback.fst f b) := by
  refine ⟨?_, ?_, ?_, finitePresentation_pullback_fst b f h.finitePresentation, ?_⟩
  · have hfp := finitePresentation_pullback_fst I.subschemeι f h.center_finitePresentation
    have hIso : FinitePresentation (I.comapIso f).hom :=
      ⟨inferInstance, inferInstance, inferInstance⟩
    rw [← Scheme.IdealSheafData.comapIso_hom_fst]
    exact ⟨MorphismProperty.comp_mem _ _ _ hIso.locallyOfFinitePresentation
        hfp.locallyOfFinitePresentation,
      MorphismProperty.comp_mem _ _ _ hIso.quasiCompact hfp.quasiCompact,
      MorphismProperty.comp_mem _ _ _ hIso.quasiSeparated hfp.quasiSeparated⟩
  · convert Stacks.Divisors.isLocallyPrincipal_comap (pullback.snd f b) (I.comap b)
      h.exceptional_locallyPrincipal using 1
    rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp]
    congr 1
    exact pullback.condition
  · have : IsProper b := h.proper
    infer_instance
  · let P : Scheme.{u} := pullback f b
    let p₁ : P ⟶ Y := pullback.fst f b
    let p₂ : P ⟶ X' := pullback.snd f b
    let E : Set X' := (I.comap b).support
    have hEclosed : IsClosed E := (I.comap b).support.isClosed
    let J : X'.IdealSheafData := supportedSectionsIdeal E
    let Q : Scheme.{u} := pullback p₂ J.subschemeι
    let i : Q ⟶ P := pullback.fst p₂ J.subschemeι
    let EP : Set P := ((I.comap f).comap p₁).support
    have hEPclosed : IsClosed EP := ((I.comap f).comap p₁).support.isClosed
    let V : X'.Opens := ⟨Eᶜ, hEclosed.isOpen_compl⟩
    let U : P.Opens := p₂ ⁻¹ᵁ V
    have hEP : EP = p₂.base ⁻¹' E := by
      simpa [EP, E] using congrArg (fun Z : TopologicalSpace.Closeds P => (Z : Set P))
        (exceptionalSupport_baseChange I b f)
    have hUEP : U = ⟨EPᶜ, hEPclosed.isOpen_compl⟩ := by
      ext x
      simp [U, V, hEP, Set.preimage_compl]
    have hVker : J = V.ι.ker := supportedSectionsIdeal_eq_complementKernel E hEclosed
    have hfactor : U.ι ≫ p₂ = (p₂ ∣_ V) ≫ V.ι := (morphismRestrict_ι p₂ V).symm
    have hcomap : i.ker.comap U.ι = ⊥ := by
      calc
        i.ker.comap U.ι = (J.comap p₂).comap U.ι := by
          simp [i, Scheme.IdealSheafData.ker_fst_of_isClosedImmersion]
        _ = J.comap (U.ι ≫ p₂) := by rw [← Scheme.IdealSheafData.comap_comp]
        _ = J.comap ((p₂ ∣_ V) ≫ V.ι) := by rw [hfactor]
        _ = (J.comap V.ι).comap (p₂ ∣_ V) := Scheme.IdealSheafData.comap_comp J _ V.ι
        _ = ⊥ := by rw [hVker, ker_comap_self, Scheme.IdealSheafData.comap_bot]
    have hi : IsIso (i ∣_ (⟨EPᶜ, hEPclosed.isOpen_compl⟩ : P.Opens)) := by
      rw [← hUEP]
      exact isIso_restrict_of_ker_comap_eq_bot i U hcomap
    let assocOver : Over.mk (i ≫ p₁) ≅ Over.mk (pullback.fst f (J.subschemeι ≫ b)) :=
      Over.isoMk (pullbackLeftPullbackSndIso f b J.subschemeι) (by simp [i, p₁, p₂])
    let baseOver : Over.mk (pullback.fst f (J.subschemeι ≫ b)) ≅
        Over.mk (pullback.fst f (blowUpToBase I)) :=
      pullbackOverIso f (J.subschemeι ≫ b) (blowUpToBase I) (Classical.choice h.blowUp)
    let e : Over.mk (i ≫ p₁) ≅ Over.mk (pullback.fst f (blowUpToBase I)) :=
      assocOver ≪≫ baseOver
    let W : Scheme.{u} := pullback f (blowUpToBase I)
    let q : Q ⟶ W := e.hom.left
    let ZB : Set W :=
      (pullback.snd f (blowUpToBase I)).base ⁻¹' (exceptionalIdeal I).support
    have hZBclosed : IsClosed ZB :=
      (exceptionalIdeal I).support.isClosed.preimage
        (pullback.snd f (blowUpToBase I)).continuous
    let K : Q.IdealSheafData := supportedSectionsIdeal (q.base ⁻¹' ZB)
    let D : P.IdealSheafData := supportedSectionsIdeal EP
    have hqiso : IsIso q := (Over.forget Y).map_isIso e.hom
    have hq : i ≫ p₁ = q ≫ pullback.fst f (blowUpToBase I) := (Over.w e.hom).symm
    have hbase : i ≫ p₂ ≫ b = q ≫ pullback.snd f (blowUpToBase I) ≫ blowUpToBase I := by
      have hp : p₂ ≫ b = p₁ ≫ f := pullback.condition.symm
      rw [hp, reassoc_of% hq, pullback.condition]
    have hset : i.base ⁻¹' EP = q.base ⁻¹' ZB := by
      ext x
      simp only [hEP, E, ZB, exceptionalIdeal, Set.mem_preimage, coe_support_comap]
      change (i ≫ p₂ ≫ b).base x ∈ I.support ↔
        (q ≫ pullback.snd f (blowUpToBase I) ≫ blowUpToBase I).base x ∈ I.support
      rw [hbase]
    have hmapK : K.map i = D := by
      dsimp only [K, D]
      rw [← hset]
      exact supportedSectionsIdeal_map_of_restrict_isIso i EP hEPclosed hi
    have hTeq : Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I) =
        supportedSectionsIdeal ZB := by
      rw [Stacks.StrictTransform.ideal_eq_ker_ι,
        supportedSectionsIdeal_eq_complementKernel ZB hZBclosed]
      congr 1
    have hmapT : K.map q =
        Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I) := by
      rw [hTeq]
      exact supportedSectionsIdeal_map_of_restrict_isIso q ZB hZBclosed inferInstance
    let e₁ := (Over.map p₁).mapIso (idealMapSubschemeIso i K D hmapK)
    let e₂ := (Over.map (pullback.fst f (blowUpToBase I))).mapIso
      (idealMapSubschemeIso q K _ hmapT)
    let eK : Over.mk ((K.subschemeι ≫ i) ≫ p₁) ≅
        Over.mk ((K.subschemeι ≫ q) ≫ pullback.fst f (blowUpToBase I)) :=
      Over.isoMk (Iso.refl K.subscheme) (by simp [hq])
    exact ⟨e₁ ≪≫ eK ≪≫ e₂.symm ≪≫ strictTransformBlowUpIso f I⟩

end AlgebraicGeometry

end
