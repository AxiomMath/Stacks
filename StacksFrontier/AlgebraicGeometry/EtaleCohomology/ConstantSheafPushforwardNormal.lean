module

public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Normal
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleQuasiFinite
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericPointDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExamplesSheaves.ConstantSheafSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDirectImages
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtalePointUniverse
public import StacksFrontier.AlgebraicGeometry.Properties.FiniteIrreducibleComponents

/-!
# Direct image of a constant sheaf of sets from the generic point or a nonempty open

Let `X` be an integral normal scheme. The direct image of a constant sheaf of sets on the small
étale site along the inclusion `Spec K ⟶ X` of the generic point, `K` the function field, is
again the constant sheaf; the same holds along the inclusion of a nonempty open subscheme.

## Main definitions

* `Stacks.EtaleCohomology.constantToPushforwardConstant`: the constant section of the constant
  sheaf on `Y` over the base change of an étale `X`-scheme.
* `Stacks.EtaleCohomology.constantSheafPushforwardComparison`: the canonical comparison from the
  constant sheaf on `X` to the direct image of the constant sheaf along a morphism `Y ⟶ X`.
* `Stacks.EtaleCohomology.constantSheafGenericPointPushforwardIso` and
  `Stacks.EtaleCohomology.constantSheafOpensPushforwardIso`: the two identifications of the
  direct image with the constant sheaf.

## Main results

* `Stacks.EtaleCohomology.exists_isIntegral_open_of_etale`: a point of a scheme étale over an
  integral normal scheme lies in an integral open subscheme.
* `Stacks.EtaleCohomology.subsingleton_pullback_genericPointInclusion`: the generic fibre of an
  integral scheme étale over an integral scheme has at most one point.
* `Stacks.EtaleCohomology.isIso_constantSheafPushforwardComparison_genericPointInclusion`: the
  comparison is an isomorphism along the inclusion of the generic point.
* `Stacks.EtaleCohomology.isIso_constantSheafPushforwardComparison_opensIota`: the comparison is
  an isomorphism along the inclusion of a nonempty open subscheme.

## References

* [Stacks Project, Lemma 59.73.13 (Tag 09Z5)](https://stacks.math.columbia.edu/tag/09Z5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u₁ v₁ w u v

namespace Stacks.EtaleCohomology

/-! ### Sheafification of a locally bijective morphism -/

/-- A locally bijective morphism from a presheaf of sets to a sheaf of sets induces an
isomorphism out of the sheafification. -/
private theorem isIso_mk_sheafifyLift {C : Type u₁} [Category.{v₁} C]
    (J : GrothendieckTopology C) [HasWeakSheafify J (Type w)]
    [J.WEqualsLocallyBijective (Type w)] {P : Cᵒᵖ ⥤ Type w} {Q : Sheaf J (Type w)}
    (η : P ⟶ Q.obj) (α : (presheafToSheaf J (Type w)).obj P ⟶ Q)
    (hα : toSheafify J P ≫ α.hom = η)
    (h₁ : Presheaf.IsLocallyInjective J η) (h₂ : Presheaf.IsLocallySurjective J η) :
    IsIso α := by
  have h : α = ((sheafificationAdjunction J (Type w)).homEquiv P Q).symm η :=
    Sheaf.hom_ext_iff.mpr (sheafifyLift_unique J η Q.property α.hom hα)
  rw [h, Adjunction.homEquiv_counit]
  have : IsIso ((presheafToSheaf J (Type w)).map η) := by
    rw [← J.W_iff]
    exact (J.W_iff_isLocallyBijective η).mpr ⟨h₁, h₂⟩
  infer_instance

/-! ### Integral objects cover the small étale site of an integral normal scheme -/

/-- Every quasi-compact open of an integral scheme has finitely many irreducible components. -/
theorem finiteIrreducibleComponents_of_isIntegral (X : Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] :
    ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite := by
  intro U _
  rcases isEmpty_or_nonempty U with hU | hU
  · exact Set.finite_univ.subset (Set.subset_univ _)
  · simp [irreducibleComponents_eq_singleton]

/-- Every point of a scheme étale over an integral normal scheme lies in the image of an open
immersion from an integral scheme. -/
theorem exists_isIntegral_open_of_etale {X Y : Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [IsNormal X] (f : Y ⟶ X) [Etale f] (y : Y) :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ Y), IsOpenImmersion g ∧ AlgebraicGeometry.IsIntegral Z ∧
      y ∈ Set.range g.base := by
  let : IsNormal Y := isNormal_of_etale f
  obtain ⟨ι, W, hWnormal, hWintegral, ⟨e⟩⟩ :=
    (isNormal_iff_exists_iso_coproduct
      (finiteIrreducibleComponents_of_etale f
        (finiteIrreducibleComponents_of_isIntegral X))).mp inferInstance
  obtain ⟨⟨i, z⟩, hz⟩ := (AlgebraicGeometry.sigmaMk W).surjective (e.hom y)
  refine ⟨W i, Sigma.ι W i ≫ e.inv, inferInstance, hWintegral i, z, ?_⟩
  have h : (Sigma.ι W i) z = e.hom y := by simpa only [sigmaMk_mk] using hz
  show e.inv ((Sigma.ι W i) z) = y
  rw [h]
  exact congrArg (fun k : Y ⟶ Y ↦ k y) e.hom_inv_id

/-! ### The generic fibre and the fibre over a nonempty open -/

/-- The generic fibre of an integral scheme étale over an integral scheme has at most one
point. -/
theorem subsingleton_pullback_genericPointInclusion {X Z : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [AlgebraicGeometry.IsIntegral Z] (q : Z ⟶ X) [Etale q] :
    Subsingleton ↥(pullback q (genericPointInclusion X)) := by
  let g := genericPointInclusion X
  let p := pullback.fst q g
  have : LocallyQuasiFinite q := (locallyQuasiFinite_of_etale q).2
  have : IsPreimmersion g :=
    inferInstanceAs (IsPreimmersion (X.fromSpecStalk (genericPoint X)))
  have : Subsingleton ↥(Spec X.functionField) :=
    inferInstanceAs (Subsingleton (PrimeSpectrum X.functionField))
  have hη : ∀ z : ↥(Spec X.functionField), g z = genericPoint X := by
    intro z
    rw [Subsingleton.elim z (IsLocalRing.closedPoint X.functionField)]
    exact genericPointInclusion_closedPoint X
  have hp : ∀ z : ↥(pullback q g), q (p z) = genericPoint X := by
    intro z
    calc q (p z) = g (pullback.snd q g z) :=
          congrArg (fun k : (pullback q g : Scheme.{u}) ⟶ X ↦ k z) pullback.condition
      _ = _ := hη _
  have hgen : q (genericPoint Z) = genericPoint X := by
    have h : q (genericPoint Z) ∈ genericPoints X :=
      genericPoints_image_of_generalizingMap q.base (Flat.generalizingMap q)
        (by rw [genericPoints_eq_singleton]; exact Set.mem_singleton _)
    rwa [genericPoints_eq_singleton, Set.mem_singleton_iff] at h
  have : DiscreteTopology ↥(q.base ⁻¹' {genericPoint X}) :=
    isDiscrete_iff_discreteTopology.mp (q.isDiscrete_preimage_singleton _)
  have heq : ∀ z : ↥(pullback q g), genericPoint Z = p z := by
    intro z
    have h : (⟨genericPoint Z, hgen⟩ : ↥(q.base ⁻¹' {genericPoint X})) ⤳ ⟨p z, hp z⟩ :=
      Topology.IsEmbedding.subtypeVal.toIsInducing.specializes_iff.mp
        (genericPoint_specializes _)
    exact congrArg Subtype.val h.eq
  exact ⟨fun a b ↦ p.isEmbedding.injective ((heq a).symm.trans (heq b))⟩

/-- For `q : Z ⟶ X` étale with `Z` nonempty and `X` irreducible, the base change `Z ×_X U` along
the inclusion of a nonempty open subscheme `U` is nonempty. -/
theorem nonempty_pullback_opensIota {X Z : Scheme.{u}} [IrreducibleSpace X] [Nonempty Z]
    (q : Z ⟶ X) [Etale q] (U : X.Opens) (hU : (U : Set X).Nonempty) :
    Nonempty ↥(pullback q U.ι) := by
  obtain ⟨x, ⟨z, hz⟩, hxU⟩ := (U.isOpen.dense hU).inter_open_nonempty (Set.range q.base)
    q.isOpenMap.isOpen_range (Set.range_nonempty q.base)
  have hzU : z ∈ Set.range (pullback.fst q U.ι).base := by
    rw [Scheme.Pullback.range_fst]
    exact ⟨⟨x, hxU⟩, hz.symm⟩
  exact ⟨hzU.choose⟩

/-- The fibre of an irreducible scheme over an open subscheme is preirreducible. -/
theorem preirreducibleSpace_pullback_opensIota {X Z : Scheme.{u}} [IrreducibleSpace Z]
    (q : Z ⟶ X) (U : X.Opens) : PreirreducibleSpace ↥(pullback q U.ι) :=
  (pullback.fst q U.ι).isOpenEmbedding.preirreducibleSpace

/-! ### The constant sheaf of sets as continuous maps into a discrete set -/

variable (X : Scheme.{u}) (E : Type (max (u + 1) v))

/-- The presheaf of sets on the small étale site of `X` sending an étale `X`-scheme to the
continuous `E`-valued maps on it. -/
private abbrev etaleContinuousPresheaf [TopologicalSpace E] :
    (X.Etale)ᵒᵖ ⥤ Type (max (u + 1) v) :=
  (Scheme.Etale.forget X ⋙ Over.forget X).op ⋙ continuousMapPresheaf.{max (u + 1) v, u} E

/-- Continuous `E`-valued maps form a sheaf of sets on the small étale site. -/
private theorem etaleContinuousPresheaf_isSheaf [TopologicalSpace E] :
    Presheaf.IsSheaf X.smallEtaleTopology (etaleContinuousPresheaf.{u, v} X E) :=
  Functor.op_comp_isSheaf_of_isSheaf (Scheme.Etale.forget X) _
    (Scheme.etaleTopology.{u}.over X) _
    (Functor.op_comp_isSheaf_of_isSheaf (Over.forget X) _ Scheme.etaleTopology.{u} _
      ((isSheaf_fpqcTopology_continuousMapPresheaf.{max (u + 1) v, u} E).of_le
        Stacks.Sites.etaleTopology_le_fpqcTopology))

/-- Continuous `E`-valued maps as a sheaf of sets on the small étale site of `X`. -/
private abbrev etaleContinuousSheaf [TopologicalSpace E] :
    Sheaf X.smallEtaleTopology (Type (max (u + 1) v)) :=
  ⟨etaleContinuousPresheaf.{u, v} X E, etaleContinuousPresheaf_isSheaf.{u, v} X E⟩

/-- The map of presheaves on the small étale site of `X` sending `e : E` to the constant map
with value `e`. -/
private def constantToEtaleContinuous [TopologicalSpace E] :
    (Functor.const (X.Etale)ᵒᵖ).obj E ⟶ etaleContinuousPresheaf.{u, v} X E where
  app W := TypeCat.ofHom fun e ↦ ContinuousMap.const (↥W.unop.left) e
  naturality _ _ _ := rfl

/-- A sieve on an object of the small étale site is covering if it is the top sieve whenever the
object is nonempty. -/
private theorem sieve_mem_smallEtaleTopology_of_nonempty {X : Scheme.{u}} {W : X.Etale}
    {S : Sieve W} (h : Nonempty ↥W.left → S = ⊤) : S ∈ X.smallEtaleTopology W := by
  by_cases hW : Nonempty ↥W.left
  · rw [h hW]
    exact X.smallEtaleTopology.top_mem _
  · exact X.smallEtaleTopology.superset_covering bot_le
      (AlgebraicGeometry.smallEtale_bot_mem X (not_nonempty_iff.mp hW))

/-- Two elements of `E` with the same constant map agree locally on the small étale site. -/
private theorem constantToEtaleContinuous_isLocallyInjective [TopologicalSpace E] :
    Presheaf.IsLocallyInjective X.smallEtaleTopology (constantToEtaleContinuous.{u, v} X E) where
  equalizerSieve_mem {W} a b hab := by
    refine sieve_mem_smallEtaleTopology_of_nonempty fun ⟨x⟩ ↦ ?_
    have hab' : a = b := congrArg (fun c : C(↥W.unop.left, E) ↦ c x) hab
    subst hab'
    exact Presheaf.equalizerSieve_self_eq_top _

/-- Every continuous map into a discrete set is locally constant on the small étale site. -/
private theorem constantToEtaleContinuous_isLocallySurjective [TopologicalSpace E]
    [DiscreteTopology E] :
    Presheaf.IsLocallySurjective X.smallEtaleTopology (constantToEtaleContinuous.{u, v} X E) where
  imageSieve_mem {W} s := by
    change C(↥W.left, E) at s
    let O : E → W.left.Opens := fun e ↦
      ⟨s ⁻¹' {e}, s.continuous.isOpen_preimage _ (isOpen_discrete _)⟩
    let Z : E → X.Etale := fun e ↦ Scheme.Etale.mk ((O e).ι ≫ W.hom)
    let k : ∀ e, Z e ⟶ W := fun e ↦ MorphismProperty.Over.homMk (O e).ι
    apply X.smallEtaleTopology.superset_covering
      ((Sieve.generate_le_iff _ _).mpr (Presieve.ofArrows_le_iff.mpr ?_))
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff k).mpr ?_)
    · intro e
      refine ⟨e, ?_⟩
      simp only [constantToEtaleContinuous]
      exact ContinuousMap.ext fun x ↦ x.property.symm
    · ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨s x, ⟨x, rfl⟩, rfl⟩

/-- The canonical map from the constant sheaf of sets with value `E` on the small étale site of
`X` to the sheaf of continuous `E`-valued maps. -/
private def constantSheafToEtaleContinuous [TopologicalSpace E] :
    (constantSheaf X.smallEtaleTopology (Type (max (u + 1) v))).obj E ⟶
      etaleContinuousSheaf.{u, v} X E :=
  ⟨sheafifyLift X.smallEtaleTopology (constantToEtaleContinuous.{u, v} X E)
    (etaleContinuousPresheaf_isSheaf.{u, v} X E)⟩

/-- **The constant sheaf of sets is the sheaf of continuous maps into the discrete set.** -/
private theorem isIso_constantSheafToEtaleContinuous [TopologicalSpace E]
    [DiscreteTopology E] : IsIso (constantSheafToEtaleContinuous.{u, v} X E) := by
  have : X.smallEtaleTopology.WEqualsLocallyBijective (Type (max (u + 1) v)) :=
    Scheme.wEqualsLocallyBijective_smallEtaleTopology_type X
  exact isIso_mk_sheafifyLift _ (constantToEtaleContinuous.{u, v} X E) _
    (toSheafify_sheafifyLift _ _ _)
    (constantToEtaleContinuous_isLocallyInjective.{u, v} X E)
    (constantToEtaleContinuous_isLocallySurjective.{u, v} X E)

/-- A continuous map from a preconnected space to a discrete space is constant. -/
private theorem apply_eq_of_preconnectedSpace {A T : Type*} [TopologicalSpace A]
    [TopologicalSpace T] [DiscreteTopology T] [PreconnectedSpace A] (s : C(A, T)) (x y : A) :
    s x = s y :=
  ((IsLocallyConstant.iff_continuous (s : A → T)).mpr
    s.continuous).apply_eq_of_preconnectedSpace x y

/-! ### The comparison morphism and its invertibility -/

section Comparison

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (E : Type (max (u + 1) v))

/-- The map of presheaves on the small étale site of `X` sending `e : E` to the constant section
of the constant sheaf on the small étale site of `Y` over the base change `W ×_X Y` of an étale
`X`-scheme `W`. -/
def constantToPushforwardConstant :
    (Functor.const (X.Etale)ᵒᵖ).obj E ⟶
      ((smallEtaleDirectImage.{u, v} f).obj
        ((constantSheaf Y.smallEtaleTopology (Type (max (u + 1) v))).obj E)).obj :=
  Functor.whiskerLeft (smallEtaleBaseChange f).op
    (toSheafify Y.smallEtaleTopology ((Functor.const (Y.Etale)ᵒᵖ).obj E))

/-- **The canonical comparison from the constant sheaf of sets on `X` to the direct image along
`f : Y ⟶ X` of the constant sheaf of sets on `Y`**: the sheafification of the map carrying
`e : E` to the constant section over the base change `W ×_X Y` of an étale `X`-scheme `W`. -/
def constantSheafPushforwardComparison :
    (constantSheaf X.smallEtaleTopology (Type (max (u + 1) v))).obj E ⟶
      (smallEtaleDirectImage.{u, v} f).obj
        ((constantSheaf Y.smallEtaleTopology (Type (max (u + 1) v))).obj E) :=
  ⟨sheafifyLift X.smallEtaleTopology (constantToPushforwardConstant.{u, v} f E)
    ((smallEtaleDirectImage.{u, v} f).obj
      ((constantSheaf Y.smallEtaleTopology (Type (max (u + 1) v))).obj E)).property⟩

/-- The map of presheaves on the small étale site of `X` sending `e : E` to the constant
`E`-valued map on the base change `W ×_X Y` of an étale `X`-scheme `W`. -/
private def constantToPushforwardContinuous [TopologicalSpace E] :
    (Functor.const (X.Etale)ᵒᵖ).obj E ⟶
      ((smallEtaleDirectImage.{u, v} f).obj (etaleContinuousSheaf.{u, v} Y E)).obj :=
  Functor.whiskerLeft (smallEtaleBaseChange f).op (constantToEtaleContinuous.{u, v} Y E)

/-- Composing the constant-section morphism with the continuous-maps model on `Y` gives the
constant-map morphism. -/
private theorem constantToPushforwardConstant_comp [TopologicalSpace E] :
    constantToPushforwardConstant.{u, v} f E ≫
        ((smallEtaleDirectImage.{u, v} f).map
          (constantSheafToEtaleContinuous.{u, v} Y E)).hom =
      constantToPushforwardContinuous.{u, v} f E := by
  have h2 : toSheafify Y.smallEtaleTopology ((Functor.const (Y.Etale)ᵒᵖ).obj E) ≫
      (constantSheafToEtaleContinuous.{u, v} Y E).hom =
      constantToEtaleContinuous.{u, v} Y E := toSheafify_sheafifyLift _ _ _
  show Functor.whiskerLeft (smallEtaleBaseChange f).op
      (toSheafify Y.smallEtaleTopology ((Functor.const (Y.Etale)ᵒᵖ).obj E) ≫
        (constantSheafToEtaleContinuous.{u, v} Y E).hom) =
    Functor.whiskerLeft (smallEtaleBaseChange f).op (constantToEtaleContinuous.{u, v} Y E)
  rw [h2]

/-- The comparison is an isomorphism as soon as the constant-map morphism into the
continuous-maps model is locally bijective. -/
private theorem isIso_constantSheafPushforwardComparison_of_locallyBijective
    [TopologicalSpace E] [DiscreteTopology E]
    (h₁ : Presheaf.IsLocallyInjective X.smallEtaleTopology
      (constantToPushforwardContinuous.{u, v} f E))
    (h₂ : Presheaf.IsLocallySurjective X.smallEtaleTopology
      (constantToPushforwardContinuous.{u, v} f E)) :
    IsIso (constantSheafPushforwardComparison.{u, v} f E) := by
  have : X.smallEtaleTopology.WEqualsLocallyBijective (Type (max (u + 1) v)) :=
    Scheme.wEqualsLocallyBijective_smallEtaleTopology_type X
  have : IsIso (constantSheafToEtaleContinuous.{u, v} Y E) :=
    isIso_constantSheafToEtaleContinuous.{u, v} Y E
  have hcomp : IsIso (constantSheafPushforwardComparison.{u, v} f E ≫
      (smallEtaleDirectImage.{u, v} f).map (constantSheafToEtaleContinuous.{u, v} Y E)) := by
    refine isIso_mk_sheafifyLift _ (constantToPushforwardContinuous.{u, v} f E) _ ?_ h₁ h₂
    have h : toSheafify X.smallEtaleTopology ((Functor.const (X.Etale)ᵒᵖ).obj E) ≫
        (constantSheafPushforwardComparison.{u, v} f E ≫
          (smallEtaleDirectImage.{u, v} f).map
            (constantSheafToEtaleContinuous.{u, v} Y E)).hom =
        (toSheafify X.smallEtaleTopology ((Functor.const (X.Etale)ᵒᵖ).obj E) ≫
          (constantSheafPushforwardComparison.{u, v} f E).hom) ≫
          ((smallEtaleDirectImage.{u, v} f).map
            (constantSheafToEtaleContinuous.{u, v} Y E)).hom := rfl
    have h2 : toSheafify X.smallEtaleTopology ((Functor.const (X.Etale)ᵒᵖ).obj E) ≫
        (constantSheafPushforwardComparison.{u, v} f E).hom =
        constantToPushforwardConstant.{u, v} f E := toSheafify_sheafifyLift _ _ _
    rw [h, h2]
    exact constantToPushforwardConstant_comp f E
  exact IsIso.of_isIso_comp_right _
    ((smallEtaleDirectImage.{u, v} f).map (constantSheafToEtaleContinuous.{u, v} Y E))

end Comparison

/-! ### Local bijectivity over the integral objects of the site -/

section LocallyBijective

variable {X Y : Scheme.{u}} [AlgebraicGeometry.IsIntegral X] [IsNormal X] (f : Y ⟶ X)
  (E : Type (max (u + 1) v))

/-- If the base change of every integral object of the small étale site of `X` is nonempty, then
so is the base change of every object with a point. -/
private theorem nonempty_pullback_of_point
    (hne : ∀ W : X.Etale, AlgebraicGeometry.IsIntegral W.left → Nonempty ↥(pullback W.hom f))
    (W : X.Etale) (w : W.left) : Nonempty ↥(pullback W.hom f) := by
  obtain ⟨Z, g, hg, hZ, -⟩ :=
    exists_isIntegral_open_of_etale (X := X) (Y := W.left) W.hom w
  obtain ⟨x⟩ := hne (Scheme.Etale.mk (g ≫ W.hom)) hZ
  exact ⟨((smallEtaleBaseChange f).map
    (MorphismProperty.Over.homMk g : Scheme.Etale.mk (g ≫ W.hom) ⟶ W)).left.base x⟩

/-- Two elements of `E` with the same constant map on a base change agree locally on the small
étale site of `X`. -/
private theorem constantToPushforwardContinuous_isLocallyInjective [TopologicalSpace E]
    (hne : ∀ W : X.Etale, AlgebraicGeometry.IsIntegral W.left → Nonempty ↥(pullback W.hom f)) :
    Presheaf.IsLocallyInjective X.smallEtaleTopology
      (constantToPushforwardContinuous.{u, v} f E) where
  equalizerSieve_mem {W} a b hab := by
    refine sieve_mem_smallEtaleTopology_of_nonempty fun ⟨w⟩ ↦ ?_
    obtain ⟨x⟩ := nonempty_pullback_of_point f hne W.unop w
    have hab' : a = b :=
      congrArg (fun c : C(↥((smallEtaleBaseChange f).obj W.unop).left, E) ↦ c x) hab
    subst hab'
    exact Presheaf.equalizerSieve_self_eq_top _

/-- Every continuous `E`-valued map on a base change is locally constant on the small étale site
of `X`, provided it is constant on the base change of every integral object. -/
private theorem constantToPushforwardContinuous_isLocallySurjective [TopologicalSpace E]
    (hne : ∀ W : X.Etale, AlgebraicGeometry.IsIntegral W.left → Nonempty ↥(pullback W.hom f))
    (hconst : ∀ W : X.Etale, AlgebraicGeometry.IsIntegral W.left →
      ∀ (s : C(↥(pullback W.hom f), E)) (x y : ↥(pullback W.hom f)), s x = s y) :
    Presheaf.IsLocallySurjective X.smallEtaleTopology
      (constantToPushforwardContinuous.{u, v} f E) where
  imageSieve_mem {W} s := by
    choose Z g hg hZ hw using exists_isIntegral_open_of_etale (X := X) (Y := W.left) W.hom
    let V : ↥W.left → X.Etale := fun w ↦ Scheme.Etale.mk (g w ≫ W.hom)
    let k : ∀ w, V w ⟶ W := fun w ↦ MorphismProperty.Over.homMk (g w)
    apply X.smallEtaleTopology.superset_covering
      ((Sieve.generate_le_iff _ _).mpr (Presieve.ofArrows_le_iff.mpr ?_))
      ((Scheme.ofArrows_mem_smallEtaleTopology_iff k).mpr ?_)
    · intro w
      obtain ⟨x⟩ := hne (V w) (hZ w)
      let t : C(↥(pullback (V w).hom f), E) :=
        ((smallEtaleDirectImage.{u, v} f).obj (etaleContinuousSheaf.{u, v} Y E)).obj.map
          (k w).op s
      refine ⟨t x, ?_⟩
      exact ContinuousMap.ext fun y ↦ hconst (V w) (hZ w) t x y
    · ext x
      simp only [Set.mem_iUnion, Set.mem_range, Set.mem_univ, iff_true]
      exact ⟨x, hw x⟩

/-- The comparison morphism is an isomorphism when the base change of every integral object of
the small étale site of `X` is nonempty and carries no nonconstant map to a discrete set. -/
private theorem isIso_constantSheafPushforwardComparison_of_forall_isIntegral
    (hne : ∀ W : X.Etale, AlgebraicGeometry.IsIntegral W.left → Nonempty ↥(pullback W.hom f))
    (hconst : ∀ W : X.Etale, AlgebraicGeometry.IsIntegral W.left →
      ∀ (T : Type (max (u + 1) v)) [TopologicalSpace T] [DiscreteTopology T]
        (s : C(↥(pullback W.hom f), T)) (x y : ↥(pullback W.hom f)), s x = s y) :
    IsIso (constantSheafPushforwardComparison.{u, v} f E) := by
  let : TopologicalSpace E := ⊥
  let : DiscreteTopology E := ⟨rfl⟩
  exact isIso_constantSheafPushforwardComparison_of_locallyBijective f E
    (constantToPushforwardContinuous_isLocallyInjective f E hne)
    (constantToPushforwardContinuous_isLocallySurjective f E hne
      (fun W hW ↦ hconst W hW E))

end LocallyBijective

/-! ### The generic point and nonempty opens of an integral normal scheme -/

/-- On an integral normal scheme the direct image of a constant sheaf
of sets along the inclusion of the generic point is the constant sheaf: the canonical comparison
morphism is an isomorphism. -/
@[stacks 09Z5 "part (1)", sga "4 IX 2.14.1" "special case", sga "7 VIII 5.1" "special case"]
theorem isIso_constantSheafPushforwardComparison_genericPointInclusion (X : Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [IsNormal X] (E : Type (max (u + 1) v)) :
    IsIso (constantSheafPushforwardComparison.{u, v} (genericPointInclusion X) E) := by
  refine isIso_constantSheafPushforwardComparison_of_forall_isIntegral _ E ?_ ?_
  · intro W hW
    obtain ⟨w⟩ := (inferInstance : Nonempty ↥W.left)
    obtain ⟨z, -, -⟩ := exists_mem_pullback_genericPointInclusion X W w
    exact ⟨z⟩
  · intro W hW T _ _ s x y
    have := subsingleton_pullback_genericPointInclusion (X := X) (Z := W.left) W.hom
    rw [Subsingleton.elim x y]

/-- The identification `g_* E̲ = E̲` of the direct image of a constant
sheaf of sets along the inclusion `g : Spec K ⟶ X` of the generic point of an integral normal
scheme with the constant sheaf, given by the canonical comparison morphism. -/
@[stacks 09Z5 "part (1)", sga "4 IX 2.14.1" "special case", sga "7 VIII 5.1" "special case"]
def constantSheafGenericPointPushforwardIso (X : Scheme.{u})
    [AlgebraicGeometry.IsIntegral X] [IsNormal X] (E : Type (max (u + 1) v)) :
    (constantSheaf X.smallEtaleTopology (Type (max (u + 1) v))).obj E ≅
      (smallEtaleDirectImage.{u, v} (genericPointInclusion X)).obj
        ((constantSheaf (Spec X.functionField).smallEtaleTopology
          (Type (max (u + 1) v))).obj E) :=
  haveI := isIso_constantSheafPushforwardComparison_genericPointInclusion.{u, v} X E
  asIso (constantSheafPushforwardComparison.{u, v} (genericPointInclusion X) E)

/-- On an integral normal scheme the direct image of a constant sheaf
of sets along the inclusion of a nonempty open subscheme is the constant sheaf: the canonical
comparison morphism is an isomorphism. -/
@[stacks 09Z5 "part (2)"]
theorem isIso_constantSheafPushforwardComparison_opensIota {X : Scheme.{u}}
    [AlgebraicGeometry.IsIntegral X] [IsNormal X] (U : X.Opens) (hU : (U : Set X).Nonempty)
    (E : Type (max (u + 1) v)) :
    IsIso (constantSheafPushforwardComparison.{u, v} U.ι E) := by
  refine isIso_constantSheafPushforwardComparison_of_forall_isIntegral _ E ?_ ?_
  · intro W hW
    exact nonempty_pullback_opensIota (X := X) (Z := W.left) W.hom U hU
  · intro W hW T _ _ s x y
    have := preirreducibleSpace_pullback_opensIota (X := X) (Z := W.left) W.hom U
    exact apply_eq_of_preconnectedSpace s x y

/-- The identification `j_* E̲ = E̲` of the direct image of a constant
sheaf of sets along the inclusion `j : U ⟶ X` of a nonempty open subscheme of an integral normal
scheme with the constant sheaf, given by the canonical comparison morphism. -/
@[stacks 09Z5 "part (2)"]
def constantSheafOpensPushforwardIso {X : Scheme.{u}} [AlgebraicGeometry.IsIntegral X]
    [IsNormal X] (U : X.Opens) (hU : (U : Set X).Nonempty) (E : Type (max (u + 1) v)) :
    (constantSheaf X.smallEtaleTopology (Type (max (u + 1) v))).obj E ≅
      (smallEtaleDirectImage.{u, v} U.ι).obj
        ((constantSheaf U.toScheme.smallEtaleTopology (Type (max (u + 1) v))).obj E) :=
  haveI := isIso_constantSheafPushforwardComparison_opensIota.{u, v} U hU E
  asIso (constantSheafPushforwardComparison.{u, v} U.ι E)

end Stacks.EtaleCohomology

end
