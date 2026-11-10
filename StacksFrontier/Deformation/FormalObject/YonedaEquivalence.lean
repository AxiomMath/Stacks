module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.FormalObject.Associated
public import StacksFrontier.Deformation.FormalObject.RepresentableMorphism

/-!
# The Yoneda equivalence for formal objects (Stacks 06HC)

For a category cofibered in groupoids over Artinian local algebras, morphisms from the
restricted functor represented by a complete local algebra are equivalent to formal objects
over that algebra. Stacks 06SK constructs that equivalence; this file equips the constructed
equivalence with the explicit quasi-inverse the Stacks source names — push a formal object
forward along the complete-algebra points and apply the inverse hom functor of Stacks 06HA —
and compares the resulting composite with the morphism associated to a formal object.

## Main definitions

* `Deformation.iota` sends a formal object to its chosen pushforwards along complete algebra
  points.
* `Deformation.psi` is the inverse hom functor of Stacks 06HA, with the canonical
  identification of the restricted represented category.
* `Deformation.iotaCompPsi` is the explicit quasi-inverse to the equivalence of Stacks 06SK.
* `Deformation.extendRepresentedHom` extends a morphism out of the restricted
  coyoneda category along the identification with the strict restriction.
* `Deformation.yonedaPushforward` is the morphism represented by an object of a strict fibre,
  built from a choice of pushforwards over an arbitrary base category.

## Main results

* `Deformation.formalObjectsYonedaEquivalence`: **Stacks 06HC**, the equivalence of Stacks
  06SK equipped with `Ψ ∘ ι`, together with `formalObjectsYonedaEquivalence_functor` and
  `formalObjectsYonedaEquivalence_inverse` naming its two directions.
* `Deformation.associatedMorphism_maps_to` identifies the image of the associated morphism;
  `Deformation.associatedMorphism_maps_to_canonicalEquivalence` is its instance at the
  constructed equivalence.
* `Deformation.psiIotaIsoAssociatedMorphism` compares this composite with the associated
  morphism.
* `Deformation.iotaIsoCompletionAssociatedMorphism` compares `ι(ξ)` with its completion,
  using Stacks 06HA.

## Implementation notes

Stacks 06SK constructs the forward equivalence, with its quotient-level and transition
formulas and its factorization through `Φ`, from nothing but the cofibered-in-groupoids
hypothesis; `formalObjectsYonedaEquivalence` equips that construction with the specified
inverse `Ψ ∘ ι`. `associatedMorphism_maps_to` identifies the formal object recovered from
the associated morphism; it is stated for an arbitrary presenting datum, and the assertion of
the tag is its instance at the constructed datum.
`psiIotaIsoAssociatedMorphism` and `iotaIsoCompletionAssociatedMorphism` give the two
chosen-pushforward comparisons. All comparisons are in categories of based functors or
strict fibres; the chosen pushforwards determine both the object and morphism formulas
of `ι`.

## References

* [Stacks Project, Tag 06HC](https://stacks.math.columbia.edu/tag/06HC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor

namespace Deformation

-- The proofs below identify morphisms of based categories across the chain
-- `BasedCategory.ofFunctor`/`Functor.Elements` that presents a restricted representable
-- category, and across `BasedFunctor.comp`.  Those definitions are made reducible here so
-- that `simp`, `rw` and instance search can traverse the chain.
attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor
  CategoryTheory.BasedFunctor.comp

universe u v w uF vF
universe u₁ v₁ u₂ v₂

section Pushforwards

section AnyBase

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
variable (q : D ⥤ C)
variable (P : ∀ ⦃A B : C⦄ (f : A ⟶ B), PushforwardChoice q f)
variable {R : C}
variable {x y z : q.Fiber R}
variable {α β γ : (coyoneda.obj (Opposite.op R)).Elements}

/-- The arrow between chosen pushforwards induced by a fibre arrow and an arrow of points. -/
public noncomputable def pushforwardMap (t : x ⟶ y) (g : α ⟶ β) :
    ((P α.2).obj x).1 ⟶ ((P β.2).obj y).1 := by
  have := (P α.2).cocartesian x
  have := (P β.2).cocartesian y
  have := t.2
  exact Functor.IsStronglyCocartesian.map q α.2 ((P α.2).inclusion x)
    g.map_val.symm (t.1 ≫ (P β.2).inclusion y)

/-- The induced arrow lies over the given arrow between points. -/
public lemma pushforwardMap_lift (t : x ⟶ y) (g : α ⟶ β) :
    q.IsHomLift g.hom (pushforwardMap q P t g) := by
  unfold pushforwardMap
  infer_instance

/-- The triangle characterizing the induced arrow between chosen pushforwards. -/
public lemma pushforwardMap_fac (t : x ⟶ y) (g : α ⟶ β) :
    (P α.2).inclusion x ≫ pushforwardMap q P t g =
      t.1 ≫ (P β.2).inclusion y := by
  unfold pushforwardMap
  have := (P α.2).cocartesian x
  have := (P β.2).cocartesian y
  have := t.2
  apply Functor.IsStronglyCocartesian.fac

/-- Identity arrows induce the identity on a chosen pushforward. -/
public lemma pushforwardMap_id (x : q.Fiber R)
    (α : (coyoneda.obj (Opposite.op R)).Elements) :
    pushforwardMap q P (𝟙 x) (𝟙 α) = 𝟙 _ := by
  have := (P α.2).cocartesian x
  have := pushforwardMap_lift q P (𝟙 x) (𝟙 α)
  have := IsHomLift.id ((P α.2).obj x).2
  apply Functor.IsStronglyCocartesian.ext q α.2 ((P α.2).inclusion x) (𝟙 α.1)
  rw [pushforwardMap_fac, Category.comp_id]
  exact Category.id_comp _

/-- Induced arrows respect simultaneous composition in the fibre and between points. -/
public lemma pushforwardMap_comp (t : x ⟶ y) (s : y ⟶ z)
    (g : α ⟶ β) (h : β ⟶ γ) :
    pushforwardMap q P (t ≫ s) (g ≫ h) =
      pushforwardMap q P t g ≫ pushforwardMap q P s h := by
  have := (P α.2).cocartesian x
  have := pushforwardMap_lift q P (t ≫ s) (g ≫ h)
  have := pushforwardMap_lift q P t g
  have := pushforwardMap_lift q P s h
  apply Functor.IsStronglyCocartesian.ext q α.2 ((P α.2).inclusion x) (g.hom ≫ h.hom)
  rw [pushforwardMap_fac, ← Category.assoc, pushforwardMap_fac,
    Category.assoc, pushforwardMap_fac]
  exact Category.assoc _ _ _

/-- The represented morphism sending `f : R ⟶ S` to the chosen pushforward `f_* x`.
Its arrows are uniquely induced by the chosen cocartesian arrows. -/
public noncomputable def yonedaPushforward (x : q.Fiber R) :
    BasedFunctor
      (BasedCategory.ofFunctor (Functor.Elements.π (coyoneda.obj (Opposite.op R))))
      (BasedCategory.ofFunctor q) := by
  let H : (coyoneda.obj (Opposite.op R)).Elements ⥤ D :=
    { obj := fun α ↦ ((P α.2).obj x).1
      map := fun g ↦ pushforwardMap q P (𝟙 x) g
      map_id := fun α ↦ pushforwardMap_id q P x α
      map_comp := fun g h ↦ by
        simpa only [Category.id_comp] using pushforwardMap_comp q P (𝟙 x) (𝟙 x) g h }
  refine ⟨H, CategoryTheory.Functor.ext (fun α ↦ ((P α.2).obj x).2) fun α β g => ?_⟩
  have := pushforwardMap_lift q P (𝟙 x) g
  exact IsHomLift.fac' q g.hom _

end AnyBase

-- `yonedaPushforward` is built by a tactic block, so its value on objects is only reachable
-- by unfolding it; the functoriality proofs below compare morphisms at that object.
attribute [local implicit_reducible] yonedaPushforward

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable (q : F ⥤ CompleteLocalAlgCat.{u, v, w} Λ k)

/-- A choice of pushforwards over complete local algebras; in particular this applies
to the completion of a cofibered category. -/
public abbrev ChosenCompletePushforwards :=
  ∀ ⦃R S : CompleteLocalAlgCat.{u, v, w} Λ k⦄ (f : R ⟶ S),
    PushforwardChoice q f

variable (P : ChosenCompletePushforwards q)

/-- The pushforward construction is functorial in the object of the strict fibre. -/
public noncomputable def yonedaPushforwardFunctor (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    q.Fiber R ⥤
      BasedFunctor (BasedCategory.ofFunctor (representedProjection R))
        (BasedCategory.ofFunctor q) where
  obj := yonedaPushforward q P
  map t :=
    { app := fun α ↦ pushforwardMap q P t (𝟙 α)
      naturality := fun {α β} g ↦ by
        change pushforwardMap q P (𝟙 _) g ≫ pushforwardMap q P t (𝟙 β) =
          pushforwardMap q P t (𝟙 α) ≫ pushforwardMap q P (𝟙 _) g
        rw [← pushforwardMap_comp, ← pushforwardMap_comp]
        simp
      isHomLift' := fun α ↦ pushforwardMap_lift q P t (𝟙 α) }
  map_id x := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext α
    exact pushforwardMap_id q P x α
  map_comp t s := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext α
    simpa using pushforwardMap_comp q P t s (𝟙 α) (𝟙 α)

/-- Evaluation of the pushforward morphism at the identity recovers the original
object, naturally and over the identity of its base. -/
public noncomputable def yonedaPushforwardEvaluationIso
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    𝟭 (q.Fiber R) ≅ yonedaPushforwardFunctor q P R ⋙ Deformation.evaluation q R := by
  let e (x : q.Fiber R) : x ≅ (P (𝟙 R)).obj x := by
    have := (P (𝟙 R)).cocartesian x
    have := Functor.IsStronglyCocartesian.isIso_of_base_isIso q (𝟙 R)
      ((P (𝟙 R)).inclusion x)
    exact
      { hom := ⟨(P (𝟙 R)).inclusion x, inferInstance⟩
        inv := ⟨inv ((P (𝟙 R)).inclusion x),
          IsHomLift.lift_id_inv_isIso q R _⟩
        hom_inv_id := Subtype.ext (IsIso.hom_inv_id _)
        inv_hom_id := Subtype.ext (IsIso.inv_hom_id _) }
  refine NatIso.ofComponents e fun t => ?_
  apply Subtype.ext
  exact (pushforwardMap_fac q P t (𝟙 (Functor.elementsMk _ R (𝟙 R)))).symm

end Pushforwards

section Restriction

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Projecting and reincluding a strict restriction recovers its points and arrows. -/
public theorem restrictedRepresentableProjection_comp_inclusion
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (representedRestrictionInverseBased R).comp (restrictedRepresentableInclusion R) =
      BasedFunctor.id _ := by
  have hobj (X : Restriction (representedProjection R)) :
      ((representedRestrictionInverseBased R).comp
        (restrictedRepresentableInclusion R)).obj X = X := by
    rcases X with ⟨@⟨S, f⟩, A, h⟩
    change S = artinianToComplete.obj A at h
    subst S
    change (Restriction.mk (p := representedProjection R) ⟨f ≫ 𝟙 _⟩ A rfl) = _
    rw [Category.comp_id]
  have hfun : ((representedRestrictionInverseBased R).comp
      (restrictedRepresentableInclusion R)).toFunctor = 𝟭 _ := by
    refine CategoryTheory.Functor.ext hobj ?_
    intro X Y g
    rcases X with ⟨@⟨S, f⟩, A, h⟩
    rcases Y with ⟨@⟨T, f'⟩, B, h'⟩
    change S = artinianToComplete.obj A at h
    change T = artinianToComplete.obj B at h'
    subst S T
    simp only [Functor.id_obj, Functor.id_map]
    apply Restriction.Hom.ext
    · apply Functor.Elements.hom_ext
      change artinianToComplete.map g.base = g.obj.hom
      have hc := g.comm
      change 𝟙 _ ≫ artinianToComplete.map g.base = g.obj.hom ≫ 𝟙 _ at hc
      simpa only [Category.id_comp, Category.comp_id] using hc
    · rfl
  have ext : ∀ (a b : BasedFunctor
      (BasedCategory.ofFunctor (Restriction.projection (p := representedProjection R)))
      (BasedCategory.ofFunctor (Restriction.projection (p := representedProjection R)))),
      a.toFunctor = b.toFunctor → a = b := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    cases h
    rfl
  exact ext _ _ hfun

/-- Restriction and extension along the identification cancel, naturally on hom categories. -/
public def extendRestrictRepresentedHomIso {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    restrictRepresentedHom p R ⋙ extendRepresentedHom p R ≅ 𝟭 _ := by
  let pre (a : BasedFunctor
      (BasedCategory.ofFunctor (Restriction.projection (p := representedProjection R)))
      (BasedCategory.ofFunctor (Restriction.projection (p := representedProjection R)))) :
      BasedFunctor (BasedCategory.ofFunctor
          (Restriction.projection (p := representedProjection R)))
        (BasedCategory.ofFunctor p) ⥤
      BasedFunctor (BasedCategory.ofFunctor
          (Restriction.projection (p := representedProjection R)))
        (BasedCategory.ofFunctor p) :=
    { obj := fun φ ↦ a.comp φ
      map := fun t ↦ BasedCategory.whiskerLeft a t
      map_id := fun _ ↦ rfl
      map_comp := fun _ _ ↦ rfl }
  change pre ((representedRestrictionInverseBased R).comp (restrictedRepresentableInclusion R)) ≅
    pre (BasedFunctor.id _)
  exact eqToIso (congrArg pre (restrictedRepresentableProjection_comp_inclusion R))

end Restriction

section Comparison

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
variable {F : Type uF} [Category.{vF} F]
variable {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- The explicit `ι` of Tag 06HC, formed from chosen pushforwards of the completion. -/
public noncomputable def iota (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (P : ChosenCompletePushforwards (FormalObject.projection (p := p))) :=
  yonedaPushforwardFunctor (FormalObject.projection (p := p)) P R

/-- The defining formula `ι(ξ)(f) = f_* ξ` uses exactly the chosen pushforward. -/
@[simp]
public theorem iota_obj (R S : CompleteLocalAlgCat.{u, v, w} Λ k)
    (P : ChosenCompletePushforwards (FormalObject.projection (p := p)))
    (ξ : (FormalObject.projection (p := p)).Fiber R) (f : R ⟶ S) :
    ((iota R P).obj ξ).obj ⟨f⟩ = ((P f).obj ξ).1 := rfl

/-- `Ψ` from Tag 06HA, using the canonical identification of the two presentations
of the restriction of the represented cofibered set. -/
public noncomputable def psi (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :=
  (completionHomEquivalence p
    (representedProjection R) hp
    (representedProjection_cofibered R)).equiv.inverse ⋙
      restrictRepresentedHom p R

/-- `Φ` from Tag 06HA after identifying the restricted represented categories. -/
public noncomputable def phi (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :=
  extendRepresentedHom p R ⋙
    (completionHomEquivalence p
      (representedProjection R) hp
      (representedProjection_cofibered R)).equiv.functor

/-- `Φ` is the unit followed by completion, exactly as specified in Tag 06HA. -/
public theorem phi_obj (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (φ : BasedFunctor
      (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p)) :
    (phi hp R).obj φ =
      (unitBasedFunctor (representedProjection R)
        (representedProjection_cofibered R)).comp
          (completionMap ((extendRepresentedHom p R).obj φ)) :=
  (completionHomEquivalence p
    (representedProjection R) hp
    (representedProjection_cofibered R)).forward _

/-- The counit of the hom equivalence, after identifying the restricted represented set. -/
public noncomputable def psiCompPhiIso (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    psi hp R ⋙ phi hp R ≅ 𝟭 _ :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft _ ((Functor.associator _ _ _).symm ≪≫
      isoWhiskerRight (extendRestrictRepresentedHomIso p R) _ ≪≫ Functor.leftUnitor _) ≪≫
    (completionHomEquivalence p
      (representedProjection R) hp
      (representedProjection_cofibered R)).equiv.counitIso

/-- The specified quasi-inverse is the composite `Ψ ∘ ι`. -/
public noncomputable def iotaCompPsi (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (P : ChosenCompletePushforwards (FormalObject.projection (p := p))) :=
  iota R P ⋙ psi hp R

/-- Applying the 06SK equivalence to `Ψ ∘ ι` recovers the original formal object,
naturally in its strict fibre. -/
public noncomputable def iotaCompPsiCounitIso
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (E : RepresentableMorphismFormalObjectEquivalence p R)
    (P : ChosenCompletePushforwards (FormalObject.projection (p := p))) :
    iotaCompPsi hp R P ⋙ E.equivalence.functor ≅ 𝟭 _ :=
  Functor.associator _ _ _ ≪≫
    isoWhiskerLeft (iota R P)
      ((Functor.associator _ _ _) ≪≫
        E.completionComparison hp (representedProjection_cofibered R)) ≪≫
    (yonedaPushforwardEvaluationIso (FormalObject.projection (p := p)) P R).symm

/-- The explicit composite is naturally isomorphic to the inverse of the adopted
06SK equivalence. -/
public noncomputable def iotaCompPsiIsoInverse
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (E : RepresentableMorphismFormalObjectEquivalence p R)
    (P : ChosenCompletePushforwards (FormalObject.projection (p := p))) :
    iotaCompPsi hp R P ≅ E.equivalence.inverse :=
  (Functor.rightUnitor _).symm ≪≫
    isoWhiskerLeft _ E.equivalence.unitIso ≪≫
    (Functor.associator _ _ _).symm ≪≫
    isoWhiskerRight (iotaCompPsiCounitIso hp R E P) _ ≪≫
    Functor.leftUnitor _

/-- Morphisms over the Artinian base from the restriction of the functor represented by `R`
to a category cofibered in groupoids form a category equivalent to the category of formal
objects over `R`, with the quasi-inverse `Ψ ∘ ι`. The forward direction is the equivalence
constructed in Tag 06SK by `representableMorphismFormalObjectEquivalence`, so it carries that
construction's explicit description at the Artinian quotient points of `R` and its
factorization through `Φ` followed by 2-Yoneda evaluation. -/
@[stacks 06HC "formal_objects_yoneda_equivalence"]
public noncomputable def formalObjectsYonedaEquivalence
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (P : ChosenCompletePushforwards (FormalObject.projection (p := p))) :
    BasedFunctor
        (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))
        (BasedCategory.ofFunctor p) ≌
      (FormalObject.projection (p := p)).Fiber R :=
  (representableMorphismFormalObjectEquivalence p hp R).equivalence.changeInverse
    (iotaCompPsiIsoInverse hp R (representableMorphismFormalObjectEquivalence p hp R) P).symm

/-- The forward direction of the Yoneda equivalence is the equivalence constructed in Tag
06SK. Its `levelIso` and `transition_comm` give the explicit description sending `φ` to the
formal object `(R, φ(R → R/𝔪_R^n), φ(f_n))`, and its `completionComparison` exhibits it as
`Φ` followed by 2-Yoneda evaluation. -/
@[stacks 06HC "formal_objects_yoneda_equivalence"]
public theorem formalObjectsYonedaEquivalence_functor
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (P : ChosenCompletePushforwards (FormalObject.projection (p := p))) :
    (formalObjectsYonedaEquivalence hp R P).functor =
      (representableMorphismFormalObjectEquivalence p hp R).equivalence.functor := rfl

/-- The quasi-inverse of the Yoneda equivalence is the composite `Ψ ∘ ι` specified in the
source. -/
@[stacks 06HC "formal_objects_yoneda_equivalence"]
public theorem formalObjectsYonedaEquivalence_inverse
    (hp : IsCofiberedInGroupoids p)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (P : ChosenCompletePushforwards (FormalObject.projection (p := p))) :
    (formalObjectsYonedaEquivalence hp R P).inverse = iotaCompPsi hp R P := rfl

end Comparison

add_to_stacks 06HC "formal_objects_yoneda_equivalence"
  representableMorphismFormalObjectEquivalence

open IsLocalRing

/-- An arrow `f` lifting the identity `𝟙 S` along `p`, whose domain and codomain have images
`R` and `S`, also lifts `eqToHom h : R ⟶ S` for every identification `h : R = S`. -/
public lemma lift_eqToHom_of_lift_id
    {C D : Type*} [Category C] [Category D] (p : D ⥤ C)
    {R S : C} (h : R = S) {a b : D} (f : a ⟶ b)
    (ha : p.obj a = R) (hb : p.obj b = S)
    (hf : p.IsHomLift (𝟙 S) f) : p.IsHomLift (eqToHom h) f := by
  apply IsHomLift.of_fac' p (eqToHom h) f ha hb
  have hfac := IsHomLift.fac' p (𝟙 S) f
  have hd : IsHomLift.domain_eq p (𝟙 S) f = ha.trans h := Subsingleton.elim _ _
  have hc : IsHomLift.codomain_eq p (𝟙 S) f = hb := Subsingleton.elim _ _
  rw [hd, hc] at hfac
  simpa only [eqToHom_trans, Category.id_comp] using hfac

/-- A commuting square of arrows whose horizontal sides are isomorphisms stays commutative
after inverting those sides. -/
private lemma comp_inv_eq_inv_comp_of_comp_eq
    {C : Type*} [Category C] {A B A' B' : C} (i : A ≅ B) (j : A' ≅ B')
    (u : A ⟶ A') (v : B ⟶ B') (h : u ≫ j.hom = i.hom ≫ v) :
    v ≫ j.inv = i.inv ≫ u := by
  rw [Iso.comp_inv_eq, Category.assoc, h, Iso.inv_hom_id_assoc]

private lemma quotientTruncation_nilpotent
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) (n : ℕ) :
    IsLocalRing.maximalIdeal (AdicTruncation.obj R n) ^ (n + 1) = ⊥ := by
  classical
  let I : Ideal R := maximalIdeal R ^ (n + 1)
  have hI : I < ⊤ := (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans_lt
    (IsLocalRing.maximalIdeal.isMaximal R).lt_top
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI.ne
  let : IsLocalRing (R ⧸ I) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  let : IsLocalHom (Ideal.Quotient.mk I) :=
    IsLocalHom.of_surjective (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  change IsLocalRing.maximalIdeal (R ⧸ I) ^ (n + 1) = ⊥
  have hm : (IsLocalRing.maximalIdeal R).map (Ideal.Quotient.mk I) =
      IsLocalRing.maximalIdeal (R ⧸ I) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simp [I, sup_eq_left.mpr (le_maximalIdeal hI.ne)]
  rw [← hm, ← Ideal.map_pow]
  simp [I]

/-- The represented morphism associated to a formal object evaluates back to that formal
object, up to an isomorphism over its complete local base.

This is the generic form, stated for an arbitrary datum `E` presenting the equivalence of
Tag 06SK; the assertion of Tag 06HC is its instance at the constructed datum, recorded in
`associatedMorphism_maps_to_canonicalEquivalence`. -/
public theorem associatedMorphism_maps_to
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p)
    (E : RepresentableMorphismFormalObjectEquivalence p ξ.base)
    (pushforwards : ChosenPushforwards p) :
    Nonempty
      (E.equivalence.functor.obj
        (associatedMorphism hp ξ pushforwards).toBasedFunctor ≅
          (Functor.Fiber.mk rfl : (FormalObject.projection (p := p)).Fiber ξ.base)) := by
  classical
  let a := associatedMorphism hp ξ pushforwards
  let xFiber := E.equivalence.functor.obj a.toBasedFunctor
  let x : FormalObject p := xFiber.1
  have hx : x.base = ξ.base := by
    simpa [x, xFiber, FormalObject.projection_obj] using xFiber.2
  let qpt (n : ℕ) : (restrictedCoyoneda ξ.base).Elements :=
    Functor.elementsMk _ (AdicTruncation.obj ξ.base n) (E.quotientPoint n)
  let qobj (n : ℕ) :
      (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda ξ.base))).obj := qpt n
  let assocObj (n : ℕ) : F := a.toBasedFunctor.obj (qobj n)
  let edge (n : ℕ) : qobj (n + 1) ⟶ qobj n :=
    Functor.Elements.homMk (x := qpt (n + 1)) (y := qpt n)
      (AdicTruncation.transition ξ.base n) (E.projectionPoint n)
  let assocMap (n : ℕ) : assocObj (n + 1) ⟶ assocObj n :=
    a.toBasedFunctor.map (edge n)
  have hm (n : ℕ) : a.level (qpt n) ≤ n :=
    (a.factor_spec (qpt n)).2.1 n (quotientTruncation_nilpotent ξ.base n)
  let w (n : ℕ) : ξ.level n ⟶ assocObj n :=
    transitionTo ξ (hm n) ≫ a.pointInclusion (qpt n)
  have hw_lift (n : ℕ) :
      p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n)) (w n) := by
    let α := qpt n
    let m := a.level α
    let z₀ := (pushforwards (a.factor α)).obj ⟨ξ.level m, ξ.level_eq m⟩
    let z : F := z₀.1
    have hin : p.IsHomLift (a.factor α)
        ((pushforwards (a.factor α)).inclusion ⟨ξ.level m, ξ.level_eq m⟩) :=
      (pushforwards (a.factor α)).cocartesian ⟨ξ.level m, ξ.level_eq m⟩ |>.toIsHomLift
    have hei : p.IsHomLift (𝟙 α.1) (eqToHom (a.obj_eq α).symm) :=
      IsHomLift.eqToHom_domain_lift_id (a.obj_eq α).symm z₀.2
    have hpin : p.IsHomLift (a.factor α) (a.pointInclusion α) := by
      rw [(comp_eqToHom_iff (a.obj_eq α) (a.pointInclusion α)
        ((pushforwards (a.factor α)).inclusion ⟨ξ.level m, ξ.level_eq m⟩)).mp
          (a.pointInclusion_eq α)]
      simpa only [Category.comp_id] using IsHomLift.comp p (a.factor α) (𝟙 α.1)
        ((pushforwards (a.factor α)).inclusion ⟨ξ.level m, ξ.level_eq m⟩)
        (eqToHom (a.obj_eq α).symm)
    obtain ⟨b, hb, hbl⟩ := point_lift ξ (a.factor_spec (qpt n)).2.2
      (a.pointInclusion α) hpin (hm n)
    have hb' : b = 𝟙 (AdicTruncation.obj ξ.base n) := by
      refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun r ↦ ?_)
      obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective r
      have hquot := DFunLike.congr_fun hb r
      rw [E.quotientPoint_hom] at hquot
      exact hquot
    rwa [hb'] at hbl
  have hw_iso (n : ℕ) : IsIso (w n) := by
    let : p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n)) (w n) := hw_lift n
    have : p.IsStronglyCocartesian (𝟙 (AdicTruncation.obj ξ.base n)) (w n) :=
      isStronglyCocartesian_of_isCofiberedInGroupoids hp
        (𝟙 (AdicTruncation.obj ξ.base n)) (w n) inferInstance
    exact Functor.IsStronglyCocartesian.isIso_of_base_isIso p
      (𝟙 (AdicTruncation.obj ξ.base n)) (w n)
  let W (n : ℕ) : ξ.level n ≅ assocObj n := asIso (w n)
  let L (n : ℕ) := E.levelIso a.toBasedFunctor n
  let J (n : ℕ) : x.level n ≅ ξ.level n := (L n).symm ≪≫ (W n).symm
  have hJlift (n : ℕ) :
      p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n)) ((J n).hom) := by
    have hL : p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n)) ((L n).symm.hom) := by
      let : p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n)) ((L n).hom) :=
        E.levelIso_over a.toBasedFunctor n
      exact IsHomLift.lift_id_inv p _ (L n)
    have hW : p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n)) ((W n).symm.hom) := by
      let : p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n)) ((W n).hom) := hw_lift n
      exact IsHomLift.lift_id_inv p _ (W n)
    dsimp [J]
    change p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n))
      ((L n).symm.hom ≫ (W n).symm.hom)
    exact IsHomLift.comp p (𝟙 (AdicTruncation.obj ξ.base n))
      (𝟙 (AdicTruncation.obj ξ.base n)) ((L n).symm.hom) ((W n).symm.hom)
  have htransition : ∀ n,
      w (n + 1) ≫ assocMap n = ξ.transition n ≫ w n := by
    intro n
    let m := max (a.level (qpt (n + 1))) (a.level (qpt n))
    have hm₁ : a.level (qpt (n + 1)) ≤ m := Nat.le_max_left _ _
    have hm₀ : a.level (qpt n) ≤ m := Nat.le_max_right _ _
    have hmn : m ≤ n + 1 := max_le (hm (n + 1)) ((hm n).trans (Nat.le_succ n))
    have hmap :
        transitionTo ξ (Nat.le_max_left _ _) ≫ a.pointInclusion (qpt (n + 1)) ≫
            assocMap n =
          transitionTo ξ (Nat.le_max_right _ _) ≫ a.pointInclusion (qpt n) := by
      simpa [assocMap, edge, qobj] using a.map_pointInclusion (edge n)
    have hleft : transitionTo ξ hmn ≫ transitionTo ξ hm₁ =
        transitionTo ξ (hm₁.trans hmn) := transitionTo_comp ξ hm₁ hmn
    have hright : transitionTo ξ hmn ≫ transitionTo ξ hm₀ =
        transitionTo ξ (hm₀.trans hmn) := transitionTo_comp ξ hm₀ hmn
    have hmap' :
        transitionTo ξ (hm₁.trans hmn) ≫ a.pointInclusion (qpt (n + 1)) ≫
            assocMap n =
          transitionTo ξ (hm₀.trans hmn) ≫ a.pointInclusion (qpt n) := by
      rw [← hleft, ← hright]
      simpa only [Category.assoc] using congrArg (fun t => transitionTo ξ hmn ≫ t) hmap
    have hleft' : hm₁.trans hmn = hm (n + 1) := Subsingleton.elim _ _
    have hright' : hm₀.trans hmn = (hm n).trans (Nat.le_succ n) := Subsingleton.elim _ _
    rw [hleft', hright', transitionTo_succ ξ (hm n)] at hmap'
    have hmap'' : transitionTo ξ (hm (n + 1)) ≫
          (a.pointInclusion (qpt (n + 1)) ≫ assocMap n) =
        (ξ.transition n ≫ transitionTo ξ (hm n)) ≫ a.pointInclusion (qpt n) := hmap'
    simpa only [w, Category.assoc] using hmap''
  have hJ (n : ℕ) :
      x.transition n ≫ (J n).hom = (J (n + 1)).hom ≫ ξ.transition n := by
    have hL : assocMap n ≫ (L n).hom =
        (L (n + 1)).hom ≫ x.transition n := by
      have hh := E.transition_comm a.toBasedFunctor n
      change assocMap n ≫ (L n).hom =
        (L (n + 1)).hom ≫ (E.equivalence.functor.obj a.toBasedFunctor).1.transition n
        at hh
      simpa [x, xFiber, FormalObject.projection_obj] using hh
    have hW := htransition n
    have hL' : x.transition n ≫ (L n).symm.hom =
        (L (n + 1)).symm.hom ≫ assocMap n :=
      comp_inv_eq_inv_comp_of_comp_eq (L (n + 1)) (L n) _ _ hL
    have hW' : assocMap n ≫ (W n).symm.hom =
        (W (n + 1)).symm.hom ≫ ξ.transition n :=
      comp_inv_eq_inv_comp_of_comp_eq (W (n + 1)) (W n) _ _ (by simpa [w, W] using hW.symm)
    calc
      x.transition n ≫ (J n).hom =
          (L (n + 1)).symm.hom ≫ assocMap n ≫ (W n).symm.hom := by
            change x.transition n ≫
              ((L n).symm.hom ≫ (W n).symm.hom) = _
            rw [← Category.assoc, hL', Category.assoc]
      _ = (L (n + 1)).symm.hom ≫ (W (n + 1)).symm.hom ≫ ξ.transition n := by rw [hW']
      _ = (J (n + 1)).hom ≫ ξ.transition n := by simp [J, Category.assoc]
  let f : x ⟶ ξ :=
    { base := eqToHom hx
      app := fun n => (J n).hom
      app_lift := by
        intro n
        simpa only [eqToHom_map] using lift_eqToHom_of_lift_id p
          (congrArg (fun R => AdicTruncation.obj R n) hx) ((J n).hom)
          (x.level_eq n) (ξ.level_eq n) (hJlift n)
      naturality := hJ }
  let g : ξ ⟶ x :=
    { base := eqToHom hx.symm
      app := fun n => (J n).symm.hom
      app_lift := by
        intro n
        have hJi : p.IsHomLift (𝟙 (AdicTruncation.obj x.base n)) ((J n).symm.hom) := by
          let : p.IsHomLift (𝟙 (AdicTruncation.obj ξ.base n)) ((J n).hom) := hJlift n
          have hq : AdicTruncation.obj x.base n = AdicTruncation.obj ξ.base n :=
            congrArg (fun R => AdicTruncation.obj R n) hx
          rw [hq]
          exact IsHomLift.lift_id_inv p _ (J n)
        simpa only [eqToHom_map] using lift_eqToHom_of_lift_id p
          (congrArg (fun R => AdicTruncation.obj R n) hx.symm) ((J n).symm.hom)
          (ξ.level_eq n) (x.level_eq n) hJi
      naturality := fun n ↦ comp_inv_eq_inv_comp_of_comp_eq (J (n + 1)) (J n) _ _ (hJ n) }
  have hfg : f ≫ g = 𝟙 x := by
    apply FormalObject.Hom.ext
    · change eqToHom hx ≫ eqToHom hx.symm = 𝟙 x.base
      simp
    · intro n
      change (J n).hom ≫ (J n).symm.hom = 𝟙 _
      simp
  have hgf : g ≫ f = 𝟙 ξ := by
    apply FormalObject.Hom.ext
    · change eqToHom hx.symm ≫ eqToHom hx = 𝟙 ξ.base
      simp
    · intro n
      change (J n).symm.hom ≫ (J n).hom = 𝟙 _
      simp
  have hf : (FormalObject.projection (p := p)).IsHomLift (𝟙 ξ.base) f := by
    apply IsHomLift.of_fac' (FormalObject.projection (p := p)) (𝟙 ξ.base) f xFiber.2 rfl
    simp [FormalObject.projection_map, f]
  have hg : (FormalObject.projection (p := p)).IsHomLift (𝟙 ξ.base) g := by
    apply IsHomLift.of_fac' (FormalObject.projection (p := p)) (𝟙 ξ.base) g rfl xFiber.2
    simp [FormalObject.projection_map, g]
  exact ⟨{
    hom := ⟨f, hf⟩
    inv := ⟨g, hg⟩
    hom_inv_id := Functor.Fiber.hom_ext hfg
    inv_hom_id := Functor.Fiber.hom_ext hgf }⟩

/-- The explicit morphism `ξ̲` associated to a formal object `ξ` maps to `ξ` under the Yoneda
equivalence: evaluating the equivalence constructed in Tag 06SK on
`associatedMorphism hp ξ pushforwards` returns `ξ`, up to an isomorphism over its complete
local base. -/
@[stacks 06HC "formal_objects_yoneda_equivalence"]
public theorem associatedMorphism_maps_to_canonicalEquivalence
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p)
    (pushforwards : ChosenPushforwards p) :
    Nonempty
      ((representableMorphismFormalObjectEquivalence p hp ξ.base).equivalence.functor.obj
        (associatedMorphism hp ξ pushforwards).toBasedFunctor ≅
          (Functor.Fiber.mk rfl : (FormalObject.projection (p := p)).Fiber ξ.base)) :=
  associatedMorphism_maps_to hp ξ
    (representableMorphismFormalObjectEquivalence p hp ξ.base) pushforwards

/-- On a formal object, the quasi-inverse of the equivalence is isomorphic to its
associated represented morphism. In particular this specifies the quasi-inverse at objects
by pushforward along Artinian points. -/
public noncomputable def inverseObjIsoAssociatedMorphism
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p)
    (E : RepresentableMorphismFormalObjectEquivalence p ξ.base)
    (pushforwards : ChosenPushforwards p) :
    E.equivalence.inverse.obj
        (Functor.Fiber.mk rfl : (FormalObject.projection (p := p)).Fiber ξ.base) ≅
      (associatedMorphism hp ξ pushforwards).toBasedFunctor := by
  let e := Classical.choice (associatedMorphism_maps_to hp ξ E pushforwards)
  exact E.equivalence.inverse.mapIso e.symm ≪≫
    (E.equivalence.unitIso.app _).symm

/-- The explicit `Ψ(ι(ξ))` is isomorphic, over the Artinian base, to the morphism `ξ̲`
associated to `ξ` using any chosen pushforwards in the original category. -/
@[stacks 06HC "formal_objects_yoneda_equivalence"]
public noncomputable def psiIotaIsoAssociatedMorphism
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p)
    (pushforwards : ChosenPushforwards p)
    (P : ChosenCompletePushforwards (FormalObject.projection (p := p))) :
    (psi hp ξ.base).obj ((iota ξ.base P).obj
        (Functor.Fiber.mk rfl : (FormalObject.projection (p := p)).Fiber ξ.base)) ≅
      (associatedMorphism hp ξ pushforwards).toBasedFunctor :=
  (iotaCompPsiIsoInverse hp ξ.base
      (representableMorphismFormalObjectEquivalence p hp ξ.base) P).app _ ≪≫
    inverseObjIsoAssociatedMorphism hp ξ
      (representableMorphismFormalObjectEquivalence p hp ξ.base) pushforwards

/-- Under the canonical represented-completion identification, `ι(ξ)` is the completion of the
associated morphism `ξ̲`: `Φ` is the unit followed by levelwise completion, as in 06HA. -/
@[stacks 06HC "formal_objects_yoneda_equivalence"]
public noncomputable def iotaIsoCompletionAssociatedMorphism
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p)
    (pushforwards : ChosenPushforwards p)
    (P : ChosenCompletePushforwards (FormalObject.projection (p := p))) :
    (iota ξ.base P).obj
        (Functor.Fiber.mk rfl : (FormalObject.projection (p := p)).Fiber ξ.base) ≅
      (unitBasedFunctor (representedProjection ξ.base)
        (representedProjection_cofibered ξ.base)).comp
          (completionMap
            ((extendRepresentedHom p ξ.base).obj
              (associatedMorphism hp ξ pushforwards).toBasedFunctor)) :=
  ((psiCompPhiIso hp ξ.base).app _).symm ≪≫
    (phi hp ξ.base).mapIso (psiIotaIsoAssociatedMorphism hp ξ pushforwards P) ≪≫
    eqToIso (phi_obj hp ξ.base _)

end Deformation

end
