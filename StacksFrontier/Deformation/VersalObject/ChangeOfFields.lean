module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Completed.SmoothModel
public import StacksFrontier.Deformation.FormalObject.VersalLifting
public import StacksFrontier.Deformation.ResidueField.Comparison
public import StacksFrontier.RingTheory.FormallySmooth.Adic
public import StacksFrontier.RingTheory.FormallySmooth.AdicArrowIso
public import StacksFrontier.RingTheory.FormallySmooth.AdicLifting

/-!
# Versal formal objects after a change of residue field

Let `Λ → k → l` be the standing finite tower of a Noetherian base ring and two residue fields,
let `𝓕` be a category cofibered in groupoids over `𝒞_{Λ,k}`, and let `ξ` be a versal formal
object of `𝓕` lying over `R` in `𝒞^_{Λ,k}`. This file produces a Noetherian complete local
`Λ`-algebra `S` with residue field `l`, a local `Λ`-algebra map `R → S` which is formally
smooth for the `𝔪_S`-adic topology and which induces the given extension `l/k` on residue
fields, together with a versal formal object of the change-of-residue-field category
`𝓕_{l/k}` lying over `S`.

The algebra `S` is a complete local lift of the smooth complete local `k`-algebra with
residue field `l`: the latter is formally smooth for its maximal-ideal-adic topology, so it is
the special fibre of a complete local `R`-algebra that is adically formally smooth over `R`.
Its residue field is the residue field of that special fibre, hence `l`, and the induced map
on residue fields is the given one.

Versality of the new formal object is smoothness of the morphism out of the restriction of the
functor represented by `S`. That morphism factors as the morphism to the change of residue
field of the functor represented by `R`, followed by the change of residue field of the
morphism associated to `ξ`. The second factor is smooth because the change of residue field
preserves smoothness, and the first is smooth because `R → S` is formally smooth in the
`𝔪_S`-adic topology: a lifting problem over a surjection `B' → B` of Artinian algebras with
residue field `l` is exactly a lifting problem for `R → S` through the quotient of `B'` by the
kernel of `B' → B`, and that kernel is nilpotent, hence closed and of nilpotent power.

## Main results

* `Deformation.exists_versal_formalObject_changeOfFields`: **Stacks 0DQF**.
* `Deformation.exists_versal_formalObject_changeOfFields_pushforward`: Stacks 0DQF with the
  levels of the new formal object exhibited as pushforwards of those of `ξ` (Stacks 0DR1).

## Implementation notes

The comparison of a point of the represented functor of `S` with a point of the represented
functor of `R` is written through the pullback presentation `B ×_l k` of the comparison
functor, so that its two coordinates are the composite `R → S → B` and the residue of `R`.
That the composite lands in the subalgebra `B ×_l k` is exactly the compatibility of `R → S`
with the residue-field identifications.

Versality of the resulting formal object is deduced from smoothness of a represented morphism
through the Yoneda equivalence of Tag 06SK: the formal object recovered from the associated
morphism of a formal object is that formal object, so the associated morphism and the given
smooth morphism have isomorphic images and are therefore isomorphic.

## References

* [Stacks Project, Tag 0DQF](https://stacks.math.columbia.edu/tag/0DQF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open scoped TensorProduct

universe u v w x y z uF vF u₁ v₁ u₂ v₂ t

namespace Deformation

/-! ### Versality from a smooth represented morphism -/

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

variable {F : Type uF} [Category.{vF} F]
  {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- Transporting a morphism out of a restricted represented category along an equality of
representing complete local algebras preserves smoothness. -/
private theorem isSmooth_cast_restricted
    {R R' : CompleteLocalAlgCat.{u, v, w} Λ k} (h : R = R')
    (φ : BasedFunctor
      (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p))
    (hφ : IsSmooth φ) : IsSmooth (h ▸ φ) := by
  cases h
  change IsSmooth φ
  exact hφ

/-- Transporting a subtype element along an equality of the constrained value does not change
its underlying term. -/
private theorem cast_subtype_val
    {α : Sort u₁} {β : Sort v₁} (f : α → β) {a b : β} (h : a = b)
    (y : {z : α // f z = a}) : (h ▸ y).1 = y.1 := by
  cases h
  rfl

/-- Transporting the Yoneda equivalence and a represented morphism along the same equality of
representing algebras transports their value. -/
private theorem cast_representableEquivalence_functor
    {R R' : CompleteLocalAlgCat.{u, v, w} Λ k} (h : R = R')
    (E : RepresentableMorphismFormalObjectEquivalence p R)
    (φ : BasedFunctor
      (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p)) :
    (h ▸ E).equivalence.functor.obj (h ▸ φ) = h ▸ E.equivalence.functor.obj φ := by
  cases h
  rfl

/-- The formal object corresponding under the Yoneda equivalence to a smooth morphism out of a
restricted represented category is versal. -/
private theorem isVersal_of_smooth_representable
    (hp : IsCofiberedInGroupoids p)
    {R : CompleteLocalAlgCat.{u, v, w} Λ k}
    (E : RepresentableMorphismFormalObjectEquivalence p R)
    (φ : BasedFunctor
      (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p))
    (hφ : IsSmooth φ) :
    IsVersal hp (E.equivalence.functor.obj φ).1 := by
  let ξFiber := E.equivalence.functor.obj φ
  let ξ := ξFiber.1
  have hξbase : ξ.base = R := ξFiber.2
  let E' : RepresentableMorphismFormalObjectEquivalence p ξ.base := hξbase.symm ▸ E
  let φ' : BasedFunctor
      (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda ξ.base)))
      (BasedCategory.ofFunctor p) := hξbase.symm ▸ φ
  have hφ' : IsSmooth φ' := isSmooth_cast_restricted hξbase.symm φ hφ
  have hξFiber' : E'.equivalence.functor.obj φ' =
      (Functor.Fiber.mk (rfl : ξ.base = ξ.base) :
        (FormalObject.projection (p := p)).Fiber ξ.base) := by
    calc
      E'.equivalence.functor.obj φ' = hξbase.symm ▸ ξFiber :=
        cast_representableEquivalence_functor hξbase.symm E φ
      _ = _ := by
        apply Subtype.ext
        exact cast_subtype_val (FormalObject.projection (p := p)).obj hξbase.symm ξFiber
  let pushforwards := chosenPushforwardsOfCofibered p hp
  let assoc := associatedMorphism hp ξ pushforwards
  obtain ⟨hAssocFiber⟩ := associatedMorphism_maps_to hp ξ E' pushforwards
  have hAssocIso : assoc.toBasedFunctor ≅ φ' :=
    E'.equivalence.fullyFaithfulFunctor.preimageIso (hAssocFiber ≪≫ eqToIso hξFiber'.symm)
  exact (isSmooth_associatedMorphism_iff_isVersal hp ξ pushforwards).mp
    (isSmooth_of_iso hAssocIso hφ')

end

section

/-- **The comparison algebra `B ×_l k` is nilpotent of the same order as `B`.** The first
projection `B ×_l k → B` is injective and sends the maximal ideal into the maximal ideal, so a
vanishing power of `𝔪_B` gives the same vanishing power of the maximal ideal of `B ×_l k`. -/
private theorem comparison_maximalIdeal_pow_eq_bot (S : ChangeOfFieldsSituation.{u, v, w})
    (B : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) {n : ℕ} (hB : maximalIdeal B ^ (n + 1) = ⊥) :
    maximalIdeal ((comparisonFunctor.{u, v, w, x} S).functor.obj B) ^ (n + 1) = ⊥ := by
  let cf := comparisonFunctor.{u, v, w, x} S
  let φ : cf.functor.obj B →+* B :=
    (RingHom.pullbackFst (residueMap S B) (algebraMap S.k S.l)).comp
      (cf.pullbackEquiv B).toRingHom
  have hφ (a : cf.functor.obj B) : φ a = ((cf.pullbackEquiv B) a).val.1 := rfl
  have hprop (a : cf.functor.obj B) :
      residueMap S B ((cf.pullbackEquiv B) a).val.1 =
        algebraMap S.k S.l ((cf.pullbackEquiv B) a).val.2 :=
    ((cf.pullbackEquiv B) a).property
  have hinj : Function.Injective φ := by
    intro a b hab
    rw [hφ, hφ] at hab
    refine (cf.pullbackEquiv B).injective
      (Subtype.ext (Prod.ext hab ((algebraMap S.k S.l).injective ?_)))
    rw [← hprop, ← hprop, hab]
  have hmax : Ideal.map φ (maximalIdeal (cf.functor.obj B)) ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have h0 : residue (cf.functor.obj B) a = 0 := (IsLocalRing.residue_eq_zero_iff a).mpr ha
    have h2 : ((cf.pullbackEquiv B) a).val.2 = 0 := by
      rw [← cf.residue_snd B a, h0, map_zero]
    have h3 : B.residueEquiv (residue B (φ a)) = 0 := by
      change residueMap S B (φ a) = 0
      rw [hφ, hprop, h2, map_zero]
    change φ a ∈ maximalIdeal B
    rw [← IsLocalRing.residue_eq_zero_iff]
    exact (map_eq_zero_iff _ B.residueEquiv.injective).mp h3
  rw [eq_bot_iff]
  intro a ha
  have hφa : φ a ∈ maximalIdeal B ^ (n + 1) := by
    have h := Ideal.mem_map_of_mem φ ha
    rw [Ideal.map_pow] at h
    exact Ideal.pow_right_mono hmax (n + 1) h
  rw [hB, Ideal.mem_bot] at hφa
  rw [Ideal.mem_bot]
  exact hinj (hφa.trans (map_zero φ).symm)

end

/-! ### Pushforwards of the levels of a formal object -/

section

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type uF} [Category.{vF} F] {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}

/-- A composite of identifications, with an identity in the middle, is an identification. -/
private theorem eqToHom_id_eqToHom_comp_eqToHom {C : Type*} [Category C] {X Y Z W : C}
    (a : X = Y) (b : Y = Z) (c : Z = W) (d : X = W) :
    (eqToHom a ≫ 𝟙 Y ≫ eqToHom b) ≫ eqToHom c = eqToHom d := by
  subst a b c
  simp

/-- Compatibility with the transitions of a family of arrows out of the levels of a formal object
which factor through earlier levels: if `ξ_{L m} ⟶ X_m ⟶ Y_m` are compatible with given maps
`X_{n+1} ⟶ X_n` and `Y_{n+1} ⟶ Y_n`, the composites with the transitions `ξ_m ⟶ ξ_{L m}` are
compatible with the transitions of `ξ`. -/
private theorem transitionTo_comp_naturality (ξ : FormalObject p) (L : ℕ → ℕ)
    (hL : ∀ n, L n ≤ n) (X Y : ℕ → F) (PI : ∀ m, ξ.level (L m) ⟶ X m) (Lf : ∀ m, X m ⟶ Y m)
    (M : ∀ n, X (n + 1) ⟶ X n) (tY : ∀ n, Y (n + 1) ⟶ Y n)
    (hcomm : ∀ n, M n ≫ Lf n = Lf (n + 1) ≫ tY n)
    (hmp : ∀ n, transitionTo ξ (Nat.le_max_left (L (n + 1)) (L n)) ≫ PI (n + 1) ≫ M n =
      transitionTo ξ (Nat.le_max_right (L (n + 1)) (L n)) ≫ PI n) (n : ℕ) :
    (transitionTo ξ (hL (n + 1)) ≫ PI (n + 1) ≫ Lf (n + 1)) ≫ tY n =
      ξ.transition n ≫ transitionTo ξ (hL n) ≫ PI n ≫ Lf n := by
  have hmax : max (L (n + 1)) (L n) ≤ n + 1 := max_le (hL (n + 1)) ((hL n).trans (Nat.le_succ n))
  have e1 : transitionTo ξ (hL (n + 1)) =
      transitionTo ξ hmax ≫ transitionTo ξ (Nat.le_max_left _ _) :=
    (transitionTo_comp ξ _ hmax).symm
  have e2 : ξ.transition n ≫ transitionTo ξ (hL n) =
      transitionTo ξ hmax ≫ transitionTo ξ (Nat.le_max_right _ _) :=
    (transitionTo_succ ξ (hL n)).symm.trans (transitionTo_comp ξ _ hmax).symm
  rw [Category.assoc, Category.assoc, ← hcomm, e1, Category.assoc, reassoc_of% (hmp n),
    ← Category.assoc, ← Category.assoc, ← e2]
  simp only [Category.assoc]

end

section

variable (S : ChangeOfFieldsSituation.{u, v, w}) {F : Type y} [Category.{z} F]
  {p : F ⥤ ArtinianLocalAlgCat.{u, max x v w, v} S.Λ S.k}

/-- The first component of a morphism of `𝓕_{l/k}` out of an object whose structure isomorphism
is an identification, followed by the structure isomorphism of the target and the
identification of its base, is an identification. -/
private theorem changeOfFields_hom_fst_comp
    {a b : CategoricalPullback p (comparisonFunctor.{u, v, w, max x v w} S).functor}
    (I : a ⟶ b) {B : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l} (e : b.snd = B)
    (hX : p.obj a.fst = (comparisonFunctor.{u, v, w, max x v w} S).functor.obj a.snd)
    (ha : a.iso.hom = eqToHom hX) (e' : a.snd = B)
    (hsnd : I.snd ≫ eqToHom e = eqToHom e') :
    p.map I.fst ≫ b.iso.hom ≫ (comparisonFunctor.{u, v, w, max x v w} S).functor.map
        (eqToHom e) =
      eqToHom (hX.trans (congrArg (comparisonFunctor.{u, v, w, max x v w} S).functor.obj e')) := by
  rw [I.w_assoc, ha, ← Functor.map_comp, hsnd, eqToHom_map, eqToHom_trans]

/-- The base map of a composite `x ⟶ z ⟶ X ⟶ Y.fst` of `𝓕`, the first two arrows lying over
`t` and `c` and the last one compatible with the structure isomorphism of `Y ∈ 𝓕_{l/k}`, read in
`B ×_l k` through that isomorphism, is `t ≫ c`. -/
private theorem changeOfFields_composite_map_eq
    {x z X X' : F}
    {Y : CategoricalPullback p (comparisonFunctor.{u, v, w, max x v w} S).functor}
    {A A' : ArtinianLocalAlgCat.{u, max x v w, v} S.Λ S.k}
    {B : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l}
    (hx : p.obj x = A) (τ : x ⟶ z) (t : A ⟶ A') (hτ : p.IsHomLift t τ)
    (π : z ⟶ X) (h0 : X = X')
    (c : A' ⟶ (comparisonFunctor.{u, v, w, max x v w} S).functor.obj B)
    (hπ : p.IsHomLift c (π ≫ eqToHom h0)) (ℓ : X ⟶ Y.fst) (e : Y.snd = B)
    (hX : p.obj X = (comparisonFunctor.{u, v, w, max x v w} S).functor.obj B)
    (hℓ : p.map ℓ ≫ Y.iso.hom ≫ (comparisonFunctor.{u, v, w, max x v w} S).functor.map
        (eqToHom e) = eqToHom hX) :
    eqToHom hx.symm ≫ p.map (τ ≫ π ≫ ℓ) ≫ Y.iso.hom ≫
        (comparisonFunctor.{u, v, w, max x v w} S).functor.map (eqToHom e) = t ≫ c := by
  subst h0
  simp only [eqToHom_refl, Category.comp_id] at hπ
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hℓ,
    IsHomLift.fac' p t τ, IsHomLift.fac' p c π]
  simp

end

/-! ### Versal formal objects after a change of residue field -/

section

/-- The residue map of an Artinian local `Λ`-algebra with residue field `l`, as an algebra map. -/
private def residueMapAlgHom (S : ChangeOfFieldsSituation.{u, v, w})
    (A : ArtinianLocalAlgCat.{u, x, w} S.Λ S.l) : A →ₐ[S.Λ] S.l where
  toRingHom := residueMap S A
  commutes' a := by
    calc
      A.residueEquiv (residue A (algebraMap S.Λ A a)) =
          A.residueEquiv (algebraMap A (ResidueField A) (algebraMap S.Λ A a)) := by
            rw [IsLocalRing.ResidueField.algebraMap_eq]
      _ = A.residueEquiv (algebraMap S.Λ (ResidueField A) a) := by
            rw [IsScalarTower.algebraMap_apply S.Λ A (ResidueField A) a]
      _ = algebraMap S.Λ S.l a := A.residueEquiv.commutes a

/-- The morphism from the restricted functor represented by `T` to the change of residue field of
the restricted functor represented by `R`, attached to a natural family of Artinian points
`R → B ×_l k` indexed by the Artinian points `T → B`. -/
private def pointToChangedFunctor (S : ChangeOfFieldsSituation.{u, v, w})
    (R : CompleteLocalAlgCat.{u, max x v w, v} S.Λ S.k)
    (T : CompleteLocalAlgCat.{u, max x v w, w} S.Λ S.l)
    (pointAt : ∀ A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l,
      (restrictedCoyoneda T).obj A →
        (restrictedCoyoneda R).obj ((comparisonFunctor.{u, v, w, max x v w} S).functor.obj A))
    (pointAt_natural : ∀ {A C : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l} (g : A ⟶ C)
      (α : (restrictedCoyoneda T).obj A),
      pointAt C ((restrictedCoyoneda T).map g α) =
        (restrictedCoyoneda R).map ((comparisonFunctor.{u, v, w, max x v w} S).functor.map g)
          (pointAt A α)) :
    BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda T)))
      (BasedCategory.ofFunctor (changeOfFieldsProjection.{u, v, w, max x v w} S
        (Functor.Elements.π (restrictedCoyoneda R)))) := by
  let cf := comparisonFunctor.{u, v, w, max x v w} S
  let reprT := restrictedCoyoneda T
  let reprR := restrictedCoyoneda R
  refine ⟨?_, ?_⟩
  · refine {
      obj := fun α => ⟨reprR.elementsMk (cf.functor.obj α.1) (pointAt α.1 α.2), α.1, Iso.refl _⟩
      map := fun {α β} g => by
        let aR : reprR.Elements := reprR.elementsMk (cf.functor.obj α.1) (pointAt α.1 α.2)
        let bR : reprR.Elements := reprR.elementsMk (cf.functor.obj β.1) (pointAt β.1 β.2)
        let gR : aR ⟶ bR := Functor.Elements.homMk
          (cf.functor.map g.hom) (by
            change reprR.map (cf.functor.map g.hom) (pointAt α.1 α.2) = pointAt β.1 β.2
            calc
              _ = pointAt β.1 (reprT.map g.hom α.2) := (pointAt_natural g.hom α.2).symm
              _ = pointAt β.1 β.2 := congrArg (pointAt β.1) g.map_val)
        exact ⟨gR, g.hom, rfl⟩
      map_id := by
        intro α
        apply CategoricalPullback.Hom.ext
        · apply Functor.Elements.hom_ext
          change cf.functor.map (𝟙 α.1) = 𝟙 (cf.functor.obj α.1)
          exact cf.functor.map_id α.1
        · rfl
      map_comp := by
        intro α β γ g h
        apply CategoricalPullback.Hom.ext
        · apply Functor.Elements.hom_ext
          change cf.functor.map (g.hom ≫ h.hom) =
            cf.functor.map g.hom ≫ cf.functor.map h.hom
          exact cf.functor.map_comp g.hom h.hom
        · rfl }
  · rfl

/-- **The levels of the formal object of Stacks 0DQF are pushforwards.** Let `newMap` be the
composite of the morphism attached to a natural family of Artinian points `R → B ×_l k` (whose
first coordinates are `T → B` composed with `f : R → T`) with the change of residue field of the
morphism associated to `ξ`, and let `ζ` be the formal object of `𝓕_{l/k}` over `T` corresponding
to it under the Yoneda equivalence. Then every level of `ξ` maps to the corresponding level of
`ζ`, compatibly with the transitions, over a map whose first coordinate is the reduction of
`f`. -/
private theorem pushforward_levels (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v w, v} S.Λ S.k)
    (hp : IsCofiberedInGroupoids p) (ξ : FormalObject p)
    (T : CompleteLocalAlgCat.{u, max x v w, w} S.Λ S.l) (f : ξ.base →ₐ[S.Λ] T)
    (pointAt : ∀ A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l,
      (restrictedCoyoneda T).obj A →
        (restrictedCoyoneda ξ.base).obj ((comparisonFunctor.{u, v, w, max x v w} S).functor.obj A))
    (pointAt_natural : ∀ {A C : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l} (g : A ⟶ C)
      (α : (restrictedCoyoneda T).obj A),
      pointAt C ((restrictedCoyoneda T).map g α) =
        (restrictedCoyoneda ξ.base).map ((comparisonFunctor.{u, v, w, max x v w} S).functor.map g)
          (pointAt A α))
    (pointAt_fst : ∀ (A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l)
      (α : (restrictedCoyoneda T).obj A) (r : ξ.base),
      (((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv A) ((pointAt A α).hom r)).val.1 =
        α.hom (f r)) :
    let ζ := (representableMorphismFormalObjectEquivalence
      (changeOfFieldsProjection.{u, v, w, max x v w} S p)
      (changeOfFieldsProjection_isCofiberedInGroupoids.{u, v, w, max x v w, y, z} S p hp)
      T).equivalence.functor.obj (BasedFunctor.comp
        (pointToChangedFunctor.{u, v, w, x} S ξ.base T pointAt pointAt_natural)
        (changeOfFieldsBasedFunctor.{u, v, w, max x v w} S
          (associatedMorphism hp ξ (chosenPushforwardsOfCofibered p hp)).toBasedFunctor))
    ∃ g : ∀ n, ξ.level n ⟶ (ζ.1.level n).fst,
      (∀ n, g (n + 1) ≫ (ζ.1.transition n).fst = ξ.transition n ≫ g n) ∧
      ∀ (n : ℕ) (r : ξ.base),
        ((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv
            ((AdicTruncation.functor n).obj T)
          ((eqToHom (ξ.level_eq n).symm ≫ p.map (g n) ≫ (ζ.1.level n).iso.hom ≫
              (comparisonFunctor.{u, v, w, max x v w} S).functor.map
                (eqToHom ((ζ.1.level_eq n).trans
                  (congrArg (AdicTruncation.functor n).obj ζ.2)))).hom
            (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n) r :
              AdicTruncation.obj ξ.base n))).val.1 =
          (Ideal.Quotient.mk (AdicTruncation.ideal T n) (f r) :
            AdicTruncation.obj T n) := by
  intro ζ
  let cf := comparisonFunctor.{u, v, w, max x v w} S
  let pushforwards := chosenPushforwardsOfCofibered p hp
  let ξMap := associatedMorphism hp ξ pushforwards
  let pointToChanged := pointToChangedFunctor.{u, v, w, x} S ξ.base T pointAt pointAt_natural
  let newMap := BasedFunctor.comp pointToChanged
    (changeOfFieldsBasedFunctor.{u, v, w, max x v w} S ξMap.toBasedFunctor)
  let p' := changeOfFieldsProjection.{u, v, w, max x v w} S p
  let E := representableMorphismFormalObjectEquivalence p'
    (changeOfFieldsProjection_isCofiberedInGroupoids.{u, v, w, max x v w, y, z} S p hp) T
  -- The canonical Artinian points `T → T/𝔪^{n+1}` and their images `R → (T/𝔪^{n+1}) ×_l k`.
  let eT : ℕ → (restrictedCoyoneda T).Elements := fun n =>
    (restrictedCoyoneda T).elementsMk (AdicTruncation.obj T n) (E.quotientPoint n)
  let αR : ℕ → (restrictedCoyoneda ξ.base).Elements := fun n =>
    (restrictedCoyoneda ξ.base).elementsMk (cf.functor.obj (AdicTruncation.obj T n))
      (pointAt _ (E.quotientPoint n))
  let gT : ∀ n, eT (n + 1) ⟶ eT n := fun n => Functor.Elements.homMk (x := eT (n + 1)) (y := eT n)
    (AdicTruncation.transition T n) (E.projectionPoint n)
  let gR : ∀ n, αR (n + 1) ⟶ αR n := fun n => (pointToChanged.map (gT n)).fst
  -- The value of `newMap` at the canonical points, compared with the levels of `ζ`, with the
  -- morphisms read in `F`.
  let Lf : ∀ m, @Quiver.Hom F _ (ξMap.toBasedFunctor.obj (αR m)) (ζ.1.level m).fst :=
    fun m => (E.levelIso newMap m).hom.fst
  have hcomm : ∀ n, @CategoryStruct.comp F _ _ _ _ (ξMap.toBasedFunctor.map (gR n)) (Lf n) =
      Lf (n + 1) ≫ (ζ.1.transition n).fst := fun n =>
    congrArg CategoricalPullback.Hom.fst (E.transition_comm newMap n)
  have hw : ∀ n, p.map (Lf n) ≫ (ζ.1.level n).iso.hom ≫
      cf.functor.map (eqToHom ((ζ.1.level_eq n).trans
        (congrArg (AdicTruncation.functor n).obj ζ.2))) =
      eqToHom (X := p.obj (ξMap.toBasedFunctor.obj (αR n)))
        (Y := cf.functor.obj (AdicTruncation.obj T n))
        (Functor.congr_obj ξMap.toBasedFunctor.w (αR n)) := by
    intro n
    have ha : (newMap.obj (eT n)).iso.hom =
        eqToHom (Functor.congr_obj ξMap.toBasedFunctor.w (αR n)) := by
      change (eqToIso ξMap.toBasedFunctor.w.symm).inv.app (αR n) ≫ 𝟙 _ ≫ 𝟙 _ = _
      rw [Category.comp_id, Category.comp_id, eqToIso.inv]
      exact eqToHom_app _ _
    have := E.levelIso_over newMap n
    have h3 : (E.levelIso newMap n).hom.snd =
        eqToHom (IsHomLift.domain_eq p' (𝟙 (AdicTruncation.obj T n))
            (E.levelIso newMap n).hom) ≫ 𝟙 _ ≫
          eqToHom (IsHomLift.codomain_eq p' (𝟙 (AdicTruncation.obj T n))
            (E.levelIso newMap n).hom).symm :=
      IsHomLift.fac' p' (𝟙 (AdicTruncation.obj T n)) (E.levelIso newMap n).hom
    have hsnd : (E.levelIso newMap n).hom.snd ≫ eqToHom ((ζ.1.level_eq n).trans
          (congrArg (AdicTruncation.functor n).obj ζ.2)) =
        eqToHom (X := (newMap.obj (eT n)).snd) (Y := (AdicTruncation.functor n).obj T) rfl :=
      (congrArg (· ≫ _) h3).trans (eqToHom_id_eqToHom_comp_eqToHom _ _ _ _)
    exact changeOfFields_hom_fst_comp S (E.levelIso newMap n).hom _ _ ha rfl hsnd
  clear_value Lf
  clear_value ζ
  have hLe : ∀ n, ξMap.level (αR n) ≤ n := fun n =>
    (ξMap.factor_spec (αR n)).2.1 n
      (comparison_maximalIdeal_pow_eq_bot S _
        (HomEquivalenceCounit.maximalIdeal_adicTruncation_pow_eq_bot T n))
  refine ⟨fun n => transitionTo ξ (hLe n) ≫ ξMap.pointInclusion (αR n) ≫ Lf n,
    fun n => ?_, fun n r => ?_⟩
  · exact transitionTo_comp_naturality ξ (fun m => ξMap.level (αR m)) hLe
      (fun m => ξMap.toBasedFunctor.obj (αR m)) (fun m => (ζ.1.level m).fst)
      (fun m => ξMap.pointInclusion (αR m)) Lf (fun m => ξMap.toBasedFunctor.map (gR m))
      (fun m => (ζ.1.transition m).fst) hcomm (fun m => ξMap.map_pointInclusion (gR m)) n
  · obtain ⟨t, ht, htl⟩ := transitionTo_lift ξ (hLe n)
    have hpI : p.IsHomLift (ξMap.factor (αR n))
        (ξMap.pointInclusion (αR n) ≫ eqToHom (ξMap.obj_eq (αR n))) := by
      rw [ξMap.pointInclusion_eq]
      exact ((pushforwards (ξMap.factor (αR n))).cocartesian
        ⟨ξ.level (ξMap.level (αR n)), ξ.level_eq (ξMap.level (αR n))⟩).toIsHomLift
    obtain ⟨c, hc⟩ : ∃ c : AdicTruncation.obj ξ.base (ξMap.level (αR n)) ⟶
        cf.functor.obj (AdicTruncation.obj T n), c = ξMap.factor (αR n) := ⟨_, rfl⟩
    obtain ⟨π, hπ⟩ : ∃ π : @Quiver.Hom F _ (ξ.level (ξMap.level (αR n)))
        (ξMap.toBasedFunctor.obj (αR n)), π = ξMap.pointInclusion (αR n) := ⟨_, rfl⟩
    have hpI' : p.IsHomLift c (π ≫ eqToHom (ξMap.obj_eq (αR n))) := by
      rwa [hc, hπ]
    have hM := changeOfFields_composite_map_eq S (ξ.level_eq n) (transitionTo ξ (hLe n)) t htl
      π (ξMap.obj_eq (αR n)) c hpI' (Lf n)
      ((ζ.1.level_eq n).trans (congrArg (AdicTruncation.functor n).obj ζ.2))
      (Functor.congr_obj ξMap.toBasedFunctor.w (αR n)) (hw n)
    beta_reduce
    rw [← hπ]
    refine (congrArg (fun m => ((cf.pullbackEquiv _) (m.hom
      (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n) r : AdicTruncation.obj ξ.base n))).val.1)
      hM).trans ?_
    have hfac := DFunLike.congr_fun (ξMap.factor_spec (αR n)).2.2 r
    have htr := DFunLike.congr_fun ht r
    rw [← hc] at hfac
    change (cf.pullbackEquiv (AdicTruncation.obj T n)
      (c.hom (t.hom (Ideal.Quotient.mk _ r)))).val.1 = _
    change t.hom (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r at htr
    rw [htr]
    change c.hom (Ideal.Quotient.mk _ r) = (pointAt _ (E.quotientPoint n)).hom r at hfac
    rw [hfac, pointAt_fst, E.quotientPoint_hom]
    rfl

/-- **Lifting along a surjection of Artinian local rings.** If `f : R → T` is formally smooth for
the `𝔪_T`-adic topology, `π : B → A` is a surjection of Artinian local rings and `α : T → A` is a
local map with `α ∘ f = π ∘ g₀`, then some `T → B` restricts to `g₀` and lifts `α`. -/
private theorem exists_lift_of_formallySmoothNAdic {R : Type u₁} {T : Type v₁} {B A : Type t}
    [CommRing R] [CommRing T] [IsLocalRing T] [CommRing B] [IsLocalRing B] [IsArtinianRing B]
    [CommRing A] [IsLocalRing A] [IsArtinianRing A]
    (f : R →+* T) (hf : RingHom.FormallySmoothNAdic.{t} f (maximalIdeal T))
    (π : B →+* A) (hπ : Function.Surjective π) (α : T →+* A) [IsLocalHom α]
    (g₀ : R →+* B) (hg₀ : ∀ r, α (f r) = π (g₀ r)) :
    ∃ lift : T →+* B, lift.comp f = g₀ ∧ π.comp lift = α := by
  let J : Ideal B := RingHom.ker π
  let eπ := π.quotientKerEquivOfSurjective hπ
  let ψ : T →+* B ⧸ J := eπ.symm.toRingHom.comp α
  have hnil (C : Type t) [CommRing C] [IsLocalRing C] [IsArtinianRing C] :
      ∃ n : ℕ, maximalIdeal C ^ (n + 1) = ⊥ := by
    obtain ⟨n, hn⟩ := (isArtinianRing_iff_isNilpotent_maximalIdeal C).mp inferInstance
    exact ⟨n, by simpa [pow_succ] using congrArg (fun I : Ideal C => I * maximalIdeal C) hn⟩
  have hψkill : ∃ n : ℕ, 1 ≤ n ∧ maximalIdeal T ^ n ≤ RingHom.ker ψ := by
    obtain ⟨n, hn'⟩ := hnil A
    refine ⟨n + 1, by omega, fun a ha => ?_⟩
    have hm : α a ∈ Ideal.map α (maximalIdeal T ^ (n + 1)) := Ideal.mem_map_of_mem α ha
    rw [Ideal.map_pow] at hm
    have hm' := pow_le_pow_left' (IsLocalRing.map_maximalIdeal_le α) (n + 1) hm
    rw [hn', Ideal.mem_bot] at hm'
    change eπ.symm (α a) = 0
    rw [hm', map_zero]
  let _ : TopologicalSpace R := ⊥
  let _ : DiscreteTopology R := ⟨rfl⟩
  let _ : IsTopologicalRing R := inferInstance
  let _ : IsLinearTopology R R := inferInstance
  let _ : TopologicalSpace T := (maximalIdeal T).adicTopology
  let _ : IsTopologicalRing T := (maximalIdeal T).ringFilterBasis.isTopologicalRing
  let _ : IsLinearTopology T T := (maximalIdeal T).isLinearTopology
  have hTadic : IsAdic (maximalIdeal T) := rfl
  have hfs : RingHom.FormallySmoothTop.{t} f :=
    (RingHom.formallySmoothTop_iff_formallySmoothNAdic f (maximalIdeal T) hTadic).2 hf
  let _ : TopologicalSpace B := ⊥
  let _ : DiscreteTopology B := ⟨rfl⟩
  let _ : IsTopologicalRing B := inferInstance
  let _ : IsAdicComplete (⊥ : Ideal B) B := inferInstance
  let _ : TopologicalSpace (B ⧸ J) := ⊥
  let _ : DiscreteTopology (B ⧸ J) := ⟨rfl⟩
  let _ : IsTopologicalRing (B ⧸ J) := inferInstance
  have hψcont : Continuous ψ := by
    rw [(is_bot_adic_iff (A := B ⧸ J)).2 inferInstance]
    exact (RingHom.continuous_adic_iff ψ (maximalIdeal T) ⊥).2 hψkill
  have hJmax : J ≤ maximalIdeal B := IsLocalRing.le_maximalIdeal (RingHom.ker_ne_top π)
  obtain ⟨m, hm⟩ := hnil B
  have hJnil : J ^ (m + 1) = ⊥ :=
    le_antisymm ((pow_le_pow_left' hJmax (m + 1)).trans hm.le) bot_le
  have hcomm : ψ.comp f = (Ideal.Quotient.mk J).comp g₀ := by
    ext r
    change eπ.symm (α (f r)) = _
    rw [hg₀]
    exact DFunLike.congr_fun (RingHom.quotientKerEquivOfSurjective_symm_comp hπ) (g₀ r)
  obtain ⟨lift, -, hliftF, hliftψ⟩ :=
    RingHom.FormallySmoothTop.exists_continuous_lift_of_isAdic
      f (maximalIdeal T) hTadic hfs (⊥ : Ideal B) ((is_bot_adic_iff (A := B)).2 inferInstance)
      J (isClosed_discrete _) (m + 1) (by omega) (by rw [hJnil])
      g₀ continuous_of_discreteTopology ψ hψcont hcomm
  refine ⟨lift, hliftF, ?_⟩
  ext a
  have ha := congrArg eπ (DFunLike.congr_fun hliftψ a)
  change eπ (Ideal.Quotient.mk J (lift a)) = eπ (eπ.symm (α a)) at ha
  have happly := RingHom.quotientKerEquivOfSurjective_apply_mk (f := π) hπ (lift a)
  change eπ (Ideal.Quotient.mk J (lift a)) = π (lift a) at happly
  rw [happly, RingEquiv.apply_symm_apply] at ha
  simpa using ha

/-- Two `Λ`-algebra maps `R → B ×_l k` are equal when their two coordinates agree. -/
private theorem pullback_algHom_ext (S : ChangeOfFieldsSituation.{u, v, w})
    {R : Type*} [CommRing R] [Algebra S.Λ R]
    (A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l)
    {γ δ : R →ₐ[S.Λ] (comparisonFunctor.{u, v, w, max x v w} S).functor.obj A}
    (h₁ : ∀ r, (((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv A) (γ r)).val.1 =
      (((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv A) (δ r)).val.1)
    (h₂ : ∀ r, (((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv A) (γ r)).val.2 =
      (((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv A) (δ r)).val.2) :
    γ = δ :=
  AlgHom.ext fun r => ((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv A).injective
    (Subtype.ext (Prod.ext (h₁ r) (h₂ r)))

/-- **Artinian points of `T` lift along surjections.** Let `fΛ : R → T` be formally smooth for
the `𝔪_T`-adic topology, and let `pointAt` attach to each `α : T → B` the point `R → B ×_l k`
with coordinates `α ∘ fΛ` and the residue of `R`. If `f₀ : B → A` is surjective and the point
attached to `α : T → A` is `f₀ ∘ γ`, then `α = f₀ ∘ α'` for some `α'` whose point is `γ`. -/
private theorem exists_point_lift (S : ChangeOfFieldsSituation.{u, v, w})
    {R : CompleteLocalAlgCat.{u, max x v w, v} S.Λ S.k}
    {T : CompleteLocalAlgCat.{u, max x v w, w} S.Λ S.l} (fΛ : R →ₐ[S.Λ] T)
    (hfSmooth : RingHom.FormallySmoothNAdic.{max x v w} fΛ.toRingHom (maximalIdeal T))
    (pointAt : ∀ A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l,
      (restrictedCoyoneda T).obj A →
        (restrictedCoyoneda R).obj ((comparisonFunctor.{u, v, w, max x v w} S).functor.obj A))
    (pointAt_fst : ∀ (A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l)
      (α : (restrictedCoyoneda T).obj A) (r : R),
      (((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv A) ((pointAt A α).hom r)).val.1 =
        α.hom (fΛ r))
    (pointAt_snd : ∀ (A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l)
      (α : (restrictedCoyoneda T).obj A) (r : R),
      (((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv A) ((pointAt A α).hom r)).val.2 =
        R.residueEquiv (residue R r))
    {B A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l} (f₀ : B ⟶ A)
    (hsurj : Function.Surjective f₀.hom) (α : (restrictedCoyoneda T).obj A)
    (γ : (restrictedCoyoneda R).obj ((comparisonFunctor.{u, v, w, max x v w} S).functor.obj B))
    (hγ : (pointAt A α).hom =
      ((comparisonFunctor.{u, v, w, max x v w} S).functor.map f₀).hom.comp γ.hom) :
    ∃ α' : (restrictedCoyoneda T).obj B,
      (restrictedCoyoneda T).map f₀ α' = α ∧ (pointAt B α').hom = γ.hom := by
  let cf := comparisonFunctor.{u, v, w, max x v w} S
  let kToL : S.k →ₐ[S.Λ] S.l := IsScalarTower.toAlgHom S.Λ S.k S.l
  let g0 : R →+* B :=
    ((AlgHom.pullbackFst (residueMapAlgHom S B) kToL).toRingHom.comp
      (cf.pullbackEquiv B).toRingHom).comp γ.hom.toRingHom
  have hdiag (r : R) : α.hom (fΛ r) = f₀.hom (g0 r) := by
    rw [← pointAt_fst A α r, hγ, AlgHom.comp_apply, cf.map_fst]
    rfl
  let _ : IsLocalHom α.hom.toRingHom := α.isLocal
  obtain ⟨lift, hliftF, hliftPi⟩ := exists_lift_of_formallySmoothNAdic fΛ.toRingHom hfSmooth
    f₀.hom.toRingHom hsurj α.hom.toRingHom g0 hdiag
  have hliftPi' (a : T) : f₀.hom (lift a) = α.hom a := by
    simpa using DFunLike.congr_fun hliftPi a
  let liftAlg : T →ₐ[S.Λ] B :=
    { toRingHom := lift
      commutes' a := by
        calc
          lift (algebraMap S.Λ T a) = lift (fΛ (algebraMap S.Λ R a)) := by rw [fΛ.commutes a]
          _ = g0 (algebraMap S.Λ R a) := DFunLike.congr_fun hliftF _
          _ = algebraMap S.Λ B a := by
            change ((cf.pullbackEquiv B) (γ.hom (algebraMap S.Λ R a))).val.1 = _
            rw [γ.hom.commutes]
            exact cf.algebraMap_fst B a }
  have hliftLocal : IsLocalHom lift :=
    have : IsLocalHom (f₀.hom.toRingHom.comp lift) := by
      rw [hliftPi]
      exact α.isLocal
    isLocalHom_of_comp lift f₀.hom.toRingHom
  let α' : (restrictedCoyoneda T).obj B :=
    { hom := liftAlg
      isLocal := hliftLocal
      residue_comm a := by
        calc
          B.residueEquiv (residue B (lift a)) =
              A.residueEquiv (residue A (f₀.hom (lift a))) := (f₀.residue_comm (lift a)).symm
          _ = A.residueEquiv (residue A (α.hom a)) :=
                congrArg _ (congrArg (residue A) (hliftPi' a))
          _ = T.residueEquiv (residue T a) := α.residue_comm a }
  refine ⟨α', ?_, ?_⟩
  · apply CompleteLocalAlgCat.Hom.ext
    ext a
    exact hliftPi' a
  refine pullback_algHom_ext.{u, v, w, x} S B (fun r => ?_) (fun r => ?_)
  · calc
      ((cf.pullbackEquiv B) ((pointAt B α').hom r)).val.1 = α'.hom (fΛ r) := pointAt_fst B α' r
      _ = g0 r := DFunLike.congr_fun hliftF r
      _ = ((cf.pullbackEquiv B) (γ.hom r)).val.1 := rfl
  · calc
      ((cf.pullbackEquiv B) ((pointAt B α').hom r)).val.2 = R.residueEquiv (residue R r) :=
        pointAt_snd B α' r
      _ = (cf.functor.obj B).residueEquiv (residue (cf.functor.obj B) (γ.hom r)) :=
        (γ.residue_comm r).symm
      _ = ((cf.pullbackEquiv B) (γ.hom r)).val.2 := cf.residue_snd B _

/-- **Points of `T` lift through a formally smooth `R → T`.** If `fΛ : R → T` is formally smooth
for the `𝔪_T`-adic topology, the morphism attached to a natural family of Artinian points
`R → B ×_l k` with coordinates `T → B` composed with `fΛ` and the residue of `R` is smooth. -/
private theorem isSmooth_pointToChangedFunctor (S : ChangeOfFieldsSituation.{u, v, w})
    (R : CompleteLocalAlgCat.{u, max x v w, v} S.Λ S.k)
    (T : CompleteLocalAlgCat.{u, max x v w, w} S.Λ S.l) (fΛ : R →ₐ[S.Λ] T)
    (hfSmooth : RingHom.FormallySmoothNAdic.{max x v w} fΛ.toRingHom (maximalIdeal T))
    (pointAt : ∀ A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l,
      (restrictedCoyoneda T).obj A →
        (restrictedCoyoneda R).obj ((comparisonFunctor.{u, v, w, max x v w} S).functor.obj A))
    (pointAt_natural : ∀ {A C : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l} (g : A ⟶ C)
      (α : (restrictedCoyoneda T).obj A),
      pointAt C ((restrictedCoyoneda T).map g α) =
        (restrictedCoyoneda R).map ((comparisonFunctor.{u, v, w, max x v w} S).functor.map g)
          (pointAt A α))
    (pointAt_fst : ∀ (A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l)
      (α : (restrictedCoyoneda T).obj A) (r : R),
      (((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv A) ((pointAt A α).hom r)).val.1 =
        α.hom (fΛ r))
    (pointAt_snd : ∀ (A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l)
      (α : (restrictedCoyoneda T).obj A) (r : R),
      (((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv A) ((pointAt A α).hom r)).val.2 =
        R.residueEquiv (residue R r)) :
    IsSmooth (pointToChangedFunctor.{u, v, w, x} S R T pointAt pointAt_natural) := by
  let cf := comparisonFunctor.{u, v, w, max x v w} S
  let reprT := restrictedCoyoneda T
  let reprR := restrictedCoyoneda R
  let πT := Functor.Elements.π reprT
  let πR := Functor.Elements.π reprR
  let q := changeOfFieldsProjection.{u, v, w, max x v w} S πR
  let pointToChanged := pointToChangedFunctor.{u, v, w, x} S R T pointAt pointAt_natural
  change IsSmooth pointToChanged
  intro B A f₀ hsurj y xx g hg
  let _ : q.IsHomLift f₀ g := hg
  rcases xx with @⟨A₀, α⟩
  rcases y with ⟨yF, yB, yIso⟩
  have hyB : yB = B := IsHomLift.domain_eq q f₀ g
  have hxA : A₀ = A := IsHomLift.codomain_eq q f₀ g
  subst B A
  have hgf : g.snd = f₀ := IsHomLift.fac' q f₀ g
  have hgbase : g.fst.hom = yIso.hom ≫ cf.functor.map f₀ := by
    have hh := g.w
    change g.fst.hom ≫ 𝟙 _ = yIso.hom ≫ cf.functor.map g.snd at hh
    simp only [Category.comp_id] at hh
    rwa [hgf] at hh
  have hpointHom : (pointAt A₀ α).hom = g.fst.hom.hom.comp yF.2.hom := by
    have hh := congrArg (fun zz : reprR.obj (cf.functor.obj A₀) => zz.hom) g.fst.map_val
    rw [restrictedCoyoneda_map_hom] at hh
    exact hh.symm
  have hpointComp : (pointAt A₀ α).hom =
      (cf.functor.map f₀).hom.comp (yIso.hom.hom.comp yF.2.hom) := by
    rw [hpointHom, hgbase]
    exact AlgHom.comp_assoc _ _ _
  obtain ⟨α', hrep, hpointLift⟩ := exists_point_lift S fΛ hfSmooth pointAt pointAt_fst
    pointAt_snd f₀ hsurj α (reprR.map yIso.hom yF.2) hpointComp
  let x' : reprT.Elements := reprT.elementsMk yB α'
  let h : x' ⟶ reprT.elementsMk A₀ α := Functor.Elements.homMk f₀ hrep
  have hhLift : (BasedCategory.ofFunctor πT).p.IsHomLift f₀ h :=
    IsHomLift.of_fac' πT f₀ h rfl rfl (by rfl)
  let aBase : reprR.Elements := reprR.elementsMk (cf.functor.obj yB) (pointAt yB α')
  have hpointEq : reprR.map yIso.inv (pointAt yB α') = yF.2 := by
    apply CompleteLocalAlgCat.Hom.ext
    apply AlgHom.ext
    intro r
    change yIso.inv.hom ((pointAt yB α').hom r) = yF.2.hom r
    rw [hpointLift]
    have hcancel : yIso.inv.hom.comp yIso.hom.hom = AlgHom.id S.Λ (πR.obj yF) := by
      simpa only [ArtinianLocalAlgCat.comp_hom, ArtinianLocalAlgCat.id_hom] using
        congrArg (fun m : πR.obj yF ⟶ πR.obj yF => m.hom) yIso.hom_inv_id
    change (yIso.inv.hom.comp yIso.hom.hom) (yF.2.hom r) = yF.2.hom r
    rw [hcancel]
    rfl
  let a : pointToChanged.obj x' ⟶ ⟨yF, yB, yIso⟩ :=
    { fst := Functor.Elements.homMk (x := aBase) (y := yF) yIso.inv hpointEq
      snd := 𝟙 yB
      w := by
        change yIso.inv ≫ yIso.hom = 𝟙 (πR.obj aBase) ≫ cf.functor.map (𝟙 yB)
        rw [cf.functor.map_id]
        change yIso.inv ≫ yIso.hom = 𝟙 (cf.functor.obj yB)
        exact yIso.inv_hom_id }
  have haLift : (BasedCategory.ofFunctor q).p.IsHomLift (𝟙 yB) a := IsHomLift.map (p := q) a
  refine ⟨x', h, a, hhLift, haLift, CategoricalPullback.Hom.ext ?_ ?_⟩
  · apply Functor.Elements.hom_ext
    change cf.functor.map f₀ = yIso.inv ≫ g.fst.hom
    rw [hgbase]
    exact (yIso.inv_hom_id_assoc _).symm
  · change f₀ = 𝟙 yB ≫ g.snd
    rw [hgf]
    exact (Category.id_comp _).symm

/-- **A formally smooth lift with residue field `l`.** Every `R` in `𝒞^_{Λ,k}` admits a local
`Λ`-algebra map `f : R → T` to a Noetherian complete local `Λ`-algebra with residue field `l`
which is formally smooth for the `𝔪_T`-adic topology and induces `l/k` on residue fields. -/
private theorem exists_formallySmooth_changeOfFields_lift (S : ChangeOfFieldsSituation.{u, v, w})
    (R : CompleteLocalAlgCat.{u, max x v w, v} S.Λ S.k) :
    ∃ (T : CompleteLocalAlgCat.{u, max x v w, w} S.Λ S.l) (f : R →ₐ[S.Λ] T),
      IsLocalHom f.toRingHom ∧
        (∀ a : R, T.residueEquiv (residue T (f a)) =
          algebraMap S.k S.l (R.residueEquiv (residue R a))) ∧
        RingHom.FormallySmoothNAdic.{max x v w} f.toRingHom (maximalIdeal T) := by
  classical
  let L := ULift.{x} S.l
  let B := smoothModel (Λ := S.k) (k := L)
  let e := R.residueEquiv
  let _ : Algebra (ResidueField R) B :=
    ((algebraMap S.k B).comp e.toRingHom).toAlgebra
  have hB : RingHom.FormallySmoothNAdic.{max x v w}
      (algebraMap (ResidueField R) B) (maximalIdeal B) :=
    RingHom.FormallySmoothNAdic.of_arrowEquiv_of_map_eq
      e.symm.toRingEquiv (RingEquiv.refl B)
      (by
        ext b
        change (algebraMap S.k (B : Type _)) (e (e.symm b)) = _
        simp
        rfl)
      (by simp; rfl)
      (smoothModel_formallySmooth (Λ := S.k) (k := L))
  obtain ⟨T, hCommT, hNoethT, hLocalT, hCompleteT, f, hfLocal, hfSmooth, hFiber⟩ :=
    exists_completeLocal_formallySmooth_lift (A := R) (B := B) hB
  let _ : CommRing T := hCommT
  let _ : IsNoetherianRing T := hNoethT
  let _ : IsLocalRing T := hLocalT
  let _ : IsAdicComplete (maximalIdeal T) T := hCompleteT
  let _ : Algebra R T := f.toAlgebra
  let _ : Algebra S.Λ T := (f.comp (algebraMap S.Λ R)).toAlgebra
  let _ : IsScalarTower S.Λ R T := IsScalarTower.of_algebraMap_eq' rfl
  let D := ResidueField R ⊗[R] T
  let eFiber : D ≃ₐ[ResidueField R] B := Classical.choice hFiber
  let _ : IsLocalRing D :=
    IsLocalRing.of_surjective' eFiber.symm.toRingEquiv.toRingHom
      eFiber.symm.toRingEquiv.surjective
  let _ : Algebra S.Λ (ResidueField R) := inferInstance
  let _ : IsScalarTower S.Λ (ResidueField R) D := inferInstance
  let _ : Algebra S.Λ B :=
    ((algebraMap S.k B).comp (algebraMap S.Λ S.k)).toAlgebra
  let _ : IsScalarTower S.Λ S.k B := IsScalarTower.of_algebraMap_eq' rfl
  let _ : IsScalarTower S.Λ (ResidueField R) B := IsScalarTower.of_algebraMap_eq' (by
    ext a
    change (algebraMap S.k B) ((algebraMap S.Λ S.k) a) =
      (algebraMap S.k B) (e ((algebraMap S.Λ (ResidueField R)) a))
    rw [e.commutes])
  let eFiberΛ : D ≃ₐ[S.Λ] B := eFiber.restrictScalars S.Λ
  let eResFiber := IsLocalRing.ResidueField.mapAlgEquiv eFiberΛ
  let j : T →ₐ[R] D := Algebra.TensorProduct.includeRight
  have hj : Function.Surjective j :=
    Algebra.TensorProduct.includeRight_surjective T
      (IsLocalRing.residue_surjective (R := (R : Type _)))
  let _ : IsLocalHom j.toRingHom := IsLocalHom.of_surjective j.toRingHom hj
  let jΛ : T →ₐ[S.Λ] D := j.restrictScalars S.Λ
  let _ : IsLocalHom jΛ.toRingHom := IsLocalHom.of_surjective jΛ.toRingHom hj
  let _ : IsLocalHom jΛ := by
    refine ⟨fun a ha => ?_⟩
    change IsUnit (jΛ.toRingHom a) at ha
    exact @IsLocalHom.map_nonunit T D (T →+* D) _ _ _ jΛ.toRingHom inferInstance a ha
  let eResT := AlgEquiv.ofBijective (IsLocalRing.ResidueField.mapAlgHom jΛ)
    ⟨RingHom.injective _, fun b => by
      obtain ⟨d, rfl⟩ := IsLocalRing.residue_surjective (R := D) b
      obtain ⟨c, rfl⟩ := hj d
      exact ⟨residue T c, rfl⟩⟩
  let eResB : ResidueField B ≃ₐ[S.Λ] ULift.{x} S.l := B.residueEquiv.restrictScalars S.Λ
  let eULift : ULift.{x} S.l ≃ₐ[S.Λ] S.l := ULift.algEquiv (R := S.Λ) (A := S.l)
  let residueEquivT : ResidueField T ≃ₐ[S.Λ] S.l :=
    eResT.trans (eResFiber.trans (eResB.trans eULift))
  let Tcat : CompleteLocalAlgCat.{u, max x v w, w} S.Λ S.l :=
    ⟨T, ⟨hNoethT, hLocalT, hCompleteT⟩, residueEquivT⟩
  have hBscalar (z : ResidueField R) :
      eULift (B.residueEquiv (residue B ((algebraMap (ResidueField R) B) z))) =
        algebraMap S.k S.l (e z) := by
    change eULift (B.residueEquiv (residue B ((algebraMap S.k B) (e z)))) = _
    rw [← IsLocalRing.ResidueField.algebraMap_eq,
      ← IsScalarTower.algebraMap_apply S.k B (ResidueField B) (e z), B.residueEquiv.commutes]
    rfl
  have hresf (r : R) :
      residueEquivT (residue T (f r)) =
        algebraMap S.k S.l (R.residueEquiv (residue R r)) := by
    have hjf : j (f r) = algebraMap (ResidueField R) D (residue R r) := by
      calc
        j (f r) = algebraMap R D r := by
          change j (algebraMap R T r) = _
          exact j.commutes r
        _ = algebraMap (ResidueField R) D (residue R r) := by
          rw [IsScalarTower.algebraMap_apply R (ResidueField R) D r]
          simp [IsLocalRing.ResidueField.algebraMap_eq]
    have hResT : eResT (residue T (f r)) = residue D (j (f r)) := by
      change IsLocalRing.ResidueField.mapAlgHom jΛ (residue T (f r)) = _
      rw [IsLocalRing.ResidueField.mapAlgHom_residue]
      rfl
    have hResFiber : eResFiber (residue D (j (f r))) = residue B (eFiber (j (f r))) := by
      change IsLocalRing.ResidueField.mapAlgEquiv eFiberΛ (residue D (j (f r))) = _
      rw [IsLocalRing.ResidueField.mapAlgEquiv_residue]
      rfl
    change eULift (eResB (eResFiber (eResT (residue T (f r))))) = _
    rw [hResT, hResFiber, hjf, eFiber.commutes]
    simpa [eResB] using hBscalar (residue R r)
  exact ⟨Tcat, IsScalarTower.toAlgHom S.Λ R T, hfLocal, hresf, hfSmooth⟩

/-- The Artinian point `R → B ×_l k` attached to a point `α : T → B`, for a `Λ`-algebra map
`fΛ : R → T` compatible with the residue fields: its coordinates are `α ∘ fΛ` and the residue
map of `R`. -/
private def changeOfFieldsPoint (S : ChangeOfFieldsSituation.{u, v, w})
    (R : CompleteLocalAlgCat.{u, max x v w, v} S.Λ S.k)
    (T : CompleteLocalAlgCat.{u, max x v w, w} S.Λ S.l) (fΛ : R →ₐ[S.Λ] T)
    (hresf : ∀ r : R, T.residueEquiv (residue T (fΛ r)) =
      algebraMap S.k S.l (R.residueEquiv (residue R r)))
    (A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l) (α : (restrictedCoyoneda T).obj A) :
    (restrictedCoyoneda R).obj ((comparisonFunctor.{u, v, w, max x v w} S).functor.obj A) := by
  let cf : ComparisonFunctor.{u, v, w, max x v w} S :=
    comparisonFunctor.{u, v, w, max x v w} S
  let e := R.residueEquiv
  let resR : R →ₐ[S.Λ] ResidueField R :=
    { toRingHom := residue R
      commutes' := fun _ => rfl }
  let bToL := residueMapAlgHom S A
  let kToL : S.k →ₐ[S.Λ] S.l := IsScalarTower.toAlgHom S.Λ S.k S.l
  let rToK : R →ₐ[S.Λ] S.k := e.toAlgHom.comp resR
  let rToA : R →ₐ[S.Λ] A := α.hom.comp fΛ
  let pbAlg := bToL.pullback kToL
  let paired := AlgHom.prod rToA rToK
  have hpaired (r : R) : paired r ∈ pbAlg := by
    change bToL (rToA r) = kToL (rToK r)
    calc
      bToL (rToA r) = T.residueEquiv (residue T (fΛ r)) := by
        change (artinianToComplete.obj A).residueEquiv
            (residue (artinianToComplete.obj A) (α.hom (fΛ r))) = _
        exact α.residue_comm (fΛ r)
      _ = kToL (rToK r) := hresf r
  let betaSub : R →ₐ[S.Λ] pbAlg := AlgHom.codRestrict paired pbAlg hpaired
  let betaToPullback : pbAlg →+* RingHom.pullback (residueMap S A) (algebraMap S.k S.l) :=
    RingHom.codRestrict pbAlg.val.toRingHom _ (by
      intro zz
      change residueMap S A zz.val.1 = algebraMap S.k S.l zz.val.2
      exact zz.property)
  let betaRing : R →+* cf.functor.obj A :=
    (cf.pullbackEquiv A).symm.toRingHom.comp (betaToPullback.comp betaSub.toRingHom)
  have hβ (x : R) : cf.pullbackEquiv A (betaRing x) = betaToPullback (betaSub x) :=
    RingEquiv.apply_symm_apply _ _
  let betaAlg : R →ₐ[S.Λ] cf.functor.obj A :=
    { toRingHom := betaRing
      commutes' := fun a => (cf.pullbackEquiv A).injective <| Subtype.ext <| Prod.ext
        ((congrArg (fun z => z.val.1) (hβ _)).trans (by
          rw [cf.algebraMap_fst]
          change α.hom (fΛ (algebraMap S.Λ R a)) = _
          rw [fΛ.commutes a]
          exact α.hom.commutes a))
        ((congrArg (fun z => z.val.2) (hβ _)).trans (by
          rw [cf.algebraMap_snd]
          exact (e.toAlgHom.comp resR).commutes a)) }
  have hres : ∀ r : R,
      (cf.functor.obj A).residueEquiv (residue (cf.functor.obj A) (betaAlg r)) =
        R.residueEquiv (residue R r) := fun r => by
    rw [cf.residue_snd]
    exact congrArg (fun z => z.val.2) (hβ r)
  refine { hom := betaAlg, isLocal := ⟨fun r hr => ?_⟩, residue_comm := hres }
  have hβ : residue (cf.functor.obj A) (betaAlg r) ≠ 0 :=
    (IsLocalRing.residue_ne_zero_iff_isUnit _).2 hr
  have hRβ : R.residueEquiv (residue R r) ≠ 0 := fun h =>
    hβ ((cf.functor.obj A).residueEquiv.injective (by rw [hres, h]; simp))
  have hrne : residue R r ≠ 0 := fun hz => hRβ (by simp [hz])
  exact (IsLocalRing.residue_ne_zero_iff_isUnit _).1 hrne

section changeOfFieldsPoint

variable (S : ChangeOfFieldsSituation.{u, v, w})
  (R : CompleteLocalAlgCat.{u, max x v w, v} S.Λ S.k)
  (T : CompleteLocalAlgCat.{u, max x v w, w} S.Λ S.l) (fΛ : R →ₐ[S.Λ] T)
  (hresf : ∀ r : R, T.residueEquiv (residue T (fΛ r)) =
    algebraMap S.k S.l (R.residueEquiv (residue R r)))

/-- The first coordinate of `changeOfFieldsPoint` is `α ∘ fΛ`. -/
private theorem changeOfFieldsPoint_fst (A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l)
    (α : (restrictedCoyoneda T).obj A) (r : R) :
    (((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv A)
      ((changeOfFieldsPoint.{u, v, w, x} S R T fΛ hresf A α).hom r)).val.1 = α.hom (fΛ r) := by
  simp [changeOfFieldsPoint, RingEquiv.apply_symm_apply]

/-- The second coordinate of `changeOfFieldsPoint` is the residue map of `R`. -/
private theorem changeOfFieldsPoint_snd (A : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l)
    (α : (restrictedCoyoneda T).obj A) (r : R) :
    (((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv A)
      ((changeOfFieldsPoint.{u, v, w, x} S R T fΛ hresf A α).hom r)).val.2 =
        R.residueEquiv (residue R r) := by
  simp [changeOfFieldsPoint, RingEquiv.apply_symm_apply]
  rfl

/-- `changeOfFieldsPoint` is natural in the Artinian algebra. -/
private theorem changeOfFieldsPoint_natural
    {A C : ArtinianLocalAlgCat.{u, max x v w, w} S.Λ S.l} (g : A ⟶ C)
    (α : (restrictedCoyoneda T).obj A) :
    changeOfFieldsPoint.{u, v, w, x} S R T fΛ hresf C ((restrictedCoyoneda T).map g α) =
      (restrictedCoyoneda R).map ((comparisonFunctor.{u, v, w, max x v w} S).functor.map g)
        (changeOfFieldsPoint.{u, v, w, x} S R T fΛ hresf A α) := by
  let cf := comparisonFunctor.{u, v, w, max x v w} S
  let pointAt := changeOfFieldsPoint.{u, v, w, x} S R T fΛ hresf
  let reprT := restrictedCoyoneda T
  apply CompleteLocalAlgCat.Hom.ext
  refine pullback_algHom_ext.{u, v, w, x} S C (fun r => ?_) (fun r => ?_)
  · change ((cf.pullbackEquiv C) ((pointAt C (reprT.map g α)).hom r)).val.1 =
      ((cf.pullbackEquiv C) (((cf.functor.map g).hom.comp (pointAt A α).hom) r)).val.1
    rw [changeOfFieldsPoint_fst, AlgHom.comp_apply, cf.map_fst, changeOfFieldsPoint_fst,
      restrictedCoyoneda_map_hom g α]
    rfl
  · change ((cf.pullbackEquiv C) ((pointAt C (reprT.map g α)).hom r)).val.2 =
      ((cf.pullbackEquiv C) (((cf.functor.map g).hom.comp (pointAt A α).hom) r)).val.2
    rw [changeOfFieldsPoint_snd, AlgHom.comp_apply, cf.map_snd, changeOfFieldsPoint_snd]

end changeOfFieldsPoint

/-- **Stacks Project, Tag 0DQF, with the levels of the new formal object.** For a versal formal
object `ξ` of a category cofibered in groupoids over `𝒞_{Λ,k}`, there are a Noetherian complete
local `Λ`-algebra `T` with residue field `l`, a local `Λ`-algebra map `f : ξ.base → T` which is
formally smooth for the `𝔪_T`-adic topology and induces the extension `l/k` on residue fields, and
a versal formal object `ξ'` over `T` of the change-of-residue-field category `𝓕_{l/k}` which is
the pushforward of `ξ` along `f`: at every level `n` there is a morphism `g n : ξ_n ⟶ ξ'_n` of `𝓕`
(an object of `𝓕_{l/k}` over `B` being an object of `𝓕` over `B ×_l k`), compatible with the
transitions, lying over a map `R/𝔪^{n+1} → (T/𝔪^{n+1}) ×_l k` whose first coordinate is the
reduction of `f`. -/
public theorem exists_versal_formalObject_changeOfFields_pushforward
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v w, v} S.Λ S.k)
    (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p)
    (hξ : IsVersal hp ξ) :
    ∃ (T : CompleteLocalAlgCat.{u, max x v w, w} S.Λ S.l)
      (f : ξ.base →ₐ[S.Λ] T),
      IsLocalHom f.toRingHom ∧
        (∀ a : ξ.base,
          T.residueEquiv (residue T (f a)) =
            algebraMap S.k S.l (ξ.base.residueEquiv (residue ξ.base a))) ∧
        RingHom.FormallySmoothNAdic.{max x v w} f.toRingHom (maximalIdeal T) ∧
        ∃ (ξ' : FormalObject
            (changeOfFieldsProjection.{u, v, w, max x v w} S p)) (hT : ξ'.base = T),
          IsVersal (changeOfFieldsProjection_isCofiberedInGroupoids S p hp) ξ' ∧
          ∃ g : ∀ n, ξ.level n ⟶ (ξ'.level n).fst,
            (∀ n, g (n + 1) ≫ (ξ'.transition n).fst = ξ.transition n ≫ g n) ∧
            ∀ (n : ℕ) (r : ξ.base),
              ((comparisonFunctor.{u, v, w, max x v w} S).pullbackEquiv
                  ((AdicTruncation.functor n).obj T)
                ((eqToHom (ξ.level_eq n).symm ≫ p.map (g n) ≫ (ξ'.level n).iso.hom ≫
                    (comparisonFunctor.{u, v, w, max x v w} S).functor.map
                      (eqToHom ((ξ'.level_eq n).trans
                        (congrArg (AdicTruncation.functor n).obj hT)))).hom
                  (Ideal.Quotient.mk (AdicTruncation.ideal ξ.base n) r :
                    AdicTruncation.obj ξ.base n))).val.1 =
                (Ideal.Quotient.mk (AdicTruncation.ideal T n) (f r) :
                  AdicTruncation.obj T n) := by
  obtain ⟨T, fΛ, hfLocal, hresf, hfSmooth⟩ :=
    exists_formallySmooth_changeOfFields_lift.{u, v, w, x} S ξ.base
  let R := ξ.base
  let pushforwards := chosenPushforwardsOfCofibered p hp
  let ξMap := associatedMorphism hp ξ pushforwards
  let pointAt := changeOfFieldsPoint.{u, v, w, x} S R T fΛ hresf
  have pointAt_natural := @changeOfFieldsPoint_natural.{u, v, w, x} S R T fΛ hresf
  let pointToChanged := pointToChangedFunctor.{u, v, w, x} S R T pointAt pointAt_natural
  let p' := changeOfFieldsProjection.{u, v, w, max x v w} S p
  let hp' := changeOfFieldsProjection_isCofiberedInGroupoids.{u, v, w, max x v w, y, z} S p hp
  let changedMap := changeOfFieldsBasedFunctor.{u, v, w, max x v w} S ξMap.toBasedFunctor
  let newMap := BasedFunctor.comp pointToChanged changedMap
  have hNewMap : IsSmooth newMap := isSmooth_comp pointToChanged changedMap
    (isSmooth_pointToChangedFunctor.{u, v, w, x} S R T fΛ hfSmooth pointAt pointAt_natural
      (changeOfFieldsPoint_fst.{u, v, w, x} S R T fΛ hresf)
      (changeOfFieldsPoint_snd.{u, v, w, x} S R T fΛ hresf))
    (isSmooth_changeOfFields.{u, v, w, max x v w} S ξMap.toBasedFunctor (hξ pushforwards))
  let E := representableMorphismFormalObjectEquivalence p' hp' T
  let ξFiber := E.equivalence.functor.obj newMap
  exact ⟨T, fΛ, hfLocal, hresf, hfSmooth, ξFiber.1, ξFiber.2,
    isVersal_of_smooth_representable hp' E newMap hNewMap,
    pushforward_levels.{u, v, w, x} S p hp ξ T fΛ pointAt pointAt_natural
      (changeOfFieldsPoint_fst.{u, v, w, x} S R T fΛ hresf)⟩

/-- **Stacks Project, Tag 0DQF.** For a versal formal object `ξ` of a category cofibered in
groupoids over `𝒞_{Λ,k}`, there is a Noetherian complete local `Λ`-algebra with residue field
`l`, receiving a local `Λ`-algebra map from the base of `ξ` which is formally smooth for its
maximal-ideal-adic topology and induces the extension `l/k` on residue fields, and carrying a
versal formal object of the change-of-residue-field category. -/
@[stacks 0DQF]
public theorem exists_versal_formalObject_changeOfFields
    (S : ChangeOfFieldsSituation.{u, v, w})
    {F : Type y} [Category.{z} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max x v w, v} S.Λ S.k)
    (hp : IsCofiberedInGroupoids p)
    (ξ : FormalObject p)
    (hξ : IsVersal hp ξ) :
    ∃ (T : CompleteLocalAlgCat.{u, max x v w, w} S.Λ S.l)
      (f : ξ.base →ₐ[S.Λ] T),
      IsLocalHom f.toRingHom ∧
        (∀ a : ξ.base,
          T.residueEquiv (residue T (f a)) =
            algebraMap S.k S.l (ξ.base.residueEquiv (residue ξ.base a))) ∧
        RingHom.FormallySmoothNAdic.{max x v w} f.toRingHom (maximalIdeal T) ∧
        ∃ ξ' : FormalObject
            (changeOfFieldsProjection.{u, v, w, max x v w} S p),
          ξ'.base = T ∧
            IsVersal (changeOfFieldsProjection_isCofiberedInGroupoids S p hp) ξ' := by
  obtain ⟨T, f, hloc, hres, hsm, ξ', hT, hv, -⟩ :=
    exists_versal_formalObject_changeOfFields_pushforward.{u, v, w, x} S p hp ξ hξ
  exact ⟨T, f, hloc, hres, hsm, ξ', hT, hv⟩

end

end Deformation
