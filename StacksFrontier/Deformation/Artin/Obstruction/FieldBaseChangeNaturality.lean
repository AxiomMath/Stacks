module

public import StacksFrontier.Deformation.Artin.Obstruction.NaiveVersalityFieldClassEquation

/-!
# Naturality of the (RS*) comparison of lift classes in the coefficients

Condition (RS*) attaches to a commutative square of the base, one leg of which is a square-zero
immersion, a comparison of classes of lifts along the two remaining legs
(`Deformation.Artin.squareLiftClassesEquiv`). This file records that the comparison is natural,
first in the square and then in the coefficients of the trivial square-zero extensions the
square is built from.

The two statements are what the tangent half of Stacks 07YA needs beyond the comparison itself:
the transition on lift classes attached to a ring map and a semilinear map of coefficients is
compatible with a change of the coefficient modules. They are separated from the construction
of the comparison because nothing here is specific to a deformation situation — the first
statement is a fact about a category fibred in groupoids and two squares of its base sharing a
leg.

## Main results

* `Deformation.Artin.exists_isStronglyCartesian_squareLiftClassesEquiv_comm` — the comparison is
  natural in the square: two squares sharing their first leg, compared by arrows on the two
  remaining corners, carry a cartesian relation between classes of lifts to a cartesian relation
  between their images.
* `Deformation.Artin.squareZeroRingBaseMap_comm` — the two trivial square-zero extensions of a
  semilinear pair of coefficients commute with a map of the coefficient modules.
* `Deformation.Artin.squareZeroOverBaseMap_comp_squareZeroOverMap_comm` — the same statement for
  the morphisms of the site the ring maps are the spectra of.
* `Deformation.Artin.isPullbackOfSquareZeroLift_baseChangeLiftClassesEquiv` — the comparison of
  lift classes is natural in the coefficients.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

/-! ### Naturality of the (RS\*) comparison in the coefficients -/

section SquareLiftClassesWitness

open CategoryTheory.Functor CategoryTheory.Limits

variable {C : Type*} [Category C] {D : Type*} [Category D] (q : D ⥤ C)
  (c : q.ChoiceOfPullbacks) (hq : q.IsFiberedInGroupoids) {U V W Z : C}
  (α : U ⟶ V) (β : U ⟶ W) (γ : V ⟶ Z) (δ : W ⟶ Z) (hc : α ≫ γ = β ≫ δ)

/-- **The (RS\*) comparison on lift classes is natural in the square.** Let two commutative
squares share their first leg `α`, and let `m : Z' ⟶ Z`, `m' : W' ⟶ W` compare the two
remaining corners, compatibly with the two square-zero immersions (`hm`, `hm'`) and with the
two fourth maps (`hsq`). If a class of lifts of `y` along `γ'` is the pullback of a class of
lifts along `γ` by a cartesian arrow over `m`, then their images under the two comparisons are
related the same way by a cartesian arrow over `m'`.

The arrow is produced by the universal property of the cartesian arrow that
`Deformation.Artin.exists_isStronglyCartesian_squareLiftClassesEquiv_apply` attaches to the
unprimed comparison, applied to the composite of the primed one's arrow with the given one;
that composite lies over `δ' ≫ m = m' ≫ δ`, which is what `hsq` provides. It is cartesian
because every arrow of a category fibred in groupoids is, and it carries the structure arrow
of one lift to that of the other because the unprimed cartesian arrow cancels. -/
public theorem exists_isStronglyCartesian_squareLiftClassesEquiv_comm
    (hE : (fiberSquareComparison q c α β γ δ hc).IsEquivalence)
    {W' Z' : C} (β' : U ⟶ W') (γ' : V ⟶ Z') (δ' : W' ⟶ Z') (hc' : α ≫ γ' = β' ≫ δ')
    (hE' : (fiberSquareComparison q c α β' γ' δ' hc').IsEquivalence)
    (m : Z' ⟶ Z) (m' : W' ⟶ W) (hm' : β' ≫ m' = β) (hsq : δ' ≫ m = m' ≫ δ)
    (y : q.Fiber V) (a₀ : (Under.post q).Fiber (Under.mk (eqToHom y.2 ≫ γ)))
    (b₀ : (Under.post q).Fiber (Under.mk (eqToHom y.2 ≫ γ')))
    (χ : b₀.1.right ⟶ a₀.1.right) (hχ : q.IsStronglyCartesian m χ)
    (hχfac : b₀.1.hom ≫ χ = a₀.1.hom) :
    ∃ (a₁ : (Under.post q).Fiber (Under.mk (eqToHom ((c.pullbackFunctor α).obj y).2 ≫ β)))
      (b₁ : (Under.post q).Fiber (Under.mk (eqToHom ((c.pullbackFunctor α).obj y).2 ≫ β')))
      (χ' : b₁.1.right ⟶ a₁.1.right),
      squareLiftClassesEquiv q c α β γ δ hc hq hE y (Quotient.mk _ a₀) = Quotient.mk _ a₁ ∧
      squareLiftClassesEquiv q c α β' γ' δ' hc' hq hE' y (Quotient.mk _ b₀) =
        Quotient.mk _ b₁ ∧
      q.IsStronglyCartesian m' χ' ∧ b₁.1.hom ≫ χ' = a₁.1.hom := by
  obtain ⟨a₁, ρa, ha₁, hρa, hρafac⟩ :=
    exists_isStronglyCartesian_squareLiftClassesEquiv_apply q c hq α β γ δ hc hE y a₀
  obtain ⟨b₁, ρb, hb₁, hρb, hρbfac⟩ :=
    exists_isStronglyCartesian_squareLiftClassesEquiv_apply q c hq α β' γ' δ' hc' hE' y b₀
  have hcomp : q.IsHomLift (m' ≫ δ) (ρb ≫ χ) := by
    rw [← hsq]
    infer_instance
  obtain ⟨χ', hχ'H, hχ'fac⟩ :
      ∃ χ' : b₁.1.right ⟶ a₁.1.right, q.IsHomLift m' χ' ∧ χ' ≫ ρa = ρb ≫ χ :=
    ⟨IsStronglyCartesian.map q δ ρa (rfl : m' ≫ δ = m' ≫ δ) (ρb ≫ χ),
      IsStronglyCartesian.map_isHomLift q δ ρa (rfl : m' ≫ δ = m' ≫ δ) (ρb ≫ χ),
      IsStronglyCartesian.fac q δ ρa (rfl : m' ≫ δ = m' ≫ δ) (ρb ≫ χ)⟩
  have ha₁H : q.IsHomLift β a₁.1.hom :=
    isHomLift_fiberUnder_hom q β ((c.pullbackFunctor α).obj y) a₁
  have hb₁H : q.IsHomLift β' b₁.1.hom :=
    isHomLift_fiberUnder_hom q β' ((c.pullbackFunctor α).obj y) b₁
  have hlhsH₀ : q.IsHomLift (β' ≫ m') (b₁.1.hom ≫ χ') := inferInstance
  have hlhsH : q.IsHomLift β (b₁.1.hom ≫ χ') := hm' ▸ hlhsH₀
  refine ⟨a₁, b₁, χ', ha₁, hb₁, hq.isStronglyCartesian_homLift m' χ', ?_⟩
  refine IsStronglyCartesian.ext q δ ρa β ?_
  refine (Category.assoc _ _ _).trans ?_
  rw [hχ'fac]
  refine (Category.assoc _ _ _).symm.trans ?_
  rw [hρbfac]
  refine (Category.assoc _ _ _).trans ?_
  rw [hχfac]
  exact hρafac.symm

end SquareLiftClassesWitness

/-! ### The (RS\*) comparison on tangent modules, and its naturality -/

section BaseChangeNaturality

open CategoryTheory.Limits CategoryTheory.Functor

variable {A A' : Type u} [CommRing A] [CommRing A'] (f : A →+* A')
  (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (toS' : Spec (.of A') ⟶ S)
  (hA : B.Contains (Spec (.of A))) (hA' : B.Contains (Spec (.of A')))
  (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toS')
  (M M' : SiteModule A B) (N N' : SiteModule A' B)
  (ψ : (M.obj : Type u) →+ (N.obj : Type u))
  (hψ : ∀ (a : A) (m : M.obj), ψ (a • m) = f a • ψ m)
  (ψ' : (M'.obj : Type u) →+ (N'.obj : Type u))
  (hψ' : ∀ (a : A) (m : M'.obj), ψ' (a • m) = f a • ψ' m)
  (φ : M ⟶ M') (φ' : N ⟶ N')
  (hcompat : ∀ m : (M.obj : Type u), ψ' (φ.hom.hom m) = φ'.hom.hom (ψ m))

include hcompat in
/-- The two trivial square-zero extensions of a semilinear pair of coefficients commute with the
maps induced by a compatible pair of module maps: the ring maps `A[M] ⟶ A'[N']` obtained by
applying `φ` and then the base change at `ψ'`, and by the base change at `ψ` and then `φ'`,
agree. -/
public theorem squareZeroRingBaseMap_comm :
    (squareZeroRingBaseMap f ψ' hψ').comp (TrivSqZeroExt.map φ.hom.hom).toRingHom =
      ((TrivSqZeroExt.map φ'.hom.hom).toRingHom).comp (squareZeroRingBaseMap f ψ hψ) := by
  refine RingHom.ext fun z => TrivSqZeroExt.ext ?_ ?_
  · change f (TrivSqZeroExt.map φ.hom.hom z).fst =
      (TrivSqZeroExt.map φ'.hom.hom (squareZeroRingBaseMap f ψ hψ z)).fst
    rw [TrivSqZeroExt.fst_map, TrivSqZeroExt.fst_map]
    rfl
  · change ψ' (TrivSqZeroExt.map φ.hom.hom z).snd =
      (TrivSqZeroExt.map φ'.hom.hom (squareZeroRingBaseMap f ψ hψ z)).snd
    rw [TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map, hcompat]
    rfl

include hf hcompat in
/-- **The (RS\*) square is natural in the coefficients.** The morphism `Spec A'[N'] ⟶ Spec A[M]`
attached to a semilinear pair `(ψ', φ)` — base change at `ψ'`, then the map induced by `φ` — is
the one attached to `(φ', ψ)`. This is the commuting square of bases behind
`Deformation.Artin.isPullbackOfSquareZeroLift_baseChangeLiftClassesEquiv`. -/
public theorem squareZeroOverBaseMap_comp_squareZeroOverMap_comm :
    squareZeroOverBaseMap f B S hS toS toS' hf M' N' ψ' hψ' ≫
        squareZeroOverMap A B S hS toS φ =
      squareZeroOverMap A' B S hS toS' φ' ≫
        squareZeroOverBaseMap f B S hS toS toS' hf M N ψ hψ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap f ψ' hψ')) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map φ.hom.hom).toRingHom) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map φ'.hom.hom).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap f ψ hψ))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  exact CommRingCat.hom_ext (squareZeroRingBaseMap_comm f B M M' N N' ψ hψ ψ' hψ' φ φ' hcompat)

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp)
  (hbij : Function.Bijective ψ) (hbij' : Function.Bijective ψ')
  (x : X) (hx : p.obj x = algebraOver A B S hS toS hA)

include hf hcompat in
/-- **The (RS\*) comparison of lift classes is natural in the coefficients.** If a class of
lifts of `x` over `Spec A[M']` is the pullback of a class over `Spec A[M]` along the module map
`φ`, then the two classes that the Rim–Schlessinger identification attaches to them stand in
the same relation over `Spec A'[N] ⟶ Spec A'[N']` along `φ'`.

This is `Deformation.Artin.exists_isStronglyCartesian_squareLiftClassesEquiv_comm` at the two
squares `A[M] = A ×_{A'} A'[N]` and `A[M'] = A ×_{A'} A'[N']`, whose comparison arrows are the
two square-zero immersions and whose fourth maps commute by
`Deformation.Artin.squareZeroOverBaseMap_comp_squareZeroOverMap_comm`. -/
public theorem isPullbackOfSquareZeroLift_baseChangeLiftClassesEquiv
    {a : squareZeroLiftClasses A B S hS toS hA p x hx M}
    {b : squareZeroLiftClasses A B S hS toS hA p x hx M'}
    (hab : IsPullbackOfSquareZeroLift A B S hS toS hA p x hx φ a b) :
    letI : p.IsFibered := hp.isFibered
    IsPullbackOfSquareZeroLift A' B S hS toS' hA' p
      (((Functor.chosenPullbacks p).pullbackFunctor
        (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩).1
      (((Functor.chosenPullbacks p).pullbackFunctor
        (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)).obj ⟨x, hx⟩).2 φ'
      (baseChangeLiftClassesEquiv f B S hS toS toS' hA hA' hf M N ψ hψ p hp hRS hbij x hx a)
      (baseChangeLiftClassesEquiv f B S hS toS toS' hA hA' hf M' N' ψ' hψ' p hp hRS hbij' x hx
        b) := by
  let : p.IsFibered := hp.isFibered
  obtain ⟨a₀, b₀, ha₀, hb₀, χ, hχ, hχfac⟩ := hab
  obtain ⟨a₁, b₁, χ', ha₁, hb₁, hχ', hχ'fac⟩ :=
    exists_isStronglyCartesian_squareLiftClassesEquiv_comm p (Functor.chosenPullbacks p) hp
      (algebraOverMapOfRingHom f B S hS toS toS' hA hA' hf)
      (squareZeroArrow A' B S hS toS' hA' N) (squareZeroArrow A B S hS toS hA M)
      (squareZeroOverBaseMap f B S hS toS toS' hf M N ψ hψ)
      (algebraOverMap_comp_squareZeroArrow f B S hS toS toS' hA hA' hf M N ψ hψ)
      (baseChangeSquare_isEquivalence f B S hS toS toS' hA hA' hf M N ψ hψ p hp hRS hbij)
      (squareZeroArrow A' B S hS toS' hA' N') (squareZeroArrow A B S hS toS hA M')
      (squareZeroOverBaseMap f B S hS toS toS' hf M' N' ψ' hψ')
      (algebraOverMap_comp_squareZeroArrow f B S hS toS toS' hA hA' hf M' N' ψ' hψ')
      (baseChangeSquare_isEquivalence f B S hS toS toS' hA hA' hf M' N' ψ' hψ' p hp hRS hbij')
      (squareZeroOverMap A B S hS toS φ) (squareZeroOverMap A' B S hS toS' φ')
      (squareZeroArrow_naturality A' B S hS toS' hA' φ')
      (squareZeroOverBaseMap_comp_squareZeroOverMap_comm f B S hS toS toS' hf M M' N N' ψ hψ ψ'
        hψ' φ φ' hcompat)
      ⟨x, hx⟩ a₀ b₀ χ hχ hχfac
  refine ⟨a₁, b₁, ?_, ?_, χ', hχ', hχ'fac⟩
  · rw [← ha₀]
    exact ha₁.symm
  · rw [← hb₀]
    exact hb₁.symm

end BaseChangeNaturality

end Deformation.Artin

end
