module

public import Mathlib.AlgebraicGeometry.Artinian
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.ArtinianLocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import StacksFrontier.AlgebraicGeometry.Pushout.SchemePushout
public import StacksFrontier.AlgebraicGeometry.Pushout.ThickeningPushout
public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothScheme
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonPaste
public import StacksFrontier.CategoryTheory.TwoFibreProduct.SquareComparisonTransfer
public import StacksFrontier.Deformation.Artin.RimSchlessinger.ConditionRS
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FiberSquareComparison
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong
public import StacksFrontier.Deformation.ArtinCriteria.Predeformation
public import StacksFrontier.Deformation.BaseCategory.FibreProduct
public import StacksFrontier.Deformation.RimSchlessinger.Basic
public import StacksFrontier.Deformation.RimSchlessingerCategory.SmallExtensionCriterion

/-!
# Condition (RS*) implies condition (RS)

## Main results

* `Deformation.Artin.satisfiesRS_of_satisfiesRSStar` — condition (RS*) implies condition
  (RS). This is observation (4) of the remarks following the source's Definition 98.18.1, in
  the section [Stacks Project, Tag 0CXN], and is registered under that section's tag.

## Implementation notes

The implication from (RS*) to (RS) is not a special case: (RS) quantifies over an arbitrary
closed immersion, whereas (RS*) only over a surjection with square-zero kernel. The source's
one-line justification is completed here as follows. All four corners are affine with local
Artinian rings of global functions, so the closed immersion is a surjection whose kernel `I`
is a proper ideal of an Artinian local ring and hence nilpotent; the pushout square has the
ring of global functions of its fourth corner identified with the fibre product of the other
three, by Stacks 0ET0 transported along `AlgebraicGeometry.Scheme.isoSpec`. Writing `I ^ n`
for the first vanishing power, the surjection is cut at `I ^ (n - 1)`, whose square vanishes;
the two intermediate corners are the spectra of the resulting quotient and of the induced
fibre product, placed on the site because a closed immersion does not increase the size of a
scheme. Condition (RS*) covers the square-zero step, induction on `n` the rest, and the two
squares of fibres are pasted by Stacks 02XB (3) and 02XD. The quantification over the four
rings is carried through isomorphisms of the rings of global functions, since the
intermediate corners are spectra and their global functions are only canonically isomorphic
to the rings they were built from.

## References

* [Stacks Project, Tag 0CXN](https://stacks.math.columbia.edu/tag/0CXN)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u u₁ u₂ u₃ v₁

namespace Deformation.Artin

open IsLocalRing

attribute [local implicit_reducible] Functor.Fiber Functor.Fiber.fiberInclusion

attribute [local implicit_reducible] Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoricalPullback.CatCommSqOver.toFunctorToCategoricalPullback
  CategoricalPullback.π₁ CategoricalPullback.π₂

universe v w

/-! ### Condition (RS*) implies condition (RS) -/

/-- The quotient of `RW` by the `n`-th power of the kernel of `γ` factors `γ` as a
square-zero surjection followed by a surjection whose kernel has `n`-th power zero. -/
private lemma exists_quotientStep {RU RW : CommRingCat.{u}} (γ : RW ⟶ RU)
    (hsurj : Function.Surjective γ.hom) {n : ℕ} (hn : 1 ≤ n)
    (hker : RingHom.ker γ.hom ^ (n + 1) = ⊥) :
    ∃ (RW₁ : CommRingCat.{u}) (π : RW ⟶ RW₁) (γ₁ : RW₁ ⟶ RU),
      π ≫ γ₁ = γ ∧ Function.Surjective π.hom ∧ RingHom.ker π.hom ^ 2 = ⊥ ∧
      Function.Surjective γ₁.hom ∧ RingHom.ker γ₁.hom ^ n = ⊥ := by
  have hn0 : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have hle : RingHom.ker γ.hom ^ n ≤ RingHom.ker γ.hom := Ideal.pow_le_self hn0
  have hle' : ∀ a : RW, a ∈ RingHom.ker γ.hom ^ n → γ.hom a = 0 :=
    fun a ha => RingHom.mem_ker.mp (hle ha)
  refine ⟨CommRingCat.of (RW ⧸ RingHom.ker γ.hom ^ n),
    CommRingCat.ofHom (Ideal.Quotient.mk (RingHom.ker γ.hom ^ n)),
    CommRingCat.ofHom (Ideal.Quotient.lift (RingHom.ker γ.hom ^ n) γ.hom hle'),
    CommRingCat.hom_ext (Ideal.Quotient.lift_comp_mk _ _ _),
    Ideal.Quotient.mk_surjective, ?_,
    Ideal.Quotient.lift_surjective_of_surjective _ hle' hsurj, ?_⟩
  · have h1 : RingHom.ker (Ideal.Quotient.mk (RingHom.ker γ.hom ^ n)) =
        RingHom.ker γ.hom ^ n := Ideal.mk_ker
    simp only [CommRingCat.hom_ofHom, h1, ← pow_mul]
    exact le_antisymm (le_trans (Ideal.pow_le_pow_right (by omega)) hker.le) bot_le
  · simp only [CommRingCat.hom_ofHom]
    rw [Ideal.ker_quotient_lift γ.hom hle, ← Ideal.map_pow, Ideal.map_quotient_self]

/-- Base-changing a fibre-product square along a factorisation of its lower-right leg. -/
private lemma exists_pullbackStep {RU RV RW RW₁ RZ : CommRingCat.{u}}
    (φ : RV ⟶ RU) (γ : RW ⟶ RU) (ψ : RZ ⟶ RV) (χ : RZ ⟶ RW)
    (π : RW ⟶ RW₁) (γ₁ : RW₁ ⟶ RU) (hπγ : π ≫ γ₁ = γ)
    (hπ : Function.Surjective π.hom) (hpb : IsPullback ψ χ φ γ) :
    ∃ (RZ₁ : CommRingCat.{u}) (τ : RZ ⟶ RZ₁) (ψ₁ : RZ₁ ⟶ RV) (χ₁ : RZ₁ ⟶ RW₁),
      τ ≫ ψ₁ = ψ ∧ τ ≫ χ₁ = χ ≫ π ∧ IsPullback ψ₁ χ₁ φ γ₁ ∧ IsPullback τ χ χ₁ π ∧
      Function.Surjective τ.hom := by
  have t : IsPullback (CommRingCat.ofHom (φ.hom.pullbackFst γ₁.hom))
      (CommRingCat.ofHom (φ.hom.pullbackSnd γ₁.hom)) φ γ₁ := by
    simpa using Stacks.Pushout.isPullback_ofHom_pullback φ.hom γ₁.hom
  have s : IsPullback ψ χ φ (π ≫ γ₁) := by rwa [hπγ]
  have hw : ψ ≫ φ = (χ ≫ π) ≫ γ₁ := by rw [Category.assoc, hπγ, hpb.w]
  refine ⟨CommRingCat.of (RingHom.pullback φ.hom γ₁.hom), t.lift ψ (χ ≫ π) hw,
    CommRingCat.ofHom (φ.hom.pullbackFst γ₁.hom),
    CommRingCat.ofHom (φ.hom.pullbackSnd γ₁.hom),
    t.lift_fst _ _ _, t.lift_snd _ _ _, t, IsPullback.of_right' s t, ?_⟩
  -- surjectivity of the induced map onto the concrete fibre product
  have hcomp : ∀ y : RW, γ₁.hom (π.hom y) = γ.hom y :=
    fun y => congrArg (fun k : RW ⟶ RU => k.hom y) hπγ
  intro x
  obtain ⟨b, hb⟩ := hπ x.1.2
  have hmem : φ.hom x.1.1 = γ₁.hom x.1.2 :=
    (Stacks.Pushout.mem_pullback_iff φ.hom γ₁.hom x.1.1 x.1.2).mp x.2
  have hx : φ.hom x.1.1 = γ.hom b := by rw [hmem, ← hb, hcomp]
  obtain ⟨z, hz1, hz2⟩ :=
    Types.exists_of_isPullback (hpb.map (forget CommRingCat)) x.1.1 b hx
  refine ⟨z, ?_⟩
  have e1 := congrArg (fun k : RZ ⟶ RV => k.hom z) (t.lift_fst ψ (χ ≫ π) hw)
  have e2 := congrArg (fun k : RZ ⟶ RW₁ => k.hom z) (t.lift_snd ψ (χ ≫ π) hw)
  apply Subtype.ext
  apply Prod.ext
  · exact e1.trans hz1
  · refine e2.trans ?_
    have hzb : χ.hom z = b := hz2
    change π.hom (χ.hom z) = (x : RV × RW₁).2
    rw [hzb]
    exact hb

/-- **Factoring a surjection of a ring fibre-product square through a square-zero step.** -/
private theorem exists_squareZeroFactorization {RU RV RW RZ : CommRingCat.{u}}
    (φ : RV ⟶ RU) (γ : RW ⟶ RU) (ψ : RZ ⟶ RV) (χ : RZ ⟶ RW)
    (hpb : IsPullback ψ χ φ γ) (hsurj : Function.Surjective γ.hom)
    {n : ℕ} (hn : 1 ≤ n) (hker : RingHom.ker γ.hom ^ (n + 1) = ⊥) :
    ∃ (RW₁ RZ₁ : CommRingCat.{u}) (π : RW ⟶ RW₁) (γ₁ : RW₁ ⟶ RU)
      (τ : RZ ⟶ RZ₁) (ψ₁ : RZ₁ ⟶ RV) (χ₁ : RZ₁ ⟶ RW₁),
      π ≫ γ₁ = γ ∧ τ ≫ ψ₁ = ψ ∧ τ ≫ χ₁ = χ ≫ π ∧
      IsPullback ψ₁ χ₁ φ γ₁ ∧ IsPullback τ χ χ₁ π ∧
      Function.Surjective π.hom ∧ RingHom.ker π.hom ^ 2 = ⊥ ∧
      Function.Surjective γ₁.hom ∧ RingHom.ker γ₁.hom ^ n = ⊥ ∧
      Function.Surjective τ.hom := by
  obtain ⟨RW₁, π, γ₁, hπγ, hπsurj, hπsq, hγ₁surj, hγ₁ker⟩ :=
    exists_quotientStep γ hsurj hn hker
  obtain ⟨RZ₁, τ, ψ₁, χ₁, hτψ, hτχ, hpb₁, hpb₂, hτsurj⟩ :=
    exists_pullbackStep φ γ ψ χ π γ₁ hπγ hπsurj hpb
  exact ⟨RW₁, RZ₁, π, γ₁, τ, ψ₁, χ₁, hπγ, hτψ, hτχ, hpb₁, hpb₂, hπsurj, hπsq,
    hγ₁surj, hγ₁ker, hτsurj⟩

/-! ### Transport of the three ring-theoretic hypotheses along isomorphisms -/

section Transport

variable {A B A' B' : CommRingCat.{u}} (α : A ⟶ B) (β : A' ⟶ B')
  (eA : A ≅ A') (eB : B ≅ B')

/-- The kernel of a map read through isomorphisms of its source and target. -/
private theorem ker_eq_comap_of_sq (h : α ≫ eB.hom = eA.hom ≫ β) :
    RingHom.ker α.hom = Ideal.comap eA.hom.hom (RingHom.ker β.hom) := by
  have hα : α = eA.hom ≫ β ≫ eB.inv := by
    rw [← Category.assoc, ← h, Category.assoc, eB.hom_inv_id, Category.comp_id]
  subst hα
  ext x
  simp only [RingHom.mem_ker, Ideal.mem_comap, CommRingCat.hom_comp, RingHom.coe_comp,
    Function.comp_apply]
  constructor
  · intro hx
    have : (eB.inv.hom (β.hom (eA.hom.hom x))) = eB.inv.hom 0 := by
      simpa only [map_zero] using hx
    exact (ConcreteCategory.bijective_of_isIso eB.inv).1 this
  · intro hx
    simp only [hx, map_zero]

private theorem surjective_of_sq (h : α ≫ eB.hom = eA.hom ≫ β)
    (hβ : Function.Surjective β.hom) : Function.Surjective α.hom := by
  have hα : α = eA.hom ≫ β ≫ eB.inv := by
    rw [← Category.assoc, ← h, Category.assoc, eB.hom_inv_id, Category.comp_id]
  subst hα
  exact ((ConcreteCategory.bijective_of_isIso eB.inv).2.comp hβ).comp
    (ConcreteCategory.bijective_of_isIso eA.hom).2

private theorem ker_pow_eq_bot_of_sq (h : α ≫ eB.hom = eA.hom ≫ β) {n : ℕ}
    (hβ : RingHom.ker β.hom ^ n = ⊥) : RingHom.ker α.hom ^ n = ⊥ :=
  le_bot_iff.mp (ker_eq_comap_of_sq α β eA eB h ▸ (Ideal.le_comap_pow _ n).trans
    (hβ ▸ (Ideal.comap_bot_of_injective _
      (ConcreteCategory.bijective_of_isIso eA.hom).1).le))

end Transport

/-! ### Affine objects of the site cut out by a surjection of rings -/

section Surj

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- An affine object of the big fppf site over `S` has its ring of global functions
contained in the site. -/
private theorem contains_spec_gamma (W : BigAffineFppf B S hS) :
    B.Contains (Spec Γ((BigAffineFppf.toScheme B S hS).obj W, ⊤)) :=
  lt_of_eq_of_lt
    (Scheme.size_congr ((BigAffineFppf.toScheme B S hS).obj W).isoSpec).symm
    W.obj.left.property

private theorem contains_spec_of_iso (W : BigAffineFppf B S hS) {R : CommRingCat.{u}}
    (e : Γ((BigAffineFppf.toScheme B S hS).obj W, ⊤) ≅ R) : B.Contains (Spec R) :=
  lt_of_eq_of_lt (Scheme.size_congr (asIso (Spec.map e.hom)))
    (contains_spec_gamma W)

private theorem contains_spec_of_surjective (W : BigAffineFppf B S hS) {R R' : CommRingCat.{u}}
    (e : Γ((BigAffineFppf.toScheme B S hS).obj W, ⊤) ≅ R) (t : R ⟶ R')
    (ht : Function.Surjective t.hom) : B.Contains (Spec R') :=
  have : IsClosedImmersion (Spec.map t) := IsClosedImmersion.spec_of_surjective t ht
  Scheme.size_lt_of_isClosedImmersion (Spec.map t) (contains_spec_of_iso W e)

variable (W : BigAffineFppf B S hS) {R R' : CommRingCat.{u}}
  (e : Γ((BigAffineFppf.toScheme B S hS).obj W, ⊤) ≅ R) (t : R ⟶ R')

/-- The morphism of schemes `Spec R' ⟶ W` attached to a map `t : R ⟶ R'` and an
identification of `R` with the ring of global functions of `W`. -/
private abbrev surjSchemeHom : Spec R' ⟶ (BigAffineFppf.toScheme B S hS).obj W :=
  Spec.map t ≫ Spec.map e.hom ≫ ((BigAffineFppf.toScheme B S hS).obj W).isoSpec.inv

variable (ht : Function.Surjective t.hom)

/-- `Spec R'` as an object of the big affine fppf site over `S`. -/
private def surjObj : BigAffineFppf B S hS :=
  ⟨siteObject B S hS (contains_spec_of_surjective W e t ht)
      (surjSchemeHom W e t ≫ B.inclusion.map W.obj.hom),
    inferInstanceAs (IsAffine (Spec _))⟩

private theorem toScheme_obj_surjObj :
    (BigAffineFppf.toScheme B S hS).obj (surjObj W e t ht) = Spec R' := rfl

/-- The closed immersion of the cut-out object into `W`. -/
private def surjHom : surjObj W e t ht ⟶ W :=
  ObjectProperty.homMk
    (Over.homMk (ObjectProperty.homMk (surjSchemeHom W e t))
      (ObjectProperty.hom_ext _
        (Category.assoc (Spec.map t)
          (Spec.map e.hom ≫ ((BigAffineFppf.toScheme B S hS).obj W).isoSpec.inv)
          (B.inclusion.map W.obj.hom))))

private theorem toScheme_map_surjHom :
    (BigAffineFppf.toScheme B S hS).map (surjHom W e t ht) = surjSchemeHom W e t := rfl

/-- The ring of global functions of the cut-out object, identified with `R'`. -/
private def surjIso :
    Γ((BigAffineFppf.toScheme B S hS).obj (surjObj W e t ht), ⊤) ≅ R' :=
  Scheme.ΓSpecIso R'

/-- The canonical identification of the global functions of an affine object with the
sections of its spectrum cancels against the structural isomorphism. -/
private theorem isoSpec_inv_appTop_gamma (W : BigAffineFppf B S hS) :
    (((BigAffineFppf.toScheme B S hS).obj W).isoSpec.inv).appTop ≫
      (Scheme.ΓSpecIso Γ((BigAffineFppf.toScheme B S hS).obj W, ⊤)).hom = 𝟙 _ := by
  rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
  simp [Scheme.isoSpec]

/-- The closed immersion of the cut-out object into `W` induces `t` on global functions. -/
private theorem appTop_surjHom :
    ((BigAffineFppf.toScheme B S hS).map (surjHom W e t ht)).appTop ≫
        (surjIso W e t ht).hom = e.hom ≫ t := by
  change (surjSchemeHom W e t).appTop ≫ (Scheme.ΓSpecIso R').hom = _
  rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop, Category.assoc, Category.assoc,
    Scheme.ΓSpecIso_naturality, ← Category.assoc ((Spec.map e.hom).appTop),
    Scheme.ΓSpecIso_naturality, Category.assoc, ← Category.assoc,
    isoSpec_inv_appTop_gamma, Category.id_comp]

end Surj

/-! ### The square that (RS*) quantifies over, presented through isomorphisms -/

section Apply

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type u₁} [Category.{v₁} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} [p.IsFibered]

/-- Abbreviation for the comparison functor of a square of the big affine site. -/
private abbrev affineSquareComparison {U V W Z : BigAffineFppf B S hS}
    (p : 𝒳 ⥤ BigFppfOver B S hS) [p.IsFibered]
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) :
    p.Fiber ((BigAffineFppf.inclusion B S hS).obj Z) ⥤
      CategoricalPullback
        ((Functor.chosenPullbacks p).pullbackFunctor
          ((BigAffineFppf.inclusion B S hS).map f))
        ((Functor.chosenPullbacks p).pullbackFunctor
          ((BigAffineFppf.inclusion B S hS).map g)) :=
  fiberSquareComparison p p.chosenPullbacks
    ((BigAffineFppf.inclusion B S hS).map f) ((BigAffineFppf.inclusion B S hS).map g)
    ((BigAffineFppf.inclusion B S hS).map i) ((BigAffineFppf.inclusion B S hS).map j)
    (by simpa only [Functor.map_comp] using
      congrArg (BigAffineFppf.inclusion B S hS).map h)

/-- **Condition (RS\*) read through isomorphisms of the four rings of global functions.** -/
private theorem affineSquareComparison_isEquivalence_of_sq_zero
    {hp : p.IsFiberedInGroupoids} (hRS : SatisfiesRSStar B S hS p hp)
    {U V W Z : BigAffineFppf B S hS}
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
    {RU RV RW RZ : CommRingCat.{u}}
    (eU : Γ((BigAffineFppf.toScheme B S hS).obj U, ⊤) ≅ RU)
    (eV : Γ((BigAffineFppf.toScheme B S hS).obj V, ⊤) ≅ RV)
    (eW : Γ((BigAffineFppf.toScheme B S hS).obj W, ⊤) ≅ RW)
    (eZ : Γ((BigAffineFppf.toScheme B S hS).obj Z, ⊤) ≅ RZ)
    {φ : RV ⟶ RU} {γ : RW ⟶ RU} {ψ : RZ ⟶ RV} {χ : RZ ⟶ RW}
    (hf : ((BigAffineFppf.toScheme B S hS).map f).appTop ≫ eU.hom = eV.hom ≫ φ)
    (hg : ((BigAffineFppf.toScheme B S hS).map g).appTop ≫ eU.hom = eW.hom ≫ γ)
    (hi : ((BigAffineFppf.toScheme B S hS).map i).appTop ≫ eV.hom = eZ.hom ≫ ψ)
    (hj : ((BigAffineFppf.toScheme B S hS).map j).appTop ≫ eW.hom = eZ.hom ≫ χ)
    (hpb : IsPullback ψ χ φ γ) (hsurj : Function.Surjective γ.hom)
    (hker : RingHom.ker γ.hom ^ 2 = ⊥) :
    (affineSquareComparison p f g i j h).IsEquivalence :=
  hRS U V W Z f g i j h
    (hpb.of_iso' eZ eV eW eU hi.symm hj.symm hf.symm hg.symm)
    (surjective_of_sq _ γ eW eU hg hsurj)
    (ker_pow_eq_bot_of_sq _ γ eW eU hg hker)

end Apply

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A surjection whose kernel lies in the kernel of a second map factors that map.** -/
private theorem exists_factor_of_surjective {R R' T : CommRingCat.{u}} (t : R ⟶ R')
    (ht : Function.Surjective t.hom) (ρ : R ⟶ T)
    (hle : RingHom.ker t.hom ≤ RingHom.ker ρ.hom) :
    ∃ ρ' : R' ⟶ T, t ≫ ρ' = ρ := by
  have hle' : ∀ a ∈ RingHom.ker t.hom, ρ.hom a = 0 := fun a ha => RingHom.mem_ker.mp (hle ha)
  refine ⟨CommRingCat.ofHom
    ((Ideal.Quotient.lift (RingHom.ker t.hom) ρ.hom hle').comp
      (RingHom.quotientKerEquivOfSurjective ht).symm.toRingHom), ?_⟩
  ext x
  change (Ideal.Quotient.lift (RingHom.ker t.hom) ρ.hom hle')
      ((RingHom.quotientKerEquivOfSurjective ht).symm (t.hom x)) = ρ.hom x
  have hx : (RingHom.quotientKerEquivOfSurjective ht).symm (t.hom x) =
      Ideal.Quotient.mk (RingHom.ker t.hom) x :=
    (RingHom.quotientKerEquivOfSurjective ht).symm_apply_eq.mpr
      (RingHom.kerLift_mk t.hom x).symm
  rw [hx, Ideal.Quotient.lift_mk]

/-- **A morphism of the site into `W` whose kernel on global functions swallows the kernel of
`t` factors through the object cut out by `t`.** -/
private theorem exists_hom_surjObj {V W : BigAffineFppf B S hS} (m : V ⟶ W)
    {R R' : CommRingCat.{u}} (e : Γ((BigAffineFppf.toScheme B S hS).obj W, ⊤) ≅ R)
    (t : R ⟶ R') (ht : Function.Surjective t.hom)
    (hle : RingHom.ker t.hom ≤
      RingHom.ker (e.inv ≫ ((BigAffineFppf.toScheme B S hS).map m).appTop).hom) :
    ∃ m' : V ⟶ surjObj W e t ht, m' ≫ surjHom W e t ht = m := by
  obtain ⟨ρ', hρ'⟩ := exists_factor_of_surjective t ht
    (e.inv ≫ ((BigAffineFppf.toScheme B S hS).map m).appTop) hle
  set g : (BigAffineFppf.toScheme B S hS).obj V ⟶ Spec R' :=
    ((BigAffineFppf.toScheme B S hS).obj V).toSpecΓ ≫ Spec.map ρ' with hg
  have hring : e.hom ≫ t ≫ ρ' = ((BigAffineFppf.toScheme B S hS).map m).appTop := by
    rw [hρ', ← Category.assoc, e.hom_inv_id, Category.id_comp]
  have hiso : ((BigAffineFppf.toScheme B S hS).obj W).toSpecΓ ≫
      ((BigAffineFppf.toScheme B S hS).obj W).isoSpec.inv = 𝟙 _ := by
    change ((BigAffineFppf.toScheme B S hS).obj W).isoSpec.hom ≫ _ = _
    rw [Iso.hom_inv_id]
  have hg2 : g ≫ surjSchemeHom W e t = (BigAffineFppf.toScheme B S hS).map m := by
    rw [hg]
    change _ ≫ Spec.map t ≫ Spec.map e.hom ≫ _ = _
    rw [Category.assoc, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, hring,
      ← Category.assoc, ← Scheme.toSpecΓ_naturality, Category.assoc, hiso,
      Category.comp_id]
  have hw : (BigAffineFppf.toScheme B S hS).map m ≫ B.inclusion.map W.obj.hom =
      B.inclusion.map V.obj.hom := by
    change B.inclusion.map m.hom.left ≫ B.inclusion.map W.obj.hom = _
    rw [← Functor.map_comp, Over.w]
  refine ⟨ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk g) ?_), ?_⟩
  · apply ObjectProperty.hom_ext
    change g ≫ surjSchemeHom W e t ≫ B.inclusion.map W.obj.hom = B.inclusion.map V.obj.hom
    rw [← Category.assoc, hg2]
    exact hw
  · apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply ObjectProperty.hom_ext
    exact hg2

/-! ### Nilpotence of the kernel of a surjection out of an Artinian local ring -/

/-- **The kernel of a surjection from an Artinian local ring onto a nonzero ring is
nilpotent.** The kernel is a proper ideal, hence contained in the maximal ideal, and the
maximal ideal of an Artinian local ring is nilpotent. -/
private theorem exists_ker_pow_eq_bot {R T : CommRingCat.{u}} [IsLocalRing R] [IsArtinianRing R]
    [Nontrivial T] (γ : R ⟶ T) (hγ : Function.Surjective γ.hom) :
    ∃ n : ℕ, 1 ≤ n ∧ RingHom.ker γ.hom ^ n = ⊥ := by
  obtain ⟨m, hm⟩ := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  have hne : RingHom.ker γ.hom ≠ ⊤ := fun htop => one_ne_zero <| by
    obtain ⟨x, hx⟩ := hγ 1
    rw [← hx]
    exact RingHom.mem_ker.mp (htop ▸ Submodule.mem_top)
  refine ⟨m + 1, Nat.le_add_left 1 m, le_bot_iff.mp ?_⟩
  calc RingHom.ker γ.hom ^ (m + 1) ≤ IsLocalRing.maximalIdeal R ^ (m + 1) :=
        Ideal.pow_right_mono (IsLocalRing.le_maximalIdeal hne) _
    _ ≤ IsLocalRing.maximalIdeal R ^ m := Ideal.pow_le_pow_right (Nat.le_succ m)
    _ ≤ ⊥ := by
        rw [← IsLocalRing.jacobson_eq_maximalIdeal (⊥ : Ideal R) bot_ne_top, hm]
        exact le_of_eq Ideal.zero_eq_bot


/-! ### Cancellation lemmas -/

/-- A surjective morphism of `CommRingCat` is an epimorphism. -/
private theorem cancel_surjective {R R' T : CommRingCat.{u}} {t : R ⟶ R'}
    (ht : Function.Surjective t.hom) {a b : R' ⟶ T} (h : t ≫ a = t ≫ b) : a = b := by
  ext x
  obtain ⟨y, hy⟩ := ht x
  have := ConcreteCategory.congr_hom h y
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply, hy] using this

/-- `AlgebraicGeometry.BigAffineFppf.toScheme` is faithful. -/
private theorem toScheme_map_injective {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U V : BigAffineFppf B S hS} {a b : U ⟶ V}
    (h : (BigAffineFppf.toScheme B S hS).map a = (BigAffineFppf.toScheme B S hS).map b) :
    a = b := by
  apply ObjectProperty.hom_ext
  apply Over.OverMorphism.ext
  exact ObjectProperty.hom_ext _ h

/-- A morphism of the big affine site whose underlying morphism of schemes is a
monomorphism can be cancelled. -/
private theorem cancel_mono_site {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U V W : BigAffineFppf B S hS} {m : V ⟶ W}
    (hm : Mono ((BigAffineFppf.toScheme B S hS).map m)) {a b : U ⟶ V}
    (h : a ≫ m = b ≫ m) : a = b := by
  refine toScheme_map_injective (hm.right_cancellation _ _ ?_)
  simpa only [Functor.map_comp] using congrArg (BigAffineFppf.toScheme B S hS).map h


/-- A map whose composite with another is `c` has kernel inside the kernel of `c`. -/
private theorem ker_le_ker_of_comp_eq {A B C : CommRingCat.{u}} {a : A ⟶ B} {b : B ⟶ C} {c : A ⟶ C}
    (h : a ≫ b = c) : RingHom.ker a.hom ≤ RingHom.ker c.hom := by
  intro x hx
  have := ConcreteCategory.congr_hom h x
  rw [RingHom.mem_ker, ← this]
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    RingHom.mem_ker.mp hx, map_zero]

/-- Postcomposing with an isomorphism does not change a kernel. -/
private theorem ker_comp_iso {A B B' : CommRingCat.{u}} (a : A ⟶ B) (e : B ≅ B') :
    RingHom.ker (a ≫ e.hom).hom = RingHom.ker a.hom := by
  ext x
  simp only [RingHom.mem_ker, CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply]
  constructor
  · intro hx
    have : e.hom.hom (a.hom x) = e.hom.hom 0 := by simpa only [map_zero] using hx
    exact (ConcreteCategory.bijective_of_isIso e.hom).1 this
  · intro hx
    simp only [hx, map_zero]

/-- A map induced on global functions by `a` is determined by cancelling the surjective
map induced by `b` in the composite `a ≫ b`. -/
private theorem appTop_eq_of_comp_surjective {X Y Z : BigAffineFppf B S hS} (a : X ⟶ Y)
    (b : Y ⟶ Z) {RX RY RZ : CommRingCat.{u}} {s : RZ ⟶ RY} {r : RY ⟶ RX}
    (eX : Γ((BigAffineFppf.toScheme B S hS).obj X, ⊤) ≅ RX)
    (eY : Γ((BigAffineFppf.toScheme B S hS).obj Y, ⊤) ≅ RY)
    (eZ : Γ((BigAffineFppf.toScheme B S hS).obj Z, ⊤) ≅ RZ)
    (hb : ((BigAffineFppf.toScheme B S hS).map b).appTop ≫ eY.hom = eZ.hom ≫ s)
    (hbs : Function.Surjective ((BigAffineFppf.toScheme B S hS).map b).appTop.hom)
    (hab : ((BigAffineFppf.toScheme B S hS).map (a ≫ b)).appTop ≫ eX.hom = eZ.hom ≫ s ≫ r) :
    ((BigAffineFppf.toScheme B S hS).map a).appTop ≫ eX.hom = eY.hom ≫ r := by
  refine cancel_surjective hbs ?_
  calc ((BigAffineFppf.toScheme B S hS).map b).appTop ≫
        ((BigAffineFppf.toScheme B S hS).map a).appTop ≫ eX.hom
      = ((BigAffineFppf.toScheme B S hS).map (a ≫ b)).appTop ≫ eX.hom := by
        rw [Functor.map_comp, Scheme.Hom.comp_appTop, Category.assoc]
    _ = eZ.hom ≫ s ≫ r := hab
    _ = ((BigAffineFppf.toScheme B S hS).map b).appTop ≫ eY.hom ≫ r := by
        rw [← Category.assoc, ← hb, Category.assoc]

/-- The kernel of a surjection, whose composite with `q` is `ρ`, lies in the kernel of the
map `a` read through an isomorphism `e` of its source. -/
private theorem ker_le_ker_inv_comp {G G' R R' U : CommRingCat.{u}} {t : R ⟶ R'} {q : R' ⟶ U}
    {ρ : R ⟶ U} (hρ : t ≫ q = ρ) (e : G ≅ R) (a : G ⟶ G') (eU : G' ≅ U)
    (h : a ≫ eU.hom = e.hom ≫ ρ) : RingHom.ker t.hom ≤ RingHom.ker (e.inv ≫ a).hom := by
  refine (ker_le_ker_of_comp_eq hρ).trans ?_
  rw [← ker_comp_iso (e.inv ≫ a) eU, Category.assoc, h, ← Category.assoc, e.inv_hom_id,
    Category.id_comp]

/-! ### From a pushout square of affine site objects to the fibre product of rings -/

section Pushout

open Stacks.Pushout

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

private theorem isoSpec_hom_appTop_gamma (X : Scheme.{u}) [IsAffine X] :
    X.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom := by
  rw [Scheme.isoSpec]
  simp

/-- **The ring of global functions of the fourth corner of an affine pushout square is the
fibre product of the rings of the other three**, compatibly with both inclusions. -/
private theorem exists_pushoutCornerIso {U V W Z : BigAffineFppf B S hS}
    (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    [IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map g)]
    (hpo : IsPushout ((BigAffineFppf.toScheme B S hS).map g)
      ((BigAffineFppf.toScheme B S hS).map f)
      ((BigAffineFppf.toScheme B S hS).map j)
      ((BigAffineFppf.toScheme B S hS).map i)) :
    ∃ e : Γ((BigAffineFppf.toScheme B S hS).obj Z, ⊤) ≅
        affinePushoutRing ((BigAffineFppf.toScheme B S hS).map g)
          ((BigAffineFppf.toScheme B S hS).map f),
      ((BigAffineFppf.toScheme B S hS).map i).appTop = e.hom ≫
          affinePushoutRingToTarget ((BigAffineFppf.toScheme B S hS).map g)
            ((BigAffineFppf.toScheme B S hS).map f) ∧
        ((BigAffineFppf.toScheme B S hS).map j).appTop = e.hom ≫
          affinePushoutRingToAmbient ((BigAffineFppf.toScheme B S hS).map g)
            ((BigAffineFppf.toScheme B S hS).map f) := by
  set P := affinePushoutRing ((BigAffineFppf.toScheme B S hS).map g)
    ((BigAffineFppf.toScheme B S hS).map f) with hP
  set ε := hpo.isoIsPushout _ _ (isPushout_of_isClosedImmersion_of_isAffine
    ((BigAffineFppf.toScheme B S hS).map g) ((BigAffineFppf.toScheme B S hS).map f)) with hε
  have hc : ε.inv.appTop ≫ ε.hom.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, ε.hom_inv_id, Scheme.Hom.id_appTop]
  have hc' : ε.hom.appTop ≫ ε.inv.appTop = 𝟙 _ := by
    rw [← Scheme.Hom.comp_appTop, ε.inv_hom_id, Scheme.Hom.id_appTop]
  have key : ∀ {T : CommRingCat.{u}} (X : Γ((BigAffineFppf.toScheme B S hS).obj Z, ⊤) ⟶ T)
      (R : P ⟶ T), ε.hom.appTop ≫ X = (Scheme.ΓSpecIso P).hom ≫ R →
      X = (ε.inv.appTop ≫ (Scheme.ΓSpecIso P).hom) ≫ R := fun X R h => by
    rw [Category.assoc, ← h, ← Category.assoc, hc, Category.id_comp]
  refine ⟨{ hom := ε.inv.appTop ≫ (Scheme.ΓSpecIso P).hom
            inv := (Scheme.ΓSpecIso P).inv ≫ ε.hom.appTop
            hom_inv_id := by
              rw [Category.assoc, ← Category.assoc (Scheme.ΓSpecIso P).hom, Iso.hom_inv_id,
                Category.id_comp, hc]
            inv_hom_id := by
              rw [Category.assoc, ← Category.assoc ε.hom.appTop, hc', Category.id_comp,
                Iso.inv_hom_id] }, ?_, ?_⟩
  · have h := congrArg Scheme.Hom.appTop (IsPushout.inr_isoIsPushout_hom _ _ hpo
      (isPushout_of_isClosedImmersion_of_isAffine
        ((BigAffineFppf.toScheme B S hS).map g) ((BigAffineFppf.toScheme B S hS).map f)))
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
      isoSpec_hom_appTop_gamma, Scheme.ΓSpecIso_naturality] at h
    exact key _ _ h
  · have h := congrArg Scheme.Hom.appTop (IsPushout.inl_isoIsPushout_hom _ _ hpo
      (isPushout_of_isClosedImmersion_of_isAffine
        ((BigAffineFppf.toScheme B S hS).map g) ((BigAffineFppf.toScheme B S hS).map f)))
    rw [Scheme.Hom.comp_appTop, Scheme.Hom.comp_appTop,
      isoSpec_hom_appTop_gamma, Scheme.ΓSpecIso_naturality] at h
    exact key _ _ h

end Pushout

/-- **Pasting two squares of fibres, with the two composites named.** -/
private theorem isEquivalence_fiberSquareComparison_paste'
    {D : Type*} [Category D] {Y : Type*} [Category Y]
    (q : Y ⥤ D) (c : q.ChoiceOfPullbacks)
    {U V W W₁ Z Z₁ : D}
    (f : U ⟶ V) (g₁ : U ⟶ W₁) (g₂ : W₁ ⟶ W)
    (i₁ : V ⟶ Z₁) (i₂ : Z₁ ⟶ Z) (j₁ : W₁ ⟶ Z₁) (j₂ : W ⟶ Z)
    (g : U ⟶ W) (i : V ⟶ Z) (hgg : g₁ ≫ g₂ = g) (hii : i₁ ≫ i₂ = i)
    (w₁ : f ≫ i₁ = g₁ ≫ j₁) (w₂ : j₁ ≫ i₂ = g₂ ≫ j₂) (w : f ≫ i = g ≫ j₂)
    (h₁ : (fiberSquareComparison q c f g₁ i₁ j₁ w₁).IsEquivalence)
    (h₂ : (fiberSquareComparison q c j₁ g₂ i₂ j₂ w₂).IsEquivalence) :
    (fiberSquareComparison q c f g i j₂ w).IsEquivalence := by
  subst hgg
  subst hii
  exact isEquivalence_fiberSquareComparison_paste q c f g₁ g₂ i₁ i₂ j₁ j₂ w₁ w₂ w h₁ h₂

section Induct

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {𝒳 : Type u₁} [Category.{v₁} 𝒳] {p : 𝒳 ⥤ BigFppfOver B S hS} [p.IsFibered]

/-- **(RS\*) implies the conclusion of (RS) for a nilpotent surjection.** The surjection is
factored through a tower of square-zero steps and the resulting squares of fibres are
pasted. -/
private theorem affineSquareComparison_isEquivalence_of_pow_eq_bot
    {hp : p.IsFiberedInGroupoids} (hRS : SatisfiesRSStar B S hS p hp) (n : ℕ) :
    ∀ (U V W Z : BigAffineFppf B S hS)
      (f : U ⟶ V) (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j)
      (RU RV RW RZ : CommRingCat.{u})
      (eU : Γ((BigAffineFppf.toScheme B S hS).obj U, ⊤) ≅ RU)
      (eV : Γ((BigAffineFppf.toScheme B S hS).obj V, ⊤) ≅ RV)
      (eW : Γ((BigAffineFppf.toScheme B S hS).obj W, ⊤) ≅ RW)
      (eZ : Γ((BigAffineFppf.toScheme B S hS).obj Z, ⊤) ≅ RZ)
      (φ : RV ⟶ RU) (γ : RW ⟶ RU) (ψ : RZ ⟶ RV) (χ : RZ ⟶ RW),
      ((BigAffineFppf.toScheme B S hS).map f).appTop ≫ eU.hom = eV.hom ≫ φ →
      ((BigAffineFppf.toScheme B S hS).map g).appTop ≫ eU.hom = eW.hom ≫ γ →
      ((BigAffineFppf.toScheme B S hS).map i).appTop ≫ eV.hom = eZ.hom ≫ ψ →
      ((BigAffineFppf.toScheme B S hS).map j).appTop ≫ eW.hom = eZ.hom ≫ χ →
      IsPullback ψ χ φ γ → Function.Surjective γ.hom →
      RingHom.ker γ.hom ^ n = ⊥ →
      (affineSquareComparison p f g i j h).IsEquivalence := by
  induction n with
  | zero =>
    intro U V W Z f g i j h RU RV RW RZ eU eV eW eZ φ γ ψ χ hf hg hi hj hpb hsurj hker
    refine affineSquareComparison_isEquivalence_of_sq_zero hRS f g i j h eU eV eW eZ
      hf hg hi hj hpb hsurj ?_
    rw [pow_zero, Ideal.one_eq_top] at hker
    exact le_bot_iff.mp (hker ▸ le_top)
  | succ n ih =>
    intro U V W Z f g i j h RU RV RW RZ eU eV eW eZ φ γ ψ χ hf hg hi hj hpb hsurj hker
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      refine affineSquareComparison_isEquivalence_of_sq_zero hRS f g i j h eU eV eW eZ
        hf hg hi hj hpb hsurj ?_
      exact le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans hker.le)
    obtain ⟨RW₁, RZ₁, π, γ₁, τ, ψ₁, χ₁, hπγ, hτψ, hτχ, hpb₁, hpb₂, hπsurj, hπsq,
      hγ₁surj, hγ₁ker, hτsurj⟩ := exists_squareZeroFactorization φ γ ψ χ hpb hsurj hn hker
    -- the two intermediate objects, cut out by the two surjections
    set W₁ := surjObj W eW π hπsurj with hW₁
    set Z₁ := surjObj Z eZ τ hτsurj with hZ₁
    set g₂ : W₁ ⟶ W := surjHom W eW π hπsurj with hg₂
    set i₂ : Z₁ ⟶ Z := surjHom Z eZ τ hτsurj with hi₂
    set eW₁ := surjIso W eW π hπsurj with heW₁
    set eZ₁ := surjIso Z eZ τ hτsurj with heZ₁
    have hg₂app : ((BigAffineFppf.toScheme B S hS).map g₂).appTop ≫ eW₁.hom = eW.hom ≫ π :=
      appTop_surjHom W eW π hπsurj
    have hi₂app : ((BigAffineFppf.toScheme B S hS).map i₂).appTop ≫ eZ₁.hom = eZ.hom ≫ τ :=
      appTop_surjHom Z eZ τ hτsurj
    -- the three factorisations through the intermediate objects
    have hjc : ((BigAffineFppf.toScheme B S hS).map (g₂ ≫ j)).appTop ≫ eW₁.hom =
        eZ.hom ≫ τ ≫ χ₁ := by
      rw [hτχ, Functor.map_comp, Scheme.Hom.comp_appTop, Category.assoc, hg₂app,
        ← Category.assoc ((BigAffineFppf.toScheme B S hS).map j).appTop, hj, Category.assoc]
    obtain ⟨g₁, hg₁⟩ := exists_hom_surjObj g eW π hπsurj
      (ker_le_ker_inv_comp hπγ eW _ eU hg)
    obtain ⟨i₁, hi₁⟩ := exists_hom_surjObj i eZ τ hτsurj
      (ker_le_ker_inv_comp hτψ eZ _ eV hi)
    obtain ⟨j₁, hj₁⟩ := exists_hom_surjObj (g₂ ≫ j) eZ τ hτsurj
      (ker_le_ker_inv_comp rfl eZ _ eW₁ hjc)
    -- the induced maps on global functions
    have hg₂surj : Function.Surjective
        (((BigAffineFppf.toScheme B S hS).map g₂).appTop.hom) :=
      surjective_of_sq _ π eW eW₁ hg₂app hπsurj
    have hi₂surj : Function.Surjective
        (((BigAffineFppf.toScheme B S hS).map i₂).appTop.hom) :=
      surjective_of_sq _ τ eZ eZ₁ hi₂app hτsurj
    have hg₁app := appTop_eq_of_comp_surjective g₁ g₂ eU eW₁ eW hg₂app hg₂surj
      (by rw [hg₁, hπγ]; exact hg)
    have hi₁app := appTop_eq_of_comp_surjective i₁ i₂ eV eZ₁ eZ hi₂app hi₂surj
      (by rw [hi₁, hτψ]; exact hi)
    have hj₁app := appTop_eq_of_comp_surjective j₁ i₂ eW₁ eZ₁ eZ hi₂app hi₂surj
      (by rw [hj₁]; exact hjc)
    -- the two sub-squares commute
    have hmono : Mono ((BigAffineFppf.toScheme B S hS).map i₂) := by
      have : IsClosedImmersion (Spec.map τ) := IsClosedImmersion.spec_of_surjective τ hτsurj
      rw [hi₂, toScheme_map_surjHom]
      change Mono (Spec.map τ ≫ Spec.map eZ.hom ≫
        ((BigAffineFppf.toScheme B S hS).obj Z).isoSpec.inv)
      infer_instance
    have w₁ : f ≫ i₁ = g₁ ≫ j₁ := by
      refine cancel_mono_site hmono ?_
      rw [Category.assoc, Category.assoc, hi₁, hj₁, ← Category.assoc, hg₁]
      exact h
    -- the comparison of the lower square, by induction
    have h₁ := ih U V W₁ Z₁ f g₁ i₁ j₁ w₁ RU RV RW₁ RZ₁ eU eV eW₁ eZ₁ φ γ₁ ψ₁ χ₁
      hf hg₁app hi₁app hj₁app hpb₁ hγ₁surj hγ₁ker
    -- the comparison of the upper square, by (RS*)
    have h₂ := affineSquareComparison_isEquivalence_of_sq_zero hRS j₁ g₂ i₂ j hj₁
      eW₁ eZ₁ eW eZ hj₁app hg₂app hi₂app hj hpb₂ hπsurj hπsq
    exact isEquivalence_fiberSquareComparison_paste' p p.chosenPullbacks
      ((BigAffineFppf.inclusion B S hS).map f) ((BigAffineFppf.inclusion B S hS).map g₁)
      ((BigAffineFppf.inclusion B S hS).map g₂) ((BigAffineFppf.inclusion B S hS).map i₁)
      ((BigAffineFppf.inclusion B S hS).map i₂) ((BigAffineFppf.inclusion B S hS).map j₁)
      ((BigAffineFppf.inclusion B S hS).map j)
      ((BigAffineFppf.inclusion B S hS).map g) ((BigAffineFppf.inclusion B S hS).map i)
      (by rw [← Functor.map_comp, hg₁]) (by rw [← Functor.map_comp, hi₁])
      (by simpa only [Functor.map_comp] using
        congrArg (BigAffineFppf.inclusion B S hS).map w₁)
      (by simpa only [Functor.map_comp] using
        congrArg (BigAffineFppf.inclusion B S hS).map hj₁)
      (by simpa only [Functor.map_comp] using
        congrArg (BigAffineFppf.inclusion B S hS).map h)
      h₁ h₂


/-! ### (RS\*) implies (RS) -/

/-- **The remark following Stacks 07Y8: condition (RS\*) implies condition (RS).**

Given a pushout square of finite-type local Artinian objects of the site along a closed
immersion, the closed immersion is a surjection of Artinian local rings, so its kernel is
nilpotent; the surjection therefore factors as a tower of square-zero surjections, each of
which (RS\*) covers, and the resulting squares of fibres paste to the given one. -/
@[stacks 0CXN "observation (4): if 𝒳 satisfies (RS*), then 𝒳 satisfies (RS); the base need \
not be locally Noetherian"]
public theorem satisfiesRS_of_satisfiesRSStar
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒵 : Type u₁} [Category.{v₁} 𝒵] (p : 𝒵 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hRS : SatisfiesRSStar B S hS p hp) :
    SatisfiesRS B S hS p hp := by
  let : p.IsFibered := hp.isFibered
  intro X X' Y Y' i j i' j' w hX hX' hY hY' _ _ _ _ hci hpo
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj X) := hX.1
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj X') := hX'.1
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj Y) := hY.1
  let : IsAffine ((BigFppfOver.toScheme B S hS).obj Y') := hY'.1
  let : IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj X, ⊤) := hX.2.1
  let : IsLocalRing Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) := hX'.2.1
  let : IsArtinianRing Γ((BigFppfOver.toScheme B S hS).obj X', ⊤) := hX'.2.2
  set U : BigAffineFppf B S hS := ⟨X, hX.1⟩ with hU
  set V : BigAffineFppf B S hS := ⟨Y, hY.1⟩ with hV
  set W : BigAffineFppf B S hS := ⟨X', hX'.1⟩ with hW
  set Z : BigAffineFppf B S hS := ⟨Y', hY'.1⟩ with hZ
  set f : U ⟶ V := ObjectProperty.homMk j with hf₀
  set g : U ⟶ W := ObjectProperty.homMk i with hg₀
  set ia : V ⟶ Z := ObjectProperty.homMk j' with hia
  set ja : W ⟶ Z := ObjectProperty.homMk i' with hja
  let : IsLocalRing Γ((BigAffineFppf.toScheme B S hS).obj U, ⊤) := hX.2.1
  let : IsLocalRing Γ((BigAffineFppf.toScheme B S hS).obj W, ⊤) := hX'.2.1
  let : IsArtinianRing Γ((BigAffineFppf.toScheme B S hS).obj W, ⊤) := hX'.2.2
  have hcomm : f ≫ ia = g ≫ ja := ObjectProperty.hom_ext _ w.symm
  have : IsClosedImmersion ((BigAffineFppf.toScheme B S hS).map g) := hci
  have hpo' : IsPushout ((BigAffineFppf.toScheme B S hS).map g)
      ((BigAffineFppf.toScheme B S hS).map f)
      ((BigAffineFppf.toScheme B S hS).map ja)
      ((BigAffineFppf.toScheme B S hS).map ia) := hpo
  have hsurj : Function.Surjective
      (((BigAffineFppf.toScheme B S hS).map g).appTop.hom) :=
    (IsClosedImmersion.isAffine_surjective_of_isAffine
      ((BigAffineFppf.toScheme B S hS).map g)).2
  obtain ⟨n, -, hker⟩ := exists_ker_pow_eq_bot
    ((BigAffineFppf.toScheme B S hS).map g).appTop hsurj
  obtain ⟨eZ, hiZ, hjZ⟩ := exists_pushoutCornerIso f g ia ja hpo'
  exact affineSquareComparison_isEquivalence_of_pow_eq_bot hRS n U V W Z f g ia ja hcomm
    Γ((BigAffineFppf.toScheme B S hS).obj U, ⊤)
    Γ((BigAffineFppf.toScheme B S hS).obj V, ⊤)
    Γ((BigAffineFppf.toScheme B S hS).obj W, ⊤)
    (Stacks.Pushout.affinePushoutRing ((BigAffineFppf.toScheme B S hS).map g)
      ((BigAffineFppf.toScheme B S hS).map f))
    (Iso.refl _) (Iso.refl _) (Iso.refl _) eZ
    ((BigAffineFppf.toScheme B S hS).map f).appTop
    ((BigAffineFppf.toScheme B S hS).map g).appTop
    (Stacks.Pushout.affinePushoutRingToTarget ((BigAffineFppf.toScheme B S hS).map g)
      ((BigAffineFppf.toScheme B S hS).map f))
    (Stacks.Pushout.affinePushoutRingToAmbient ((BigAffineFppf.toScheme B S hS).map g)
      ((BigAffineFppf.toScheme B S hS).map f))
    (by rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by rw [Iso.refl_hom, Iso.refl_hom, Category.comp_id, Category.id_comp])
    (by rwa [Iso.refl_hom, Category.comp_id])
    (by rwa [Iso.refl_hom, Category.comp_id])
    (Stacks.Pushout.isPullback_affinePushoutRing _ _) hsurj hker

end Induct

end Deformation.Artin
