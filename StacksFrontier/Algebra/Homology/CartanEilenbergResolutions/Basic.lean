module

import Mathlib.CategoryTheory.Abelian.Injective.Extend
import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedFunctorInjective
public import StacksFrontier.Algebra.Homology.HomotopyCategory.DegreewiseSplit
public import StacksFrontier.Algebra.Homology.MapTotalComplex
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Cartan-Eilenberg resolutions: definition and the horseshoe lemma

This file defines Cartan-Eilenberg resolutions of cochain complexes
(`CochainComplex.CartanEilenbergResolution`, [Stacks, Tag 015H]) and proves the horseshoe lemma
in the form used to construct them: given a short exact sequence whose two ends are already
resolved by bounded below complexes of injectives, its middle term is resolved compatibly.

## Implementation notes

The horseshoe lemma is proved from the K-injectivity of a bounded below complex of injectives
rather than by an induction on the degree: the twisting morphism which turns the biproduct
`T₁^q ⊞ T₃^q` into a resolution of the middle term is obtained by lifting along a
quasi-isomorphism, and the homotopy by which it fails to be compatible with the augmentations on
the nose is absorbed into the augmentation of `T₁`.

## References

* [Stacks, Tag 015H]
* [Stacks, Tag 013T]
-/

@[expose] public section

open CategoryTheory Limits HomologicalComplex StacksDraft.TotalComplexQuasiIso

/-! ### Cartan-Eilenberg resolutions -/

namespace CochainComplex

section Definition

variable {C : Type*} [Category C] [Abelian C]

/-- A Cartan-Eilenberg resolution of a cochain complex `K` in an abelian category: a double
complex `I` of injective objects, vanishing in first degrees `≪ 0` and in negative second
degrees, together with an augmentation `ε` from `K` placed in second degree `0`, such that
the complexes `I^{p,•}`, `Ker(d₁^{p,•})`, `Im(d₁^{p,•})` and `H^p_I(I^{•,•})` are
injective resolutions of `K^p`, `Ker(d_K^p)`, `Im(d_K^p)` and `H^p(K^•)`. -/
@[stacks 015H, ega "0 11.4.2" "injective, bdd below"]
public structure CartanEilenbergResolution (K : CochainComplex C ℤ) where
  /-- the double complex `I^{•,•}` doing the resolving, viewed as a cochain complex of
  cochain complexes: `bicomplex.X p` is the column `I^{p,•}` -/
  bicomplex : HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ)
  /-- the augmentation `ε : K^• ⟶ I^{•,0}`, as a morphism of double complexes from `K`
  placed in second degree `0` -/
  ε : ((HomologicalComplex.single C (ComplexShape.up ℤ) 0).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj K ⟶ bicomplex
  /-- (1) there is an `i` with `I^{p,q} = 0` for all `p < i` and all `q` -/
  boundedBelow : CochainComplex.plus (CochainComplex C ℤ) bicomplex
  /-- (2) `I^{p,q} = 0` for `q < 0` -/
  isStrictlyGE : ∀ p, CochainComplex.IsStrictlyGE (bicomplex.X p) 0
  /-- (3) the terms of `I^{p,•}` are injective -/
  injective : ∀ p q, Injective ((bicomplex.X p).X q)
  /-- (3) `I^{p,•}` resolves `K^p` -/
  quasiIso : ∀ p, QuasiIso (ε.f p)
  /-- (4) the terms of `Ker(d₁^{p,•})` are injective -/
  injective_cycles : ∀ p q, Injective ((bicomplex.cycles p).X q)
  /-- (4) `Ker(d₁^{p,•})` resolves `Ker(d_K^p)` -/
  quasiIso_cyclesMap : ∀ p, QuasiIso (cyclesMap ε p)
  /-- (5) the terms of `Im(d₁^{p,•})` are injective -/
  injective_image : ∀ p q, Injective ((image (bicomplex.dFrom p)).X q)
  /-- (5) `Im(d₁^{p,•})` resolves `Im(d_K^p)` -/
  quasiIso_imageMap : ∀ p, QuasiIso (image.map (ε.sqFrom p))
  /-- (6) the terms of `H^p_I(I^{•,•})` are injective -/
  injective_homology : ∀ p q, Injective ((bicomplex.homology p).X q)
  /-- (6) `H^p_I(I^{•,•})` resolves `H^p(K^•)` -/
  quasiIso_homologyMap : ∀ p, QuasiIso (homologyMap ε p)

attribute [instance] CartanEilenbergResolution.isStrictlyGE
  CartanEilenbergResolution.injective CartanEilenbergResolution.quasiIso
  CartanEilenbergResolution.injective_cycles CartanEilenbergResolution.quasiIso_cyclesMap
  CartanEilenbergResolution.injective_image CartanEilenbergResolution.quasiIso_imageMap
  CartanEilenbergResolution.injective_homology
  CartanEilenbergResolution.quasiIso_homologyMap

end Definition

end CochainComplex

namespace StacksDraft.CartanEilenbergResolutions

universe w w' v v' u u' v'' u''

section Lifting

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **A morphism into a K-injective complex extends along a quasi-isomorphism**, up to
homotopy: if `f : X ⟶ Y` is a quasi-isomorphism of cochain complexes and `Z` is K-injective,
then every `g : X ⟶ Z` is homotopic to `f` followed by some `u : Y ⟶ Z`.

Morphisms into a K-injective complex see only the derived category: `DerivedCategory.Qh` is
bijective on morphisms with K-injective target (`CochainComplex.IsKInjective.Qh_map_bijective`),
and a quasi-isomorphism becomes invertible there, so `u` is the morphism whose homotopy class
corresponds to `Q(g) ∘ Q(f)⁻¹`. A bounded below complex of injectives is K-injective
(`CochainComplex.isKInjective_of_injective`), so for such a `Z` this is the classical
statement that a morphism into a complex of injectives extends along a resolution — in the
form which needs no degreewise induction. -/
private theorem exists_homotopy_comp_of_quasiIso {X Y Z : CochainComplex C ℤ}
    (f : X ⟶ Y) [QuasiIso f] [Z.IsKInjective] (g : X ⟶ Z) :
    ∃ u : Y ⟶ Z, Nonempty (Homotopy (f ≫ u) g) := by
  let _ := HasDerivedCategory.standard C
  have hnat : ∀ {A B : CochainComplex C ℤ} (α : A ⟶ B),
      DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map α) =
        (DerivedCategory.quotientCompQhIso C).hom.app A ≫ DerivedCategory.Q.map α ≫
          (DerivedCategory.quotientCompQhIso C).inv.app B := by
    intro A B α
    have h := (DerivedCategory.quotientCompQhIso C).hom.naturality α
    simp only [Functor.comp_map] at h
    rw [← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  obtain ⟨u, hu⟩ := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj Y) Z).surjective
      ((DerivedCategory.quotientCompQhIso C).hom.app Y ≫ inv (DerivedCategory.Q.map f) ≫
        DerivedCategory.Q.map g ≫ (DerivedCategory.quotientCompQhIso C).inv.app Z)
  refine ⟨(HomotopyCategory.quotient C (ComplexShape.up ℤ)).preimage u,
    ⟨HomotopyCategory.homotopyOfEq _ _ ?_⟩⟩
  apply (CochainComplex.IsKInjective.Qh_map_bijective
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj X) Z).injective
  rw [Functor.map_comp, Functor.map_preimage, DerivedCategory.Qh.map_comp, hnat f, hnat g, hu]
  simp

/-- A morphism from a complex concentrated in degree `0` to `T` is given by a morphism
`a : A ⟶ T ^ 0` with `a ≫ d ^ 0 = 0`. -/
private theorem exists_augmentation {A : C} {T : CochainComplex C ℤ}
    (ι : (single C (ComplexShape.up ℤ) 0).obj A ⟶ T) :
    ∃ a : A ⟶ T.X 0, (singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) A).hom ≫ a = ι.f 0 ∧
      a ≫ T.d 0 1 = 0 :=
  ⟨(singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) A).inv ≫ ι.f 0, by simp,
    by rw [Category.assoc, ι.comm, single_obj_d, zero_comp, comp_zero]⟩

end Lifting

section Twist

variable {C : Type u} [Category.{v} C] [Abelian C]
variable {T₁ T₃ : CochainComplex C ℤ} (u : ∀ q : ℤ, T₃.X q ⟶ T₁.X (q + 1))
  (hu : ∀ q : ℤ, u q ≫ T₁.d (q + 1) (q + 1 + 1) + T₃.d q (q + 1) ≫ u (q + 1) = 0)

include hu in
/-- For a *twisting* `u ^ q : T₃ ^ q ⟶ T₁ ^ {q + 1}` satisfying
`u ^ q ≫ d₁ ^ {q + 1} + d₃ ^ q ≫ u ^ {q + 1} = 0`, the sequence
`0 → T₁ → CochainComplex.twist (CochainComplex.twistHom u hu) → T₃ → 0` (maps
`CochainComplex.twistι` and `CochainComplex.twistπ`) is short exact; it is split in each degree.

Here `CochainComplex.twist (CochainComplex.twistHom u hu)` is the **twisted biproduct** of `T₁`
and `T₃` along `u`: the complex with terms `T₁ ^ q ⊞ T₃ ^ q` and differential
`(d₁, u ; 0, d₃)`. Every degreewise split short exact sequence is of this form.

The twisting condition says that `u` is a morphism of complexes `T₃ ⟶ T₁⟦1⟧`, and then
`CochainComplex.twist (CochainComplex.twistHom u hu)` is isomorphic to the mapping cone of the
corresponding morphism `T₃⟦-1⟧ ⟶ T₁`; it is defined directly, in terms of the family `u`, so
that its terms and differentials are available without the shift and `Cochain` bookkeeping that
`CochainComplex.mappingCone` is phrased in. -/
@[sga "4 XVII 5.5.25.2" "more general"]
private lemma twist_shortExact :
    (ShortComplex.mk _ _
      (CochainComplex.twistι_comp_twistπ (CochainComplex.twistHom u hu))).ShortExact :=
  HomologicalComplex.shortExact_of_degreewise_shortExact _ fun _ =>
    ShortComplex.Splitting.shortExact
      { r := biprod.fst, s := biprod.inr, f_r := by simp, s_g := by simp, id := by simp }

private lemma twist_isStrictlyGE (n : ℤ) (h₁ : T₁.IsStrictlyGE n) (h₃ : T₃.IsStrictlyGE n) :
    (CochainComplex.twist (CochainComplex.twistHom u hu)).IsStrictlyGE n := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro i hi
  rw [CochainComplex.twist_X]
  exact (biprod_isZero_iff _ _).2
    ⟨T₁.isZero_of_isStrictlyGE n i hi, T₃.isZero_of_isStrictlyGE n i hi⟩

private lemma twist_injective (q : ℤ) (h₁ : Injective (T₁.X q)) (h₃ : Injective (T₃.X q)) :
    Injective ((CochainComplex.twist (CochainComplex.twistHom u hu)).X q) := by
  rw [CochainComplex.twist_X]; infer_instance

end Twist

section Horseshoe

variable (C : Type u) [Category.{v} C] [Abelian C]

/-- The horseshoe property of an abelian category `C`: every short exact sequence
`0 → S₁ → S₂ → S₃ → 0` of objects of `C`, together with injective resolutions `T₁` of `S₁`
and `T₃` of `S₃`, is covered by a short exact sequence of complexes
`0 → T₁ → T₂ → T₃ → 0` in which `T₂` is an injective resolution of `S₂` and the two squares
built from the augmentations commute.

This is the case of a short exact sequence of objects — i.e. of complexes concentrated in
degree `0` — of [Stacks, Tag 013T], with the resolutions of *both* outer terms prescribed;
the resolutions are taken `ℤ`-graded and supported in degrees `≥ 0`, as
`CochainComplex.CartanEilenbergResolution` requires of the columns of its double complex. -/
public abbrev HorseshoeProperty : Prop :=
  ∀ (S : ShortComplex C), S.ShortExact → ∀ (T₁ T₃ : CochainComplex C ℤ),
    CochainComplex.IsStrictlyGE T₁ 0 → CochainComplex.IsStrictlyGE T₃ 0 →
    (∀ q, Injective (T₁.X q)) → (∀ q, Injective (T₃.X q)) →
    ∀ (ι₁ : (single C (ComplexShape.up ℤ) 0).obj S.X₁ ⟶ T₁)
      (ι₃ : (single C (ComplexShape.up ℤ) 0).obj S.X₃ ⟶ T₃),
      QuasiIso ι₁ → QuasiIso ι₃ →
      ∃ (T₂ : CochainComplex C ℤ) (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) (w : f ≫ g = 0)
        (ι₂ : (single C (ComplexShape.up ℤ) 0).obj S.X₂ ⟶ T₂),
        (ShortComplex.mk f g w).ShortExact ∧ CochainComplex.IsStrictlyGE T₂ 0 ∧
          (∀ q, Injective (T₂.X q)) ∧ QuasiIso ι₂ ∧
          ι₁ ≫ f = (single C (ComplexShape.up ℤ) 0).map S.f ≫ ι₂ ∧
          ι₂ ≫ g = (single C (ComplexShape.up ℤ) 0).map S.g ≫ ι₃

/-- **The horseshoe lemma for injective resolutions.** An abelian category with enough
injectives has the horseshoe property: given a short exact sequence
`0 → S₁ → S₂ → S₃ → 0` and injective resolutions `T₁` of `S₁` and `T₃` of `S₃`, there is an
injective resolution `T₂` of `S₂` and a short exact sequence of complexes
`0 → T₁ → T₂ → T₃ → 0` over the given one.

[Stacks, Tag 013T] proves this for a short exact sequence of bounded below *complexes* by a
pushout construction which resolves one degree at a time. For a short exact sequence of
objects the resolution `T₂` is instead the twisted biproduct: write `α₁ : S₁ ⟶ T₁ ^ 0` and
`α₃ : S₃ ⟶ T₃ ^ 0` for the augmentations, extend `α₁` along the monomorphism `S₁ ⟶ S₂` to
`α : S₂ ⟶ T₁ ^ 0` (possible because `T₁ ^ 0` is injective), and let `v : S₃ ⟶ T₁ ^ 1` be the
morphism with `S.g ≫ v = α ≫ d₁ ^ 0`, which exists because `S₁ ⟶ S₂ ⟶ T₁ ^ 0 ⟶ T₁ ^ 1` is
zero and `0 → S₁ → S₂ → S₃ → 0` is exact; it satisfies `v ≫ d₁ ^ 1 = 0` because `S₂ ⟶ S₃` is
an epimorphism. Then
```
T₂ ^ q = T₁ ^ q ⊞ T₃ ^ q,      d₂ ^ q = (d₁ ^ q, u ^ q ; 0, d₃ ^ q),
ι₂ = (α, S.g ≫ α₃) : S₂ ⟶ T₁ ^ 0 ⊞ T₃ ^ 0
```
for a family `u ^ q : T₃ ^ q ⟶ T₁ ^ {q + 1}` with `d₃ ^ q ≫ u ^ {q + 1} + u ^ q ≫ d₁ ^ {q + 1}
= 0` and `α₃ ≫ u ^ 0 = -v`: the first identity says exactly that `u` is a morphism of
complexes `T₃ ⟶ T₁⟦1⟧`, and it is what makes `d₂ ≫ d₂ = 0`, while the second makes
`ι₂ ≫ d₂ ^ 0 = 0`. The source builds `u` by induction on `q`; it need not be built by hand,
because `T₁⟦1⟧` is a bounded below complex of injectives, hence K-injective, and `-v` is a
morphism of complexes `S₃[0] ⟶ T₁⟦1⟧`, so `exists_homotopy_comp_of_quasiIso` applied to the
quasi-isomorphism `ι₃ : S₃[0] ⟶ T₃` produces `u` with `ι₃ ≫ u` homotopic to `-v`. A homotopy
out of a complex concentrated in degree `0` has one possibly nonzero component, so the
conclusion is `α₃ ≫ u ^ 0 = -v + k ≫ d₁ ^ 0` for some `k : S₃ ⟶ T₁ ^ 0`, and replacing `α`
by `α - S.g ≫ k` (which still restricts to `α₁` along `S₁ ⟶ S₂`, since `S₁ ⟶ S₂ ⟶ S₃` is
zero) absorbs the correction. Finally `0 → T₁ → T₂ → T₃ → 0` is degreewise split, hence
short exact, its terms are injective, it is supported in degrees `≥ 0`, the two commutation
requirements hold by construction, and `QuasiIso ι₂` follows from `QuasiIso ι₁` and
`QuasiIso ι₃` by two-out-of-three in a short exact sequence of complexes (the `τ₂` analogue
of Mathlib's `HomologicalComplex.HomologySequence.quasiIso_τ₃`, which Mathlib does not
have). -/
public theorem horseshoeProperty [EnoughInjectives C] : HorseshoeProperty C := by
  intro S hS T₁ T₃ hge₁ hge₃ hinj₁ hinj₃ ι₁ ι₃ hqi₁ hqi₃
  have := hS.mono_f
  have := hS.epi_g
  have := hge₁
  have := hge₃
  have := hinj₁
  have := hinj₃
  have := hqi₃
  have : ∀ n : ℤ, Injective ((T₁⟦(1 : ℤ)⟧).X n) := fun n => hinj₁ (n + 1)
  have : (T₁⟦(1 : ℤ)⟧).IsStrictlyGE (-1) := T₁.isStrictlyGE_shift 0 1 (-1) (by ring)
  have : (T₁⟦(1 : ℤ)⟧).IsKInjective := CochainComplex.isKInjective_of_injective _ (-1)
  have hfg : ∀ {W : C} (t : S.X₃ ⟶ W), S.f ≫ S.g ≫ t = 0 := fun t => by
    rw [← Category.assoc, S.zero, zero_comp]
  -- the two given augmentations, read as morphisms of objects of `C`
  obtain ⟨a₁, ha₁, ha₁d⟩ := exists_augmentation ι₁
  obtain ⟨a₃, ha₃, ha₃d⟩ := exists_augmentation ι₃
  -- `a₁` extends to `S.X₂` because `T₁ ^ 0` is injective
  obtain ⟨α, hα⟩ : ∃ α : S.X₂ ⟶ T₁.X 0, S.f ≫ α = a₁ :=
    ⟨Injective.factorThru _ S.f, Injective.comp_factorThru _ _⟩
  -- `α ≫ d₁ ^ 0` kills `S.X₁`, hence descends to `S.X₃`
  obtain ⟨v, hv⟩ : ∃ v : S.X₃ ⟶ T₁.X 1, S.g ≫ v = α ≫ T₁.d 0 1 :=
    hS.exact.desc' _ (by rw [← Category.assoc, hα, ha₁d])
  have hvd : v ≫ T₁.d 1 2 = 0 := by
    rw [← cancel_epi S.g, comp_zero, ← Category.assoc, hv, Category.assoc,
      HomologicalComplex.d_comp_d, comp_zero]
  -- the twisting morphism `T₃ ⟶ T₁⟦1⟧`, from K-injectivity of `T₁⟦1⟧`, and the homotopy
  -- defect by which it fails to lie over `-v`
  obtain ⟨u, hu, k, hk⟩ : ∃ u : ∀ q : ℤ, T₃.X q ⟶ T₁.X (q + 1),
      (∀ q : ℤ, u q ≫ T₁.d (q + 1) (q + 1 + 1) + T₃.d q (q + 1) ≫ u (q + 1) = 0) ∧
      ∃ k : S.X₃ ⟶ T₁.X 0, a₃ ≫ u 0 = k ≫ T₁.d 0 1 - v := by
    obtain ⟨w, ⟨h⟩⟩ := exists_homotopy_comp_of_quasiIso ι₃
      (HomologicalComplex.mkHomFromSingle (K := T₁⟦(1 : ℤ)⟧) (j := (0 : ℤ)) (-v) (fun m hm => by
        obtain rfl : m = 1 := by simpa using hm.symm
        simp [CochainComplex.shiftFunctor_obj_d', hvd]))
    refine ⟨fun q => w.f q, fun q => ?_,
      -((singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) S.X₃).inv ≫ h.hom 0 (-1)), ?_⟩
    · have hc := w.comm q (q + 1)
      rw [show (T₁⟦(1 : ℤ)⟧).d q (q + 1) = -T₁.d (q + 1) (q + 1 + 1) from by
        simp [CochainComplex.shiftFunctor_obj_d']] at hc
      rw [← hc]
      simp
    · have hc := h.comm 0
      rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by simp), single_obj_d, zero_comp,
        zero_add, prevD_eq h.hom (show (ComplexShape.up ℤ).Rel (-1) 0 by simp),
        HomologicalComplex.mkHomFromSingle_f] at hc
      rw [← cancel_epi (singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) S.X₃).hom,
        ← Category.assoc, ha₃, ← HomologicalComplex.comp_f, hc]
      simp [CochainComplex.shiftFunctor_obj_d', sub_eq_add_neg]
  -- the augmentation of the twisted biproduct
  obtain ⟨ι₂, hι₂⟩ : ∃ ι₂ : (single C (ComplexShape.up ℤ) 0).obj S.X₂ ⟶
        CochainComplex.twist (CochainComplex.twistHom u hu),
      ι₂.f 0 = (singleObjXSelf (ComplexShape.up ℤ) (0 : ℤ) S.X₂).hom ≫
        biprod.lift (α - S.g ≫ k) (S.g ≫ a₃) :=
    ⟨HomologicalComplex.mkHomFromSingle _ (fun m hm => by
      obtain rfl : m = 0 + 1 := hm.symm
      rw [CochainComplex.twist_d]
      simp only [CochainComplex.twistHom_f]
      refine biprod.hom_ext _ _ ?_ ?_
      · -- the differential `d₁ ^ 0` reads `T₁.d 0 (0 + 1)` here and `T₁.d 0 1` in `hv` and `hk`
        rw [show T₁.d 0 1 = T₁.d 0 (0 + 1) from rfl] at hv hk
        simp only [Category.assoc, biprod.lift_fst, Preadditive.comp_add,
          biprod.lift_fst_assoc, biprod.lift_snd_assoc, zero_comp]
        rw [hk]
        simp only [Preadditive.sub_comp, Preadditive.comp_sub, Category.assoc, hv]
        rw [sub_add_sub_cancel, sub_self]
      · simp [ha₃d]), HomologicalComplex.mkHomFromSingle_f _ _⟩
  have hc₁ : ι₁ ≫ CochainComplex.twistι (CochainComplex.twistHom u hu)
      = (single C (ComplexShape.up ℤ) 0).map S.f ≫ ι₂ := by
    apply HomologicalComplex.from_single_hom_ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.twistι_f, hι₂,
      HomologicalComplex.single_map_f_self, ← ha₁]
    refine biprod.hom_ext _ _ ?_ ?_ <;> simp [hα, hfg]
  have hc₂ : ι₂ ≫ CochainComplex.twistπ (CochainComplex.twistHom u hu)
      = (single C (ComplexShape.up ℤ) 0).map S.g ≫ ι₃ := by
    ext
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, CochainComplex.twistπ_f, hι₂,
      HomologicalComplex.single_map_f_self, ← ha₃]
    simp
  refine ⟨CochainComplex.twist (CochainComplex.twistHom u hu),
    CochainComplex.twistι (CochainComplex.twistHom _ _),
    CochainComplex.twistπ (CochainComplex.twistHom _ _),
    CochainComplex.twistι_comp_twistπ (CochainComplex.twistHom _ _), ι₂,
    twist_shortExact _ _, twist_isStrictlyGE _ _ 0 hge₁ hge₃,
    fun q => twist_injective _ _ q (hinj₁ q) (hinj₃ q), ?_, hc₁, hc₂⟩
  exact quasiIso_τ₂ (S₁ := S.map (single C (ComplexShape.up ℤ) 0))
    (S₂ := ShortComplex.mk _ _ (CochainComplex.twistι_comp_twistπ (CochainComplex.twistHom u hu)))
    { τ₁ := ι₁, τ₂ := ι₂, τ₃ := ι₃, comm₁₂ := hc₁, comm₂₃ := hc₂ }
    (hS.map_of_exact _) (twist_shortExact _ _)

end Horseshoe

section Resolutions

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Every object `A` of an abelian category with enough injectives has an injective
resolution `A ⟶ T` by a `ℤ`-graded cochain complex supported in degrees `≥ 0`, and one may
insist that `T` be a zero object whenever `A` is one.

Only the last clause is not immediate from `CategoryTheory.InjectiveResolution.of`: it is
what makes the double complex built out of these resolutions vanish in the first degrees in
which the complex being resolved does, and it is arranged by resolving a zero object by
itself. -/
@[sga "4½ Etat_0 3.2.3" "partial"]
private theorem exists_injectiveResolution_isZero [EnoughInjectives C] (A : C) :
    ∃ (T : CochainComplex C ℤ) (ι : (single C (ComplexShape.up ℤ) 0).obj A ⟶ T),
      CochainComplex.IsStrictlyGE T 0 ∧ (∀ q, Injective (T.X q)) ∧ QuasiIso ι ∧
        (IsZero A → IsZero T) := by
  by_cases hA : IsZero A
  · have h0 : IsZero ((single C (ComplexShape.up ℤ) 0).obj A) := Functor.map_isZero _ hA
    refine ⟨(single C (ComplexShape.up ℤ) 0).obj A, 𝟙 _, inferInstance, fun q => ?_,
      inferInstance, fun _ => h0⟩
    have hq : IsZero (((single C (ComplexShape.up ℤ) 0).obj A).X q) :=
      (HomologicalComplex.eval C (ComplexShape.up ℤ) q).map_isZero h0
    exact ⟨fun {Y Z} g f _ => ⟨0, by simp [hq.eq_of_tgt g 0]⟩⟩
  · exact ⟨(InjectiveResolution.of A).cochainComplex, (InjectiveResolution.of A).ι',
      inferInstance, fun q => inferInstance, inferInstance, fun h => absurd h hA⟩

end Resolutions

end StacksDraft.CartanEilenbergResolutions

end
