module

public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ShortExact
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.AwaySections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.VanishingCriterionCoextension
public import StacksFrontier.RingTheory.Localization.Glueing.AwaySum
public import StacksCore.Tactic.StacksAttribute

/-!
# The short exact sequence of localizations attached to a sum of two global sections

Let `(𝒞, 𝒪)` be a ringed site and let `a, b` be global sections of `𝒪`, with `h = a + b`. The
sheaves of `𝒪`-modules `𝒪_h`, `𝒪_{ha}`, `𝒪_{hb}` and `𝒪_{hab}` sit in a short exact sequence

  `0 → 𝒪_h → 𝒪_{ha} ⊕ 𝒪_{hb} → 𝒪_{hab} → 0`,

which is the sequence [Stacks, Tag 0998] uses to prove that its vanishing locus is closed under
addition. This file constructs it and draws that conclusion.

## Main definitions

* `AlgebraicGeometry.RingedSite.addGlobalSection`: the sum of two global sections of `𝒪`, as a
  global section. The sum in which the tag asserts the locus to be closed has to be formed by
  hand, the type of global sections carrying no additive structure of its own.
* `AlgebraicGeometry.RingedSite.awayPresheafTransition`: for global sections `f`, `f'` whose
  values satisfy `f|_U ∣ f'|_U` over every object, the comparison map
  `𝒪[1/f] ⟶ 𝒪[1/f']` of presheaves of rings, and
  `AlgebraicGeometry.RingedSite.awayModulePresheafTransition` its reading as a map of presheaves
  of `𝒪`-modules.

## Main results

* `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_of_shortExact`: vanishing of the derived
  internal Hom into `K` on the last two terms of a short exact sequence of sheaves of
  `𝒪`-modules forces it on the first. This is the dévissage the source performs with the
  sequence below.
* `AlgebraicGeometry.RingedSite.shortExact_awayModulePresheafAddComplex`: **the sequence of
  presheaves of `𝒪`-modules `0 → 𝒪[1/h] → 𝒪[1/ha] ⊕ 𝒪[1/hb] → 𝒪[1/hab] → 0` is short exact.**
* `AlgebraicGeometry.RingedSite.shortExact_awayModuleAddComplex`: **the same sequence of sheaves
  of `𝒪`-modules is short exact**, obtained by sheafifying.
* `AlgebraicGeometry.RingedSite.memVanishingIdeal_addGlobalSection`: **the vanishing locus of
  [Stacks, Tag 0998] is closed under addition**, which is what the source uses the sequence for,
  and `AlgebraicGeometry.RingedSite.isRightOrthogonalAway_addGlobalSection` the same conclusion
  at condition (2) of [Stacks, Tag 0997].
* `AlgebraicGeometry.RingedSite.memVanishingIdeal_over_addGlobalSection`: the same for sections
  over an arbitrary object of the site, which is the form the local-generation argument of
  [Stacks, Tag 099F] needs. It is the previous statement at the localized ringed site
  `AlgebraicGeometry.RingedSite.over X U` and needs nothing further: a slice of a ringed site is
  again one, and no hypothesis of the sequence is about global sections as opposed to sections.

## Implementation notes

The additivity statement sits here rather than beside the other closure properties of the locus
in `VanishingIdeal.lean` because the short exact sequence needs the sectionwise description of
`𝒪_f` from `AwaySections.lean`, which imports that file.

Everything is checked on sections and then sheafified: the sections of `𝒪[1/f]` are localizations
on the nose, `𝒪_f` is the sheafification of `𝒪[1/f]` as a sheaf of `𝒪`-modules by
`AlgebraicGeometry.RingedSite.awaySheafificationIsoAwayModule`, and the sheafification of
presheaves of modules is exact. The sectionwise statement is the commutative algebra of
`StacksFrontier/RingTheory/Localization/Glueing/AwaySum.lean`, which is stated for arbitrary
localizations of `𝒪(U)` away from the four values and for arbitrary `𝒪(U)`-algebra comparison
maps — which is what the sectionwise components of `awayModulePresheafTransition` are, so no
identification of maps has to be proved.

The four global sections are not built here from `a` and `b`; they are taken as data together
with equations for their values. A consumer therefore chooses its own spelling of the products
— `AlgebraicGeometry.RingedSite.mulGlobalSection`, or a `prodGlobalSection` over a subset — and
supplies the value equations, which are `simp` lemmas on either spelling.

That an additive functor carries a binary biproduct to one is what transports the middle term of
the sequence through sheafification and through the inclusion of sheaves into the derived
category. The library already carries that fact, as
`CategoryTheory.Functor.biprodIsoOfAdditive` of
`StacksFrontier/AlgebraicGeometry/Spaces/Perfect/MayerVietoris.lean`, with its two value equations.
It is re-proved here under the distinct name `biprodIsoOfAdditiveAux` rather than imported,
because that module sits in the Perfect-complex development and importing it would pull the étale
and approximation closure into this one.

## References

* [Stacks Project, Tag 0998](https://stacks.math.columbia.edu/tag/0998)
* [Stacks Project, Tag 0997](https://stacks.math.columbia.edu/tag/0997)
* [Stacks Project, Tag 00EJ](https://stacks.math.columbia.edu/tag/00EJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v₁ u₁ v₂ u₂ u

namespace CategoryTheory.Functor

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  [Preadditive C] [Preadditive D] [HasBinaryBiproducts C] [HasBinaryBiproducts D]

/-- **An additive functor carries a binary biproduct to a binary biproduct.** The comparison map
is the one built from the projections, and its inverse the one built from the inclusions; that
the two composites are identities is the relation
`CategoryTheory.Limits.biprod.total` together with the additivity of the functor. -/
def biprodIsoOfAdditiveAux (F : C ⥤ D) [F.Additive] (A B : C) :
    F.obj (A ⊞ B) ≅ F.obj A ⊞ F.obj B where
  hom := biprod.lift (F.map biprod.fst) (F.map biprod.snd)
  inv := biprod.desc (F.map biprod.inl) (F.map biprod.inr)
  hom_inv_id := by
    rw [biprod.lift_desc, ← F.map_comp, ← F.map_comp, ← F.map_add, biprod.total, F.map_id]
  inv_hom_id := by
    refine biprod.hom_ext' _ _ (biprod.hom_ext _ _ ?_ ?_) (biprod.hom_ext _ _ ?_ ?_) <;>
      simp [← F.map_comp]

end CategoryTheory.Functor

namespace CategoryTheory.ShortComplex

variable {R : Type u} [Ring R] {A B₁ B₂ W D : ModuleCat.{v} R}

/-- **A short complex of modules whose middle term carries the data of a binary biproduct is
short exact as soon as the three elementwise statements hold for the two summands.** The data is
a pair of sections `i₁, i₂` and retractions `p₁, p₂` with the four biproduct identities and the
completeness relation `p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙`, together with the two components `α₁, α₂` of the
first map and the two components `β₁, β₂` of the second — the second map being the *difference*
of the latter, which is the shape a Zariski glueing sequence has.

The middle term is not asked to be a biproduct of `B₁` and `B₂`, only to carry that data; an
additive functor applied to an honest biproduct supplies it. -/
theorem shortExact_of_biprodData
    (i₁ : B₁ ⟶ W) (i₂ : B₂ ⟶ W) (p₁ : W ⟶ B₁) (p₂ : W ⟶ B₂)
    (α₁ : A ⟶ B₁) (α₂ : A ⟶ B₂) (β₁ : B₁ ⟶ D) (β₂ : B₂ ⟶ D)
    (f : A ⟶ W) (g : W ⟶ D) (hfg : f ≫ g = 0)
    (htot : p₁ ≫ i₁ + p₂ ≫ i₂ = 𝟙 W)
    (hf₁ : f ≫ p₁ = α₁) (hf₂ : f ≫ p₂ = α₂)
    (hg₁ : i₁ ≫ g = β₁) (hg₂ : i₂ ≫ g = -β₂)
    (hinj : ∀ a : A, α₁ a = 0 → α₂ a = 0 → a = 0)
    (hmid : ∀ (x : B₁) (y : B₂), β₁ x = β₂ y → ∃ a : A, α₁ a = x ∧ α₂ a = y)
    (hsurj : ∀ z : D, ∃ (x : B₁) (y : B₂), β₁ x - β₂ y = z) :
    (ShortComplex.mk f g hfg).ShortExact := by
  -- The two components of an element of the middle term, and its reconstruction from them.
  have hdecomp : ∀ w : W, i₁ (p₁ w) + i₂ (p₂ w) = w := by
    intro w
    have := congrArg (fun φ : W ⟶ W => φ w) htot
    simpa using this
  -- Evaluating an equation `u ≫ v = w` of morphisms on an element.
  have key : ∀ {M N P : ModuleCat.{v} R} (u : M ⟶ N) (v : N ⟶ P) (w : M ⟶ P),
      u ≫ v = w → ∀ x, v (u x) = w x := by
    rintro _ _ _ u v w rfl x
    rfl
  have hfp₁ := key _ _ _ hf₁
  have hfp₂ := key _ _ _ hf₂
  have hgi₁ := key _ _ _ hg₁
  have hgi₂ : ∀ y : B₂, g (i₂ y) = -(β₂ y) := key _ _ _ hg₂
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · rw [ShortComplex.moduleCat_exact_iff]
    intro w hw
    have hβ : β₁ (p₁ w) = β₂ (p₂ w) := by
      have h0 : g (i₁ (p₁ w) + i₂ (p₂ w)) = 0 := by rw [hdecomp w]; exact hw
      rw [map_add, hgi₁, hgi₂] at h0
      rw [← sub_eq_zero, sub_eq_add_neg]
      exact h0
    obtain ⟨a, ha₁, ha₂⟩ := hmid _ _ hβ
    refine ⟨a, ?_⟩
    calc f a = i₁ (p₁ (f a)) + i₂ (p₂ (f a)) := (hdecomp (f a)).symm
      _ = i₁ (p₁ w) + i₂ (p₂ w) := by rw [hfp₁, hfp₂, ha₁, ha₂]
      _ = w := hdecomp w
  · rw [ModuleCat.mono_iff_injective]
    intro a a' haa
    have hz : a - a' = 0 := by
      refine hinj _ ?_ ?_
      · rw [map_sub, ← hfp₁, ← hfp₁, haa, sub_self]
      · rw [map_sub, ← hfp₂, ← hfp₂, haa, sub_self]
    exact sub_eq_zero.1 hz
  · rw [ModuleCat.epi_iff_surjective]
    intro z
    obtain ⟨x, y, hxy⟩ := hsurj z
    refine ⟨i₁ x + i₂ y, ?_⟩
    change g (i₁ x + i₂ y) = z
    rw [map_add, hgi₁, hgi₂, ← hxy, sub_eq_add_neg]

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, u, u})

section Sum

/-- **The sum of two global sections of the structure sheaf**, as a global section. The type of
global sections carries no additive structure of its own, so the sum in which [Stacks, Tag 0998]
asserts its vanishing locus to be closed is formed here by hand, from the sums of the values and
the additivity of restriction. -/
def addGlobalSection (g h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) :
    Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}) :=
  (Presheaf.globalSectionsEquivSections _).symm
    ⟨fun U ↦ globalSectionVal g U + globalSectionVal h U, fun {U V} k ↦ by
      change (X.O.obj.map k).hom (globalSectionVal g U + globalSectionVal h U) = _
      rw [map_add, globalSectionVal_map g k, globalSectionVal_map h k]⟩

/-- The value of the sum `g + h` over `U` is the sum of the values of `g` and `h` over `U`. -/
@[simp]
theorem globalSectionVal_addGlobalSection
    (g h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u})) (U : X.Cᵒᵖ) :
    globalSectionVal (addGlobalSection X g h) U =
      globalSectionVal g U + globalSectionVal h U := by
  simp [addGlobalSection, globalSectionVal]

end Sum

section Transition

variable (h h' : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))

/-- **The sections of `𝒪[1/f]` over an object are the localization of `𝒪(U)` away from the value
of `f` there**, for the canonical `Algebra` structure of a localization. This is the shape
instance search needs; `AlgebraicGeometry.RingedSite.isLocalizationAway_awayPresheaf` is the same
statement for the `Algebra` structure induced by the canonical ring map, and neither is reachable
from the other by unification because `awayMultiplicativeSubpresheaf` is not reducible. -/
instance isLocalizationAway_awayPresheaf_obj (U : X.Cᵒᵖ) :
    IsLocalization.Away (globalSectionVal h U) ((awayPresheaf h).obj U) :=
  inferInstanceAs (IsLocalization ((awayMultiplicativeSubpresheaf h).obj U)
    ((awayPresheaf h).obj U))

/-- If the value of `f` divides the value of `f'` over every object then every power of `f|_U`
becomes a unit in `𝒪(U)[1/f'|_U]`. -/
theorem isUnit_algebraMap_awayPresheaf
    (hdvd : ∀ U, globalSectionVal h U ∣ globalSectionVal h' U) (U : X.Cᵒᵖ)
    (s : (awayMultiplicativeSubpresheaf h).obj U) :
    IsUnit (algebraMap (X.O.obj.obj U) ((awayPresheaf h').obj U) (s : X.O.obj.obj U)) := by
  obtain ⟨n, hn⟩ := s.2
  rw [← hn, map_pow]
  exact IsUnit.pow n (IsLocalization.Away.isUnit_of_dvd
    (S := (awayPresheaf h').obj U) (globalSectionVal h' U) (hdvd U))

/-- **The comparison `𝒪(U)[1/f|_U] ⟶ 𝒪(U)[1/f'|_U]` over a single object, as a map of
`𝒪(U)`-algebras**, available because every power of `f|_U` is invertible in the target. -/
def awayPresheafTransitionAlgHom
    (hdvd : ∀ U, globalSectionVal h U ∣ globalSectionVal h' U) (U : X.Cᵒᵖ) :
    (awayPresheaf h).obj U →ₐ[X.O.obj.obj U] (awayPresheaf h').obj U :=
  IsLocalization.liftAlgHom (M := (awayMultiplicativeSubpresheaf h).obj U)
    (f := Algebra.ofId (X.O.obj.obj U) ((awayPresheaf h').obj U))
    (isUnit_algebraMap_awayPresheaf X h h' hdvd U)

/-- The comparison `𝒪(U)[1/f|_U] ⟶ 𝒪(U)[1/f'|_U]` sends the image of `x ∈ 𝒪(U)` to the image
of `x`. -/
@[simp]
theorem awayPresheafTransitionAlgHom_algebraMap
    (hdvd : ∀ U, globalSectionVal h U ∣ globalSectionVal h' U) (U : X.Cᵒᵖ)
    (x : X.O.obj.obj U) :
    awayPresheafTransitionAlgHom X h h' hdvd U
        (algebraMap (X.O.obj.obj U) ((awayPresheaf h).obj U) x) =
      algebraMap (X.O.obj.obj U) ((awayPresheaf h').obj U) x :=
  (awayPresheafTransitionAlgHom X h h' hdvd U).commutes x

/-- The comparison map carries the canonical image of a section of `𝒪` to its canonical
image. -/
@[simp]
theorem awayPresheafTransitionAlgHom_toAwayPresheaf
    (hdvd : ∀ U, globalSectionVal h U ∣ globalSectionVal h' U) (U : X.Cᵒᵖ)
    (x : X.O.obj.obj U) :
    awayPresheafTransitionAlgHom X h h' hdvd U (((toAwayPresheaf h).app U).hom x) =
      ((toAwayPresheaf h').app U).hom x :=
  awayPresheafTransitionAlgHom_algebraMap X h h' hdvd U x

/-- **The comparison `𝒪[1/f] ⟶ 𝒪[1/f']` of presheaves of rings.** Naturality holds because both
composites around a restriction square are maps out of a localization agreeing on `𝒪(U)`. -/
def awayPresheafTransition (hdvd : ∀ U, globalSectionVal h U ∣ globalSectionVal h' U) :
    awayPresheaf h ⟶ awayPresheaf h' where
  app U := CommRingCat.ofHom (awayPresheafTransitionAlgHom X h h' hdvd U).toRingHom
  naturality {U V} α := by
    apply CommRingCat.hom_ext
    apply IsLocalization.ringHom_ext (M := (awayMultiplicativeSubpresheaf h).obj U)
    apply RingHom.ext
    intro x
    have n₁ := congrArg (fun k : X.O.obj.obj U ⟶ (awayPresheaf h).obj V => k.hom x)
      ((toAwayPresheaf h).naturality α)
    have n₂ := congrArg (fun k : X.O.obj.obj U ⟶ (awayPresheaf h').obj V => k.hom x)
      ((toAwayPresheaf h').naturality α)
    simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] at n₁ n₂
    change (awayPresheafTransitionAlgHom X h h' hdvd V)
        (((awayPresheaf h).map α).hom (((toAwayPresheaf h).app U).hom x)) =
      ((awayPresheaf h').map α).hom
        ((awayPresheafTransitionAlgHom X h h' hdvd U) (((toAwayPresheaf h).app U).hom x))
    rw [← n₁, awayPresheafTransitionAlgHom_toAwayPresheaf,
      awayPresheafTransitionAlgHom_toAwayPresheaf, ← n₂]

open Stacks.PresheafOfModules.ChangeOfRings

/-- **The comparison `𝒪[1/f] ⟶ 𝒪[1/f']` of presheaves of `𝒪`-modules.** -/
def awayModulePresheafTransition
    (hdvd : ∀ U, globalSectionVal h U ∣ globalSectionVal h' U) :
    awayModulePresheaf X h ⟶ awayModulePresheaf X h' :=
  PresheafOfModules.homMk
    (Functor.whiskerRight (awayPresheafTransition X h h' hdvd)
      (forget₂ CommRingCat.{u} RingCat.{u} ⋙ forget₂ RingCat.{u} AddCommGrpCat.{u}))
    (fun U r m => by
      let r' : X.O.obj.obj U := r
      let m' : (awayPresheaf h).obj U := m
      change (awayPresheafTransitionAlgHom X h h' hdvd U)
          (((toAwayPresheaf h).app U).hom r' * m') =
        ((toAwayPresheaf h').app U).hom r' *
          (awayPresheafTransitionAlgHom X h h' hdvd U) m'
      rw [map_mul, awayPresheafTransitionAlgHom_toAwayPresheaf])

/-- Over every object the comparison map of presheaves of `𝒪`-modules is the algebra map
`AlgebraicGeometry.RingedSite.awayPresheafTransitionAlgHom`. -/
theorem awayModulePresheafTransition_app_apply
    (hdvd : ∀ U, globalSectionVal h U ∣ globalSectionVal h' U) (U : X.Cᵒᵖ)
    (m : (awayPresheaf h).obj U) :
    ((awayModulePresheafTransition X h h' hdvd).app U).hom m =
      awayPresheafTransitionAlgHom X h h' hdvd U m := rfl

/-- **Two composites of comparison maps out of `𝒪[1/f]` agree**, a map out of a sectionwise
localization being determined by its restriction along `𝒪 ⟶ 𝒪[1/f]`. This is what makes the
sequence of the sum a complex. -/
theorem awayModulePresheafTransition_comp_eq
    (h₁ h₂ h₃ : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (d₁ : ∀ U, globalSectionVal h U ∣ globalSectionVal h₁ U)
    (d₁' : ∀ U, globalSectionVal h₁ U ∣ globalSectionVal h₃ U)
    (d₂ : ∀ U, globalSectionVal h U ∣ globalSectionVal h₂ U)
    (d₂' : ∀ U, globalSectionVal h₂ U ∣ globalSectionVal h₃ U) :
    awayModulePresheafTransition X h h₁ d₁ ≫ awayModulePresheafTransition X h₁ h₃ d₁' =
      awayModulePresheafTransition X h h₂ d₂ ≫ awayModulePresheafTransition X h₂ h₃ d₂' := by
  refine PresheafOfModules.hom_ext fun U => ModuleCat.hom_ext (LinearMap.ext fun m => ?_)
  have key : (awayPresheafTransitionAlgHom X h₁ h₃ d₁' U).toRingHom.comp
        (awayPresheafTransitionAlgHom X h h₁ d₁ U).toRingHom =
      (awayPresheafTransitionAlgHom X h₂ h₃ d₂' U).toRingHom.comp
        (awayPresheafTransitionAlgHom X h h₂ d₂ U).toRingHom := by
    apply IsLocalization.ringHom_ext (M := (awayMultiplicativeSubpresheaf h).obj U)
    apply RingHom.ext
    intro x
    simp
  exact congrArg (fun k : (awayPresheaf h).obj U →+* (awayPresheaf h₃).obj U => k m) key

end Transition

section AddComplex

variable (ha hb hh hhf hhg hhfg : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (eh : ∀ U, globalSectionVal ha U + globalSectionVal hb U = globalSectionVal hh U)
  (ehf : ∀ U, globalSectionVal hhf U = globalSectionVal hh U * globalSectionVal ha U)
  (ehg : ∀ U, globalSectionVal hhg U = globalSectionVal hh U * globalSectionVal hb U)
  (ehfg : ∀ U, globalSectionVal hhfg U =
    globalSectionVal hh U * globalSectionVal ha U * globalSectionVal hb U)

include ehf in
/-- `h` divides `ha`. -/
theorem dvd_globalSectionVal_mulLeft (U : X.Cᵒᵖ) :
    globalSectionVal hh U ∣ globalSectionVal hhf U :=
  ⟨globalSectionVal ha U, ehf U⟩

include ehg in
/-- `h` divides `hb`. -/
theorem dvd_globalSectionVal_mulRight (U : X.Cᵒᵖ) :
    globalSectionVal hh U ∣ globalSectionVal hhg U :=
  ⟨globalSectionVal hb U, ehg U⟩

include ehf ehfg in
/-- `ha` divides `hab`. -/
theorem dvd_globalSectionVal_mulLeft_mul (U : X.Cᵒᵖ) :
    globalSectionVal hhf U ∣ globalSectionVal hhfg U :=
  ⟨globalSectionVal hb U, by rw [ehfg, ehf]⟩

include ehg ehfg in
/-- `hb` divides `hab`. -/
theorem dvd_globalSectionVal_mulRight_mul (U : X.Cᵒᵖ) :
    globalSectionVal hhg U ∣ globalSectionVal hhfg U :=
  ⟨globalSectionVal ha U, by rw [ehfg, ehg]; ring⟩

/-- The composite of the two maps of the sequence of the sum vanishes. -/
theorem awayModulePresheafAddComplex_zero :
    biprod.lift (awayModulePresheafTransition X hh hhf
          (dvd_globalSectionVal_mulLeft X ha hh hhf ehf))
        (awayModulePresheafTransition X hh hhg
          (dvd_globalSectionVal_mulRight X hb hh hhg ehg)) ≫
      biprod.desc (awayModulePresheafTransition X hhf hhfg
          (dvd_globalSectionVal_mulLeft_mul X ha hb hh hhf hhfg ehf ehfg))
        (-awayModulePresheafTransition X hhg hhfg
          (dvd_globalSectionVal_mulRight_mul X ha hb hh hhg hhfg ehg ehfg)) = 0 := by
  rw [biprod.lift_desc, Preadditive.comp_neg,
    awayModulePresheafTransition_comp_eq X hh hhf hhg hhfg
      (dvd_globalSectionVal_mulLeft X ha hh hhf ehf)
      (dvd_globalSectionVal_mulLeft_mul X ha hb hh hhf hhfg ehf ehfg)
      (dvd_globalSectionVal_mulRight X hb hh hhg ehg)
      (dvd_globalSectionVal_mulRight_mul X ha hb hh hhg hhfg ehg ehfg),
    add_neg_cancel]

/-- **The sequence `0 → 𝒪[1/h] → 𝒪[1/ha] ⊕ 𝒪[1/hb] → 𝒪[1/hab] → 0` of presheaves of
`𝒪`-modules.** -/
def awayModulePresheafAddComplex :
    ShortComplex (PresheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj) :=
  ShortComplex.mk _ _ (awayModulePresheafAddComplex_zero X ha hb hh hhf hhg hhfg ehf ehg ehfg)

include eh in
/-- **The sequence of the sum is short exact over every object of the site.** Over `U` it is the
sequence `0 → 𝒪(U)_h → 𝒪(U)_{ha} × 𝒪(U)_{hb} → 𝒪(U)_{hab} → 0` of
`StacksFrontier/RingTheory/Localization/Glueing/AwaySum.lean`, the four modules of sections being
localizations of `𝒪(U)` away from the four values and the four comparison maps being
`𝒪(U)`-algebra maps. -/
theorem shortExact_awayModulePresheafAddComplex_map (U : X.Cᵒᵖ) :
    ((awayModulePresheafAddComplex X ha hb hh hhf hhg hhfg ehf ehg ehfg).map
      (PresheafOfModules.evaluation
        ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj U)).ShortExact := by
  set e := PresheafOfModules.evaluation ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj U with he
  set B₁ := awayModulePresheaf X hhf with hB₁
  set B₂ := awayModulePresheaf X hhg with hB₂
  set α₁ := awayModulePresheafTransition X hh hhf
    (dvd_globalSectionVal_mulLeft X ha hh hhf ehf) with hα₁
  set α₂ := awayModulePresheafTransition X hh hhg
    (dvd_globalSectionVal_mulRight X hb hh hhg ehg) with hα₂
  set β₁ := awayModulePresheafTransition X hhf hhfg
    (dvd_globalSectionVal_mulLeft_mul X ha hb hh hhf hhfg ehf ehfg) with hβ₁
  set β₂ := awayModulePresheafTransition X hhg hhfg
    (dvd_globalSectionVal_mulRight_mul X ha hb hh hhg hhfg ehg ehfg) with hβ₂
  -- The four localizations of `𝒪(U)`, at the four values.
  have iF : IsLocalization.Away
      (globalSectionVal hh U * globalSectionVal ha U) ((awayPresheaf hhf).obj U) := by
    rw [← ehf U]; infer_instance
  have iG : IsLocalization.Away
      (globalSectionVal hh U * globalSectionVal hb U) ((awayPresheaf hhg).obj U) := by
    rw [← ehg U]; infer_instance
  have iFG : IsLocalization.Away
      (globalSectionVal hh U * globalSectionVal ha U * globalSectionVal hb U)
      ((awayPresheaf hhfg).obj U) := by
    rw [← ehfg U]; infer_instance
  refine ShortComplex.shortExact_of_biprodData
    (e.map (biprod.inl : B₁ ⟶ B₁ ⊞ B₂)) (e.map (biprod.inr : B₂ ⟶ B₁ ⊞ B₂))
    (e.map (biprod.fst : B₁ ⊞ B₂ ⟶ B₁)) (e.map (biprod.snd : B₁ ⊞ B₂ ⟶ B₂))
    (e.map α₁) (e.map α₂) (e.map β₁) (e.map β₂)
    (e.map (biprod.lift α₁ α₂)) (e.map (biprod.desc β₁ (-β₂)))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [← e.map_comp, ← e.map_comp, ← e.map_add, biprod.total, e.map_id]
  · rw [← e.map_comp, biprod.lift_fst]
  · rw [← e.map_comp, biprod.lift_snd]
  · rw [← e.map_comp, biprod.inl_desc]
  · rw [← e.map_comp, biprod.inr_desc, e.map_neg]
  · exact fun a h₁ h₂ => AwaySum.eq_zero_of_eq_zero (eh U)
      (awayPresheafTransitionAlgHom X hh hhf
        (dvd_globalSectionVal_mulLeft X ha hh hhf ehf) U)
      (awayPresheafTransitionAlgHom X hh hhg
        (dvd_globalSectionVal_mulRight X hb hh hhg ehg) U) h₁ h₂
  · exact fun x y hxy => AwaySum.exists_eq_of_eq (eh U)
      (awayPresheafTransitionAlgHom X hh hhf
        (dvd_globalSectionVal_mulLeft X ha hh hhf ehf) U)
      (awayPresheafTransitionAlgHom X hh hhg
        (dvd_globalSectionVal_mulRight X hb hh hhg ehg) U)
      (awayPresheafTransitionAlgHom X hhf hhfg
        (dvd_globalSectionVal_mulLeft_mul X ha hb hh hhf hhfg ehf ehfg) U)
      (awayPresheafTransitionAlgHom X hhg hhfg
        (dvd_globalSectionVal_mulRight_mul X ha hb hh hhg hhfg ehg ehfg) U) hxy
  · exact fun z => AwaySum.exists_sub_eq (eh U)
      (awayPresheafTransitionAlgHom X hhf hhfg
        (dvd_globalSectionVal_mulLeft_mul X ha hb hh hhf hhfg ehf ehfg) U)
      (awayPresheafTransitionAlgHom X hhg hhfg
        (dvd_globalSectionVal_mulRight_mul X ha hb hh hhg hhfg ehg ehfg) U) z

include eh in
/-- **The sequence `0 → 𝒪[1/h] → 𝒪[1/ha] ⊕ 𝒪[1/hb] → 𝒪[1/hab] → 0` of presheaves of
`𝒪`-modules is short exact.** -/
theorem shortExact_awayModulePresheafAddComplex :
    (awayModulePresheafAddComplex X ha hb hh hhf hhg hhfg ehf ehg ehfg).ShortExact :=
  PresheafOfModules.shortExact_of_objectwise _
    (shortExact_awayModulePresheafAddComplex_map X ha hb hh hhf hhg hhfg eh ehf ehg ehfg)

/-- Sheafification of presheaves of `𝒪`-modules is additive: it is a left adjoint, so preserves
zero morphisms, and it preserves finite limits. -/
instance additive_sheafification :
    (PresheafOfModules.sheafification
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)).Additive := by
  have : PreservesLimitsOfShape (Discrete WalkingPair)
      (PresheafOfModules.sheafification
        (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj)) := inferInstance
  exact Functor.additive_of_preserves_binary_products _

/-- **The sequence `0 → 𝒪_h → 𝒪_{ha} ⊕ 𝒪_{hb} → 𝒪_{hab} → 0` of sheaves of `𝒪`-modules**, as the
sheafification of the sequence of presheaves. -/
def awayModuleAddComplex :
    ShortComplex (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  (awayModulePresheafAddComplex X ha hb hh hhf hhg hhfg ehf ehg ehfg).map
    (PresheafOfModules.sheafification (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj))

include eh in
/-- **The sequence `0 → 𝒪_h → 𝒪_{ha} ⊕ 𝒪_{hb} → 𝒪_{hab} → 0` of sheaves of `𝒪`-modules is short
exact.** This is the short exact sequence [Stacks, Tag 0998] uses to prove that its vanishing
locus is closed under addition. -/
theorem shortExact_awayModuleAddComplex :
    (awayModuleAddComplex X ha hb hh hhf hhg hhfg ehf ehg ehfg).ShortExact :=
  (shortExact_awayModulePresheafAddComplex X ha hb hh hhf hhg hhfg eh ehf ehg ehfg).map_of_exact _

/-- The first term of the sequence is `𝒪_h`. -/
def awayModuleAddComplexX₁Iso :
    (awayModuleAddComplex X ha hb hh hhf hhg hhfg ehf ehg ehfg).X₁ ≅ awayModule X hh :=
  awaySheafificationIsoAwayModule X hh

/-- Sheaves of `𝒪`-modules have binary biproducts, being a preadditive category with binary
products. Instance search does not reach this on its own within its budget. (The base's
`AlgebraicGeometry.RingedSite.hasBinaryBiproducts_sheafOfModules` of
`StacksFrontier/AlgebraicGeometry/Duality/EffectiveCartierIdealDualTensor.lean` is a
`local instance`, so it is not available here, and its name is taken.) -/
instance hasBinaryBiproducts_sheafOfModules_ringSheaf :
    HasBinaryBiproducts (SheafOfModules.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :=
  HasBinaryBiproducts.of_hasBinaryProducts

/-- The middle term of the sequence is `𝒪_{ha} ⊕ 𝒪_{hb}`. -/
def awayModuleAddComplexX₂Iso :
    (awayModuleAddComplex X ha hb hh hhf hhg hhfg ehf ehg ehfg).X₂ ≅
      awayModule X hhf ⊞ awayModule X hhg :=
  haveI : HasBinaryBiproduct
      ((PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj (awayModulePresheaf X hhf))
      ((PresheafOfModules.sheafification
        (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).obj (awayModulePresheaf X hhg)) :=
    HasBinaryBiproducts.has_binary_biproduct _ _
  Functor.biprodIsoOfAdditiveAux
      (PresheafOfModules.sheafification (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj))
      (awayModulePresheaf X hhf) (awayModulePresheaf X hhg) ≪≫
    biprod.mapIso (awaySheafificationIsoAwayModule X hhf) (awaySheafificationIsoAwayModule X hhg)

/-- The last term of the sequence is `𝒪_{hab}`. -/
def awayModuleAddComplexX₃Iso :
    (awayModuleAddComplex X ha hb hh hhf hhg hhfg ehf ehg ehfg).X₃ ≅ awayModule X hhfg :=
  awaySheafificationIsoAwayModule X hhfg

end AddComplex

section Additivity

attribute [local instance] HasDerivedCategory.standard

/-- **Vanishing of the derived internal Hom into `K` on the last two terms of a short exact
sequence of sheaves of `𝒪`-modules forces it on the first.** The sequence, placed in degree
zero, defines a distinguished triangle in `D(𝒪)` whose vertices are its three terms, so this is
`AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_obj₁_of_distTriang` at that triangle.

This is the step by which [Stacks, Tag 0998] obtains additivity of its vanishing locus: the
source's input is the short exact sequence
`0 → 𝒪_{f + g} → 𝒪_{f(f + g)} ⊕ 𝒪_{g(f + g)} → 𝒪_{gf(f + g)} → 0`, and what it then does with
it is this lemma together with
`AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_biprod` for the middle term. -/
theorem isZero_derivedSheafHom_of_shortExact
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (S : ShortComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hS : S.ShortExact)
    (h₂ : IsZero (((derivedSheafHomBifunctor X).obj
      (op ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj S.X₂))).obj K))
    (h₃ : IsZero (((derivedSheafHomBifunctor X).obj
      (op ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj S.X₃))).obj K)) :
    IsZero (((derivedSheafHomBifunctor X).obj
      (op ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj S.X₁))).obj K) :=
  isZero_derivedSheafHom_obj₁_of_distTriang X K _
    (DerivedCategory.triangleOfSES_distinguished (hS.map_of_exact
      (HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) 0)))
    h₂ h₃

/-- **The vanishing locus is closed under multiplication, at the tag's own membership
condition.** If `f` lies in the vanishing locus of `K` then so does `gf`, for every global
section `g` of `𝒪`.

This is `AlgebraicGeometry.RingedSite.isRightOrthogonalAway_mulGlobalSection` read through the
implication (1) ⇒ (2) of [Stacks, Tag 0997],
`AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_awayRestrictScalars_of_isZero`, which turns
membership into right orthogonality; the converse direction is
`AlgebraicGeometry.RingedSite.MemVanishingIdeal.of_isRightOrthogonalAway`.

It is stated here rather than beside `isRightOrthogonalAway_mulGlobalSection` in
`VanishingIdeal.lean` because it is the one declaration of that file needing
`VanishingCriterionCoextension.lean`, and that import reaches `Completion.lean`, whose consumer
`AlgebraicGeometry.RingedSite.completionFunctor_obj_eq_derivedSheafHom_flip` of
`KoszulLimitFormula.lean` then fails to discharge its `omit` clause. -/
@[stacks 0998 "closure under multiplication, at the membership condition"]
theorem memVanishingIdeal_mulGlobalSection_of_memVanishingIdeal
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (g h : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (H : MemVanishingIdeal X K h) :
    MemVanishingIdeal X K (mulGlobalSection X g h) :=
  memVanishingIdeal_mulGlobalSection X K g h
    (isZero_derivedSheafHom_awayRestrictScalars_of_isZero X h K H)

/-- **The vanishing locus is closed under addition.** If `R𝑆heafHom_𝒪(𝒪_a, K)` and
`R𝑆heafHom_𝒪(𝒪_b, K)` vanish then so does `R𝑆heafHom_𝒪(𝒪_{a + b}, K)`.

Write `h = a + b`. Multiplicativity — `isRightOrthogonalAway_mulGlobalSection` together with the
implication (1) ⇒ (2) of [Stacks, Tag 0997], `isZero_derivedSheafHom_awayRestrictScalars_of_isZero`
— puts the three products `ha`, `hb` and `hab` in the locus, and the short exact sequence
`0 → 𝒪_h → 𝒪_{ha} ⊕ 𝒪_{hb} → 𝒪_{hab} → 0` of
`AlgebraicGeometry.RingedSite.shortExact_awayModuleAddComplex` then puts `h` there by the
dévissage `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_of_shortExact`, the middle term
being handled by `AlgebraicGeometry.RingedSite.isZero_derivedSheafHom_biprod`.

Nothing is assumed of `K`, of `a` or of `b`. -/
@[stacks 0998 "closure under addition"]
theorem memVanishingIdeal_addGlobalSection
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a b : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (Ha : MemVanishingIdeal X K a) (Hb : MemVanishingIdeal X K b) :
    MemVanishingIdeal X K (addGlobalSection X a b) := by
  set hh := addGlobalSection X a b with hhdef
  set hhf := mulGlobalSection X hh a with hhfdef
  set hhg := mulGlobalSection X hh b with hhgdef
  set hhfg := mulGlobalSection X hhf b with hhfgdef
  have eh : ∀ U, globalSectionVal a U + globalSectionVal b U = globalSectionVal hh U := by
    intro U; rw [hhdef, globalSectionVal_addGlobalSection]
  have ehf : ∀ U, globalSectionVal hhf U = globalSectionVal hh U * globalSectionVal a U := by
    intro U; rw [hhfdef, globalSectionVal_mulGlobalSection]
  have ehg : ∀ U, globalSectionVal hhg U = globalSectionVal hh U * globalSectionVal b U := by
    intro U; rw [hhgdef, globalSectionVal_mulGlobalSection]
  have ehfg : ∀ U, globalSectionVal hhfg U =
      globalSectionVal hh U * globalSectionVal a U * globalSectionVal b U := by
    intro U; rw [hhfgdef, globalSectionVal_mulGlobalSection, ehf]
  -- Multiplicativity, at the three products the sequence has.
  have oa : IsRightOrthogonalAway X K a :=
    isZero_derivedSheafHom_awayRestrictScalars_of_isZero X a K Ha
  have ob : IsRightOrthogonalAway X K b :=
    isZero_derivedSheafHom_awayRestrictScalars_of_isZero X b K Hb
  have m₁ : MemVanishingIdeal X K hhf := memVanishingIdeal_mulGlobalSection X K hh a oa
  have m₂ : MemVanishingIdeal X K hhg := memVanishingIdeal_mulGlobalSection X K hh b ob
  have m₃ : MemVanishingIdeal X K hhfg := memVanishingIdeal_mulGlobalSection X K hhf b ob
  -- The dévissage along the short exact sequence of the sum.
  have hS := shortExact_awayModuleAddComplex X a b hh hhf hhg hhfg eh ehf ehg ehfg
  have h₃ := (isZero_derivedSheafHom_iff_of_iso X K
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).mapIso
      (awayModuleAddComplexX₃Iso X a b hh hhf hhg hhfg ehf ehg ehfg))).2 m₃
  have hbip : IsZero (((derivedSheafHomBifunctor X).obj
      (op ((DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj
        (awayModule X hhf ⊞ awayModule X hhg)))).obj K) :=
    (isZero_derivedSheafHom_iff_of_iso X K
      (Functor.biprodIsoOfAdditiveAux (DerivedCategory.singleFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0)
        (awayModule X hhf) (awayModule X hhg))).2
      (isZero_derivedSheafHom_biprod X K _ _ m₁ m₂)
  have h₂ := (isZero_derivedSheafHom_iff_of_iso X K
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).mapIso
      (awayModuleAddComplexX₂Iso X a b hh hhf hhg hhfg ehf ehg ehfg))).2 hbip
  exact (isZero_derivedSheafHom_iff_of_iso X K
    ((DerivedCategory.singleFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).mapIso
      (awayModuleAddComplexX₁Iso X a b hh hhf hhg hhfg ehf ehg ehfg))).1
    (isZero_derivedSheafHom_of_shortExact X K _ hS h₂ h₃)

/-- **Right orthogonality to `D(𝒪_f)` is closed under addition as well**, by the implication
(1) ⇒ (2) of [Stacks, Tag 0997] applied to
`AlgebraicGeometry.RingedSite.memVanishingIdeal_addGlobalSection`. -/
theorem isRightOrthogonalAway_addGlobalSection
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (a b : Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
    (Ha : MemVanishingIdeal X K a) (Hb : MemVanishingIdeal X K b) :
    IsRightOrthogonalAway X K (addGlobalSection X a b) :=
  isZero_derivedSheafHom_awayRestrictScalars_of_isZero X (addGlobalSection X a b) K
    (memVanishingIdeal_addGlobalSection X K a b Ha Hb)

/-- **Closure of the vanishing locus under addition, for sections over an arbitrary object of the
site.** A section of `𝒪` over `U` is a global section of the structure sheaf of the localized
ringed site `AlgebraicGeometry.RingedSite.over X U`, on which
`AlgebraicGeometry.RingedSite.memVanishingIdeal_addGlobalSection` applies as it stands: that
theorem assumes nothing of the ringed site, and a slice of a ringed site is again one.

This is the form in which the local-generation argument of [Stacks, Tag 099F] consumes
additivity, a local section of a finitely generated ideal sheaf being only locally an
`𝒪`-combination of the generators. -/
theorem memVanishingIdeal_over_addGlobalSection (U : X.C)
    (K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (over X U).O)))
    (a b : Presheaf.globalSections ((over X U).O.obj ⋙ forget CommRingCat.{u}))
    (Ha : MemVanishingIdeal (over X U) K a) (Hb : MemVanishingIdeal (over X U) K b) :
    MemVanishingIdeal (over X U) K (addGlobalSection (over X U) a b) :=
  memVanishingIdeal_addGlobalSection (over X U) K a b Ha Hb

end Additivity

end AlgebraicGeometry.RingedSite

end
