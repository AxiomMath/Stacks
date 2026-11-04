module

public import StacksFrontier.AlgebraicGeometry.FormsTrace.AffinePullback
public import StacksFrontier.AlgebraicGeometry.FormsTrace.Glue
public import StacksFrontier.AlgebraicGeometry.FormsTrace.FramedBasis
public import StacksFrontier.AlgebraicGeometry.FormsTrace.Rule
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.BaseChange
public import StacksFrontier.RingTheory.FormsTrace.ExistenceTransport
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis

/-!
# Uniqueness of trace maps on forms

This file proves the uniqueness half of Stacks, Lemma 0FLB: a rule
`f ↦ Θ^p_{Y/X} : f_*Ω^p_{Y/ℤ} ⟶ Ω^p_{X/ℤ}` on finite syntomic morphisms satisfying condition (1)
(composition with `Ω^p_X ⊗ f_*𝒪_Y → f_*Ω^p_Y` is `id ⊗ Trace_f`) and condition (2) (compatibility
with base change) is unique.

The source's proof: the question is local on `X`, so we may assume `X` affine and `Y → X` the
base change of a universal chart, along which (2) pulls the maps back; over the universal chart
the maps are determined by (1), since the discriminant is a nonzerodivisor on the forms of the
base and a power of it kills the relative differentials.

Concretely, two such rules agree on every framed affine open `U` of `X`
(`Stacks.FormsTrace.isBasis_framedOpens`), which form a basis. If `Γ(Y, f⁻¹U) = 0` there is
nothing to prove. Otherwise a frame `F` of `B = Γ(Y, f⁻¹U)` over `A = Γ(X, U)` presents `B/A` as
the base change of the base change `S/R` of the universal family to a polynomial ring `R` over a
universal chart, along a surjection `R → A`. Then:

* on `g : Spec S ⟶ Spec R` condition (1) on global sections says that the two families of maps of
  rings are trace maps on forms (`Stacks.FormsTrace.IsFormsTrace`); transported to `S/R`, where
  the discriminant is a nice element, they coincide
  (`AlgebraicGeometry.FormsTraceRule.app_top_eq_of_isNiceElement`);
* condition (2) for the cartesian square `Spec B → Spec S` over `Spec A → Spec R` transfers this
  to `Spec B → Spec A`, every form of `B` being the restriction of a form of `S`
  (`AlgebraicGeometry.FormsTraceRule.app_eq_of_isPullback_of_surjective`);
* condition (2) for the cartesian square `Spec B → Y` over `Spec A → X` given by the open
  immersions of `U` and `f⁻¹U` transfers it to `f` over `U`, pulling forms back along
  `Spec A → X` being injective over `U`
  (`AlgebraicGeometry.FormsTraceRule.app_eq_of_isPullback_of_injective`).

## Main results

* `Stacks.FormsTrace.IsFormsTrace.eq_of_ringEquiv`: trace maps on forms are unique over a pair
  isomorphic to one with a nice element.
* `AlgebraicGeometry.isPullback_fromSpec`: the cartesian square of an affine open and its preimage.
* `AlgebraicGeometry.sectionsFamily`, `AlgebraicGeometry.isFormsTrace_sectionsFamily`: the
  ring-level maps of a rule over an affine open, which are trace maps on forms under (1).
* `AlgebraicGeometry.FormsTraceRule.eq_of_isTrace_of_isBaseChange`: uniqueness (Stacks 0FLB).

## References

* [Stacks Project, Tag 0FLB](https://stacks.math.columbia.edu/tag/0FLB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped nonZeroDivisors

universe u

namespace Stacks.FormsTrace

section RingEquiv

variable {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
  [Algebra A B] [Algebra A' B']

/-- The pull-back of forms along a bijective ring map is injective: composing with the pull-back
along the inverse gives the identity. -/
theorem formsMap_injective_of_bijective {R R' : Type u} [CommRing R] [CommRing R'] [Algebra R R']
    (h : Function.Bijective (algebraMap R R')) (p : ℕ) :
    Function.Injective (formsMap R R' p) := by
  let e : R ≃+* R' := RingEquiv.ofBijective (algebraMap R R') h
  let : Algebra R' R := e.symm.toRingHom.toAlgebra
  have : IsScalarTower R R' R :=
    IsScalarTower.of_algebraMap_eq fun r => (e.symm_apply_apply r).symm
  intro x y hxy
  have h2 := congrArg (formsMap R' R p) hxy
  rwa [formsMap_formsMap, formsMap_formsMap, formsMap_self, formsMap_self] at h2

/-- **Uniqueness of trace maps on forms transports along isomorphisms of ring maps.** Let
`eA : A ≅ A'` and `eB : B ≅ B'` be ring isomorphisms compatible with finite projective ring maps
`A → B` and `A' → B'`, and let `h` be a nice element for `B/A`. Then two families on the forms of
`B'` with property (1) of Stacks, Lemma 0FLB are equal. -/
theorem IsFormsTrace.eq_of_ringEquiv (eA : A ≃+* A') (eB : B ≃+* B')
    (hcomm : ∀ a, eB (algebraMap A B a) = algebraMap A' B' (eA a))
    [Module.Finite A B] [Module.Projective A B] [Module.Finite A' B'] [Module.Projective A' B']
    {h : A} (hh : IsNiceElement A B h)
    {Θ₁ Θ₂ : ∀ p : ℕ, ⋀[B']^p Ω[B'⁄ℤ] →ₗ[A'] ⋀[A']^p Ω[A'⁄ℤ]}
    (h₁ : IsFormsTrace A' B' Θ₁) (h₂ : IsFormsTrace A' B' Θ₂) : Θ₁ = Θ₂ := by
  let : Algebra A A' := eA.toRingHom.toAlgebra
  let : Algebra A' A := eA.symm.toRingHom.toAlgebra
  let : Algebra B B' := eB.toRingHom.toAlgebra
  let : Algebra B' B := eB.symm.toRingHom.toAlgebra
  let : Algebra A B' := ((algebraMap A' B').comp eA.toRingHom).toAlgebra
  let : Algebra A' B := ((algebraMap A B).comp eA.symm.toRingHom).toAlgebra
  have : IsScalarTower A A' B' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have : IsScalarTower A B B' := IsScalarTower.of_algebraMap_eq fun a => (hcomm a).symm
  have : IsScalarTower A A' A :=
    IsScalarTower.of_algebraMap_eq fun a => (eA.symm_apply_apply a).symm
  have : IsScalarTower A' A A' :=
    IsScalarTower.of_algebraMap_eq fun a => (eA.apply_symm_apply a).symm
  have : IsScalarTower B' B B' :=
    IsScalarTower.of_algebraMap_eq fun b => (eB.apply_symm_apply b).symm
  have hB (p : ℕ) (a : A) (x : ⋀[B]^p Ω[B⁄ℤ]) :
      formsMap B B' p (a • x) = eA a • formsMap B B' p x := by
    rw [← algebraMap_smul B a x, map_smulₛₗ]
    show eB (algebraMap A B a) • _ = _
    rw [hcomm, algebraMap_smul]
  have hA (p : ℕ) (a' : A') (y : ⋀[A']^p Ω[A'⁄ℤ]) :
      formsMap A' A p (a' • y) = eA.symm a' • formsMap A' A p y :=
    map_smulₛₗ _ a' y
  let conj : (∀ p : ℕ, ⋀[B']^p Ω[B'⁄ℤ] →ₗ[A'] ⋀[A']^p Ω[A'⁄ℤ]) →
      ∀ p : ℕ, ⋀[B]^p Ω[B⁄ℤ] →ₗ[A] ⋀[A]^p Ω[A⁄ℤ] := fun Θ p =>
    { toFun := fun x => formsMap A' A p (Θ p (formsMap B B' p x))
      map_add' := fun x y => by simp only [map_add]
      map_smul' := fun a x => by
        show formsMap A' A p (Θ p (formsMap B B' p (a • x))) =
          a • formsMap A' A p (Θ p (formsMap B B' p x))
        rw [hB, map_smul, hA, RingEquiv.symm_apply_apply] }
  have hconj : ∀ Θ, IsFormsTrace A' B' Θ → IsFormsTrace A B (conj Θ) := by
    intro Θ hΘ p b ω
    show formsMap A' A p (Θ p (formsMap B B' p (b • formsMap A B p ω))) = _
    rw [map_smulₛₗ, formsMap_formsMap (A := A) (B := B) (C := B'),
      ← formsMap_formsMap (A := A) (B := A') (C := B')]
    show formsMap A' A p (Θ p (eB b • formsMap A' B' p (formsMap A A' p ω))) = _
    rw [hΘ, hA, formsMap_formsMap (A := A) (B := A') (C := A), formsMap_self,
      trace_ringEquiv eA eB hcomm, RingEquiv.symm_apply_apply]
  have heq := (hconj Θ₁ h₁).eq_of_isNiceElement hh (hconj Θ₂ h₂)
  funext p
  refine LinearMap.ext fun x => ?_
  have hx : formsMap B B' p (formsMap B' B p x) = x := by
    rw [formsMap_formsMap, formsMap_self]
  simpa only [conj, LinearMap.coe_mk, AddHom.coe_mk, hx, formsMap_formsMap (A := A') (B := A)
    (C := A'), formsMap_self] using
    congrArg (fun Θ => formsMap A A' p (Θ p (formsMap B' B p x))) heq

end RingEquiv

end Stacks.FormsTrace

namespace AlgebraicGeometry

/-- **The cartesian square of an affine open and its preimage**: for affine opens `U ⊆ X` and
`f⁻¹U ⊆ Y`, the square `Spec Γ(Y, f⁻¹U) → Y` over `Spec Γ(X, U) → X` (the canonical open
immersions) with vertical maps `f` and `Spec(f.app U)` is cartesian. -/
theorem isPullback_fromSpec {X Y : Scheme.{u}} (f : Y ⟶ X) {U : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen (f ⁻¹ᵁ U)) :
    IsPullback hV.fromSpec (Spec.map (f.app U)) f hU.fromSpec := by
  have hsq : Spec.map (f.app U) ≫ hU.isoSpec.inv = hV.isoSpec.inv ≫ f ∣_ U := by
    rw [← cancel_mono U.ι, Category.assoc, Category.assoc, morphismRestrict_ι]
    have h := IsAffineOpen.SpecMap_appLE_fromSpec f hU hV le_rfl
    rwa [← Scheme.Hom.app_eq_appLE] at h
  have s : IsPullback hV.isoSpec.inv (Spec.map (f.app U)) (f ∣_ U) hU.isoSpec.inv :=
    IsPullback.of_horiz_isIso ⟨hsq.symm⟩
  exact s.paste_horiz (isPullback_morphismRestrict f U).flip

namespace FormsTraceRule

variable {Θ Θ' : FormsTraceRule.{u}}

/-- **Transferring equality along a base change, surjective case.** If `Θ`, `Θ'` satisfy
condition (2), agree on `f` over `U`, and every form of `Y'` over `f'⁻¹U'` is the restriction of
the pull-back of a form of `Y` over `f⁻¹U`, they agree on the base change `f'` over `U'`. -/
theorem app_eq_of_isPullback_of_surjective (h₂ : Θ.IsBaseChange) (h₂' : Θ'.IsBaseChange)
    {X Y X' Y' : Scheme.{u}} (f : Y ⟶ X) (f' : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (sq : IsPullback b f' f a) [IsFinite f] [IsFinite f'] (hf : Syntomic f) (hf' : Syntomic f')
    (p : ℕ) (U : X.Opens) (U' : X'.Opens) (hU : U' ≤ a ⁻¹ᵁ U)
    (heq : ∀ η : Γ(Scheme.absoluteDifferentialForms Y p, f ⁻¹ᵁ U),
      (Θ f hf p).app U η = (Θ' f hf p).app U η)
    (hsurj : ∀ ζ : Γ(Scheme.absoluteDifferentialForms Y' p, f' ⁻¹ᵁ U'), ∃ η,
      (Scheme.absoluteDifferentialForms Y' p).presheaf.map
        (homOfLE (AlgebraicGeometry.preimage_le_preimage_of_comm sq.w.symm hU)).op
        (b.absoluteFormsPullback p (f ⁻¹ᵁ U) η) = ζ)
    (ζ : Γ(Scheme.absoluteDifferentialForms Y' p, f' ⁻¹ᵁ U')) :
    (Θ f' hf' p).app U' ζ = (Θ' f' hf' p).app U' ζ := by
  obtain ⟨η, rfl⟩ := hsurj ζ
  rw [h₂ f f' a b sq hf hf' p U U' hU η, h₂' f f' a b sq hf hf' p U U' hU η]
  exact congrArg (fun z => (Scheme.absoluteDifferentialForms X' p).presheaf.map (homOfLE hU).op
    (a.absoluteFormsPullback p U z)) (heq η)

/-- **Transferring equality along a base change, injective case.** If `Θ`, `Θ'` satisfy
condition (2) and agree on the base change `f'` over `U'`, and the pull-back of forms of `X` over
`U` to forms of `X'` over `U'` is injective, they agree on `f` over `U`. -/
theorem app_eq_of_isPullback_of_injective (h₂ : Θ.IsBaseChange) (h₂' : Θ'.IsBaseChange)
    {X Y X' Y' : Scheme.{u}} (f : Y ⟶ X) (f' : Y' ⟶ X') (a : X' ⟶ X) (b : Y' ⟶ Y)
    (sq : IsPullback b f' f a) [IsFinite f] [IsFinite f'] (hf : Syntomic f) (hf' : Syntomic f')
    (p : ℕ) (U : X.Opens) (U' : X'.Opens) (hU : U' ≤ a ⁻¹ᵁ U)
    (heq : ∀ ζ : Γ(Scheme.absoluteDifferentialForms Y' p, f' ⁻¹ᵁ U'),
      (Θ f' hf' p).app U' ζ = (Θ' f' hf' p).app U' ζ)
    (hinj : Function.Injective fun ω : Γ(Scheme.absoluteDifferentialForms X p, U) =>
      (Scheme.absoluteDifferentialForms X' p).presheaf.map (homOfLE hU).op
        (a.absoluteFormsPullback p U ω)) (η : Γ(Scheme.absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    (Θ f hf p).app U η = (Θ' f hf p).app U η :=
  hinj <| (h₂ f f' a b sq hf hf' p U U' hU η).symm.trans
    ((heq _).trans (h₂' f f' a b sq hf hf' p U U' hU η))

end FormsTraceRule

section Sections

variable {X Y : Scheme.{u}}

/-- The sections over `U` of a morphism out of a pushforward, on a section of the source over
`f⁻¹U`. -/
theorem pushforward_val_app_apply (f : Y ⟶ X) {M : Y.Modules} {N : X.Modules}
    (φ : (Scheme.Modules.pushforward f).obj M ⟶ N) (U : X.Opens) (s : Γ(M, f ⁻¹ᵁ U)) :
    (φ.val.app (op U)).hom s = φ.app U s :=
  rfl

/-- A `Γ(Y, f⁻¹U)`-linear identification `e` of the sections of `M` over `f⁻¹U` with a module `P`,
read as a `Γ(X, U)`-linear map from `P` to the sections over `U` of `f_*M`. -/
def sectionsToPushforward (f : Y ⟶ X) {M : Y.Modules} {U : X.Opens} {P : Type*} [AddCommGroup P]
    [Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U)] [Module Γ(Y, f ⁻¹ᵁ U) P] [Module Γ(X, U) P]
    [IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U) P]
    (halg : algebraMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U) = (f.app U).hom)
    (e : Γ(M, f ⁻¹ᵁ U) ≃ₗ[Γ(Y, f ⁻¹ᵁ U)] P) :
    P →ₗ[Γ(X, U)] Γ((Scheme.Modules.pushforward f).obj M, U) where
  toFun x := e.symm x
  map_add' := e.symm.map_add
  map_smul' a x := by
    have h := e.symm.map_smul (algebraMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U) a) x
    rwa [algebraMap_smul, halg] at h

/-- A morphism out of `f_*M` on the image of `AlgebraicGeometry.sectionsToPushforward`. -/
theorem val_app_sectionsToPushforward (f : Y ⟶ X) {M : Y.Modules} {N : X.Modules} {U : X.Opens}
    {P : Type*} [AddCommGroup P] [Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U)] [Module Γ(Y, f ⁻¹ᵁ U) P]
    [Module Γ(X, U) P] [IsScalarTower Γ(X, U) Γ(Y, f ⁻¹ᵁ U) P]
    (halg : algebraMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U) = (f.app U).hom)
    (e : Γ(M, f ⁻¹ᵁ U) ≃ₗ[Γ(Y, f ⁻¹ᵁ U)] P) (φ : (Scheme.Modules.pushforward f).obj M ⟶ N)
    (x : P) : (φ.val.app (op U)).hom (sectionsToPushforward f halg e x) = φ.app U (e.symm x) :=
  rfl

/-- **The ring-level family of a rule over an affine open**: the maps
`Ω^q_{Γ(Y, f⁻¹U)} → Ω^q_{Γ(X, U)}` corresponding to `Θ^q_{Y/X}` on sections over `U`, for affine
`U` and `f⁻¹U`. -/
def sectionsFamily (Θ : FormsTraceRule.{u}) (f : Y ⟶ X) [IsFinite f] (hf : Syntomic f)
    {U : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U)) (q : ℕ) :
    letI := (f.app U).hom.toAlgebra
    ⋀[Γ(Y, f ⁻¹ᵁ U)]^q Ω[Γ(Y, f ⁻¹ᵁ U)⁄ℤ] →ₗ[Γ(X, U)] ⋀[Γ(X, U)]^q Ω[Γ(X, U)⁄ℤ] :=
  letI := (f.app U).hom.toAlgebra
  (Scheme.absoluteFormsSectionsEquiv X hU q).toLinearMap ∘ₗ ((Θ f hf q).val.app (op U)).hom ∘ₗ
    sectionsToPushforward f rfl (Scheme.absoluteFormsSectionsEquiv Y hV q)

/-- `sectionsFamily` unfolded. -/
theorem sectionsFamily_apply (Θ : FormsTraceRule.{u}) (f : Y ⟶ X) [IsFinite f] (hf : Syntomic f)
    {U : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen (f ⁻¹ᵁ U)) (q : ℕ)
    (x : ⋀[Γ(Y, f ⁻¹ᵁ U)]^q Ω[Γ(Y, f ⁻¹ᵁ U)⁄ℤ]) :
    sectionsFamily Θ f hf hU hV q x = Scheme.absoluteFormsSectionsEquiv X hU q
      ((Θ f hf q).app U ((Scheme.absoluteFormsSectionsEquiv Y hV q).symm x)) := by
  let := (f.app U).hom.toAlgebra
  exact congrArg (Scheme.absoluteFormsSectionsEquiv X hU q)
    (val_app_sectionsToPushforward f rfl (Scheme.absoluteFormsSectionsEquiv Y hV q) (Θ f hf q) x)

/-- **Condition (1) on an affine open makes the ring-level family a trace map on forms.** -/
theorem isFormsTrace_sectionsFamily {Θ : FormsTraceRule.{u}} (h₁ : Θ.IsTrace) (f : Y ⟶ X)
    [IsFinite f] (hf : Syntomic f) {U : X.Opens} (hU : IsAffineOpen U)
    (hV : IsAffineOpen (f ⁻¹ᵁ U)) :
    letI := (f.app U).hom.toAlgebra
    haveI := AlgebraicGeometry.flat hf
    haveI := AlgebraicGeometry.locallyOfFinitePresentation hf
    haveI := f.moduleFinite_app U hU
    haveI := f.moduleProjective_app U hU
    Stacks.FormsTrace.IsFormsTrace Γ(X, U) Γ(Y, f ⁻¹ᵁ U) (sectionsFamily Θ f hf hU hV) := by
  let := (f.app U).hom.toAlgebra
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  have := f.moduleFinite_app U hU
  have := f.moduleProjective_app U hU
  intro q b ω
  have hpull : (Scheme.absoluteFormsSectionsEquiv Y hV q).symm
      (Stacks.FormsTrace.formsMap Γ(X, U) Γ(Y, f ⁻¹ᵁ U) q ω) =
      f.absoluteFormsPullback q U ((Scheme.absoluteFormsSectionsEquiv X hU q).symm ω) := by
    rw [LinearEquiv.symm_apply_eq,
      Scheme.Hom.absoluteFormsSectionsEquiv_absoluteFormsPullback_app f hU hV q,
      LinearEquiv.apply_symm_apply]
  rw [sectionsFamily_apply, map_smul, hpull, h₁ f hf q U b, map_smul,
    LinearEquiv.apply_symm_apply, f.finiteTrace_app_of_isAffineOpen U hU]

end Sections

/-- Over `Spec`, the map on global sections of `Spec φ` for a surjective ring map `φ` is
surjective. -/
theorem appLE_top_surjective {R S : CommRingCat.{u}} (φ : R ⟶ S) (hφ : Function.Surjective φ)
    (h : (⊤ : (Spec S).Opens) ≤ Spec.map φ ⁻¹ᵁ ⊤) :
    Function.Surjective ((Spec.map φ).appLE ⊤ ⊤ h) := by
  have h1 : (Spec.map φ).appLE ⊤ ⊤ h = (Spec.map φ).appTop :=
    Scheme.Hom.appLE_eq_app (Spec.map φ) (U := ⊤)
  have h2 : (Spec.map φ).appTop = (Scheme.ΓSpecIso R).hom ≫ φ ≫ (Scheme.ΓSpecIso S).inv := by
    rw [Scheme.ΓSpecIso_inv_naturality, Iso.hom_inv_id_assoc]
  rw [h1, h2]
  intro y
  obtain ⟨x, hx⟩ := hφ ((Scheme.ΓSpecIso S).hom y)
  refine ⟨(Scheme.ΓSpecIso R).inv x, ?_⟩
  show (Scheme.ΓSpecIso S).inv (φ ((Scheme.ΓSpecIso R).hom ((Scheme.ΓSpecIso R).inv x))) = y
  rw [Iso.inv_hom_id_apply, hx, Iso.hom_inv_id_apply]

/-- The map on sections of the canonical open immersion `Spec Γ(X, U) → X`, from `U` to the
whole of `Spec Γ(X, U)`, is bijective. -/
theorem fromSpec_appLE_bijective {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U)
    (h : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U) :
    Function.Bijective (hU.fromSpec.appLE U ⊤ h) := by
  have hle : homOfLE h = eqToHom hU.fromSpec_preimage_self.symm := Subsingleton.elim _ _
  have : IsIso (hU.fromSpec.appLE U ⊤ h) := by
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, hle]
    infer_instance
  exact ConcreteCategory.bijective_of_isIso _

/-- **Every form is a pulled back form** along a morphism which is surjective on the sections over
affine opens `V' ≤ b⁻¹V`. -/
theorem exists_absoluteFormsPullback_eq {Y Y' : Scheme.{u}} (b : Y' ⟶ Y) {V : Y.Opens}
    (hV : IsAffineOpen V) {V' : Y'.Opens} (hV' : IsAffineOpen V') (h : V' ≤ b ⁻¹ᵁ V)
    (hs : Function.Surjective (b.appLE V V' h)) (p : ℕ)
    (ζ : Γ(Scheme.absoluteDifferentialForms Y' p, V')) :
    ∃ η, (Scheme.absoluteDifferentialForms Y' p).presheaf.map (homOfLE h).op
      (b.absoluteFormsPullback p V η) = ζ := by
  let := (b.appLE V V' h).hom.toAlgebra
  obtain ⟨x, hx⟩ := Stacks.FormsTrace.DescentAux.formsMap_surjective hs p
    (Scheme.absoluteFormsSectionsEquiv _ hV' p ζ)
  refine ⟨(Scheme.absoluteFormsSectionsEquiv _ hV p).symm x, ?_⟩
  apply (Scheme.absoluteFormsSectionsEquiv _ hV' p).injective
  rw [Scheme.absoluteFormsSectionsEquiv_absoluteFormsPullback b hV hV' h p,
    LinearEquiv.apply_symm_apply, hx]

/-- **Pulling forms back is injective** along a morphism which is bijective on the sections over
affine opens `U' ≤ a⁻¹U`. -/
theorem absoluteFormsPullback_injective {X X' : Scheme.{u}} (a : X' ⟶ X) {U : X.Opens}
    (hU : IsAffineOpen U) {U' : X'.Opens} (hU' : IsAffineOpen U') (h : U' ≤ a ⁻¹ᵁ U)
    (hb : Function.Bijective (a.appLE U U' h)) (p : ℕ) :
    Function.Injective fun ω : Γ(Scheme.absoluteDifferentialForms X p, U) =>
      (Scheme.absoluteDifferentialForms X' p).presheaf.map (homOfLE h).op
        (a.absoluteFormsPullback p U ω) := by
  let := (a.appLE U U' h).hom.toAlgebra
  intro ω ω' hωω'
  have e := congrArg (Scheme.absoluteFormsSectionsEquiv _ hU' p) hωω'
  simp only [Scheme.absoluteFormsSectionsEquiv_absoluteFormsPullback a hU hU' h p] at e
  exact (Scheme.absoluteFormsSectionsEquiv X hU p).injective
    (Stacks.FormsTrace.formsMap_injective_of_bijective hb p e)

namespace FormsTraceRule

variable {Θ Θ' : FormsTraceRule.{u}}

/-- **Uniqueness on the spectrum of a nice pair.** If `S` is a finite projective `R`-algebra with
a nice element (Stacks.FormsTrace.IsNiceElement) and `g = Spec(R → S)` is finite syntomic, two
rules with condition (1) agree on `g` over the whole of `Spec R`. -/
theorem app_top_eq_of_isNiceElement (h₁ : Θ.IsTrace) (h₁' : Θ'.IsTrace) {R S : Type u}
    [CommRing R] [CommRing S] [Algebra R S] [Module.Finite R S] [Module.Projective R S]
    (g : Spec (.of S) ⟶ Spec (.of R)) (hgdef : g = Spec.map (CommRingCat.ofHom (algebraMap R S)))
    [IsFinite g] (hg : Syntomic g) {h : R} (hh : Stacks.FormsTrace.IsNiceElement R S h) (p : ℕ)
    (η : Γ(Scheme.absoluteDifferentialForms (Spec (.of S)) p, g ⁻¹ᵁ ⊤)) :
    (Θ g hg p).app ⊤ η = (Θ' g hg p).app ⊤ η := by
  have := AlgebraicGeometry.flat hg
  have := AlgebraicGeometry.locallyOfFinitePresentation hg
  have hR : IsAffineOpen (⊤ : (Spec (.of R)).Opens) := isAffineOpen_top _
  have hV : IsAffineOpen (g ⁻¹ᵁ ⊤) := isAffineOpen_top _
  let := (g.app ⊤).hom.toAlgebra
  have := g.moduleFinite_app ⊤ hR
  have := g.moduleProjective_app ⊤ hR
  let eA : R ≃+* Γ(Spec (.of R), ⊤) := (Scheme.ΓSpecIso (.of R)).symm.commRingCatIsoToRingEquiv
  let eB : S ≃+* Γ(Spec (.of S), g ⁻¹ᵁ ⊤) :=
    (Scheme.ΓSpecIso (.of S)).symm.commRingCatIsoToRingEquiv
  have hcomm : ∀ r, eB (algebraMap R S r) = algebraMap _ _ (eA r) := fun r => by
    subst hgdef
    exact congrArg (fun φ => φ.hom r)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R S)))
  have heq := Stacks.FormsTrace.IsFormsTrace.eq_of_ringEquiv eA eB hcomm hh
    (isFormsTrace_sectionsFamily h₁ g hg hR hV) (isFormsTrace_sectionsFamily h₁' g hg hR hV)
  have k (T : FormsTraceRule.{u}) :
      sectionsFamily T g hg hR hV p (Scheme.absoluteFormsSectionsEquiv _ hV p η) =
        Scheme.absoluteFormsSectionsEquiv _ hR p ((T g hg p).app ⊤ η) := by
    rw [sectionsFamily_apply, LinearEquiv.symm_apply_apply]
  exact (Scheme.absoluteFormsSectionsEquiv (Spec (.of R)) hR p).injective
    ((k Θ).symm.trans ((LinearMap.congr_fun (congrFun heq p) _).trans (k Θ')))

/-- **Uniqueness over a framed affine open.** Two rules with conditions (1) and (2) agree on `f`
over an affine open `U` carrying a frame `F` of `Γ(Y, f⁻¹U)` over `Γ(X, U)`. -/
private theorem app_eq_of_chartFrame (h₁ : Θ.IsTrace) (h₂ : Θ.IsBaseChange) (h₁' : Θ'.IsTrace)
    (h₂' : Θ'.IsBaseChange) {X Y : Scheme.{u}} (f : Y ⟶ X) [IsFinite f] (hf : Syntomic f) (p : ℕ)
    {U : X.Opens} (hU : IsAffineOpen U) {d : ℕ} [NeZero d]
    (F : @Stacks.FormsTrace.ChartFrame d _ Γ(X, U) Γ(Y, f ⁻¹ᵁ U) _ _ (f.app U).hom.toAlgebra)
    (η : Γ(Scheme.absoluteDifferentialForms Y p, f ⁻¹ᵁ U)) :
    (Θ f hf p).app U η = (Θ' f hf p).app U η := by
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  have hV : IsAffineOpen (f ⁻¹ᵁ U) := hU.preimage f
  let : Algebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let := F.algebraChart
  let := F.algebraCarrier
  let := F.algebraChartTarget
  have := F.isScalarTower_chart
  have := F.isScalarTower_carrier
  have := F.isPushout
  set g := Spec.map (CommRingCat.ofHom (algebraMap F.Chart F.ChartAlgebra))
  set gA := Spec.map (f.app U)
  set a := Spec.map (CommRingCat.ofHom (algebraMap F.Chart Γ(X, U)))
  set b := Spec.map (CommRingCat.ofHom (algebraMap F.ChartAlgebra Γ(Y, f ⁻¹ᵁ U)))
  have sq₂ : IsPullback b gA g a :=
    isPullback_SpecMap_of_isPushout _ _ _ _
      (CommRingCat.isPushout_of_isPushout F.Chart F.ChartAlgebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U))
  have sq₁ : IsPullback hV.fromSpec gA f hU.fromSpec := isPullback_fromSpec f hU hV
  have : IsFinite g := by
    rw [IsFinite.SpecMap_iff]
    exact RingHom.finite_algebraMap.mpr inferInstance
  have hg : Syntomic g := by
    refine HasRingHomProperty.Spec_iff.mpr ?_
    show RingHom.Syntomic (algebraMap F.Chart F.ChartAlgebra)
    rw [RingHom.syntomic_iff, toAlgebra_algebraMap]
    exact Stacks.FormsTrace.universalChartRing_syntomic.{u} Γ(X, U) F.good
  have : IsFinite gA := MorphismProperty.of_isPullback sq₁ inferInstance
  have hgA : Syntomic gA := MorphismProperty.of_isPullback sq₁ hf
  have hG := app_top_eq_of_isNiceElement h₁ h₁' g rfl hg F.nice p
  have hle₂ : (⊤ : (Spec Γ(X, U)).Opens) ≤ a ⁻¹ᵁ ⊤ := le_refl _
  have hh := AlgebraicGeometry.preimage_le_preimage_of_comm sq₂.w.symm hle₂
  have hA := app_eq_of_isPullback_of_surjective h₂ h₂' g gA a b sq₂ hg hgA p ⊤ ⊤ hle₂ hG
    (exists_absoluteFormsPullback_eq b (isAffineOpen_top _) (isAffineOpen_top _) hh
      (appLE_top_surjective _ (Stacks.FormsTrace.algebraMap_surjective_of_isPushout F.Chart
        F.ChartAlgebra Γ(X, U) Γ(Y, f ⁻¹ᵁ U) F.eval_surjective) hh) p)
  have hle₁ : (⊤ : (Spec Γ(X, U)).Opens) ≤ hU.fromSpec ⁻¹ᵁ U := hU.fromSpec_preimage_self.ge
  exact app_eq_of_isPullback_of_injective h₂ h₂' f gA hU.fromSpec hV.fromSpec sq₁ hf hgA p U ⊤
    hle₁ hA (absoluteFormsPullback_injective hU.fromSpec hU (isAffineOpen_top _) hle₁
      (fromSpec_appLE_bijective hU hle₁) p) η

/-- **Uniqueness of trace maps on forms** (Stacks, Lemma 0FLB, uniqueness): two rules
`f ↦ Θ^p_{Y/X}` on finite syntomic morphisms satisfying conditions (1) and (2) of Lemma 0FLB are
equal. -/
theorem eq_of_isTrace_of_isBaseChange (h₁ : Θ.IsTrace) (h₂ : Θ.IsBaseChange)
    (h₁' : Θ'.IsTrace) (h₂' : Θ'.IsBaseChange) : Θ = Θ' := by
  funext X Y f _ hf p
  have := AlgebraicGeometry.flat hf
  have := AlgebraicGeometry.locallyOfFinitePresentation hf
  have hB : Opens.IsBasis (Set.range fun U : {U : X.Opens // Stacks.FormsTrace.IsFramedOpen f U} =>
      U.1) := by
    rw [Subtype.range_coe_subtype]
    exact Stacks.FormsTrace.isBasis_framedOpens f hf
  refine Scheme.Hom.formsMap_ext_of_isBasis f hB p _ _ fun U η => ?_
  obtain ⟨U, hUf⟩ := U
  show (Θ f hf p).app U η = (Θ' f hf p).app U η
  rcases hUf.2 with hsub | ⟨d, hd, ⟨F⟩⟩
  · have : Subsingleton Γ(Scheme.absoluteDifferentialForms Y p, f ⁻¹ᵁ U) :=
      Module.subsingleton Γ(Y, f ⁻¹ᵁ U) _
    rw [show η = 0 from Subsingleton.elim _ _]
    exact ((Θ f hf p).app U).hom.map_zero.trans ((Θ' f hf p).app U).hom.map_zero.symm
  · exact app_eq_of_chartFrame h₁ h₂ h₁' h₂' f hf p hUf.1 F η

end FormsTraceRule

end AlgebraicGeometry

end
