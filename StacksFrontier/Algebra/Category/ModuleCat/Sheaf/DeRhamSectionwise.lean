module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ChangeOfRings
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerStalk
public import StacksFrontier.RingTheory.DeRham.Complex

/-!
# The sectionwise de Rham differential, as a morphism of presheaves of modules

Let `φ : R ⟶ R'` be a morphism of presheaves of commutative rings on a category `C`. Mathlib's
`PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ` is the presheaf of
*sectionwise* relative differentials, `U ↦ Ω_{R'(U)/R(U)}`, and
`PresheafOfModules.extPow p` is the presheaf of sectionwise exterior powers, so

`PresheafOfModules.extPow p (relativeDifferentials' φ) : U ↦ ⋀^p_{R'(U)} Ω_{R'(U)/R(U)}`.

`KaehlerDifferential.deRhamDifferential p` is the ring-level de Rham differential, the unique
`R(U)`-linear map `Ω^p_{R'(U)/R(U)} → Ω^{p+1}_{R'(U)/R(U)}` with

`d (b₀ · d b₁ ∧ ⋯ ∧ d b_p) = d b₀ ∧ d b₁ ∧ ⋯ ∧ d b_p`.

This file proves that **those maps are compatible with the restriction maps**, and so assembles
them into a morphism of presheaves of `R`-modules — and, with the square-zero property, into a
cochain complex of presheaves of `R`-modules. The terms are presheaves of `R`-modules and not of
`R'`-modules because the differential is only `R`-linear: already in degree zero the Leibniz
rule gives `d (b b') = b d b' + b' d b`.

## Main definitions

* `PresheafOfModules.restrictScalarsHom`: a morphism between two restrictions of scalars along
  `α : R ⟶ R'`, built from a natural family of additive maps that is linear for the scalars
  coming from `R`.
* `PresheafOfModules.sectionwiseForms`: the presheaf `U ↦ ⋀^p_{R'(U)} Ω_{R'(U)/R(U)}`, as a
  presheaf of `R`-modules.
* `PresheafOfModules.sectionwiseDeRhamDifferential`: **the ring-level de Rham differential, as a
  morphism of presheaves of `R`-modules.**
* `PresheafOfModules.sectionwiseDeRhamComplex`: the cochain complex of presheaves of `R`-modules
  it assembles into.

## Main results

* `KaehlerDifferential.deRhamDifferential_comm`: **the de Rham differential commutes with base
  change along a square of rings.** Given `A → B`, `A' → B'` and maps `σA : A → A'`,
  `σB : B → B'` forming a commuting square, any additive `σB`-semilinear family on the exterior
  powers that carries a wedge of exact differentials to the wedge of the exact differentials of
  the images commutes with `deRhamDifferential`.
* `PresheafOfModules.sectionwiseDeRhamDifferentialApp_naturality`: **the sectionwise de Rham
  differential is compatible with the restriction maps**, which is the above applied to the
  restriction square of `φ`.
* `PresheafOfModules.sectionwiseDeRhamDifferentialApp_smul_ιMulti_d`: the de Rham rule, read on
  the sections of the sectionwise exterior powers.
* `PresheafOfModules.sectionwiseDeRhamDifferential_comp_self`: the differential squares to zero.

## Implementation notes

What is forced and what is chosen.

* `KaehlerDifferential.deRhamDifferential_comm` is the **second conjunct** of
  `KaehlerDifferential.isBaseChange_exteriorPower_and_deRhamDifferential_comm`
  (`StacksFrontier.RingTheory.DeRham.Basic`, Tag 0H8Y) with its `Algebra.IsPushout A A' B B'`
  hypothesis dropped — a restriction map of a presheaf of rings does not exhibit `R'(V)` as
  `R'(U) ⊗_{R(U)} R(V)`, so the pushout form is unusable here, and the proof of that conjunct
  never uses the pushout. The two spanning hypotheses are also traded for weaker ones: the maps
  are taken as `AddMonoidHom`s together with an explicit semilinearity equation, rather than as
  `B`-linear maps into a `B`-module or as bundled `→ₛₗ` maps, because the restriction maps of
  `extPow` are semilinear for the ring homomorphism spelled
  `((R' ⋙ forget₂ CommRingCat RingCat).map f).hom`, whose source carries no `Module` instance
  that typeclass inference can find for `Ω[R'(U)⁄R(U)]`.
* The spanning lemma the proof rests on is `Crystalline.span_range_smul_ιMulti_eq_top`, applied
  **over `A`**, not over `B`: the elements `b₀ · (d b₁ ∧ ⋯ ∧ d b_p)` span `Ω^p_{B/A}` already as
  an `A`-module, and `A`-spanning is what an only-`A`-linear map needs. (Contrast
  `AlgebraicGeometry.SheafOfModules.locallyGeneratedByExactWedges`, which uses
  `Crystalline.span_range_ιMulti_eq_top` over `B` because the composite there is `B`-linear.)
* The de Rham differential is applied at the **`CommRingCat` spelling** of its two rings,
  `(A := R.obj U) (B := R'.obj U)`, and the local algebra instance is `(φ.app U).hom.toAlgebra`.
  That is the spelling `CommRingCat.KaehlerDifferential` itself uses, so
  `↥((relativeDifferentials' φ).obj U)` and `Ω[R'(U)⁄R(U)]` are identified in a handful of
  unfoldings. With the rings spelled `(R ⋙ forget₂ CommRingCat RingCat).obj U` instead — the
  spelling `extPow` and `extPowSections` are stated at — the same identification exhausts the
  heartbeat budget, and with the two rings left as metavariables it does so too. No heartbeat
  limit is raised anywhere in this file.
* `PresheafOfModules.extPow` and `extPowSections` are stated at a module universe `max w a`,
  and the unifier cannot solve `max w ?a =?= w`; every use below therefore carries explicit
  universe arguments `.{v, u, w, w}`. Left to unification the failure surfaces as
  `stuck at solving universe constraint`, naming `Quiver.Hom`.
* Everything is stated for an arbitrary category `C`, not for the opens of a space, and at
  independent universes `v u w`; nothing is narrowed.

**No Stacks tag.** The ring-level differential and its defining rule carry Tag 0FKG in
`StacksFrontier.RingTheory.DeRham.Basic`; this file adds no statement of the source, only the
restriction-map compatibility that the *existence* half of Tag 0FKM needs. What existence still
needs beyond this file: local injectivity of
`AlgebraicGeometry.SheafOfModules.exactWedgeComparison`, and then the descent of
`sectionwiseDeRhamDifferential` along that comparison to the exterior powers of the sheaf of
relative differentials, using the local surjectivity proved in
`StacksFrontier.Topology.Sheaves.Modules.DeRhamUniqueness`.

## References

* [Stacks Project, Tag 0FKM](https://stacks.math.columbia.edu/tag/0FKM)
* [Stacks Project, Tag 0FKG](https://stacks.math.columbia.edu/tag/0FKG)
* [Stacks Project, Tag 0H8Y](https://stacks.math.columbia.edu/tag/0H8Y)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u w

namespace KaehlerDifferential

/-- `deRhamDifferential` commutes with multiplication by a scalar that comes from the base
ring. -/
theorem deRhamDifferential_algebraMap_smul {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    (p : ℕ) (a : A) (x : ⋀[B]^p (Ω[B⁄A])) :
    deRhamDifferential p (algebraMap A B a • x) =
      algebraMap A B a • deRhamDifferential (A := A) p x := by
  rw [algebraMap_smul, map_smul, algebraMap_smul]

/-- **The de Rham differential commutes with base change along a square of rings.** -/
theorem deRhamDifferential_comm {A A' B B' : Type*} [CommRing A] [CommRing A'] [CommRing B]
    [CommRing B'] [Algebra A B] [Algebra A' B'] {σA : A → A'} {σB : B → B'}
    (hsq : ∀ a : A, σB (algebraMap A B a) = algebraMap A' B' (σA a)) (p : ℕ)
    (ψ : ⋀[B]^p (Ω[B⁄A]) →+ ⋀[B']^p (Ω[B'⁄A']))
    (ψ' : ⋀[B]^(p + 1) (Ω[B⁄A]) →+ ⋀[B']^(p + 1) (Ω[B'⁄A']))
    (hψs : ∀ (s : B) (x : ⋀[B]^p (Ω[B⁄A])), ψ (s • x) = σB s • ψ x)
    (hψ's : ∀ (s : B) (x : ⋀[B]^(p + 1) (Ω[B⁄A])), ψ' (s • x) = σB s • ψ' x)
    (hψ : ∀ b : Fin p → B, ψ (exteriorPower.ιMulti B p fun i ↦ D A B (b i)) =
      exteriorPower.ιMulti B' p fun i ↦ D A' B' (σB (b i)))
    (hψ' : ∀ b : Fin (p + 1) → B, ψ' (exteriorPower.ιMulti B (p + 1) fun i ↦ D A B (b i)) =
      exteriorPower.ιMulti B' (p + 1) fun i ↦ D A' B' (σB (b i)))
    (ω : ⋀[B]^p (Ω[B⁄A])) :
    ψ' (deRhamDifferential p ω) = deRhamDifferential (A := A') p (ψ ω) := by
  have hmem : ω ∈ Submodule.span A (Set.range fun b : Fin (p + 1) → B ↦
      b 0 • exteriorPower.ιMulti B p fun i ↦ D A B (b i.succ)) := by
    rw [Crystalline.span_range_smul_ιMulti_eq_top (R := A) (D A B)
      (span_range_derivation A B) p]
    exact Submodule.mem_top
  induction hmem using Submodule.span_induction with
  | mem v hv =>
      obtain ⟨b, rfl⟩ := hv
      rw [deRhamDifferential_smul_ιMulti_D p b, hψ' b, hψs, hψ fun i ↦ b i.succ]
      exact (deRhamDifferential_smul_ιMulti_D (A := A') p fun i ↦ σB (b i)).symm
  | zero => rw [map_zero, map_zero, map_zero, map_zero]
  | add v w _ _ ihv ihw => rw [map_add, map_add, map_add, ihv, ihw, map_add]
  | smul a v _ ih =>
      rw [← algebraMap_smul B a, deRhamDifferential_algebraMap_smul, hψ's, hψs, hsq,
        deRhamDifferential_algebraMap_smul, ih]

end KaehlerDifferential

namespace PresheafOfModules

section RestrictScalars

variable {C : Type u} [Category.{v} C] {R R' : Cᵒᵖ ⥤ RingCat.{w}}

/-- A morphism between two restrictions of scalars, from a natural family of additive maps that
is linear for the scalars coming from `R`. -/
noncomputable def restrictScalarsHom (α : R ⟶ R') {M N : PresheafOfModules.{w} R'}
    (g : ∀ U, M.obj U →+ N.obj U)
    (hsmul : ∀ (U : Cᵒᵖ) (r : R.obj U) (x : M.obj U),
      g U (α.app U r • x) = α.app U r • g U x)
    (hnat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.obj U), g V (M.map f x) = N.map f (g U x)) :
    (restrictScalars α).obj M ⟶ (restrictScalars α).obj N where
  app U := ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (α.app U).hom).obj (M.obj U))
    (Y := (ModuleCat.restrictScalars (α.app U).hom).obj (N.obj U))
    { toFun := g U
      map_add' := (g U).map_add
      map_smul' := hsmul U }
  naturality f := ModuleCat.hom_ext (LinearMap.ext (hnat f))

/-- The component of `restrictScalarsHom α g hsmul hnat` at `U` is the additive map `g U`. -/
@[simp]
theorem restrictScalarsHom_app (α : R ⟶ R') {M N : PresheafOfModules.{w} R'}
    {g : ∀ U, M.obj U →+ N.obj U}
    {hsmul : ∀ (U : Cᵒᵖ) (r : R.obj U) (x : M.obj U),
      g U (α.app U r • x) = α.app U r • g U x}
    {hnat : ∀ {U V : Cᵒᵖ} (f : U ⟶ V) (x : M.obj U), g V (M.map f x) = N.map f (g U x)}
    (U : Cᵒᵖ) (x : M.obj U) :
    (restrictScalarsHom α g hsmul hnat).app U x = g U x := rfl

end RestrictScalars

section DeRham

open PresheafOfModulesOfCommRing.DifferentialsConstruction

variable {C : Type u} [Category.{v} C] {R R' : Cᵒᵖ ⥤ CommRingCat.{w}} (φ : R ⟶ R')

/-- The presheaf of sectionwise relative differential `p`-forms of `φ`, as a presheaf of
`R`-modules. -/
noncomputable abbrev sectionwiseForms (p : ℕ) :
    PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat) :=
  (restrictScalars (Functor.whiskerRight φ (forget₂ CommRingCat RingCat))).obj
    (extPow.{v, u, w, w} p (relativeDifferentials' φ))

/-- The restriction map of `extPow n (relativeDifferentials' φ)`, as a semilinear map between
the exterior powers of the sections of the sectionwise Kähler differentials. -/
noncomputable abbrev extPowRestrictₛₗ {U V : Cᵒᵖ} (f : U ⟶ V) (n : ℕ) :
    ⋀[(R' ⋙ forget₂ CommRingCat RingCat).obj U]^n ((relativeDifferentials' φ).obj U)
      →ₛₗ[((R' ⋙ forget₂ CommRingCat RingCat).map f).hom]
        ⋀[(R' ⋙ forget₂ CommRingCat RingCat).obj V]^n ((relativeDifferentials' φ).obj V) :=
  ExteriorAlgebra.powMapₛₗ n ((R' ⋙ forget₂ CommRingCat RingCat).map f).hom
    ((relativeDifferentials' φ).restrictₛₗ f)

/-- The restriction maps of `extPow p (relativeDifferentials' φ)` carry a wedge of exact
differentials to the wedge of the exact differentials of the restricted sections. -/
theorem extPowRestrictₛₗ_ιMulti_d {U V : Cᵒᵖ} (f : U ⟶ V) (p : ℕ)
    (b : Fin p → (R' ⋙ forget₂ CommRingCat RingCat).obj U) :
    extPowRestrictₛₗ φ f p
        (exteriorPower.ιMulti ((R' ⋙ forget₂ CommRingCat RingCat).obj U) p
          fun i ↦ (derivation' φ).d (b i)) =
      exteriorPower.ιMulti ((R' ⋙ forget₂ CommRingCat RingCat).obj V) p
        fun i ↦ (derivation' φ).d (((R' ⋙ forget₂ CommRingCat RingCat).map f).hom (b i)) := by
  refine Subtype.ext ?_
  rw [ExteriorAlgebra.powMapₛₗ_coe, exteriorPower.ιMulti_apply_coe,
    ExteriorAlgebra.mapₛₗ_ιMulti, exteriorPower.ιMulti_apply_coe]
  exact congrArg (ExteriorAlgebra.ιMulti _ p)
    (funext fun i ↦ relativeDifferentials'_map_d φ f (b i))

/-- The ring-level de Rham differential of `φ` at one object, read on the sections of the
presheaves of sectionwise exterior powers. -/
noncomputable def sectionwiseDeRhamDifferentialApp (p : ℕ) (U : Cᵒᵖ) :
    (extPow.{v, u, w, w} p (relativeDifferentials' φ)).obj U →+
      (extPow.{v, u, w, w} (p + 1) (relativeDifferentials' φ)).obj U :=
  letI : Algebra (R.obj U) (R'.obj U) := (φ.app U).hom.toAlgebra
  AddMonoidHom.comp
    (extPowSections.{v, u, w, w} (p + 1)
      (relativeDifferentials' φ) U).symm.toLinearMap.toAddMonoidHom
    (AddMonoidHom.comp
      (KaehlerDifferential.deRhamDifferential (A := R.obj U) (B := R'.obj U) p).toAddMonoidHom
      (extPowSections.{v, u, w, w} p (relativeDifferentials' φ) U).toLinearMap.toAddMonoidHom)

/-- The sectionwise de Rham differential is linear for the scalars coming from `R`. -/
theorem sectionwiseDeRhamDifferentialApp_smul (p : ℕ) (U : Cᵒᵖ)
    (r : R.obj U) (x : (extPow.{v, u, w, w} p (relativeDifferentials' φ)).obj U) :
    sectionwiseDeRhamDifferentialApp φ p U ((φ.app U).hom r • x) =
      (φ.app U).hom r • sectionwiseDeRhamDifferentialApp φ p U x :=
  let : Algebra (R.obj U) (R'.obj U) := (φ.app U).hom.toAlgebra
  (congrArg (extPowSections.{v, u, w, w} (p + 1) (relativeDifferentials' φ) U).symm
      ((congrArg (KaehlerDifferential.deRhamDifferential (A := R.obj U) (B := R'.obj U) p)
          (map_smul (extPowSections.{v, u, w, w} p (relativeDifferentials' φ) U) _ x)).trans
        (KaehlerDifferential.deRhamDifferential_algebraMap_smul (A := R.obj U) (B := R'.obj U)
          p r _))).trans
    (map_smul (extPowSections.{v, u, w, w} (p + 1) (relativeDifferentials' φ) U).symm _ _)

/-- **The sectionwise de Rham differential is compatible with the restriction maps.** -/
theorem sectionwiseDeRhamDifferentialApp_naturality (p : ℕ) {U V : Cᵒᵖ} (f : U ⟶ V)
    (x : (extPow.{v, u, w, w} p (relativeDifferentials' φ)).obj U) :
    sectionwiseDeRhamDifferentialApp φ p V
        ((extPow.{v, u, w, w} p (relativeDifferentials' φ)).map f x) =
      (extPow.{v, u, w, w} (p + 1) (relativeDifferentials' φ)).map f
        (sectionwiseDeRhamDifferentialApp φ p U x) := by
  let : Algebra (R.obj U) (R'.obj U) := (φ.app U).hom.toAlgebra
  let : Algebra (R.obj V) (R'.obj V) := (φ.app V).hom.toAlgebra
  exact (KaehlerDifferential.deRhamDifferential_comm
    (A := R.obj U) (A' := R.obj V) (B := R'.obj U) (B' := R'.obj V)
    (σA := fun a ↦ ((R ⋙ forget₂ CommRingCat RingCat).map f).hom a)
    (σB := fun s ↦ ((R' ⋙ forget₂ CommRingCat RingCat).map f).hom s)
    (fun a ↦ congrArg (fun g : R.obj U ⟶ R'.obj V ↦ CommRingCat.Hom.hom g a)
      (φ.naturality f).symm) p
    (extPowRestrictₛₗ φ f p).toAddMonoidHom (extPowRestrictₛₗ φ f (p + 1)).toAddMonoidHom
    (fun s y ↦ LinearMap.map_smulₛₗ (extPowRestrictₛₗ φ f p) s y)
    (fun s y ↦ LinearMap.map_smulₛₗ (extPowRestrictₛₗ φ f (p + 1)) s y)
    (extPowRestrictₛₗ_ιMulti_d φ f p) (extPowRestrictₛₗ_ιMulti_d φ f (p + 1)) _).symm

/-- **The de Rham rule for the sectionwise differential**: a multiple of a wedge of exact
differentials is carried to the wedge of the exact differentials of all the factors. -/
theorem sectionwiseDeRhamDifferentialApp_smul_ιMulti_d (p : ℕ) (U : Cᵒᵖ)
    (b : Fin (p + 1) → (R' ⋙ forget₂ CommRingCat RingCat).obj U) :
    extPowSections.{v, u, w, w} (p + 1) (relativeDifferentials' φ) U
        (sectionwiseDeRhamDifferentialApp φ p U
          ((extPowSections.{v, u, w, w} p (relativeDifferentials' φ) U).symm
            (b 0 • exteriorPower.ιMulti ((R' ⋙ forget₂ CommRingCat RingCat).obj U) p
              fun i ↦ (derivation' φ).d (b i.succ)))) =
      exteriorPower.ιMulti ((R' ⋙ forget₂ CommRingCat RingCat).obj U) (p + 1)
        fun i ↦ (derivation' φ).d (b i) :=
  let : Algebra (R.obj U) (R'.obj U) := (φ.app U).hom.toAlgebra
  KaehlerDifferential.deRhamDifferential_smul_ιMulti_D (A := R.obj U) (B := R'.obj U) p b

/-- The sectionwise de Rham differential squares to zero. -/
theorem sectionwiseDeRhamDifferentialApp_comp_self (p : ℕ) (U : Cᵒᵖ)
    (x : (extPow.{v, u, w, w} p (relativeDifferentials' φ)).obj U) :
    sectionwiseDeRhamDifferentialApp φ (p + 1) U
      (sectionwiseDeRhamDifferentialApp φ p U x) = 0 :=
  let : Algebra (R.obj U) (R'.obj U) := (φ.app U).hom.toAlgebra
  KaehlerDifferential.deRhamDifferential_comp_self (A := R.obj U) (B := R'.obj U) p
    (extPowSections.{v, u, w, w} p (relativeDifferentials' φ) U x)

/-- **The ring-level de Rham differential, as a morphism of presheaves of `R`-modules.** -/
noncomputable def sectionwiseDeRhamDifferential (p : ℕ) :
    sectionwiseForms φ p ⟶ sectionwiseForms φ (p + 1) :=
  restrictScalarsHom _ (sectionwiseDeRhamDifferentialApp φ p)
    (sectionwiseDeRhamDifferentialApp_smul φ p)
    (fun f x ↦ sectionwiseDeRhamDifferentialApp_naturality φ p f x)

/-- The component of `sectionwiseDeRhamDifferential φ p` at `U` is the ring-level de Rham
differential `sectionwiseDeRhamDifferentialApp φ p U`. -/
@[simp]
theorem sectionwiseDeRhamDifferential_app (p : ℕ) (U : Cᵒᵖ)
    (x : (extPow.{v, u, w, w} p (relativeDifferentials' φ)).obj U) :
    (sectionwiseDeRhamDifferential φ p).app U x = sectionwiseDeRhamDifferentialApp φ p U x := rfl

/-- **The sectionwise de Rham differential squares to zero**, as an equation of morphisms of
presheaves of `R`-modules. -/
theorem sectionwiseDeRhamDifferential_comp_self (p : ℕ) :
    sectionwiseDeRhamDifferential φ p ≫ sectionwiseDeRhamDifferential φ (p + 1) = 0 :=
  PresheafOfModules.hom_ext fun U ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦
    sectionwiseDeRhamDifferentialApp_comp_self φ p U x)

/-- **The sectionwise relative de Rham complex of `φ`**, as a cochain complex of presheaves of
`R`-modules. -/
noncomputable def sectionwiseDeRhamComplex :
    CochainComplex (PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) ℕ :=
  CochainComplex.of (sectionwiseForms φ) (sectionwiseDeRhamDifferential φ)
    (sectionwiseDeRhamDifferential_comp_self φ)

/-- The degree-`p` term of `sectionwiseDeRhamComplex φ` is `sectionwiseForms φ p`. -/
@[simp]
theorem sectionwiseDeRhamComplex_X (p : ℕ) :
    (sectionwiseDeRhamComplex φ).X p = sectionwiseForms φ p := rfl

/-- The differential of `sectionwiseDeRhamComplex φ` from degree `p` to degree `p + 1` is
`sectionwiseDeRhamDifferential φ p`. -/
@[simp]
theorem sectionwiseDeRhamComplex_d (p : ℕ) :
    (sectionwiseDeRhamComplex φ).d p (p + 1) = sectionwiseDeRhamDifferential φ p := by
  apply CochainComplex.of_d

end DeRham

end PresheafOfModules

end
