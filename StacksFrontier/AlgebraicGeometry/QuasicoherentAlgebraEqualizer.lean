module

public import StacksFrontier.AlgebraicGeometry.AffineAlgebraEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Basic
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleColimits.EqualizerAlgebra
public import StacksFrontier.AlgebraicGeometry.QuasicoherentAlgebraEqualizer.Basic
public import StacksFrontier.AlgebraicGeometry.QuasicoherentAlgebraEqualizer.FiniteEtale

/-!
# The equalizer of two morphisms of quasi-coherent algebras is quasi-coherent

Let `X` be a scheme and let `φ, ψ : A ⟶ B` be two morphisms of quasi-coherent sheaves of
commutative `𝒪_X`-algebras. The sheaf of algebras `equalizerAlgebra φ ψ` whose sections over an
open are the sections of `A` on which `φ` and `ψ` agree is again quasi-coherent, so that it is an
object of the category of quasi-coherent `𝒪_X`-algebras and in particular has a relative
spectrum.

Quasi-coherence is a direct computation with sections: over an affine open `U` and a section
`a : Γ(X, U)`, the sections of the equalizer over the basic open `X.basicOpen a` are the
localization away from `a` of its sections over `U`. This is exactness of localization, read off
on sections: a section of the equalizer over `X.basicOpen a` lifts, after multiplication by a
power of `a`, to a section of `A` over `U`, and a further power of `a` forces that lift into the
equalizer because the difference of its two images in `B` dies on `X.basicOpen a`.

The last section specialises to the situation of Stacks Tag 0BN9: when the sections of `A` and of
`B` over every affine open are finite étale, so are those of the equalizer — that is the affine,
algebraic statement `Stacks.FundamentalGroup.etale_and_moduleFinite_equalizer` — and therefore
the relative spectrum of the equalizer is a finite étale cover of `X`.

## Main results

* `Stacks.QuasicoherentAlgebraEqualizer.isLocalizedModule_equalizerAlgebra` — the sections of
  the equalizer over a basic open are the localization of its sections over the ambient affine
  open.
* `Stacks.QuasicoherentAlgebraEqualizer.isQuasicoherent_equalizerAlgebra` — **the equalizer of
  two morphisms of quasi-coherent `𝒪_X`-algebras is quasi-coherent.**
* `Stacks.QuasicoherentAlgebraEqualizer.eqSubring_eq_toSubring_equalizer` — over an open, the
  sections of the equalizer are Mathlib's `AlgHom.equalizer` of the two maps of
  `Γ(X, U)`-algebras on sections; this is the shape in which
  `Stacks.FundamentalGroup.etale_and_moduleFinite_equalizer` applies to them.
* `Stacks.QuasicoherentAlgebraEqualizer.quasicoherentEqualizer` — the equalizer as an object of
  the category `Stacks.AffineAlgebraEquivalence.QuasicoherentAlgebra X`, with
  `Stacks.QuasicoherentAlgebraEqualizer.isLimitQuasicoherentFork` its universal property and
  `Stacks.QuasicoherentAlgebraEqualizer.hasEqualizers_quasicoherentAlgebra` the resulting
  instance: **the category of quasi-coherent `𝒪_X`-algebras has equalizers.**
* `Stacks.QuasicoherentAlgebraEqualizer.etale_and_finite_app_equalizerAlgebra` and
  `Stacks.QuasicoherentAlgebraEqualizer.isFinite_and_etale_relativeSpecToBase_equalizerAlgebra`
  — **the relative spectrum of the equalizer is a finite étale cover of `X`** when the sections
  of both algebras over every affine open are finite étale over the sections of the structure
  sheaf.

## Implementation notes

Quasi-coherence is obtained from
`Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`,
the criterion that a module whose sections over the basic opens of each affine open are
localizations of its sections over that affine open is quasi-coherent. Its hypothesis is checked
with `IsLocalizedModule.Away.mk_of_addCommGroup`, whose three obligations are discharged from the
corresponding localization statements for `A` and for `B`, which are
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ`.

Sections of the equalizer are elements of a `Subring` of the sections of `A`, so the whole
argument is phrased through `val` and `mk`, which pass between a section of the equalizer and the
underlying section of `A`. All the compatibilities of `val` with the module operations, the
restriction maps and the two module structures on sections over a smaller open hold by `rfl`: the
`Γ(X, U)`-action on the sections of the underlying module of an algebra sheaf is multiplication by
the image of the structure morphism, and that of
`Stacks.RelativeSpec.AlgebraSheaf.underlyingModule` of the equalizer is the restriction of that of
`A`.

The map on sections of a morphism of algebra sheaves is packaged as `secMap`, rather than used as
`φ.right.hom.app (op W)`, because instance search does not identify the sections
`Γ(A.underlyingModule, W)` of the underlying module with the sections `A.right.obj.obj (op W)` of
the algebra sheaf: the two are definitionally equal but not syntactically, so the module
operations are not found at the latter spelling.

## References

* [Stacks Project, Tag 01LM](https://stacks.math.columbia.edu/tag/01LM)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
* [Stacks Project, Tag 0BN9](https://stacks.math.columbia.edu/tag/0BN9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.TorsionQuasicoherent

universe u

namespace Stacks.QuasicoherentAlgebraEqualizer

variable {X : Scheme.{u}} {A B : AlgebraSheaf X} (φ ψ : A ⟶ B)

/-! ### Sections of the underlying modules -/

/-- The map on sections of a morphism of algebra sheaves, as a map between the sections of the
underlying `𝒪_X`-modules. -/
def secMap {W : X.Opens} (y : Γ(A.underlyingModule, W)) : Γ(B.underlyingModule, W) :=
  (φ.right.hom.app (op W)).hom y

/-- A section of `A` lies in the equalizer exactly when `φ` and `ψ` agree on it, phrased
through `secMap`. -/
theorem mem_eqSubring_iff' {W : X.Opens} (y : Γ(A.underlyingModule, W)) :
    y ∈ eqSubring φ ψ (op W) ↔ secMap φ y = secMap ψ y :=
  Iff.rfl

/-- A morphism of algebra sheaves commutes with the structure morphisms from `𝒪_X`. -/
theorem secMap_structureMap (U : (Opens X)ᵒᵖ) (r : X.sheaf.obj.obj U) :
    (φ.right.hom.app U).hom ((A.hom.hom.app U).hom r) = (B.hom.hom.app U).hom r := by
  have hφ : ((A.hom ≫ φ.right).hom.app U).hom r = (B.hom.hom.app U).hom r := by rw [Under.w φ]
  exact hφ

/-- The map on sections of a morphism of algebra sheaves is `Γ(X, W)`-linear. -/
theorem secMap_smul {W : X.Opens} (r : Γ(X, W)) (y : Γ(A.underlyingModule, W)) :
    secMap φ (r • y) = r • secMap φ y := by
  have h : ∀ y' : A.right.obj.obj (op W),
      (φ.right.hom.app (op W)).hom ((A.hom.hom.app (op W)).hom r * y') =
        (B.hom.hom.app (op W)).hom r * (φ.right.hom.app (op W)).hom y' := fun y' ↦ by
    rw [map_mul]
    exact congrArg (fun t ↦ t * (φ.right.hom.app (op W)).hom y') (secMap_structureMap φ (op W) r)
  exact h y

/-- The map on sections over `V` of a morphism of algebra sheaves is linear for the action of
`Γ(X, U)` through restriction, for `V ≤ U`. -/
theorem secMap_smulOfLE {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U))
    (y : Γ(A.underlyingModule, V)) :
    letI := moduleOfLE A.underlyingModule h
    letI := moduleOfLE B.underlyingModule h
    secMap φ (r • y) = r • secMap φ y :=
  secMap_smul φ (X.presheaf.map (homOfLE h).op r) y

/-- The map on sections of a morphism of algebra sheaves commutes with restriction. -/
theorem secMap_restrictₗ {U V : X.Opens} (h : V ≤ U) (y : Γ(A.underlyingModule, U)) :
    secMap φ (restrictₗ A.underlyingModule h y) =
      restrictₗ B.underlyingModule h (secMap φ y) :=
  secMap_naturality φ (homOfLE h).op y

/-! ### Sections of the equalizer -/

/-- The underlying section of `A` of a section of the equalizer. -/
def val {W : X.Opens} (z : Γ((equalizerAlgebra φ ψ).underlyingModule, W)) :
    Γ(A.underlyingModule, W) :=
  (show ↥(eqSubring φ ψ (op W)) from z).val

/-- A section of `A` on which `φ` and `ψ` agree, as a section of the equalizer. -/
def mk {W : X.Opens} (y : Γ(A.underlyingModule, W)) (hy : y ∈ eqSubring φ ψ (op W)) :
    Γ((equalizerAlgebra φ ψ).underlyingModule, W) :=
  show ↥(eqSubring φ ψ (op W)) from ⟨y, hy⟩

/-- The underlying section of `mk φ ψ y hy` is `y`. -/
theorem val_mk {W : X.Opens} (y : Γ(A.underlyingModule, W)) (hy : y ∈ eqSubring φ ψ (op W)) :
    val φ ψ (mk φ ψ y hy) = y :=
  rfl

/-- The two maps `φ` and `ψ` agree on the underlying section of a section of the equalizer. -/
theorem secMap_val_eq {W : X.Opens} (z : Γ((equalizerAlgebra φ ψ).underlyingModule, W)) :
    secMap φ (val φ ψ z) = secMap ψ (val φ ψ z) :=
  (show ↥(eqSubring φ ψ (op W)) from z).2

/-- A section of the equalizer is determined by its underlying section of `A`. -/
theorem val_inj {W : X.Opens} {z₁ z₂ : Γ((equalizerAlgebra φ ψ).underlyingModule, W)}
    (h : val φ ψ z₁ = val φ ψ z₂) : z₁ = z₂ :=
  Subtype.ext h

/-- Taking the underlying section commutes with the `Γ(X, W)`-action. -/
theorem val_smul {W : X.Opens} (r : Γ(X, W))
    (z : Γ((equalizerAlgebra φ ψ).underlyingModule, W)) :
    val φ ψ (r • z) = r • val φ ψ z :=
  rfl

/-- Taking the underlying section over `V` commutes with the action of `Γ(X, U)` through
restriction, for `V ≤ U`. -/
theorem val_smulOfLE {U V : X.Opens} (h : V ≤ U) (r : Γ(X, U))
    (z : Γ((equalizerAlgebra φ ψ).underlyingModule, V)) :
    letI := moduleOfLE (equalizerAlgebra φ ψ).underlyingModule h
    letI := moduleOfLE A.underlyingModule h
    val φ ψ (r • z) = r • val φ ψ z :=
  rfl

/-- The underlying section of the zero section of the equalizer is zero. -/
theorem val_zero {W : X.Opens} :
    val φ ψ (0 : Γ((equalizerAlgebra φ ψ).underlyingModule, W)) =
      (0 : Γ(A.underlyingModule, W)) :=
  rfl

/-- Taking the underlying section commutes with restriction. -/
theorem val_restrictₗ {U V : X.Opens} (h : V ≤ U)
    (z : Γ((equalizerAlgebra φ ψ).underlyingModule, U)) :
    letI := moduleOfLE (equalizerAlgebra φ ψ).underlyingModule h
    letI := moduleOfLE A.underlyingModule h
    val φ ψ (restrictₗ (equalizerAlgebra φ ψ).underlyingModule h z) =
      restrictₗ A.underlyingModule h (val φ ψ z) :=
  rfl

/-! ### Quasi-coherence -/

section Quasicoherence

variable [A.IsQuasicoherent] [B.IsQuasicoherent]

/-- **The sections of the equalizer over a basic open are a localization.** For an affine open
`U` of `X` and a section `a : Γ(X, U)`, the sections of `equalizerAlgebra φ ψ` over
`X.basicOpen a` are the localization away from `a` of its sections over `U`. -/
theorem isLocalizedModule_equalizerAlgebra {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) :
    letI := moduleOfLE (equalizerAlgebra φ ψ).underlyingModule (X.basicOpen_le a)
    IsLocalizedModule.Away a
      (restrictₗ (equalizerAlgebra φ ψ).underlyingModule (X.basicOpen_le a)) := by
  let := moduleOfLE (equalizerAlgebra φ ψ).underlyingModule (X.basicOpen_le a)
  let := moduleOfLE A.underlyingModule (X.basicOpen_le a)
  let := moduleOfLE B.underlyingModule (X.basicOpen_le a)
  have hA : IsLocalizedModule.Away a (restrictₗ A.underlyingModule (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ A.underlyingModule hU a rfl (X.basicOpen_le a)
  have hB : IsLocalizedModule.Away a (restrictₗ B.underlyingModule (X.basicOpen_le a)) :=
    isLocalizedModule_restrictₗ B.underlyingModule hU a rfl (X.basicOpen_le a)
  obtain ⟨hAinj, hAsurj⟩ :=
    smul_bijective_of_isLocalizedModule (restrictₗ A.underlyingModule (X.basicOpen_le a)) a
  obtain ⟨hBinj, -⟩ :=
    smul_bijective_of_isLocalizedModule (restrictₗ B.underlyingModule (X.basicOpen_le a)) a
  refine IsLocalizedModule.Away.mk_of_addCommGroup (isUnit_algebraMap_end ?_ ?_) ?_ ?_
  · intro z₁ z₂ hz
    refine val_inj φ ψ (hAinj _ _ ?_)
    rw [← val_smulOfLE φ ψ (X.basicOpen_le a) a z₁, ← val_smulOfLE φ ψ (X.basicOpen_le a) a z₂, hz]
  · intro z
    obtain ⟨w, hw⟩ := hAsurj (val φ ψ z)
    have hwmem : w ∈ eqSubring φ ψ (op (X.basicOpen a)) := by
      rw [mem_eqSubring_iff']
      refine hBinj _ _ ?_
      rw [← secMap_smulOfLE φ (X.basicOpen_le a) a w, ← secMap_smulOfLE ψ (X.basicOpen_le a) a w,
        hw]
      exact secMap_val_eq φ ψ z
    exact ⟨mk φ ψ w hwmem, val_inj φ ψ hw⟩
  · intro z
    obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj
      (restrictₗ A.underlyingModule (X.basicOpen_le a)) a (val φ ψ z)
    have hd : restrictₗ B.underlyingModule (X.basicOpen_le a) (secMap φ x - secMap ψ x) =
        restrictₗ B.underlyingModule (X.basicOpen_le a) 0 := by
      rw [map_zero, map_sub, ← secMap_restrictₗ φ (X.basicOpen_le a) x,
        ← secMap_restrictₗ ψ (X.basicOpen_le a) x, ← hx,
        secMap_smulOfLE φ (X.basicOpen_le a) (a ^ n) (val φ ψ z),
        secMap_smulOfLE ψ (X.basicOpen_le a) (a ^ n) (val φ ψ z), secMap_val_eq φ ψ z, sub_self]
    obtain ⟨m, hm⟩ := IsLocalizedModule.Away.exists_of_eq
      (f := restrictₗ B.underlyingModule (X.basicOpen_le a)) a hd
    have hymem : (a ^ m • x : Γ(A.underlyingModule, U)) ∈ eqSubring φ ψ (op U) := by
      rw [mem_eqSubring_iff', secMap_smul φ (a ^ m) x, secMap_smul ψ (a ^ m) x]
      rw [smul_zero, smul_sub, sub_eq_zero] at hm
      exact hm
    refine ⟨m + n, mk φ ψ (a ^ m • x) hymem, val_inj φ ψ ?_⟩
    rw [val_smulOfLE φ ψ (X.basicOpen_le a) (a ^ (m + n)) z,
      val_restrictₗ φ ψ (X.basicOpen_le a) (mk φ ψ (a ^ m • x) hymem),
      val_mk φ ψ (a ^ m • x) hymem, map_smul, ← hx, smul_smul, ← pow_add]
  · intro y hy
    have h0 : restrictₗ A.underlyingModule (X.basicOpen_le a) (val φ ψ y) =
        restrictₗ A.underlyingModule (X.basicOpen_le a) 0 := by
      rw [map_zero, ← val_restrictₗ φ ψ (X.basicOpen_le a) y, hy, val_zero]
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq
      (f := restrictₗ A.underlyingModule (X.basicOpen_le a)) a h0
    refine ⟨n, val_inj φ ψ ?_⟩
    rw [val_smul φ ψ (a ^ n) y, hn, smul_zero, val_zero]

/-- **The equalizer of two morphisms of quasi-coherent sheaves of `𝒪_X`-algebras is
quasi-coherent.** -/
instance isQuasicoherent_equalizerAlgebra : (equalizerAlgebra φ ψ).IsQuasicoherent :=
  isQuasicoherent_of_isLocalizedModule_restrictₗ (equalizerAlgebra φ ψ).underlyingModule
    fun _ hU a ↦ isLocalizedModule_equalizerAlgebra φ ψ hU a

end Quasicoherence

/-! ### The sections as an equalizer of algebras

Over an open `U` the sections of the equalizer are Mathlib's `AlgHom.equalizer` of the two
`Γ(X, U)`-algebra maps on sections. This is the form in which
`Stacks.FundamentalGroup.etale_and_moduleFinite_equalizer` applies to them. -/

/-- The map on sections over an open of a morphism of algebra sheaves, as a map of
`Γ(X, U)`-algebras. -/
def algSecMap (U : X.Opens) :
    letI := AlgebraSheaf.algebraSections A U
    letI := AlgebraSheaf.algebraSections B U
    AlgebraSheaf.sections A U →ₐ[Γ(X, U)] AlgebraSheaf.sections B U :=
  letI := AlgebraSheaf.algebraSections A U
  letI := AlgebraSheaf.algebraSections B U
  { (φ.right.hom.app (op U)).hom with
    commutes' := secMap_structureMap φ (op U) }

/-- The sections of the equalizer over an open are the underlying subring of the equalizer
subalgebra of the two maps of `Γ(X, U)`-algebras on sections. -/
theorem eqSubring_eq_toSubring_equalizer (U : X.Opens) :
    letI := AlgebraSheaf.algebraSections A U
    letI := AlgebraSheaf.algebraSections B U
    eqSubring φ ψ (op U) = (AlgHom.equalizer (algSecMap φ U) (algSecMap ψ U)).toSubring :=
  rfl

/-! ### The equalizer in the category of quasi-coherent algebras -/

section Quasicoherent

variable {A' B' : QuasicoherentAlgebra X} (φ' ψ' : A' ⟶ B')

/-- **The equalizer of two morphisms of quasi-coherent `𝒪_X`-algebras, as an object of the
category of quasi-coherent `𝒪_X`-algebras.** -/
def quasicoherentEqualizer : QuasicoherentAlgebra X :=
  ⟨equalizerAlgebra φ'.hom ψ'.hom,
    @isQuasicoherent_equalizerAlgebra X A'.obj B'.obj φ'.hom ψ'.hom A'.property B'.property⟩

/-- The inclusion of the equalizer of two morphisms of quasi-coherent algebras into the source. -/
def quasicoherentEqualizerι : quasicoherentEqualizer φ' ψ' ⟶ A' :=
  ObjectProperty.homMk (equalizerAlgebraι φ'.hom ψ'.hom)

/-- The inclusion of the equalizer equalizes `φ'` and `ψ'`. -/
theorem quasicoherentEqualizerι_comp :
    quasicoherentEqualizerι φ' ψ' ≫ φ' = quasicoherentEqualizerι φ' ψ' ≫ ψ' :=
  ObjectProperty.hom_ext _ (equalizerAlgebraι_comp φ'.hom ψ'.hom)

/-- **The category of quasi-coherent `𝒪_X`-algebras has equalizers**, computed on sections: the
equalizer of `φ'` and `ψ'` is the sheaf of algebras whose sections over an open are the sections
on which `φ'` and `ψ'` agree. -/
def isLimitQuasicoherentFork :
    IsLimit (Fork.ofι (quasicoherentEqualizerι φ' ψ') (quasicoherentEqualizerι_comp φ' ψ')) :=
  Fork.IsLimit.mk _
    (fun s ↦ ObjectProperty.homMk (lift φ'.hom ψ'.hom s.ι.hom
      (congrArg InducedCategory.Hom.hom s.condition)))
    (fun s ↦ ObjectProperty.hom_ext _ (lift_comp_ι φ'.hom ψ'.hom s.ι.hom
      (congrArg InducedCategory.Hom.hom s.condition)))
    (fun s _m hm ↦ ObjectProperty.hom_ext _ (hom_ext φ'.hom ψ'.hom
      ((congrArg InducedCategory.Hom.hom hm).trans
        (lift_comp_ι φ'.hom ψ'.hom s.ι.hom
          (congrArg InducedCategory.Hom.hom s.condition)).symm)))

/-- Two parallel morphisms of quasi-coherent `𝒪_X`-algebras have an equalizer. -/
instance hasLimitParallelPair_quasicoherentAlgebra : HasLimit (parallelPair φ' ψ') :=
  HasLimit.mk ⟨_, isLimitQuasicoherentFork φ' ψ'⟩

/-- The category of quasi-coherent `𝒪_X`-algebras has equalizers. -/
instance hasEqualizers_quasicoherentAlgebra (X : Scheme.{u}) :
    HasEqualizers (QuasicoherentAlgebra X) :=
  hasEqualizers_of_hasLimit_parallelPair _

end Quasicoherent

/-! ### The equalizer of finite étale algebras

Over an open where the sections of `A` and of `B` are finite étale over the sections of the
structure sheaf, so are the sections of the equalizer: this is the affine, algebraic
right-exactness statement `Stacks.FundamentalGroup.etale_and_moduleFinite_equalizer`. Hence the
relative spectrum of the equalizer is a finite étale cover of the base. -/

/-- **The sections of the equalizer are finite étale** over an open where the sections of `A` and
of `B` are. -/
theorem etale_and_finite_app_equalizerAlgebra (U : X.Opens)
    (hAe : RingHom.Etale (A.hom.hom.app (op U)).hom)
    (hAf : RingHom.Finite (A.hom.hom.app (op U)).hom)
    (hBe : RingHom.Etale (B.hom.hom.app (op U)).hom)
    (hBf : RingHom.Finite (B.hom.hom.app (op U)).hom) :
    RingHom.Etale ((equalizerAlgebra φ ψ).hom.hom.app (op U)).hom ∧
      RingHom.Finite ((equalizerAlgebra φ ψ).hom.hom.app (op U)).hom := by
  let := AlgebraSheaf.algebraSections A U
  let := AlgebraSheaf.algebraSections B U
  have : Algebra.Etale Γ(X, U) (AlgebraSheaf.sections A U) := RingHom.etale_algebraMap.mp hAe
  have : Module.Finite Γ(X, U) (AlgebraSheaf.sections A U) := RingHom.finite_algebraMap.mp hAf
  have : Algebra.Etale Γ(X, U) (AlgebraSheaf.sections B U) := RingHom.etale_algebraMap.mp hBe
  have : Module.Finite Γ(X, U) (AlgebraSheaf.sections B U) := RingHom.finite_algebraMap.mp hBf
  obtain ⟨he, hf⟩ := Stacks.FundamentalGroup.etale_and_moduleFinite_equalizer
    Γ(X, U) (AlgebraSheaf.sections A U) (AlgebraSheaf.sections B U)
    (algSecMap φ U) (algSecMap ψ U)
  exact ⟨RingHom.etale_algebraMap.mpr he, RingHom.finite_algebraMap.mpr hf⟩

/-- **The relative spectrum of the equalizer of two morphisms of quasi-coherent algebras is a
finite étale cover of the base**, as soon as the sections of both algebras over every affine open
are finite étale over the sections of the structure sheaf. -/
theorem isFinite_and_etale_relativeSpecToBase_equalizerAlgebra
    [A.IsQuasicoherent] [B.IsQuasicoherent]
    (hA : ∀ U : X.affineOpens, RingHom.Etale (A.hom.hom.app (op (U : X.Opens))).hom ∧
      RingHom.Finite (A.hom.hom.app (op (U : X.Opens))).hom)
    (hB : ∀ U : X.affineOpens, RingHom.Etale (B.hom.hom.app (op (U : X.Opens))).hom ∧
      RingHom.Finite (B.hom.hom.app (op (U : X.Opens))).hom) :
    IsFinite (relativeSpecToBase (equalizerAlgebra φ ψ)) ∧
      Etale (relativeSpecToBase (equalizerAlgebra φ ψ)) := by
  have h (U : X.affineOpens) := etale_and_finite_app_equalizerAlgebra φ ψ
    (U : X.Opens) (hA U).1 (hA U).2 (hB U).1 (hB U).2
  exact ⟨isFinite_relativeSpecToBase _ fun U ↦ (h U).2,
    etale_relativeSpecToBase _ fun U ↦ (h U).1⟩

/-! ### The case of two finite étale covers -/

section FiniteEtaleCovers

variable {Y Z : Scheme.{u}}

/-- For a finite étale `p : Y ⟶ X`, the structure map of `p_* 𝒪_Y` on sections over an affine
open is finite étale. -/
theorem etale_and_finite_app_pushforwardAlgebra (p : Y ⟶ X) [IsFinite p] [Etale p]
    (U : X.Opens) (hU : IsAffineOpen U) :
    RingHom.Etale ((pushforwardAlgebra p).hom.hom.app (op U)).hom ∧
      RingHom.Finite ((pushforwardAlgebra p).hom.hom.app (op U)).hom :=
  ⟨(etale_iff_app p).mp ‹Etale p› U hU, IsFinite.finite_app p U hU⟩

/-- **The relative spectrum of the equalizer of two morphisms between the pushed-forward
structure sheaves of two finite étale covers of `X` is itself a finite étale cover of `X`.** This
is the geometric half of the right-exactness statement of Stacks Tag 0BN9: under the
anti-equivalence of Tag 01SA, two morphisms `Y ⇉ Z` of finite étale covers of `X` correspond to
two morphisms `q_* 𝒪_Z ⇉ p_* 𝒪_Y` of quasi-coherent algebras, and the coequalizer of the first
pair is the relative spectrum of the equalizer of the second. -/
theorem isFinite_and_etale_relativeSpecToBase_of_finiteEtale (p : Y ⟶ X) (q : Z ⟶ X)
    [IsFinite p] [Etale p] [IsFinite q] [Etale q]
    (φ' ψ' : pushforwardAlgebra p ⟶ pushforwardAlgebra q) :
    letI := isQuasicoherent_pushforwardAlgebra p
    letI := isQuasicoherent_pushforwardAlgebra q
    IsFinite (relativeSpecToBase (equalizerAlgebra φ' ψ')) ∧
      Etale (relativeSpecToBase (equalizerAlgebra φ' ψ')) :=
  let := isQuasicoherent_pushforwardAlgebra p
  let := isQuasicoherent_pushforwardAlgebra q
  isFinite_and_etale_relativeSpecToBase_equalizerAlgebra φ' ψ'
    (fun U ↦ etale_and_finite_app_pushforwardAlgebra p (U : X.Opens) U.2)
    (fun U ↦ etale_and_finite_app_pushforwardAlgebra q (U : X.Opens) U.2)

end FiniteEtaleCovers

end Stacks.QuasicoherentAlgebraEqualizer

end
