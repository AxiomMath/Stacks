module

public import Mathlib.AlgebraicGeometry.Modules.Presheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.RingTheory.Etale.Kaehler
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.ComparisonAndDegreeZero
public import StacksCore.Tactic.StacksAttribute

/-!
# Derivations on the cohomology of an étale scheme

An absolute derivation of a ring acts canonically, as a twisted derivation, on the
structure-sheaf cohomology modules of a quasi-compact, quasi-separated étale scheme.

## Main definitions

* `structureSheafCohomology` is the cohomology of the structure sheaf as a module over the
  base ring.
* `SheafDerivation` records compatible extensions of a base derivation on opens, normalized
  by the unique extension to every affine étale algebra of sections.
* `inducedCohomology` applies derived sections to an additive sheaf operator, using the
  canonical comparison between module-valued and abelian-sheaf cohomology.
* `TwistedDerivation` packages the induced operator with its Leibniz law.

## Main results

* `subsingleton_sheafDerivation`: the affine-normalized sheaf derivation is unique.
* `nonempty_twistedDerivation`: the affine-normalized sheaf derivation exists, and the
  Leibniz law holds for its induced operator on cohomology.
* `etaleCohomologyDerivation` selects this uniquely determined derivation and operator.

## Implementation notes

On an affine open the sections form a formally étale algebra over the base ring, so the base
derivation extends to them uniquely; base changing the module of differentials along a formally
étale map produces that extension. The extensions are compatible with restriction, so they glue
to an additive endomorphism of the structure sheaf, to which one applies sheaf cohomology. In
every degree the comparison of Stacks 01F1 identifies this cohomology with the underlying group
of the module-valued right derived evaluation, and restriction of scalars along the structure
morphism supplies the base-ring module structure.

All schemes and rings live in a single universe, as required by the common category containing
the morphism `V ⟶ Spec A`.

## References

* [Stacks Project, Tag 0EC7](https://stacks.math.columbia.edu/tag/0EC7)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open Stacks.Cohomology.ModuleComparison
open scoped TensorProduct

universe u

namespace Stacks.EtaleDerivation

/-- The ring of global sections of a scheme, as the coefficient ring over which global
module-valued sections are taken. -/
abbrev globalRing (V : Scheme.{u}) : RingCat.{u} := (V.ringCatSheaf).obj.obj (op (⊤ : V.Opens))

/-- A section of the structure sheaf, viewed as an element of the underlying sheaf of
(not necessarily commutative) rings. -/
abbrev ringSection {V : Scheme.{u}} (U : (Opens ↥V)ᵒᵖ) (s : Γ(V, U.unop)) :
    (V.ringCatSheaf).obj.obj U := s

/-- Extend a derivation across a formally étale algebra by base changing the
module of differentials. -/
private noncomputable def extendDerivationFormallyEtale
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra.FormallyEtale A B] (θ : Derivation ℤ A A) : Derivation ℤ B C := by
  let θB : Derivation ℤ A C := (Algebra.linearMap A C).compDer θ
  let e : B ⊗[A] Ω[A⁄ℤ] ≃ₗ[B] Ω[B⁄ℤ] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A B
  let L : B ⊗[A] Ω[A⁄ℤ] →ₗ[B] C :=
    LinearMap.liftBaseChange B θB.liftKaehlerDifferential
  exact KaehlerDifferential.linearMapEquivDerivation (R := ℤ) (S := B) (M := C)
    (L.comp e.symm.toLinearMap)

/-- The étale extension agrees with the original derivation on base scalars. -/
private theorem extendDerivationFormallyEtale_algebraMap
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra.FormallyEtale A B] (θ : Derivation ℤ A A) (a : A) :
    extendDerivationFormallyEtale θ (algebraMap A B a) = algebraMap A C (θ a) := by
  let θB : Derivation ℤ A C := (Algebra.linearMap A C).compDer θ
  let e : B ⊗[A] Ω[A⁄ℤ] ≃ₗ[B] Ω[B⁄ℤ] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A B
  let L : B ⊗[A] Ω[A⁄ℤ] →ₗ[B] C :=
    LinearMap.liftBaseChange B θB.liftKaehlerDifferential
  unfold extendDerivationFormallyEtale
  show L (e.symm (KaehlerDifferential.D ℤ B (algebraMap A B a))) = _
  rw [KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_symm_D_algebraMap]
  simp only [L, LinearMap.liftBaseChange_tmul, one_smul, θB,
    Derivation.liftKaehlerDifferential_comp_D]
  rfl

/-- Formal étaleness also makes this extension unique. -/
private theorem extendDerivationFormallyEtale_unique
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra.FormallyEtale A B] (θ : Derivation ℤ A A)
    (D : Derivation ℤ B C)
    (hD : ∀ a : A, D (algebraMap A B a) = algebraMap A C (θ a)) :
    D = extendDerivationFormallyEtale θ := by
  let θB : Derivation ℤ A C := (Algebra.linearMap A C).compDer θ
  let e : B ⊗[A] Ω[A⁄ℤ] ≃ₗ[B] Ω[B⁄ℤ] :=
    KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale ℤ A B
  let L : B ⊗[A] Ω[A⁄ℤ] →ₗ[B] C :=
    LinearMap.liftBaseChange B θB.liftKaehlerDifferential
  let p : Ω[A⁄ℤ] →ₗ[A] C :=
    (D.liftKaehlerDifferential.restrictScalars A).comp
      ((e.toLinearMap.restrictScalars A).comp (TensorProduct.mk A B Ω[A⁄ℤ] 1))
  have hp : p = θB.liftKaehlerDifferential := by
    apply LinearMap.ext
    intro ω
    show p ω = θB.liftKaehlerDifferential ω
    have hmem : ω ∈ Submodule.span A (Set.range (KaehlerDifferential.D ℤ A)) := by
      rw [KaehlerDifferential.span_range_derivation]
      exact Submodule.mem_top
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hmem
    · rintro x ⟨a, rfl⟩
      have he : e (1 ⊗ₜ[A] KaehlerDifferential.D ℤ A a) =
          KaehlerDifferential.D ℤ B (algebraMap A B a) := by
        simp [e]
      show D.liftKaehlerDifferential (e (1 ⊗ₜ[A] KaehlerDifferential.D ℤ A a)) = _
      rw [he, Derivation.liftKaehlerDifferential_comp_D, hD,
        Derivation.liftKaehlerDifferential_comp_D]
      rfl
    · simp [p]
    · intro x y _ _ hx hy
      show p (x + y) = θB.liftKaehlerDifferential (x + y)
      rw [map_add, map_add, hx, hy]
    · intro a x _ hx
      show p (a • x) = θB.liftKaehlerDifferential (a • x)
      rw [map_smul, map_smul, hx]
  have hω (ω : Ω[A⁄ℤ]) :
      D.liftKaehlerDifferential (e (1 ⊗ₜ[A] ω)) = θB.liftKaehlerDifferential ω :=
    LinearMap.congr_fun hp ω
  have hcomp : D.liftKaehlerDifferential.comp e.toLinearMap = L := by
    apply LinearMap.ext
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul b ω =>
        have he : e (b ⊗ₜ[A] ω) = b • e (1 ⊗ₜ[A] ω) := by simp [e]
        show D.liftKaehlerDifferential (e (b ⊗ₜ[A] ω)) = L (b ⊗ₜ[A] ω)
        rw [he, map_smul, hω, LinearMap.liftBaseChange_tmul]
    | add x y hx hy =>
        show (D.liftKaehlerDifferential.comp e.toLinearMap) (x + y) = L (x + y)
        rw [map_add, L.map_add, hx, hy]
  have htarget : (extendDerivationFormallyEtale θ).liftKaehlerDifferential =
      L.comp e.symm.toLinearMap := by
    let E : (Ω[B⁄ℤ] →ₗ[B] C) ≃ₗ[B] Derivation ℤ B C :=
      KaehlerDifferential.linearMapEquivDerivation (R := ℤ) (S := B) (M := C)
    show E.symm (E (L.comp e.symm.toLinearMap)) = _
    exact E.symm_apply_apply _
  have hlift : D.liftKaehlerDifferential =
      (extendDerivationFormallyEtale θ).liftKaehlerDifferential := by
    apply LinearMap.ext
    intro ω
    have heq := congrArg (fun g ↦ g (e.symm ω)) hcomp
    change D.liftKaehlerDifferential (e (e.symm ω)) = L (e.symm ω) at heq
    rw [e.apply_symm_apply] at heq
    have ht := congrArg (fun g : Ω[B⁄ℤ] →ₗ[B] C ↦ g ω) htarget
    change (extendDerivationFormallyEtale θ).liftKaehlerDifferential ω =
      L (e.symm ω) at ht
    exact heq.trans ht.symm
  apply Derivation.ext
  intro b
  rw [← Derivation.liftKaehlerDifferential_comp_D D b, hlift,
    Derivation.liftKaehlerDifferential_comp_D]

/-- Restricting the canonical extension along an algebra map gives the canonical
extension with values in the target algebra. -/
private theorem extendDerivationFormallyEtale_restrict
    {A B C : Type u} [CommRing A] [CommRing B] [CommRing C] [Algebra A B]
    [Algebra A C] [Algebra B C] [IsScalarTower A B C]
    [Algebra.FormallyEtale A B] (θ : Derivation ℤ A A) :
    (Algebra.linearMap B C).compDer
        (extendDerivationFormallyEtale (A := A) (B := B) (C := B) θ) =
      extendDerivationFormallyEtale (A := A) (B := B) (C := C) θ := by
  apply extendDerivationFormallyEtale_unique θ
  intro a
  show algebraMap B C
    (extendDerivationFormallyEtale (A := A) (B := B) (C := B) θ
      (algebraMap A B a)) = algebraMap A C (θ a)
  rw [extendDerivationFormallyEtale_algebraMap]
  exact (IsScalarTower.algebraMap_apply A B C (θ a)).symm

/-- The sections of an affine open of an étale scheme are formally étale over the base ring. -/
private theorem affineSections_formallyEtale
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (U : V.Opens) (hU : IsAffineOpen U) :
    letI : Algebra A Γ(V, U) :=
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
    Algebra.FormallyEtale A Γ(V, U) := by
  let : Algebra A Γ(V, U) :=
    ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U (by simp)).hom.toAlgebra
  have hφ : RingHom.Etale ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ U (by simp)).hom :=
    RingHom.Etale.stableUnderComposition _ _
      (RingHom.Etale.of_bijective
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv))
      (Etale.etale_appLE f (isAffineOpen_top (Spec (.of A))) hU (by simp))
  let : Algebra.Etale A Γ(V, U) := hφ.toAlgebra
  infer_instance

/-- The unique extension on the sections of an affine open of an étale scheme. -/
private noncomputable def affineSectionsDerivation
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) (U : V.Opens) (hU : IsAffineOpen U) :
    Derivation ℤ Γ(V, U) Γ(V, U) := by
  let B := Γ(V, U)
  let eA := Scheme.ΓSpecIso (.of A)
  let fU := f.appLE ⊤ U (by simp)
  let φ := eA.inv ≫ fU
  letI : Algebra A B := φ.hom.toAlgebra
  haveI := affineSections_formallyEtale f U hU
  exact extendDerivationFormallyEtale θ

/-- The extension on an affine open agrees with the base derivation on base scalars. -/
private theorem affineSectionsDerivation_extends_base
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) (U : V.Opens) (hU : IsAffineOpen U) (a : A) :
    affineSectionsDerivation f θ U hU
        (f.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of A)).inv a)) =
      f.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of A)).inv (θ a)) := by
  let B := Γ(V, U)
  let eA := Scheme.ΓSpecIso (.of A)
  let fU := f.appLE ⊤ U (by simp)
  let φ := eA.inv ≫ fU
  let : Algebra A B := φ.hom.toAlgebra
  have := affineSections_formallyEtale f U hU
  show extendDerivationFormallyEtale θ (algebraMap A B a) = _
  rw [extendDerivationFormallyEtale_algebraMap]
  rfl

/-- A derivation of the sections of an affine open that extends the base derivation is the
canonical extension. -/
private theorem affineSectionsDerivation_unique
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) (U : V.Opens) (hU : IsAffineOpen U)
    (d : Derivation ℤ Γ(V, U) Γ(V, U))
    (hd : ∀ a : A,
      d (f.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of A)).inv a)) =
        f.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of A)).inv (θ a))) :
    d = affineSectionsDerivation f θ U hU := by
  let B := Γ(V, U)
  let eA := Scheme.ΓSpecIso (.of A)
  let fU := f.appLE ⊤ U (by simp)
  let φ := eA.inv ≫ fU
  let : Algebra A B := φ.hom.toAlgebra
  have := affineSections_formallyEtale f U hU
  have hD : ∀ a : A, d (algebraMap A B a) = algebraMap A B (θ a) := by
    intro a
    show d (φ.hom a) = φ.hom (θ a)
    simpa [eA, fU, φ] using hd a
  have hext := extendDerivationFormallyEtale_unique θ d hD
  simpa only [affineSectionsDerivation] using hext

/-- The extensions on two nested affine opens commute with restriction. -/
private theorem affineSectionsDerivation_naturality
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) {U W : V.Opens} (h : W ≤ U)
    (hU : IsAffineOpen U) (hW : IsAffineOpen W) :
    ∀ s : Γ(V, U),
      affineSectionsDerivation f θ W hW
          (V.presheaf.map (homOfLE h).op s) =
        V.presheaf.map (homOfLE h).op (affineSectionsDerivation f θ U hU s) := by
  let B := Γ(V, U)
  let C := Γ(V, W)
  let eA := Scheme.ΓSpecIso (.of A)
  let fU := f.appLE ⊤ U (by simp)
  let fW := f.appLE ⊤ W (by simp)
  let φU := eA.inv ≫ fU
  let φW := eA.inv ≫ fW
  let r := V.presheaf.map (homOfLE h).op
  let : Algebra A B := φU.hom.toAlgebra
  let : Algebra A C := φW.hom.toAlgebra
  let : Algebra B C := r.hom.toAlgebra
  have hcomp : φU ≫ r = φW := by
    dsimp [φU, φW, fU, fW, r]
    rw [Category.assoc, f.appLE_map (U := ⊤) (V := U) (by simp) (homOfLE h).op]
  have hcompA (a : A) : r.hom (φU.hom a) = φW.hom a := by
    simpa only [CommRingCat.hom_comp, RingHom.comp_apply] using
      congrArg (fun g : CommRingCat.of A ⟶ CommRingCat.of C ↦ g.hom a) hcomp
  let : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq fun a ↦ (hcompA a).symm
  have := affineSections_formallyEtale f U hU
  have := affineSections_formallyEtale f W hW
  let D₁ : Derivation ℤ B C :=
    Derivation.compAlgebraMap B (affineSectionsDerivation f θ W hW)
  let D₂ : Derivation ℤ B C :=
    (Algebra.linearMap B C).compDer (affineSectionsDerivation f θ U hU)
  have hbaseU (a : A) :
      affineSectionsDerivation f θ U hU (φU.hom a) = φU.hom (θ a) :=
    affineSectionsDerivation_extends_base f θ U hU a
  have hbaseW (a : A) :
      affineSectionsDerivation f θ W hW (φW.hom a) = φW.hom (θ a) :=
    affineSectionsDerivation_extends_base f θ W hW a
  have hD₁ (a : A) : D₁ (algebraMap A B a) = algebraMap A C (θ a) := by
    show affineSectionsDerivation f θ W hW (r.hom (φU.hom a)) = φW.hom (θ a)
    rw [hcompA, hbaseW]
  have hD₂ (a : A) : D₂ (algebraMap A B a) = algebraMap A C (θ a) := by
    show r.hom (affineSectionsDerivation f θ U hU (φU.hom a)) = φW.hom (θ a)
    rw [hbaseU, hcompA]
  have hD₁D₂ : D₁ = D₂ := (extendDerivationFormallyEtale_unique θ D₁ hD₁).trans
    (extendDerivationFormallyEtale_unique θ D₂ hD₂).symm
  exact fun s ↦ congrArg (fun d : Derivation ℤ B C ↦ d s) hD₁D₂

/-- The affine opens contained in `U`. -/
private abbrev AffineOpenSubsets (V : Scheme.{u}) (U : V.Opens) :=
  {W : V.Opens // IsAffineOpen W ∧ W ≤ U}

/-- The affine opens contained in `U` cover `U`. -/
private theorem affineOpenSubsets_cover (V : Scheme.{u}) (U : V.Opens) :
    iSup (fun i : AffineOpenSubsets V U => (i : V.Opens)) = U := by
  apply le_antisymm
  · exact iSup_le fun i ↦ i.property.2
  · intro x hx
    rw [Opens.mem_iSup]
    obtain ⟨_, ⟨W, hWaff, rfl⟩, hxW, hWU⟩ :=
      V.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
    exact ⟨⟨W, hWaff, hWU⟩, hxW⟩

/-- Restricting a section in two steps is restricting it in one. -/
private theorem presheaf_restrict_comp_apply
    {V : Scheme.{u}} {T U W : V.Opens} (hTU : T ≤ U) (hUW : U ≤ W)
    (s : Γ(V, W)) :
    V.presheaf.map (homOfLE hTU).op
        (V.presheaf.map (homOfLE hUW).op s) =
      V.presheaf.map (homOfLE (hTU.trans hUW)).op s := by
  have hm : V.presheaf.map (homOfLE hUW).op ≫
      V.presheaf.map (homOfLE hTU).op =
        V.presheaf.map (homOfLE (hTU.trans hUW)).op := by
    rw [← V.presheaf.map_comp]
    congr 1
  exact ConcreteCategory.congr_hom hm s

/-- The extensions on two affine opens contained in `U`, applied to the restrictions of a
section over `U`, agree on the intersection. -/
private theorem affineSectionsDerivation_compatible
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) {U : V.Opens}
    (i j : AffineOpenSubsets V U) (s : Γ(V, U)) :
    V.presheaf.map (homOfLE (inf_le_left : i.1 ⊓ j.1 ≤ i.1)).op
        (affineSectionsDerivation f θ i.1 i.2.1
          (V.presheaf.map (homOfLE i.2.2).op s)) =
      V.presheaf.map (homOfLE (inf_le_right : i.1 ⊓ j.1 ≤ j.1)).op
        (affineSectionsDerivation f θ j.1 j.2.1
          (V.presheaf.map (homOfLE j.2.2).op s)) := by
  apply V.IsSheaf.section_ext
  intro x hx
  obtain ⟨_, ⟨T, hTaff, rfl⟩, hxT, hTij⟩ :=
    V.isBasis_affineOpens.exists_subset_of_mem_open hx (i.1 ⊓ j.1).2
  have hTij' : T ≤ i.1 ⊓ j.1 := by simpa using hTij
  refine ⟨T, hTij', hxT, ?_⟩
  have hTi : T ≤ i.1 := hTij'.trans inf_le_left
  have hTj : T ≤ j.1 := hTij'.trans inf_le_right
  have hTU : T ≤ U := hTi.trans i.2.2
  have hleft := affineSectionsDerivation_naturality f θ hTi i.2.1 hTaff
    (V.presheaf.map (homOfLE i.2.2).op s)
  have hright := affineSectionsDerivation_naturality f θ hTj j.2.1 hTaff
    (V.presheaf.map (homOfLE j.2.2).op s)
  calc
    _ = V.presheaf.map (homOfLE hTi).op
        (affineSectionsDerivation f θ i.1 i.2.1
          (V.presheaf.map (homOfLE i.2.2).op s)) :=
      presheaf_restrict_comp_apply _ _ _
    _ = affineSectionsDerivation f θ T hTaff
        (V.presheaf.map (homOfLE hTi).op
          (V.presheaf.map (homOfLE i.2.2).op s)) := hleft.symm
    _ = affineSectionsDerivation f θ T hTaff
        (V.presheaf.map (homOfLE hTj).op
          (V.presheaf.map (homOfLE j.2.2).op s)) := by
      rw [presheaf_restrict_comp_apply, presheaf_restrict_comp_apply]
    _ = V.presheaf.map (homOfLE hTj).op
        (affineSectionsDerivation f θ j.1 j.2.1
          (V.presheaf.map (homOfLE j.2.2).op s)) := hright
    _ = _ := (presheaf_restrict_comp_apply _ _ _).symm

/-- The extensions on the affine opens contained in `U`, applied to the restrictions of a
section over `U`, glue to a unique section over `U`. -/
private theorem existsUnique_gluedAffineSections
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) (U : V.Opens) (s : Γ(V, U)) :
    ∃! t : Γ(V, U), ∀ i : AffineOpenSubsets V U,
      V.presheaf.map (homOfLE i.2.2).op t =
        affineSectionsDerivation f θ i.1 i.2.1
          (V.presheaf.map (homOfLE i.2.2).op s) := by
  let I := AffineOpenSubsets V U
  let W : I → V.Opens := fun i ↦ i.1
  let sections : ∀ i, Γ(V, W i) := fun i ↦
    affineSectionsDerivation f θ i.1 i.2.1
      (V.presheaf.map (homOfLE i.2.2).op s)
  have hcover : U ≤ iSup W := by
    rw [← affineOpenSubsets_cover V U]
  have hcompat : TopCat.Presheaf.IsCompatible V.presheaf W sections := by
    intro i j
    simpa only [I, W, sections,
      show Opens.infLELeft i.1 j.1 = homOfLE (inf_le_left : i.1 ⊓ j.1 ≤ i.1)
        from Subsingleton.elim _ _,
      show Opens.infLERight i.1 j.1 = homOfLE (inf_le_right : i.1 ⊓ j.1 ≤ j.1)
        from Subsingleton.elim _ _] using affineSectionsDerivation_compatible f θ i j s
  simpa only [I, W, sections] using
    TopCat.Sheaf.existsUnique_gluing' ⟨V.presheaf, V.IsSheaf⟩ W U
      (fun i ↦ homOfLE i.2.2) hcover sections hcompat

/-- The section over `U` glued from the extensions on the affine opens contained in `U`. -/
private noncomputable def gluedAffineSectionsOp
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) (U : V.Opens) (s : Γ(V, U)) : Γ(V, U) :=
  (existsUnique_gluedAffineSections f θ U s).choose

/-- The glued section restricts on each affine open to the extension there. -/
private theorem gluedAffineSectionsOp_restrict
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) (U : V.Opens) (s : Γ(V, U))
    (i : AffineOpenSubsets V U) :
    V.presheaf.map (homOfLE i.2.2).op (gluedAffineSectionsOp f θ U s) =
      affineSectionsDerivation f θ i.1 i.2.1
        (V.presheaf.map (homOfLE i.2.2).op s) :=
  (existsUnique_gluedAffineSections f θ U s).choose_spec.1 i

/-- The glued operator is additive. -/
private theorem gluedAffineSectionsOp_add
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) (U : V.Opens) (s t : Γ(V, U)) :
    gluedAffineSectionsOp f θ U (s + t) =
      gluedAffineSectionsOp f θ U s + gluedAffineSectionsOp f θ U t := by
  apply (existsUnique_gluedAffineSections f θ U (s + t)).unique
  · exact gluedAffineSectionsOp_restrict f θ U (s + t)
  · intro i
    simp only [map_add, gluedAffineSectionsOp_restrict]

/-- The glued operator sends zero to zero. -/
private theorem gluedAffineSectionsOp_zero
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) (U : V.Opens) :
    gluedAffineSectionsOp f θ U 0 = 0 := by
  apply (existsUnique_gluedAffineSections f θ U (0 : Γ(V, U))).unique
  · exact gluedAffineSectionsOp_restrict f θ U 0
  · intro i
    simp only [map_zero]

/-- The glued operator satisfies the Leibniz rule. -/
private theorem gluedAffineSectionsOp_leibniz
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) (U : V.Opens) (s t : Γ(V, U)) :
    gluedAffineSectionsOp f θ U (s * t) =
      s * gluedAffineSectionsOp f θ U t + t * gluedAffineSectionsOp f θ U s := by
  apply (existsUnique_gluedAffineSections f θ U (s * t)).unique
  · exact gluedAffineSectionsOp_restrict f θ U (s * t)
  · intro i
    simp only [map_mul, map_add, gluedAffineSectionsOp_restrict, Derivation.leibniz, smul_eq_mul]

/-- On an affine open the glued operator is the extension there. -/
private theorem gluedAffineSectionsOp_onAffine
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) (U : V.Opens) (hU : IsAffineOpen U)
    (s : Γ(V, U)) :
    gluedAffineSectionsOp f θ U s = affineSectionsDerivation f θ U hU s := by
  let i : AffineOpenSubsets V U := ⟨U, hU, le_rfl⟩
  simpa [i] using gluedAffineSectionsOp_restrict f θ U s i

/-- The section over `U` given by an element of the base ring. -/
private def baseSection
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    (U : V.Opens) (a : A) : Γ(V, U) :=
  f.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of A)).inv a)

/-- Base sections restrict to base sections. -/
private theorem baseSection_restrict
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    {U W : V.Opens} (h : W ≤ U) (a : A) :
    V.presheaf.map (homOfLE h).op (baseSection f U a) = baseSection f W a := by
  show (f.appLE ⊤ U (by simp) ≫ V.presheaf.map (homOfLE h).op).hom
      ((Scheme.ΓSpecIso (.of A)).inv a) = _
  exact ConcreteCategory.congr_hom
    (f.appLE_map (U := ⊤) (V := U) (by simp) (homOfLE h).op)
    ((Scheme.ΓSpecIso (.of A)).inv a)

/-- Multiplication by a base section on sections over an open. -/
private def baseScalarSectionsHom
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    (U : V.Opens) (a : A) : Γ(V, U) →+ Γ(V, U) where
  toFun s := baseSection f U a * s
  map_zero' := by simp
  map_add' s t := by simp [mul_add]

/-- The glued operator sends the base section of `a` to the base section of `θ a`. -/
private theorem gluedAffineSectionsOp_base
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) (U : V.Opens) (a : A) :
    gluedAffineSectionsOp f θ U (baseSection f U a) = baseSection f U (θ a) := by
  show (existsUnique_gluedAffineSections f θ U
    (baseSection f U a)).choose = _
  apply (existsUnique_gluedAffineSections f θ U
    (baseSection f U a)).choose_eq_iff.mpr
  intro i
  calc
    V.presheaf.map (homOfLE i.2.2).op (baseSection f U (θ a)) =
      baseSection f i.1 (θ a) := baseSection_restrict f i.2.2 (θ a)
    _ = affineSectionsDerivation f θ i.1 i.2.1 (baseSection f i.1 a) := by
      symm
      simpa [baseSection] using
        affineSectionsDerivation_extends_base f θ i.1 i.2.1 a
    _ = affineSectionsDerivation f θ i.1 i.2.1
        (V.presheaf.map (homOfLE i.2.2).op (baseSection f U a)) := by
      rw [baseSection_restrict]

/-- The glued operator commutes with restriction. -/
private theorem gluedAffineSectionsOp_naturality
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) {U W : V.Opens} (hUW : U ≤ W)
    (s : Γ(V, W)) :
    gluedAffineSectionsOp f θ U (V.presheaf.map (homOfLE hUW).op s) =
      V.presheaf.map (homOfLE hUW).op (gluedAffineSectionsOp f θ W s) := by
  refine (existsUnique_gluedAffineSections f θ U
    (V.presheaf.map (homOfLE hUW).op s)).unique
      (y₁ := gluedAffineSectionsOp f θ U (V.presheaf.map (homOfLE hUW).op s))
      (y₂ := V.presheaf.map (homOfLE hUW).op (gluedAffineSectionsOp f θ W s)) ?_ ?_
  · exact gluedAffineSectionsOp_restrict f θ U _
  · intro i
    let j : AffineOpenSubsets V W := ⟨i.1, i.2.1, i.2.2.trans hUW⟩
    calc
      V.presheaf.map (homOfLE i.2.2).op
          (V.presheaf.map (homOfLE hUW).op
            (gluedAffineSectionsOp f θ W s)) =
        V.presheaf.map (homOfLE j.2.2).op (gluedAffineSectionsOp f θ W s) :=
          presheaf_restrict_comp_apply i.2.2 hUW _
      _ = affineSectionsDerivation f θ i.1 i.2.1
          (V.presheaf.map (homOfLE j.2.2).op s) :=
            gluedAffineSectionsOp_restrict f θ W s j
      _ = affineSectionsDerivation f θ i.1 i.2.1
          (V.presheaf.map (homOfLE i.2.2).op
            (V.presheaf.map (homOfLE hUW).op s)) := by
              rw [presheaf_restrict_comp_apply]

/-- The glued operator on the sections over `U`, as a derivation. -/
private noncomputable def gluedSectionsDerivation
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) (U : V.Opens) :
    Derivation ℤ Γ(V, U) Γ(V, U) :=
  Derivation.mk' (AddMonoidHom.toIntLinearMap
    { toFun := gluedAffineSectionsOp f θ U
      map_zero' := gluedAffineSectionsOp_zero f θ U
      map_add' := gluedAffineSectionsOp_add f θ U })
    (gluedAffineSectionsOp_leibniz f θ U)

/-- Structure-sheaf cohomology in degree `i`, with its canonical module structure over the
base ring: the right derived functor of module-valued global sections, restricted along the
structure morphism. -/
abbrev structureSheafCohomology {A : Type u} [CommRing A] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of A)) (i : ℕ) : ModuleCat.{u} A :=
  let E : SheafOfModules.{u} (V.ringCatSheaf) ⥤ ModuleCat.{u} (globalRing V) :=
    SheafOfModules.evaluation (V.ringCatSheaf) (op (⊤ : V.Opens))
  let : E.Additive := ⟨by intros; rfl⟩
  (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom).obj
    ((E.rightDerived i).obj (SheafOfModules.unit (V.ringCatSheaf)))

/-- The underlying sheaf of abelian groups of the structure sheaf. -/
abbrev structureSheafAdditive (V : Scheme.{u}) :=
  (SheafOfModules.toSheaf (V.ringCatSheaf)).obj (SheafOfModules.unit (V.ringCatSheaf))

/-- Multiplication by a base section is natural on all sheaves of modules. -/
private def baseScalarModuleNatTrans
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    (a : A) : 𝟭 (SheafOfModules.{u} (V.ringCatSheaf)) ⟶
      𝟭 (SheafOfModules.{u} (V.ringCatSheaf)) where
  app M :=
    show M ⟶ M from
    { val :=
        { app U := by
            letI : CommRing ((V.ringCatSheaf).obj.obj U) :=
              inferInstanceAs (CommRing Γ(V, U.unop))
            exact ModuleCat.ofHom (LinearMap.lsmul ((V.ringCatSheaf).obj.obj U)
              (M.val.obj U) (ringSection U (baseSection f U.unop a)))
          naturality := by
            intro U W h
            ext x
            change ringSection W (baseSection f W.unop a) •
                (M.val.map h x : M.val.obj W) =
              M.val.map h (ringSection U (baseSection f U.unop a) • x)
            rw [M.val.map_smul]
            congr 1
            exact (baseSection_restrict f (leOfHom h.unop) a).symm } }
  naturality := by
    intro M N g
    ext U x
    exact ((g.val.app U).hom.map_smul (baseSection f U.unop a) x).symm

/-- Multiplication by a base section on the structure sheaf as a module. -/
private def baseScalarModuleHom
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    (a : A) : SheafOfModules.unit (V.ringCatSheaf) ⟶
      SheafOfModules.unit (V.ringCatSheaf) :=
  (baseScalarModuleNatTrans f a).app (SheafOfModules.unit (V.ringCatSheaf))

/-- The additive sheaf endomorphism given by multiplication by a base scalar. -/
private def baseScalarSheafHom
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    (a : A) : structureSheafAdditive V ⟶ structureSheafAdditive V :=
  (SheafOfModules.toSheaf (V.ringCatSheaf)).map (baseScalarModuleHom f a)

/-- On sections, `baseScalarSheafHom` is multiplication by the base section. -/
private theorem baseScalarSheafHom_apply
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    (a : A) (U : V.Opens) (s : Γ(V, U)) :
    (baseScalarSheafHom f a).hom.app (op U) s = baseScalarSectionsHom f U a s := by
  rfl

/-- The extension of a base derivation to the structure sheaf. On each affine open it
is the unique derivation extending the base derivation; the extensions commute with
restriction. -/
structure SheafDerivation {A : Type u} [CommRing A] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of A)) (θ : Derivation ℤ A A) where
  /-- The derivation on sections over an open. -/
  onSections (U : V.Opens) : Derivation ℤ Γ(V, U) Γ(V, U)
  /-- Compatibility with restriction to a smaller open. -/
  naturality {U W : V.Opens} (h : U ≤ W) (s : Γ(V, W)) :
    onSections U (V.presheaf.map (homOfLE h).op s) =
      V.presheaf.map (homOfLE h).op (onSections W s)
  /-- The derivation agrees with the given derivation on base scalars. -/
  extends_base (U : V.Opens) (a : A) :
    onSections U (f.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of A)).inv a)) =
      f.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of A)).inv (θ a))
  /-- On affine opens this is the unique extension to the étale algebra of sections. -/
  affine_normalization (U : V.Opens) (hU : IsAffineOpen U)
      (d : Derivation ℤ Γ(V, U) Γ(V, U))
      (hd : ∀ a : A,
        d (f.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of A)).inv a)) =
          f.appLE ⊤ U (by simp) ((Scheme.ΓSpecIso (.of A)).inv (θ a))) :
    onSections U = d

/-- The affine-normalized sheaf derivation obtained by gluing the affine extensions. -/
private noncomputable def canonicalSheafDerivation
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [Etale f] (θ : Derivation ℤ A A) : SheafDerivation f θ where
  onSections := gluedSectionsDerivation f θ
  naturality := by
    intro U W h s
    change gluedAffineSectionsOp f θ U (V.presheaf.map (homOfLE h).op s) = _
    exact gluedAffineSectionsOp_naturality f θ h s
  extends_base := by
    intro U a
    change gluedAffineSectionsOp f θ U (baseSection f U a) = _
    exact gluedAffineSectionsOp_base f θ U a
  affine_normalization := by
    intro U hU d hd
    rw [affineSectionsDerivation_unique f θ U hU d fun a ↦ by simpa only [baseSection] using hd a]
    ext s
    exact gluedAffineSectionsOp_onAffine f θ U hU s

/-- The additive sheaf endomorphism assembled from the compatible local derivations. -/
def SheafDerivation.toSheafHom {A : Type u} [CommRing A] {V : Scheme.{u}}
    {f : V ⟶ Spec (.of A)} {θ : Derivation ℤ A A} (D : SheafDerivation f θ) :
    structureSheafAdditive V ⟶ structureSheafAdditive V where
  hom :=
    { app := fun U ↦ AddCommGrpCat.ofHom (D.onSections U.unop).toAddMonoidHom
      naturality := by
        intro U W h
        ext s
        exact D.naturality (leOfHom h.unop) s }

/-- The Leibniz rule for a sheaf derivation against multiplication by a base scalar. -/
private theorem SheafDerivation.toSheafHom_baseScalar_leibniz
    {A : Type u} [CommRing A] {V : Scheme.{u}} {f : V ⟶ Spec (.of A)}
    {θ : Derivation ℤ A A} (D : SheafDerivation f θ) (a : A) :
    baseScalarSheafHom f a ≫ D.toSheafHom =
      baseScalarSheafHom f (θ a) + D.toSheafHom ≫ baseScalarSheafHom f a := by
  ext U s
  change Γ(V, U.unop) at s
  show D.onSections U.unop ((baseScalarSheafHom f a).hom.app U s) =
    (baseScalarSheafHom f (θ a)).hom.app U s +
      (baseScalarSheafHom f a).hom.app U (D.onSections U.unop s)
  rw [baseScalarSheafHom_apply f a U.unop s,
    baseScalarSheafHom_apply f (θ a) U.unop s,
    baseScalarSheafHom_apply f a U.unop (D.onSections U.unop s)]
  show D.onSections U.unop (baseSection f U.unop a * s) =
    baseSection f U.unop (θ a) * s + baseSection f U.unop a * D.onSections U.unop s
  rw [(D.onSections U.unop).leibniz]
  show baseSection f U.unop a * D.onSections U.unop s +
    s * D.onSections U.unop (baseSection f U.unop a) = _
  rw [show D.onSections U.unop (baseSection f U.unop a) =
    baseSection f U.unop (θ a) from D.extends_base U.unop a]
  ring

/-- The canonical comparison of Tag 01F1 between the underlying group of module-valued
structure-sheaf cohomology and abelian-sheaf cohomology of the structure sheaf. -/
def cohomologyComparison {A : Type u} [CommRing A] {V : Scheme.{u}}
    (_f : V ⟶ Spec (.of A)) (i : ℕ) :
    (forget₂ (ModuleCat (globalRing V)) AddCommGrpCat).obj
        (((SheafOfModules.evaluation (V.ringCatSheaf) (op (⊤ : V.Opens))).rightDerived i).obj
          (SheafOfModules.unit (V.ringCatSheaf))) ≅
      (((sheafSections (Opens.grothendieckTopology V) AddCommGrpCat).obj
        (op (⊤ : V.Opens))).rightDerived i).obj (structureSheafAdditive V) :=
  (rightDerivedSectionsForgetIso (V.ringCatSheaf) ⊤ i).app
    (SheafOfModules.unit (V.ringCatSheaf))

/-- The operator on structure-sheaf cohomology induced by an additive sheaf endomorphism:
derived sections applied to it, transported through the canonical comparison. -/
def inducedCohomology {A : Type u} [CommRing A] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of A)) (i : ℕ)
    (D : structureSheafAdditive V ⟶ structureSheafAdditive V) :
    structureSheafCohomology f i →+ structureSheafCohomology f i :=
  ((cohomologyComparison f i).hom ≫
    (((sheafSections (Opens.grothendieckTopology V) AddCommGrpCat).obj
      (op (⊤ : V.Opens))).rightDerived i).map D ≫
    (cohomologyComparison f i).inv).hom

/-- A scalar chain map induces the same scalar on homology. -/
private theorem homologyMap_apply_of_scalar
    {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}
    (K : HomologicalComplex (ModuleCat.{u} R) c) (g : K ⟶ K) (r : R)
    (hg : ∀ j (x : K.X j), g.f j x = r • x) (i : ι) (x : K.homology i) :
    HomologicalComplex.homologyMap g i x = r • x := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ i)).mp inferInstance x
  have hz : HomologicalComplex.cyclesMap g i z = r • z := by
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).mp inferInstance
    rw [← ConcreteCategory.comp_apply, HomologicalComplex.cyclesMap_i]
    show g.f i (K.iCycles i z) = K.iCycles i (r • z)
    rw [hg, (K.iCycles i).hom.map_smul]
  rw [← ConcreteCategory.comp_apply, HomologicalComplex.homologyπ_naturality]
  show K.homologyπ i (HomologicalComplex.cyclesMap g i z) = _
  rw [hz, (K.homologyπ i).hom.map_smul]

/-- Derived module-valued evaluation sends multiplication by a base section to
multiplication by its global value. -/
private theorem rightDerived_baseScalarModuleHom
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    (a : A) (i : ℕ) :
    let E : SheafOfModules.{u} (V.ringCatSheaf) ⥤ ModuleCat.{u} (globalRing V) :=
      SheafOfModules.evaluation (V.ringCatSheaf) (op (⊤ : V.Opens))
    letI : E.Additive := ⟨by intros; rfl⟩
    ∀ x : (E.rightDerived i).obj (SheafOfModules.unit (V.ringCatSheaf)),
      (E.rightDerived i).map (baseScalarModuleHom f a) x =
        ringSection (op (⊤ : V.Opens)) (baseSection f ⊤ a) • x := by
  intro E
  let : E.Additive := ⟨by intros; rfl⟩
  intro x
  let M := SheafOfModules.unit (V.ringCatSheaf)
  let I := injectiveResolution M
  let α := baseScalarModuleNatTrans f a
  let g : I.cocomplex ⟶ I.cocomplex :=
    { f := fun j ↦ α.app (I.cocomplex.X j)
      comm' := fun j k _ ↦ (α.naturality (I.cocomplex.d j k)).symm }
  have hg : I.ι.f 0 ≫ g.f 0 = baseScalarModuleHom f a ≫ I.ι.f 0 :=
    α.naturality (I.ι.f 0)
  have hn := I.isoRightDerivedObj_hom_naturality (baseScalarModuleHom f a) I g hg E i
  apply (ModuleCat.mono_iff_injective (I.isoRightDerivedObj E i).hom).mp inferInstance
  have hx := ConcreteCategory.congr_hom hn x
  change (I.isoRightDerivedObj E i).hom ((E.rightDerived i).map
    (baseScalarModuleHom f a) x) =
      HomologicalComplex.homologyMap ((E.mapHomologicalComplex _).map g) i
        ((I.isoRightDerivedObj E i).hom x) at hx
  rw [hx, (I.isoRightDerivedObj E i).hom.hom.map_smul]
  exact homologyMap_apply_of_scalar _ _
    (ringSection (op (⊤ : V.Opens)) (baseSection f ⊤ a)) (fun _ _ ↦ rfl) _ _

/-- Multiplication by a base scalar induces the module action of that scalar on cohomology. -/
private theorem inducedCohomology_baseScalar
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    (i : ℕ) (a : A) (x : structureSheafCohomology f i) :
    inducedCohomology f i (baseScalarSheafHom f a) x = a • x := by
  have hn := (rightDerivedSectionsForgetIso (V.ringCatSheaf) ⊤ i).hom.naturality
    (baseScalarModuleHom f a)
  have heq : (cohomologyComparison f i).hom ≫
      (((sheafSections (Opens.grothendieckTopology V) AddCommGrpCat).obj
        (op (⊤ : V.Opens))).rightDerived i).map (baseScalarSheafHom f a) ≫
        (cohomologyComparison f i).inv =
      (forget₂ (ModuleCat (globalRing V)) AddCommGrpCat).map
        (((SheafOfModules.evaluation (V.ringCatSheaf) (op (⊤ : V.Opens))).rightDerived i).map
          (baseScalarModuleHom f a)) := by
    have hn' : (cohomologyComparison f i).hom ≫
        (((sheafSections (Opens.grothendieckTopology V) AddCommGrpCat).obj
          (op (⊤ : V.Opens))).rightDerived i).map (baseScalarSheafHom f a) =
        (forget₂ (ModuleCat (globalRing V)) AddCommGrpCat).map
          (((SheafOfModules.evaluation (V.ringCatSheaf) (op (⊤ : V.Opens))).rightDerived i).map
            (baseScalarModuleHom f a)) ≫ (cohomologyComparison f i).hom := hn.symm
    rw [← Category.assoc, hn', Category.assoc, Iso.hom_inv_id, Category.comp_id]
  show ((cohomologyComparison f i).hom ≫ _ ≫ (cohomologyComparison f i).inv) x = _
  rw [heq]
  exact rightDerived_baseScalarModuleHom f a i x

/-- The induced operator of a composite is the composite of the induced operators. -/
private theorem inducedCohomology_comp_apply
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A)) (i : ℕ)
    (D E : structureSheafAdditive V ⟶ structureSheafAdditive V)
    (x : structureSheafCohomology f i) :
    inducedCohomology f i (D ≫ E) x =
      inducedCohomology f i E (inducedCohomology f i D x) := by
  let c := cohomologyComparison f i
  let F := (((sheafSections (Opens.grothendieckTopology V) AddCommGrpCat).obj
    (op (⊤ : V.Opens))).rightDerived i)
  show c.inv (F.map (D ≫ E) (c.hom x)) = c.inv (F.map E (c.hom (c.inv (F.map D (c.hom x)))))
  rw [Iso.inv_hom_id_apply, F.map_comp]
  rfl

/-- Right derived functors preserve addition of morphisms. -/
private theorem rightDerived_additive
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    [HasInjectiveResolutions C] (F : C ⥤ D) [F.Additive] (i : ℕ) :
    (F.rightDerived i).Additive := by
  have : (injectiveResolutions C).Additive := ⟨by
    intro X Y f g
    have hadd : (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X) +
            InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X)) =
        (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
            (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X)) +
          (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
            (InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X)) :=
      (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map_add
    show (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
        (InjectiveResolution.desc (f + g) (injectiveResolution Y)
          (injectiveResolution X)) =
      (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X)) +
        (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X))
    rw [← hadd]
    apply HomotopyCategory.eq_of_homotopy
    apply InjectiveResolution.descHomotopy (f + g)
    · simp
    · simp [Preadditive.comp_add, Preadditive.add_comp]⟩
  unfold Functor.rightDerived Functor.rightDerivedToHomotopyCategory
  infer_instance

/-- The induced operator of a sum is the sum of the induced operators. -/
private theorem inducedCohomology_add_apply
    {A : Type u} [CommRing A] {V : Scheme.{u}} (f : V ⟶ Spec (.of A)) (i : ℕ)
    (D E : structureSheafAdditive V ⟶ structureSheafAdditive V)
    (x : structureSheafCohomology f i) :
    inducedCohomology f i (D + E) x =
      inducedCohomology f i D x + inducedCohomology f i E x := by
  let F := (sheafSections (Opens.grothendieckTopology V) AddCommGrpCat).obj
    (op (⊤ : V.Opens))
  have : F.Additive := by
    show (sheafToPresheaf _ _ ⋙ (evaluation _ _).obj (op (⊤ : V.Opens))).Additive
    infer_instance
  have : (F.rightDerived i).Additive := rightDerived_additive F i
  show (cohomologyComparison f i).inv.hom
    ((F.rightDerived i).map (D + E) ((cohomologyComparison f i).hom x)) = _
  rw [Functor.map_add]
  exact map_add _ _ _

/-- The operator induced by a sheaf derivation satisfies the twisted Leibniz rule. -/
private theorem inducedCohomology_leibniz
    {A : Type u} [CommRing A] {V : Scheme.{u}} {f : V ⟶ Spec (.of A)}
    {θ : Derivation ℤ A A} (D : SheafDerivation f θ) (i : ℕ)
    (a : A) (x : structureSheafCohomology f i) :
    inducedCohomology f i D.toSheafHom (a • x) =
      θ a • x + a • inducedCohomology f i D.toSheafHom x := by
  have h := congrArg (fun h ↦ inducedCohomology f i h x)
    (D.toSheafHom_baseScalar_leibniz a)
  simpa only [inducedCohomology_add_apply, inducedCohomology_comp_apply,
    inducedCohomology_baseScalar] using h

/-- An affine-normalized sheaf derivation together with the twisted Leibniz law, for the
standard `A`-module structure, of the operator it induces on cohomology in degree `i`. -/
structure TwistedDerivation {A : Type u} [CommRing A] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of A)) (i : ℕ) (θ : Derivation ℤ A A) where
  /-- The affine-normalized extension to the structure sheaf. -/
  sheafDerivation : SheafDerivation f θ
  /-- The induced operator satisfies the twisted Leibniz rule. -/
  leibniz (a : A) (x : structureSheafCohomology f i) :
    inducedCohomology f i sheafDerivation.toSheafHom (a • x) =
      θ a • x + a • inducedCohomology f i sheafDerivation.toSheafHom x

/-- The underlying additive operator on the canonical cohomology module. -/
def TwistedDerivation.toAddMonoidHom {A : Type u} [CommRing A] {V : Scheme.{u}}
    {f : V ⟶ Spec (.of A)} {i : ℕ} {θ : Derivation ℤ A A}
    (D : TwistedDerivation f i θ) :
    structureSheafCohomology f i →+ structureSheafCohomology f i :=
  inducedCohomology f i D.sheafDerivation.toSheafHom

/-- The affine-normalized, restriction-compatible extension of a base derivation to the
structure sheaf is unique. -/
@[stacks 0EC7 "uniqueness"]
theorem subsingleton_sheafDerivation {A : Type u} [CommRing A] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of A)) (θ : Derivation ℤ A A) :
    Subsingleton (SheafDerivation f θ) := by
  refine ⟨fun D E ↦ ?_⟩
  cases D with
  | mk dD hDnat hDbase hDaff =>
    cases E with
    | mk dE hEnat hEbase hEaff =>
      congr 1
      funext U
      ext s
      apply V.IsSheaf.section_ext
      intro x hx
      obtain ⟨_, ⟨W : V.Opens, hWaff, rfl⟩, hxW, hWU⟩ :=
        V.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
      have hWU' : W ≤ U := hWU
      refine ⟨W, hWU', hxW, ?_⟩
      have hWE : dD W = dE W :=
        hDaff W hWaff (dE W) (hEbase W)
      rw [← hDnat hWU' s, ← hEnat hWU' s, hWE]

/-- An absolute derivation of the base ring extends to an affine-normalized derivation of the
structure sheaf of a quasi-compact, quasi-separated étale scheme. In every degree its induced
additive operator on the canonical cohomology module satisfies the twisted Leibniz rule. -/
@[stacks 0EC7 "existence and Leibniz rule"]
theorem nonempty_twistedDerivation {A : Type u} [CommRing A] {V : Scheme.{u}}
    (f : V ⟶ Spec (.of A)) [QuasiCompact f] [QuasiSeparated f] [Etale f]
    (θ : Derivation ℤ A A) (i : ℕ) : Nonempty (TwistedDerivation f i θ) :=
  ⟨{ sheafDerivation := canonicalSheafDerivation f θ
     leibniz := inducedCohomology_leibniz (canonicalSheafDerivation f θ) i }⟩

/-- The canonical affine-normalized extension and its induced cohomology operator. -/
noncomputable def etaleCohomologyDerivation {A : Type u} [CommRing A]
    {V : Scheme.{u}} (f : V ⟶ Spec (.of A))
    [QuasiCompact f] [QuasiSeparated f] [Etale f]
    (θ : Derivation ℤ A A) (i : ℕ) : TwistedDerivation f i θ :=
  (nonempty_twistedDerivation f θ i).some
end Stacks.EtaleDerivation
