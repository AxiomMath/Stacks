module

public import StacksFrontier.AlgebraicGeometry.Algebraization.CoherentTriple
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.IntegralSupport
public import StacksFrontier.AlgebraicGeometry.Modules.TildeFiniteness
public import StacksFrontier.AlgebraicGeometry.CoherentPullback.Basic
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.AffineComparison
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.RingTheory.Length.MaximalIdealPower
public import StacksFrontier.Algebra.Category.ModuleCat.FiniteLength
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.Completion.Quasicoherent.IdealPowerMultiple
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.LocalRing.Length
public import Mathlib.Algebra.Category.Grp.Zero
public import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of the closed-fibre map of a prepared extension

Let `A` be a Noetherian local ring, `f ∈ A`, and let `T` be a coherent triple for `(A, f)`. A
*prepared extension* of `T` is a coherent `f`-torsion-free module `F'` on `Spec A` together with
an isomorphism with `T.F` over the punctured spectrum, a map to `T.F₀` on the closed fibre, and
the compatibility of the two over the punctured closed fibre.

The map to `T.F₀` on the closed fibre becomes, on global sections and after restriction of
scalars from `A / fA` to `A`, a map of `A`-modules. This file proves that its kernel and its
cokernel have finite length over `A`, which is what makes the Euler characteristic attached to
`T` well defined.

## Main definitions

* `Stacks.Algebraization.PreparedExtension`: the data of a prepared extension.
* `Stacks.Algebraization.PreparedExtension.closedFibreMap`: its closed-fibre map on global
  sections, regarded as a map of `A`-modules.

## Main results

* `Stacks.Algebraization.kernel_finiteLength` and
  `Stacks.Algebraization.cokernel_finiteLength`: the kernel and the cokernel of the closed-fibre
  map have finite length over `A`.

## Implementation notes

The compatibility datum of a prepared extension forces the closed-fibre map to be an isomorphism
over the punctured closed fibre, so its kernel and cokernel are supported at the closed point of
the closed fibre. For a coherent module on the spectrum of a Noetherian local ring, support at
the closed point means that a power of the maximal ideal annihilates the global sections
([Stacks, Tag 01Y9], in the form
`Stacks.AlgebraicGeometry.IrreducibleDevissage.exists_isZero_idealPowSmul`), and a finite module
annihilated by a power of the maximal ideal has finite length. Restriction of scalars from
`A / fA` to `A` preserves finite length because the residue field extension is trivial, by
`IsLocalRing.length_restrictScalars`.

When `f` is a unit the closed fibre is empty and both modules are subsingletons, so the two
statements hold for trivial reasons; that case is separated out because the argument above needs
`f` to lie in the maximal ideal in order to identify the punctured closed fibre with the
punctured spectrum of `A / fA`.

Kernels and cokernels are taken in the category of modules, and transported across the
comparison with the global sections of the sheaf-theoretic kernel and cokernel; this is where
quasi-coherence of the two modules on the closed fibre is used, through
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ` being an isomorphism.

## References

* [Stacks Project, Tag 0F24](https://stacks.math.columbia.edu/tag/0F24)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Stacks.Algebraization

/-! ### Bridging instances for the scalar action on sections

The sections of a sheaf of modules carry their scalar action over
`X.ringCatSheaf.obj.obj U`, while the sections of the structure sheaf are
`Γ(X, U) = X.presheaf.obj (op U)`; instance search does not cross the `TopCat.Sheaf`
definition that separates the two, nor the two spellings `Γ(M, U)` and `M.val.obj U` of the
sections of `M`. The bridges are the `local` instances of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/Completion/IdealPowerQuasicoherent.lean` and of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/Completion/Quasicoherent/IdealPowerMultiple.lean`,
re-activated here rather than restated; each is `inferInstanceAs` of the canonical instance at
the other spelling. -/

attribute [local instance] sectionsModuleΓ sectionsModuleΓSheaf sectionsModuleΓPresheaf

/-! ### Finite length after restriction of scalars -/

/-- **Restriction of scalars along a surjection of local rings preserves finite length** when
the residue field extension is finite. -/
public theorem isFiniteLength_restrictScalars_local
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (M : Type u) [AddCommGroup M] [Module A M] [Module B M]
    [IsScalarTower A B M] (hM : IsFiniteLength B M) : IsFiniteLength A M :=
  Module.length_ne_top_iff.mp <| by
    rw [IsLocalRing.length_restrictScalars A B M]
    exact WithTop.mul_ne_top (Module.length_ne_top_iff.mpr hM) (by
      rw [Module.length_eq_finrank]
      exact ENat.natCast_ne_top _)

/-- Restriction of scalars along a local homomorphism preserves finite length of module objects
when the residue field extension is finite. -/
private theorem isFiniteLength_restrictScalars_moduleCat
    (A : Type u) [CommRing A] [IsLocalRing A]
    (B : Type u) [CommRing B] [IsLocalRing B] [Algebra A B]
    [IsLocalHom (algebraMap A B)]
    [Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B)]
    (M : ModuleCat.{u} B) (hM : IsFiniteLength B M.carrier) :
    IsFiniteLength A ((ModuleCat.restrictScalars (algebraMap A B)).obj M).carrier :=
  by
  let : IsScalarTower A B ((ModuleCat.restrictScalars (algebraMap A B)).obj M).carrier :=
    ⟨fun a b m => by rw [Algebra.smul_def, mul_smul]; rfl⟩
  exact isFiniteLength_restrictScalars_local A B
    ((ModuleCat.restrictScalars (algebraMap A B)).obj M).carrier hM

/-! ### Sections of a module that vanishes on an open -/

/-- A sheaf of modules that is a zero object has only the zero section over every open. -/
public theorem subsingleton_sections_of_isZero {X : Scheme.{u}} {F : X.Modules}
    (hF : IsZero F) (U : X.Opens) : Subsingleton Γ(F, U) := by
  have hid : (𝟙 F : F ⟶ F) = 0 := (IsZero.iff_id_eq_zero F).mp hF
  have h : ∀ x : Γ(F, U), x = 0 := fun x => by
    simpa using congrArg (fun φ : F ⟶ F => φ.app U x) hid
  exact ⟨fun s t => (h s).trans (h t).symm⟩

/-- A submodule of a sheaf of modules whose associated sheaf is a zero object has no nonzero
sections over any open. -/
public theorem submodule_obj_eq_bot_of_isZero {X : Scheme.{u}} {F : X.Modules}
    (N : F.Submodule) (hN : IsZero N.toSheafOfModules) (V : X.Opens) :
    N.toSubmodule.obj (op V) = ⊥ := by
  refine (Submodule.eq_bot_iff _).mpr fun x hx => ?_
  exact congrArg Subtype.val
    ((subsingleton_sections_of_isZero hN V).elim (⟨x, hx⟩ : Γ(N.toSheafOfModules, V)) 0)

/-- **A module vanishing on an open has support in the complement.** -/
public theorem supp_subset_compl_of_isZero_restrict {X : Scheme.{u}}
    (U : X.Opens) (F : X.Modules)
    (hF : IsZero ((Scheme.Modules.restrictFunctor U.ι).obj F)) :
    SheafOfModules.supp F ⊆ (U : Set X)ᶜ := by
  intro point hpoint hmem
  let x : U.toScheme := ⟨point, hmem⟩
  let S := Scheme.Modules.toPresheaf U.toScheme ⋙ TopCat.Presheaf.stalkFunctor Ab.{u} x
  have hzero : IsZero (F.presheaf.stalk point) :=
    (S.map_isZero hF).of_iso ((Scheme.Modules.restrictStalkNatIso U.ι x).app F).symm
  obtain ⟨value, hvalue⟩ := hpoint
  exact hvalue ((AddCommGrpCat.subsingleton_of_isZero hzero).elim value 0)

/-! ### Global sections of a coherent module on an affine scheme -/

/-- **The global sections of a coherent module on an affine scheme are a finite module.** -/
public theorem finite_globalSections_of_isCoherent {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (hM : _root_.SheafOfModules.IsCoherent M) :
    Module.Finite R (moduleSpecΓFunctor.obj M) := by
  have : M.IsQuasicoherent := isQuasicoherent_of_isCoherent M
  have : M.IsFiniteType := _root_.SheafOfModules.IsCoherent.isFiniteType
  have hfinite : (tilde (moduleSpecΓFunctor.obj M)).IsFiniteType :=
    Stacks.Coherent.isFiniteType_of_iso_local (asIso M.fromTildeΓ).symm inferInstance
  exact (AlgebraicGeometry.tilde_isFiniteType_iff _).mp hfinite

/-- The quasi-coherent ideal sheaf of the closed point of the spectrum of a local ring. -/
public noncomputable def puncturedSpectrumIdeal (A : Type u) [CommRing A] [IsLocalRing A] :
    (baseScheme A).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal
    ⟨{IsLocalRing.closedPoint A},
      ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2
        (IsLocalRing.maximalIdeal.isMaximal A))⟩

/-- Over the whole spectrum, the ideal of the closed point is the image of the maximal ideal
under the canonical identification of `A` with the global functions. -/
public theorem puncturedSpectrumIdeal_top (A : Type u) [CommRing A] [IsLocalRing A] :
    (puncturedSpectrumIdeal A).ideal ⟨⊤, isAffineOpen_top _⟩ =
      Ideal.map (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
        (IsLocalRing.maximalIdeal A) := by
  let φ := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hφ : Function.Surjective φ := by
    intro value
    exact ⟨(Scheme.ΓSpecIso (CommRingCat.of A)).hom value,
      ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of A)).hom_inv_id value⟩
  have hclosed : ({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) =
      PrimeSpectrum.zeroLocus (IsLocalRing.maximalIdeal A : Set A) :=
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2
      (IsLocalRing.maximalIdeal.isMaximal A)).closure_eq.symm.trans
      (PrimeSpectrum.closure_singleton _)
  change PrimeSpectrum.vanishingIdeal
      ((isAffineOpen_top (Spec (.of A))).fromSpec ⁻¹' {IsLocalRing.closedPoint A}) = _
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  change PrimeSpectrum.vanishingIdeal
      (PrimeSpectrum.comap φ ⁻¹' {IsLocalRing.closedPoint A}) = _
  rw [hclosed, PrimeSpectrum.preimage_comap_zeroLocus,
    ← PrimeSpectrum.zeroLocus_span, PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical]
  change (Ideal.map φ (IsLocalRing.maximalIdeal A)).radical = _
  have hker : RingHom.ker φ = ⊥ := (RingHom.injective_iff_ker_eq_bot φ).mp
    (Function.LeftInverse.injective (g := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom)
      fun x => ConcreteCategory.congr_hom (Scheme.ΓSpecIso (CommRingCat.of A)).inv_hom_id x)
  exact (Ideal.map_isPrime_of_surjective hφ (by simp [hker])).radical

/-- **A coherent module supported at the closed point is annihilated by a power of the maximal
ideal on global sections.** -/
public theorem maximalIdealPower_smul_eq_bot_of_isZero_restrict
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (F : (baseScheme A).Modules) (hcoh : _root_.SheafOfModules.IsCoherent F)
    (hF : IsZero ((Scheme.Modules.restrictFunctor
      (Stacks.Divisors.puncturedSpectrum A).ι).obj F)) :
    ∃ n : ℕ, ∀ a ∈ IsLocalRing.maximalIdeal A ^ n, ∀ v : ↑Γ(F, ⊤),
      (Scheme.ΓSpecIso (CommRingCat.of A)).inv a • v = 0 := by
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have hsupp : SheafOfModules.supp F ⊆
      (({IsLocalRing.closedPoint A} : Set (PrimeSpectrum A)) : Set (baseScheme A)) := by
    intro point hpoint
    exact not_not.mp
      (supp_subset_compl_of_isZero_restrict (Stacks.Divisors.puncturedSpectrum A) F hF hpoint)
  obtain ⟨n, hn⟩ :=
    Stacks.AlgebraicGeometry.IrreducibleDevissage.exists_isZero_idealPowSmul F
      ⟨{IsLocalRing.closedPoint A},
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2
          (IsLocalRing.maximalIdeal.isMaximal A))⟩ hsupp
  have hsmul := Submodule.smul_le.mp ((Stacks.AlgebraicGeometry.IdealPowerSmul.obj_idealPowSmul
    _ n F ⟨⊤, isAffineOpen_top _⟩).ge.trans
      (submodule_obj_eq_bot_of_isZero _ hn (⊤ : (baseScheme A).Opens)).le)
  refine ⟨n, fun a ha v => (Submodule.mem_bot _).mp (hsmul _ ?_ v Submodule.mem_top)⟩
  rw [show Stacks.AlgebraicGeometry.IdealPowerSmul.closedIdeal
      (⟨{IsLocalRing.closedPoint A},
        ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).2
          (IsLocalRing.maximalIdeal.isMaximal A))⟩ : Closeds (baseScheme A)) =
      puncturedSpectrumIdeal A from rfl,
    puncturedSpectrumIdeal_top, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ ha

/-- **The global sections of a coherent module supported at the closed point have finite
length.** -/
public theorem finiteLength_globalSections_of_isZero_restrict
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (F : (baseScheme A).Modules) (hcoh : _root_.SheafOfModules.IsCoherent F)
    (hF : IsZero ((Scheme.Modules.restrictFunctor
      (Stacks.Divisors.puncturedSpectrum A).ι).obj F)) :
    IsFiniteLength A ((moduleSpecΓFunctor (R := .of A)).obj F) := by
  have : Module.Finite A ((moduleSpecΓFunctor (R := .of A)).obj F) :=
    finite_globalSections_of_isCoherent F hcoh
  obtain ⟨n, hn⟩ := maximalIdealPower_smul_eq_bot_of_isZero_restrict A F hcoh hF
  have hle : IsLocalRing.maximalIdeal A ^ (n + 1) •
      (⊤ : Submodule A ((moduleSpecΓFunctor (R := .of A)).obj F)) ≤ ⊥ := by
    refine Submodule.smul_le.mpr fun a ha v _ => ?_
    exact (Submodule.mem_bot _).mpr (hn a (Ideal.pow_le_pow_right (Nat.le_succ n) ha) v)
  exact (Submodule.quotEquivOfEqBot _ rfl).isFiniteLength
    (Module.finiteLength_quotient_of_contains_maximalIdealPower A
      ((moduleSpecΓFunctor (R := .of A)).obj F) ⊥ n hle)

/-! ### Kernel and cokernel of a map of quasi-coherent modules on an affine scheme -/

/-- The global sections of the kernel of a map of quasi-coherent modules on an affine scheme are
the kernel of the map on global sections. -/
public noncomputable def specSectionsKernelIso
    {R : CommRingCat.{u}} {G H : (Spec R).Modules}
    [hGi : IsIso G.fromTildeΓ] [hHi : IsIso H.fromTildeΓ] (g : G ⟶ H) :
    (moduleSpecΓFunctor (R := R)).obj (kernel g) ≅
      kernel ((moduleSpecΓFunctor (R := R)).map g) := by
  have hnat : (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map g) ≫ H.fromTildeΓ =
      G.fromTildeΓ ≫ g := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality g
  exact (moduleSpecΓFunctor (R := R)).mapIso
      ((PreservesKernel.iso (tilde.functor R) ((moduleSpecΓFunctor (R := R)).map g) ≪≫
        kernel.mapIso _ g (@asIso _ _ _ _ G.fromTildeΓ hGi)
          (@asIso _ _ _ _ H.fromTildeΓ hHi) hnat).symm) ≪≫
    (tilde.toTildeΓNatIso (R := R)).symm.app (kernel ((moduleSpecΓFunctor (R := R)).map g))

/-- The global sections of the cokernel of a map of quasi-coherent modules on an affine scheme
are the cokernel of the map on global sections. -/
public noncomputable def specSectionsCokernelIso
    {R : CommRingCat.{u}} {G H : (Spec R).Modules}
    [hGi : IsIso G.fromTildeΓ] [hHi : IsIso H.fromTildeΓ] (g : G ⟶ H) :
    (moduleSpecΓFunctor (R := R)).obj (cokernel g) ≅
      cokernel ((moduleSpecΓFunctor (R := R)).map g) := by
  have hnat : (tilde.functor R).map ((moduleSpecΓFunctor (R := R)).map g) ≫ H.fromTildeΓ =
      G.fromTildeΓ ≫ g := (Scheme.Modules.fromTildeΓNatTrans (R := R)).naturality g
  exact (moduleSpecΓFunctor (R := R)).mapIso
      ((PreservesCokernel.iso (tilde.functor R) ((moduleSpecΓFunctor (R := R)).map g) ≪≫
        cokernel.mapIso _ g (@asIso _ _ _ _ G.fromTildeΓ hGi)
          (@asIso _ _ _ _ H.fromTildeΓ hHi) hnat).symm) ≪≫
    (tilde.toTildeΓNatIso (R := R)).symm.app (cokernel ((moduleSpecΓFunctor (R := R)).map g))

/-- The kernel of a map that becomes a monomorphism on an open vanishes there. -/
public theorem isZero_restrict_kernel_of_mono_restrict
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i]
    {F G : Y.Modules} (g : F ⟶ G)
    (hg : Mono ((Scheme.Modules.restrictFunctor i).map g)) :
    IsZero ((Scheme.Modules.restrictFunctor i).obj (kernel g)) :=
  (isZero_kernel_of_mono ((Scheme.Modules.restrictFunctor i).map g)).of_iso
    (PreservesKernel.iso (Scheme.Modules.restrictFunctor i) g)

/-- The cokernel of a map that becomes an epimorphism on an open vanishes there. -/
public theorem isZero_restrict_cokernel_of_epi_restrict
    {X Y : Scheme.{u}} (i : X ⟶ Y) [IsOpenImmersion i]
    {F G : Y.Modules} (g : F ⟶ G)
    (hg : Epi ((Scheme.Modules.restrictFunctor i).map g)) :
    IsZero ((Scheme.Modules.restrictFunctor i).obj (cokernel g)) :=
  have : (Scheme.Modules.restrictFunctor i).IsLeftAdjoint :=
    (Scheme.Modules.restrictAdjunction i).isLeftAdjoint
  (isZero_cokernel_of_epi ((Scheme.Modules.restrictFunctor i).map g)).of_iso
    (PreservesCokernel.iso (Scheme.Modules.restrictFunctor i) g)

/-- When `f` lies in the maximal ideal, the punctured closed fibre is the punctured spectrum of
`A / fA`. -/
public theorem puncturedClosedFibre_eq_puncturedSpectrum
    (A : Type u) [CommRing A] [IsLocalRing A] (f : A)
    [IsLocalRing (A ⧸ Ideal.span {f})]
    (hf : f ∈ IsLocalRing.maximalIdeal A) :
    puncturedClosedFibre A f =
      Stacks.Divisors.puncturedSpectrum (A ⧸ Ideal.span {f}) := by
  let q : A →+* A ⧸ Ideal.span {f} := Ideal.Quotient.mk _
  have hIne : Ideal.span {f} ≠ ⊤ := Ideal.span_singleton_ne_top
    (by simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hf)
  have : Nontrivial (A ⧸ Ideal.span {f}) := Ideal.Quotient.nontrivial_iff.mpr hIne
  have : IsLocalHom q := IsLocalHom.of_surjective q Ideal.Quotient.mk_surjective
  have hclosed : PrimeSpectrum.comap q (IsLocalRing.closedPoint (A ⧸ Ideal.span {f})) =
      IsLocalRing.closedPoint A :=
    PrimeSpectrum.ext (IsLocalRing.maximalIdeal_comap q)
  ext x
  change PrimeSpectrum.comap q x ≠ IsLocalRing.closedPoint A ↔
    x ≠ IsLocalRing.closedPoint (A ⧸ Ideal.span {f})
  exact ⟨fun hx hxb => hx (by rwa [hxb]), fun hx hxa => hx
    (PrimeSpectrum.comap_injective_of_surjective q Ideal.Quotient.mk_surjective
      (hxa.trans hclosed.symm))⟩

/-! ### Prepared extensions -/

/-- **A prepared extension of a coherent triple.** It is a coherent module on `Spec A` on which
`f` acts regularly, isomorphic to the punctured-spectrum member of the triple over the punctured
spectrum, mapping to the closed-fibre member over the closed fibre, compatibly over the
punctured closed fibre. -/
public structure PreparedExtension (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (T : CoherentTriple A f) where
  /-- The coherent module on `Spec A`. -/
  F' : (baseScheme A).Modules
  /-- `F'` is coherent. -/
  coherent : _root_.SheafOfModules.IsCoherent F'
  /-- Multiplication by `f` is injective on the sections of `F'` over every open. -/
  regular : ∀ V : (baseScheme A).Opens,
    IsSMulRegular Γ(F', V)
      ((baseScheme A).presheaf.map (homOfLE (le_top : V ≤ ⊤)).op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv f))
  /-- The isomorphism with `T.F` over the punctured spectrum. -/
  alpha' : (Scheme.Modules.pullback
    (Stacks.Divisors.puncturedSpectrum A).ι).obj F' ≅ T.F
  /-- The map to `T.F₀` over the closed fibre. -/
  alpha₀' : (Scheme.Modules.pullback (closedImmersion A f)).obj F' ⟶ T.F₀
  /-- The two agree over the punctured closed fibre. -/
  compatible :
    let i := closedImmersion A f
    let U := Stacks.Divisors.puncturedSpectrum A
    let j := U.ι
    let j₀ := (puncturedClosedFibre A f).ι
    let k := morphismRestrict i U
    let c := (Scheme.Modules.pullbackCongr (morphismRestrict_ι i U).symm).hom.app F'
    c ≫ (Scheme.Modules.pullbackComp k j).inv.app F' ≫
        (Scheme.Modules.pullback k).map alpha'.hom ≫ T.alpha.hom =
      (Scheme.Modules.pullbackComp j₀ i).inv.app F' ≫
        (Scheme.Modules.pullback j₀).map alpha₀'

/-- The closed-fibre map of a prepared extension is an isomorphism over the punctured closed
fibre: the compatibility identifies it with an isomorphism there. -/
public theorem isIso_restrict_alpha₀'
    (A : Type u) [CommRing A] [IsLocalRing A] {f : A}
    {T : CoherentTriple A f} (P : PreparedExtension A f T) :
    IsIso ((Scheme.Modules.restrictFunctor (puncturedClosedFibre A f).ι).map P.alpha₀') := by
  let i := closedImmersion A f
  let U := Stacks.Divisors.puncturedSpectrum A
  let j₀ := (puncturedClosedFibre A f).ι
  let k := morphismRestrict i U
  let c (F : (baseScheme A).Modules) :=
    (Scheme.Modules.pullbackCongr (morphismRestrict_ι i U).symm).hom.app F
  let p₁ (F : (baseScheme A).Modules) :=
    c F ≫ (Scheme.Modules.pullbackComp k U.ι).inv.app F
  let p₀ (F : (baseScheme A).Modules) :=
    (Scheme.Modules.pullbackComp j₀ i).inv.app F
  have : IsIso (p₁ P.F' ≫ (Scheme.Modules.pullback k).map P.alpha'.hom ≫
      T.alpha.hom) := by infer_instance
  have : IsIso (p₀ P.F' ≫ (Scheme.Modules.pullback j₀).map P.alpha₀') := by
    rw [← P.compatible]
    infer_instance
  have : IsIso (p₀ P.F') := by infer_instance
  have : IsIso ((Scheme.Modules.pullback j₀).map P.alpha₀') :=
    IsIso.of_isIso_comp_left (p₀ P.F') _
  exact (NatIso.isIso_map_iff (Scheme.Modules.restrictFunctorIsoPullback j₀)
    P.alpha₀').mpr inferInstance

/-- The closed-fibre map of a prepared extension, taken on global sections and regarded as a map
of `A`-modules by restriction of scalars along `A → A / fA`. -/
public noncomputable def PreparedExtension.closedFibreMap
    {A : Type u} [CommRing A] [IsLocalRing A] {f : A}
    {T : CoherentTriple A f} (P : PreparedExtension A f T) :
    ModuleCat.of A
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
        ((moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).obj
          ((Scheme.Modules.pullback (closedImmersion A f)).obj P.F'))).carrier ⟶
    ModuleCat.of A
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).obj
        ((moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).obj T.F₀)).carrier :=
  (ModuleCat.restrictScalars (Ideal.Quotient.mk (Ideal.span {f}))).map
    ((moduleSpecΓFunctor (R := .of (A ⧸ Ideal.span {f}))).map P.alpha₀')

private theorem kernel_cokernel_finiteLength_of_mem_maximalIdeal
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A) (hf : f ∈ IsLocalRing.maximalIdeal A)
    (T : CoherentTriple A f) (P : PreparedExtension A f T) :
    IsFiniteLength A (kernel P.closedFibreMap).carrier ∧
      IsFiniteLength A (cokernel P.closedFibreMap).carrier := by
  let I : Ideal A := Ideal.span {f}
  let B := A ⧸ I
  have hIne : I ≠ ⊤ := Ideal.span_singleton_ne_top
    (by simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] using hf)
  have : Nontrivial B := Ideal.Quotient.nontrivial_iff.mpr hIne
  let : IsLocalRing B := IsLocalRing.of_surjective' (Ideal.Quotient.mk I)
    Ideal.Quotient.mk_surjective
  have : IsNoetherianRing B := inferInstanceAs (IsNoetherianRing (A ⧸ I))
  let : Algebra A B := Ideal.Quotient.algebra A
  have : IsLocalHom (algebraMap A B) := IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have : Module.Finite (IsLocalRing.ResidueField A) (IsLocalRing.ResidueField B) := by
    refine Module.Finite.of_surjective (Algebra.linearMap _ _) fun z => ?_
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective b
    exact ⟨IsLocalRing.residue A a, rfl⟩
  have : _root_.SheafOfModules.IsCoherent P.F' := P.coherent
  let G := (Scheme.Modules.pullback (closedImmersion A f)).obj P.F'
  have : _root_.SheafOfModules.IsCoherent G :=
    AlgebraicGeometry.isCoherent_pullback (closedImmersion A f) P.F'
  have : _root_.SheafOfModules.IsCoherent T.F₀ := T.coherent_F₀
  let g : G ⟶ T.F₀ := P.alpha₀'
  have hIso : IsIso ((Scheme.Modules.restrictFunctor
      (Stacks.Divisors.puncturedSpectrum B).ι).map g) := by
    rw [← puncturedClosedFibre_eq_puncturedSpectrum A f hf]
    exact isIso_restrict_alpha₀' A P
  have hKzero := isZero_restrict_kernel_of_mono_restrict
    (Stacks.Divisors.puncturedSpectrum B).ι g inferInstance
  have hCzero := isZero_restrict_cokernel_of_epi_restrict
    (Stacks.Divisors.puncturedSpectrum B).ι g inferInstance
  have hGiso : IsIso G.fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ G).1 (isQuasicoherent_of_isCoherent G)
  have hF₀iso : IsIso T.F₀.fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ T.F₀).1 (isQuasicoherent_of_isCoherent T.F₀)
  have hKmap : IsFiniteLength B
      (kernel ((moduleSpecΓFunctor (R := .of B)).map g)).carrier :=
    ModuleCat.isFiniteLength_of_iso (specSectionsKernelIso g)
      (finiteLength_globalSections_of_isZero_restrict B (kernel g)
        (SheafOfModules.kernel_isCoherent g) hKzero)
  have hCmap : IsFiniteLength B
      (cokernel ((moduleSpecΓFunctor (R := .of B)).map g)).carrier :=
    ModuleCat.isFiniteLength_of_iso (specSectionsCokernelIso g)
      (finiteLength_globalSections_of_isZero_restrict B (cokernel g)
        (SheafOfModules.cokernel_isCoherent g) hCzero)
  let Res := ModuleCat.restrictScalars (Ideal.Quotient.mk I)
  let gB := (moduleSpecΓFunctor (R := .of B)).map g
  refine ⟨?_, ?_⟩
  · change IsFiniteLength A (kernel (Res.map gB)).carrier
    exact ModuleCat.isFiniteLength_of_iso (PreservesKernel.iso Res gB)
      (isFiniteLength_restrictScalars_moduleCat A B _ hKmap)
  · change IsFiniteLength A (cokernel (Res.map gB)).carrier
    exact ModuleCat.isFiniteLength_of_iso (PreservesCokernel.iso Res gB)
      (isFiniteLength_restrictScalars_moduleCat A B _ hCmap)

private theorem kernel_cokernel_finiteLength_of_isUnit
    (A : Type u) [CommRing A] [IsLocalRing A]
    (f : A) (hunit : IsUnit f) (T : CoherentTriple A f)
    (P : PreparedExtension A f T) :
    IsFiniteLength A (kernel P.closedFibreMap).carrier ∧
      IsFiniteLength A (cokernel P.closedFibreMap).carrier := by
  let I : Ideal A := Ideal.span {f}
  have : Subsingleton (A ⧸ I) :=
    Ideal.Quotient.subsingleton_iff.mpr (Ideal.span_singleton_eq_top.2 hunit)
  have key : ∀ M : ModuleCat (A ⧸ I),
      IsFiniteLength A (ModuleCat.of A
        ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M).carrier).carrier := fun M => by
    have hs : Subsingleton M.carrier := Module.subsingleton (A ⧸ I) _
    have : Subsingleton (ModuleCat.of A
      ((ModuleCat.restrictScalars (Ideal.Quotient.mk I)).obj M).carrier).carrier := hs
    exact IsFiniteLength.of_subsingleton
  exact ModuleCat.isFiniteLength_kernel_cokernel P.closedFibreMap (key _) (key _)

/-- **The kernel of the closed-fibre map of a prepared extension has finite length over `A`.** -/
@[stacks 0F24 "finite length of the kernel"]
public theorem kernel_finiteLength
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A)
    (T : CoherentTriple A f) (P : PreparedExtension A f T) :
    IsFiniteLength A (kernel P.closedFibreMap).carrier := by
  by_cases hf : f ∈ IsLocalRing.maximalIdeal A
  · exact (kernel_cokernel_finiteLength_of_mem_maximalIdeal A f hf T P).1
  · exact (kernel_cokernel_finiteLength_of_isUnit A f
      (by simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hf) T P).1

/-- **The cokernel of the closed-fibre map of a prepared extension has finite length over
`A`.** -/
@[stacks 0F24 "finite length of the cokernel"]
public theorem cokernel_finiteLength
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (f : A)
    (T : CoherentTriple A f) (P : PreparedExtension A f T) :
    IsFiniteLength A (cokernel P.closedFibreMap).carrier := by
  by_cases hf : f ∈ IsLocalRing.maximalIdeal A
  · exact (kernel_cokernel_finiteLength_of_mem_maximalIdeal A f hf T P).2
  · exact (kernel_cokernel_finiteLength_of_isUnit A f
      (by simpa only [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, not_not] using hf) T P).2

end Stacks.Algebraization

end
