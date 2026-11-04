module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.StructureSheaf
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Regular.Flat
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.RegularSequence.ExtVanishing
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Vanishing of `Ext` into a free module on an affine scheme

Let `X` be an affine scheme, write `R = Γ(X, 𝒪_X)`, let `N` be an `𝒪_X`-module and let
`E ≅ 𝒪_X^{(ι)}` be a free `𝒪_X`-module. If `r_1, …, r_c ∈ R` is a weakly regular sequence in
`R` all of whose terms annihilate `N`, then `Ext^q_{𝒪_X}(N, E) = 0` for every `q < c`.

The general vanishing statement — `Ext^q(N, E) = 0` whenever the sequence annihilates `N` and is
weakly regular *on `E`* — is proved elsewhere; what is added here is that on an affine scheme a
sequence which is weakly regular in the ring of global functions is weakly regular on a free
module. This is proved by transporting the question to `Spec R`, where a free module is `M^~`
for `M = R^{(ι)}`, a flat `R`-module, so that the sequence is weakly regular on `M`. Each step
of the induction then says two things about multiplication by `r ∈ R` on `M^~`: it is a
monomorphism, and its cokernel is `(M/rM)^~`. The first is checked on sections, which over an
open `U ⊆ Spec R` are a submodule of a product of localizations of `M`, on each of which `r`
acts injectively because localization is flat. The second only needs that `M ↦ M^~` preserves
cokernels, which it does, being a left adjoint.

## Main definitions

* `Stacks.RegularSequence.modulesEquivalenceOfIso`: an isomorphism of schemes induces an
  equivalence between their categories of modules, given by restriction along the inverse.
* `Stacks.RegularSequence.cokernelGlobalSmulCenterTildeIso`: the cokernel of multiplication by
  `r` on `M^~` is the sheaf associated with `M/rM`.

## Main results

* `Stacks.RegularSequence.IsWeaklyRegularOn.of_iso` and
  `Stacks.RegularSequence.IsWeaklyRegularOn.restrict_of_iso`: weak regularity of a list of
  global functions on a module is invariant under isomorphisms of the module, and transfers
  along an isomorphism of the base scheme.
* `Stacks.RegularSequence.tilde_map_smul_id`: multiplication by `r ∈ R` on `M^~` is the action
  of the global function on `Spec R` corresponding to `r`.
* `Stacks.RegularSequence.isWeaklyRegularOn_tilde`: a weakly regular sequence on an `R`-module
  `M` is weakly regular, as a sequence of global functions, on `M^~`.
* `Stacks.RegularSequence.subsingleton_ext_of_isAffine_of_iso_free`: **the vanishing**,
  `Ext^q_{𝒪_X}(N, E) = 0` for `X` affine, `E` free and `q` below the length of the sequence.

## Implementation notes

The transfer from `Spec Γ(X, 𝒪_X)` back to `X` moves the *hypothesis* rather than the
conclusion: weak regularity of the sequence on the free module is transported along the
restriction functor of `X.isoSpec`, and the vanishing is then applied on `X` itself. This avoids
having to transport `Ext`-groups along an equivalence of abelian categories. Restriction along
an isomorphism of schemes is an equivalence, which is what makes it preserve both the
monomorphism and the cokernel appearing in the definition of weak regularity.

No declaration here carries a `@[stacks 0G5I]` attribute; see the implementation notes of
`Stacks.RegularSequence.subsingleton_ext_of_isWeaklyRegularOn` for why. What is missing from
[Stacks, Tag 0G5I] is still its step 1, the reduction to the affine case, which is the
local-to-global spectral sequence of `Ext`.

## References

* [Stacks Project, Tag 0G5I](https://stacks.math.columbia.edu/tag/0G5I)
* [Stacks Project, Tag 01HV](https://stacks.math.columbia.edu/tag/01HV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe w v u

namespace Stacks.RegularSequence

attribute [local instance] HasExt.standard

/-- Weak regularity of a list of global functions on an `𝒪_X`-module only depends on the
isomorphism class of the module. -/
theorem IsWeaklyRegularOn.of_iso {X : Scheme.{u}} (fs : List Γ(X, ⊤)) :
    ∀ {E E' : X.Modules}, (E ≅ E') → IsWeaklyRegularOn E fs → IsWeaklyRegularOn E' fs := by
  induction fs with
  | nil => intro E E' _ _; exact isWeaklyRegularOn_nil _
  | cons r fs ih =>
    intro E E' e h
    rw [isWeaklyRegularOn_cons_iff] at h ⊢
    have hnat : (globalSmulCenter X r).app E ≫ e.hom =
        e.hom ≫ (globalSmulCenter X r).app E' := ((globalSmulCenter X r).naturality e.hom).symm
    have : Mono ((globalSmulCenter X r).app E) := h.1
    refine ⟨?_, ih (cokernel.mapIso ((globalSmulCenter X r).app E)
      ((globalSmulCenter X r).app E') e e hnat) h.2⟩
    have heq : (globalSmulCenter X r).app E' = e.inv ≫ (globalSmulCenter X r).app E ≫ e.hom := by
      rw [hnat, Iso.inv_hom_id_assoc]
    rw [heq]
    infer_instance

/-- A morphism of `𝒪_X`-modules which is injective on sections over every open is a
monomorphism. -/
theorem mono_of_injective_app {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    (h : ∀ U : X.Opens, Function.Injective (φ.app U)) : Mono φ where
  right_cancellation {Z} g₁ g₂ hg := by
    refine Scheme.Modules.hom_ext _ _ fun U => ?_
    ext x
    exact h U (congrArg (fun ψ : Z ⟶ N => ψ.app U x) hg)

/-- On an affine scheme, the centre element attached to a ring element `r` acts on sections of
any `𝒪_{Spec R}`-module as the scalar `r`. -/
theorem globalSmulCenter_app_app_Spec {R : CommRingCat.{u}} (N : (Spec R).Modules) (r : R)
    (U : (Spec R).Opens) (x : Γ(N, U)) :
    ((globalSmulCenter (Spec R) ((Scheme.ΓSpecIso R).inv r)).app N).app U x = r • x := by
  rw [globalSmulCenter_app_app]
  exact (Scheme.Modules.smul_Spec_def r x).symm

/-- Two morphisms out of `M^~` agree as soon as they agree on global sections. -/
theorem tilde_hom_ext {R : CommRingCat.{u}} {M : ModuleCat.{u} R} {N : (Spec R).Modules}
    (φ ψ : (tilde.functor R).obj M ⟶ N)
    (h : moduleSpecΓFunctor.map φ = moduleSpecΓFunctor.map ψ) : φ = ψ :=
  (tilde.adjunction.homEquiv M N).injective (by
    rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, h])

/-- Multiplication by `r` on `M^~` is multiplication by the global function corresponding to
`r` on every `𝒪_{Spec R}`-module. -/
theorem tilde_map_smul_id (R : CommRingCat.{u}) (M : ModuleCat.{u} R) (r : R) :
    (tilde.functor R).map (r • 𝟙 M) =
      (globalSmulCenter (Spec R) ((Scheme.ΓSpecIso R).inv r)).app (tilde M) := by
  show (tilde.functor R).map (r • 𝟙 M) =
    (globalSmulCenter (Spec R) ((Scheme.ΓSpecIso R).inv r)).app ((tilde.functor R).obj M)
  refine tilde_hom_ext _ _ ?_
  refine (cancel_epi (tilde.toOpen M ⊤)).mp ?_
  have hL : tilde.toOpen M ⊤ ≫
      (modulesSpecToSheaf.map (tilde.map (r • 𝟙 M))).hom.app (.op ⊤) =
      (r • 𝟙 M) ≫ tilde.toOpen M ⊤ := tilde.toOpen_map_app (r • 𝟙 M) ⊤
  refine hL.trans ?_
  ext m
  show tilde.toOpen M ⊤ (r • m) =
    ((globalSmulCenter (Spec R) ((Scheme.ΓSpecIso R).inv r)).app
      ((tilde.functor R).obj M)).app ⊤ (tilde.toOpen M ⊤ m)
  rw [map_smul]
  exact (globalSmulCenter_app_app_Spec ((tilde.functor R).obj M) r ⊤ _).symm

/-- A ring element acting regularly on `M` acts regularly on every localization of `M`. -/
theorem isSMulRegular_localizedModule {R : Type u} [CommRing R] (M : Type u) [AddCommGroup M]
    [Module R M] {a : R} (ha : IsSMulRegular M a) (S : Submonoid R) :
    IsSMulRegular (LocalizedModule S M) a := by
  have h := ((RingTheory.Sequence.isWeaklyRegular_singleton_iff M a).mpr ha).of_isLocalizedModule
    (Localization S) S (LocalizedModule.mkLinearMap S M)
  rw [List.map_cons, List.map_nil,
    RingTheory.Sequence.isWeaklyRegular_singleton_iff] at h
  exact (isSMulRegular_algebraMap_iff (Localization S)).mp h

/-- A ring element acting regularly on `M` acts regularly on the sections of `M^~` over every
open subset of `Spec R`. -/
theorem isSMulRegular_tilde_sections {R : CommRingCat.{u}} (M : ModuleCat.{u} R) {a : R}
    (ha : IsSMulRegular M a) (U : (Spec R).Opens) :
    IsSMulRegular Γ((tilde.functor R).obj M, U) a := by
  have h2 : IsSMulRegular (∀ x : U, StructureSheaf.Localizations M x.1) a :=
    IsSMulRegular.pi fun x => isSMulRegular_localizedModule M ha _
  have h3 : IsSMulRegular ((structureSheafInType R M).obj.obj (Opposite.op U)) a :=
    h2.submodule (StructureSheaf.sectionsSubmodule M U) a
  exact (((tilde.modulesSpecToSheafIso M).app (Opposite.op U)).toLinearEquiv.isSMulRegular_congr
    a).mpr h3

/-- Multiplication by a nonzerodivisor on `M` is a monomorphism on `M^~`. -/
theorem mono_globalSmulCenter_tilde {R : CommRingCat.{u}} (M : ModuleCat.{u} R) {a : R}
    (ha : IsSMulRegular M a) :
    Mono ((globalSmulCenter (Spec R) ((Scheme.ΓSpecIso R).inv a)).app
      ((tilde.functor R).obj M)) := by
  refine mono_of_injective_app _ fun U x y hxy => ?_
  refine isSMulRegular_tilde_sections M ha U ?_
  exact ((globalSmulCenter_app_app_Spec _ a U x).symm.trans hxy).trans
    (globalSmulCenter_app_app_Spec _ a U y)

/-- The cokernel of multiplication by `a` on `M^~` is the sheaf associated with `M/aM`. -/
noncomputable def cokernelGlobalSmulCenterTildeIso {R : CommRingCat.{u}} (M : ModuleCat.{u} R)
    (a : R) :
    cokernel ((globalSmulCenter (Spec R) ((Scheme.ΓSpecIso R).inv a)).app
        ((tilde.functor R).obj M)) ≅
      (tilde.functor R).obj (ModuleCat.of R (QuotSMulTop a M)) :=
  cokernelIsoOfEq (tilde_map_smul_id R M a).symm ≪≫
    (PreservesCokernel.iso (tilde.functor R) (ModuleCat.smulShortComplex M a).f).symm ≪≫
    (tilde.functor R).mapIso (IsColimit.coconePointUniqueUpToIso
      (cokernelIsCokernel (ModuleCat.smulShortComplex M a).f)
      (ModuleCat.smulShortComplex_exact M a).gIsCokernel)

/-- A regular sequence in `R` is weakly regular on every flat `R`-module. -/
@[ega "0 15.1.13" "special case", ega "IV 19.7.1" "partial", ega "IV 19.7.2" "more general"]
theorem isWeaklyRegular_of_flat {R : Type*} [CommRing R] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Flat R M] {rs : List R}
    (hreg : RingTheory.Sequence.IsWeaklyRegular R rs) :
    RingTheory.Sequence.IsWeaklyRegular M rs :=
  ((TensorProduct.lid R M).isWeaklyRegular_congr rs).mp hreg.isWeaklyRegular_rTensor

/-- A weakly regular sequence on an `R`-module `M` is weakly regular, as a sequence of global
functions on `Spec R`, on the sheaf `M^~`. -/
@[ega "0 15.2.2" "Regular half"]
theorem isWeaklyRegularOn_tilde {R : CommRingCat.{u}} :
    ∀ (rs : List R) (M : ModuleCat.{u} R), RingTheory.Sequence.IsWeaklyRegular M rs →
      IsWeaklyRegularOn ((tilde.functor R).obj M)
        (rs.map (Scheme.ΓSpecIso R).inv) := by
  intro rs
  induction rs with
  | nil => intro M _; exact isWeaklyRegularOn_nil _
  | cons a rs ih =>
    intro M hreg
    rw [RingTheory.Sequence.isWeaklyRegular_cons_iff] at hreg
    rw [List.map_cons, isWeaklyRegularOn_cons_iff]
    refine ⟨mono_globalSmulCenter_tilde M hreg.1, ?_⟩
    exact IsWeaklyRegularOn.of_iso _ (cokernelGlobalSmulCenterTildeIso M a).symm
      (ih (ModuleCat.of R (QuotSMulTop a M)) hreg.2)

/-! ### Transfer along an isomorphism of schemes -/

/-- Restriction along an open immersion turns multiplication by a global function into
multiplication by its pullback. -/
theorem globalSmulCenter_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    (M : Y.Modules) (r : Γ(Y, ⊤)) :
    (Scheme.Modules.restrictFunctor f).map ((globalSmulCenter Y r).app M) =
      (globalSmulCenter X (f.appTop r)).app (M.restrict f) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m
  change Γ(M, f ''ᵁ U) at m
  show Y.presheaf.map (f ''ᵁ U).leTop.op r • m =
    (f.appIso U).inv (X.presheaf.map U.leTop.op (f.appTop r)) • m
  have h : Y.presheaf.map (f ''ᵁ U).leTop.op ≫ (f.appIso U).hom =
      f.appTop ≫ X.presheaf.map U.leTop.op := by
    rw [Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]
    rfl
  have hr := congrArg (fun g : Γ(Y, ⊤) ⟶ Γ(X, U) => g r) h
  change (f.appIso U).hom (Y.presheaf.map (f ''ᵁ U).leTop.op r) =
    X.presheaf.map U.leTop.op (f.appTop r) at hr
  rw [← hr]
  simp

/-- An isomorphism of schemes induces an equivalence between their categories of modules. -/
noncomputable def modulesEquivalenceOfIso {X Y : Scheme.{u}} (e : X ≅ Y) :
    X.Modules ≌ Y.Modules :=
  CategoryTheory.Equivalence.mk
    (Scheme.Modules.restrictFunctor e.inv) (Scheme.Modules.restrictFunctor e.hom)
    ((Scheme.Modules.restrictFunctorId (X := X)).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id.symm ≪≫
      Scheme.Modules.restrictFunctorComp e.hom e.inv)
    ((Scheme.Modules.restrictFunctorComp e.inv e.hom).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.inv_hom_id ≪≫
      Scheme.Modules.restrictFunctorId)

/-- Restriction along an isomorphism of schemes is an equivalence of categories. -/
theorem restrictFunctor_isEquivalence {X Y : Scheme.{u}} (e : X ≅ Y) :
    (Scheme.Modules.restrictFunctor e.hom).IsEquivalence :=
  (modulesEquivalenceOfIso e).isEquivalence_inverse

/-- Weak regularity of a list of global functions transfers along an isomorphism of schemes. -/
theorem IsWeaklyRegularOn.restrict_of_iso {X Y : Scheme.{u}} (e : X ≅ Y) (fs : List Γ(Y, ⊤)) :
    ∀ M : Y.Modules, IsWeaklyRegularOn M fs →
      IsWeaklyRegularOn (M.restrict e.hom) (fs.map e.hom.appTop) := by
  have := restrictFunctor_isEquivalence e
  induction fs with
  | nil => intro M _; exact isWeaklyRegularOn_nil _
  | cons r fs ih =>
    intro M h
    rw [isWeaklyRegularOn_cons_iff] at h
    rw [List.map_cons, isWeaklyRegularOn_cons_iff]
    have hm : Mono ((globalSmulCenter Y r).app M) := h.1
    have hg : (Scheme.Modules.restrictFunctor e.hom).map ((globalSmulCenter Y r).app M) =
        (globalSmulCenter X (e.hom.appTop r)).app (M.restrict e.hom) :=
      globalSmulCenter_restrict e.hom M r
    refine ⟨hg ▸ (Functor.map_mono _ _), ?_⟩
    refine IsWeaklyRegularOn.of_iso _ (Iso.symm (cokernelIsoOfEq hg.symm ≪≫
      (PreservesCokernel.iso (Scheme.Modules.restrictFunctor e.hom)
        ((globalSmulCenter Y r).app M)).symm)) (ih _ h.2)

/-! ### Vanishing of `Ext` into a free module on an affine scheme -/

/-- **`Ext` into a free module vanishes below the length of an annihilating regular sequence.**
On an affine scheme `X`, let `rs` be a weakly regular sequence in `Γ(X, 𝒪_X)` each term of which
annihilates `N`, and let `E` be a free `𝒪_X`-module. Then `Ext^q_{𝒪_X}(N, E) = 0` for every
`q` smaller than the length of `rs`. -/
theorem subsingleton_ext_of_isAffine_of_iso_free
    {X : Scheme.{u}} [IsAffine X] (N E : X.Modules) (ι : Type u)
    (e : E ≅ SheafOfModules.free.{u} ι) (rs : List Γ(X, ⊤))
    (hann : ∀ r ∈ rs, (globalSmulCenter X r).app N = 0)
    (hreg : RingTheory.Sequence.IsWeaklyRegular Γ(X, ⊤) rs)
    (q : ℕ) (hq : q < rs.length) :
    Subsingleton (Abelian.Ext N E q) := by
  have hid : ∀ a : Γ(X, ⊤),
      X.isoSpec.hom.appTop ((Scheme.ΓSpecIso Γ(X, ⊤)).inv a) = a := by
    intro a
    rw [show X.isoSpec.hom.appTop = (Scheme.ΓSpecIso Γ(X, ⊤)).hom from X.toSpecΓ_appTop]
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso Γ(X, ⊤)).inv_hom_id a
  have hfree : RingTheory.Sequence.IsWeaklyRegular (ι →₀ Γ(X, ⊤)) rs :=
    isWeaklyRegular_of_flat _ hreg
  have h1 := isWeaklyRegularOn_tilde rs (ModuleCat.of Γ(X, ⊤) (ι →₀ Γ(X, ⊤))) hfree
  have h2 := IsWeaklyRegularOn.restrict_of_iso X.isoSpec _ _ h1
  rw [List.map_map, show X.isoSpec.hom.appTop ∘ ⇑(Scheme.ΓSpecIso Γ(X, ⊤)).inv = id from
    funext hid, List.map_id] at h2
  refine subsingleton_ext_of_isWeaklyRegularOn N rs E hann ?_ q hq
  refine IsWeaklyRegularOn.of_iso _ ?_ h2
  exact (Scheme.Modules.restrictFunctor X.isoSpec.hom).mapIso (tildeFinsupp ι) ≪≫
    (Scheme.Modules.restrictFreeIso X.isoSpec.hom ι).symm ≪≫ e.symm

end Stacks.RegularSequence

end
