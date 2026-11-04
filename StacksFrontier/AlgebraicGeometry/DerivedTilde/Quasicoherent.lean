module

public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.QuasiCoherentAbelian
public import StacksFrontier.AlgebraicGeometry.DerivedTilde.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.Basic
public import StacksFrontier.AlgebraicGeometry.QcohLimits.ClosedUnderKernels
public import StacksFrontier.AlgebraicGeometry.SectionsExact.Discharge
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.Affine
public import StacksFrontier.RingTheory.LocalCohomology.Deps.QuasicoherentAffineVanishing
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
public import StacksFrontier.AlgebraicGeometry.ModuleSpecGammaAdditive

/-!
# Quasi-coherent modules on an affine scheme form a weak Serre subcategory

On `Spec R` the quasi-coherent `𝒪`-modules are closed under kernels, cokernels and extensions,
hence form a weak Serre subcategory of all `𝒪`-modules, and therefore the complexes with
quasi-coherent cohomology form a triangulated subcategory of `D(𝒪_{Spec R})`.

Kernels and cokernels are already available: a kernel of a morphism of quasi-coherent modules is
quasi-coherent on any scheme (`Stacks.AlgebraicGeometry.QcohLimits.isQuasicoherent_kernel`), and
so is a cokernel on an affine scheme
(`AlgebraicGeometry.Scheme.Modules.isQuasicoherent_cokernel`, Stacks 01IC). Closure under
extensions is the content added here, and it is the one of the three that genuinely uses
cohomology. Let `0 → A → E → B → 0` be a short exact sequence of `𝒪_{Spec R}`-modules with `A`
and `B` quasi-coherent. Global sections are left exact, and `H¹(Spec R, A) = 0` by Serre
vanishing (Stacks 01XB), so `0 → Γ(A) → Γ(E) → Γ(B) → 0` is again short exact; applying the
exact functor `~` and comparing with the original sequence through the counit `Γ(M)^~ → M` of the
tilde–Gamma adjunction gives a morphism of short exact sequences which is an isomorphism on the
two outer terms, hence by the short five lemma on `E` as well. So `E ≅ Γ(E)^~` is quasi-coherent.

## Main results

* `AlgebraicGeometry.isQuasicoherent_X₂_of_shortExact` — quasi-coherent modules on `Spec R` are
  closed under extensions.
* `AlgebraicGeometry.isQuasicoherent_isWeakSerreClass` and
  `AlgebraicGeometry.isQuasicoherent_isWeakSerre` — they form a weak Serre subcategory, in the
  two formulations used in this repository.
* `AlgebraicGeometry.derivedQuasicoherent_isTriangulated` — `D_QCoh(𝒪_{Spec R})` is a strictly
  full saturated triangulated subcategory of `D(𝒪_{Spec R})`.

## Implementation notes

Everything is stated for `Spec R` and not for a general scheme, because that is the range in
which closure under extensions is proved here: Serre vanishing is applied on the affine open `⊤`,
and the comparison `Γ(E)^~ → E` is the counit of an adjunction that exists only over an affine
base. The general statement is Stacks 06VT and is still open in this repository, as is the
Grothendieck abelian structure on the quasi-coherent modules themselves (Stacks 077P, which rests
on Gabber's Stacks 077N). Neither is needed for the affine statements below, and no `@[stacks]`
attribute is attached for that reason: a tag here would report those general tags as formalized.

The long exact cohomology sequence enters through
`Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives`, the `ℕ`-indexed right
derived δ-functor of `Γ(U, -)`; its degree-`n` part is `(secF 𝒪 U).rightDerived n` *by
definition*, which is `Hgroup 𝒪 U n`, the group Serre vanishing speaks about, so no comparison of
indexings is needed. The identification of the degree-zero part with `Γ(U, -)` is
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`, whose left-exactness side condition is
`Stacks.SectionsExact.preservesFiniteLimits_secF`.

Sheaf cohomology here is valued in `AddCommGrpCat` while `~` needs an `R`-module, so the
surjectivity obtained from the δ-functor is transported to `moduleSpecΓFunctor` by hand. The two
functors have literally the same underlying map on sections over `⊤`, so the transport is just
`ModuleCat.epi_iff_surjective` against `AddCommGrpCat.epi_iff_surjective`.

`(Spec R).Modules` and `SheafOfModules (Spec R).ringCatSheaf` are definitionally equal but carry
separately declared `Category` and `Preadditive` instances, and which of the two a statement is
phrased in is not a matter of taste here. Additivity of `moduleSpecΓFunctor` is only found by
instance search in the first view, while the cohomological step needs the second: the comparison
`F.rightDerived 0 ≅ F` of a functor out of `SheafOfModules (Spec R).ringCatSheaf` cannot be
applied to an object of `(Spec R).Modules`, because the identification of `TopCat.Sheaf` with
sheaves for `Opens.grothendieckTopology` is not visible at the transparency instance search uses.
So the vanishing argument is phrased over `SheafOfModules`, the transport of surjectivity is
stated for a bare morphism, and everything after that is over `(Spec R).Modules`; the two views
are crossed only where a short complex or a morphism is passed, which unification handles.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 01IC](https://stacks.math.columbia.edu/tag/01IC)
* [Stacks Project, Tag 06VT](https://stacks.math.columbia.edu/tag/06VT)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w u

namespace AlgebraicGeometry

variable (R : CommRingCat.{u})

/-- Global sections of `𝒪_{Spec R}`-modules is left exact: it is right adjoint to `~`. -/
instance moduleSpecΓFunctor_preservesFiniteLimits :
    PreservesFiniteLimits (moduleSpecΓFunctor (R := R)) := by
  have := (tilde.adjunction (R := R)).rightAdjoint_preservesLimits
  infer_instance

/-- **Serre vanishing in the form used below.** If `0 → A → E → B → 0` is a short exact sequence
of `𝒪_{Spec R}`-modules with `A` quasi-coherent, then `Γ(Spec R, E) → Γ(Spec R, B)` is surjective
as a map of abelian groups: the long exact cohomology sequence continues into
`H¹(Spec R, A) = 0`. -/
theorem epi_secF_map_g_of_shortExact
    {S : ShortComplex (SheafOfModules.{u} (Spec R).ringCatSheaf)} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] :
    Epi ((secF (Spec R).ringCatSheaf (⊤ : Opens (Spec R))).map S.g) := by
  let _ : HasDerivedCategory.{u} AddCommGrpCat.{u} :=
    Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian _
  let _ : PreservesFiniteLimits (secF (Spec R).ringCatSheaf (⊤ : Opens (Spec R))) :=
    Stacks.SectionsExact.preservesFiniteLimits_secF _ _
  set F := secF (Spec R).ringCatSheaf (⊤ : Opens (Spec R))
  let D := Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives F
  have hz : IsZero ((D.functor 1).obj S.X₁) :=
    Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen
      (Spec R) S.X₁ ⊤ (isAffineOpen_top _) 1 one_pos
  have hepi : Epi ((F.rightDerived 0).map S.g) :=
    (ShortComplex.exact_iff_epi _ (hz.eq_of_tgt (D.δ hS 0) 0)).1 (D.exact_δ₁ hS 0)
  rw [← NatIso.naturality_1 (Functor.rightDerivedZeroIsoSelf F) S.g]
  infer_instance

/-- Surjectivity of a map on global sections is the same statement for abelian groups and for
`R`-modules: the two functors agree on the underlying map of sections over `⊤`. -/
theorem epi_moduleSpecΓFunctor_map_of_epi_secF_map {M N : (Spec R).Modules} (f : M ⟶ N)
    (h : Epi ((secF (Spec R).ringCatSheaf (⊤ : Opens (Spec R))).map f)) :
    Epi ((moduleSpecΓFunctor (R := R)).map f) := by
  rw [ModuleCat.epi_iff_surjective]
  exact (AddCommGrpCat.epi_iff_surjective _).1 h

/-- Global sections carry a short exact sequence of `𝒪_{Spec R}`-modules with quasi-coherent
kernel to a short exact sequence of `R`-modules. -/
theorem shortExact_map_moduleSpecΓFunctor {S : ShortComplex (Spec R).Modules}
    (hS : S.ShortExact) [S.X₁.IsQuasicoherent] :
    (S.map (moduleSpecΓFunctor (R := R))).ShortExact :=
  have := hS.mono_f
  { exact := hS.exact.map_of_mono_of_preservesKernel _ ‹Mono S.f› inferInstance
    mono_f := show Mono ((moduleSpecΓFunctor (R := R)).map S.f) from inferInstance
    epi_g := epi_moduleSpecΓFunctor_map_of_epi_secF_map R S.g
      (epi_secF_map_g_of_shortExact R (S := S) hS) }

/-- **Quasi-coherent modules on an affine scheme are closed under extensions.** The middle term
of a short exact sequence of `𝒪_{Spec R}`-modules whose outer terms are quasi-coherent is
quasi-coherent: global sections of the sequence are again short exact by Serre vanishing, and the
counit `Γ(-)^~ ⟶ 𝟭` of the tilde–Gamma adjunction is then an isomorphism of short exact sequences
on the outer terms, hence on the middle one by the short five lemma. -/
theorem isQuasicoherent_X₂_of_shortExact {S : ShortComplex (Spec R).Modules} (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] : S.X₂.IsQuasicoherent := by
  let φ : S.map (moduleSpecΓFunctor (R := R) ⋙ tilde.functor R) ⟶ S.map (𝟭 ((Spec R).Modules)) :=
    S.mapNatTrans Scheme.Modules.fromTildeΓNatTrans
  have h₁ : IsIso φ.τ₁ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₁
  have h₃ : IsIso φ.τ₃ := Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent S.X₃
  exact (isQuasicoherent_iff_isIso_fromTildeΓ S.X₂).2
    (ShortComplex.isIso₂_of_shortExact_of_isIso₁₃ φ
      ((shortExact_map_moduleSpecΓFunctor R hS).map_of_exact (tilde.functor R)) hS)

/-- The zero module is quasi-coherent, being `0̃`. -/
instance isQuasicoherent_containsZero :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).ContainsZero where
  exists_zero := by
    obtain ⟨Z, hZ⟩ := HasZeroObject.zero (C := ModuleCat.{u} R)
    exact ⟨(tilde.functor R).obj Z, (tilde.functor R).map_isZero hZ, inferInstance⟩

/-- Quasi-coherent modules on `Spec R` are closed under cokernels. -/
instance isQuasicoherent_isClosedUnderCokernels :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderCokernels where
  cokernels_le := by
    rintro _ ⟨f, k, hk, h₁, h₂⟩
    have := h₁
    have := h₂
    exact (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_of_iso
      (IsColimit.coconePointUniqueUpToIso (cokernelIsCokernel f) hk)
      (Scheme.Modules.isQuasicoherent_cokernel f)

/-- Quasi-coherent modules on `Spec R` are closed under extensions. -/
instance isQuasicoherent_isClosedUnderExtensions :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {S} hS h₁ h₃ := by
    have : S.X₁.IsQuasicoherent := h₁
    have : S.X₃.IsQuasicoherent := h₃
    exact isQuasicoherent_X₂_of_shortExact R (S := S) hS

/-- **Quasi-coherent modules on an affine scheme form a weak Serre subcategory**: they contain
zero, are closed under isomorphisms, and are closed under kernels, cokernels and extensions. -/
instance isQuasicoherent_isWeakSerreClass :
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).IsWeakSerreClass where

/-- The five-term formulation of `isQuasicoherent_isWeakSerreClass`: in an exact sequence
`A₀ → A₁ → A₂ → A₃ → A₄` of `𝒪_{Spec R}`-modules with the four outer terms quasi-coherent, the
middle term is quasi-coherent. -/
theorem isQuasicoherent_isWeakSerre :
    WeakSerre.IsWeakSerre (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf) :=
  ⟨inferInstance,
    (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).exists_prop_of_isWeakSerreClass,
    fun E h₀ h₁ h₃ h₄ ↦ ObjectProperty.prop_mid_of_exact₄
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf).prop_obj₂_of_exact
      E.zero₀ E.zero₁ E.zero₂ E.exact₁ E.exact₂ E.exact₃ h₀ h₁ h₃ h₄⟩

/-- `D_QCoh(𝒪_{Spec R})`, the complexes with quasi-coherent cohomology, is a strictly full
saturated triangulated subcategory of `D(𝒪_{Spec R})`.

The derived category is taken at a free `[HasDerivedCategory.{w} (Spec R).Modules]` binder: the
weak Serre property of quasi-coherence is a statement about `𝒪_{Spec R}`-modules and says nothing
about any model of the derived category, so the conclusion holds at every one. -/
instance derivedQuasicoherent_isTriangulated [HasDerivedCategory.{w} (Spec R).Modules] :
    (DerivedCategoryB.derivedCategoryB (A := (Spec R).Modules)
      (SheafOfModules.isQuasicoherent (Spec R).ringCatSheaf)).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _ (isQuasicoherent_isWeakSerre R)

end AlgebraicGeometry

end
