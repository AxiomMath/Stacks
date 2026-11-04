module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.AffineBase
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Finiteness
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology

/-!
# Finiteness of the cohomology over an affine base is coherence of the higher direct image

[Stacks, Tag 02O6] says that for `A` a Noetherian ring, `f : X ⟶ Spec A` proper and `F` a
coherent `𝒪_X`-module, each `Hⁱ(X, F)` is a finite `A`-module. Its proof in the source is one
step: *"this is just the affine case of [Stacks, Tag 02O5]"*, namely [Stacks, Tags 01XJ] and
[01XK] identify `Rⁱ f_* F` with the quasi-coherent module attached to `Hⁱ(X, F)`, and
[Stacks, Tag 01XZ] says that module is coherent exactly when `Hⁱ(X, F)` is a finite `A`-module.

This file proves that step, in both directions and with no properness used: over an **affine**
base, for a quasi-compact quasi-separated `f` and a quasi-coherent `F`, finiteness of the
`Γ(S, ⊤)`-module `Hⁱ(X, F)` and coherence of `Rⁱ f_* F` are equivalent. So [Stacks, Tag 02O6]
and the affine case of [Stacks, Tag 02O5] are one statement, and anything that discharges either
discharges the other.

Two consequences are drawn. The first is unconditional: along a **finite** morphism to an affine
locally Noetherian base the cohomology of a coherent module is a finite module, because
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_rightDerived_of_isFinite` supplies
the coherence. The second is the form in which the Euler-characteristic development consumes
[Stacks, Tag 02O6]: for `X` over a field `k`, finite dimensionality of
`AlgebraicGeometry.cohomologyOverField k f F n` follows from coherence of `Rⁿ f_* F`, so the
hypothesis carried by the additivity of the Euler characteristic and by the dévissage statements
of `StacksDraft/AlgebraicGeometry/F3b/CurveTensorEuler/` is implied by [Stacks, Tag 02O5] at the
base `Spec k`.

## Main results

* `Stacks.AlgebraicGeometry.ProperCohomologyFinite.moduleFinite_cohomology_of_isCoherent`:
  over an affine base, coherence of `Rⁿ f_* F` gives finiteness of the `Γ(S, ⊤)`-module
  `Hⁿ(X, F)`. **This is the content of [Stacks, Tag 02O6] relative to [Stacks, Tag 02O5].**
* `…ProperCohomologyFinite.isCoherent_of_moduleFinite_cohomology`: the converse, over an affine
  locally Noetherian base.
* `…ProperCohomologyFinite.moduleFinite_cohomology_iff_isCoherent`: the two together.
* `…ProperCohomologyFinite.moduleFinite_cohomology_of_isFinite`: **[Stacks, Tag 02O6] for a
  finite morphism**, unconditionally.
* `…ProperCohomologyFinite.isCoherent_rightDerived_of_isFiniteType`: along a proper morphism to a
  locally Noetherian base, coherence of `Rⁿ f_* F` is finiteness of type and nothing else — so
  the whole of [Stacks, Tag 02O5] is that one property.
* `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_forall_isFiniteType`: the
  consequence for the consumers. The [Stacks, Tag 02O6] hypothesis they carry follows from the
  single property `IsFiniteType` of the higher direct images.
* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isCoherent_rightDerived` and
  `AlgebraicGeometry.forall_finiteDimensional_cohomologyOverField_of_forall_isCoherent`: the
  same reduction in the `cohomologyOverField` spelling the Euler-characteristic development
  uses, pointwise and quantified over all coherent modules.
* `AlgebraicGeometry.finiteDimensional_cohomologyOverField_of_isFinite`: **[Stacks, Tag 02O6]
  over a field for a finite morphism**, unconditionally.

## Implementation notes

**No `@[stacks 02O6]` attribute is attached to anything here.** The tag asserts the finiteness
with no hypothesis beyond properness of `f`, Noetherianness of the base and coherence of `F`;
every statement below either carries the coherence of `Rⁿ f_* F` as a hypothesis — which is
[Stacks, Tag 02O5], not in the library for a general proper morphism — or restricts `f` to be
finite. The equivalence is nevertheless the whole mathematical content of the tag's own proof.

**Why the base is `Γ(S, ⊤)` and not a ring.** [Stacks, Tag 01XK] is formalized as
`Stacks.Cohomology.AffineBase.affineBaseHigherDirectImageIso`, an isomorphism of functors into
`ModuleCat Γ(S, ⊤)` whose left-hand side is the cohomology upstairs with scalars restricted
along `f.appTop`. Stating the result at `Γ(S, ⊤)` lets it be applied with no transport; for
`S = Spec A` the ring `Γ(S, ⊤)` is isomorphic to `A` and the field case below shows how the
transport is made when it is wanted.

**Transporting finiteness across a surjective ring map.** The `k`-module structure on
`AlgebraicGeometry.cohomologyOverField` restricts scalars along `Γ(Spec k, ⊤) ≅ k` composed with
`f.appTop`, so finiteness over `Γ(Spec k, ⊤)` has to be moved to `k` across a ring
*isomorphism*. `moduleFinite_compHom_of_surjective` does this for any surjective ring map, by
`Module.Finite.trans`: a surjective ring map makes the target a finite module over the source.

## References

* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 02O5](https://stacks.math.columbia.edu/tag/02O5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.CoherenceCriteria
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.FiniteDirectImageCoherent

universe u

namespace Stacks.AlgebraicGeometry.ProperCohomologyFinite

/-! ### Transport of finiteness along a surjective ring map -/

/-- **A module finite over `A` is finite over `R` when `R → A` is surjective**, for the
`R`-module structure obtained by restricting scalars.

`R` is a finite `R`-module over itself, hence `A` is a finite `R`-module because `R → A` is
surjective; the scalar tower is the definition of the restricted action, and
`Module.Finite.trans` concludes. -/
theorem moduleFinite_compHom_of_surjective {R A : Type u} [CommRing R] [CommRing A]
    (ψ : R →+* A) (hψ : Function.Surjective ψ) (M : Type u) [AddCommGroup M] [Module A M]
    [Module.Finite A M] : @Module.Finite R M _ _ (Module.compHom M ψ) := by
  let _ : Module R M := Module.compHom M ψ
  let _ : Algebra R A := ψ.toAlgebra
  have : Module.Finite R A := Module.Finite.of_surjective (Algebra.linearMap R A) hψ
  have : IsScalarTower R A M := ⟨fun x a m => by
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    exact mul_smul (ψ x) a m⟩
  exact Module.Finite.trans A M

/-! ### [Stacks, Tag 02O6] relative to [Stacks, Tag 02O5] -/

variable {X S : Scheme.{u}} (f : X ⟶ S) [AlgebraicGeometry.QuasiCompact f]
  [AlgebraicGeometry.QuasiSeparated f] [AlgebraicGeometry.IsAffine S]

/-- The cohomology of `F` upstairs, with scalars restricted along `f.appTop`, is the global
sections of `Rⁿ f_* F`: this is [Stacks, Tag 01XK] evaluated at `F`. -/
noncomputable def cohomologyIsoSectionsRightDerived (F : X.Modules) [F.IsQuasicoherent] (n : ℕ) :
    (ModuleCat.restrictScalars f.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F) ≅
      (moduleGlobalSections S).obj (((Scheme.Modules.pushforward f).rightDerived n).obj F) :=
  (affineBaseHigherDirectImageIso f n).app
    (⟨F, inferInstance⟩ : (SheafOfModules.isQuasicoherent X.ringCatSheaf).FullSubcategory)

/-- **The content of [Stacks, Tag 02O6], relative to [Stacks, Tag 02O5].** Over an affine base,
coherence of `Rⁿ f_* F` makes `Hⁿ(X, F)` a finite `Γ(S, ⊤)`-module.

A coherent module is quasi-coherent of finite type, so its sections over the affine open `⊤`
form a finite module ([Stacks, Tag 01XZ] (4), as
`AlgebraicGeometry.moduleFinite_sections_on_affine`); [Stacks, Tag 01XK] identifies those
sections with `Hⁿ(X, F)`. Properness of `f` is not used: only that it is quasi-compact and
quasi-separated, which [Stacks, Tag 01XK] needs. -/
theorem moduleFinite_cohomology_of_isCoherent (F : X.Modules) [F.IsQuasicoherent] (n : ℕ)
    (h : (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsCoherent) :
    Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived n).obj F)) := by
  obtain ⟨hqc, hft⟩ := isQuasicoherent_isFiniteType_of_isCoherent
    (((Scheme.Modules.pushforward f).rightDerived n).obj F)
  have := hqc
  have := hft
  have hfin : Module.Finite Γ(S, ⊤)
      ((moduleGlobalSections S).obj (((Scheme.Modules.pushforward f).rightDerived n).obj F)) :=
    AlgebraicGeometry.moduleFinite_sections_on_affine
      (((Scheme.Modules.pushforward f).rightDerived n).obj F) ⊤ (isAffineOpen_top S)
  exact Module.Finite.equiv (cohomologyIsoSectionsRightDerived f F n).toLinearEquiv.symm

/-- **The converse**: over an affine locally Noetherian base, finiteness of `Hⁿ(X, F)` as a
`Γ(S, ⊤)`-module makes `Rⁿ f_* F` coherent.

`Rⁿ f_* F` is quasi-coherent by [Stacks, Tag 01XJ]; [Stacks, Tag 01XK] turns the hypothesis into
finiteness of its sections over `⊤`, which is an affine open covering of `S` by itself, so it is
of finite type ([Stacks, Tag 01XZ] (5) ⇒ (2)); quasi-coherent of finite type over a locally
Noetherian scheme is coherent. -/
theorem isCoherent_of_moduleFinite_cohomology [IsLocallyNoetherian S] (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ)
    (h : Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived n).obj F))) :
    (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsCoherent := by
  have hsec : Module.Finite Γ(S, ⊤)
      ((moduleGlobalSections S).obj (((Scheme.Modules.pushforward f).rightDerived n).obj F)) :=
    Module.Finite.equiv (cohomologyIsoSectionsRightDerived f F n).toLinearEquiv
  have hft : (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsFiniteType :=
    isFiniteType_of_cover_isFiniteTildeOn
      (((Scheme.Modules.pushforward f).rightDerived n).obj F)
      (fun _ : PUnit.{u + 1} => (⊤ : S.Opens)) (IsOpenCover.mk iSup_const)
      (fun _ => isAffineOpen_top S)
      (fun _ => isFiniteTildeOn_of_moduleFinite_sections _ ⟨⊤, isAffineOpen_top S⟩ hsec)
  have := hft
  exact isCoherent_of_isQuasicoherent_of_isFiniteType _

/-- **[Stacks, Tag 02O6] is the affine case of [Stacks, Tag 02O5].** Over an affine locally
Noetherian base, `Hⁿ(X, F)` is a finite `Γ(S, ⊤)`-module exactly when `Rⁿ f_* F` is coherent. -/
theorem moduleFinite_cohomology_iff_isCoherent [IsLocallyNoetherian S] (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ) :
    Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars f.appTop.hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F)) ↔
      (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsCoherent :=
  ⟨isCoherent_of_moduleFinite_cohomology f F n, moduleFinite_cohomology_of_isCoherent f F n⟩

/-- **[Stacks, Tag 02O6] for a finite morphism**, unconditionally. A finite morphism is proper,
so this is the tag's conclusion under the strictly stronger hypothesis `IsFinite f`; the
coherence input is [Stacks, Tag 01Y6], as
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_rightDerived_of_isFinite`. -/
theorem moduleFinite_cohomology_of_isFinite {X S : Scheme.{u}} (g : X ⟶ S)
    [AlgebraicGeometry.IsFinite g] [AlgebraicGeometry.IsAffine S] [IsLocallyNoetherian S]
    (F : X.Modules) [F.IsCoherent] (n : ℕ) :
    Module.Finite Γ(S, ⊤) ((ModuleCat.restrictScalars g.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived n).obj F)) := by
  have := isQuasicoherent_of_isCoherent F
  exact moduleFinite_cohomology_of_isCoherent g F n
    (isCoherent_rightDerived_of_isFinite g F n)

/-- **Coherence of `Rⁿ f_* F` along a proper morphism is finiteness of type and nothing else.**
Quasi-coherence is found by instance search from [Stacks, Tag 01XJ], and quasi-coherent of finite
type over a locally Noetherian scheme is coherent ([Stacks, Tag 01XZ]). So the whole of
[Stacks, Tag 02O5] at a general proper morphism is the single property `IsFiniteType`. -/
theorem isCoherent_rightDerived_of_isFiniteType {X S : Scheme.{u}} (g : X ⟶ S)
    [AlgebraicGeometry.IsProper g] [IsLocallyNoetherian S] (F : X.Modules) [F.IsQuasicoherent]
    (n : ℕ) (h : (((Scheme.Modules.pushforward g).rightDerived n).obj F).IsFiniteType) :
    (((Scheme.Modules.pushforward g).rightDerived n).obj F).IsCoherent := by
  have := h
  exact isCoherent_of_isQuasicoherent_of_isFiniteType _

end Stacks.AlgebraicGeometry.ProperCohomologyFinite

namespace AlgebraicGeometry

open Stacks.AlgebraicGeometry.ProperCohomologyFinite

/-! ### The field case, in the spelling the Euler characteristic uses -/

/-- `AlgebraicGeometry.cohomologyOverField` with its scalar restriction factored through
`Γ(Spec k, ⊤)`. The two differ only in that the definition uses `f.appLE ⊤ ⊤` where
[Stacks, Tag 01XK] uses `f.appTop`, and those are equal by
`AlgebraicGeometry.Scheme.Hom.app_eq_appLE`. -/
theorem cohomologyOverField_eq_restrictScalars_appTop (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (F : X.Modules) (n : ℕ) :
    cohomologyOverField k f F n =
      (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom).obj
        (((moduleGlobalSections X).rightDerived n).obj F) := by
  unfold cohomologyOverField
  rw [show f.appLE ⊤ ⊤ (by simp) = f.appTop from (Scheme.Hom.app_eq_appLE f).symm]
  rfl

/-- **The hypothesis [Stacks, Tag 02O6] that the Euler-characteristic development carries, from
coherence of the higher direct image.** For `X` over a field `k` by a quasi-compact
quasi-separated morphism, if `Rⁿ f_* F` is coherent then `Hⁿ(X, F)` is finite-dimensional
over `k`.

Finiteness over `Γ(Spec k, ⊤)` is `moduleFinite_cohomology_of_isCoherent`; it is moved to `k`
across the ring isomorphism `Γ(Spec k, ⊤) ≅ k` by `moduleFinite_compHom_of_surjective`. -/
theorem finiteDimensional_cohomologyOverField_of_isCoherent_rightDerived (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f] (F : X.Modules)
    [F.IsQuasicoherent] (n : ℕ)
    (h : (((Scheme.Modules.pushforward f).rightDerived n).obj F).IsCoherent) :
    FiniteDimensional k (cohomologyOverField k f F n) := by
  rw [cohomologyOverField_eq_restrictScalars_appTop k f F n]
  have hA := moduleFinite_cohomology_of_isCoherent f F n h
  have hsurj : Function.Surjective (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of k)).inv).2
  exact moduleFinite_compHom_of_surjective
    (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom hsurj
    ((ModuleCat.restrictScalars f.appTop.hom).obj
      (((moduleGlobalSections X).rightDerived n).obj F))

/-- **[Stacks, Tag 02O6] over a field, for the whole family of coherent modules at once**, in
exactly the shape carried as the hypothesis `h02O6` by dévissage statements elsewhere
and as `hfin₁`/`hfin₃` by
`AlgebraicGeometry.eulerCharacteristic_add_of_shortExact_of_finiteDimensional`. Its input is
[Stacks, Tag 02O5] at the base `Spec k`. -/
theorem forall_finiteDimensional_cohomologyOverField_of_forall_isCoherent (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [QuasiCompact f] [QuasiSeparated f]
    (h : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, (((Scheme.Modules.pushforward f).rightDerived n).obj G).IsCoherent) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f G n) := by
  intro G hG n
  have := hG
  have := isQuasicoherent_of_isCoherent G
  exact finiteDimensional_cohomologyOverField_of_isCoherent_rightDerived k f G n (h G hG n)

/-- **The hypothesis [Stacks, Tag 02O6] from ONE property.** For `X` proper over a field `k`, if
each `Rⁿ f_* G` is of finite type then each `Hⁿ(X, G)` is finite-dimensional over `k`, for every
coherent `G`. The hypothesis is exactly the residue of [Stacks, Tag 02O5] at a general proper
morphism — quasi-coherence of `Rⁿ f_* G` is free by instance search from [Stacks, Tag 01XJ], and
quasi-coherent of finite type over a locally Noetherian base is coherent — so the `h02O6`
hypothesis carried across the Euler-characteristic development reduces to that single property
and to nothing else. -/
theorem forall_finiteDimensional_cohomologyOverField_of_forall_isFiniteType (k : Type u)
    [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    (h : ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, (((Scheme.Modules.pushforward f).rightDerived n).obj G).IsFiniteType) :
    ∀ G : X.Modules, SheafOfModules.IsCoherent G →
      ∀ n : ℕ, FiniteDimensional k (cohomologyOverField k f G n) := by
  refine forall_finiteDimensional_cohomologyOverField_of_forall_isCoherent k f ?_
  intro G hG n
  have := hG
  have := isQuasicoherent_of_isCoherent G
  exact isCoherent_rightDerived_of_isFiniteType f G n (h G hG n)

/-- **[Stacks, Tag 02O6] over a field for a finite morphism**, unconditionally: for `X` finite
over `Spec k`, the cohomology of a coherent module is finite-dimensional over `k`. The coherence
input is [Stacks, Tag 01Y6]. -/
theorem finiteDimensional_cohomologyOverField_of_isFinite (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsFinite f] (F : X.Modules) [F.IsCoherent]
    (n : ℕ) : FiniteDimensional k (cohomologyOverField k f F n) := by
  have := isQuasicoherent_of_isCoherent F
  exact finiteDimensional_cohomologyOverField_of_isCoherent_rightDerived k f F n
    (Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_rightDerived_of_isFinite
      f F n)

end AlgebraicGeometry

end
