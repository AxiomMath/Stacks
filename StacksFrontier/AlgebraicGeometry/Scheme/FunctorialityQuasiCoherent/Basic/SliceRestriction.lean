module

public import Mathlib.Algebra.Category.ModuleCat.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.EffectiveEpi.Comp
public import Mathlib.CategoryTheory.ExtremalEpi
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.CategoryTheory.Limits.SmallComplete
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.Tactic.SetNotationForOrder
public import Mathlib.Topology.Sheaves.Over
public import StacksCore.Tactic.StacksAttribute

/-!
# Pushforward of quasi-coherent modules: the tilde criterion and slice restriction

Part 1 of the proof of `AlgebraicGeometry.pushforward_isQuasicoherent`.

On `Spec R`, the tilde-Gamma counit `M.fromTildeΓ` is an isomorphism iff every basic-open
section restriction `Γ(M, ⊤) → Γ(M, D(f))` is a localization at `powers f`. The over-site of an
open `U` is identified with the opens site of `U`, and so sheaves of modules on the slice
`X.ringCatSheaf.over U` with sheaves of modules on the open subscheme `U.toScheme`; slice
presentations transport along this identification.

## References

* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u


namespace AlgebraicGeometry

open CategoryTheory Limits

/-- If `f` is a localization map and `g ∘ₗ e = f` for a linear equivalence `e`, then `g` is a
localization map as well. -/
private theorem isLocalizedModule_of_comp_linearEquiv {R : Type u} [CommRing R] {S : Submonoid R}
    {M M₀ M' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M₀] [Module R M₀]
    [AddCommGroup M'] [Module R M'] {f : M →ₗ[R] M'} {g : M₀ →ₗ[R] M'}
    (hf : IsLocalizedModule S f) (e : M ≃ₗ[R] M₀) (h : g ∘ₗ e.toLinearMap = f) :
    IsLocalizedModule S g := by
  have := IsLocalizedModule.of_linearEquiv_right S f e.symm
  rwa [← h, LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.comp_id] at this

/-- **Basic-open restriction of a `tilde` sheaf is a module localization.**

For `N : ModuleCat R` and `f : R`, the presheaf restriction map of the associated sheaf
`Ñ = tilde N` from global sections `Γ(Ñ, ⊤)` to the basic open `Γ(Ñ, D(f))` exhibits the
latter as `IsLocalizedModule (powers f)` over `R`.

This is the affine, Spec-local heart of that statement. Mathlib
carries the localization fact for the map `tilde.toOpen N (D f) : N → Γ(Ñ, D(f))` out of
`N`; since `tilde.toOpen N ⊤ : N → Γ(Ñ, ⊤)` is an isomorphism and
`tilde.toOpen N (D f) = tilde.toOpen N ⊤ ≫ restriction` (`tilde.toOpen_res`), precomposing
the localization map with the inverse isomorphism (`IsLocalizedModule.of_linearEquiv_right`)
transfers the property to the restriction map. Mathlib states the fact only
for the map out of `N`, not for the presheaf restriction of `Ñ`. -/
@[ega "I 9.6.2" "partial"]
private theorem isLocalizedModule_tilde_restrict {R : CommRingCat.{u}} (N : ModuleCat.{u} R)
    (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj (tilde N)).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  have hres := tilde.toOpen_res N ⊤ (PrimeSpectrum.basicOpen f)
    (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤))
  exact isLocalizedModule_of_comp_linearEquiv
    (inferInstance : IsLocalizedModule (Submonoid.powers f)
      (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom)
    (tilde.isoTop N).toLinearEquiv (by rw [← hres]; rfl)

/-- **Basic-open restriction localizes, for a sheaf in the essential image of `tilde`.**

For a sheaf of modules `M` on `Spec R` whose tilde-Gamma counit `M.fromTildeΓ` is an
isomorphism (equivalently, `M` lies in the essential image of the `tilde` functor — the
honest Spec-affine stand-in for quasi-coherence, see the section header), the presheaf
restriction map of `M` from global sections `Γ(M, ⊤)` to the basic open `Γ(M, D(f))`
exhibits the latter as `IsLocalizedModule (powers f)` over `R`.

This transports `isLocalizedModule_tilde_restrict` across the isomorphism
`M.fromTildeΓ : tilde N ⟶ M` (where `N = Γ(M, ⊤)`): the induced presheaf isomorphism is
natural in the open, so on each of `⊤` and `D(f)` it provides an `R`-linear isomorphism
intertwining the two restriction maps. Post- and pre-composing the localization map for
`tilde N` with these isomorphisms (`IsLocalizedModule.of_linearEquiv`,
`IsLocalizedModule.of_linearEquiv_right`) yields the property for `M`.

it is the affine engine of that statement. The
general quasi-coherent case additionally requires the (currently Mathlib-absent) bridge
`IsQuasicoherent M → IsIso M.fromTildeΓ`. -/
private theorem isLocalizedModule_restrict_of_isIso_fromTildeΓ {R : CommRingCat.{u}}
    (M : (Spec R).Modules) [IsIso M.fromTildeΓ] (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  -- the presheaf-level isomorphism induced by the (iso) counit `M.fromTildeΓ`
  let ψ := (TopCat.Sheaf.forget (ModuleCat R) (Spec R)).map (modulesSpecToSheaf.map M.fromTildeΓ)
  have : IsIso ψ := inferInstance
  have hTop : IsIso (ψ.app (.op (⊤ : (Spec R).Opens))) := inferInstance
  have hDf : IsIso (ψ.app (.op (PrimeSpectrum.basicOpen f))) := inferInstance
  -- The two components, ascribed once at the `.presheaf.obj` spelling: `TopCat.Sheaf.forget`
  -- reaches the same module by `delta` only, and without the ascription the `convert` below is
  -- left with `HEq` goals between the two spellings instead of an equation of linear maps.
  let ψTop : (modulesSpecToSheaf.obj
        (tilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)))).presheaf.obj (.op ⊤) ⟶
      (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤) :=
    ψ.app (.op (⊤ : (Spec R).Opens))
  let ψDf : (modulesSpecToSheaf.obj
        (tilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)))).presheaf.obj
        (.op (PrimeSpectrum.basicOpen f)) ⟶
      (modulesSpecToSheaf.obj M).presheaf.obj (.op (PrimeSpectrum.basicOpen f)) :=
    ψ.app (.op (PrimeSpectrum.basicOpen f))
  have : IsIso ψTop := hTop
  have : IsIso ψDf := hDf
  -- the component isomorphisms as `R`-linear equivalences
  let eTop : _ ≃ₗ[R] _ := (asIso ψTop).toLinearEquiv
  let eDf : _ ≃ₗ[R] _ := (asIso ψDf).toLinearEquiv
  -- the restriction map of `tilde N` (localizes by `isLocalizedModule_tilde_restrict`)
  let rt := ((modulesSpecToSheaf.obj
        (tilde ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)))).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom
  -- naturality square of `ψ` for `D(f) ⟶ ⊤`
  have hnat := ψ.naturality (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op
  have hnathom := congrArg ModuleCat.Hom.hom hnat
  rw [ModuleCat.hom_comp, ModuleCat.hom_comp] at hnathom
  have hrt : IsLocalizedModule (Submonoid.powers f) rt :=
    isLocalizedModule_tilde_restrict ((modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤)) f
  have step1 : IsLocalizedModule (Submonoid.powers f) (eDf.toLinearMap ∘ₗ rt) :=
    IsLocalizedModule.of_linearEquiv (S := Submonoid.powers f) (f := rt) (e := eDf)
  -- The target restriction map composed with `eTop` is `eDf ∘ rt`. Stated as a fully-typed
  -- equation of named linear maps rather than reached by `convert … using 1`: `convert` descends
  -- into the module-instance arguments of `IsLocalizedModule` and leaves the map argument as an
  -- `HEq`, which `LinearMap.ext` cannot close.
  let resM := ((modulesSpecToSheaf.obj M).presheaf.map
    (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom
  have hmap : resM ∘ₗ eTop.toLinearMap = eDf.toLinearMap ∘ₗ rt := by
    apply LinearMap.ext
    intro x
    -- Term mode: the goal mixes `(TopCat.Sheaf.forget _ _).obj M` with `M.presheaf`, so it is
    -- not type-correct at `implicit` transparency and `simp only [LinearMap.comp_apply]` refuses
    -- silently.
    exact (LinearMap.congr_fun hnathom x).symm
  exact isLocalizedModule_of_comp_linearEquiv step1 eTop hmap

/-- A morphism of sheaves of `R`-modules on `Spec R` that is an isomorphism on every basic open
`D(f)` is an isomorphism. This is the "isomorphism on a basis ⟹ isomorphism" reduction specialised
to the basic-open basis of `Spec R` (`PrimeSpectrum.isBasis_basic_opens`): injectivity on stalks is
`stalkFunctor_map_injective_of_isBasis`, surjectivity on stalks is the basic-open germ lift, and
`isIso_of_stalkFunctor_map_iso` concludes. Glue used to assemble `IsIso M.fromTildeΓ`
from per-basic-open section data. -/
private theorem isIso_sheaf_of_isIso_app_basicOpen {R : CommRingCat.{u}}
    {F G : TopCat.Sheaf (ModuleCat.{u} R) (Spec R)} (α : F ⟶ G)
    (h : ∀ f : R, IsIso (α.1.app (.op (PrimeSpectrum.basicOpen f)))) : IsIso α := by
  have hB : TopologicalSpace.Opens.IsBasis (Set.range (@PrimeSpectrum.basicOpen R _)) :=
    PrimeSpectrum.isBasis_basic_opens
  have hinj : ∀ U ∈ Set.range (@PrimeSpectrum.basicOpen R _),
      Function.Injective (α.1.app (.op U)) := by
    rintro U ⟨f, rfl⟩
    exact ((ConcreteCategory.isIso_iff_bijective _).mp (h f)).1
  have hstalk : ∀ x, IsIso ((TopCat.Presheaf.stalkFunctor (ModuleCat.{u} R) x).map α.1) := by
    intro x
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB hinj x, ?_⟩
    intro t
    obtain ⟨U, hxU, hUB, s, rfl⟩ := TopCat.Presheaf.exists_mem_germ_eq_of_isBasis hB G.presheaf x t
    obtain ⟨f, rfl⟩ := hUB
    obtain ⟨s', rfl⟩ := ((ConcreteCategory.isIso_iff_bijective _).mp (h f)).2 s
    -- A term rather than `rw`: the goal mixes `F.presheaf.obj` with `F.obj.obj`, so it is not
    -- type-correct at `implicit` transparency and `rw` reports the pattern as absent.
    exact ⟨F.presheaf.germ _ x hxU s',
      TopCat.Presheaf.stalkFunctor_map_germ_apply _ x hxU α.1 s'⟩
  exact TopCat.Presheaf.isIso_of_stalkFunctor_map_iso α

/-- A linear map intertwining two localizations of the same module at the same submonoid is
bijective: if `f : M →ₗ M'` and `g : M →ₗ M''` both exhibit a localization at `S` and
`h : M' →ₗ M''` satisfies `h ∘ₗ f = g`, then `h` is bijective (it is the canonical localization
isomorphism `IsLocalizedModule.linearEquiv`). Stated with the two `IsLocalizedModule` facts as
explicit hypotheses to avoid typeclass-diamond ambiguity at the call site. -/
private theorem bijective_comp_of_localizations {R : Type u} [CommRing R] (S : Submonoid R)
    {M M' M'' : Type u} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
    [AddCommGroup M''] [Module R M''] {f : M →ₗ[R] M'} {g : M →ₗ[R] M''} {h : M' →ₗ[R] M''}
    (hf : IsLocalizedModule S f) (hg : IsLocalizedModule S g) (hh : h ∘ₗ f = g) :
    Function.Bijective h := by
  have := hf; have := hg
  have heq : h = (IsLocalizedModule.linearEquiv S f g).toLinearMap := by
    apply IsLocalizedModule.linearMap_ext S (f := f) (f' := g)
    apply LinearMap.ext
    intro x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, ← LinearMap.comp_apply, hh,
      LinearEquiv.coe_toLinearMap, IsLocalizedModule.linearEquiv_apply]
  rw [heq]
  exact (IsLocalizedModule.linearEquiv S f g).bijective

/-- **`IsIso M.fromTildeΓ` from per-basic-open section localization** (the cheap stalk/section
assembly of that statement, the assembly step). If for every
`f : R` the section restriction `Γ(M, ⊤) → Γ(M, D(f))` of a sheaf of modules `M` on `Spec R`
exhibits the target as `IsLocalizedModule (powers f)` over `R` — exactly the conclusion of the core
construction (`isLocalizedModule_basicOpen_of_isQuasicoherent`) — then the tilde-Gamma counit
`M.fromTildeΓ` is
an isomorphism (equivalently `M` lies in the essential image of `tilde`).

On each basic open `D(f)` the component of `modulesSpecToSheaf.map M.fromTildeΓ` is a map between
two localizations of `N = Γ(M, ⊤)` at `powers f`: the source `Γ(tilde N, D(f))` localizes via the
private instance `tilde.toOpen N (D f)` and the target `Γ(M, D(f))` localizes by hypothesis, and
the two
localization maps are intertwined by `Scheme.Modules.toOpen_fromTildeΓ_app`. Hence the component is
the canonical localization isomorphism (`IsLocalizedModule.linearEquiv`);
`isIso_sheaf_of_isIso_app_basicOpen` upgrades this to an isomorphism of sheaves, and
`modulesSpecToSheaf` being fully faithful reflects it to `IsIso M.fromTildeΓ`.

This turns the remaining keystone obligation into exactly the core construction: combined with the
converse engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ`, the per-basic-open localization hypothesis is
*equivalent* to `IsIso M.fromTildeΓ`. Mathlib has no `IsQuasicoherent → IsIso
fromTildeΓ` bridge. -/
private theorem isIso_fromTildeΓ_of_isLocalizedModule_restrict {R : CommRingCat.{u}}
    (M : (Spec R).Modules)
    (H : ∀ f : R, IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom) :
    IsIso M.fromTildeΓ := by
  have hmain : IsIso (modulesSpecToSheaf.map M.fromTildeΓ) := by
    apply isIso_sheaf_of_isIso_app_basicOpen
    intro f
    set N := (modulesSpecToSheaf.obj M).presheaf.obj (.op ⊤) with hN
    -- target localizes by hypothesis; source localizes by the `tilde.toOpen` instance
    have htgt : IsLocalizedModule (Submonoid.powers f)
        ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := H f
    set comp := (modulesSpecToSheaf.map M.fromTildeΓ).1.app (.op (PrimeSpectrum.basicOpen f))
      with hcomp
    rw [ConcreteCategory.isIso_iff_bijective]
    have hcompose := Scheme.Modules.toOpen_fromTildeΓ_app M (PrimeSpectrum.basicOpen f)
    -- the component intertwines the two localization maps of `N` at `powers f`
    have h1 : comp.hom ∘ₗ (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom
        = ((modulesSpecToSheaf.obj M).presheaf.map
          (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
      have e := congrArg ModuleCat.Hom.hom hcompose
      rwa [ModuleCat.hom_comp] at e
    show Function.Bijective (⇑comp.hom)
    exact bijective_comp_of_localizations (Submonoid.powers f)
      (inferInstance : IsLocalizedModule _ (tilde.toOpen N (PrimeSpectrum.basicOpen f)).hom)
      (H f) h1
  exact SpecModulesToSheafFullyFaithful.isIso_of_isIso_map M.fromTildeΓ

/- **Characterization of `IsIso M.fromTildeΓ` by section localization.** For a sheaf of modules
`M` on `Spec R`, the tilde-Gamma counit `M.fromTildeΓ` is an isomorphism iff for every `f : R` the
section restriction `Γ(M, ⊤) → Γ(M, D(f))` exhibits the target as `IsLocalizedModule (powers f)`.

The forward direction is the affine engine `isLocalizedModule_restrict_of_isIso_fromTildeΓ`; the
reverse is `isIso_fromTildeΓ_of_isLocalizedModule_restrict`. Combined with the core construction
(`isLocalizedModule_basicOpen_of_isQuasicoherent`, which is not formalized here) — which supplies
the right-hand side for any quasi-coherent `M` — this yields the affine case. -/
/-! ## Supplementary results — the core construction building blocks

The keystone the core construction that statement asks: for a *quasi-coherent*
`M : (Spec R).Modules` and `f : R`, the section restriction `Γ(M,⊤) → Γ(M,D(f))` is
`IsLocalizedModule (powers f)`. Via `isIso_fromTildeΓ_iff_isLocalizedModule_restrict` this is
*equivalent* to `IsIso M.fromTildeΓ` — i.e. to the statement that a quasi-coherent sheaf on an
affine scheme lies in the essential image of `tilde` (the `QCoh(Spec R) ≃ Mod R` equivalence). That
equivalence is a genuine Mathlib gap at the pinned commit
(`Mathlib/AlgebraicGeometry/Modules/Tilde.lean` only proves the *globally presented* case,
`isIso_fromTildeΓ_of_presentation`).

The composition lemma below discharges the **globally-presented** sub-case end to end (it is the
Route-F endpoint once a global presentation/tilde identification is in hand). The residual gap is
exactly the production of a global presentation/tilde from local (quasi-coherent) data on `Spec R`.
-/

/- **Basic-open restriction localizes, for a globally presented module.** If `M : (Spec R).Modules`
admits a global `SheafOfModules.Presentation`, then for every `f : R` the section restriction
`Γ(M,⊤) → Γ(M,D(f))` exhibits the target as `IsLocalizedModule (powers f)` over `R`.

This is the composition of Mathlib's `isIso_fromTildeΓ_of_presentation` (a global presentation
forces `M.fromTildeΓ` to be an isomorphism, i.e. `M` is a `tilde`) with the affine engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ`. It is the Route-F endpoint for the
globally-presented case; the general quasi-coherent case additionally requires producing a global
presentation/tilde identification from the (Mathlib-absent) affine `QCoh(Spec R) ≃ Mod R`
bridge. -/
/-- **`map_units` field of the core construction, for any sheaf of modules.** For
`M : (Spec R).Modules` and `f : R`, every element of `Submonoid.powers f` acts invertibly on
the sections `Γ(M, D(f))` over `R`. This is exactly the first field
`IsLocalizedModule.map_units` of the target `isLocalizedModule_basicOpen_of_isQuasicoherent`, in
the shape the 3-field constructor consumes.

It holds for an *arbitrary* `M` (no quasi-coherence needed): on `D(f)` the element `f` already maps
to a unit of the structure ring `Γ(O_{Spec R}, D(f))` (the away-localization
`IsLocalization.Away.algebraMap_isUnit`), and the `R`-action on `Γ(M, D(f))` factors through it via
the scalar tower `R → Γ(O, D(f)) → Γ(M, D(f))`. Packaged from Mathlib's
`AlgebraicGeometry.tilde.isUnit_algebraMap_end_basicOpen`. Only as the *named* field
of the Route-F decomposition; the substance of the core construction is `surj`/`exists_of_eq` (see
handoff). -/
private theorem map_units_restrict_basicOpen {R : CommRingCat.{u}} (M : (Spec R).Modules) (f : R) :
    ∀ x : Submonoid.powers f, IsUnit (algebraMap R (Module.End R
      ((modulesSpecToSheaf.obj M).presheaf.obj
        (.op (PrimeSpectrum.basicOpen f)))) (x : R)) := by
  rintro ⟨x, n, rfl⟩
  rw [map_pow]
  exact (Scheme.Modules.isUnit_algebraMap_end_of_le_basicOpen (M := M) f le_rfl).pow n

/-- **Finite basic-open cover refining a quasi-coherent presentation cover.** Given a
sheaf of modules `M` on `Spec R` together with quasi-coherent data `q` (a — possibly
infinite — open cover `q.X : q.I → (Spec R).Opens` of `⊤` with a presentation of
`M.over (q.X i)` on each member), there is a *finite* family of elements `t : Finset R`
whose basic opens cover `Spec R` (`Ideal.span t = ⊤`), with each basic open `D(r)`
(`r ∈ t`) contained in some member `q.X i` of the presentation cover.

This is the topological "finite-cover front" of that statement:
quasi-compactness of `Spec R` plus the basic-open basis (`PrimeSpectrum.isBasis_basic_opens`)
refine `q.X` to a finite basic-open subcover; the cover condition `q.coversTop` is read off the
`Opens.grothendieckTopology` sieve via `Sieve.mem_ofObjects_iff`, and finiteness is extracted
through `Ideal.span_eq_top_iff_finite`. To obtain `q` from `[M.IsQuasicoherent]`, take
`‹M.IsQuasicoherent›.nonempty_quasicoherentData.some`.

The remaining (heavy) step toward the affine case — transporting each presentation `q.presentation
i`
of `M.over (q.X i)` across `D(r) ≅ Spec R_r` to `IsIso ((M|_{D(r)}).fromTildeΓ)` — is the
site-slice ↔ scheme-pullback transport, which has no Mathlib support at the pinned commit.
Mathlib has no affine quasi-coherent → finite presentation cover lemma. -/
private theorem exists_finite_basicOpen_cover_le_quasicoherentData {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) :
    ∃ t : Finset R, Ideal.span (t : Set R) = ⊤ ∧
      ∀ r ∈ t, ∃ i, (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ q.X i := by
  classical
  set G : Set R := {r | ∃ i, (PrimeSpectrum.basicOpen r : (Spec R).Opens) ≤ q.X i} with hG
  have hspanG : Ideal.span G = ⊤ := by
    rw [← PrimeSpectrum.iSup_basicOpen_eq_top_iff']
    rw [eq_top_iff]
    intro x _
    simp only [TopologicalSpace.Opens.mem_iSup]
    obtain ⟨U, f, hf, hxU⟩ := q.coversTop ⊤ x (by trivial)
    rw [Sieve.mem_ofObjects_iff] at hf
    obtain ⟨i, ⟨hUi⟩⟩ := hf
    have hxXi : x ∈ q.X i := (leOfHom hUi) hxU
    obtain ⟨V, ⟨r, rfl⟩, hxV, hVle⟩ :=
      (TopologicalSpace.Opens.isBasis_iff_nbhd.mp PrimeSpectrum.isBasis_basic_opens) hxXi
    exact ⟨r, ⟨i, hVle⟩, hxV⟩
  obtain ⟨t, htsub, htspan⟩ := (Ideal.span_eq_top_iff_finite G).mp hspanG
  exact ⟨t, htspan, fun r hr => htsub hr⟩

/-! ## Supplementary results — the over-site ↔ open-subspace sheaf equivalence

The slice-to-geometric bridge that statement (`overRestrictIso`) rests on an
equivalence of *sheaf* categories
`Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology ↥U) A`
induced by the equivalence of underlying sites
`Opens.overEquivalence U : Over U ≌ Opens ↥U`. Mathlib carries `Opens.overEquivalence` but leaves
the *continuity* of its two functors and the induced sheaf-category equivalence as an explicit gap
(see `Mathlib/Topology/Sheaves/Over.lean`: "show that both functors of the equivalence
`overEquivalence U` are continuous and induce an equivalence between
`Sheaf ((Opens.grothendieckTopology X).over U) A` and `Sheaf (Opens.grothendieckTopology U) A`").

This section fills that gap. The two cover-lifting (`IsCocontinuous`) facts are the substance:
a sieve covers in the Grothendieck-topology-over-`U` exactly when its image under the slice
forgetful functor covers in the ambient space, and that condition matches the pointwise covering
condition on the open subspace `↥U` because `Subtype.val : ↥U → X` is an injective open embedding.
From the two cocontinuities, `Equivalence.isDenseSubsite_inverse_of_isCocontinuous` produces the
dense-subsite hypothesis and `Equivalence.sheafCongr` produces the sheaf equivalence.

It is the foundational (purely topological / topos-theoretic) layer of the slice-to-geometric
transport; the remaining steps toward `overRestrictIso` (identifying the sliced structure sheaf
`O_X.over U` with the open subscheme's structure sheaf `U.toScheme.ringCatSheaf` under this
equivalence, then lifting to sheaves of modules via `pushforwardPushforwardEquivalence` and
relating to `Scheme.Modules.restrictFunctor U.ι`) are the geometric layer above it. -/

section OverSiteSheafEquivalence

open TopologicalSpace Topology

variable {X : Type u} [TopologicalSpace X] (U : Opens X)

/-- The functor of `Opens.overEquivalence U` is cocontinuous (cover-lifting) from the
`U`-slice of the ambient Grothendieck topology to the Grothendieck topology of the open
subspace `↥U`. Foundational layer of the slice-to-geometric bridge `overRestrictIso`;
fills that gap. -/
private instance overEquivalence_functor_isCocontinuous :
    (Opens.overEquivalence U).functor.IsCocontinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) where
  cover_lift := by
    intro Y S hS
    rw [GrothendieckTopology.mem_over_iff]
    intro x hx
    have hxU : x ∈ U := leOfHom Y.hom hx
    have hmem : (⟨x, hxU⟩ : ↥U) ∈ (Opens.overEquivalence U).functor.obj Y := hx
    obtain ⟨V, h, hSh, hxV⟩ := hS ⟨x, hxU⟩ hmem
    have hVle : (V : Set ↥U) ⊆ Subtype.val ⁻¹' (Y.left : Set X) := leOfHom h
    set W : Opens X := ⟨Subtype.val '' (V : Set ↥U),
      (U.isOpenEmbedding'.isOpen_iff_image_isOpen).1 V.isOpen⟩ with hWdef
    have hWle : W ≤ Y.left := by
      rintro y ⟨z, hzV, rfl⟩
      exact hVle hzV
    refine ⟨W, homOfLE hWle, ?_, ⟨⟨x, hxU⟩, hxV, rfl⟩⟩
    rw [Sieve.overEquiv_iff]
    change S ((Opens.overEquivalence U).functor.map (Over.homMk (homOfLE hWle)))
    have hdomle :
        (Opens.overEquivalence U).functor.obj (Over.mk ((homOfLE hWle) ≫ Y.hom)) ≤ V := by
      intro z hz
      obtain ⟨z', hz'V, hz'eq⟩ := (hz : (z : X) ∈ (W : Set X))
      exact (Subtype.val_injective hz'eq) ▸ hz'V
    convert S.downward_closed hSh (homOfLE hdomle) using 1
    all_goals apply Subsingleton.elim

/-- The inverse of `Opens.overEquivalence U` is cocontinuous (cover-lifting) from the
Grothendieck topology of the open subspace `↥U` to the `U`-slice of the ambient Grothendieck
topology. Foundational layer of the slice-to-geometric bridge `overRestrictIso`;
fills that gap. -/
private instance overEquivalence_inverse_isCocontinuous :
    (Opens.overEquivalence U).inverse.IsCocontinuous
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) where
  cover_lift := by
    intro W S hS
    rw [GrothendieckTopology.mem_over_iff] at hS
    intro y hy
    have hpy : (y : X) ∈ ((Opens.overEquivalence U).inverse.obj W).left := ⟨y, hy, rfl⟩
    obtain ⟨P, f, hSf0, hpP⟩ := hS (y : X) hpy
    rw [Sieve.overEquiv_iff] at hSf0
    have hPle : (P : Set X) ⊆ ((Opens.overEquivalence U).inverse.obj W).left := leOfHom f
    set V : Opens ↥U :=
      ⟨Subtype.val ⁻¹' (P : Set X), P.isOpen.preimage continuous_subtype_val⟩ with hVdef
    have hVle : V ≤ W := by
      intro z hz
      obtain ⟨z', hz'W, hz'eq⟩ := hPle (hz : (z : X) ∈ (P : Set X))
      exact (Subtype.val_injective hz'eq) ▸ hz'W
    refine ⟨V, homOfLE hVle, ?_, hpP⟩
    change S ((Opens.overEquivalence U).inverse.map (homOfLE hVle))
    have hdomle : ((Opens.overEquivalence U).inverse.obj V).left ≤ P := by
      rintro p ⟨p', hp'V, rfl⟩
      exact hp'V
    convert S.downward_closed hSf0 (Over.homMk (homOfLE hdomle) ?_) using 1
    all_goals apply Subsingleton.elim

/-- The dense-subsite witness for the inverse of `Opens.overEquivalence U`, assembled from the two
cover-lifting facts above. Glue for `overEquivalence_sheafCongr`. -/
private instance overEquivalence_inverse_isDenseSubsite :
    (Opens.overEquivalence U).inverse.IsDenseSubsite
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) :=
  Equivalence.isDenseSubsite_inverse_of_isCocontinuous _ _ _

/-- The functor of `Opens.overEquivalence U` is continuous. Derived from the cocontinuity of the
inverse and the equivalence adjunction `inverse ⊣ functor`. Needed downstream of `overRestrictIso`
for `SheafOfModules.pushforwardPushforwardEquivalence`. -/
private instance overEquivalence_functor_isContinuous :
    (Opens.overEquivalence U).functor.IsContinuous
      ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) := by
  have : (Opens.overEquivalence U).symm.functor.IsCocontinuous
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) :=
    inferInstanceAs ((Opens.overEquivalence U).inverse.IsCocontinuous _ _)
  exact (Opens.overEquivalence U).symm.toAdjunction.isContinuous_of_isCocontinuous _ _

/-- The inverse of `Opens.overEquivalence U` is continuous. Derived from the cocontinuity of the
functor and the equivalence adjunction `functor ⊣ inverse`. Needed downstream of `overRestrictIso`
for `SheafOfModules.pushforwardPushforwardEquivalence`. -/
private instance overEquivalence_inverse_isContinuous :
    (Opens.overEquivalence U).inverse.IsContinuous
      (Opens.grothendieckTopology ↥U) ((Opens.grothendieckTopology X).over U) :=
  (Opens.overEquivalence U).toAdjunction.isContinuous_of_isCocontinuous _ _

/-- **The over-site ↔ open-subspace sheaf equivalence.** For a topological space `X`, an open
`U ⊆ X`, and any category `A`, the equivalence of sites
`Opens.overEquivalence U : Over U ≌ Opens ↥U`
lifts to an equivalence of sheaf categories
`Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology ↥U) A`.

This is exactly the equivalence that `Mathlib/Topology/Sheaves/Over.lean` leaves open. It is the
foundational layer of the slice-to-geometric bridge (`overRestrictIso`): once the sliced structure
sheaf `O_X.over U` is identified with the structure
sheaf of the open subscheme `U.toScheme` under this equivalence, a presentation of `M.over U`
transports (via `pushforwardPushforwardEquivalence` + `restrictFunctorIsoPullback`) to a geometric
presentation of `M|_U`. Mathlib supplies only the underlying site equivalence. -/
private noncomputable def overEquivalence_sheafCongr (A : Type*) [Category A] :
    Sheaf ((Opens.grothendieckTopology X).over U) A ≌ Sheaf (Opens.grothendieckTopology ↥U) A :=
  (Opens.overEquivalence U).sheafCongr
    ((Opens.grothendieckTopology X).over U) (Opens.grothendieckTopology ↥U) A

end OverSiteSheafEquivalence

/-! ## Supplementary results — the slice-to-geometric module bridge

This section builds the geometric layer of the slice-to-geometric bridge
that statement on top of the topological `overEquivalence_sheafCongr` of the previous
section. It identifies, on the level of *sheaves of modules*, the abstract Grothendieck-slice
restriction `M.over U` (a sheaf of modules over the sliced structure sheaf `O_X.over U` on the
slice site `J.over U`) with the geometric restriction `(restrictFunctor U.ι).obj M` on the small
Zariski site of the open subscheme `U.toScheme`.

The key structural facts, all holding *definitionally* at the pinned commit, are:
* `(Opens.overEquivalence U).inverse ⋙ Over.forget U = U.ι.opensFunctor` (`rfl`): the inverse leg
  of the site equivalence, post-composed with the slice-forgetful functor, is the opens functor of
  the open immersion `U.ι`;
* consequently `U.toScheme.ringCatSheaf = (overEquivalence_sheafCongr U RingCat).functor.obj
  (X.ringCatSheaf.over U)` (`rfl`): the structure sheaf of the open subscheme is the transport of
  the sliced structure sheaf across the ring-valued sheaf equivalence (this is *step 2*, the
  geometric ring-sheaf identification, discharged by `rfl`).

From these, `SheafOfModules.pushforwardPushforwardEquivalence` lifts the site equivalence to an
equivalence of categories of sheaves of modules (`overRestrictEquiv`, *step 3*), under whose
functor the sliced module `M.over U` corresponds to the geometric restriction
(`overRestrictIso`, *step 4*).

Mathlib (at the pinned commit) supplies only the underlying site equivalence and the
`pushforward`/`restrictFunctor` machinery; the assembly is -/

section OverRestrictBridge

open TopologicalSpace Topology

namespace Scheme.Modules

variable {X : Scheme.{u}} (U : X.Opens)

/-- **The slice-to-geometric equivalence of categories of sheaves of modules** (step 3).

For a scheme `X` and an open `U ⊆ X`, the category of sheaves of modules over the sliced structure
sheaf `O_X.over U` on the slice site `J.over U` is equivalent to the category `U.toScheme.Modules`
of sheaves of modules on the open subscheme `U.toScheme`. The equivalence is obtained by lifting
the topological site equivalence `Opens.overEquivalence U` (and its ring-valued sheaf congruence
`overEquivalence_sheafCongr`) to sheaves of modules via
`SheafOfModules.pushforwardPushforwardEquivalence`.

This is Mathlib's `AlgebraicGeometry.Scheme.Modules.overEquiv`; it is kept under a local name
only because the narrative of this file refers to it at some twenty use sites. -/
private noncomputable abbrev overRestrictEquiv :
    SheafOfModules.{u} (X.ringCatSheaf.over U) ≌ U.toScheme.Modules :=
  Scheme.Modules.overEquiv U

/-- The functor of `overRestrictEquiv`, with its codomain spelled
`SheafOfModules U.toScheme.ringCatSheaf` rather than `U.toScheme.Modules`.

`Scheme.Modules` is a `def` for `SheafOfModules` whose `Category` instance is a structure copy, so
the two spellings reach `Category` by different routes and typeclass resolution — which works at
reducible transparency — cannot identify them. Every declaration downstream that hands this functor
to `SheafOfModules.Presentation.map` or `.ofIsIso`, both of which are stated over
`SheafOfModules.{u} S`, uses this name, so the identification is performed once here, in term
position, instead of being asked of instance search at each site. -/
private noncomputable def overRestrictFunctor :
    SheafOfModules.{u} (X.ringCatSheaf.over U) ⥤ SheafOfModules.{u} U.toScheme.ringCatSheaf :=
  (overRestrictEquiv U).functor

/-- The slice-to-geometric functor preserves colimits, being one half of an equivalence. -/
private instance overRestrictFunctor_preservesColimitsOfSize :
    PreservesColimitsOfSize.{u, u} (overRestrictFunctor U) :=
  Adjunction.leftAdjoint_preservesColimits (overRestrictEquiv U).toAdjunction

/-- **Step-4 functor identification of the bridge.** The composite of `SheafOfModules.over · U`
with the slice-to-geometric equivalence `overRestrictEquiv U` is the geometric restriction functor
`restrictFunctor U.ι` along the open immersion `U.ι`. Both are pushforwards along the immersion's
opens functor (`(Opens.overEquivalence U).inverse ⋙ Over.forget U = U.ι.opensFunctor`, `rfl`); the
two ring-sheaf comparison morphisms agree, so the identification is `pushforwardComp` followed by
`pushforwardCongr`. -/
private noncomputable abbrev overRestrictFunctorIso :
    (SheafOfModules.pushforward (S := X.ringCatSheaf.over U) (𝟙 _)) ⋙
        (overRestrictEquiv U).functor ≅ restrictFunctor U.ι :=
  Scheme.Modules.overFunctorEquiv U

/-- **The slice-to-geometric isomorphism on an object** (step 4): for a sheaf of modules
`M` on `X`, the transport of the abstract Grothendieck-slice restriction `M.over U` under the
slice-to-geometric equivalence `overRestrictEquiv U` is canonically isomorphic to the geometric
restriction `(restrictFunctor U.ι).obj M`. This is the object-level form of
`overRestrictFunctorIso`; composed with `restrictFunctorIsoPullback` it lands the geometric
restriction as the pullback `U.ι^* M`. the load-bearing slice-touching ingredient of
the the affine case transport that statement. -/
private noncomputable def overRestrictIso (M : X.Modules) :
    (overRestrictFunctor U).obj (M.over U) ≅ (restrictFunctor U.ι).obj M :=
  (overRestrictFunctorIso U).app M

/-- **The slice-to-geometric isomorphism in pullback form** (the affine case, C, step 4'): the
transport of the
abstract Grothendieck-slice restriction `M.over U` under `overRestrictEquiv U` is canonically
isomorphic to the inverse-image (pullback) `U.ι^* M` of `M` along the open immersion `U.ι`. This is
`overRestrictIso` composed with Mathlib's `restrictFunctorIsoPullback`; it is the form a
presentation of `M.over U` transports into a presentation of the geometric pullback `U.ι^* M`. -/
private noncomputable def overRestrictPullbackIso (M : X.Modules) :
    @Iso (SheafOfModules.{u} U.toScheme.ringCatSheaf) _
      ((overRestrictFunctor U).obj (M.over U)) ((Scheme.Modules.pullback U.ι).obj M) :=
  overRestrictIso U M ≪≫ (restrictFunctorIsoPullback U.ι).app M

end Scheme.Modules

end OverRestrictBridge

/-! ## Supplementary results — slice-to-geometric presentation transport

This section builds the geometric milestone of the the affine case per-element transport
that statement : a `SheafOfModules.Presentation` of the
abstract Grothendieck-slice restriction `M.over U` is transported, across the slice-to-geometric
bridge `overRestrictPullbackIso`, into a `SheafOfModules.Presentation` of the *geometric*
restriction `(Scheme.Modules.pullback U.ι).obj M = U.ι^* M` on the open subscheme `U.toScheme`.

The load-bearing ingredient is the unit-iso `overRestrictUnitIso`: the slice-to-geometric
equivalence functor `(overRestrictEquiv U).functor` (definitionally a `SheafOfModules.pushforward`
along the equivalence-of-sites inverse with the *identity* ring comparison) sends the
private structure-sheaf module `unit` to `unit`. This is exactly the `F.obj (unit R) ≅ unit S`
datum that
`SheafOfModules.Presentation.map` consumes; once it is in hand, `Presentation.map` +
`Presentation.ofIsIso` (across `overRestrictPullbackIso`) realise the transport. The unit-iso rests
on the general fact `isIso_unitToPushforwardObjUnit_of_isIso'`: the canonical map
`unit S ⟶ (pushforward ψ).obj (unit R)` is an iso whenever the ring-sheaf comparison `ψ` is
(here `ψ = 𝟙`).

Mathlib (at the pinned commit) supplies `SheafOfModules.unitToPushforwardObjUnit` and proves it iso
only under a finality hypothesis on the site functor
(`Mathlib/Algebra/Category/ModuleCat/Sheaf/PullbackFree.lean`); the
`IsIso ψ ⟹ IsIso (unitToPushforwardObjUnit ψ)` route used here, and the slice transport, are -/

section SliceGeometricPresentation

open CategoryTheory Limits TopologicalSpace Topology

/-- **`unitToPushforwardObjUnit` is an isomorphism when the ring-sheaf comparison is.**

For a continuous functor `F` of sites and a morphism of ring sheaves
`ψ : S ⟶ (F.sheafPushforwardContinuous …).obj R` that is an isomorphism, the canonical map
`unitToPushforwardObjUnit ψ : unit S ⟶ (pushforward ψ).obj (unit R)` is an isomorphism. Its
component on each object is `(forget₂ RingCat AddCommGrpCat).map (ψ.hom.app _)`, iso as `ψ` is;
the conclusion follows by the reflect-isomorphism functors `SheafOfModules.toSheaf` and
`sheafToPresheaf` together with `NatTrans.isIso_iff_isIso_app`.

Mathlib proves `unitToPushforwardObjUnit` iso only under a finality hypothesis on `F`
(`SheafOfModules.PullbackFree`); this `IsIso ψ`-driven form is the one the slice-to-geometric
unit-iso `overRestrictUnitIso` consumes (with `ψ = 𝟙`). -/
private theorem isIso_unitToPushforwardObjUnit_of_isIso' {C : Type u} [Category.{u} C]
    {D : Type u} [Category.{u} D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D} {Fu : C ⥤ D}
    {S : Sheaf J RingCat.{u}} {Rr : Sheaf K RingCat.{u}} [Fu.IsContinuous J K]
    (ψ : S ⟶ (Fu.sheafPushforwardContinuous RingCat.{u} J K).obj Rr)
    [J.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    [K.HasSheafCompose (forget₂ RingCat.{u} AddCommGrpCat.{u})]
    (hψ : IsIso ψ) :
    IsIso (SheafOfModules.unitToPushforwardObjUnit ψ) := by
  have := hψ
  have hmap : IsIso ((sheafToPresheaf J RingCat).map ψ) := inferInstance
  rw [NatTrans.isIso_iff_isIso_app] at hmap
  rw [← isIso_iff_of_reflects_iso _ (SheafOfModules.toSheaf _)]
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf _ _)]
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  have hiso : IsIso (ψ.hom.app V) := hmap V
  have : IsIso ((forget₂ RingCat AddCommGrpCat).map (ψ.hom.app V)) := inferInstance
  exact this

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-- **The slice-to-geometric equivalence functor sends `unit` to `unit`**.

For an open `U ⊆ X`, the functor of the slice-to-geometric equivalence `overRestrictEquiv U`
(definitionally `SheafOfModules.pushforward` along `(Opens.overEquivalence U).inverse` with the
identity ring comparison) carries the sliced structure-sheaf module `unit (O_X.over U)` to the
private structure-sheaf module `unit (U.toScheme.ringCatSheaf)` of the open subscheme. This is the
`F.obj (unit R) ≅ unit S` datum consumed by `SheafOfModules.Presentation.map` in
`overRestrictPresentation`. -/
private noncomputable def overRestrictUnitIso (U : X.Opens) :
    (overRestrictFunctor U).obj (SheafOfModules.unit (X.ringCatSheaf.over U)) ≅
      SheafOfModules.unit U.toScheme.ringCatSheaf :=
  U.sheafOfModulesEquivOverUnit X.ringCatSheaf

/-- **Slice presentation ⟹ geometric-restriction presentation**.

Given a sheaf of modules `M` on `X`, an open `U ⊆ X`, and a `SheafOfModules.Presentation` of the
abstract Grothendieck-slice restriction `M.over U`, there is a `SheafOfModules.Presentation` of the
*geometric* restriction `(pullback U.ι).obj M = U.ι^* M` on the open subscheme `U.toScheme`. The
transport is `Presentation.map` along the slice-to-geometric equivalence functor (using the
unit-iso `overRestrictUnitIso`) followed by `Presentation.ofIsIso` across the bridge
`overRestrictPullbackIso`.

This closes the slice-touching step of the the affine case per-element transport
that statement : with `U = q.X i` and
`P = q.presentation i` it produces a global presentation of `U.ι^* M`; the remaining geometric step
restricts further to a basic affine `D(r) ≅ Spec R_r` and concludes via
`isIso_fromTildeΓ_of_presentation`. -/
private noncomputable def overRestrictPresentation (U : X.Opens) (M : X.Modules)
    (P : (M.over U).Presentation) : ((Scheme.Modules.pullback U.ι).obj M).Presentation :=
  -- `IsIso` is passed explicitly rather than searched for: the trace shows search reducing the
  -- goal to `IsIso (Iso.hom ?e)` and failing to assign `?e`, because `Iso`'s `Category` argument
  -- here and the one `ofIsIso` reconstructs are two routes to the same instance and assignment
  -- happens at reducible transparency.
  @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _ (overRestrictPullbackIso U M).hom
    (overRestrictPullbackIso U M).isIso_hom
    (SheafOfModules.Presentation.map.{u} P (overRestrictFunctor U) (overRestrictUnitIso U))

-- Reconstructing a global presentation expands the cover colimit and sheafification instances.
/-- **Geometric restriction to a cover member is globally presented**.

For a sheaf of modules `M` on `X` with quasi-coherence data `q` and an index `i`, the geometric
restriction `(pullback (q.X i).ι).obj M = (q.X i).ι^* M` of `M` to the open subscheme
`(q.X i).toScheme` admits a `SheafOfModules.Presentation`. It is `overRestrictPresentation` applied
to the slice presentation `q.presentation i : (M.over (q.X i)).Presentation` supplied by the
quasi-coherence datum.

This is the per-cover-member output that feeds the affine descent of the the affine case transport
that statement : for `D(r) ≤ q.X i` one further
restricts this
presentation to the basic affine `D(r) ≅ Spec R_r` and concludes via
`isIso_fromTildeΓ_of_presentation`. The heartbeat headroom tames the slice-site
`IsRightAdjoint`/`HasSheafify` synthesis blow-up that `Presentation.map` triggers across the
equivalence functor (the same `backward.isDefEq.respectTransparency false` incantation Mathlib's
own `QuasicoherentData.bind` uses). -/
private noncomputable def presentationPullbackιOfQuasicoherentData (M : X.Modules)
    (q : M.QuasicoherentData) (i : q.I) :
    ((Scheme.Modules.pullback (Scheme.Opens.ι (q.X i))).obj M).Presentation :=
  overRestrictPresentation (q.X i) M (q.presentation i)

end Scheme.Modules

end SliceGeometricPresentation

end AlgebraicGeometry
