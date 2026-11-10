module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic.PresentationDescent
import all StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic.PresentationDescent

/-!
# Pushforward of quasi-coherent modules: basic-open section localization

Part 3 of the proof of `AlgebraicGeometry.pushforward_isQuasicoherent`.

For a quasi-coherent sheaf of modules `M` on a scheme `X`, an affine open `U` and
`f : Γ(X, U)`, the section restriction `Γ(M, U) → Γ(M, X.basicOpen f)` is a localization at
`powers f`: first on `Spec R`, then on an arbitrary scheme through the pullback along
`hU.fromSpec`, which preserves quasi-coherence.

## Main definitions

* `AlgebraicGeometry.Scheme.Modules.restrictBasicOpenₗ`: the `Γ(X, U)`-linear section
  restriction `Γ(M, U) → Γ(M, X.basicOpen f)`.

## References

* [Stacks Project, Tag 01LC](https://stacks.math.columbia.edu/tag/01LC)
-/

@[expose] public section

open CategoryTheory
open AlgebraicGeometry

universe u


namespace AlgebraicGeometry

open CategoryTheory Limits

section BasicOpenPresentationDescent

open CategoryTheory Limits TopologicalSpace Topology

namespace Scheme.Modules

variable {X : Scheme.{u}}

/-! ## Supplementary results — Hfr: combined algebra transport

The two `IsLocalizedModule` bridges (I) `isLocalizedModule_of_ringEquiv_semilinear` and (II)
`isLocalizedModule_restrictScalars_powers_algebraMap` are chained into a single transport lemma:
the localization that the affine case (`IsIso fromTildeΓ`) produces on the slice `Spec R_r` (a
localization at
`powers f'` over the section ring `S`) is read back, across the `σ`-semilinear section isos and the
base change `R → A` (`A = R_r`), as a localization at `powers f` over the base ring `R`. -/

/-- **(I)+(II) combined: ring-iso-semilinear localization transport descending to the base ring.**

Given a base ring `R`, an `R`-algebra `A`, a ring iso `σ : S ≃+* A` carrying `f' : S` to
`algebraMap R A f`, a localization `g` at `powers f'` over `S`, two `σ`-semilinear additive
isomorphisms `e₁, e₂` onto `A`-modules (also `R`-modules via the scalar tower `R → A`), and an
`A`-linear map `h` intertwining `g` with the `eᵢ` (`h (e₁ x) = e₂ (g x)`), the restriction of
scalars of `h` to `R` is a localization at `powers f` over `R`.

This is the algebra core of the the affine case `Hfr` transport: bridge (I)
(`isLocalizedModule_of_ringEquiv_semilinear`) moves the localization across the ring iso to
`powers (algebraMap R A f)` over `A`, then bridge (II)
(`isLocalizedModule_restrictScalars_powers_algebraMap`) descends it to `powers f` over `R`. -/
@[ega "0 1.5.2" "special case"]
private theorem isLocalizedModule_powers_transport
    {R A S : Type*} [CommRing R] [CommRing A] [CommRing S] [Algebra R A]
    (σ : S ≃+* A) (f : R) (f' : S) (hf : σ f' = algebraMap R A f)
    {M₁ M₂ N₁ N₂ : Type*}
    [AddCommGroup M₁] [Module S M₁] [AddCommGroup M₂] [Module S M₂]
    [AddCommGroup N₁] [Module A N₁] [Module R N₁] [IsScalarTower R A N₁]
    [AddCommGroup N₂] [Module A N₂] [Module R N₂] [IsScalarTower R A N₂]
    (g : M₁ →ₗ[S] M₂) [IsLocalizedModule (Submonoid.powers f') g]
    (e₁ : M₁ ≃+ N₁) (e₂ : M₂ ≃+ N₂)
    (he₁ : ∀ (a : S) (x : M₁), e₁ (a • x) = σ a • e₁ x)
    (he₂ : ∀ (a : S) (x : M₂), e₂ (a • x) = σ a • e₂ x)
    (h : N₁ →ₗ[A] N₂)
    (hh : ∀ x, h (e₁ x) = e₂ (g x)) :
    IsLocalizedModule (Submonoid.powers f) (h.restrictScalars R) := by
  have hI : IsLocalizedModule ((Submonoid.powers f').map (σ : S →+* A)) h :=
    isLocalizedModule_of_ringEquiv_semilinear σ (Submonoid.powers f') g e₁ e₂ he₁ he₂ h hh
  have key : (Submonoid.powers f').map (σ : S →+* A) = Submonoid.powers (algebraMap R A f) := by
    rw [Submonoid.map_powers]
    exact congrArg Submonoid.powers hf
  rw [key] at hI
  have := hI
  exact isLocalizedModule_restrictScalars_powers_algebraMap f h

/-- **`IsIso M.fromTildeΓ` is invariant under isomorphism of modules.** If `M ≅ M'` as sheaves of
modules on `Spec R` and `M.fromTildeΓ` is an isomorphism, then so is `M'.fromTildeΓ`.

Immediate from `isIso_fromTildeΓ_iff`
(`IsIso M.fromTildeΓ ↔ M ∈ essImage (tilde.functor R)`) and the
fact that the essential image is closed under isomorphism (`Functor.essImage.ofIso`). This is the
transport that lets the affine `IsIso fromTildeΓ` for the iterated-pullback module
`(pullback isoSpec.inv).obj ((pullback ι_W).obj ((pullback ι).obj M))` be carried to the pullback
`(pullback j).obj M` along the single composite open immersion `j = isoSpec.inv ≫ ι_W ≫ ι` (which
is isomorphic to the iterated one via the `pullbackComp` coherences). -/
private theorem isIso_fromTildeΓ_of_iso {R : CommRingCat.{u}} {M M' : (Spec R).Modules}
    (e : M ≅ M') [IsIso M.fromTildeΓ] : IsIso M'.fromTildeΓ := by
  rw [isIso_fromTildeΓ_iff] at *
  exact Functor.essImage.ofIso e ‹_›

/-! ## Supplementary results — the affine case section-transport producer

The geometric producer chain manufacturing the basic-open `Hfr` datum from the per-element
transport. -/

/-- **Composite open immersion `j : Spec Γ(q.X i, ι⁻¹ᵁ D(s)) ⟶ Spec R`** identifying the affine
slice with the basic open `D(s)`.  It is `isoSpec.inv ≫ ι_W ≫ ι_{q.X i}` where
`W := ι_{q.X i}⁻¹ᵁ D(s)`; the domain is the genuine affine `Spec` of the slice's section ring.
the geometric backbone of the section-transport producer. -/
private noncomputable def compositeBasicOpenImmersion {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i) :
    Spec Γ(↑(q.X i), (Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)) ⟶ Spec R :=
  ((IsAffineOpen.Spec_basicOpen s).preimage_of_isOpenImmersion (Scheme.Opens.ι (q.X i))
      (by rwa [Scheme.Opens.opensRange_ι])).isoSpec.inv ≫
    Scheme.Opens.ι ((Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)) ≫
    Scheme.Opens.ι (q.X i)

/-- **(producer, a) `fromTildeΓ` iso of the composite-immersion pullback.** For a quasi-coherent
`M` on `Spec R` and a basic open `D(s) ≤ q.X i`, the pullback module `(pullback j).obj M` along the
composite immersion `j = compositeBasicOpenImmersion` has an isomorphism `fromTildeΓ` counit.

The geometric content is the affine keystone `isIso_fromTildeΓ_restrict_basicOpen`, which supplies
`IsIso fromTildeΓ` for the *iterated* pullback
`(pullback isoSpec.inv).obj ((pullback ι_W).obj ((pullback ι_{q.X i}).obj M))`; the iterated and
the composite pullbacks are identified by the `pullbackComp` pseudofunctor coherences, and
`isIso_fromTildeΓ_of_iso` transports the isomorphism across. the critical first
ingredient of the section-transport producer. -/
private theorem pullback_composite_immersion_isIso_fromTildeΓ {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i) :
    IsIso (@Scheme.Modules.fromTildeΓ
      (Γ(↑(q.X i), (Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)))
      ((Scheme.Modules.pullback (compositeBasicOpenImmersion M q s i hs)).obj M)) :=
  @isIso_fromTildeΓ_of_iso _ _ _
    ((Scheme.Modules.pullback (((IsAffineOpen.Spec_basicOpen s).preimage_of_isOpenImmersion
          (Scheme.Opens.ι (q.X i))
          (by rwa [Scheme.Opens.opensRange_ι])).isoSpec.inv)).mapIso
        ((Scheme.Modules.pullbackComp
          (Scheme.Opens.ι ((Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)))
          (Scheme.Opens.ι (q.X i))).app M) ≪≫
      (Scheme.Modules.pullbackComp
        (((IsAffineOpen.Spec_basicOpen s).preimage_of_isOpenImmersion (Scheme.Opens.ι (q.X i))
          (by rwa [Scheme.Opens.opensRange_ι])).isoSpec.inv)
        (Scheme.Opens.ι ((Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)) ≫
          Scheme.Opens.ι (q.X i))).app M)
    (isIso_fromTildeΓ_restrict_basicOpen M q s i hs)

/-- The composite immersion `j = compositeBasicOpenImmersion` is an open immersion (composite of an
iso and two open immersions). Needed for `.opensRange`, `''ᵁ`, and `gammaImageRingEquiv` on `j`. -/
private instance compositeBasicOpenImmersion_isOpenImmersion {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i) :
    IsOpenImmersion (compositeBasicOpenImmersion M q s i hs) := by
  unfold compositeBasicOpenImmersion
  infer_instance

/-- The image under `V.ι` of the preimage of an open contained in `V` is that open.

Both opens are variables on purpose. Applied at the call site to `q.X i` and
`PrimeSpectrum.basicOpen s`, the statement would carry two spellings that are only `delta`-apart —
`(Spec R).ringCatSheaf` is a `TopCat.Sheaf` where `SheafOfModules.QuasicoherentData` is indexed by
a `Sheaf (Opens.grothendieckTopology ↥(Spec R))`, and `PrimeSpectrum.basicOpen s` is an
`Opens (PrimeSpectrum ↑R)` where `V.ι ⁻¹ᵁ _` wants an `(Spec R).Opens`. Either one makes the goal
ill-typed at `implicit` transparency, and `rw` then reports `?f ''ᵁ ?f ⁻¹ᵁ ?U` as absent from a
goal that displays it. A statement in variables has neither. -/
private theorem image_preimage_of_le {Y : Scheme.{u}} (V W : Y.Opens) (h : W ≤ V) :
    V.ι ''ᵁ V.ι ⁻¹ᵁ W = W := by
  rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι]
  exact inf_eq_right.mpr h

/-- **(producer, b) Range of the composite immersion is `D(s)`.** The open range of
`j = compositeBasicOpenImmersion` is exactly the basic open `D(s)`: `isoSpec.inv` is an iso (its
range is `⊤`), so the range is `ι_{q.X i} ''ᵁ (ι_{q.X i}⁻¹ᵁ D(s)) = (q.X i) ⊓ D(s) = D(s)` using
`D(s) ≤ q.X i`.  image bookkeeping for the section-transport producer. -/
private theorem compositeBasicOpenImmersion_opensRange {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i) :
    (compositeBasicOpenImmersion M q s i hs).opensRange
      = (PrimeSpectrum.basicOpen s : (Spec R).Opens) := by
  unfold compositeBasicOpenImmersion
  rw [Scheme.Hom.opensRange_comp_of_isIso,
    Scheme.Hom.opensRange_comp, Scheme.Opens.opensRange_ι]
  exact image_preimage_of_le (q.X i) _ hs

/-! ## Supplementary results — the affine case section-transport producer (b-flocus/c/d/TOP)

The remaining producer chain assembling the basic-open `Hfr` datum (consumed by
`isLocalizedModule_basicOpen_descent_of_basicOpen_cover`) from the per-element transport
`pullback_composite_immersion_isIso_fromTildeΓ` via the algebra combiner
`isLocalizedModule_powers_transport`.   -/

/-- **Image of an affine basic open under an open immersion of affines.** For an open immersion
`j : Spec S ⟶ Spec R` and `f' : S`, the image `j ''ᵁ D(f')` is the `Spec R` scheme basic open of
the transported global section `(j.appIso ⊤).inv ((ΓSpecIso S).inv f')`.  Pure geometry:
`basicOpen_eq_of_affine` turns `D(f')` into the scheme basic open of a global structure section of
`Spec S`, and `Scheme.image_basicOpen` transports it across `j`.  Stated with `j` opaque so the
`rw` does not unfold a concrete composite immersion. -/
private theorem image_basicOpen_of_affine {S R : CommRingCat.{u}} (j : Spec S ⟶ Spec R)
    [IsOpenImmersion j] (f' : S) :
    j ''ᵁ (PrimeSpectrum.basicOpen f')
      = (Spec R).basicOpen ((j.appIso ⊤).inv ((Scheme.ΓSpecIso S).inv f')) := by
  rw [← basicOpen_eq_of_affine f', Scheme.image_basicOpen j ((Scheme.ΓSpecIso S).inv f')]

/- **(producer, b-flocus, image of a basic open).** The image under
`j = compositeBasicOpenImmersion`
of a basic open `D(f')` of the affine slice is the `Spec R` basic open of the transported section
`(j.appIso ⊤).inv ((ΓSpecIso _).inv f')`.  Instantiates `image_basicOpen_of_affine` at the concrete
composite immersion. -/
/-- **Image of an affine basic open as an intersection with the range.** If the appIso-transport of
`f'` agrees with the restriction to `j ''ᵁ ⊤` of a global section `g : Γ(Spec R, ⊤)`, then
`j ''ᵁ D(f') = (j ''ᵁ ⊤) ⊓ (Spec R).basicOpen g`.  Combines `image_basicOpen_of_affine` with the
private structure-sheaf identity `Scheme.basicOpen_res`. -/
private theorem image_basicOpen_eq_inf {S R : CommRingCat.{u}} (j : Spec S ⟶ Spec R)
    [IsOpenImmersion j] (f' : S) (g : Γ(Spec R, ⊤))
    (hfg : (j.appIso ⊤).inv ((Scheme.ΓSpecIso S).inv f')
        = (Spec R).presheaf.map (homOfLE (le_top : (j ''ᵁ ⊤) ≤ ⊤)).op g) :
    j ''ᵁ (PrimeSpectrum.basicOpen f') = (j ''ᵁ ⊤) ⊓ (Spec R).basicOpen g := by
  rw [image_basicOpen_of_affine, hfg, Scheme.basicOpen_res]

/-- **The `Γ(X,U)`-linear section restriction map of a sheaf of modules.** For `M : X.Modules` and
an inclusion of opens `i : V ⟶ U`, the presheaf restriction `Γ(M, U) → Γ(M, V)` is `Γ(X, U)`-linear
when `Γ(M, V)` carries the `Γ(X, U)`-module structure restricted along `X.presheaf.map i.op`
(`Module.compHom`). Linearity is `Scheme.Modules.map_smul`. the linear-map packaging
of the section restriction needed to state `IsLocalizedModule` for a general scheme (Mathlib's
presheaf-of-modules restriction is semilinear, not bundled this way). -/
private noncomputable def restrictₗ {X : Scheme.{u}} (M : X.Modules) {U V : X.Opens} (i : V ⟶ U) :
    letI : Module Γ(X, U) Γ(M, V) := Module.compHom _ (X.presheaf.map i.op).hom
    Γ(M, U) →ₗ[Γ(X, U)] Γ(M, V) :=
  letI : Module Γ(X, U) Γ(M, V) := Module.compHom _ (X.presheaf.map i.op).hom
  { toFun := fun x => M.presheaf.map i.op x
    map_add' := map_add _
    map_smul' := fun r x => Scheme.Modules.map_smul M i r x }

/-- **Basic-open section localization along an abstract affine open immersion.** For an open
immersion `j : Spec S ⟶ X` with the datum `IsIso (fromTildeΓ ((pullback j).obj M))`, a slice
element `f' : S`, and `f : Γ(X, j ''ᵁ ⊤)` with `σ f' = f`
(`σ = (ΓSpecIso S)⁻¹ ≫ gammaImageRingEquiv j ⊤`), the section restriction
`Γ(M, j ''ᵁ ⊤) → Γ(M, j ''ᵁ D(f'))` is `IsLocalizedModule (powers f)` over `Γ(X, j ''ᵁ ⊤)`.

The proof mirrors `section_localization_hfr_aux` but over an arbitrary ambient scheme `X` (so the
localization ring is the *local* section ring `A = Γ(X, j ''ᵁ ⊤)`, not a global `R`): the engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ` localizes the slice restriction `g` over `S`, the
`σ`-semilinear section comparisons `e₁, e₂` (`gammaPullbackImageIso`) intertwine `g` with the
`M`-side restriction `h = restrictₗ M ii`, and `isLocalizedModule_powers_transport` (with base
ring `R = A`, so the base change is trivial) transports the localization across `σ` to
`powers (σ f') = powers f`. -/
private theorem section_localization_hfr_aux_general {X : Scheme.{u}} {S : CommRingCat.{u}}
    (M : X.Modules) (j : Spec S ⟶ X) [IsOpenImmersion j]
    (hP1 : IsIso (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pullback j).obj M)))
    (f : Γ(X, j ''ᵁ (⊤ : (Spec S).Opens))) (f' : S)
    (hf' : (gammaImageRingEquiv j ⊤) ((Scheme.ΓSpecIso S).inv f') = f) :
    letI : Module Γ(X, j ''ᵁ (⊤ : (Spec S).Opens)) Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f')) :=
      Module.compHom _ (X.presheaf.map (j.opensFunctor.map (homOfLE le_top)).op).hom
    IsLocalizedModule (Submonoid.powers f)
      (show Γ(M, j ''ᵁ (⊤ : (Spec S).Opens)) →ₗ[Γ(X, j ''ᵁ (⊤ : (Spec S).Opens))]
          Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f')) from
        restrictₗ M (j.opensFunctor.map (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)))) := by
  let M' := (Scheme.Modules.pullback j).obj M
  have : IsIso (Scheme.Modules.fromTildeΓ M') := hP1
  let σ : (S : Type _) ≃+* (Γ(X, j ''ᵁ (⊤ : (Spec S).Opens)) : Type _) :=
    (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv.trans (gammaImageRingEquiv j ⊤)
  have hf : σ f' = algebraMap _ _ f := hf'
  let ii : (j ''ᵁ (PrimeSpectrum.basicOpen f') : X.Opens) ⟶ j ''ᵁ (⊤ : (Spec S).Opens) :=
    j.opensFunctor.map (homOfLE le_top)
  let iAN₂ : Module (Γ(X, j ''ᵁ (⊤ : (Spec S).Opens)) : Type _)
      (ToType Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f'))) :=
    Module.compHom _ (X.presheaf.map ii.op).hom
  let e₁ := (gammaPullbackImageIso j M ⊤).addCommGroupIsoToAddEquiv
  let e₂ := (gammaPullbackImageIso j M (PrimeSpectrum.basicOpen f')).addCommGroupIsoToAddEquiv
  let g := ((modulesSpecToSheaf.obj M').presheaf.map
    (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤)).op).hom
  have : IsLocalizedModule (Submonoid.powers f') g :=
    isLocalizedModule_restrict_of_isIso_fromTildeΓ M' f'
  let h : ToType Γ(M, j ''ᵁ (⊤ : (Spec S).Opens)) →ₗ[(Γ(X, j ''ᵁ (⊤ : (Spec S).Opens)) : Type _)]
      ToType Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f')) :=
    { toFun := fun m => (M.presheaf.map ii.op) m
      map_add' := fun x y => map_add _ x y
      map_smul' := fun a m => Scheme.Modules.map_smul M ii a m }
  have he₁ : ∀ (a : (S : Type _))
      (x : ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op ⊤))),
      e₁ (a • x) = σ a • e₁ x :=
    fun a x => gammaPullbackImageIso_hom_semilinear j M ⊤ ((Scheme.ΓSpecIso S).inv a) x
  have key0 := j.appIso_inv_naturality (U := (⊤ : (Spec S).Opens))
    (V := PrimeSpectrum.basicOpen f') (homOfLE le_top).op
  have he₂ : ∀ (a : (S : Type _))
      (x : ToType ((modulesSpecToSheaf.obj M').presheaf.obj (.op (PrimeSpectrum.basicOpen f')))),
      e₂ (a • x) = σ a • e₂ x := by
    intro a x
    have h1 := gammaPullbackImageIso_hom_semilinear j M (PrimeSpectrum.basicOpen f')
      ((Spec S).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso S).inv a)) x
    have key : (gammaImageRingEquiv j (PrimeSpectrum.basicOpen f'))
          ((Spec S).presheaf.map (homOfLE le_top).op ((Scheme.ΓSpecIso S).inv a))
        = (X.presheaf.map ii.op).hom (σ a) :=
      congrArg (fun φ => φ.hom ((Scheme.ΓSpecIso S).inv a)) key0
    exact h1.trans (congrArg (· • e₂ x) key)
  have hh : ∀ x, h (e₁ x) = e₂ (g x) := by
    intro x
    have hn := ConcreteCategory.congr_hom
      (gammaPullbackImageIso_hom_naturality j M
        (homOfLE (le_top : PrimeSpectrum.basicOpen f' ≤ ⊤))) x
    -- `exact` rather than `simp only [comp_apply] at hn`: `PrimeSpectrum.basicOpen f'` appears at
    -- `Opens (PrimeSpectrum ↑S)` where the presheaf wants `Opens ↥(Spec S)`, so `hn` is not
    -- type-correct at `implicit` transparency and `simp` refuses silently. The composition is
    -- unfolded by the final defeq check instead.
    exact hn.symm
  exact isLocalizedModule_powers_transport σ f f' hf g e₁ e₂ he₁ he₂ h hh

-- Large multi-step assembly (localization combiner + `eqToHom` open-transport); needs headroom.
/-- **(producer, TOP-aux) Basic-open `Hfr` along an abstract affine open immersion.**  For an open
immersion `j : Spec S ⟶ Spec R` with `IsIso (fromTildeΓ ((pullback j).obj M))` (the datum), a
ring element `f : R` and a slice element `f' : S` whose appIso-transport is the restriction of `f`
(`hf'`), and target opens `U = j ''ᵁ ⊤`, `V = j ''ᵁ D(f')`, the section restriction
`Γ(M, U) → Γ(M, V)` is `IsLocalizedModule (powers f)` over `R`.

The proof assembles the affine object-level `IsIso fromTildeΓ` into a section-level localization
via the algebra combiner `isLocalizedModule_powers_transport`: the engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ` localizes `Γ(M',⊤) → Γ(M', D(f'))` over the slice
ring `S`; the `σ`-semilinear section isos `e₁ = gammaPullbackImageIso ⊤`,
`e₂ = gammaPullbackImageIso D(f')` (over `σ = (ΓSpecIso S)⁻¹ ≪≫ gammaImageRingEquiv ⊤`) and the
restriction map `h` intertwine it, and the combiner descends the result to `powers f` over `R`.
Finally the `j ''ᵁ`-form opens are transported to `U` / `V` via `eT`, `eB`.  `j` is kept abstract
so the section-ring defeqs stay cheap.
the abstract core of the keystone `Hfr` producer. -/
private theorem section_localization_hfr_aux {R S : CommRingCat.{u}} (M : (Spec R).Modules)
    (j : Spec S ⟶ Spec R) [IsOpenImmersion j]
    (hP1 : IsIso (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pullback j).obj M)))
    (f : R) (f' : S) (U V : (Spec R).Opens) (hUV : V ≤ U)
    (eT : (j ''ᵁ (⊤ : (Spec S).Opens)) = U)
    (eB : (j ''ᵁ (PrimeSpectrum.basicOpen f')) = V)
    (hf' : (j.appIso ⊤).inv ((Scheme.ΓSpecIso S).inv f')
        = (Spec R).presheaf.map (homOfLE (le_top : (j ''ᵁ ⊤) ≤ ⊤)).op
            ((Scheme.ΓSpecIso R).inv f)) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE hUV).op).hom := by
  set A := Γ(Spec R, j ''ᵁ (⊤ : (Spec S).Opens)) with hA
  let _ : Algebra (R : Type _) (A : Type _) := RingHom.toAlgebra
    (((Spec R).presheaf.map (homOfLE (le_top : (j ''ᵁ ⊤) ≤ ⊤)).op).hom.comp
      (Scheme.ΓSpecIso R).inv.hom)
  let ii : (j ''ᵁ (PrimeSpectrum.basicOpen f') : (Spec R).Opens) ⟶ j ''ᵁ (⊤ : (Spec S).Opens) :=
    j.opensFunctor.map (homOfLE le_top)
  let _ : Module (A : Type _) (ToType Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f'))) :=
    Module.compHom _ ((Spec R).presheaf.map ii.op).hom
  let _ : Module (R : Type _) (ToType Γ(M, j ''ᵁ (⊤ : (Spec S).Opens))) :=
    Module.compHom _ (algebraMap (R : Type _) (A : Type _))
  let _ : Module (R : Type _) (ToType Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f'))) :=
    Module.compHom _ (algebraMap (R : Type _) (A : Type _))
  have : IsScalarTower (R : Type _) (A : Type _) (ToType Γ(M, j ''ᵁ (⊤ : (Spec S).Opens))) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : IsScalarTower (R : Type _) (A : Type _)
      (ToType Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f'))) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : IsLocalizedModule (Submonoid.powers (algebraMap (R : Type _) (A : Type _) f))
      (restrictₗ M ii) := section_localization_hfr_aux_general M j hP1 _ f' hf'
  have RESULT : IsLocalizedModule (Submonoid.powers f) ((restrictₗ M ii).restrictScalars R) :=
    isLocalizedModule_restrictScalars_powers_algebraMap f _
  -- transport the `j ''ᵁ`-form localization to the `D(s)` / `D(f) ⊓ D(s)` Hfr form
  -- the combiner's map is, by defeq, the `modulesSpecToSheaf` restriction along `ii`
  have RESULT' : IsLocalizedModule (Submonoid.powers f)
      (((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) := RESULT
  -- eqToHom open isos transporting `j ''ᵁ ⊤ → U` and `j ''ᵁ D(f') → V`
  have hUop : (Opposite.op U : (Spec R).Opensᵒᵖ)
      = Opposite.op (j ''ᵁ (⊤ : (Spec S).Opens)) := congrArg Opposite.op eT.symm
  have hVop : (Opposite.op V : (Spec R).Opensᵒᵖ)
      = Opposite.op (j ''ᵁ (PrimeSpectrum.basicOpen f')) := congrArg Opposite.op eB.symm
  let αU := (asIso ((modulesSpecToSheaf.obj M).presheaf.map (eqToHom hUop))).toLinearEquiv
  let αV := (asIso ((modulesSpecToSheaf.obj M).presheaf.map (eqToHom hVop))).toLinearEquiv
  have hRES := RESULT'
  have step1 : IsLocalizedModule (Submonoid.powers f)
      ((((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) ∘ₗ αU.toLinearMap) :=
    IsLocalizedModule.of_linearEquiv_right (S := Submonoid.powers f)
      (f := ((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) αU
  have hS1 := step1
  have step : IsLocalizedModule (Submonoid.powers f)
      (αV.symm.toLinearMap ∘ₗ
        ((((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) ∘ₗ αU.toLinearMap)) :=
    IsLocalizedModule.of_linearEquiv (S := Submonoid.powers f)
      (f := (((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) ∘ₗ αU.toLinearMap) αV.symm
  -- forward naturality square (uses only the forward eqToHom isos, both `rfl`-identified)
  have hsq : ((((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) ∘ₗ αU.toLinearMap)
      = (αV.toLinearMap ∘ₗ
          ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE hUV).op).hom) := by
    rw [show αU.toLinearMap = ((modulesSpecToSheaf.obj M).presheaf.map (eqToHom hUop)).hom from rfl,
      show αV.toLinearMap = ((modulesSpecToSheaf.obj M).presheaf.map (eqToHom hVop)).hom from rfl,
      ← ModuleCat.hom_comp, ← ModuleCat.hom_comp, ← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (fun m => ((modulesSpecToSheaf.obj M).presheaf.map m).hom)
      (Subsingleton.elim _ _)
  have hcancel : αV.symm.toLinearMap ∘ₗ αV.toLinearMap = LinearMap.id := by
    ext y
    simp
  -- the transported composite equals the Hfr restriction map
  have hcomp : ((modulesSpecToSheaf.obj M).presheaf.map (homOfLE hUV).op).hom
      = αV.symm.toLinearMap ∘ₗ
        ((((modulesSpecToSheaf.obj M).presheaf.map ii.op).hom) ∘ₗ αU.toLinearMap) := by
    rw [hsq, ← LinearMap.comp_assoc, hcancel, LinearMap.id_comp]
  rw [hcomp]
  exact step

/-- **(producer, TOP) Basic-open `Hfr` from the per-element transport.**  For a quasi-coherent
`M` on `Spec R`, a basic open `D(s) ≤ q.X i`, and `f : R`, the section restriction
`Γ(M, D(s)) → Γ(M, D(f) ⊓ D(s))` is `IsLocalizedModule (powers f)` over `R`.  This is the gated
basic-open `Hfr` datum consumed by `isLocalizedModule_basicOpen_descent_of_basicOpen_cover`.

Thin wrapper around `section_localization_hfr_aux`: it instantiates the abstract open immersion at
the concrete composite immersion `j = compositeBasicOpenImmersion`, supplies the datum
`pullback_composite_immersion_isIso_fromTildeΓ`, picks `f' = σ⁻¹(algebraMap R A f)` (so `hf'` is
`σ.apply_symm_apply`), and identifies the `j ''ᵁ`-form opens with `D(s)` (`opensRange`) and
`D(f) ⊓ D(s)` (`image_basicOpen_eq_inf`).  the geometric producer of the the affine case
keystone `Hfr`. -/
private theorem section_localization_hfr_basicOpen {R : CommRingCat.{u}}
    (M : (Spec R).Modules) (q : M.QuasicoherentData) (f s : R) (i : q.I)
    (hs : (PrimeSpectrum.basicOpen s : (Spec R).Opens) ≤ q.X i) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (inf_le_right : PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen s
          ≤ PrimeSpectrum.basicOpen s)).op).hom := by
  set S := Γ(↑(q.X i), (Scheme.Opens.ι (q.X i)) ⁻¹ᵁ (PrimeSpectrum.basicOpen s)) with hS
  set j := compositeBasicOpenImmersion M q s i hs with hj
  set A := Γ(Spec R, j ''ᵁ (⊤ : (Spec S).Opens)) with hA
  let algRA : (R : Type _) →+* (A : Type _) :=
    ((Spec R).presheaf.map (homOfLE (le_top : (j ''ᵁ ⊤) ≤ ⊤)).op).hom.comp
      (Scheme.ΓSpecIso R).inv.hom
  let instAlg : Algebra (R : Type _) (A : Type _) := RingHom.toAlgebra algRA
  let σ : (S : Type _) ≃+* (A : Type _) :=
    (Scheme.ΓSpecIso S).symm.commRingCatIsoToRingEquiv.trans (gammaImageRingEquiv j ⊤)
  let f' : (S : Type _) := σ.symm (algebraMap (R : Type _) (A : Type _) f)
  have hf' : (j.appIso ⊤).inv ((Scheme.ΓSpecIso S).inv f')
      = (Spec R).presheaf.map (homOfLE (le_top : (j ''ᵁ ⊤) ≤ ⊤)).op
          ((Scheme.ΓSpecIso R).inv f) := σ.apply_symm_apply _
  have eT : (j ''ᵁ (⊤ : (Spec S).Opens)) = PrimeSpectrum.basicOpen s :=
    (Scheme.Hom.image_top_eq_opensRange j).trans
      (compositeBasicOpenImmersion_opensRange M q s i hs)
  have eB : (j ''ᵁ (PrimeSpectrum.basicOpen f'))
      = PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen s := by
    rw [image_basicOpen_eq_inf j f' ((Scheme.ΓSpecIso R).inv f) hf', eT, basicOpen_eq_of_affine]
    exact inf_comm _ _
  exact section_localization_hfr_aux M j
    (pullback_composite_immersion_isIso_fromTildeΓ M q s i hs) f f'
    (PrimeSpectrum.basicOpen s) (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen s)
    inf_le_right eT eB hf'

/-! ## Supplementary results — the open-immersion case single-chart transport

The general-scheme keystone that statement
(`isLocalizedModule_basicOpen`): for a quasi-coherent sheaf of modules `M` on an *arbitrary* scheme
`X`, an affine open `U`, and `f : Γ(X, U)`, the section restriction `Γ(M, U) → Γ(M, D(f))` is
`IsLocalizedModule (powers f)` over `Γ(X, U)`.

It is the single-chart affine transport on top of the core construction: pull `M` back along the
affine immersion
`hU.fromSpec : Spec Γ(X, U) ⟶ X` (range `U`), so the pullback `M'` is quasi-coherent on
`Spec Γ(X, U)`, where the affine case gives `IsIso M'.fromTildeΓ`; the engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ` localizes the slice restriction over `Γ(X, U)`,
and the `σ`-semilinear section comparison `gammaPullbackImageIso` (bridge (I)
`isLocalizedModule_of_ringEquiv_semilinear`) transports it to the `M`-side restriction. No
cover-and-glue: `U` is already affine, so there is a single chart. -/

/-- **The `Γ(X,U)`-linear restriction of sections to a basic open `D(f)`** (`f : Γ(X, U)`). The
section restriction `Γ(M, U) → Γ(M, X.basicOpen f)` is `Γ(X, U)`-linear, where
`Γ(M, X.basicOpen f)` carries any `Γ(X, U)`-module structure compatible (via `IsScalarTower`)
with its native `Γ(X, X.basicOpen f)`-module structure and the canonical `Γ(X, U)`-algebra map
`Γ(X, U) → Γ(X, X.basicOpen f)` (the restriction `X.presheaf.map`). Linearity combines
`Scheme.Modules.map_smul` with the scalar tower. -/
noncomputable def restrictBasicOpenₗ {X : Scheme.{u}} (M : X.Modules) {U : X.Opens}
    (f : Γ(X, U))
    [Module Γ(X, U) Γ(M, X.basicOpen f)]
    [IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)] :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(M, X.basicOpen f) where
  toFun := fun x => M.presheaf.map (homOfLE (X.basicOpen_le f)).op x
  map_add' := map_add _
  map_smul' := fun r x => by
    change M.presheaf.map (homOfLE (X.basicOpen_le f)).op (r • x) = r • _
    rw [Scheme.Modules.map_smul M (homOfLE (X.basicOpen_le f)) r x,
      ← algebraMap_smul Γ(X, X.basicOpen f) r (M.presheaf.map (homOfLE (X.basicOpen_le f)).op x)]
    rfl

/-- **`fromSpec`-section coherence.** For an affine open `U` of a scheme `X`, the
`eqToHom`-transport `Γ(X, hU.fromSpec ''ᵁ ⊤) → Γ(X, U)` (along the equality
`hU.fromSpec ''ᵁ ⊤ = U`) equals the composite ring iso
`(hU.fromSpec.appIso ⊤).hom ≫ (ΓSpecIso Γ(X, U)).hom`. Equivalently, the section ring iso
`σ = (ΓSpecIso)⁻¹ ≫ gammaImageRingEquiv (fromSpec) ⊤` is, up to this `eqToHom` transport, the
identity. -/
private theorem fromSpec_image_top_section_coherence {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U)
    (eT : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U) :
    X.presheaf.map (eqToHom eT.symm).op
      = (hU.fromSpec.appIso (⊤ : (Spec Γ(X, U)).Opens)).hom ≫ (Scheme.ΓSpecIso Γ(X, U)).hom := by
  rw [← cancel_epi (X.presheaf.map (eqToHom eT).op),
    ← X.presheaf.map_comp, ← op_comp, eqToHom_trans, eqToHom_refl, op_id, X.presheaf.map_id]
  rw [Scheme.Hom.appIso_hom', Scheme.Hom.appLE]
  have hnat := hU.fromSpec.naturality (eqToHom eT).op
  simp only [Category.assoc]
  rw [reassoc_of% hnat, hU.fromSpec_app_self]
  simp only [eqToHom_unop, eqToHom_map, eqToHom_op]
  simp only [Category.assoc]
  rw [eqToHom_trans_assoc, ← eqToHom_map (Spec Γ(X, U)).presheaf,
    ← (Spec Γ(X, U)).presheaf.map_comp_assoc]
  · rw [Subsingleton.elim (eqToHom _ ≫ (homOfLE _).op)
      (𝟙 (Opposite.op (⊤ : (Spec Γ(X, U)).Opens))),
      (Spec Γ(X, U)).presheaf.map_id, Category.id_comp, Iso.inv_hom_id]
  · rw [eT, hU.fromSpec_preimage_self]

/-- **(keystone) Section-localization descent for quasi-coherent `M`.**  For a quasi-coherent
sheaf of modules `M` on `Spec R` and `f : R`, the global-to-`D(f)` section restriction
`Γ(M, ⊤) → Γ(M, D(f))` is `IsLocalizedModule (powers f)` over `R`.

Instantiates the cover-form descent `isLocalizedModule_basicOpen_descent_of_basicOpen_cover` at the
finite basic-open cover `exists_finite_basicOpen_cover_le_quasicoherentData` refining the
quasi-coherent data `q`, with the per-element basic-open `Hfr` supplied by the producer
`section_localization_hfr_basicOpen` (each cover overlap `D(s) ≤ D(r) ≤ q.X i` feeds the producer
at `i`).  the named keystone (Hartshorne II.5.3 / Stacks
`lemma-invert-f-sections`), built without the global affine `QCoh ≃ Mod` equivalence. -/
@[ega "III 1.2.2" "affine scheme X = Spec R"]
private theorem isLocalizedModule_basicOpen_descent {R : CommRingCat.{u}} (M : (Spec R).Modules)
    [hqc : M.IsQuasicoherent] (f : R) :
    IsLocalizedModule (Submonoid.powers f)
      ((modulesSpecToSheaf.obj M).presheaf.map
        (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)).op).hom := by
  obtain ⟨q⟩ := hqc.nonempty_quasicoherentData
  obtain ⟨t, hspan, hcov⟩ := exists_finite_basicOpen_cover_le_quasicoherentData M q
  refine isLocalizedModule_basicOpen_descent_of_basicOpen_cover M f t hspan ?_
  intro s hs_ex
  obtain ⟨r, hr, hsr⟩ := hs_ex
  obtain ⟨i, hri⟩ := hcov r hr
  exact section_localization_hfr_basicOpen M q f s i (le_trans hsr hri)

/- **Section-localization for a quasi-coherent sheaf on `Spec R`.** For a quasi-coherent sheaf of
modules `M` on `Spec R` and
`f : R`, the section restriction `Γ(M, ⊤) → Γ(M, D(f))` exhibits the target as the localized module
`(powers f)⁻¹ Γ(M, ⊤)`, i.e. it is `IsLocalizedModule (powers f)` over `R`.

This is the clean named form of the affine case's downstream corollary: the affine case
(`isIso_fromTildeΓ_of_isQuasicoherent`) makes `M.fromTildeΓ` an isomorphism, and the affine engine
`isLocalizedModule_restrict_of_isIso_fromTildeΓ` then delivers all three `IsLocalizedModule` fields
at once. Mathlib has no `QCoh(Spec R) → section-localization` bridge. It is the
affine `X = Spec R`, `U = ⊤` instance of the general-scheme keystone
`isLocalizedModule_basicOpen` (the open-immersion case). -/
-- The multi-step eqToHom open-transport + bridge-(I) ring-iso assembly needs heartbeat headroom.
/-- **** Basic-open section localization from the the core construction,
given the datum directly.  For a sheaf of modules `M` on a scheme `X`, an affine open `U`, the the
affine case
hypothesis `hP1 : IsIso (fromTildeΓ ((pullback hU.fromSpec).obj M))`, and `f : Γ(X, U)`, the
consumer-facing basic-open section restriction `restrictBasicOpenₗ M f` is
`IsLocalizedModule (powers f)` over `Γ(X, U)`.

This is the mechanical eqToHom bridge from `section_localization_hfr_aux_general` (instantiated at
the affine immersion `j = hU.fromSpec`, slice element `f' = f`, image section `f_im = σ f`) to
`restrictBasicOpenₗ`: the open identifications `j ''ᵁ ⊤ = U` (`eT`) and
`j ''ᵁ D(f) = X.basicOpen f` (`IsAffineOpen.fromSpec_image_basicOpen`) plus the section ring iso
`ρ = X.presheaf.map (eqToHom eT.symm).op : Γ(X, j ''ᵁ ⊤) ≃+* Γ(X, U)` transport the localization
across (bridge (I) `isLocalizedModule_of_ringEquiv_semilinear`), the only non-trivial coherence
being `ρ (σ f) = f`, supplied by the crux `fromSpec_image_top_section_coherence`.  :
separates the genuinely-new QC-pullback from the mechanical transport. -/
private theorem isLocalizedModule_basicOpen_of_hP1 {X : Scheme.{u}} (M : X.Modules)
    {U : X.Opens} (hU : IsAffineOpen U)
    (hP1 : IsIso (Scheme.Modules.fromTildeΓ ((Scheme.Modules.pullback hU.fromSpec).obj M)))
    (f : Γ(X, U))
    [Module Γ(X, U) Γ(M, X.basicOpen f)]
    [IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)] :
    IsLocalizedModule (Submonoid.powers f) (restrictBasicOpenₗ M f) := by
  set j := hU.fromSpec with hj
  have eT : (j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) = U :=
    (Scheme.Hom.image_top_eq_opensRange j).trans hU.opensRange_fromSpec
  have eB : (j ''ᵁ (PrimeSpectrum.basicOpen f)) = X.basicOpen f := hU.fromSpec_image_basicOpen f
  -- the image section `f_im = σ f` and the `hf'` discharge (rfl)
  set f_im : Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) :=
    (gammaImageRingEquiv j ⊤) ((Scheme.ΓSpecIso Γ(X, U)).inv f) with hf_im
  have hf' : (gammaImageRingEquiv j ⊤) ((Scheme.ΓSpecIso Γ(X, U)).inv f) = f_im := rfl
  -- `ii : j ''ᵁ D(f) ⟶ j ''ᵁ ⊤` and the core localization over `A = Γ(X, j ''ᵁ ⊤)`
  set ii : (j ''ᵁ (PrimeSpectrum.basicOpen f) : X.Opens) ⟶ j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) :=
    j.opensFunctor.map (homOfLE (le_top : PrimeSpectrum.basicOpen f ≤ ⊤)) with hii
  let : Module Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))
      Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f)) :=
    Module.compHom _ (X.presheaf.map ii.op).hom
  have core : IsLocalizedModule (Submonoid.powers f_im)
      (show Γ(M, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) →ₗ[Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))]
          Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f)) from restrictₗ M ii) :=
    section_localization_hfr_aux_general M j hP1 f_im f hf'
  -- the ring iso `ρ : Γ(X, j ''ᵁ ⊤) ≃+* Γ(X, U)`
  have : IsIso (X.presheaf.map (eqToHom eT.symm).op) := inferInstance
  set ρ : Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) ≃+* Γ(X, U) :=
    (asIso (X.presheaf.map (eqToHom eT.symm).op)).commRingCatIsoToRingEquiv with hρ
  -- `ρ (σ f) = f`, the crux coherence
  have hρf : ρ f_im = f := by
    have hcrux := fromSpec_image_top_section_coherence hU eT
    change (X.presheaf.map (eqToHom eT.symm).op).hom f_im = f
    rw [hcrux, hf_im, CommRingCat.comp_apply]
    change (Scheme.ΓSpecIso Γ(X, U)).hom.hom ((j.appIso ⊤).hom.hom
        ((j.appIso ⊤).inv.hom ((Scheme.ΓSpecIso Γ(X, U)).inv.hom f))) = f
    rw [Iso.inv_hom_id_apply, Iso.inv_hom_id_apply]
  -- additive isos `e₁ : Γ(M, j ''ᵁ ⊤) ≃+ Γ(M, U)`, `e₂ : Γ(M, j ''ᵁ D(f)) ≃+ Γ(M, X.basicOpen f)`
  have : IsIso (M.presheaf.map (eqToHom eT.symm).op) := inferInstance
  have : IsIso (M.presheaf.map (eqToHom eB.symm).op) := inferInstance
  set e₁ := (asIso (M.presheaf.map (eqToHom eT.symm).op)).addCommGroupIsoToAddEquiv with he₁def
  set e₂ := (asIso (M.presheaf.map (eqToHom eB.symm).op)).addCommGroupIsoToAddEquiv with he₂def
  -- semilinearity of `e₁`, `e₂` over `ρ`
  have he₁ : ∀ (a : Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)))
      (x : ToType Γ(M, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))),
      e₁ (a • x) = ρ a • e₁ x := by
    intro a x
    exact Scheme.Modules.map_smul M (eqToHom eT.symm) a x
  have he₂ : ∀ (a : Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)))
      (x : ToType Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f))),
      e₂ (a • x) = ρ a • e₂ x := by
    intro a x
    change (M.presheaf.map (eqToHom eB.symm).op).hom
        ((X.presheaf.map ii.op).hom a • x) = ρ a • e₂ x
    rw [Scheme.Modules.map_smul M (eqToHom eB.symm) ((X.presheaf.map ii.op).hom a) x,
      ← algebraMap_smul Γ(X, X.basicOpen f) (ρ a) (e₂ x)]
    refine congrArg (· • (e₂ x)) ?_
    change (X.presheaf.map (eqToHom eB.symm).op).hom ((X.presheaf.map ii.op).hom a)
      = (X.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom (ρ a)
    change ((X.presheaf.map ii.op) ≫ (X.presheaf.map (eqToHom eB.symm).op)).hom a
      = ((X.presheaf.map (eqToHom eT.symm).op) ≫
          (X.presheaf.map (homOfLE (X.basicOpen_le f)).op)).hom a
    rw [← X.presheaf.map_comp, ← X.presheaf.map_comp]
    exact congrArg (fun m => (X.presheaf.map m).hom a) (Subsingleton.elim _ _)
  -- the intertwining `restrictBasicOpenₗ M f (e₁ x) = e₂ (g x)`
  have hh : ∀ x, restrictBasicOpenₗ M f (e₁ x)
      = e₂ ((show Γ(M, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) →ₗ[Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))]
          Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f)) from restrictₗ M ii) x) := by
    intro x
    change (M.presheaf.map (homOfLE (X.basicOpen_le f)).op).hom
        ((M.presheaf.map (eqToHom eT.symm).op).hom x)
      = (M.presheaf.map (eqToHom eB.symm).op).hom ((M.presheaf.map ii.op).hom x)
    change ((M.presheaf.map (eqToHom eT.symm).op) ≫
          (M.presheaf.map (homOfLE (X.basicOpen_le f)).op)).hom x
      = ((M.presheaf.map ii.op) ≫ (M.presheaf.map (eqToHom eB.symm).op)).hom x
    rw [← M.presheaf.map_comp, ← M.presheaf.map_comp]
    exact congrArg (fun m => (M.presheaf.map m).hom x) (Subsingleton.elim _ _)
  -- assemble bridge (I)
  have := core
  exact isLocalizedModule_powers_transport ρ f f_im hρf
    (show Γ(M, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens)) →ₗ[Γ(X, j ''ᵁ (⊤ : (Spec Γ(X, U)).Opens))]
          Γ(M, j ''ᵁ (PrimeSpectrum.basicOpen f)) from restrictₗ M ii)
    e₁ e₂ he₁ he₂ (restrictBasicOpenₗ M f) hh

/-! ## Supplementary results — pullback of QC along an open immersion

Route-1 chain L1–L6 building `isQuasicoherent_pullback_fromSpec`: the pullback of a quasi-coherent
sheaf of modules along the affine immersion `hU.fromSpec : Spec Γ(X, U) → X` is again
quasi-coherent.
This is the QC-pullback input the the open-immersion case final close `isLocalizedModule_basicOpen`
feeds to the affine case
(`isIso_fromTildeΓ_of_isQuasicoherent`). -/

/-- The inverse of `overRestrictEquiv`, with its domain spelled
`SheafOfModules V.toScheme.ringCatSheaf`. The companion of `overRestrictFunctor`, and named for
the same reason. -/
private noncomputable def overRestrictFunctorInv (V : X.Opens) :
    SheafOfModules.{u} V.toScheme.ringCatSheaf ⥤ SheafOfModules.{u} (X.ringCatSheaf.over V) :=
  (overRestrictEquiv V).inverse

/-- The inverse slice-to-geometric functor preserves colimits, being one half of an
equivalence. -/
private instance overRestrictFunctorInv_preservesColimitsOfSize (V : X.Opens) :
    PreservesColimitsOfSize.{u, u} (overRestrictFunctorInv V) :=
  Adjunction.leftAdjoint_preservesColimits (overRestrictEquiv V).symm.toAdjunction

/-- **The inverse slice-equivalence functor sends `unit` to `unit`.**
Dual to `overRestrictUnitIso`: the inverse functor of `overRestrictEquiv V` carries the
private structure-sheaf (unit) module of the open subscheme `V.toScheme` to the unit module of the
over-site `X.ringCatSheaf.over V`. Built by transport across the equivalence: apply the inverse
functor to `(overRestrictUnitIso V).symm`, then collapse the `functor ⋙ inverse` round trip via the
unit isomorphism of the equivalence. This avoids the `unitToPushforwardObjUnit`/`IsContinuous`
coercion friction of a direct construction. -/
private noncomputable def overRestrictUnitIsoInv (V : X.Opens) :
    (overRestrictFunctorInv V).obj (SheafOfModules.unit V.toScheme.ringCatSheaf) ≅
      SheafOfModules.unit (X.ringCatSheaf.over V) :=
  V.sheafOfModulesEquivOverInverseUnit X.ringCatSheaf

/-- **Geometric presentation back-transported to a slice presentation.**
Dual to `overRestrictPresentation`: a presentation of the geometric pullback `(V.ι^*) M` yields a
presentation of the abstract Grothendieck slice `M.over V`. Transport the given presentation across
`(overRestrictPullbackIso V M).inv` (`Presentation.ofIsIso`), `Presentation.map` along the inverse
slice-equivalence functor (using `overRestrictUnitIsoInv V`), then collapse the round trip
across the
equivalence unit iso. -/
private noncomputable def overRestrictPresentationInv (V : X.Opens) (M : X.Modules)
    (P : ((Scheme.Modules.pullback V.ι).obj M).Presentation) : (M.over V).Presentation :=
  SheafOfModules.Presentation.ofIsIso.{u}
    ((overRestrictEquiv V).unitIso.symm.app (M.over V)).hom
    (SheafOfModules.Presentation.map.{u}
      (@SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
        (overRestrictPullbackIso V M).inv (overRestrictPullbackIso V M).isIso_inv P)
      (overRestrictFunctorInv V) (overRestrictUnitIsoInv V).symm)

/-- The opens functor of an open immersion is `Final`: it is a right adjoint, the underlying map
being open. -/
private instance final_opensMap_of_isOpenImmersion {A B : Scheme.{u}} (k : A ⟶ B)
    [IsOpenImmersion k] : (Opens.map k.base).Final :=
  haveI : (Opens.map k.base).IsRightAdjoint :=
    k.isOpenEmbedding.isOpenMap.adjunction.isRightAdjoint
  inferInstance

/-- The comparison out of the pullback of the unit module along an open immersion is an
isomorphism. Restated from `SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal` for the same
reason as `isIso_pullbackObjUnitToUnit_schemeIso`. -/
private instance isIso_pullbackObjUnitToUnit_openImmersion {A B : Scheme.{u}} (k : A ⟶ B)
    [IsOpenImmersion k] :
    IsIso (SheafOfModules.pullbackObjUnitToUnit (k.toRingCatSheafHom)) :=
  SheafOfModules.instIsIsoPullbackObjUnitToUnitOfFinal _

/-- **Pullback along an open immersion sends `unit` to `unit`.**
For an open immersion `k : A ⟶ B`, the pullback functor `pullback k` carries the structure-sheaf
(unit) module of `B` to that of `A`. The canonical comparison `pullbackObjUnitToUnit` is an iso
because the site functor `Opens.map k.base` is `Final` — it is a right adjoint, since `k.base` is
an open map (`IsOpenMap.adjunction`). -/
private noncomputable def pullbackOpenImmersionUnitIso {A B : Scheme.{u}} (k : A ⟶ B)
    [IsOpenImmersion k] :
    (pullbackFunctor k).obj (SheafOfModules.unit B.ringCatSheaf) ≅
      SheafOfModules.unit A.ringCatSheaf :=
  @asIso _ _ _ _ (SheafOfModules.pullbackObjUnitToUnit (k.toRingCatSheafHom))
    (isIso_pullbackObjUnitToUnit_openImmersion k)

/-- **Pseudofunctoriality iso for the preimage square.**
For an open immersion `g : Y ⟶ X`, `M` on `X`, and `U ⊆ X`, the induced open immersion
`k := g.resLE U (g ⁻¹ᵁ U)` (with `k ≫ U.ι = (g ⁻¹ᵁ U).ι ≫ g`) gives, by pseudofunctoriality of
pullback (`pullbackComp` / `pullbackCongr`), a natural iso
`(pullback k).obj ((pullback U.ι).obj M) ≅ (pullback (g ⁻¹ᵁ U).ι).obj ((pullback g).obj M)`. -/
private noncomputable def pullbackPreimageιIso {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (M : X.Modules) (U : X.Opens) :
    (Scheme.Modules.pullback (g.resLE U (g ⁻¹ᵁ U) le_rfl)).obj
        ((Scheme.Modules.pullback U.ι).obj M) ≅
      (Scheme.Modules.pullback (Scheme.Opens.ι (g ⁻¹ᵁ U))).obj
        ((Scheme.Modules.pullback g).obj M) :=
  (Scheme.Modules.pullbackComp (g.resLE U (g ⁻¹ᵁ U) le_rfl) U.ι).app M ≪≫
    (Scheme.Modules.pullbackCongr
      (Scheme.Hom.resLE_comp_ι g (U := U) (V := g ⁻¹ᵁ U) le_rfl)).app M ≪≫
    ((Scheme.Modules.pullbackComp (Scheme.Opens.ι (g ⁻¹ᵁ U)) g).app M).symm

-- Transporting the presentation across the pseudofunctoriality isomorphism unfolds two
-- pullbacks and an open immersion together.
-- Heartbeat headroom for the slice-site presentation transport, as elsewhere in this file.
-- Instance search runs over that same transported presentation.
/-- **Presentation of the pullback's restriction to a preimage cover member.**
For an open immersion `g : Y ⟶ X`, `M` quasi-coherent with datum `q`, and index `i`, the geometric
restriction `(W_i.ι^*) ((pullback g).obj M)` of `N := (pullback g).obj M` to the preimage
`W_i := g ⁻¹ᵁ (q.X i)` admits a presentation. Build it by mapping the global presentation
`presentationPullbackιOfQuasicoherentData M q i` of `(q.X i).ι^* M` along the pullback
of the induced
open immersion `k := g.resLE (q.X i) W_i` (unit datum `pullbackOpenImmersionUnitIso`), then
transporting across the pseudofunctoriality iso `pullbackPreimageιIso`. -/
private noncomputable def presentationPullbackιPreimage {Y : Scheme.{u}} (g : Y ⟶ X)
    [IsOpenImmersion g]
    (M : X.Modules) (q : M.QuasicoherentData) (i : q.I) :
    ((Scheme.Modules.pullback (Scheme.Opens.ι (g ⁻¹ᵁ (q.X i)))).obj
        ((Scheme.Modules.pullback g).obj M)).Presentation :=
  haveI hk : IsOpenImmersion (g.resLE (q.X i) (g ⁻¹ᵁ (q.X i)) le_rfl) := by
    delta Scheme.Hom.resLE; infer_instance
  @SheafOfModules.Presentation.ofIsIso _ _ _ _ _ _ _ _
    (pullbackPreimageιIso g M (q.X i)).hom (pullbackPreimageιIso g M (q.X i)).isIso_hom
    (SheafOfModules.Presentation.map.{u}
      (presentationPullbackιOfQuasicoherentData M q i)
      (pullbackFunctor (g.resLE (q.X i) (g ⁻¹ᵁ (q.X i)) le_rfl))
      (pullbackOpenImmersionUnitIso (g.resLE (q.X i) (g ⁻¹ᵁ (q.X i)) le_rfl)).symm)

-- Feeding the transported presentation through the slice back-transport re-elaborates it.
-- Instance search runs over the result of that back-transport.
/-- **The pulled-back sheaf is quasi-coherent on each preimage cover member.**
For an open immersion `g : Y ⟶ X`, `M` quasi-coherent with datum `q`, and index `i`, the abstract
Grothendieck slice `((pullback g).obj M).over (g ⁻¹ᵁ (q.X i))` is quasi-coherent: feed the
geometric presentation `presentationPullbackιPreimage` into the geometric→slice back-transport
`overRestrictPresentationInv` and apply `Presentation.isQuasicoherent`. -/
private theorem isQuasicoherent_over_preimage {Y : Scheme.{u}} (g : Y ⟶ X) [IsOpenImmersion g]
    (M : X.Modules) (q : M.QuasicoherentData) (i : q.I) :
    (((Scheme.Modules.pullback g).obj M).over (g ⁻¹ᵁ (q.X i))).IsQuasicoherent :=
  (overRestrictPresentationInv (g ⁻¹ᵁ (q.X i)) ((Scheme.Modules.pullback g).obj M)
    (presentationPullbackιPreimage g M q i)).isQuasicoherent

/-- **The preimage family of a quasi-coherence cover covers the source.**
For a morphism `g : Y ⟶ X` and quasi-coherence datum `q` for `M` on `X` (whose cover
`{q.X i}` covers
`X`), the preimage family `{g ⁻¹ᵁ (q.X i)}` covers `Y`. Direct from the opens-topology covering
characterization: any `y ∈ W` has `g y ∈ q.X i` for some `i` (since `{q.X i}` covers `⊤`), so
`W ⊓ g ⁻¹ᵁ (q.X i)` is a neighbourhood of `y` in the sieve. -/
private theorem coversTop_preimage {Y : Scheme.{u}} (g : Y ⟶ X)
    (M : X.Modules) (q : M.QuasicoherentData) :
    (Opens.grothendieckTopology ↥Y).CoversTop (fun i => g ⁻¹ᵁ (q.X i)) := by
  intro W' y hy
  obtain ⟨U_X, _fX, hsieve, hgyU⟩ := q.coversTop ⊤ (g.base y) (by trivial)
  rw [Sieve.mem_ofObjects_iff] at hsieve
  obtain ⟨i, ⟨hUi⟩⟩ := hsieve
  refine ⟨W' ⊓ (g ⁻¹ᵁ (q.X i)), homOfLE inf_le_left, ?_, hy, ?_⟩
  · rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨homOfLE inf_le_right⟩⟩
  · change g.base y ∈ q.X i
    exact leOfHom hUi hgyU

-- Heartbeat headroom for the slice-site `of_coversTop` `bind` synthesis.
/-- **Quasi-coherence is preserved under pullback along `fromSpec`.**
For `M` quasi-coherent on `X` and an affine open `U`, the pullback of `M` along the affine
immersion `hU.fromSpec : Spec Γ(X, U) ⟶ X` is quasi-coherent. -/
private theorem isQuasicoherent_pullback_fromSpec (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) :
    ((Scheme.Modules.pullback hU.fromSpec).obj M).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback_of_isOpenImmersion
      hU.fromSpec M

/-- **the open-immersion case keystone : basic-open section localization for
a quasi-coherent sheaf on an arbitrary scheme.** For `M` quasi-coherent on `X`, an affine open `U`,
and `f : Γ(X, U)`, the section restriction `Γ(M, U) → Γ(M, X.basicOpen f)` is
`IsLocalizedModule (powers f)` over `Γ(X, U)`. Assembles the QC-pullback → the affine case
(`isIso_fromTildeΓ_of_isQuasicoherent`) → the eqToHom
bridge. closes the open-immersion case. -/
@[ega "III 1.2.2" "special case"]
private theorem isLocalizedModule_basicOpen (M : X.Modules) [M.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    [Module Γ(X, U) Γ(M, X.basicOpen f)]
    [IsScalarTower Γ(X, U) Γ(X, X.basicOpen f) Γ(M, X.basicOpen f)] :
    IsLocalizedModule (Submonoid.powers f) (restrictBasicOpenₗ M f) :=
  have := isQuasicoherent_pullback_fromSpec M hU
  isLocalizedModule_basicOpen_of_hP1 M hU
    (isIso_fromTildeΓ_of_isQuasicoherent ((Scheme.Modules.pullback hU.fromSpec).obj M)) f

end Scheme.Modules

end BasicOpenPresentationDescent

end AlgebraicGeometry
