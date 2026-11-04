module

public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.PullbackSection
public import StacksFrontier.AlgebraicGeometry.FlatBaseChangeCohomology.AffineDegreeZero.Modules
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AmpleFibreTwistStalkVanishing
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientSections
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.InfinitesimalBaseIdealSections
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctions
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.StalkFormalFunctionsFrom02O8
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionFullyFaithful.SectionsComplete
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualBijective

/-!
# Tag 0D2M

[Stacks, Tag 0D2M] concerns a proper morphism `f : X ⟶ Y` with `Y` Noetherian, an invertible
`𝒪_X`-module `ℒ`, a coherent `𝒪_X`-module `ℱ` and a point `y ∈ Y` at which `ℒ_y` is ample on the
fibre `X_y`; it produces a `d₀` such that for all `d ≥ d₀`

1. `R ᵖ f_*(ℱ ⊗ ℒ ^⊗ d)_y = 0` for every `p > 0`, and
2. `f_*(ℱ ⊗ ℒ ^⊗ d)_y ⟶ H ⁰(X_y, ℱ_y ⊗ ℒ_y ^⊗ d)` is surjective.

The first clause is
`StacksFrontier/AlgebraicGeometry/FormalFunctions/AmpleFibreTwistStalkVanishing.lean`. This file
supplies the second and states the tag.

## Main definitions

* `Stacks.FormalFunctions.fiberSectionsStalkHom` — **the map of the tag's second display**: the
  canonical `(f_* ℳ)_y ⟶ Γ(X_y, (f.fiberι y) ^* ℳ)`, sending the germ at `y` of a section over
  `f ⁻¹ U` to its restriction to the fibre. It exists for every `f`, with no hypothesis, because
  the fibre lies over every open neighbourhood of `y`.
* `Stacks.FormalFunctions.fiberTwistSectionsStalkHom` — the same map read in the fibre twist
  `ℱ_y ⊗ ℒ_y ^⊗ d`, through [Stacks, Tag 0EGK].
* `Stacks.FormalFunctions.fiberToStalkBaseChange` — the fibre as a closed subscheme of
  `X' = X ×_Y Spec 𝒪_{Y,y}`, namely `V(𝔪_y 𝒪_{X'})`.

## Main results

* `Stacks.FormalFunctions.exists_isZero_stalk_rightDerived_and_surjective_fiberTwist` —
  **[Stacks, Tag 0D2M]**, both clauses, at the tag's own hypotheses, the second clause into
  `H ⁰(X_y, ℱ_y ⊗ ℒ_y ^⊗ d)`.
* `Stacks.FormalFunctions.exists_isZero_stalk_rightDerived_and_surjective_twistModule` — the same
  with the second clause into the restriction of `ℱ ⊗ ℒ ^⊗ d` to the fibre.
* `Stacks.FormalFunctions.surjective_fiberSectionsStalkHom` — the second clause, from the
  surjectivity of the adic quotient projection on the base change.
* `Stacks.FormalFunctions.exists_pullbackSection_stalkBaseChangeι_eq` — **degree-zero flat base
  change at a stalk, elementwise**: every section of `q ^* ℳ` on `X'` is the restriction of a
  section of `ℳ` over `f ⁻¹ V` for some `V ∋ y`.
* `Stacks.FormalFunctions.exists_pullbackSection_fromSpecStalk_eq` — every section of
  `(Y.fromSpecStalk y) ^* ℱ` is pulled back from a neighbourhood of `y`. No hypothesis on `Y`.
* `Stacks.FormalFunctions.baseChangeNatTrans_val_app_top_pullbackSection` — the normalisation of
  the canonical base-change morphism on a section taken over a *neighbourhood* of a point of the
  base, which is the form a germ argument needs.

## Implementation notes

The chain of the surjectivity clause, read from the fibre end, with `X' = X ×_Y Spec 𝒪_{Y,y}`,
`q : X' ⟶ X` the projection and `ℳ = ℱ ⊗ ℒ ^⊗ d`:

1. `Stacks.FormalFunctions.exists_subsingleton_and_surjective_twistModule_stalkBaseChange` gives
   the surjectivity of `H ⁰(X', q ^* ℳ) ⟶ H ⁰(X', q ^* ℳ / 𝔪_y q ^* ℳ)` — the local-base form of
   the tag, transported to `X'`.
2. Degree-zero derived global sections *are* global sections, so that is the surjectivity of the
   quotient projection on sections (`surjective_app_top_of_surjective_adicCohomologyProj`).
3. [Stacks, Tag 0EL1] (`Stacks.Algebraization.idealQuotientPushforwardIso`) identifies
   `q ^* ℳ / 𝔪_y q ^* ℳ` with the direct image of the restriction of `q ^* ℳ` to
   `V(𝔪_y 𝒪_{X'})`, compatibly with the projection and the adjunction unit; so restriction of
   sections to that closed subscheme is surjective. Degree zero throughout, so
   `Γ(X', i_* 𝒩) = Γ(V(𝔪_y 𝒪_{X'}), 𝒩)` holds definitionally and [Stacks, Tag 01E8] is not
   needed.
4. `Stacks.FormalFunctions.fiberIsoInfinitesimalBaseIdealSubschemePow` identifies the fibre with
   `V(𝔪_y 𝒪_{X'})`, and restriction of sections along an isomorphism of schemes is bijective.
5. Degree-zero flat base change along `Spec 𝒪_{Y,y} ⟶ Y` — [Stacks, Tag 02KH] part (1) at
   `i = 0`, `…FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`, for the *canonical*
   morphism — identifies `Γ(X', q ^* ℳ)` with `Γ(Spec 𝒪_{Y,y}, (Y.fromSpecStalk y) ^* f_* ℳ)`,
   and the latter consists of pullbacks of sections of `f_* ℳ` over neighbourhoods of `y`.

Every identification in that chain is the canonical one, as it must be: the conclusion is the
surjectivity of a *named* map, and unlike the vanishing clause it cannot be transported along a
merely existential isomorphism.

Two things make the chain go through without heavy bookkeeping. The elementwise formulation —
"every section is the restriction of a section over some `f ⁻¹ V`" rather than "this composite of
isomorphisms is that map" — means no square has to be proved to commute: the maps are composed on
elements. And step 5 is stated at a *general* open `V ∋ y`, which is what
`baseChangeNatTrans_val_app_top_pullbackSection` adds to the existing normalisation at `⊤`; the
localisation step that produces the open is
`exists_pullbackSection_fromSpecStalk_eq`, which inverts a function with invertible germ by
realising the inverse germ on a smaller neighbourhood, so no basic open and no
`IsLocalization` instance on the stalk is needed downstream.

`Stacks.FormalFunctions.exists_pullbackSection_eq_of_comp_eq` presents the inclusion of the fibre
as a *variable* morphism `w` together with an equality `fiberToStalkBaseChange f y ≫ q = w`, and
substitutes it away at the start of the proof. That is not cosmetic: transporting a section along
`Scheme.Modules.pullbackCongr`, which is an `eqToIso` of functors, forces the kernel to unfold
`Scheme.Modules.pullback` at the two concrete pullback schemes and does not terminate within the
default budget. With the equality substituted the transport never appears.

## References

* [Stacks Project, Tag 0D2M](https://stacks.math.columbia.edu/tag/0D2M)
* [Stacks Project, Tag 02KH](https://stacks.math.columbia.edu/tag/02KH)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EGK](https://stacks.math.columbia.edu/tag/0EGK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

open Stacks.AlgebraicGeometry.AffinePushforward (baseChangeNatTrans pushforwardSquareIso)
open Stacks.AlgebraicGeometry.IdealPower (idealPowerMultiple)
open Stacks.AlgebraicGeometry.RelativeProjChain (isIso_pullbackPushforwardAdjunction_unit_app)
open Stacks.AlgebraicGeometry.SectionsBaseChange (le_preimage_top)
open Stacks.Algebraization (idealPowerQuotient idealQuotientPushforwardIso
  idealQuotientPushforwardMap_π sectionsEquivOfIso)
open Stacks.Cohomology.FormalFunctions (adicCohomologyProj baseIdealSheaf
  moduleGlobalSectionsRightDerivedZeroIso)
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence (pullbackTwistModuleIso twistModule)
open Stacks.Ample (IsAmple IsInvertibleModule tensorPowModule)
open Stacks.AmpleLocallyClosed (pullbackModule)

universe u

namespace Stacks.FormalFunctions

/-! ### The base-change morphism on sections pulled back from a neighbourhood -/

section Normalisation

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {f' : X' ⟶ S'} {g : S' ⟶ S} {g' : X' ⟶ X}

/-- **The comparison of the two composite direct images disappears after restriction to the whole
of `X'`.** On sections over an open `U` of the base the comparison is transport along the equality
of opens `(f' ≫ g) ⁻¹ᵁ U = (g' ≫ f) ⁻¹ᵁ U`, and the opens of a scheme form a thin category, so
composing it with a restriction gives the restriction from the other open. -/
public theorem pushforwardSquareIso_val_app_res (w : g' ≫ f = f' ≫ g) (N : X'.Modules)
    (U : S.Opens) (hU : (⊤ : S'.Opens) ≤ g ⁻¹ᵁ U) (hU' : (⊤ : X'.Opens) ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U))
    (b : N.val.obj (op ((g' ≫ f) ⁻¹ᵁ U))) :
    ((Scheme.Modules.pushforward f').obj N).val.map (homOfLE hU).op
        (((pushforwardSquareIso w).hom.app N).val.app (op U) b) =
      N.val.map (homOfLE hU').op b := by
  have E : (f' ≫ g) ⁻¹ᵁ U = (g' ≫ f) ⁻¹ᵁ U := congrArg (fun φ : X' ⟶ S => φ ⁻¹ᵁ U) w.symm
  have h0 : ((pushforwardSquareIso w).hom.app N).val.app (op U) b =
      N.val.map (eqToHom E).op b := rfl
  have h1 : ((Scheme.Modules.pushforward f').obj N).val.map (homOfLE hU).op
        (N.val.map (eqToHom E).op b) =
      N.val.map ((Opens.map f'.base).map (homOfLE hU)).op (N.val.map (eqToHom E).op b) := rfl
  rw [h0, h1]
  exact (PresheafOfModules.map_comp_apply N.val (eqToHom E).op
      ((Opens.map f'.base).map (homOfLE hU)).op b).symm.trans
    (PresheafOfModules.congr_map_apply N.val (Subsingleton.elim _ _) b)

/-- **The base-change morphism carries the pullback of a section over a neighbourhood of the base
to the pullback of that same section.** This is the normalisation
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.baseChangeNatTrans_app_top_pullbackUnitSections`
with the section taken over an arbitrary open `U` of `S` rather than over the whole of `S`, and
both sides read over the whole of `X'`.

It is what identifies `Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` as the
canonical comparison at a *germ*: the sections a germ at a point of `S` is built from live over a
neighbourhood of that point and not over `S`, so the form at `⊤` cannot see them. -/
public theorem baseChangeNatTrans_val_app_top_pullbackSection (w : g' ≫ f = f' ≫ g)
    (F : X.Modules) (U : S.Opens) (hU : (⊤ : S'.Opens) ≤ g ⁻¹ᵁ U)
    (hU' : (⊤ : X'.Opens) ≤ g' ⁻¹ᵁ (f ⁻¹ᵁ U)) (a : F.val.obj (op (f ⁻¹ᵁ U))) :
    ((baseChangeNatTrans w).app F).val.app (op (⊤ : S'.Opens))
        (Scheme.Modules.pullbackSection g ((Scheme.Modules.pushforward f).obj F) U ⊤ hU a) =
      Scheme.Modules.pullbackSection g' F (f ⁻¹ᵁ U) ⊤ hU' a := by
  set s := ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
    ((Scheme.Modules.pushforward f).obj F)).val.app (op U) a with hs
  set u := ((Scheme.Modules.pullbackPushforwardAdjunction g').unit.app F).val.app
    (op (f ⁻¹ᵁ U)) a with hu
  have hmate : ((baseChangeNatTrans w).app F).val.app (op (g ⁻¹ᵁ U)) s =
      ((pushforwardSquareIso w).hom.app ((Scheme.Modules.pullback g').obj F)).val.app (op U) u :=
    (congrArg (fun t : (Scheme.Modules.pushforward f).obj F ⟶
        (Scheme.Modules.pushforward g).obj ((Scheme.Modules.pushforward f').obj
          ((Scheme.Modules.pullback g').obj F)) => t.val.app (op U) a)
      (Stacks.AlgebraicGeometry.ModuleBaseChange.unit_baseChangeNatTrans w F)).symm
  have hnat := PresheafOfModules.naturality_apply ((baseChangeNatTrans w).app F).val
    (homOfLE hU).op s
  have hsrc : Scheme.Modules.pullbackSection g ((Scheme.Modules.pushforward f).obj F) U ⊤ hU a =
      ((Scheme.Modules.pushforward f ⋙ Scheme.Modules.pullback g).obj F).val.map
        (homOfLE hU).op s := rfl
  rw [hsrc, hnat, hmate]
  exact pushforwardSquareIso_val_app_res w ((Scheme.Modules.pullback g').obj F) U hU hU' u

end Normalisation

/-! ### Sections over the spectrum of a stalk come from a neighbourhood -/

section FromSpecStalk

/-- **Every section of `(Y.fromSpecStalk y)^* ℱ` is the pullback of a section of `ℱ` over an open
neighbourhood of `y`.** Equivalently: the canonical map `ℱ_y ⟶ Γ(Spec 𝒪_{Y,y}, g^* ℱ)` out of the
stalk is surjective — indeed it is the isomorphism of
`AlgebraicGeometry.exists_fromSpecStalkSectionsStalkLinearEquiv`, but only the surjectivity is
stated here, and in the elementwise form a germ argument consumes.

The proof is the localisation statement. Over an affine open `U ∋ y` the sections of the pullback
are the localisation of `Γ(ℱ, U)` at the prime of `y`
(`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_pullbackSectionₗ` together with
`AlgebraicGeometry.isLocalization_sections_fromSpecStalk`), so `s • z` is the pullback of a
section `a` over `U` for some `s ∉ 𝔭`. Such an `s` has invertible germ at `y`, hence pulls back to
a unit of `Γ(Spec 𝒪_{Y,y}, 𝒪)`; the inverse of that unit is itself the germ of a function `s'` on
some neighbourhood `V ∋ y`, and `s' · a` on `U ⊓ V` pulls back to `z`. No basic open is needed:
the inverse is produced in the stalk and then realised on a neighbourhood. -/
public theorem exists_pullbackSection_fromSpecStalk_eq {Y : Scheme.{u}} (ℱ : Y.Modules)
    [ℱ.IsQuasicoherent] (y : Y)
    (z : Γ((Scheme.Modules.pullback (Y.fromSpecStalk y)).obj ℱ, ⊤)) :
    ∃ (V : Y.Opens) (hy : y ∈ V) (b : Γ(ℱ, V)),
      Scheme.Modules.pullbackSection (Y.fromSpecStalk y) ℱ V ⊤
        (le_preimage_fromSpecStalk_of_mem y V hy) b = z := by
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (x := y) (U := ⊤)
    (TopologicalSpace.Opens.mem_top y)
  let := Scheme.Modules.pullbackSectionsModule (Y.fromSpecStalk y) ℱ U ⊤
    (le_preimage_fromSpecStalk_of_mem y U hyU)
  have := Scheme.Modules.isLocalizedModule_pullbackSectionₗ (Y.fromSpecStalk y) ℱ hU
    (isAffineOpen_top (Spec (Y.presheaf.stalk y))) (le_preimage_fromSpecStalk_of_mem y U hyU)
    (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl (isLocalization_sections_fromSpecStalk y hU hyU)
  obtain ⟨⟨a, s⟩, hsz⟩ := IsLocalizedModule.surj
    (hU.primeIdealOf ⟨y, hyU⟩).asIdeal.primeCompl
    (Scheme.Modules.pullbackSectionₗ (Y.fromSpecStalk y) ℱ U ⊤
      (le_preimage_fromSpecStalk_of_mem y U hyU)) z
  let : Algebra Γ(Y, U) (Y.presheaf.stalk y) := (Y.presheaf.germ U y hyU).hom.toAlgebra
  have : IsLocalization.AtPrime (Y.presheaf.stalk y) (hU.primeIdealOf ⟨y, hyU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨y, hyU⟩
  have hunit : IsUnit (((Y.fromSpecStalk y).appLE U ⊤
      (le_preimage_fromSpecStalk_of_mem y U hyU)).hom s.1) := by
    rw [fromSpecStalk_appLE_top_apply]
    exact ((IsLocalization.AtPrime.isUnit_to_map_iff (Y.presheaf.stalk y)
      (hU.primeIdealOf ⟨y, hyU⟩).asIdeal s.1).mpr s.2).map
        (Scheme.ΓSpecIso (Y.presheaf.stalk y)).inv.hom
  obtain ⟨v, hv⟩ := hunit
  obtain ⟨V, hyV, s', hs'⟩ := TopCat.Presheaf.exists_germ_eq Y.presheaf
    ((Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom.hom (↑v⁻¹))
  have hinv : ((Y.fromSpecStalk y).appLE V ⊤
        (le_preimage_fromSpecStalk_of_mem y V hyV)).hom s' =
      ↑v⁻¹ := by
    rw [fromSpecStalk_appLE_top_apply y hyV s', hs']
    exact ConcreteCategory.congr_hom (Scheme.ΓSpecIso (Y.presheaf.stalk y)).hom_inv_id _
  refine ⟨U ⊓ V, ⟨hyU, hyV⟩,
    (Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom s' •
      (ℱ.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) a, ?_⟩
  have h1 := pullbackSectionHom_smul (Y.fromSpecStalk y) ℱ (U ⊓ V) ⊤
    (le_preimage_fromSpecStalk_of_mem y (U ⊓ V) ⟨hyU, hyV⟩)
    ((Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom s')
    ((ℱ.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) a)
  have h2 := pullbackSectionHom_map (Y.fromSpecStalk y) ℱ U (U ⊓ V)
    (inf_le_left : U ⊓ V ≤ U) ⊤ (le_preimage_fromSpecStalk_of_mem y (U ⊓ V) ⟨hyU, hyV⟩)
    (le_preimage_fromSpecStalk_of_mem y U hyU) a
  have h2' : pullbackSectionHom (Y.fromSpecStalk y) ℱ (U ⊓ V) ⊤
        (le_preimage_fromSpecStalk_of_mem y (U ⊓ V) ⟨hyU, hyV⟩)
        ((ℱ.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) a) =
      pullbackSectionHom (Y.fromSpecStalk y) ℱ U ⊤
        (le_preimage_fromSpecStalk_of_mem y U hyU) a := h2
  have h3 : ((Y.fromSpecStalk y).appLE (U ⊓ V) ⊤
        (le_preimage_fromSpecStalk_of_mem y (U ⊓ V) ⟨hyU, hyV⟩)).hom
      ((Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom s') =
      ((Y.fromSpecStalk y).appLE V ⊤ (le_preimage_fromSpecStalk_of_mem y V hyV)).hom s' := by
    rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]
  have hz : v.val • z = pullbackSectionHom (Y.fromSpecStalk y) ℱ U ⊤
      (le_preimage_fromSpecStalk_of_mem y U hyU) a := by
    rw [hv]; exact hsz
  change pullbackSectionHom (Y.fromSpecStalk y) ℱ (U ⊓ V) ⊤
      (le_preimage_fromSpecStalk_of_mem y (U ⊓ V) ⟨hyU, hyV⟩)
      ((Y.presheaf.map (homOfLE (inf_le_right : U ⊓ V ≤ V)).op).hom s' •
        (ℱ.presheaf.map (homOfLE (inf_le_left : U ⊓ V ≤ U)).op) a) = z
  rw [h1, h3, hinv, h2', ← hz, smul_smul, Units.inv_mul, one_smul]

end FromSpecStalk

/-! ### Surjectivity of pulling sections back -/

section Surjectivity

/-- **Surjectivity of pulling sections back composes.** If every section of `r ^* M` over `W` is
pulled back from a section of `M` over `U`, and every section of `p ^* (r ^* M)` over `V` is
pulled back from one of `r ^* M` over `W`, then every section of `(p ≫ r) ^* M` over `V` is pulled
back from one of `M` over `U`: the comparison of the iterated pullback with the pullback along the
composite is an isomorphism, so it is surjective on sections. -/
public theorem exists_pullbackSection_comp {A B C : Scheme.{u}} (p : A ⟶ B) (r : B ⟶ C)
    (M : C.Modules) (U : C.Opens) (W : B.Opens) (V : A.Opens)
    (hr : W ≤ r ⁻¹ᵁ U) (hp : V ≤ p ⁻¹ᵁ W) (h : V ≤ (p ≫ r) ⁻¹ᵁ U)
    (h1 : ∀ s : Γ((Scheme.Modules.pullback r).obj M, W),
      ∃ a : Γ(M, U), Scheme.Modules.pullbackSection r M U W hr a = s)
    (h2 : ∀ t : Γ((Scheme.Modules.pullback p).obj ((Scheme.Modules.pullback r).obj M), V),
      ∃ s : Γ((Scheme.Modules.pullback r).obj M, W),
        Scheme.Modules.pullbackSection p ((Scheme.Modules.pullback r).obj M) W V hp s = t)
    (t : Γ((Scheme.Modules.pullback (p ≫ r)).obj M, V)) :
    ∃ a : Γ(M, U), Scheme.Modules.pullbackSection (p ≫ r) M U V h a = t := by
  obtain ⟨t', ht'⟩ := (sectionsEquivOfIso
    ((Scheme.Modules.pullbackComp p r).app M) V).surjective t
  obtain ⟨s, hs⟩ := h2 t'
  obtain ⟨a, ha⟩ := h1 s
  refine ⟨a, ?_⟩
  rw [← Scheme.Modules.pullbackSection_comp p r M U W V hr hp h a, ha, hs]
  exact ht'

/-- **Pulling sections back along an isomorphism of schemes is surjective** (indeed bijective) on
global sections: the unit of the adjunction is an isomorphism there,
`Stacks.RelativeProj.isIso_pullbackPushforwardAdjunction_unit_app`. -/
public theorem exists_pullbackSection_top_of_isIso {A B : Scheme.{u}} (p : A ⟶ B) [IsIso p]
    (N : B.Modules) (h : (⊤ : A.Opens) ≤ p ⁻¹ᵁ (⊤ : B.Opens))
    (t : Γ((Scheme.Modules.pullback p).obj N, ⊤)) :
    ∃ s : Γ(N, ⊤), Scheme.Modules.pullbackSection p N ⊤ ⊤ h s = t := by
  have := isIso_pullbackPushforwardAdjunction_unit_app p N
  obtain ⟨s, hs⟩ := (sectionsEquivOfIso
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction p).unit.app N)) ⊤).surjective t
  exact ⟨s, (Scheme.Modules.pullbackSection_top p N h s).trans hs⟩

/-- **Restricting sections to a closed subscheme cut out by `I ^ n` is surjective as soon as the
quotient projection `M ⟶ M / I ^ n M` is surjective on global sections.** The two differ by the
isomorphism `M / I ^ n M ≅ v_* v ^* M` of [Stacks, Tag 0EL1]
(`idealQuotientPushforwardIso`), which is normalised by the adjunction unit,
and the unit on global sections is exactly the pullback of a section. -/
public theorem exists_pullbackSection_top_of_surjective_cokernel_π {W : Scheme.{u}}
    (I : W.IdealSheafData) (n : ℕ) (M : W.Modules) [M.IsQuasicoherent]
    {Z : Scheme.{u}} (v : Z ⟶ W) [IsClosedImmersion v] (hv : Scheme.Hom.ker v = I ^ n)
    (hπ : Function.Surjective ((cokernel.π (C := W.Modules)
      (idealPowerMultiple I n M).ι).app (⊤ : W.Opens)))
    (h : (⊤ : Z.Opens) ≤ v ⁻¹ᵁ (⊤ : W.Opens))
    (t : Γ((Scheme.Modules.pullback v).obj M, ⊤)) :
    ∃ m : Γ(M, ⊤), Scheme.Modules.pullbackSection v M ⊤ ⊤ h m = t := by
  obtain ⟨c, hc⟩ := (sectionsEquivOfIso
    (idealQuotientPushforwardIso I n M v hv) ⊤).surjective t
  obtain ⟨m, hm⟩ := hπ c
  refine ⟨m, ?_⟩
  have hkey := congrArg (fun φ : M ⟶ (Scheme.Modules.pushforward v).obj
      ((Scheme.Modules.pullback v).obj M) => φ.val.app (op (⊤ : W.Opens)) m)
    (idealQuotientPushforwardMap_π I n M v hv)
  refine (Scheme.Modules.pullbackSection_top v M h m).trans (hkey.symm.trans (Eq.trans ?_ hc))
  exact congrArg (fun z => (idealQuotientPushforwardIso I n M v hv).hom.app (⊤ : W.Opens) z) hm

/-- **Surjectivity of pulling sections back is transported along an isomorphism of modules.** -/
public theorem exists_pullbackSection_of_iso {A B : Scheme.{u}} (k : B ⟶ A) {M N : A.Modules}
    (θ : M ≅ N) (U : A.Opens) (V : B.Opens) (h : V ≤ k ⁻¹ᵁ U)
    (hN : ∀ t : Γ((Scheme.Modules.pullback k).obj N, V),
      ∃ a : Γ(N, U), Scheme.Modules.pullbackSection k N U V h a = t)
    (t : Γ((Scheme.Modules.pullback k).obj M, V)) :
    ∃ a : Γ(M, U), Scheme.Modules.pullbackSection k M U V h a = t := by
  obtain ⟨a, ha⟩ := hN (sectionsEquivOfIso
    ((Scheme.Modules.pullback k).mapIso θ) V t)
  refine ⟨θ.inv.app U a, ?_⟩
  refine (sectionsEquivOfIso
    ((Scheme.Modules.pullback k).mapIso θ) V).injective ?_
  refine Eq.trans ?_ ha
  refine (Scheme.Modules.pullbackSection_naturality k θ.hom U V h (θ.inv.app U a)).trans ?_
  exact congrArg (fun z => Scheme.Modules.pullbackSection k N U V h z)
    (congrArg (fun χ : N ⟶ N => Scheme.Modules.Hom.app χ U a) θ.inv_hom_id)

/-- **The quotient projection `M ⟶ M / I ^ n M` is surjective on global sections as soon as
`H ⁰(X, M) ⟶ H ⁰(X, M / I ^ n M)` is.** Degree-zero derived global sections *are* global sections
(`moduleGlobalSectionsRightDerivedZeroIso`), and under that
identification `H ⁰(φ)` is `φ` on sections, by naturality of that isomorphism. -/
public theorem surjective_app_top_of_surjective_adicCohomologyProj {A : Type u} [CommRing A]
    {W : Scheme.{u}} (fw : W ⟶ Spec (.of A)) (J : Ideal A) (M : W.Modules) (n : ℕ)
    (hs : Function.Surjective
      (adicCohomologyProj A fw J M 0 n)) :
    Function.Surjective ((cokernel.π (C := W.Modules)
      (idealPowerMultiple
        (baseIdealSheaf A J fw) n M).ι).app (⊤ : W.Opens)) := by
  intro b
  obtain ⟨x', hx'⟩ := (ConcreteCategory.bijective_of_isIso
    ((moduleGlobalSectionsRightDerivedZeroIso W).hom.app
      (idealPowerQuotient
        (baseIdealSheaf A J fw) n M))).surjective b
  obtain ⟨x, hx⟩ := hs x'
  refine ⟨(moduleGlobalSectionsRightDerivedZeroIso W).hom.app
    M x, ?_⟩
  have hnat := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
    ((moduleGlobalSectionsRightDerivedZeroIso W).hom.naturality
      (cokernel.π (C := W.Modules) (idealPowerMultiple (baseIdealSheaf A J fw) n M).ι))) x
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp] at hnat
  refine hnat.symm.trans ?_
  exact (congrArg (fun z => (moduleGlobalSectionsRightDerivedZeroIso W).hom.app
    (idealPowerQuotient (baseIdealSheaf A J fw) n M) z) hx).trans hx'

end Surjectivity

/-! ### Sections of the pullback to the base change come from a neighbourhood -/

section BaseChange

variable {X Y : Scheme.{u}}

/-- **Every section of `q ^* G` on `X' = X ×_Y Spec 𝒪_{Y,y}` is pulled back from a section of `G`
over `f ⁻¹ V` for some open neighbourhood `V` of `y`**, `q : X' ⟶ X` being the projection.

This is the degree-zero flat base change of [Stacks, Tag 02KH] part (1) along the flat morphism
`Spec 𝒪_{Y,y} ⟶ Y`, read on elements: the canonical comparison
`Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans` is an isomorphism
(`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat`), so every
section of `q ^* G` comes from a section of `g ^* f_* G` over `Spec 𝒪_{Y,y}`, which by
`Stacks.FormalFunctions.exists_pullbackSection_fromSpecStalk_eq` is the pullback of a section of
`f_* G` over a neighbourhood of `y`; and the comparison carries that pullback to the pullback
along `q` of the very same section, which is
`Stacks.FormalFunctions.baseChangeNatTrans_val_app_top_pullbackSection`. -/
public theorem exists_pullbackSection_stalkBaseChangeι_eq (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (y : Y) (G : X.Modules) [G.IsQuasicoherent]
    (t : Γ((Scheme.Modules.pullback (stalkBaseChangeι f y)).obj G, ⊤)) :
    ∃ (V : Y.Opens) (hy : y ∈ V) (a : Γ(G, f ⁻¹ᵁ V)),
      Scheme.Modules.pullbackSection (stalkBaseChangeι f y) G (f ⁻¹ᵁ V) ⊤
        (top_le_preimage_stalkBaseChangeι f y V hy) a = t := by
  have : Flat (Y.fromSpecStalk y) := AlgebraicGeometry.flat_fromSpecStalk Y y
  have : ((Scheme.Modules.pushforward f).obj G).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent f G
  have H : IsPullback (stalkBaseChangeι f y) (stalkBaseChangeStructure f y) f
      (Y.fromSpecStalk y) := IsPullback.of_hasPullback f (Y.fromSpecStalk y)
  have := Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat H G
  obtain ⟨z, hz⟩ := (sectionsEquivOfIso
    (asIso ((baseChangeNatTrans H.w).app G)) ⊤).surjective t
  obtain ⟨V, hyV, b, hb⟩ := exists_pullbackSection_fromSpecStalk_eq
    ((Scheme.Modules.pushforward f).obj G) y z
  refine ⟨V, hyV, b, ?_⟩
  rw [← baseChangeNatTrans_val_app_top_pullbackSection H.w G V
    (le_preimage_fromSpecStalk_of_mem y V hyV) (top_le_preimage_stalkBaseChangeι f y V hyV) b, hb]
  exact hz

end BaseChange

/-! ### Sections on the fibre come from a neighbourhood -/

section Fibre

variable {X Y : Scheme.{u}}

/-- **The fibre `X_y` as a closed subscheme of `X' = X ×_Y Spec 𝒪_{Y,y}`**, as a morphism: the
identification `Stacks.FormalFunctions.fiberIsoInfinitesimalBaseIdealSubschemePow` followed by the
inclusion of `V(𝔪_y 𝒪_{X'})`. -/
public def fiberToStalkBaseChange (f : X ⟶ Y) (y : Y) : f.fiber y ⟶ stalkBaseChange f y :=
  (fiberIsoInfinitesimalBaseIdealSubschemePow f y).hom ≫
    (infinitesimalBaseIdealSheaf f y ^ 1).subschemeι

/-- The inclusion of the fibre into the base change composed with the projection `X' ⟶ X` is
`f.fiberι y`. -/
public theorem fiberToStalkBaseChange_comp (f : X ⟶ Y) (y : Y) :
    fiberToStalkBaseChange f y ≫ stalkBaseChangeι f y = f.fiberι y := by
  rw [fiberToStalkBaseChange, Category.assoc]
  exact fiberIsoInfinitesimalBaseIdealSubschemePow_hom_comp f y

/-- **Every global section of `M` restricted to the fibre is the restriction of a global section
of `M`**, for `M` quasi-coherent on `X' = X ×_Y Spec 𝒪_{Y,y}` whose quotient projection
`M ⟶ M / 𝔪_y M` is surjective on global sections.

The inclusion of the fibre factors as the isomorphism onto `V(𝔪_y 𝒪_{X'})` followed by the
inclusion of that closed subscheme; the first is surjective on sections because it is an
isomorphism, the second by [Stacks, Tag 0EL1] together with the hypothesis. -/
public theorem exists_pullbackSection_fiberToStalkBaseChange (f : X ⟶ Y) (y : Y)
    (M : (stalkBaseChange f y).Modules) [M.IsQuasicoherent]
    (hπ : Function.Surjective ((cokernel.π (C := (stalkBaseChange f y).Modules)
      (idealPowerMultiple
        (infinitesimalBaseIdealSheaf f y) 1 M).ι).app (⊤ : (stalkBaseChange f y).Opens)))
    (r : Γ((Scheme.Modules.pullback (fiberToStalkBaseChange f y)).obj M, ⊤)) :
    ∃ s : Γ(M, ⊤), Scheme.Modules.pullbackSection (fiberToStalkBaseChange f y) M ⊤ ⊤
      (le_preimage_top (fiberToStalkBaseChange f y) ⊤) s = r :=
  exists_pullbackSection_comp (fiberIsoInfinitesimalBaseIdealSubschemePow f y).hom
    (infinitesimalBaseIdealSheaf f y ^ 1).subschemeι M ⊤ ⊤ ⊤
    (le_preimage_top (infinitesimalBaseIdealSheaf f y ^ 1).subschemeι ⊤)
    (le_preimage_top (fiberIsoInfinitesimalBaseIdealSubschemePow f y).hom ⊤)
    (le_preimage_top (fiberToStalkBaseChange f y) ⊤)
    (exists_pullbackSection_top_of_surjective_cokernel_π (infinitesimalBaseIdealSheaf f y) 1 M
      (infinitesimalBaseIdealSheaf f y ^ 1).subschemeι
      (Scheme.IdealSheafData.ker_subschemeι _) hπ _)
    (exists_pullbackSection_top_of_isIso (fiberIsoInfinitesimalBaseIdealSubschemePow f y).hom _ _)
    r

/-- **Every global section of the pullback of `G` to the fibre `X_y` is pulled back from a section
of `G` over `f ⁻¹ V`, for some open neighbourhood `V` of `y`** — granted that the quotient
projection `M ⟶ M / 𝔪_y M` is surjective on global sections, for some quasi-coherent `M` on
`X' = X ×_Y Spec 𝒪_{Y,y}` isomorphic to the pullback of `G`.

Stated for a morphism `w : X_y ⟶ X` *presented* as the composite through the base change, so that
the proof never has to transport along the equality of the two morphisms; the form at
`w = f.fiberι y` is `Stacks.FormalFunctions.exists_pullbackSection_fiberι_eq`.

The route is `X_y ⟶ V(𝔪_y 𝒪_{X'}) ⟶ X' ⟶ X`: the first two steps are
`Stacks.FormalFunctions.exists_pullbackSection_fiberToStalkBaseChange`, the third is degree-zero
flat base change, `Stacks.FormalFunctions.exists_pullbackSection_stalkBaseChangeι_eq`. -/
public theorem exists_pullbackSection_eq_of_comp_eq (f : X ⟶ Y) [QuasiCompact f]
    [QuasiSeparated f] (y : Y) (G : X.Modules) [G.IsQuasicoherent]
    (M : (stalkBaseChange f y).Modules) [M.IsQuasicoherent]
    (θ : (Scheme.Modules.pullback (stalkBaseChangeι f y)).obj G ≅ M)
    (hπ : Function.Surjective ((cokernel.π (C := (stalkBaseChange f y).Modules)
      (idealPowerMultiple
        (infinitesimalBaseIdealSheaf f y) 1 M).ι).app (⊤ : (stalkBaseChange f y).Opens)))
    {w : f.fiber y ⟶ X} (hw : fiberToStalkBaseChange f y ≫ stalkBaseChangeι f y = w)
    (hle : ∀ V : Y.Opens, y ∈ V → (⊤ : (f.fiber y).Opens) ≤ w ⁻¹ᵁ (f ⁻¹ᵁ V))
    (t : Γ((Scheme.Modules.pullback w).obj G, ⊤)) :
    ∃ (V : Y.Opens) (hy : y ∈ V) (a : Γ(G, f ⁻¹ᵁ V)),
      Scheme.Modules.pullbackSection w G (f ⁻¹ᵁ V) ⊤ (hle V hy) a = t := by
  subst hw
  obtain ⟨t₁, ht₁⟩ := (sectionsEquivOfIso
    ((Scheme.Modules.pullbackComp (fiberToStalkBaseChange f y)
      (stalkBaseChangeι f y)).app G) ⊤).surjective t
  obtain ⟨t₂, ht₂⟩ := exists_pullbackSection_of_iso (fiberToStalkBaseChange f y) θ ⊤ ⊤
    (le_preimage_top (fiberToStalkBaseChange f y) ⊤)
    (exists_pullbackSection_fiberToStalkBaseChange f y M hπ) t₁
  obtain ⟨V, hyV, a, ha⟩ := exists_pullbackSection_stalkBaseChangeι_eq f y G t₂
  refine ⟨V, hyV, a, ?_⟩
  rw [← Scheme.Modules.pullbackSection_comp (fiberToStalkBaseChange f y) (stalkBaseChangeι f y) G
    (f ⁻¹ᵁ V) ⊤ ⊤ (top_le_preimage_stalkBaseChangeι f y V hyV)
    (le_preimage_top (fiberToStalkBaseChange f y) ⊤) (hle V hyV) a, ha, ht₂]
  exact ht₁

/-- **The surjectivity clause of [Stacks, Tag 0D2M], in elementwise form**: granted that the
quotient projection `M ⟶ M / 𝔪_y M` is surjective on global sections, for some quasi-coherent `M`
on `X' = X ×_Y Spec 𝒪_{Y,y}` isomorphic to the pullback of `G`, every global section of
`(f.fiberι y) ^* G` on the fibre `X_y` is the pullback of a section of `G` over `f ⁻¹ V` for some
open neighbourhood `V` of `y` — that is, it is in the image of the canonical map out of the stalk
`(f_* G)_y`. -/
public theorem exists_pullbackSection_fiberι_eq (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (y : Y) (G : X.Modules) [G.IsQuasicoherent] (M : (stalkBaseChange f y).Modules)
    [M.IsQuasicoherent]
    (θ : (Scheme.Modules.pullback (stalkBaseChangeι f y)).obj G ≅ M)
    (hπ : Function.Surjective ((cokernel.π (C := (stalkBaseChange f y).Modules)
      (idealPowerMultiple
        (infinitesimalBaseIdealSheaf f y) 1 M).ι).app (⊤ : (stalkBaseChange f y).Opens)))
    (t : Γ((Scheme.Modules.pullback (f.fiberι y)).obj G, ⊤)) :
    ∃ (V : Y.Opens) (hy : y ∈ V) (a : Γ(G, f ⁻¹ᵁ V)),
      Scheme.Modules.pullbackSection (f.fiberι y) G (f ⁻¹ᵁ V) ⊤
        (top_le_preimage_fiberι f y V hy) a = t :=
  exists_pullbackSection_eq_of_comp_eq f y G M θ hπ (fiberToStalkBaseChange_comp f y)
    (fun V hy => top_le_preimage_fiberι f y V hy) t

end Fibre

/-! ### The comparison map out of the stalk, and Tag 0D2M -/

section Tag

variable {X Y : Scheme.{u}}

/-- **Restricting a section to the fibre does not change when the section is first restricted to a
smaller neighbourhood of `y`.** This is what makes the pullbacks to the fibre a cocone on the
diagram whose colimit is the stalk `(f_* G)_y`. -/
public theorem pullbackSectionHom_fiberι_map (f : X ⟶ Y) (y : Y) (G : X.Modules)
    {U V : Y.Opens} (hVU : V ≤ U) (hyV : y ∈ V)
    (x : Γ((Scheme.Modules.pushforward f).obj G, U)) :
    pullbackSectionHom (f.fiberι y) G (f ⁻¹ᵁ V) ⊤ (top_le_preimage_fiberι f y V hyV)
        (((Scheme.Modules.pushforward f).obj G).presheaf.map (homOfLE hVU).op x) =
      pullbackSectionHom (f.fiberι y) G (f ⁻¹ᵁ U) ⊤
        (top_le_preimage_fiberι f y U (hVU hyV)) x := by
  refine Eq.trans (congrArg (fun z => pullbackSectionHom (f.fiberι y) G (f ⁻¹ᵁ V) ⊤
      (top_le_preimage_fiberι f y V hyV) z)
    (PresheafOfModules.congr_map_apply G.val (Subsingleton.elim
      ((Opens.map f.base).map (homOfLE hVU)).op
      (homOfLE ((Opens.map f.base).map (homOfLE hVU)).le).op) x))
    (pullbackSectionHom_map (f.fiberι y) G (f ⁻¹ᵁ U) (f ⁻¹ᵁ V)
      ((Opens.map f.base).map (homOfLE hVU)).le ⊤ (top_le_preimage_fiberι f y V hyV)
      (top_le_preimage_fiberι f y U (hVU hyV)) x)

/-- The restrictions to the fibre `X_y` of the sections of `G` over the opens `f ⁻¹ U`, for `U` an
open neighbourhood of `y`, as a cocone on the diagram whose colimit is the stalk `(f_* G)_y`. -/
public def fiberSectionsCocone (f : X ⟶ Y) (y : Y) (G : X.Modules) :
    Cocone ((OpenNhds.inclusion y).op ⋙ ((Scheme.Modules.pushforward f).obj G).presheaf) where
  pt := Γ((Scheme.Modules.pullback (f.fiberι y)).obj G, ⊤)
  ι :=
    { app U := pullbackSectionHom (f.fiberι y) G (f ⁻¹ᵁ U.unop.1) ⊤
        (top_le_preimage_fiberι f y U.unop.1 U.unop.2)
      naturality := fun U V i => by
        refine (Category.comp_id _).symm.trans ?_ |>.symm
        exact AddCommGrpCat.hom_ext (AddMonoidHom.ext fun x =>
          (pullbackSectionHom_fiberι_map f y G i.unop.le V.unop.2 x).symm) }

/-- **The canonical map `(f_* G)_y ⟶ Γ(X_y, (f.fiberι y) ^* G)`**: the germ at `y` of a section of
`G` over `f ⁻¹ U` goes to its restriction to the fibre. It exists for every `f`, with no
hypothesis, because the fibre lies over every open neighbourhood of `y`.

This is the map whose surjectivity is the second conclusion of [Stacks, Tag 0D2M]. -/
public def fiberSectionsStalkHom (f : X ⟶ Y) (y : Y) (G : X.Modules) :
    ((Scheme.Modules.pushforward f).obj G).presheaf.stalk y ⟶
      Γ((Scheme.Modules.pullback (f.fiberι y)).obj G, ⊤) :=
  colimit.desc _ (fiberSectionsCocone f y G)

/-- The map `fiberSectionsStalkHom f y G` sends the germ at `y` of a section `a` of `f_* G` over
`U` to the restriction of `a` to the fibre `X_y`. -/
@[simp]
public theorem fiberSectionsStalkHom_germ (f : X ⟶ Y) (y : Y) (G : X.Modules) (U : Y.Opens)
    (hy : y ∈ U) (a : Γ((Scheme.Modules.pushforward f).obj G, U)) :
    fiberSectionsStalkHom f y G
        (((Scheme.Modules.pushforward f).obj G).presheaf.germ U y hy a) =
      Scheme.Modules.pullbackSection (f.fiberι y) G (f ⁻¹ᵁ U) ⊤
        (top_le_preimage_fiberι f y U hy) a :=
  ConcreteCategory.congr_hom (colimit.ι_desc (fiberSectionsCocone f y G) (op ⟨U, hy⟩)) a

/-- **The surjectivity clause of [Stacks, Tag 0D2M] as a surjectivity of the canonical map**,
granted the hypothesis of `Stacks.FormalFunctions.exists_pullbackSection_fiberι_eq`: every element
of `Γ(X_y, (f.fiberι y) ^* G)` is the restriction to the fibre of a section over some `f ⁻¹ V`,
hence the image of a germ. -/
public theorem surjective_fiberSectionsStalkHom (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (y : Y) (G : X.Modules) [G.IsQuasicoherent] (M : (stalkBaseChange f y).Modules)
    [M.IsQuasicoherent]
    (θ : (Scheme.Modules.pullback (stalkBaseChangeι f y)).obj G ≅ M)
    (hπ : Function.Surjective ((cokernel.π (C := (stalkBaseChange f y).Modules)
      (idealPowerMultiple
        (infinitesimalBaseIdealSheaf f y) 1 M).ι).app (⊤ : (stalkBaseChange f y).Opens))) :
    Function.Surjective (fiberSectionsStalkHom f y G) := by
  intro t
  obtain ⟨V, hyV, a, ha⟩ := exists_pullbackSection_fiberι_eq f y G M θ hπ t
  exact ⟨((Scheme.Modules.pushforward f).obj G).presheaf.germ V y hyV a,
    (fiberSectionsStalkHom_germ f y G V hyV a).trans ha⟩

/-- **The map `f_*(ℱ ⊗ ℒ ^⊗ d)_y ⟶ H ⁰(X_y, ℱ_y ⊗ ℒ_y ^⊗ d)` of [Stacks, Tag 0D2M].** The germ at
`y` of a section of `ℱ(d) = ℱ ⊗ ℒ ^⊗ d` over `f ⁻¹ U` goes to its restriction to the fibre
(`Stacks.FormalFunctions.fiberSectionsStalkHom`), read in the twist `ℱ_y ⊗ ℒ_y ^⊗ d` of the
restrictions `ℱ_y = (f.fiberι y) ^* ℱ` and `ℒ_y = (f.fiberι y) ^* ℒ` through the canonical
isomorphism `(f.fiberι y) ^* (ℱ(d)) ≅ ℱ_y(d)` of [Stacks, Tag 0EGK]
(`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.pullbackTwistModuleIso`). -/
public def fiberTwistSectionsStalkHom (f : X ⟶ Y) (y : Y) (F L : X.Modules)
    [IsInvertibleModule X L] (d : ℤ) :
    ((Scheme.Modules.pushforward f).obj (twistModule X L F d)).presheaf.stalk y ⟶
      Γ(twistModule (f.fiber y) ((Scheme.Modules.pullback (f.fiberι y)).obj L)
        ((Scheme.Modules.pullback (f.fiberι y)).obj F) d, ⊤) :=
  fiberSectionsStalkHom f y (twistModule X L F d) ≫
    Scheme.Modules.Hom.app (pullbackTwistModuleIso (f.fiberι y) L F d).hom ⊤

/-- The map of [Stacks, Tag 0D2M] into the fibre twist is surjective exactly when the restriction
map into the restriction of the twist is: the two differ by an isomorphism on global sections. -/
public theorem surjective_fiberTwistSectionsStalkHom_iff (f : X ⟶ Y) (y : Y) (F L : X.Modules)
    [IsInvertibleModule X L] (d : ℤ) :
    Function.Surjective (fiberTwistSectionsStalkHom f y F L d) ↔
      Function.Surjective (fiberSectionsStalkHom f y (twistModule X L F d)) := by
  have h : ⇑(fiberTwistSectionsStalkHom f y F L d) =
      (sectionsEquivOfIso (pullbackTwistModuleIso (f.fiberι y) L F d) ⊤) ∘
        (fiberSectionsStalkHom f y (twistModule X L F d)) := by
    funext s
    exact ConcreteCategory.comp_apply _ _ s
  rw [h]
  exact (sectionsEquivOfIso (pullbackTwistModuleIso (f.fiberι y) L F d) ⊤).comp_surjective _

/-- The twist of a coherent module by an invertible module is coherent and quasi-coherent. -/
private theorem isCoherent_and_isQuasicoherent_twistModule (Z : Scheme.{u}) (L F : Z.Modules)
    [IsInvertibleModule Z L] [F.IsCoherent] (d : ℤ) :
    (twistModule Z L F d).IsCoherent ∧ (twistModule Z L F d).IsQuasicoherent := by
  have : (twistModule Z L F d).IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible Z F
      (tensorPowModule Z L d)
  exact ⟨this, _root_.isQuasicoherent_of_isCoherent _⟩

/-- **Both clauses of [Stacks, Tag 0D2M], with the second read in the restriction of the twist to
the fibre.** This is `exists_isZero_stalk_rightDerived_and_surjective_fiberTwist` before the
restriction `(f.fiberι y) ^* (ℱ ⊗ ℒ ^⊗ d)` is identified with `ℱ_y ⊗ ℒ_y ^⊗ d`.

The proof is the source's. Base changing along the flat morphism `Spec 𝒪_{Y,y} ⟶ Y` replaces `Y`
by the spectrum of a Noetherian local ring and `y` by its closed point, where both clauses are
`Stacks.FormalFunctions.exists_subsingleton_and_surjective_twistModule_stalkBaseChange`. The first
clause is then carried back to the stalk by
`Stacks.FormalFunctions.exists_isZero_stalk_rightDerived_twistModule`, and the second by
`Stacks.FormalFunctions.surjective_fiberSectionsStalkHom`: [Stacks, Tag 0EL1] turns the
surjectivity of `H ⁰(X', ℱ'(d)) ⟶ H ⁰(X', ℱ'(d) / 𝔪_y ℱ'(d))` into the surjectivity of
restriction of sections to the closed subscheme `V(𝔪_y 𝒪_{X'}) ≅ X_y`, and degree-zero flat base
change — [Stacks, Tag 02KH] part (1) at `i = 0`,
`Stacks.AlgebraicGeometry.FlatBaseChangeCohomology.isIso_baseChangeNatTrans_of_flat` — identifies
the sections of `ℱ'(d)` on `X'` with the germs at `y` of sections of `ℱ(d)` over the `f ⁻¹ U`. -/
public theorem exists_isZero_stalk_rightDerived_and_surjective_twistModule (f : X ⟶ Y)
    [IsProper f] [AlgebraicGeometry.IsNoetherian Y] (y : Y) (F L : X.Modules)
    [IsInvertibleModule X L] [F.IsCoherent]
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      (∀ p : ℕ, 0 < p →
          IsZero ((((Scheme.Modules.pushforward f).rightDerived p).obj
            (twistModule X L F d)).presheaf.stalk y)) ∧
        Function.Surjective (fiberSectionsStalkHom f y (twistModule X L F d)) := by
  have : AlgebraicGeometry.IsLocallyNoetherian Y := inferInstance
  have : QuasiSeparated f := inferInstance
  obtain ⟨d₁, hd₁⟩ := exists_isZero_stalk_rightDerived_twistModule f y F L hL
  obtain ⟨d₂, hd₂⟩ := exists_subsingleton_and_surjective_twistModule_stalkBaseChange f y F L hL
  refine ⟨max d₁ d₂, fun d hd => ⟨hd₁ d (le_trans (le_max_left _ _) hd), ?_⟩⟩
  obtain ⟨_, _⟩ := isCoherent_and_isQuasicoherent_twistModule X L F d
  have : ((Scheme.Modules.pullback (stalkBaseChangeι f y)).obj F).IsCoherent :=
    AlgebraicGeometry.isCoherent_pullback (stalkBaseChangeι f y) F
  obtain ⟨_, _⟩ := isCoherent_and_isQuasicoherent_twistModule (stalkBaseChange f y)
    ((Scheme.Modules.pullback (stalkBaseChangeι f y)).obj L)
    ((Scheme.Modules.pullback (stalkBaseChangeι f y)).obj F) d
  exact surjective_fiberSectionsStalkHom f y (twistModule X L F d)
    (twistModule (stalkBaseChange f y)
      ((Scheme.Modules.pullback (stalkBaseChangeι f y)).obj L)
      ((Scheme.Modules.pullback (stalkBaseChangeι f y)).obj F) d)
    (pullbackTwistModuleIso (stalkBaseChangeι f y) L F d)
    (surjective_app_top_of_surjective_adicCohomologyProj (stalkBaseChangeStructure f y)
      (stalkMaximalIdeal y) _ 1 ((hd₂ d (le_trans (le_max_right _ _) hd)).2))

/-- **[Stacks, Tag 0D2M].**

Let `f : X ⟶ Y` be a proper morphism of schemes with `Y` Noetherian, let `ℒ` be an invertible
`𝒪_X`-module, let `ℱ` be a coherent `𝒪_X`-module and let `y ∈ Y` be a point such that
`ℒ_y` is ample on the fibre `X_y`. Then there exists a `d₀` such that for all `d ≥ d₀`

1. `R ᵖ f_*(ℱ ⊗_{𝒪_X} ℒ ^⊗ d)_y = 0` for `p > 0`, and
2. the map `f_*(ℱ ⊗_{𝒪_X} ℒ ^⊗ d)_y ⟶ H ⁰(X_y, ℱ_y ⊗_{𝒪_{X_y}} ℒ_y ^⊗ d)` is surjective.

Here `X_y` is `f.fiber y` with its morphism `f.fiberι y` to `X`, `ℱ_y` and `ℒ_y` are the
restrictions of `ℱ` and `ℒ` to it, `R ᵖ f_*` is the `p`-th right derived functor of
`Scheme.Modules.pushforward f`, and `H ⁰(X_y, -)` is the module of global sections. The map in
the second clause is `Stacks.FormalFunctions.fiberTwistSectionsStalkHom`: the germ at `y` of a
section over `f ⁻¹ U` goes to its restriction to the fibre. The proof is
`exists_isZero_stalk_rightDerived_and_surjective_twistModule` together with the identification
`(f.fiberι y) ^* (ℱ ⊗ ℒ ^⊗ d) ≅ ℱ_y ⊗ ℒ_y ^⊗ d` of [Stacks, Tag 0EGK]. -/
@[stacks 0D2M]
public theorem exists_isZero_stalk_rightDerived_and_surjective_fiberTwist (f : X ⟶ Y)
    [IsProper f] [AlgebraicGeometry.IsNoetherian Y] (y : Y) (F L : X.Modules)
    [IsInvertibleModule X L] [F.IsCoherent]
    (hL : IsAmple (f.fiber y) (pullbackModule (f.fiberι y) L)) :
    ∃ d₀ : ℤ, ∀ d : ℤ, d₀ ≤ d →
      (∀ p : ℕ, 0 < p →
          IsZero ((((Scheme.Modules.pushforward f).rightDerived p).obj
            (twistModule X L F d)).presheaf.stalk y)) ∧
        Function.Surjective (fiberTwistSectionsStalkHom f y F L d) := by
  obtain ⟨d₀, hd₀⟩ := exists_isZero_stalk_rightDerived_and_surjective_twistModule f y F L hL
  exact ⟨d₀, fun d hd => ⟨(hd₀ d hd).1,
    (surjective_fiberTwistSectionsStalkHom_iff f y F L d).2 (hd₀ d hd).2⟩⟩

end Tag

end Stacks.FormalFunctions

end
