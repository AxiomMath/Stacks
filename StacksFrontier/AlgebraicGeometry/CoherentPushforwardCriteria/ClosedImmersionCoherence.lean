module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.RingTheory.Finiteness.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.ClosureSubscheme
public import StacksFrontier.AlgebraicGeometry.CoherentPushforwardCriteria.PointClosureSquare
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.Coherence
public import StacksFrontier.AlgebraicGeometry.Scheme.FunctorialityQuasiCoherent.Basic

/-!
# Coherence across a closed immersion

Let `i : Z ⟶ X` be a closed immersion of locally Noetherian schemes and let `G` be a
quasi-coherent `𝒪_Z`-module. This file proves that `i_* G` is coherent exactly when `G` is, and
deduces the coherence assertion of [Stacks, Tag 0BK2]: for an open immersion `j : U ⟶ X` and a
point `x` of `U`, coherence of the direct image to `X` of the structure sheaf of the reduced
closure of `{x}` can be tested on the reduced closure of `{j x}` in `X`.

## Main definitions

* `Stacks.AlgebraicGeometry.ClosedImmersionCoherence.specRestrictPushforwardIso`: the direct
  image `f_* G`, read on an affine open `V` of the target whose preimage is affine, is the direct
  image along `Spec (f.app V)` of `G` read on `f ⁻¹ᵁ V`.
* `Stacks.AlgebraicGeometry.ClosedImmersionCoherence.specModulePushforwardIso`: the
  corresponding identification of the two modules of sections, with scalars restricted along
  `f.app V`.

## Main results

* `isFiniteType_of_isFiniteType_pushforward_unconditional` and
  `isCoherent_of_isCoherent_pushforward`: finite type and coherence **descend along an arbitrary
  affine morphism** — the first with no Noetherian hypothesis at all, the second needing only the
  source locally Noetherian. Only this direction holds at that generality; the two `iff`s below
  need the closed immersion.
* `Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isFiniteType_pushforward_iff` and
  `isCoherent_pushforward_iff`: finite type and coherence are tested on the direct image along a
  closed immersion of locally Noetherian schemes.
* `Stacks.AlgebraicGeometry.ClosedImmersionCoherence.isCoherent_pushforward_pointClosure_iff`:
  the coherence assertion of [Stacks, Tag 0BK2].

## Implementation notes

The whole argument happens on one affine open `V` of `X` at a time, and the comparison it needs
is `specModulePushforwardIso`. Both sides of the equivalence are read through
`Stacks.AlgebraicGeometry.CoherentTFAE.specModule`, the `Γ(X, V)`-module of sections of the
restriction to `V` transported to `Spec Γ(X, V)`; the point of that functor is that
condition (4) of [Stacks, Tag 01XZ] is stated with it in both directions
(`isFiniteTildeOn_of_finite_specModule` and `finite_specModule` below). The comparison itself is
assembled in three steps, all of which are isomorphisms of functors already in the library or
immediate from them:

* restriction to `V` commutes with the direct image
  (`Stacks.AlgebraicGeometry.AffinePushforward.restrictPushforwardIso`);
* restriction along the inverse of an isomorphism of schemes *is* the direct image along the
  isomorphism (`restrictIsoPushforward`), which turns the two remaining restrictions into direct
  images so that `AlgebraicGeometry.Scheme.Modules.pushforwardComp` applies;
* conjugating `f ∣_ V` by the two canonical isomorphisms with spectra gives
  `Spec.map (f.app V)` (`isoSpec_comp_morphismRestrict`, from Mathlib's
  `AlgebraicGeometry.IsAffineOpen.SpecMap_appLE_fromSpec`).

Once the two modules of sections are identified, the mathematics is the elementary statement
that along a ring map `φ : R ⟶ S` a module is finite over `S` as soon as it is finite over `R`,
and conversely when `φ` is surjective. Surjectivity of `f.app V` is exactly what a closed
immersion supplies, by `AlgebraicGeometry.Scheme.Hom.app_surjective`; this is the only place
where `IsClosedImmersion` rather than `IsAffineHom` is used, which is why the descending
direction `isFiniteType_of_isFiniteType_pushforward` is stated for an arbitrary affine
morphism.

`finite_specModule` is the `Module.Finite` content of
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_isQuasicoherent_of_isFiniteType`,
which concludes the packaged `IsFiniteTildeOn` predicate instead; the comparison above is a
statement about the module, so the module statement is what is needed here.

## References

* [Stacks Project, Tag 0BK2](https://stacks.math.columbia.edu/tag/0BK2)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace Opposite
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.CoherenceCriteria

universe u

namespace Stacks.AlgebraicGeometry.ClosedImmersionCoherence

/-! ### Restriction along an isomorphism is a direct image -/

/-- Restriction along the inverse of an isomorphism of schemes is the direct image along the
isomorphism. Both are inverse to the direct image along the inverse: the direct images along
`e.hom` and `e.inv` compose to the identity, and restriction along `e.inv` is a retraction of
the direct image along `e.inv`. -/
noncomputable def restrictIsoPushforward {Y Z : Scheme.{u}} (e : Y ≅ Z) :
    Scheme.Modules.restrictFunctor e.inv ≅ Scheme.Modules.pushforward e.hom :=
  haveI : IsOpenImmersion e.inv := IsOpenImmersion.of_isIso e.inv
  haveI : IsOpenImmersion e.hom := IsOpenImmersion.of_isIso e.hom
  let hFG : Scheme.Modules.pushforward e.hom ⋙ Scheme.Modules.pushforward e.inv ≅ 𝟭 _ :=
    Scheme.Modules.pushforwardComp e.hom e.inv ≪≫
      Scheme.Modules.pushforwardCongr e.hom_inv_id ≪≫ Scheme.Modules.pushforwardId Y
  let hGR : Scheme.Modules.pushforward e.inv ⋙ Scheme.Modules.restrictFunctor e.inv ≅ 𝟭 _ :=
    Scheme.Modules.restrictFunctorAdjCounitIso e.inv
  (Functor.leftUnitor _).symm ≪≫
    Functor.isoWhiskerRight hFG.symm (Scheme.Modules.restrictFunctor e.inv) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (Scheme.Modules.pushforward e.hom) hGR ≪≫
    Functor.rightUnitor _

/-! ### A morphism of affine opens is the spectrum of its ring map -/

/-- **A morphism read on affine opens is `Spec` of the induced ring map.** For `f : Z ⟶ X` and an
affine open `V` of `X` whose preimage is affine, conjugating `f ∣_ V` by the two canonical
isomorphisms with spectra gives `Spec.map (f.app V)`. -/
theorem isoSpec_comp_morphismRestrict {Z X : Scheme.{u}} (f : Z ⟶ X) {V : X.Opens}
    (hV : IsAffineOpen V) (hW : IsAffineOpen (f ⁻¹ᵁ V)) :
    hW.isoSpec.hom ≫ Spec.map (f.app V) = (f ∣_ V) ≫ hV.isoSpec.hom := by
  have key := IsAffineOpen.SpecMap_appLE_fromSpec f hV hW (le_refl (f ⁻¹ᵁ V))
  simp only [IsAffineOpen.fromSpec, Category.assoc] at key
  rw [← morphismRestrict_ι f V] at key
  have key2 : Spec.map (f.appLE V (f ⁻¹ᵁ V) (le_refl _)) ≫ hV.isoSpec.inv =
      hW.isoSpec.inv ≫ (f ∣_ V) := by
    refine (cancel_mono V.ι).mp ?_
    simpa only [Category.assoc] using key
  rw [Scheme.Hom.app_eq_appLE, ← Iso.eq_inv_comp, ← Category.assoc, ← key2, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]

/-! ### The direct image read on an affine open of the target -/

/-- **The affine-open form of a direct image is a direct image along a morphism of spectra.**
Reading `f_* G` on an affine open `V` of the target whose preimage is affine gives the direct
image along `Spec.map (f.app V)` of `G` read on `f ⁻¹ᵁ V`. -/
noncomputable def specRestrictPushforwardIso {Z X : Scheme.{u}} (f : Z ⟶ X) (G : Z.Modules)
    {V : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen (f ⁻¹ᵁ V)) :
    specRestrict ((Scheme.Modules.pushforward f).obj G) hV ≅
      (Scheme.Modules.pushforward (Spec.map (f.app V))).obj (specRestrict G hW) :=
  haveI : IsOpenImmersion hV.isoSpec.inv := IsOpenImmersion.of_isIso _
  haveI : IsOpenImmersion hW.isoSpec.inv := IsOpenImmersion.of_isIso _
  let A := (Scheme.Modules.restrictFunctor hV.isoSpec.inv).mapIso
      ((AffinePushforward.restrictPushforwardIso f V).app G) ≪≫
    (restrictIsoPushforward hV.isoSpec).app _ ≪≫
    (Scheme.Modules.pushforwardComp (f ∣_ V) hV.isoSpec.hom).app _
  let B := (Scheme.Modules.pushforward (Spec.map (f.app V))).mapIso
      ((restrictIsoPushforward hW.isoSpec).app (G.restrict (f ⁻¹ᵁ V).ι)) ≪≫
    (Scheme.Modules.pushforwardComp hW.isoSpec.hom (Spec.map (f.app V))).app _ ≪≫
    (Scheme.Modules.pushforwardCongr (isoSpec_comp_morphismRestrict f hV hW)).app _
  A ≪≫ B.symm

/-- **The global sections of a direct image along a morphism of spectra** are the global sections
of the module with scalars restricted along the ring map. The two modules have the same carrier,
and the two actions agree by naturality of `AlgebraicGeometry.Scheme.ΓSpecIso`. -/
theorem moduleSpecΓ_pushforward_specMap {R S : CommRingCat.{u}} (φ : R ⟶ S)
    (N : (Spec S).Modules) :
    moduleSpecΓFunctor.obj ((Scheme.Modules.pushforward (Spec.map φ)).obj N) =
      (ModuleCat.restrictScalars φ.hom).obj (moduleSpecΓFunctor.obj N) := by
  have h : ((Spec.map φ).appTop).hom.comp (Scheme.ΓSpecIso R).inv.hom
      = (Scheme.ΓSpecIso S).inv.hom.comp φ.hom :=
    congrArg CommRingCat.Hom.hom (Scheme.ΓSpecIso_inv_naturality φ).symm
  show (ModuleCat.restrictScalars
      (((Spec.map φ).appTop).hom.comp (Scheme.ΓSpecIso R).inv.hom)).obj
        (N.val.obj (op (⊤ : (Spec S).Opens)))
    = (ModuleCat.restrictScalars
      ((Scheme.ΓSpecIso S).inv.hom.comp φ.hom)).obj
        (N.val.obj (op (⊤ : (Spec S).Opens)))
  rw [h]

/-- **The module of a direct image at an affine open of the target** is the module of the source
at the preimage, with scalars restricted along `f.app V`. -/
noncomputable def specModulePushforwardIso {Z X : Scheme.{u}} (f : Z ⟶ X) (G : Z.Modules)
    {V : X.Opens} (hV : IsAffineOpen V) (hW : IsAffineOpen (f ⁻¹ᵁ V)) :
    specModule ((Scheme.Modules.pushforward f).obj G) hV ≅
      (ModuleCat.restrictScalars (f.app V).hom).obj (specModule G hW) :=
  moduleSpecΓFunctor.mapIso (specRestrictPushforwardIso f G hV hW) ≪≫
    eqToIso (moduleSpecΓ_pushforward_specMap (f.app V) (specRestrict G hW))

/-! ### Finiteness along a ring map -/

private theorem span_le_span_restrictScalars {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (M : ModuleCat.{u} S) (T : Set M) :
    ∀ x, x ∈ Submodule.span R (M := ((ModuleCat.restrictScalars f).obj M)) T →
      x ∈ Submodule.span S T := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul r a _ ha => exact Submodule.smul_mem _ (f r) ha

private theorem span_restrictScalars_le_span {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{u} S) (T : Set M) :
    ∀ x, x ∈ Submodule.span S T →
      x ∈ Submodule.span R (M := ((ModuleCat.restrictScalars f).obj M)) T := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy => exact Submodule.subset_span hy
  | zero => exact zero_mem _
  | add a b _ _ ha hb => exact add_mem ha hb
  | smul s a _ ha =>
      obtain ⟨r, rfl⟩ := hf s
      exact Submodule.smul_mem _ r ha

/-- A module finite over a ring acting through a ring map is finite over the target ring: a
generating family over the source generates over the target, because the source acts through the
map. -/
theorem finite_of_finite_restrictScalars {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (M : ModuleCat.{u} S) (h : Module.Finite R ((ModuleCat.restrictScalars f).obj M)) :
    Module.Finite S M := by
  rw [Module.finite_def, Submodule.fg_def] at h ⊢
  obtain ⟨T, hTfin, hTgen⟩ := h
  exact ⟨T, hTfin, le_antisymm le_top fun x _ =>
    span_le_span_restrictScalars f M T x (hTgen ▸ Submodule.mem_top)⟩

/-- Along a *surjective* ring map a finite module stays finite after restriction of scalars:
every scalar of the target is the image of one of the source. -/
theorem finite_restrictScalars_of_finite {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
    (hf : Function.Surjective f) (M : ModuleCat.{u} S) (h : Module.Finite S M) :
    Module.Finite R ((ModuleCat.restrictScalars f).obj M) := by
  rw [Module.finite_def, Submodule.fg_def] at h ⊢
  obtain ⟨T, hTfin, hTgen⟩ := h
  exact ⟨T, hTfin, le_antisymm le_top fun x _ =>
    span_restrictScalars_le_span f hf M T x (hTgen ▸ Submodule.mem_top)⟩

/-! ### Finiteness of the sections at an affine open -/

/-- **A quasi-coherent module of finite type has finite sections over every affine open.** -/
theorem finite_specModule {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    {V : X.Opens} (hV : IsAffineOpen V) : Module.Finite Γ(X, V) (specModule F hV) :=
  have : (F.restrict V.ι).IsFiniteType := isFiniteType_restrict V.ι F
  have : (specRestrict F hV).IsFiniteType := isFiniteType_restrict hV.isoSpec.inv _
  have h : (tilde (specModule F hV)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_iso.{u} (M := specRestrict F hV)
      (asIso (specRestrict F hV).fromTildeΓ).symm
  (AlgebraicGeometry.tilde_isFiniteType_iff (specModule F hV)).mp h

/-- Finite type descends along an affine morphism, by testing on the preimages of affine opens. -/
private theorem isFiniteType_of_isFiniteType_pushforward_aux {Z X : Scheme.{u}}
    (f : Z ⟶ X) [IsAffineHom f] (G : Z.Modules) [G.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj G).IsFiniteType] : G.IsFiniteType := by
  refine isFiniteType_of_cover_isFiniteTildeOn G (fun V : X.affineOpens => f ⁻¹ᵁ (V : X.Opens))
    (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top X)) (fun V => V.2.preimage f) fun V => ?_
  refine isFiniteTildeOn_of_finite_specModule G _ (V.2.preimage f) ?_
  have h2 : Module.Finite Γ(X, (V : X.Opens))
      ((ModuleCat.restrictScalars (f.app (V : X.Opens)).hom).obj
        (specModule G (V.2.preimage f))) :=
    have : Module.Finite Γ(X, (V : X.Opens))
        (specModule ((Scheme.Modules.pushforward f).obj G) V.2) := finite_specModule _ V.2
    Module.Finite.equiv (specModulePushforwardIso f G V.2 (V.2.preimage f)).toLinearEquiv
  exact finite_of_finite_restrictScalars _ _ h2

/-- **Finite type descends along an affine morphism.** If the direct image of a quasi-coherent
module along an affine morphism into a locally Noetherian scheme is of finite type, then so is
the module. -/
theorem isFiniteType_of_isFiniteType_pushforward {Z X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : Z ⟶ X) [IsAffineHom f] (G : Z.Modules) [G.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj G).IsFiniteType] : G.IsFiniteType := by
  exact isFiniteType_of_isFiniteType_pushforward_aux f G

/-- **Finite type descends along an affine morphism.** If the direct image of a quasi-coherent
module along an affine morphism is of finite type, then so is the module.

No scheme here is Noetherian: the argument is the identification of the two modules of sections
over an affine open of the target, followed by `finite_of_finite_restrictScalars`, which needs
nothing of the ring map. -/
theorem isFiniteType_of_isFiniteType_pushforward_unconditional {Z X : Scheme.{u}}
    (f : Z ⟶ X) [IsAffineHom f] (G : Z.Modules) [G.IsQuasicoherent]
    [((Scheme.Modules.pushforward f).obj G).IsFiniteType] : G.IsFiniteType := by
  exact isFiniteType_of_isFiniteType_pushforward_aux f G

/-- **Finite type ascends along a closed immersion.** On every affine open of the target the
sections of the direct image are the sections of the module on the preimage, finite over the
quotient ring and hence, the ring map being surjective, over the ring itself. -/
theorem isFiniteType_pushforward {Z X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Z] (f : Z ⟶ X) [IsClosedImmersion f] (G : Z.Modules)
    [G.IsQuasicoherent] [G.IsFiniteType] :
    ((Scheme.Modules.pushforward f).obj G).IsFiniteType := by
  refine isFiniteType_of_cover_isFiniteTildeOn _ (fun V : X.affineOpens => (V : X.Opens))
    (IsOpenCover.mk (iSup_affineOpens_eq_top X)) (fun V => V.2) fun V => ?_
  refine isFiniteTildeOn_of_finite_specModule _ _ V.2 ?_
  have h2 := finite_restrictScalars_of_finite (f.app (V : X.Opens)).hom
    (Scheme.Hom.app_surjective f _ V.2) (specModule G (V.2.preimage f))
    (finite_specModule G (V.2.preimage f))
  exact Module.Finite.equiv
    (specModulePushforwardIso f G V.2 (V.2.preimage f)).symm.toLinearEquiv

/-- **Finite type is tested on the direct image along a closed immersion.** -/
theorem isFiniteType_pushforward_iff {Z X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Z] (f : Z ⟶ X) [IsClosedImmersion f] (G : Z.Modules)
    [G.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj G).IsFiniteType ↔ G.IsFiniteType :=
  ⟨fun _ => isFiniteType_of_isFiniteType_pushforward_unconditional f G,
    fun _ => isFiniteType_pushforward f G⟩

/-- **Coherence descends along an affine morphism.** If the direct image of a quasi-coherent
module along an affine morphism is coherent, then so is the module, provided the source is
locally Noetherian.

Only the source is Noetherian, and only the source has to be: coherence of the direct image
gives its finiteness of type, which descends along any affine morphism by
`isFiniteType_of_isFiniteType_pushforward_unconditional` with no Noetherian hypothesis at all,
and on a locally Noetherian source finiteness of type plus quasi-coherence is coherence, by
`Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType`.

The converse fails for a merely affine morphism: `Spec k[X] ⟶ Spec k` carries the structure
sheaf, which is coherent, to `k[X]`, which is not a finite `k`-module. It needs the morphism to
be finite — `isFiniteType_pushforward` below, for a closed immersion, and
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite`, which
is [Stacks, Tag 01Y6]. -/
theorem isCoherent_of_isCoherent_pushforward {Z X : Scheme.{u}}
    [IsLocallyNoetherian Z] (f : Z ⟶ X) [IsAffineHom f] (G : Z.Modules) [G.IsQuasicoherent]
    (h : ((Scheme.Modules.pushforward f).obj G).IsCoherent) : G.IsCoherent := by
  have := (isQuasicoherent_isFiniteType_of_isCoherent
    ((Scheme.Modules.pushforward f).obj G)).2
  have : G.IsFiniteType := isFiniteType_of_isFiniteType_pushforward_unconditional f G
  exact isCoherent_of_isQuasicoherent_of_isFiniteType (X := Z) G

/-- **Coherence is tested on the direct image along a closed immersion.** For `i : Z ⟶ X` a
closed immersion of locally Noetherian schemes and `G` a quasi-coherent `𝒪_Z`-module, `i_* G` is
coherent if and only if `G` is. This is the general form of the coherence assertion of
[Stacks, Tag 0BK2]; the forward implication is [Stacks, Tag 01Y6] for a finite morphism. -/
theorem isCoherent_pushforward_iff {Z X : Scheme.{u}} [IsLocallyNoetherian X]
    [IsLocallyNoetherian Z] (f : Z ⟶ X) [IsClosedImmersion f] (G : Z.Modules)
    [G.IsQuasicoherent] :
    ((Scheme.Modules.pushforward f).obj G).IsCoherent ↔ G.IsCoherent := by
  refine ⟨isCoherent_of_isCoherent_pushforward f G, fun _ => ?_⟩
  have := (isQuasicoherent_isFiniteType_of_isCoherent G).2
  have : ((Scheme.Modules.pushforward f).obj G).IsFiniteType := isFiniteType_pushforward f G
  exact isCoherent_of_isQuasicoherent_of_isFiniteType _

/-! ### The coherence assertion of Stacks 0BK2 -/

/-- **Stacks Project, Tag 0BK2.** Coherence of the direct image to `X` of the structure sheaf of
the reduced closure of `{x}` in `U` is equivalent to coherence of its direct image to the reduced
closure of `{j x}` in `X`: the two iterated direct images agree, and the remaining vertical arrow
is a closed immersion. -/
@[stacks 0BK2 "coherence equivalence"]
theorem isCoherent_pushforward_pointClosure_iff {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] [IsLocallyNoetherian U] [IsLocallyNoetherian X] (x : U)
    (j' : (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme ⟶
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subscheme)
    (comm : j' ≫ (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({j x} : Set X))).subschemeι =
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subschemeι ≫ j) :
    ((Scheme.Modules.pushforward j).obj
      ((Scheme.Modules.pushforward
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subschemeι).obj
        (SheafOfModules.unit
          (Scheme.IdealSheafData.vanishingIdeal
            (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf))).IsCoherent ↔
    ((Scheme.Modules.pushforward j').obj
      (SheafOfModules.unit
        (Scheme.IdealSheafData.vanishingIdeal
          (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)).IsCoherent := by
  have hj' : IsOpenImmersion j' :=
    Scheme.IdealSheafData.isOpenImmersion_of_comp_subschemeι_eq j x j' comm
  have hNZ : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subscheme :=
    Scheme.IdealSheafData.isLocallyNoetherian_subscheme _
  have hNW : IsLocallyNoetherian (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({x} : Set U))).subscheme :=
    Scheme.IdealSheafData.isLocallyNoetherian_subscheme _
  have hQC : ((Scheme.Modules.pushforward j').obj
      (SheafOfModules.unit (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf)).IsQuasicoherent :=
    AlgebraicGeometry.pushforward_isQuasicoherent j' _
  have e := Scheme.Modules.pushforwardPointClosureIso j x j' comm
  rw [← isCoherent_pushforward_iff (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({j x} : Set X))).subschemeι
    ((Scheme.Modules.pushforward j').obj (SheafOfModules.unit
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({x} : Set U))).subscheme.ringCatSheaf))]
  exact ⟨fun _ => Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso e.symm,
    fun _ => Stacks.AlgebraicGeometry.CoherentDevissage.isCoherent_of_iso e⟩

end Stacks.AlgebraicGeometry.ClosedImmersionCoherence

end
