module

public import StacksFrontier.AlgebraicGeometry.GabberColimit.Basic
public import StacksFrontier.AlgebraicGeometry.TorsionQuasicoherent.Local
public import StacksFrontier.AlgebraicGeometry.Properties.CardinalGenerated

/-!
# The cardinally generated quasi-coherent submodule containing a given section

Let `X` be a scheme, let `F` be a quasi-coherent `𝒪_X`-module and let `κ = cardinalBound X`.
The main result of this file is that **every local section of `F` lies in the image of a
`κ`-generated quasi-coherent submodule of `F`** (`exists_isCardinalGenerated_mem`). This is
the part of Gabber's theorem (Stacks 077N) saying that the `κ`-generated quasi-coherent
submodules of `F` jointly generate `F`, without any statement about the filteredness of the
family or about the colimit of the resulting diagram.

The construction is the one of
`StacksFrontier/AlgebraicGeometry/GabberColimit/Basic.lean`: the chosen section is closed up,
by `exists_bounded_compatible_family`, to a family `T` of at most `κ` sections over each affine
open whose spans form a compatible family `N`, and `sheafSubmodule F N` is the subsheaf cut out
by `N`. This file proves that `sheafSubmodule F N` is quasi-coherent and bounds its local
generators.

## Main definitions

* `gabberModule F N hN`: the subsheaf of `F` attached to a compatible family `N` of submodules
  of the sections over the affine opens, bundled as an object of `X.Modules` so that instance
  search finds the module structure on its sections, with `val` and `mk` naming the two
  directions of the (definitional) identification of its sections with the sections of `F`
  lying locally in `N`.
* `specSectionsEquiv M hU`: the sections over `⊤` of the restriction of `M` to
  `Spec Γ(X, U)` along `IsAffineOpen.fromSpec`, identified `Γ(X, U)`-linearly with `Γ(M, U)`.

## Main results

* `isLocalizedModule_gabber`: the sections of `gabberModule F N hN` over a basic open
  `X.basicOpen a` of an affine open `U` are the localization away from `a` of its sections over
  `U`.  Both inclusions of the compatibility condition are used: the sections over the basic
  open are *spanned* by the restrictions of the sections over `U`, which is exactly the
  statement that `N` localizes (`Submodule.localized'_eq_span`).
* `gabberModule_isQuasicoherent`: hence `gabberModule F N hN` is quasi-coherent, by the
  localization criterion
  `Stacks.AlgebraicGeometry.TorsionQuasicoherent.isQuasicoherent_of_isLocalizedModule_restrictₗ`.
* `exists_presentation_of_span_eq_top`: a module whose restriction to `Spec Γ(X, U)` is
  quasi-coherent has, over `U`, a presentation whose generators are indexed by any chosen
  spanning set of `Γ(M, U)`.
* `isCardinalGenerated_gabberModule`: if `N` is spanned by a family `T` of at most `κ`
  sections over each affine open, then `gabberModule F N hN` is `κ`-generated.
* `exists_isCardinalGenerated_mem`: the main result described above.

## Implementation notes

`X.Modules` is a `def` for `SheafOfModules X.ringCatSheaf` which does not unfold at
instance-reducible transparency, so the module structure on the sections of
`(sheafSubmodule F N hN).toSheafOfModules` is not found by instance search; as in
`StacksFrontier/AlgebraicGeometry/TorsionQuasicoherent/Basic.lean`, the subsheaf is therefore
bundled as `gabberModule F N hN : X.Modules` and its sections are reached through `val` and
`mk`.

In `specSectionsEquiv` the domain is written as
`↑(moduleSpecΓFunctor.obj (M.restrict hU.fromSpec))` rather than as the sections
`Γ(M.restrict hU.fromSpec, ⊤)`, which are the same type but not syntactically equal: the
`Set.image` of the inverse equivalence has to elaborate against the former in
`exists_presentation_of_span_eq_top`, and a coercion carried in the stated type of the
equivalence is discharged once, at its definition.

## References

* [Stacks Project, Tag 077N](https://stacks.math.columbia.edu/tag/077N)
* [Stacks Project, Tag 077L](https://stacks.math.columbia.edu/tag/077L)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open Stacks.AlgebraicGeometry.AffinePushforward
open Stacks.AlgebraicGeometry.GabberColimit
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange
open Stacks.AlgebraicGeometry.TorsionQuasicoherent
open Stacks.AlgebraicGeometry.CardinalGeneration

universe u

namespace Stacks.AlgebraicGeometry.Coherator

/-! ### Spanning sets of a submodule -/

/-- A spanning set of a submodule spans the whole of that submodule, viewed as a module in its
own right. -/
theorem span_subtype_eq_top {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    {p : Submodule R M} {T : Set M} (hT : p = Submodule.span R T) :
    Submodule.span R {z : ↥p | (z : M) ∈ T} = ⊤ := by
  have hTp : T ⊆ (p : Set M) := hT ▸ Submodule.subset_span
  refine Submodule.map_injective_of_injective (f := p.subtype) p.injective_subtype ?_
  rw [Submodule.map_span, Submodule.map_subtype_top]
  have himg : (p.subtype '' {z : ↥p | (z : M) ∈ T}) = T := by
    refine Set.eq_of_subset_of_subset ?_ ?_
    · rintro x ⟨z, hz, rfl⟩
      exact hz
    · exact fun x hx ↦ ⟨⟨x, hTp hx⟩, hx, rfl⟩
  rw [himg, hT]

variable {X : Scheme.{u}}

/-! ### Presentations with a prescribed set of generators -/

/-- A module which, over each affine open of `X`, has a presentation with at most `κ`
generators is `κ`-generated: the affine opens cover `X`, and the generators of the
presentations are the required local generating families. -/
theorem isCardinalGenerated_of_exists_presentations (M : X.Modules) (κ : Cardinal.{u})
    (h : ∀ V : X.affineOpens, ∃ P : (M.over V.1).Presentation,
      Cardinal.mk P.generators.I ≤ κ) :
    SheafOfModules.IsCardinalGenerated (R := X.ringCatSheaf) M κ := by
  choose P hP using h
  exact ⟨{ I := X.affineOpens
           X := fun V ↦ V.1
           coversTop := (Opens.coversTop_iff _ _).mpr
             (IsOpenCover.mk (iSup_affineOpens_eq_top X))
           generators := fun V ↦ (P V).generators }, hP⟩

/-- The sections over `⊤` of the restriction of `M` to `Spec Γ(X, U)` along
`IsAffineOpen.fromSpec`, identified `Γ(X, U)`-linearly with the sections of `M` over `U`. -/
def specSectionsEquiv (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    ↑(moduleSpecΓFunctor.obj (M.restrict hU.fromSpec)) ≃ₗ[Γ(X, U)] Γ(M, U) :=
  (restrictSectionsEquiv M hU ⊤).trans
    (sectionsCongrSelf M ((Scheme.Hom.image_top_eq_opensRange _).trans hU.opensRange_fromSpec)
      (fromSpec_image_le hU ⊤))

/-- **A presentation with a prescribed set of generators.**  If the restriction of `M` to
`Spec Γ(X, U)` is quasi-coherent, then every spanning set `s` of `Γ(M, U)` indexes the
generators of a presentation of `M.over U`.

The module on `Spec Γ(X, U)` is the `tilde` of its global sections, `presentationTilde` builds
a presentation of a `tilde` out of a spanning set, and transporting a presentation along an
isomorphism, along a restriction to an open and along `Scheme.Modules.overEquiv` all leave the
indexing type of the generators unchanged. -/
theorem exists_presentation_of_span_eq_top (M : X.Modules) {U : X.Opens} (hU : IsAffineOpen U)
    (hqc : (M.restrict hU.fromSpec).IsQuasicoherent)
    (s : Set Γ(M, U)) (hs : Submodule.span Γ(X, U) s = ⊤) :
    ∃ P : (M.over U).Presentation, Cardinal.mk P.generators.I ≤ Cardinal.mk s := by
  have hiso : IsIso (M.restrict hU.fromSpec).fromTildeΓ :=
    (isQuasicoherent_iff_isIso_fromTildeΓ (M.restrict hU.fromSpec)).mp hqc
  set e := specSectionsEquiv M hU with he
  set s' : Set ↑(moduleSpecΓFunctor.obj (M.restrict hU.fromSpec)) := e.symm '' s with hs'
  have hspan : Submodule.span Γ(X, U) s' = ⊤ := by
    have h : Submodule.span Γ(X, U)
        (⇑(e.symm : Γ(M, U) →ₗ[Γ(X, U)] ↑(moduleSpecΓFunctor.obj (M.restrict hU.fromSpec)))
          '' s) = ⊤ := by
      rw [← Submodule.map_span, hs, Submodule.map_top]
      exact LinearMap.range_eq_top_of_surjective _ e.symm.surjective
    rw [hs']
    exact h
  let P0 := presentationTilde.{u} _ s' hspan _ (Submodule.span_eq _)
  let P1 : (M.restrict hU.fromSpec).Presentation :=
    presentationOfIso (@asIso _ _ _ _ (M.restrict hU.fromSpec).fromTildeΓ hiso) P0
  let P2 := Scheme.Modules.presentationRestrict hU.isoSpec.hom P1
  let iso : (M.restrict hU.fromSpec).restrict hU.isoSpec.hom ≅ M.restrict U.ι :=
    ((Scheme.Modules.restrictFunctorComp hU.isoSpec.hom hU.fromSpec).app M).symm ≪≫
      (Scheme.Modules.restrictFunctorCongr hU.isoSpec_hom_fromSpec).app M
  refine ⟨presentationOver U M (presentationOfIso iso P2), ?_⟩
  show Cardinal.mk ↥s' ≤ Cardinal.mk ↥s
  rw [hs']
  exact Cardinal.mk_image_le

/-! ### The subsheaf attached to a compatible family -/

variable (F : X.Modules) [F.IsQuasicoherent]
  (N : ∀ U : X.affineOpens, Submodule Γ(X, U.1) Γ(F, U.1)) (hN : IsCompatible F N)

/-- The subsheaf of `F` cut out by a compatible family `N` of submodules of the sections over
the affine opens, bundled as an object of `X.Modules`. -/
def gabberModule : X.Modules := (sheafSubmodule F N hN).toSheafOfModules

/-- The underlying section of `F` of a section of `gabberModule F N hN`. -/
def val {W : X.Opens} (z : Γ(gabberModule F N hN, W)) : Γ(F, W) :=
  (show ↥(localSections F N W) from z).1

/-- Sections of `gabberModule F N hN` are determined by their underlying sections of `F`. -/
theorem val_inj {W : X.Opens} {z₁ z₂ : Γ(gabberModule F N hN, W)}
    (h : val F N hN z₁ = val F N hN z₂) : z₁ = z₂ := Subtype.ext h

/-- A section of `F` lying locally in `N`, viewed as a section of `gabberModule F N hN`. -/
def mk {W : X.Opens} (s : Γ(F, W)) (hs : IsLocallyIn F N s) : Γ(gabberModule F N hN, W) :=
  show ↥(localSections F N W) from ⟨s, hs⟩

/-- The underlying section of `mk F N hN s hs` is `s`. -/
@[simp]
theorem val_mk {W : X.Opens} (s : Γ(F, W)) (hs : IsLocallyIn F N s) :
    val F N hN (mk F N hN s hs) = s := rfl

/-- Over an affine open the sections of `gabberModule F N hN` are the members of `N`. -/
theorem val_mem (W : X.affineOpens) (z : Γ(gabberModule F N hN, W.1)) :
    val F N hN z ∈ N W :=
  (obj_sheafSubmodule F N hN W).le (show ↥(localSections F N W.1) from z).2

/-- A member of `N` over an affine open, viewed as a section of `gabberModule F N hN`. -/
def mkAffine (W : X.affineOpens) (s : Γ(F, W.1)) (hs : s ∈ N W) :
    Γ(gabberModule F N hN, W.1) :=
  mk F N hN s (show s ∈ localSections F N W.1 from (obj_sheafSubmodule F N hN W).ge hs)

/-- The underlying section of `mkAffine F N hN W s hs` is `s`. -/
@[simp]
theorem val_mkAffine (W : X.affineOpens) (s : Γ(F, W.1)) (hs : s ∈ N W) :
    val F N hN (mkAffine F N hN W s hs) = s := rfl

/-- `val` commutes with scalar multiplication. -/
@[simp]
theorem val_smul {W : X.Opens} (r : Γ(X, W)) (z : Γ(gabberModule F N hN, W)) :
    val F N hN (r • z) = r • val F N hN z := rfl

/-- `val` sends the zero section to the zero section. -/
@[simp]
theorem val_zero {W : X.Opens} :
    val F N hN (0 : Γ(gabberModule F N hN, W)) = (0 : Γ(F, W)) := rfl

/-- `val` is linear for the scalars restricted from a larger open. -/
theorem val_smul' {W V : X.Opens} (h : V ≤ W) (r : Γ(X, W)) (z : Γ(gabberModule F N hN, V)) :
    letI := moduleOfLE (gabberModule F N hN) h
    letI := moduleOfLE F h
    val F N hN (r • z) = r • val F N hN z := rfl

/-- `val` commutes with restriction of sections. -/
theorem val_restrictₗ {W V : X.Opens} (h : V ≤ W) (z : Γ(gabberModule F N hN, W)) :
    letI := moduleOfLE (gabberModule F N hN) h
    letI := moduleOfLE F h
    val F N hN (restrictₗ (gabberModule F N hN) h z) = restrictₗ F h (val F N hN z) := rfl

/-- The inclusion of `gabberModule F N hN` into `F`. -/
def ιF : gabberModule F N hN ⟶ F := (sheafSubmodule F N hN).ι

/-- On sections, the inclusion `ιF F N hN` is `val`. -/
@[simp]
theorem ιF_app {W : X.Opens} (z : Γ(gabberModule F N hN, W)) :
    (ιF F N hN).app W z = val F N hN z := rfl

/-- The inclusion of `gabberModule F N hN` into `F` is a monomorphism: it is injective on
sections. -/
instance mono_ιF : Mono (ιF F N hN) where
  right_cancellation {Z} g h hgh := by
    refine Scheme.Modules.hom_ext _ _ fun W ↦ ?_
    ext z
    refine val_inj F N hN ?_
    have hz := congrArg (fun t : Z ⟶ F ↦ t.app W z) hgh
    simpa using hz

/-! ### Quasi-coherence -/

/-- **The subsheaf attached to a compatible family localizes.**  The sections of
`gabberModule F N hN` over a basic open `X.basicOpen a` of an affine open `U` are the
localization away from `a` of its sections over `U`.

That `a` acts invertibly is automatic, because the restriction of `a` to `X.basicOpen a` is a
unit of `Γ(X, X.basicOpen a)` and the sections form a module over that ring.  Surjectivity up
to powers of `a` is the compatibility condition for the pair `(U, X.basicOpen a)`, which by
`Submodule.localized'_eq_span` says precisely that `N` localizes, and injectivity up to powers
of `a` is inherited from `F`. -/
theorem isLocalizedModule_gabber {U : X.Opens} (hU : IsAffineOpen U) (a : Γ(X, U)) :
    letI := moduleOfLE (gabberModule F N hN) (X.basicOpen_le a)
    IsLocalizedModule.Away a (restrictₗ (gabberModule F N hN) (X.basicOpen_le a)) := by
  set G := gabberModule F N hN with hG
  set hle := X.basicOpen_le a with hhle
  let := moduleOfLE G hle
  let := moduleOfLE F hle
  let := algebraOfLE X hle
  let := isScalarTowerOfLE F hle
  have hV : IsAffineOpen (X.basicOpen a) := hU.basicOpen a
  have hFloc : IsLocalizedModule.Away a (restrictₗ F hle) :=
    isLocalizedModule_restrictₗ F hU a rfl hle
  have hSloc : IsLocalization.Away a Γ(X, X.basicOpen a) := hU.isLocalization_basicOpen a
  have hunit : IsUnit (X.presheaf.map (homOfLE hle).op a) :=
    X.toRingedSpace.isUnit_res_basicOpen a
  have hkey : (N ⟨X.basicOpen a, hV⟩ : Submodule Γ(X, X.basicOpen a) Γ(F, X.basicOpen a)) =
      Submodule.localized' Γ(X, X.basicOpen a) (Submonoid.powers a) (restrictₗ F hle)
        (N ⟨U, hU⟩) := by
    rw [Submodule.localized'_eq_span, hN ⟨U, hU⟩ ⟨X.basicOpen a, hV⟩ hle]
    rfl
  refine IsLocalizedModule.Away.mk_of_addCommGroup ?_ ?_ ?_
  · refine (Module.End.isUnit_iff _).mpr ⟨fun z₁ z₂ h ↦ ?_, fun z ↦ ?_⟩
    · simp only [Module.algebraMap_end_apply] at h
      exact hunit.smul_left_cancel.mp h
    · obtain ⟨v, hv⟩ := hunit.exists_left_inv
      refine ⟨v • z, ?_⟩
      rw [Module.algebraMap_end_apply]
      show (X.presheaf.map (homOfLE hle).op a) • v • z = z
      rw [smul_smul, mul_comm, hv, one_smul]
  · intro z
    have hz : val F N hN z ∈ N ⟨X.basicOpen a, hV⟩ := val_mem F N hN ⟨X.basicOpen a, hV⟩ z
    rw [hkey, Submodule.mem_localized'] at hz
    obtain ⟨m, hm, s, hs⟩ := hz
    obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff (s : Γ(X, U)) a).mp s.2
    refine ⟨n, mkAffine F N hN ⟨U, hU⟩ m hm, val_inj F N hN ?_⟩
    rw [val_smul', val_restrictₗ, val_mkAffine]
    rw [IsLocalizedModule.mk'_eq_iff] at hs
    rw [hn]
    exact hs.symm
  · intro x hx
    have h0 : restrictₗ F hle (val F N hN x) = restrictₗ F hle (0 : Γ(F, U)) := by
      rw [map_zero, ← val_restrictₗ F N hN hle x, hx]
      rfl
    obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq (f := restrictₗ F hle) a h0
    refine ⟨n, val_inj F N hN ?_⟩
    rw [val_smul, val_zero, hn, smul_zero]

/-- **The subsheaf attached to a compatible family is quasi-coherent.** -/
theorem gabberModule_isQuasicoherent : (gabberModule F N hN).IsQuasicoherent :=
  isQuasicoherent_of_isLocalizedModule_restrictₗ (gabberModule F N hN)
    fun _ hU a ↦ isLocalizedModule_gabber F N hN hU a

/-! ### The bound on the local generators -/

/-- **The subsheaf attached to a compatible family spanned by `κ` sections is `κ`-generated.**
Over an affine open `U` the sections of `gabberModule F N hN` are `N U`, which is spanned by
`T U`, so `exists_presentation_of_span_eq_top` provides a presentation whose generators are
indexed by (a subset of) `T U`. -/
theorem isCardinalGenerated_gabberModule (T : ∀ U : X.affineOpens, Set Γ(F, U.1))
    (hNT : ∀ U, N U = Submodule.span Γ(X, U.1) (T U)) (κ : Cardinal.{u})
    (hT : ∀ U, Cardinal.mk (T U) ≤ κ) :
    SheafOfModules.IsCardinalGenerated (R := X.ringCatSheaf) (gabberModule F N hN) κ := by
  refine isCardinalGenerated_of_exists_presentations (gabberModule F N hN) κ fun V ↦ ?_
  obtain ⟨U, hU'⟩ := V
  have hU : IsAffineOpen U := hU'
  have hqcV : ((gabberModule F N hN).restrict hU.fromSpec).IsQuasicoherent :=
    isQuasicoherent_restrict_fromSpec (gabberModule F N hN) hU
      fun a ↦ isLocalizedModule_gabber F N hN hU a
  have hspan : Submodule.span Γ(X, U)
      {z : Γ(gabberModule F N hN, U) | val F N hN z ∈ T ⟨U, hU'⟩} = ⊤ :=
    span_subtype_eq_top (p := localSections F N U) (T := T ⟨U, hU'⟩)
      ((obj_sheafSubmodule F N hN ⟨U, hU'⟩).trans (hNT ⟨U, hU'⟩))
  obtain ⟨P, hP⟩ := exists_presentation_of_span_eq_top (gabberModule F N hN) hU hqcV _ hspan
  refine ⟨P, hP.trans (le_trans ?_ (hT ⟨U, hU'⟩))⟩
  refine Cardinal.mk_le_of_injective
    (f := fun z : {z : Γ(gabberModule F N hN, U) | val F N hN z ∈ T ⟨U, hU'⟩} ↦
      (⟨val F N hN z.1, z.2⟩ : (T ⟨U, hU'⟩ : Set Γ(F, U)))) ?_
  intro z₁ z₂ h
  have h' : val F N hN z₁.1 = val F N hN z₂.1 :=
    congrArg (fun w : (T ⟨U, hU'⟩ : Set Γ(F, U)) ↦ (w : Γ(F, U))) h
  exact Subtype.ext (val_inj F N hN h')

/-! ### The main existence result -/

/-- **Every local section of a quasi-coherent module lies in a `cardinalBound X`-generated
quasi-coherent submodule.** This is part of Gabber's theorem (Stacks 077N).

The chosen section is closed up by `exists_bounded_compatible_family` to a family of at most
`cardinalBound X` sections over each affine open whose spans are compatible, and the subsheaf
cut out by those spans is quasi-coherent and `cardinalBound X`-generated. -/
theorem exists_isCardinalGenerated_mem (F : X.Modules) [F.IsQuasicoherent] {U : X.Opens}
    (s : Γ(F, U)) :
    ∃ G : X.Modules, G.IsQuasicoherent ∧
      SheafOfModules.IsCardinalGenerated (R := X.ringCatSheaf) G (cardinalBound X) ∧
      ∃ φ : G ⟶ F, Mono φ ∧ s ∈ Set.range (φ.app U) := by
  have hκ : Cardinal.aleph0 ≤ cardinalBound X := aleph0_le_cardinalBound X
  have hXκ : Cardinal.mk X.affineOpens ≤ cardinalBound X := mk_affineOpens_le_cardinalBound X
  have hSsub : ∀ V : X.affineOpens,
      {y | ∃ h : V.1 ≤ U, F.presheaf.map (homOfLE h).op s = y}.Subsingleton := by
    rintro V y ⟨h1, rfl⟩ z ⟨h2, rfl⟩
    rfl
  obtain ⟨T, hST, hTκ, hTcompat⟩ := exists_bounded_compatible_family F hκ hXκ
    (fun V ↦ {y | ∃ h : V.1 ≤ U, F.presheaf.map (homOfLE h).op s = y})
    fun V ↦ ((hSsub V).finite.lt_aleph0.le).trans hκ
  set N : ∀ V : X.affineOpens, Submodule Γ(X, V.1) Γ(F, V.1) :=
    fun V ↦ Submodule.span Γ(X, V.1) (T V) with hNdef
  have hN : IsCompatible F N := isCompatible_span F T hTcompat
  refine ⟨gabberModule F N hN, gabberModule_isQuasicoherent F N hN,
    isCardinalGenerated_gabberModule F N hN T (fun _ ↦ rfl) _ hTκ, ιF F N hN, inferInstance,
    mk F N hN s fun W h ↦ ?_, rfl⟩
  exact Submodule.subset_span (hST W ⟨h, rfl⟩)

end Stacks.AlgebraicGeometry.Coherator

end
