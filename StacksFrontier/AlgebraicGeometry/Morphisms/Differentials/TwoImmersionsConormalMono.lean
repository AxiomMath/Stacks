module

public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.TwoImmersionsConormalSequence
public import StacksFrontier.AlgebraicGeometry.PullbackPseudofunctor.Basic
public import StacksFrontier.RingTheory.Smooth.Conormal

/-!
# Exactness on the left of the conormal sequence of two immersions

Let `i : Z ⟶ X` and `j : Z ⟶ Y` be immersions of schemes fitting into a commutative triangle
`i ≫ p = j` over a morphism `p : X ⟶ Y`. [Stacks, Tag 067L] attaches to that triangle a
canonical sequence of `𝒪_Z`-modules

`𝒞_{Z/Y} ⟶ 𝒞_{Z/X} ⟶ i^*Ω_{X/Y} ⟶ 0`,

whose first arrow is `Stacks.ConormalSequenceTwoImmersions.conormalTransitivityMap`.
[Stacks, Tag 06AB] asserts that when `p` is smooth the sequence is in addition exact on the
left, that is, the first arrow is injective.

## Main results

* `Stacks.ConormalSequenceTwoImmersions.mono_conormalTransitivityMap_of_formallySmooth`: the
  canonical map `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` is a monomorphism as soon as `p` induces a formally
  smooth ring map on every compatible pair of affine opens.
* `Stacks.ConormalSequenceTwoImmersions.mono_conormalTransitivityMap`: the same for a smooth
  `p`, which is the hypothesis [Stacks, Tag 06AB] states it under.

## Route

The source reduces the statement to its commutative-algebra counterpart
[Stacks, Tag 06A9]: for ring maps `A → B → C` with `A → C` surjective and `A → B` formally
smooth, the map `I/I² ⟶ J/J²` of [Stacks, Tag 065V] — where `I = ker (A → C)` and
`J = ker (B → C)` — admits a left inverse, hence is injective. That is
`Algebra.FormallySmooth.exists_leftInverse_mapCotangent`.

The reduction is carried out on sections rather than on stalks. Around every point of `Z`
there are affine opens `U ⊆ X` and `V ⊆ Y` with `U ⊆ p⁻¹V`, both inside the coborder of the
range of the corresponding immersion, and with `i⁻¹U = j⁻¹V`; such opens are produced from a
section of `𝒪_Z` cutting out a small enough basic open, lifted to `V₀` along the surjection
`Γ(Y, V₀) → Γ(Z, j⁻¹V₀)` and transported to `X` along `p`. On such a pair the three rings
`Γ(Y, V) → Γ(X, U) → Γ(Z, i⁻¹U)` are exactly the tower of [Stacks, Tag 06A9], the two ideals
are the ones cutting out `Z` in the two charts, and the affine characterisation of
[Stacks, Tag 01R4] — `Stacks.Immersion.IsInducedConormalSheafMap` — identifies the map on
sections with `Ideal.mapCotangent`. Injectivity on the opens `j⁻¹V` therefore follows, and
those opens are arbitrarily small, so the first arrow is a monomorphism by the sheaf condition.

The affine characterisation speaks of the transpose of the arrow along the adjunction
`(𝟙 Z)^* ⊣ (𝟙 Z)_*`. The transpose is the composite of the unit with the arrow, and both the
unit and the identification of pullback along an identity with the identity functor are
isomorphisms, so monomorphy transfers between the transpose and the arrow itself.

## Implementation notes

Only formal smoothness of the ring maps `Γ(Y, V) → Γ(X, U)` on affine charts is used, which is
weaker than smoothness of `p`; the general statement is proved first and specialised.

The transpose is given a name of its own,
`Stacks.ConormalSequenceTwoImmersions.conormalTransitivitySections`, and is a definition rather
than an abbreviation. The elaborated statement of the affine characterisation is large, and
leaving the transpose reducible makes the two spellings of a conormal sheaf meet in a
definitional-equality check on terms of that size.

## What is not proved here

[Stacks, Tag 06AB] speaks of the three-term sequence, and only its left-hand exactness is
proved below. Exactness at `𝒞_{Z/X}` and surjectivity onto `i^*Ω_{X/Y}` are the content of
[Stacks, Tag 067L] rather than of [Stacks, Tag 06AB], and are not restated here; they are
`Stacks.ConormalSequenceTwoImmersions.conormalShortComplexModules_exact` of
`StacksFrontier.AlgebraicGeometry.Thickenings.UnramifiedPairSplitConormalSequence` and
`Stacks.ConormalSequenceTwoImmersions.epi_conormalDifferential` of
`StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.TwoImmersionsConormalExact`. The short
exactness of the three-term sequence therefore belongs with those and not here: it asks for the
second arrow, which is
`Stacks.ConormalSequenceRight.conormalDifferential` of
`StacksFrontier.AlgebraicGeometry.ConormalSequenceRight.Basic`, and whose target is written in a
presentation of `𝒞_{Z/X}` other than the one the first arrow above uses.

## References

* [Stacks Project, Tag 06AB](https://stacks.math.columbia.edu/tag/06AB)
* [Stacks Project, Tag 067L](https://stacks.math.columbia.edu/tag/067L)
* [Stacks Project, Tag 06A9](https://stacks.math.columbia.edu/tag/06A9)
* [Stacks Project, Tag 065V](https://stacks.math.columbia.edu/tag/065V)
* [Stacks Project, Tag 01R4](https://stacks.math.columbia.edu/tag/01R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open RingedSpaceModuleAdjunction 

universe u

namespace Stacks.ConormalSequenceTwoImmersions

/-! ### Affine charts of an immersion -/

/-- An affine open of the ambient scheme inside the coborder of the range of an immersion
carries an affine model of the scheme-theoretic intersection: that intersection is the
spectrum of a quotient of the ring of functions on the open, compatibly with
`AlgebraicGeometry.IsAffineOpen.isoSpec`. -/
private theorem exists_affineModel {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U) (hUc : U ≤ i.coborderRange) :
    ∃ (I : Ideal Γ(X, U)) (e : pullback i U.ι ≅ Spec (CommRingCat.of (Γ(X, U) ⧸ I))),
      pullback.snd i U.ι ≫ hU.isoSpec.hom =
        e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I)) := by
  have hcl : IsClosedImmersion (i ∣_ U) := by
    have h := isClosedImmersion_resLE_of_le_coborderRange i U hUc
    rwa [Scheme.Hom.resLE_eq_morphismRestrict] at h
  let _ : IsAffine (U : Scheme.{u}) := hU
  obtain ⟨I, e₀, he₀⟩ :=
    (IsClosedImmersion.Spec_iff (f := (i ∣_ U) ≫ hU.isoSpec.hom)).mp inferInstance
  refine ⟨I, pullbackRestrictIsoRestrict i U ≪≫ e₀, ?_⟩
  rw [Iso.trans_hom, Category.assoc, ← he₀, ← Category.assoc,
    pullbackRestrictIsoRestrict_hom_morphismRestrict]

/-- The map on sections of an immersion over an affine open inside the coborder of its range is
surjective: over such an open the immersion is a closed immersion of affine schemes. -/
private theorem surjective_app_of_le_coborderRange {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U) (hUc : U ≤ i.coborderRange) :
    Function.Surjective (i.app U).hom := by
  obtain ⟨I, e, he⟩ := exists_affineModel i U hU hUc
  have h := Stacks.Conormal.surjective_appLE_of_affineModel i U hU I e he
  rwa [Scheme.Hom.appLE_eq_app] at h

/-- The kernel of the map on sections of an immersion over an affine open with an affine model is
the ideal of that model. -/
private theorem ker_app_eq_of_affineModel {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U))
    (e : pullback i U.ι ≅ Spec (CommRingCat.of (Γ(X, U) ⧸ I)))
    (he : pullback.snd i U.ι ≫ hU.isoSpec.hom =
      e.hom ≫ Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk I))) :
    RingHom.ker (i.app U).hom = I := by
  have h := Stacks.Conormal.ker_appLE_eq_of_affineModel i U hU I e he
  rwa [Scheme.Hom.appLE_eq_app] at h

/-- The preimage of an affine open inside the coborder of the range of an immersion is an
affine open of the source. -/
private theorem isAffineOpen_preimage_of_le_coborderRange {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.Opens) (hU : IsAffineOpen U) (hUc : U ≤ i.coborderRange) :
    IsAffineOpen (i ⁻¹ᵁ U) := by
  obtain ⟨I, e, he⟩ := exists_affineModel i U hU hUc
  exact Stacks.Conormal.isAffineOpen_preimage_of_affineModel i U I e

section Triangle

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y)
  [IsImmersion i] [IsImmersion j]

/-- **Compatible affine charts for a triangle of immersions.** Every point of `Z` has, inside
any given open neighbourhood, one of the form `j⁻¹V` for an affine open `V ⊆ Y` admitting an
affine open `U ⊆ X` with `U ⊆ p⁻¹V` and `i⁻¹U = j⁻¹V`, both `U` and `V` lying in the coborder
of the range of the immersion into them.

A first pair of affine opens is chosen around the images of the point; the preimage `j⁻¹V₀` is
then affine, so it contains a basic open `D(c)` inside the prescribed neighbourhood, and `c`
lifts to a section `r` of `𝒪_Y` over `V₀`. Taking `V = D(r)` and `U = D(p^♯ r)` makes both
preimages equal to `D(c)`. -/
private theorem exists_compatible_affine (h : i ≫ p = j) (z : Z) (W : Z.Opens) (hzW : z ∈ W) :
    ∃ (U : X.Opens) (V : Y.Opens), IsAffineOpen U ∧ IsAffineOpen V ∧
      U ≤ i.coborderRange ∧ V ≤ j.coborderRange ∧ U ≤ p ⁻¹ᵁ V ∧
      i ⁻¹ᵁ U = j ⁻¹ᵁ V ∧ z ∈ j ⁻¹ᵁ V ∧ j ⁻¹ᵁ V ≤ W := by
  have hzjc : j z ∈ j.coborderRange := subset_coborder (Set.mem_range_self z)
  have hzic : i z ∈ i.coborderRange := subset_coborder (Set.mem_range_self z)
  obtain ⟨V₀, hV₀, hzV₀, hV₀c⟩ := exists_isAffineOpen_mem_and_subset hzjc
  have hpt : p (i z) = j z := congrArg (fun f : Z ⟶ Y => f z) h
  have hzp : i z ∈ p ⁻¹ᵁ V₀ := by change p (i z) ∈ V₀; rw [hpt]; exact hzV₀
  obtain ⟨U₀, hU₀, hzU₀, hU₀le⟩ :=
    exists_isAffineOpen_mem_and_subset (X := X) (U := i.coborderRange ⊓ p ⁻¹ᵁ V₀) ⟨hzic, hzp⟩
  have hU₀c : U₀ ≤ i.coborderRange := le_trans hU₀le inf_le_left
  have hU₀V₀ : U₀ ≤ p ⁻¹ᵁ V₀ := le_trans hU₀le inf_le_right
  have hT₀ : IsAffineOpen (j ⁻¹ᵁ V₀) :=
    isAffineOpen_preimage_of_le_coborderRange j V₀ hV₀ hV₀c
  have hzT₁ : z ∈ i ⁻¹ᵁ U₀ := hzU₀
  obtain ⟨c, hcT, hzc⟩ :=
    hT₀.exists_basicOpen_le (V := (i ⁻¹ᵁ U₀) ⊓ W) ⟨z, hzT₁, hzW⟩ (show z ∈ j ⁻¹ᵁ V₀ from hzV₀)
  obtain ⟨r, hr⟩ := surjective_app_of_le_coborderRange j V₀ hV₀ hV₀c c
  refine ⟨X.basicOpen ((p.appLE V₀ U₀ hU₀V₀).hom r), Y.basicOpen r,
    hU₀.basicOpen _, hV₀.basicOpen r, le_trans (X.basicOpen_le _) hU₀c,
    le_trans (Y.basicOpen_le r) hV₀c, ?_, ?_, ?_, ?_⟩
  · rw [Scheme.basicOpen_appLE]
    exact inf_le_right
  · have hpreV : j ⁻¹ᵁ Y.basicOpen r = Z.basicOpen c := by
      rw [Scheme.preimage_basicOpen, hr]
    rw [hpreV, Scheme.basicOpen_appLE, i.preimage_inf, ← Scheme.Hom.comp_preimage i p, h, hpreV]
    exact inf_eq_right.mpr (le_trans hcT inf_le_left)
  · rw [Scheme.preimage_basicOpen, hr]; exact hzc
  · rw [Scheme.preimage_basicOpen, hr]; exact le_trans hcT inf_le_right

end Triangle

/-- The triangle, read on sections over a compatible pair of affine opens: the ring map of `p`
followed by the one of `i` is the ring map of `j`. -/
private theorem appLE_comp_app {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y)
    (h : i ≫ p = j) (U : X.Opens) (V : Y.Opens)
    (hUV : U ≤ p ⁻¹ᵁ V) (hle : i ⁻¹ᵁ U ≤ j ⁻¹ᵁ V) :
    p.appLE V U hUV ≫ i.app U = j.appLE V (i ⁻¹ᵁ U) hle := by
  subst j
  simpa only [Scheme.Hom.appLE_eq_app] using
    Scheme.Hom.appLE_comp_appLE i p V U (i ⁻¹ᵁ U) hUV le_rfl

/-! ### The algebraic input -/

/-- **[Stacks, Tag 06A9], as injectivity.** For ring maps `A → B → C` with `A → C` surjective
and `A → B` formally smooth, the map `ker (A → C) / ker (A → C)² ⟶ ker (B → C) / ker (B → C)²`
of [Stacks, Tag 065V] is injective: it admits a left inverse by
`Algebra.FormallySmooth.exists_leftInverse_mapCotangent`. -/
private theorem injective_mapCotangent (A B C : Type*) [CommRing A] [CommRing B] [CommRing C]
    [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] [Algebra.FormallySmooth A B]
    (hAC : Function.Surjective (algebraMap A C)) {J : Ideal A} {I : Ideal B}
    (hJ : J = RingHom.ker (algebraMap A C)) (hI : I = RingHom.ker (algebraMap B C))
    (hIJ : J ≤ Ideal.comap (Algebra.ofId A B) I) :
    Function.Injective (Ideal.mapCotangent J I (Algebra.ofId A B) hIJ) := by
  subst hJ hI
  obtain ⟨ρ, hρ⟩ := Algebra.FormallySmooth.exists_leftInverse_mapCotangent A B C hAC
  refine Function.LeftInverse.injective (g := ρ) fun x => ?_
  simpa only [LinearMap.comp_apply, LinearMap.id_apply] using congrArg (fun f => f x) hρ

section Chart

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y)
  [IsImmersion i] [IsImmersion j]

omit [IsImmersion i] in
/-- **The algebraic content of exactness on the left, on a compatible pair of affine charts.**
Let `U ⊆ X` and `V ⊆ Y` be affine opens with `U ⊆ p⁻¹V` and `i⁻¹U = j⁻¹V`, let `V` lie in the
coborder of the range of `j`, let `I ⊆ Γ(X, U)` and `J ⊆ Γ(Y, V)` cut out `Z`, and let `p`
induce a formally smooth ring map on the pair. Then two classes in `J/J²` with the same image
in `I/I²` under `p^♯` are equal.

The three rings `Γ(Y, V) → Γ(X, U) → Γ(Z, i⁻¹U)` form the tower of [Stacks, Tag 06A9]: the
first map is formally smooth, the composite is surjective because `j` is a closed immersion
over `V` and `i⁻¹U = j⁻¹V`, and the two ideals are the kernels of the composite and of the
second map. -/
private theorem toCotangent_eq_of_appLE_toCotangent_eq (h : i ≫ p = j)
    (U : X.Opens) (V : Y.Opens) (hV : IsAffineOpen V)
    (hVc : V ≤ j.coborderRange) (hUV : U ≤ p ⁻¹ᵁ V) (hVeq : i ⁻¹ᵁ U = j ⁻¹ᵁ V)
    (hfs : (p.appLE V U hUV).hom.FormallySmooth)
    (I : Ideal Γ(X, U)) (J : Ideal Γ(Y, V))
    (hI : RingHom.ker (i.app U).hom = I) (hJ : RingHom.ker (j.app V).hom = J)
    (hIJ : ∀ a ∈ J, (p.appLE V U hUV).hom a ∈ I) (c c' : J)
    (hcc : I.toCotangent ⟨(p.appLE V U hUV).hom (c : Γ(Y, V)), hIJ _ c.2⟩ =
      I.toCotangent ⟨(p.appLE V U hUV).hom (c' : Γ(Y, V)), hIJ _ c'.2⟩) :
    J.toCotangent c = J.toCotangent c' := by
  let _ : Algebra Γ(Y, V) Γ(X, U) := (p.appLE V U hUV).hom.toAlgebra
  let _ : Algebra Γ(X, U) Γ(Z, i ⁻¹ᵁ U) := (i.app U).hom.toAlgebra
  let _ : Algebra Γ(Y, V) Γ(Z, i ⁻¹ᵁ U) := (j.appLE V (i ⁻¹ᵁ U) hVeq.le).hom.toAlgebra
  let _ : IsScalarTower Γ(Y, V) Γ(X, U) Γ(Z, i ⁻¹ᵁ U) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (congrArg (fun f => f.hom a) (appLE_comp_app i j p h U V hUV hVeq.le)).symm
  let _ : Algebra.FormallySmooth Γ(Y, V) Γ(X, U) := hfs
  have hres : Z.presheaf.map (homOfLE hVeq.le).op = Z.presheaf.map (eqToHom hVeq).op := by
    congr 1
  have hiso : Function.Bijective ((Z.presheaf.map (eqToHom hVeq).op).hom) :=
    ConcreteCategory.bijective_of_isIso _
  have hsurj : Function.Surjective (algebraMap Γ(Y, V) Γ(Z, i ⁻¹ᵁ U)) := by
    show Function.Surjective (j.appLE V (i ⁻¹ᵁ U) hVeq.le).hom
    rw [Scheme.Hom.appLE, hres]
    exact hiso.2.comp (surjective_app_of_le_coborderRange j V hV hVc)
  have hJker : J = RingHom.ker (algebraMap Γ(Y, V) Γ(Z, i ⁻¹ᵁ U)) := by
    refine hJ.symm.trans ?_
    ext a
    show (j.app V).hom a = 0 ↔ (j.appLE V (i ⁻¹ᵁ U) hVeq.le).hom a = 0
    rw [Scheme.Hom.appLE, hres, CommRingCat.comp_apply]
    exact ⟨fun ha => by rw [ha, map_zero], fun ha => hiso.1 (by rw [ha, map_zero])⟩
  have hIJ' : J ≤ Ideal.comap (Algebra.ofId Γ(Y, V) Γ(X, U)) I := fun a ha => hIJ a ha
  refine injective_mapCotangent Γ(Y, V) Γ(X, U) Γ(Z, i ⁻¹ᵁ U) hsurj hJker hI.symm hIJ' ?_
  rw [Ideal.mapCotangent_toCotangent, Ideal.mapCotangent_toCotangent]
  exact hcc

end Chart

/-! ### Monomorphy from injectivity on small opens -/

/-- A morphism of sheaves of modules injective on the sections over a basis of opens is a
monomorphism: the forgetful functor to sheaves of abelian groups is faithful, so it reflects
monomorphisms, and a morphism of sheaves of abelian groups injective on a basis is injective on
every stalk. -/
public theorem mono_of_isBasis_app_injective {T : TopCat.{u}}
    {O : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} {M N : SheafOfModules.{u} O}
    (ψ : M ⟶ N) {B : Set (Opens T)} (hB : Opens.IsBasis B)
    (h : ∀ U ∈ B, Function.Injective (ConcreteCategory.hom (ψ.val.app (op U)))) :
    Mono ψ := by
  refine (SheafOfModules.toSheaf O).mono_of_mono_map
    ((TopCat.Presheaf.mono_iff_stalk_mono _).2 fun x => ?_)
  refine ConcreteCategory.mono_of_injective _ ?_
  exact TopCat.Presheaf.stalkFunctor_map_injective_of_isBasis hB (fun U hU => h U hU) x

/-- A morphism of sheaves of modules injective on the sections over arbitrarily small opens
around every point is a monomorphism. -/
public theorem mono_of_app_injective_nbhd {T : TopCat.{u}}
    {O : Sheaf (Opens.grothendieckTopology T) RingCat.{u}} {M N : SheafOfModules.{u} O}
    (ψ : M ⟶ N)
    (hnb : ∀ (W : Opens T) (x : T), x ∈ W → ∃ W' : Opens T, W' ≤ W ∧ x ∈ W' ∧
      Function.Injective (ConcreteCategory.hom (ψ.val.app (op W')))) : Mono ψ := by
  refine mono_of_isBasis_app_injective ψ
    (B := {W | Function.Injective (ConcreteCategory.hom (ψ.val.app (op W)))}) ?_
    fun U hU => hU
  rw [Opens.isBasis_iff_nbhd]
  intro W y hyW
  obtain ⟨W', hle, hy, hinj⟩ := hnb W y hyW
  exact ⟨W', hinj, hy, hle⟩

/-- Cancelling a split epimorphism on the left of a monomorphism. -/
public theorem mono_of_comp_mono {C : Type*} [Category C] {A B D : C} {f : A ⟶ B} {r : B ⟶ A}
    (hrf : r ≫ f = 𝟙 B) {g : B ⟶ D} (hm : Mono (f ≫ g)) : Mono g := by
  refine ⟨fun u v huv => ?_⟩
  have h : u ≫ r = v ≫ r := hm.right_cancellation _ _ (by
    rw [Category.assoc, Category.assoc, ← Category.assoc r f g, hrf, Category.id_comp, huv])
  simpa [hrf] using h =≫ f

/-- The inverse of an isomorphism of modules is injective on elements. -/
public theorem injective_iso_inv {R : Type u} [Ring R] {M N : ModuleCat.{u} R} (e : M ≅ N) :
    Function.Injective e.inv.hom :=
  (ConcreteCategory.bijective_of_isIso e.inv).1

/-! ### The transpose along the identity adjunction -/

/-- The unit of the pullback-pushforward adjunction along the identity of a scheme is the
inverse of the isomorphism identifying pullback along an identity with the identity functor;
in particular it is an isomorphism. -/
theorem unit_id_eq (W : Scheme.{u})
    (M : SheafOfModules.{u} (structureSheafRing W.toLocallyRingedSpace.toRingedSpace)) :
    (modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 W)).toShHom).unit.app M =
      (Stacks.PullbackPseudofunctor.modulePullbackIdIso
        W.toLocallyRingedSpace.toRingedSpace).inv.app M :=
  (((Stacks.PullbackPseudofunctor.modulePullbackIdIso
      W.toLocallyRingedSpace.toRingedSpace).app M).comp_hom_eq_id).mp
    (Stacks.PullbackPseudofunctor.unit_comp_map_modulePullbackIdIso_hom_app
      W.toLocallyRingedSpace.toRingedSpace M)

/-- Transposing a morphism out of the pullback along an identity is composing with the unit,
pushforward along an identity being the identity functor. -/
public theorem homEquiv_id_eq (W : Scheme.{u})
    (M N : SheafOfModules.{u} (structureSheafRing W.toLocallyRingedSpace.toRingedSpace))
    (c : (modulePullback (Scheme.Hom.toLRSHom (𝟙 W)).toShHom).obj M ⟶ N) :
    (modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 W)).toShHom).homEquiv M N c =
      (modulePullbackPushforwardAdjunction
        (Scheme.Hom.toLRSHom (𝟙 W)).toShHom).unit.app M ≫ c :=
  Adjunction.homEquiv_unit _ _ _ _

section Mono

variable {Z X Y : Scheme.{u}} (i : Z ⟶ X) (j : Z ⟶ Y) (p : X ⟶ Y)
  [IsImmersion i] [IsImmersion j]

/-- **The first arrow of [Stacks, Tag 067L], read on sections.** The transpose along
`(𝟙 Z)^* ⊣ (𝟙 Z)_*` of the canonical map `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}`, which is the form in which the
affine characterisation of [Stacks, Tag 01R4] describes it. -/
private def conormalTransitivitySections (h : i ≫ p = j) :=
  (modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).homEquiv
    (Stacks.Conormal.conormalSheaf j) (Stacks.Conormal.conormalSheaf i)
    ((pullbackIdIso Z).hom.app (Stacks.Conormal.conormalSheaf j) ≫
      conormalTransitivityMap i j p h)

/-- The transpose is the unit followed by the canonical map. -/
private theorem conormalTransitivitySections_eq (h : i ≫ p = j) :
    conormalTransitivitySections i j p h =
      (modulePullbackPushforwardAdjunction (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).unit.app
          (Stacks.Conormal.conormalSheaf j) ≫
        (pullbackIdIso Z).hom.app (Stacks.Conormal.conormalSheaf j) ≫
          conormalTransitivityMap i j p h :=
  homEquiv_id_eq Z _ _ _

/-- **The transpose of the first arrow is a monomorphism** when `p` induces a formally smooth
ring map on every compatible pair of affine opens. -/
private theorem mono_conormalTransitivitySections
    (hfs : ∀ (U : X.Opens) (V : Y.Opens), IsAffineOpen U → IsAffineOpen V →
      ∀ hUV : U ≤ p ⁻¹ᵁ V, (p.appLE V U hUV).hom.FormallySmooth)
    (h : i ≫ p = j) : Mono (conormalTransitivitySections i j p h) := by
  refine mono_of_app_injective_nbhd (conormalTransitivitySections i j p h) fun W z hzW => ?_
  obtain ⟨U, V, hU, hV, hUc, hVc, hUV, hVeq, hzV, hVW⟩ :=
    exists_compatible_affine i j p h z W hzW
  refine ⟨j ⁻¹ᵁ V, hVW, hzV, ?_⟩
  unfold conormalTransitivitySections
  obtain ⟨I, eI, heI⟩ := exists_affineModel i U hU hUc
  obtain ⟨J, eJ, heJ⟩ := exists_affineModel j V hV hVc
  have hcomm : i ≫ p = 𝟙 Z ≫ j := h.trans (Category.id_comp j).symm
  have hmem : ∀ a ∈ J, (p.appLE V U hUV).hom a ∈ I := fun a ha =>
    Stacks.Immersion.immersionConormalSheafMap_ideal_mem i j (𝟙 Z) p hcomm U hU V hV hUV I J
      eI heI eJ heJ ⟨a, ha⟩
  have hI := ker_app_eq_of_affineModel i U hU I eI heI
  have hJ := ker_app_eq_of_affineModel j V hV J eJ heJ
  have hchar := isInducedConormalSheafMap_conormalTransitivityMap i j p h U hU V hV hUV I J
    eI heI eJ heJ
  have key := fun c : J => hchar c ⟨(p.appLE V U hUV).hom (c : Γ(Y, V)), hmem _ c.2⟩ rfl
  have hex : ∀ x, ∃ a : J, (Stacks.Conormal.affineConormalIsoCotangent j V hV J eJ heJ).inv.hom
      (J.toCotangent a) = x := fun x => by
    obtain ⟨a, ha⟩ := J.toCotangent_surjective
      ((Stacks.Conormal.affineConormalIsoCotangent j V hV J eJ heJ).hom.hom x)
    refine ⟨a, ?_⟩
    rw [ha]
    exact (ModuleCat.hom_comp_apply (Stacks.Conormal.affineConormalIsoCotangent j V hV J eJ heJ).hom
        (Stacks.Conormal.affineConormalIsoCotangent j V hV J eJ heJ).inv x).symm.trans
      (ModuleCat.hom_apply_congr
        (Stacks.Conormal.affineConormalIsoCotangent j V hV J eJ heJ).hom_inv_id x)
  intro x y hxy
  obtain ⟨a, hx⟩ := hex x
  obtain ⟨a', hy⟩ := hex y
  have h3 : (Stacks.Conormal.affineConormalIsoCotangent i U hU I eI heI).inv.hom
        (I.toCotangent ⟨(p.appLE V U hUV).hom (a : Γ(Y, V)), hmem _ a.2⟩) =
      (Stacks.Conormal.affineConormalIsoCotangent i U hU I eI heI).inv.hom
        (I.toCotangent ⟨(p.appLE V U hUV).hom (a' : Γ(Y, V)), hmem _ a'.2⟩) := by
    rw [← key a, ← key a', hx, hy, hxy]
  rw [← hx, ← hy,
    toCotangent_eq_of_appLE_toCotangent_eq i j p h U V hV hVc hUV hVeq
      (hfs U V hU hV hUV) I J hI hJ hmem a a'
      (injective_iso_inv (Stacks.Conormal.affineConormalIsoCotangent i U hU I eI heI) h3)]

/-- **Exactness on the left of the conormal sequence of two immersions.** For immersions
`i : Z ⟶ X` and `j : Z ⟶ Y` in a commutative triangle `i ≫ p = j`, the canonical map
`𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of [Stacks, Tag 067L] is a monomorphism as soon as `p` induces a formally
smooth ring map on every compatible pair of affine opens.

The transpose of the map along `(𝟙 Z)^* ⊣ (𝟙 Z)_*` is a monomorphism by
`mono_conormalTransitivitySections`, and it is the composite of the map with two isomorphisms:
the unit of that adjunction and the identification of pullback along an identity with the
identity functor. -/
theorem mono_conormalTransitivityMap_of_formallySmooth
    (hfs : ∀ (U : X.Opens) (V : Y.Opens), IsAffineOpen U → IsAffineOpen V →
      ∀ hUV : U ≤ p ⁻¹ᵁ V, (p.appLE V U hUV).hom.FormallySmooth)
    (h : i ≫ p = j) : Mono (conormalTransitivityMap i j p h) := by
  have hmono := mono_conormalTransitivitySections i j p hfs h
  rw [conormalTransitivitySections_eq] at hmono
  have hrf : (Stacks.PullbackPseudofunctor.modulePullbackIdIso
        Z.toLocallyRingedSpace.toRingedSpace).hom.app (Stacks.Conormal.conormalSheaf j) ≫
      (modulePullbackPushforwardAdjunction
          (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).unit.app (Stacks.Conormal.conormalSheaf j) =
      𝟙 ((modulePullback (Scheme.Hom.toLRSHom (𝟙 Z)).toShHom).obj
        (Stacks.Conormal.conormalSheaf j)) := by
    rw [unit_id_eq]
    exact Iso.hom_inv_id_app _ _
  have hrf' : (pullbackIdIso Z).inv.app (Stacks.Conormal.conormalSheaf j) ≫
      (pullbackIdIso Z).hom.app (Stacks.Conormal.conormalSheaf j) =
      𝟙 (Stacks.Conormal.conormalSheaf j) :=
    Iso.inv_hom_id_app _ _
  exact mono_of_comp_mono hrf' (mono_of_comp_mono hrf hmono)

/-- **[Stacks, Tag 06AB], exactness on the left.** For immersions `i : Z ⟶ X` and `j : Z ⟶ Y`
in a commutative triangle `i ≫ p = j` with `p` smooth, the canonical map
`𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of [Stacks, Tag 067L] is a monomorphism.

A smooth morphism induces a smooth, hence formally smooth, ring map on every compatible pair of
affine opens, so this is `mono_conormalTransitivityMap_of_formallySmooth`. -/
@[stacks 06AB "exactness on the left, that is, that the first arrow `𝒞_{Z/Y} ⟶ 𝒞_{Z/X}` of the
sequence of 067L is a monomorphism. Exactness at `𝒞_{Z/X}` and surjectivity onto `i^*Ω_{X/Y}`
are the content of 067L and are not restated here; they are proved in the modules named in the
module docstring, which also says where the second arrow of the sequence is."]
theorem mono_conormalTransitivityMap [Smooth p] (h : i ≫ p = j) :
    Mono (conormalTransitivityMap i j p h) :=
  mono_conormalTransitivityMap_of_formallySmooth i j p
    (fun _ _ hU hV hUV => (p.smooth_appLE hV hU hUV).formallySmooth) h

end Mono

end Stacks.ConormalSequenceTwoImmersions

end
