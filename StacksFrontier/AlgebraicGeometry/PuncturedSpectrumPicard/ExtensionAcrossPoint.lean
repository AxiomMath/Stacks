module

public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.FinitePresentationModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleFinitePresentation
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.ExtensionToPuncturedSpectrum
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extending an invertible module across one point of an open of an affine scheme

Let `A` be a ring, `U` an open of `Spec A`, `𝔭 ∈ U` a point and `V = U ∖ {𝔭}`.  The one-point
extension step of [Stacks, Tag 0F2F] asserts that if the punctured spectrum of `A_𝔭` has trivial
Picard group then `Pic(U) ⟶ Pic(V)` is surjective; it is carried as the hypothesis
`Stacks.PuncturedSpectrumPicard.PicardExtendsAcrossPoint` by
`StacksFrontier/AlgebraicGeometry/PuncturedSpectrumPicard/ExtensionToPuncturedSpectrum.lean`.

This file proves it.  The argument glues the given invertible module on `V` with the *trivial*
module on `Spec 𝒪_{U, 𝔭}` — the glueing is possible because `Pic` of the punctured spectrum of
`A_𝔭` is trivial, so the two restrictions to the punctured local scheme, both invertible, have
the same Picard class there and are therefore isomorphic — and feeds the resulting glueing datum
to [Stacks, Tag 0F21], formalized in this library as
`AlgebraicGeometry.GlueingNearPoint.moduleGlueingEquivalenceNearClosedPoint`.  What comes back is
a module of finite presentation on `U`, and it is invertible because invertibility descends along
the fpqc covering `(U ∖ {𝔭}) ⊔ Spec 𝒪_{U, 𝔭} ⟶ U` that [Stacks, Tag 0F21] is built from.

## Main definitions

* `Stacks.PuncturedSpectrumPicard.SchemeInvertibleModules`: the invertible sheaves of modules on
  a scheme, the category whose skeleton is `Stacks.Picard.ofScheme`.
* `Stacks.PuncturedSpectrumPicard.finitePresentationOfInvertible`: **the `Pic`-versus-finite
  presentation translation.**  An invertible module on a scheme, read as an object of
  `AlgebraicGeometry.GlueingNearPoint.FinitePresentationModules`, the category in which
  [Stacks, Tag 0F21] is stated.
* `Stacks.PuncturedSpectrumPicard.stalkIsoLocalizationAtPrime`: **the identification
  `𝒪_{U, 𝔭} ≅ A_𝔭`** for `U` an open of `Spec A`.
* `Stacks.PuncturedSpectrumPicard.puncturedLocalSchemeIso`: that identification carried to
  punctured spectra, `Spec 𝒪_{U, 𝔭} ∖ {𝔭} ≅ Spec A_𝔭 ∖ {𝔭}`.
* `Stacks.PuncturedSpectrumPicard.puncturedOpenIsoOfCoeEqSdiff`: the identification of `V` with
  the open complement of `𝔭` taken inside the scheme `U`, over `U`.

## Main results

* `Stacks.PuncturedSpectrumPicard.nonempty_iso_picardUnitObj`: a scheme with trivial Picard
  group has only the trivial invertible module, which is what makes the glueing datum of the
  argument exist.
* `Stacks.PuncturedSpectrumPicard.subsingleton_picard_of_schemeIso`: triviality of the Picard
  group transfers along an isomorphism of schemes.
* `Stacks.PuncturedSpectrumPicard.subsingleton_picard_puncturedLocalScheme`: hypothesis (2) of
  [Stacks, Tag 0F2F] — triviality of `Pic` of the punctured spectrum of `A_𝔭` — read at the
  punctured local scheme of `U` at `𝔭`, which is where [Stacks, Tag 0F21] needs it.
* `Stacks.PuncturedSpectrumPicard.preimage_puncturedOpen_fromSpecStalk`: the punctured local
  scheme of `S` at a closed point `s` is the open complement of the closed point of
  `Spec 𝒪_{S, s}`.
* `Stacks.PuncturedSpectrumPicard.quasiCompact_ι_of_noetherianSpace`: the side condition of
  [Stacks, Tag 0F21] holds for every open of a Noetherian scheme.
* `Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_homOfLE_of_puncturedOpen`: the
  conclusion of `PicardExtendsAcrossPoint` for one `(V, U, 𝔭)` follows from the same statement
  with `U ∖ {𝔭}` read inside the scheme `U`, which is the shape [Stacks, Tag 0F21] speaks in.
* `Stacks.PuncturedSpectrumPicard.isInvertible_of_puncturedCover`: invertibility is local on the
  punctured cover of a closed point.
* `Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_puncturedOpen`: the one-point
  extension for a closed point of an arbitrary scheme.
* `Stacks.PuncturedSpectrumPicard.picardExtendsAcrossPoint`:
  **`PicardExtendsAcrossPoint` for a Noetherian ring**, the carried input of
  [Stacks, Tag 0F2F].

## Implementation notes

**No bridge is needed between the two pullback functors.**  Picard classes are pulled back by
`Stacks.Picard.pullbackClass`, which is built from the ringed-space pullback
`Stacks.RingedSpace.pullbackFunctor`, whereas the restriction functors of
`AlgebraicGeometry.GlueingNearPoint.moduleGlueingDataNearPoint` are Mathlib's
`AlgebraicGeometry.Scheme.Modules.pullback`.  The two are *definitionally* equal — both are
`CategoryTheory.SheafOfModules.pullback` of the same morphism of sheaves of rings — so an
isomorphism of invertible modules produced from an equality of Picard classes is already a
comparison morphism of a glueing datum.  Likewise the ambient categories need no bridge: the
sheaf of rings over which `Stacks.Picard.ofScheme` is formed is definitionally the scheme's own
`ringCatSheaf`, which is what `Stacks.PuncturedSpectrumPicard.invertibleToModules` records.

**Noetherian is used only for the side condition of [Stacks, Tag 0F21].**  That tag asks the
inclusion of the open complement of the point to be quasi-compact, which for an open of
`Spec A` with `A` Noetherian is automatic.  Nothing else in the argument needs it, and
`surjective_schemePullbackClass_puncturedOpen` is stated for an arbitrary scheme with that side
condition as a hypothesis.

## References

* [Stacks Project, Tag 0F2F](https://stacks.math.columbia.edu/tag/0F2F)
* [Stacks Project, Tag 0F21](https://stacks.math.columbia.edu/tag/0F21)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing

universe u

namespace Stacks.PuncturedSpectrumPicard

/-! ### Invertible modules and modules of finite presentation -/

section Translation

variable (X : Scheme.{u})

/-- The category of invertible sheaves of modules on a scheme, the category whose skeleton is
the Picard group `Stacks.Picard.ofScheme`. -/
abbrev SchemeInvertibleModules :=
  Stacks.SheafOfModules.InvertibleModules X.toRingedSpace.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace)

variable {X}

/-- An invertible sheaf of modules on a scheme, read as a sheaf of modules on that scheme.  The
sheaf of rings over which `Stacks.Picard.ofScheme` is formed is the scheme's own sheaf of rings,
so no transport is involved. -/
def invertibleToModules (L : SchemeInvertibleModules X) : X.Modules := L.obj

instance isFinitePresentation_invertibleToModules (L : SchemeInvertibleModules X) :
    (invertibleToModules L).IsFinitePresentation :=
  Stacks.SheafOfModules.isFinitePresentation_of_isInvertible_ringedSpace
    X.toRingedSpace L.obj L.property

/-- **An invertible module is a module of finite presentation.**  This is the translation
between `Stacks.Picard.ofScheme`, which is built from invertible sheaves of modules, and
`AlgebraicGeometry.GlueingNearPoint.FinitePresentationModules`, the category in which
[Stacks, Tag 0F21] is stated. -/
def finitePresentationOfInvertible (L : SchemeInvertibleModules X) :
    GlueingNearPoint.FinitePresentationModules X :=
  ⟨invertibleToModules L, isFinitePresentation_invertibleToModules L⟩

@[simp]
theorem finitePresentationOfInvertible_obj (L : SchemeInvertibleModules X) :
    (finitePresentationOfInvertible L).obj = invertibleToModules L := rfl

end Translation

/-! ### Triviality of a Picard group -/

section Trivial

variable {X : Scheme.{u}}

/-- **A scheme with trivial Picard group has only the trivial invertible module.**  Two
invertible modules are isomorphic as soon as their Picard classes agree, and in a subsingleton
Picard group they always do. -/
theorem nonempty_iso_picardUnitObj (hX : Subsingleton (Stacks.Picard.ofScheme X))
    (L : SchemeInvertibleModules X) :
    Nonempty (L ≅ Stacks.SheafOfModules.picardUnitObj X.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace)) := by
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff X.toRingedSpace.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) L.obj
    (Stacks.SheafOfModules.picardUnitObj X.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace)).obj L.property
    (Stacks.SheafOfModules.picardUnitObj X.toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace)).property).1 (hX.allEq _ _)
  exact ⟨ObjectProperty.isoMk _ e⟩

/-- **Triviality of the Picard group transfers along an isomorphism of schemes**, pullback along
an isomorphism being injective. -/
theorem subsingleton_picard_of_schemeIso {Y : Scheme.{u}} (e : X ≅ Y)
    (hY : Subsingleton (Stacks.Picard.ofScheme Y)) :
    Subsingleton (Stacks.Picard.ofScheme X) :=
  ⟨fun _ _ => schemePullbackClass_injective_of_iso e.symm (hY.allEq _ _)⟩

end Trivial

/-! ### Quasi-compactness of an open inclusion in a Noetherian scheme -/

/-- **An open inclusion into a Noetherian topological space is quasi-compact**, every subset of
a Noetherian space being compact.  This is the side condition of [Stacks, Tag 0F21]. -/
@[ega "0 2.2.4" "special case"]
theorem quasiCompact_ι_of_noetherianSpace {S : Scheme.{u}} [NoetherianSpace S] (V : S.Opens) :
    QuasiCompact V.ι := by
  refine ⟨fun W _ _ => ?_⟩
  have : NoetherianSpace (V : Set S) := NoetherianSpace.set _
  exact NoetherianSpace.isCompact (α := (V : Set S)) _

/-! ### The punctured local scheme at a point -/

section LocalScheme

/-- The point of the open subscheme `U` of `Spec A` determined by a prime `𝔭 ∈ U`. -/
def pointOfMem {A : Type u} [CommRing A] (U : (Spec (CommRingCat.of A)).Opens)
    {p : PrimeSpectrum A} (hp : p ∈ U) : U.toScheme := ⟨p, hp⟩

/-- **An isomorphism of local rings is a local homomorphism**, being surjective. -/
theorem isLocalHom_hom_of_isIso {R S : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing S]
    (f : R ⟶ S) [IsIso f] : IsLocalHom f.hom :=
  IsLocalHom.of_surjective _ (ConcreteCategory.bijective_of_isIso f).2

/-- **An isomorphism of local rings matches up the closed points of their spectra.** -/
theorem preimage_singleton_closedPoint {R S : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing S]
    (f : R ⟶ S) [IsIso f] :
    (Spec.map f) ⁻¹' ({closedPoint R} : Set (Spec R)) = {closedPoint S} := by
  have hf : IsLocalHom f.hom := isLocalHom_hom_of_isIso f
  have hinv : IsLocalHom (inv f).hom := isLocalHom_hom_of_isIso (inv f)
  have hid : Spec.map f ≫ Spec.map (inv f) = CategoryTheory.CategoryStruct.id (Spec S) := by
    rw [← Spec.map_comp, IsIso.inv_hom_id, Spec.map_id]
  have hleft : ∀ q : Spec S, Spec.map (inv f) (Spec.map f q) = q := by
    intro q
    rw [← Scheme.Hom.comp_apply, hid]
    rfl
  ext q
  simp only [Set.mem_preimage]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← hleft q, h]
    exact Spec_closedPoint
  · rw [h]
    exact Spec_closedPoint

/-- **An isomorphism of local rings carries punctured spectra to punctured spectra.** -/
theorem preimage_puncturedOpen_specMap {R S : CommRingCat.{u}} [IsLocalRing R] [IsLocalRing S]
    (f : R ⟶ S) [IsIso f] :
    Spec.map f ⁻¹ᵁ GlueingNearPoint.puncturedOpen (isClosed_singleton_closedPoint R) =
      GlueingNearPoint.puncturedOpen (isClosed_singleton_closedPoint S) := by
  refine TopologicalSpace.Opens.ext ?_
  change (Spec.map f) ⁻¹' ({closedPoint R} : Set (Spec R))ᶜ =
    ({closedPoint S} : Set (Spec S))ᶜ
  rw [Set.preimage_compl, preimage_singleton_closedPoint]

/-- **The punctured local scheme of `S` at `s` is the open complement of the closed point of
`Spec 𝒪_{S, s}`.**  The morphism `Spec 𝒪_{S, s} ⟶ S` is a preimmersion, hence injective on
points, and it sends the closed point to `s`. -/
theorem preimage_puncturedOpen_fromSpecStalk {S : Scheme.{u}} {s : S}
    (hs : IsClosed ({s} : Set S)) :
    S.fromSpecStalk s ⁻¹ᵁ GlueingNearPoint.puncturedOpen hs =
      GlueingNearPoint.puncturedOpen
        (isClosed_singleton_closedPoint (S.presheaf.stalk s)) := by
  refine TopologicalSpace.Opens.ext ?_
  change (S.fromSpecStalk s) ⁻¹' ({s} : Set S)ᶜ =
    ({closedPoint (S.presheaf.stalk s)} : Set (Spec (S.presheaf.stalk s)))ᶜ
  rw [Set.preimage_compl]
  congr 1
  ext q
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  refine ⟨fun h => (S.fromSpecStalk s).isEmbedding.injective
    (h.trans Scheme.fromSpecStalk_closedPoint.symm), fun h => ?_⟩
  rw [h]
  exact Scheme.fromSpecStalk_closedPoint

variable {A : Type u} [CommRing A]

/-- **The local ring of an open of `Spec A` at a point is the localization of `A` at that
prime.**  The stalk of an open subscheme is the stalk of the ambient scheme, and the stalk of
`Spec A` at `𝔭` is `A_𝔭`. -/
@[ega "IV 10.7.3" "partial"]
def stalkIsoLocalizationAtPrime (U : (Spec (CommRingCat.of A)).Opens) (p : PrimeSpectrum A)
    (hp : p ∈ U) :
    U.toScheme.presheaf.stalk (pointOfMem U hp) ≅
      CommRingCat.of (Localization.AtPrime p.asIdeal) :=
  U.stalkIso ⟨p, hp⟩ ≪≫ Spec.stalkIso (CommRingCat.of A) p

/-- **The punctured spectrum of `𝒪_{U, 𝔭}` is the punctured spectrum of `A_𝔭`.** -/
def puncturedLocalSchemeIso (U : (Spec (CommRingCat.of A)).Opens) (p : PrimeSpectrum A)
    (hp : p ∈ U) :
    (Stacks.Divisors.puncturedSpectrum (Localization.AtPrime p.asIdeal)).toScheme ≅
      (GlueingNearPoint.puncturedOpen
        (S := Spec (U.toScheme.presheaf.stalk (pointOfMem U hp)))
        (s := closedPoint (U.toScheme.presheaf.stalk (pointOfMem U hp)))
        (isClosed_singleton_closedPoint
          (U.toScheme.presheaf.stalk (pointOfMem U hp)))).toScheme :=
  (Spec (CommRingCat.of (Localization.AtPrime p.asIdeal))).isoOfEq
      (preimage_puncturedOpen_specMap (stalkIsoLocalizationAtPrime U p hp).hom).symm ≪≫
    asIso (Spec.map (stalkIsoLocalizationAtPrime U p hp).hom ∣_ _)

/-- **Triviality of `Pic` of the punctured spectrum of `A_𝔭` gives triviality of `Pic` of the
punctured local scheme of `U` at `𝔭`.**  This is hypothesis (2) of [Stacks, Tag 0F2F] read where
[Stacks, Tag 0F21] needs it. -/
theorem subsingleton_picard_puncturedLocalScheme (U : (Spec (CommRingCat.of A)).Opens)
    (p : PrimeSpectrum A) (hp : p ∈ U)
    (h : Subsingleton (Stacks.Picard.ofScheme
      (Stacks.Divisors.puncturedSpectrum (Localization.AtPrime p.asIdeal)).toScheme)) :
    Subsingleton (Stacks.Picard.ofScheme (GlueingNearPoint.puncturedOpen
      (S := Spec (U.toScheme.presheaf.stalk (pointOfMem U hp)))
      (s := closedPoint (U.toScheme.presheaf.stalk (pointOfMem U hp)))
      (isClosed_singleton_closedPoint
        (U.toScheme.presheaf.stalk (pointOfMem U hp)))).toScheme) :=
  subsingleton_picard_of_schemeIso (puncturedLocalSchemeIso U p hp).symm h

end LocalScheme

/-! ### The one-point extension statement in the shape of Stacks 0F21 -/

section Reduction

variable {A : Type u} [CommRing A]

/-- **Removing one point of an open of `Spec A` leaves it closed in that open.**  If `V` is the
open `U ∖ {𝔭}` of `Spec A` then the complement of `𝔭` inside the scheme `U` is the preimage of
`V`, which is open. -/
theorem isClosed_singleton_of_coe_eq_sdiff {V U : (Spec (CommRingCat.of A)).Opens}
    {p : PrimeSpectrum A} (hp : p ∈ U)
    (hVeq : (V : Set ↥(Spec (CommRingCat.of A))) =
      (U : Set ↥(Spec (CommRingCat.of A))) \ {p}) :
    IsClosed ({(pointOfMem U hp)} : Set U.toScheme) := by
  rw [← isOpen_compl_iff]
  have hset : ({(pointOfMem U hp)} : Set U.toScheme)ᶜ =
      U.ι ⁻¹' (V : Set ↥(Spec (CommRingCat.of A))) := by
    ext x
    simp only [Set.mem_compl_iff, Set.mem_preimage, hVeq, Set.mem_sdiff]
    refine ⟨fun hx => ⟨x.2, fun hxp => hx (Subtype.ext hxp)⟩, fun hx hxe => ?_⟩
    exact hx.2 (congrArg Subtype.val hxe)
  rw [hset]
  exact V.isOpen.preimage U.ι.continuous

/-- **The open complement of `𝔭` inside `U` has image `V = U ∖ {𝔭}`.** -/
theorem ι_image_puncturedOpen_eq {V U : (Spec (CommRingCat.of A)).Opens}
    {p : PrimeSpectrum A} (hp : p ∈ U)
    (hVeq : (V : Set ↥(Spec (CommRingCat.of A))) =
      (U : Set ↥(Spec (CommRingCat.of A))) \ {p})
    (hs : IsClosed ({(pointOfMem U hp)} : Set U.toScheme)) :
    U.ι ''ᵁ GlueingNearPoint.puncturedOpen hs = V := by
  refine TopologicalSpace.Opens.ext ?_
  change U.ι '' ({(pointOfMem U hp)} : Set U.toScheme)ᶜ =
    (V : Set ↥(Spec (CommRingCat.of A)))
  rw [hVeq]
  ext x
  simp only [Set.mem_image, Set.mem_compl_iff, Set.mem_sdiff]
  refine ⟨?_, fun hx => ⟨⟨x, hx.1⟩, fun hxe => hx.2 (congrArg Subtype.val hxe), rfl⟩⟩
  rintro ⟨y, hy, rfl⟩
  exact ⟨y.2, fun hyp => hy (Subtype.ext hyp)⟩

/-- **The isomorphism `U ∖ {𝔭} ≅ V` over `U`.**  The open complement of `𝔭` taken inside the
scheme `U` and the open `V = U ∖ {𝔭}` of `Spec A` are the same scheme over `U`. -/
def puncturedOpenIsoOfCoeEqSdiff {V U : (Spec (CommRingCat.of A)).Opens}
    {p : PrimeSpectrum A} (hp : p ∈ U)
    (hVeq : (V : Set ↥(Spec (CommRingCat.of A))) =
      (U : Set ↥(Spec (CommRingCat.of A))) \ {p})
    (hs : IsClosed ({(pointOfMem U hp)} : Set U.toScheme)) :
    (GlueingNearPoint.puncturedOpen hs).toScheme ≅ V.toScheme :=
  U.ι.isoImage (GlueingNearPoint.puncturedOpen hs) ≪≫
    (Spec (CommRingCat.of A)).isoOfEq (ι_image_puncturedOpen_eq hp hVeq hs)

/-- The isomorphism `U ∖ {𝔭} ≅ V` is an isomorphism over `U`. -/
theorem puncturedOpenIsoOfCoeEqSdiff_inv_ι {V U : (Spec (CommRingCat.of A)).Opens}
    {p : PrimeSpectrum A} (hp : p ∈ U) (hVU : V ≤ U)
    (hVeq : (V : Set ↥(Spec (CommRingCat.of A))) =
      (U : Set ↥(Spec (CommRingCat.of A))) \ {p})
    (hs : IsClosed ({(pointOfMem U hp)} : Set U.toScheme)) :
    (puncturedOpenIsoOfCoeEqSdiff hp hVeq hs).inv ≫ (GlueingNearPoint.puncturedOpen hs).ι =
      (Spec (CommRingCat.of A)).homOfLE hVU := by
  rw [puncturedOpenIsoOfCoeEqSdiff, Iso.trans_inv, Category.assoc,
    Scheme.Opens.isoImage_ι_inv_ι, Scheme.isoOfEq_inv, Scheme.homOfLE_homOfLE]

/-- **The one-point extension statement in the shape of [Stacks, Tag 0F21].**  For `V` the open
`U ∖ {𝔭}` of `Spec A`, surjectivity of `Pic(U) ⟶ Pic(V)` follows from surjectivity of
`Pic(U) ⟶ Pic(U ∖ {𝔭})` with `U ∖ {𝔭}` read as the open complement of `𝔭` *inside the scheme*
`U`, which is the shape in which [Stacks, Tag 0F21] speaks. -/
theorem surjective_schemePullbackClass_homOfLE_of_puncturedOpen
    {V U : (Spec (CommRingCat.of A)).Opens} {p : PrimeSpectrum A} (hp : p ∈ U) (hVU : V ≤ U)
    (hVeq : (V : Set ↥(Spec (CommRingCat.of A))) =
      (U : Set ↥(Spec (CommRingCat.of A))) \ {p})
    (hs : IsClosed ({(pointOfMem U hp)} : Set U.toScheme))
    (h : Function.Surjective (Stacks.Picard.schemePullbackClass
      (GlueingNearPoint.puncturedOpen hs).ι)) :
    Function.Surjective (Stacks.Picard.schemePullbackClass
      ((Spec (CommRingCat.of A)).homOfLE hVU)) := by
  intro c
  obtain ⟨x, hx⟩ := h (Stacks.Picard.schemePullbackClass
    (puncturedOpenIsoOfCoeEqSdiff hp hVeq hs).hom c)
  refine ⟨x, ?_⟩
  rw [← puncturedOpenIsoOfCoeEqSdiff_inv_ι hp hVU hVeq hs,
    ← Stacks.Picard.schemePullbackClass_comp, hx, Stacks.Picard.schemePullbackClass_comp,
    Iso.inv_hom_id, Stacks.Picard.schemePullbackClass_id]

end Reduction

/-! ### The glueing step -/

section Glueing

/-- Invertibility of a sheaf of modules on a scheme, in the form the Picard group takes. -/
abbrev SchemeIsInvertible (X : Scheme.{u}) (M : X.Modules) : Prop :=
  Stacks.SheafOfModules.IsInvertible X.toRingedSpace.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) M

/-- The Picard class of an invertible sheaf of modules on a scheme. -/
abbrev picardClassOfScheme (X : Scheme.{u}) (M : X.Modules) (hM : SchemeIsInvertible X M) :
    Stacks.Picard.ofScheme X :=
  Stacks.SheafOfModules.picardClass X.toRingedSpace.presheaf
    (Stacks.RingedSpace.structureIsSheaf X.toRingedSpace) M hM

/-- **Invertibility is local on the punctured cover of a closed point.**  A module of finite
presentation on `S` whose restriction to the open complement `S ∖ {s}` and whose restriction
along `Spec 𝒪_{S, s} ⟶ S` are both invertible is itself invertible.

Those two morphisms form an fpqc covering of `S`
(`AlgebraicGeometry.GlueingNearPoint.puncturedCover`), a module of finite presentation is
quasi-coherent, and invertibility descends along an fpqc covering
(`Stacks.Picard.isInvertible_of_pullback_fpqcCover`). -/
theorem isInvertible_of_puncturedCover {S : Scheme.{u}} {s : S} (hs : IsClosed ({s} : Set S))
    [QuasiCompact (GlueingNearPoint.puncturedOpen hs).ι] (M : S.Modules)
    (hfp : M.IsFinitePresentation)
    (h1 : SchemeIsInvertible (GlueingNearPoint.puncturedOpen hs).toScheme
      ((Scheme.Modules.pullback (GlueingNearPoint.puncturedOpen hs).ι).obj M))
    (h2 : SchemeIsInvertible (Spec (S.presheaf.stalk s))
      ((Scheme.Modules.pullback (S.fromSpecStalk s)).obj M)) :
    SchemeIsInvertible S M :=
  Stacks.Picard.isInvertible_of_pullback_fpqcCover M
    (Stacks.Modules.isQuasicoherent_of_isFinitePresentation (h := hfp) M)
    (GlueingNearPoint.puncturedCover hs)
    (fun index => by
      cases index
      · exact h1
      · exact h2)

/-- **The one-point extension of an invertible module, by [Stacks, Tag 0F21].**  Let `s` be a
closed point of a scheme `S` whose open complement has quasi-compact inclusion, and suppose the
punctured local scheme at `s` has trivial Picard group.  Then every invertible module on
`S ∖ {s}` is the restriction of an invertible module on `S`.

The invertible module representing the given class restricts to an invertible module on the
punctured local scheme, as does the trivial module on `Spec 𝒪_{S, s}`; the Picard group there
being trivial, the two restrictions are isomorphic, which is the comparison morphism of a
glueing datum.  [Stacks, Tag 0F21] turns that datum into a module of finite presentation on `S`
restricting to the two of them, and `isInvertible_of_puncturedCover` makes it invertible. -/
theorem surjective_schemePullbackClass_puncturedOpen {S : Scheme.{u}} {s : S}
    (hs : IsClosed ({s} : Set S))
    (hqc : QuasiCompact (GlueingNearPoint.puncturedOpen hs).ι)
    (htriv : Subsingleton (Stacks.Picard.ofScheme
      ((S.fromSpecStalk s) ⁻¹ᵁ GlueingNearPoint.puncturedOpen hs).toScheme)) :
    Function.Surjective (Stacks.Picard.schemePullbackClass
      (GlueingNearPoint.puncturedOpen hs).ι) := by
  have := hqc
  intro c
  let L := finitePresentationOfInvertible (Stacks.Picard.picardRepresentative
    (GlueingNearPoint.puncturedOpen hs).toScheme.toRingedSpace c)
  let H := finitePresentationOfInvertible (Stacks.SheafOfModules.picardUnitObj
    (Spec (S.presheaf.stalk s)).toRingedSpace.presheaf
    (Stacks.RingedSpace.structureIsSheaf (Spec (S.presheaf.stalk s)).toRingedSpace))
  have hL : SchemeIsInvertible (GlueingNearPoint.puncturedOpen hs).toScheme L.obj :=
    (Stacks.Picard.picardRepresentative
      (GlueingNearPoint.puncturedOpen hs).toScheme.toRingedSpace c).property
  have hH : SchemeIsInvertible (Spec (S.presheaf.stalk s)) H.obj :=
    (Stacks.SheafOfModules.picardUnitObj
      (Spec (S.presheaf.stalk s)).toRingedSpace.presheaf
      (Stacks.RingedSpace.structureIsSheaf (Spec (S.presheaf.stalk s)).toRingedSpace)).property
  have h1 : SchemeIsInvertible
      ((S.fromSpecStalk s ⁻¹ᵁ GlueingNearPoint.puncturedOpen hs)).toScheme
      ((Scheme.Modules.pullback (S.fromSpecStalk s ∣_ GlueingNearPoint.puncturedOpen hs)).obj
        L.obj) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of
      (S.fromSpecStalk s ∣_ GlueingNearPoint.puncturedOpen hs).toLRSHom.toShHom _ hL
  have h2 : SchemeIsInvertible
      ((S.fromSpecStalk s ⁻¹ᵁ GlueingNearPoint.puncturedOpen hs)).toScheme
      ((Scheme.Modules.pullback
          (S.fromSpecStalk s ⁻¹ᵁ GlueingNearPoint.puncturedOpen hs).ι).obj H.obj) :=
    Stacks.RingedSpace.modulePullback_isInvertible_of
      (S.fromSpecStalk s ⁻¹ᵁ GlueingNearPoint.puncturedOpen hs).ι.toLRSHom.toShHom _ hH
  obtain ⟨α⟩ := (Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ h1 h2).1 (htriv.allEq _ _)
  let D : GlueingNearPoint.moduleGlueingDataNearPoint S
      (GlueingNearPoint.puncturedOpen hs) s :=
    ⟨{ left := L, right := H, hom := α.hom }, α.isIso_hom⟩
  let E := GlueingNearPoint.moduleGlueingEquivalenceNearClosedPoint S s hs hqc
  let M : GlueingNearPoint.FinitePresentationModules S := E.inverse.obj D
  let eD : E.functor.obj M ≅ D := E.counitIso.app D
  let eL : (Scheme.Modules.pullback (GlueingNearPoint.puncturedOpen hs).ι).obj M.obj ≅ L.obj :=
    (ObjectProperty.ι _).mapIso
      ((GlueingNearPoint.moduleOpenComponent S (GlueingNearPoint.puncturedOpen hs) s).mapIso eD)
  let eH : (Scheme.Modules.pullback (S.fromSpecStalk s)).obj M.obj ≅ H.obj :=
    (ObjectProperty.ι _).mapIso
      ((GlueingNearPoint.moduleLocalComponent S (GlueingNearPoint.puncturedOpen hs) s).mapIso eD)
  have hMinv : SchemeIsInvertible S M.obj :=
    isInvertible_of_puncturedCover hs M.obj M.property
      (by have := hL; exact Stacks.SheafOfModules.isInvertible_of_iso _ _ eL.symm)
      (by have := hH; exact Stacks.SheafOfModules.isInvertible_of_iso _ _ eH.symm)
  refine ⟨picardClassOfScheme S M.obj hMinv, ?_⟩
  rw [← Stacks.Picard.classOf_picardRepresentative
    (GlueingNearPoint.puncturedOpen hs).toScheme.toRingedSpace c]
  exact (Stacks.Picard.pullbackClass_classOf
    (GlueingNearPoint.puncturedOpen hs).ι.toLRSHom.toShHom M.obj hMinv).trans
    ((Stacks.SheafOfModules.picardClass_eq_iff _ _ _ _ _ _).2 ⟨eL⟩)

end Glueing

/-! ### The one-point extension step for an open of an affine scheme -/

section Main

/-- **The one-point extension step of [Stacks, Tag 0F2F].**  For `A` a Noetherian ring, `U` an
open of `Spec A`, `𝔭 ∈ U` and `V = U ∖ {𝔭}`: if the punctured spectrum of `A_𝔭` has trivial
Picard group then `Pic(U) ⟶ Pic(V)` is surjective.

This is the input that
`StacksFrontier/AlgebraicGeometry/PuncturedSpectrumPicard/ExtensionToPuncturedSpectrum.lean`
carries as the hypothesis `PicardExtendsAcrossPoint`.  `V` is the open complement of `𝔭` taken
inside the scheme `U` (`surjective_schemePullbackClass_homOfLE_of_puncturedOpen`), the side
condition of [Stacks, Tag 0F21] holds because `Spec A` is a Noetherian space
(`quasiCompact_ι_of_noetherianSpace`), the punctured local scheme of `U` at `𝔭` is the punctured
spectrum of `A_𝔭` (`preimage_puncturedOpen_fromSpecStalk`,
`subsingleton_picard_puncturedLocalScheme`), and the extension itself is
`surjective_schemePullbackClass_puncturedOpen`. -/
theorem picardExtendsAcrossPoint (A : Type u) [CommRing A] [IsNoetherianRing A] :
    PicardExtendsAcrossPoint A := by
  intro V U p hp hVU hVeq htriv
  have hs : IsClosed ({pointOfMem U hp} : Set U.toScheme) :=
    isClosed_singleton_of_coe_eq_sdiff hp hVeq
  refine surjective_schemePullbackClass_homOfLE_of_puncturedOpen hp hVU hVeq hs ?_
  have hns : NoetherianSpace U.toScheme :=
    NoetherianSpace.set (U : Set ↥(Spec (CommRingCat.of A)))
  refine surjective_schemePullbackClass_puncturedOpen hs
    (quasiCompact_ι_of_noetherianSpace _) ?_
  rw [preimage_puncturedOpen_fromSpecStalk hs]
  exact subsingleton_picard_puncturedLocalScheme U p hp htriv

end Main

/-! ### Stacks 0F2F with the one-point extension step discharged -/

section Tag

variable {A : Type u} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] {f : A}

/-- **Stacks 0F2F, with the one-point extension step discharged.**  Surjectivity of
`Pic(U) ⟶ Pic(U₀)` for the punctured spectrum `U` of a Noetherian local ring `A` and the
punctured spectrum `U₀` of `A/fA`.

This is `Stacks.PuncturedSpectrumPicard.surjective_schemePullbackClass_puncturedClosedFibre`
with its `hstep` hypothesis supplied by `picardExtendsAcrossPoint`, so the only input still
granted is the conclusion of [Stacks, Tag 0F2D]. -/
@[stacks 0F2F "GRANTED, and not proved here, ONE input: h0F2D, the conclusion of Stacks 0F2D \
for (A,f), carried as Stacks.PuncturedSpectrumPicard.PicardColimitSurjective — the predicate \
the restricted 0F2D of StacksFrontier.AlgebraicGeometry.PuncturedSpectrumPicard.FormalTower \
states unproved and explicitly disclaims, so that tag's restriction is inherited here. The \
source's other input, `By Limits, Lemma 0F21 applied n times`, is NO LONGER granted: the \
one-point step is proved as Stacks.PuncturedSpectrumPicard.picardExtendsAcrossPoint and \
supplied here. Clause (2) of the source is h2, transcribed with the two standard \
identifications performed in the statement: a maximal ideal of A_f is a prime 𝔭 of A with \
f ∉ 𝔭 maximal among such, and (A_f)_𝔭 = A_𝔭 = Localization.AtPrime 𝔭"]
theorem surjective_schemePullbackClass_puncturedClosedFibre_of_isNoetherianRing
    (hf : f ∈ maximalIdeal A) (h0F2D : PicardColimitSurjective A f)
    (h2 : ∀ p : PrimeSpectrum A, f ∉ p.asIdeal →
      (∀ q : PrimeSpectrum A, p.asIdeal < q.asIdeal → f ∈ q.asIdeal) →
      Subsingleton (Stacks.Picard.ofScheme
        (Stacks.Divisors.puncturedSpectrum (Localization.AtPrime p.asIdeal)).toScheme)) :
    Function.Surjective (Stacks.Picard.schemePullbackClass
      (morphismRestrict (Stacks.Algebraization.closedImmersion A f)
        (Stacks.Divisors.puncturedSpectrum A))) :=
  surjective_schemePullbackClass_puncturedClosedFibre hf (picardExtendsAcrossPoint A) h0F2D h2

end Tag

end Stacks.PuncturedSpectrumPicard

end
