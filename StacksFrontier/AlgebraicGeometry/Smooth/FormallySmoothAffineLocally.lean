module

public import StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothCriterion
public import StacksFrontier.RingTheory.LocalProperties.FormallySmooth
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Formal smoothness read off affine opens

Stacks 0D0F states that four conditions on a morphism of schemes `f : X ⟶ Y` are equivalent:

1. `f` is formally smooth, i.e. has the infinitesimal lifting property;
2. every point of `X` has an open neighbourhood `V`, mapping into an open `U ⊆ Y`, with
   `f|_V : V ⟶ U` formally smooth;
3. for every pair of affine opens `U ⊆ Y`, `V ⊆ X` with `f(V) ⊆ U` the ring map
   `Γ(Y, U) ⟶ Γ(X, V)` is formally smooth;
4. there is an affine open covering `Y = ⋃ Uⱼ` and, for each `j`, an affine open covering
   `f⁻¹(Uⱼ) = ⋃ Vⱼᵢ` with every `Γ(Y, Uⱼ) ⟶ Γ(X, Vⱼᵢ)` formally smooth.

Conditions (3) and (4) are properties of the ring maps `f` induces on sections, so they are
captured by `AlgebraicGeometry.affineLocally` applied to `RingHom.FormallySmooth`; that is the
morphism property `Stacks.Smooth.FormallySmoothAffineLocally` defined here. The equivalence
(3) ⟺ (4) then comes from `RingHom.FormallySmooth.propertyIsLocal`.

**What is proved here, and what is not.** Conditions (3) and (4) are proved equivalent, and
condition (1) is proved to imply them (hence also (2), trivially, and (4)). The implication
back from (3) or (4) to (1) is *not* proved **in this file**. It is proved elsewhere, and the
tag is registered there: `Stacks.Smooth.formallySmooth_tfae` in
`StacksFrontier.AlgebraicGeometry.Smooth.FormallySmoothTFAE` carries
`@[stacks 0D0F "all four criteria, for an arbitrary morphism of schemes"]`, unconditionally.
Its `3 → 1` is `Stacks.Smooth.formallySmooth_of_formallySmooth_appLE`, the source's torsor
argument, whose pseudo-torsor `Stacks.Smooth.isLiftPseudoTorsor` is assembled from the two
*unrestricted* clauses of [Stacks Project, Tag 04FJ]
(`Stacks.Thickenings.exists_addAction_compatibleLifts` and
`Stacks.Thickenings.existsUnique_compatibleLiftsVAdd_eq`). **Nothing in this file carries
`@[stacks 0D0F]`** because the tag asserts the equivalence of all four conditions and only part
of it is proved here — not because the remaining implication is unavailable.

## Main definitions

* `Stacks.Smooth.FormallySmoothAffineLocally` is `affineLocally RingHom.FormallySmooth`: the
  property of inducing a formally smooth ring map on sections over affine opens.

## Main results

* `Stacks.Smooth.formallySmoothAffineLocally_iff_appLE`: the property is condition (3), read on
  all pairs of affine opens.
* `Stacks.Smooth.formallySmoothAffineLocally_iff_exists_affineCovers`: the property is condition
  (4), the existence of one pair of compatible affine coverings. Together with the previous
  statement this is the implication (3) ⟺ (4) of Stacks 0D0F.
* `Stacks.Smooth.formallySmoothAffineLocally_iff_exists_appLE`: the property can be checked at
  each point of the source, on one pair of affine opens around it.
* `Stacks.Smooth.formallySmoothAffineLocally_of_formallySmooth`: condition (1) implies condition
  (3), hence also (4). This is the implication (1) ⟹ (3) of Stacks 0D0F.
* `Stacks.Smooth.exists_formallySmooth_resLE_of_formallySmooth`: condition (1) implies
  condition (2), by `Stacks.Smooth.FormallySmooth.resLE` with `V = X` and `U = Y`.
* `Stacks.Smooth.FormallySmooth.resLE_of_le`: a restriction of a formally smooth restriction is
  formally smooth, Stacks 02H3 for a restricted morphism.
* `Stacks.Smooth.formallySmoothAffineLocally_of_exists_formallySmooth_resLE`: condition (2)
  implies condition (3), hence also (4). This is the implication (2) ⟹ (4) of Stacks 0D0F.
* `Stacks.Smooth.formallySmooth_iff_formallySmoothAffineLocally_of_isAffineHom`: for an **affine**
  morphism all four conditions are equivalent. The affineness hypothesis is not in Stacks 0D0F.
* `Stacks.Smooth.smooth_iff_formallySmoothAffineLocally`: a morphism is smooth exactly when it is
  affine-locally formally smooth and locally of finite presentation, Stacks 02H6 with formal
  smoothness read on affine opens.

## Implementation notes

The name records what is proved: `FormallySmoothAffineLocally` is defined by conditions (3)
and (4) and is *not* known to agree with the lifting property `Stacks.Smooth.FormallySmooth`, so
it must not be called `FormallySmooth`.

`AlgebraicGeometry.HasRingHomProperty` packages the whole local theory of such a property, given
that the underlying ring property is local; the instance below supplies
`RingHom.FormallySmooth.propertyIsLocal` for that. From it, `iff_appLE` is condition (3) verbatim
and `iff_exists_appLE` is the pointwise form of condition (2) with affine opens; condition (4) is
derived from the pointwise form in both directions, the forward direction using that the affine
opens contained in a given open cover it.

The implication (1) ⟹ (3) is `Stacks.Smooth.FormallySmooth.resLE` — formal smoothness passes to
restrictions, which is Stacks 02H3 — followed by the affine dictionary
`Stacks.Smooth.formallySmooth_iff_of_isAffine` and the identification
`AlgebraicGeometry.arrowResLEAppIso` of `(f.resLE U V e).appTop` with `f.appLE U V e`.

## References

* [Stacks Project, Tag 0D0F](https://stacks.math.columbia.edu/tag/0D0F)
* [Stacks Project, Tag 02H3](https://stacks.math.columbia.edu/tag/02H3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Smooth

/-- A morphism of schemes is **affine-locally formally smooth** when the ring map it induces on
sections over any pair of affine opens `V ⊆ f⁻¹(U)` is formally smooth. These are conditions (3)
and (4) of Stacks 0D0F; the equivalence with the lifting property
`Stacks.Smooth.FormallySmooth`, condition (1), is not proved here. -/
def FormallySmoothAffineLocally : MorphismProperty Scheme.{u} :=
  affineLocally @RingHom.FormallySmooth

/-- `FormallySmoothAffineLocally` is the morphism property of schemes associated with the local
ring-map property `RingHom.FormallySmooth`. -/
instance : HasRingHomProperty (@FormallySmoothAffineLocally.{u}) @RingHom.FormallySmooth :=
  ⟨RingHom.FormallySmooth.propertyIsLocal, rfl⟩

/-- **Condition (3) of Stacks 0D0F.** A morphism is affine-locally formally smooth exactly when
`Γ(Y, U) ⟶ Γ(X, V)` is a formally smooth ring map for every pair of affine opens `U ⊆ Y`,
`V ⊆ X` with `f(V) ⊆ U`. -/
theorem formallySmoothAffineLocally_iff_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FormallySmoothAffineLocally f ↔
      ∀ (U : Y.affineOpens) (V : X.affineOpens) (e : V.1 ≤ f ⁻¹ᵁ U.1),
        RingHom.FormallySmooth (f.appLE U.1 V.1 e).hom :=
  HasRingHomProperty.iff_appLE

/-- A morphism is affine-locally formally smooth exactly when every point of the source has an
affine open neighbourhood `V`, inside the preimage of an affine open `U` of the target, with
`Γ(Y, U) ⟶ Γ(X, V)` formally smooth. This is the pointwise form of condition (2) of
Stacks 0D0F, with the local condition read on sections. -/
theorem formallySmoothAffineLocally_iff_exists_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FormallySmoothAffineLocally f ↔
      ∀ x : X, ∃ (U : Y.affineOpens) (V : X.affineOpens) (_ : x ∈ V.1)
        (e : V.1 ≤ f ⁻¹ᵁ U.1), RingHom.FormallySmooth (f.appLE U.1 V.1 e).hom :=
  HasRingHomProperty.iff_exists_appLE
    (RingHom.FormallySmooth.stableUnderComposition.stableUnderCompositionWithLocalizationAway
      RingHom.FormallySmooth.holdsForLocalizationAway).left

/-- A point of an open `W` of a scheme lies in an affine open contained in `W`. -/
private theorem exists_affineOpen_mem_le {X : Scheme.{u}} {W : X.Opens} {x : X} (hx : x ∈ W) :
    ∃ V : X.affineOpens, x ∈ V.1 ∧ V.1 ≤ W := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  exact ⟨⟨V, hV⟩, hxV, hVW⟩

/-- Every open of a scheme is covered by the affine opens it contains. -/
private theorem le_iSup_affineOpens_le (X : Scheme.{u}) (W : X.Opens) :
    W ≤ ⨆ V : {V : X.affineOpens // V.1 ≤ W}, V.1.1 := by
  intro x hx
  obtain ⟨V, hxV, hVW⟩ := exists_affineOpen_mem_le hx
  exact Opens.mem_iSup.mpr ⟨⟨V, hVW⟩, hxV⟩

/-- **Condition (4) of Stacks 0D0F, and its equivalence with condition (3).** A morphism is
affine-locally formally smooth — equivalently, satisfies condition (3) by
`Stacks.Smooth.formallySmoothAffineLocally_iff_appLE` — exactly when there is *one* affine open
covering `Y = ⋃ Uⱼ` together with, for each `j`, an affine open covering `f⁻¹(Uⱼ) = ⋃ Vⱼᵢ` such
that every `Γ(Y, Uⱼ) ⟶ Γ(X, Vⱼᵢ)` is formally smooth. -/
theorem formallySmoothAffineLocally_iff_exists_affineCovers {X Y : Scheme.{u}} (f : X ⟶ Y) :
    FormallySmoothAffineLocally f ↔
      ∃ (J : Type u) (U : J → Y.affineOpens) (I : J → Type u) (V : ∀ j, I j → X.affineOpens)
        (e : ∀ j i, (V j i).1 ≤ f ⁻¹ᵁ (U j).1),
        (⨆ j, (U j).1 = ⊤) ∧ (∀ j, f ⁻¹ᵁ (U j).1 ≤ ⨆ i, (V j i).1) ∧
          ∀ j i, RingHom.FormallySmooth (f.appLE (U j).1 (V j i).1 (e j i)).hom := by
  constructor
  · intro H
    rw [formallySmoothAffineLocally_iff_appLE] at H
    exact ⟨Y.affineOpens, id, fun U ↦ {V : X.affineOpens // V.1 ≤ f ⁻¹ᵁ U.1},
      fun _ V ↦ V.1, fun _ V ↦ V.2, iSup_affineOpens_eq_top Y,
      fun U ↦ le_iSup_affineOpens_le X (f ⁻¹ᵁ U.1), fun U V ↦ H U V.1 V.2⟩
  · rintro ⟨J, U, I, V, e, hU, hV, H⟩
    rw [formallySmoothAffineLocally_iff_exists_appLE]
    intro x
    have hx : f.base x ∈ (⨆ j, (U j).1 : Y.Opens) := hU ▸ Opens.mem_top _
    obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hx
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hV j hj)
    exact ⟨U j, V j i, hi, e j i, H j i⟩

/-- Over a pair of affine opens the lifting property for the restriction of `f` is formal
smoothness of the ring map on sections. -/
private theorem ringHom_formallySmooth_appLE {X Y : Scheme.{u}} (f : X ⟶ Y) {U : Y.Opens}
    {V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) (e : V ≤ f ⁻¹ᵁ U)
    (h : FormallySmooth (f.resLE U V e)) : RingHom.FormallySmooth (f.appLE U V e).hom := by
  have : IsAffine (U : Scheme.{u}) := hU
  have : IsAffine (V : Scheme.{u}) := hV
  exact (RingHom.FormallySmooth.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f U V e)).mp
    ((formallySmooth_iff_of_isAffine _).mp h)

/-- **(1) ⟹ (3) of Stacks 0D0F.** A formally smooth morphism of schemes induces a formally
smooth ring map on sections over every pair of affine opens `V ⊆ f⁻¹(U)`, hence is
affine-locally formally smooth. Combined with
`Stacks.Smooth.formallySmoothAffineLocally_iff_exists_affineCovers` this also gives
(1) ⟹ (4). -/
theorem formallySmoothAffineLocally_of_formallySmooth {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : FormallySmooth f) : FormallySmoothAffineLocally f :=
  (formallySmoothAffineLocally_iff_appLE f).mpr fun U V e ↦
    ringHom_formallySmooth_appLE f U.2 V.2 e (hf.resLE e)

/-- A restriction of a formally smooth restriction is formally smooth: a lift over
`f.resLE U V e` automatically factors through the smaller open `V₀` of the source, because a
first-order thickening of affine schemes is surjective on points. This is Stacks 02H3 for the
restricted morphism. -/
theorem FormallySmooth.resLE_of_le {X Y : Scheme.{u}} {f : X ⟶ Y} {U : Y.Opens} {V : X.Opens}
    {e : V ≤ f ⁻¹ᵁ U} (hf : FormallySmooth (f.resLE U V e)) {U₀ : Y.Opens} {V₀ : X.Opens}
    (hU : U₀ ≤ U) (hV : V₀ ≤ V) (e₀ : V₀ ≤ f ⁻¹ᵁ U₀) :
    FormallySmooth (f.resLE U₀ V₀ e₀) := by
  have hsq : X.homOfLE hV ≫ f.resLE U V e = f.resLE U₀ V₀ e₀ ≫ Y.homOfLE hU := by
    rw [Scheme.Hom.map_resLE, Scheme.Hom.resLE_map]
  intro R A φ hφ hφ2 g h hcomm
  obtain ⟨k, hk1, hk2⟩ := hf R A φ hφ hφ2 (g ≫ X.homOfLE hV) (h ≫ Y.homOfLE hU)
    (by rw [Category.assoc, hsq, ← Category.assoc, hcomm, Category.assoc])
  have hran : Set.range k.base ⊆ Set.range (X.homOfLE hV).base := by
    rintro y ⟨p, rfl⟩
    obtain ⟨q, rfl⟩ := specMap_base_surjective hφ hφ2 p
    rw [← Scheme.Hom.comp_apply, hk1, Scheme.Hom.comp_apply]
    exact Set.mem_range_self _
  refine ⟨IsOpenImmersion.lift (X.homOfLE hV) k hran, ?_, ?_⟩
  · rw [← cancel_mono (X.homOfLE hV), Category.assoc, IsOpenImmersion.lift_fac, hk1]
  · rw [← cancel_mono (Y.homOfLE hU), Category.assoc, ← hsq, ← Category.assoc,
      IsOpenImmersion.lift_fac, hk2]

/-- **(1) ⟹ (2) of Stacks 0D0F.** A formally smooth morphism satisfies condition (2) with
`V = X` and `U = Y`. -/
theorem exists_formallySmooth_resLE_of_formallySmooth {X Y : Scheme.{u}} {f : X ⟶ Y}
    (hf : FormallySmooth f) (x : X) :
    ∃ (U : Y.Opens) (V : X.Opens) (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
      FormallySmooth (f.resLE U V e) :=
  ⟨⊤, ⊤, Opens.mem_top x, le_top, hf.resLE le_top⟩

/-- **(2) ⟹ (3) of Stacks 0D0F.** If every point of the source has an open neighbourhood `V`
mapping into an open `U` of the target with `f|_V : V ⟶ U` formally smooth, then `f` is
affine-locally formally smooth. Shrinking `U` and `V` to affine opens keeps the restriction
formally smooth, by `Stacks.Smooth.FormallySmooth.resLE_of_le`. -/
theorem formallySmoothAffineLocally_of_exists_formallySmooth_resLE {X Y : Scheme.{u}} (f : X ⟶ Y)
    (H : ∀ x : X, ∃ (U : Y.Opens) (V : X.Opens) (_ : x ∈ V) (e : V ≤ f ⁻¹ᵁ U),
      FormallySmooth (f.resLE U V e)) :
    FormallySmoothAffineLocally f := by
  rw [formallySmoothAffineLocally_iff_exists_appLE]
  intro x
  obtain ⟨U, V, hxV, e, hfs⟩ := H x
  obtain ⟨U₀, hfxU₀, hU₀U⟩ := exists_affineOpen_mem_le (X := Y) (e hxV)
  obtain ⟨V₀, hxV₀, hV₀V⟩ := exists_affineOpen_mem_le (show x ∈ V ⊓ f ⁻¹ᵁ U₀.1 from ⟨hxV, hfxU₀⟩)
  have e₀ : V₀.1 ≤ f ⁻¹ᵁ U₀.1 := hV₀V.trans inf_le_right
  exact ⟨U₀, V₀, hxV₀, e₀, ringHom_formallySmooth_appLE f U₀.2 V₀.2 e₀
    (hfs.resLE_of_le hU₀U (hV₀V.trans inf_le_left) e₀)⟩

/-- **(3) ⟹ (1) of Stacks 0D0F for an affine morphism.** If `f` is an affine morphism and is
affine-locally formally smooth, then it has the infinitesimal lifting property. Base changing to
the affine thickening makes the source affine as well, where the affine dictionary applies, and a
lift is the same thing as a section of the base change.

The affineness hypothesis is what makes this reachable: in general the local lifts have to be
glued, and the gluing is governed by the vanishing of the first cohomology of a quasi-coherent
sheaf on the affine thickening (Stacks 0D0E), which is not available. -/
theorem formallySmooth_of_formallySmoothAffineLocally_of_isAffineHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsAffineHom f] (hf : FormallySmoothAffineLocally f) : FormallySmooth f := by
  have : (@FormallySmoothAffineLocally.{u}).IsStableUnderBaseChange :=
    HasRingHomProperty.isStableUnderBaseChange (P := @FormallySmoothAffineLocally.{u})
      RingHom.FormallySmooth.isStableUnderBaseChange
  intro R A φ hφ hφ2 g h hcomm
  have hsnd : FormallySmooth (pullback.snd f h) :=
    (formallySmooth_iff_of_isAffine _).mpr
      (HasRingHomProperty.iff_of_isAffine.mp (MorphismProperty.pullback_snd f h hf))
  obtain ⟨k, hk1, hk2⟩ :=
    hsnd R A φ hφ hφ2 (pullback.lift g (Spec.map φ) hcomm) (𝟙 _)
      (by rw [Category.comp_id, pullback.lift_snd])
  refine ⟨k ≫ pullback.fst f h, ?_, ?_⟩
  · rw [← Category.assoc, hk1, pullback.lift_fst]
  · rw [Category.assoc, pullback.condition, ← Category.assoc, hk2, Category.id_comp]

/-- **Stacks 0D0F for an affine morphism.** For an affine morphism of schemes the lifting
property, condition (1), is equivalent to conditions (3) and (4); the latter two are
`Stacks.Smooth.formallySmoothAffineLocally_iff_appLE` and
`Stacks.Smooth.formallySmoothAffineLocally_iff_exists_affineCovers`.

This is **not** Stacks 0D0F, which has no affineness hypothesis. -/
theorem formallySmooth_iff_formallySmoothAffineLocally_of_isAffineHom {X Y : Scheme.{u}}
    (f : X ⟶ Y) [IsAffineHom f] :
    FormallySmooth f ↔ FormallySmoothAffineLocally f :=
  ⟨formallySmoothAffineLocally_of_formallySmooth,
    formallySmooth_of_formallySmoothAffineLocally_of_isAffineHom f⟩

/-- **Stacks 02H6 in the affine-local form.** A morphism of schemes is smooth if and only if it
is affine-locally formally smooth and locally of finite presentation. Both sides are read on
pairs of affine opens, where smoothness of a ring map is `RingHom.smooth_def`: formal smoothness
together with finite presentation. -/
@[ega "IV 17.3.1", sga "3 III 2.5" "partial"]
theorem smooth_iff_formallySmoothAffineLocally {X Y : Scheme.{u}} (f : X ⟶ Y) :
    AlgebraicGeometry.Smooth f ↔
      FormallySmoothAffineLocally f ∧ LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.iff_appLE (P := @AlgebraicGeometry.Smooth.{u}),
    formallySmoothAffineLocally_iff_appLE,
    HasRingHomProperty.iff_appLE (P := @LocallyOfFinitePresentation.{u})]
  simp only [RingHom.smooth_def, forall_and]

end Stacks.Smooth

end
