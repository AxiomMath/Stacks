module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSource.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
public import StacksFrontier.RingTheory.Etale.Height

/-!
# Properties of algebraic spaces defined by properties of schemes

Let `P` be a property of schemes which is local for the étale topology. An algebraic space
over `S` *has* `P` when it admits a surjective étale atlas by a scheme having `P`. This
condition does not depend on the atlas: it holds for one surjective étale atlas exactly
when every étale scheme over the space has `P`. For a representable algebraic space it is
`P` of the representing scheme.

Among the properties the source lists as being local in the étale topology is the dimension
of the local ring at a point, which for an étale ring map is unchanged on corresponding
primes.

## Main definitions

* `AlgebraicGeometry.Space.HasEtaleLocalProperty`: an algebraic space has an étale-local
  property of schemes.

## Main results

* `AlgebraicGeometry.Space.exists_atlas_iff_forall_etale`: the condition is
  independent of the atlas.
* `AlgebraicGeometry.Space.exists_atlas_iff_of_representable`: for a representable
  algebraic space the condition is the property of the representing scheme.
* `AlgebraicGeometry.Space.hasEtaleLocalProperty_of_representable`: the easy direction of
  that equivalence, which needs no locality hypothesis.

## Implementation notes

Locality is `CategoryTheory.ObjectProperty.IsLocal` for
`AlgebraicGeometry.Scheme.etalePrecoverage`, which gives both halves of what the two results need:
the property passes to an étale scheme over one having it, and it descends along a surjective étale
morphism. Those two directions are isolated as the first two private lemmas below; the remaining
private lemmas are the bookkeeping that turns a relative morphism property on a
Yoneda-representable morphism into the corresponding property of the underlying scheme morphism.

The definition is an abbreviation, so a client which has produced an atlas can use the
characterizations without an unfolding lemma, and the statements of the two results are
phrased with it for the same reason.

## References

* [Stacks Project, Tag 03E6](https://stacks.math.columbia.edu/tag/03E6)
* [Stacks Project, Tag 03E8](https://stacks.math.columbia.edu/tag/03E8)
* [Stacks Project, Tag 0BBL](https://stacks.math.columbia.edu/tag/0BBL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry.Space

/-- An étale-local property of schemes passes from the target of an étale morphism to its
source. -/
private theorem property_of_etale_map {P : ObjectProperty Scheme.{u}}
    [P.IsLocal Scheme.etalePrecoverage] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hf : Etale f) (hY : P Y) : P X := by
  let Z : Bool → Scheme.{u} := fun | true => X | false => Y
  let g : ∀ i, Z i ⟶ Y := fun | true => f | false => 𝟙 Y
  have hcover : Presieve.ofArrows Z g ∈ Scheme.etalePrecoverage Y := by
    show Presieve.ofArrows Z g ∈ Scheme.precoverage (fun X Y f => Etale f) Y
    rw [Scheme.ofArrows_mem_precoverage_iff (P := fun X Y f => Etale f)]
    refine ⟨fun y => ⟨false, y, rfl⟩, ?_⟩
    rintro (_ | _)
    · infer_instance
    · exact hf
  exact ObjectProperty.IsLocal.component (P := P) hcover f
    (Presieve.ofArrows.mk true) hY

/-- An étale-local property of schemes descends along a surjective étale morphism. -/
private theorem property_of_surjective_etale_map {P : ObjectProperty Scheme.{u}}
    [P.IsLocal Scheme.etalePrecoverage] {X Y : Scheme.{u}}
    (f : X ⟶ Y) (hs : Surjective f) (he : Etale f) (hX : P X) : P Y := by
  have hcover : Presieve.singleton f ∈ Scheme.etalePrecoverage Y := by
    show Presieve.singleton f ∈ Scheme.precoverage (fun X Y f => Etale f) Y
    rw [Scheme.singleton_mem_precoverage_iff (P := fun X Y f => Etale f)]
    exact ⟨hs.surj, he⟩
  apply ObjectProperty.of_presieve (P := P) hcover
  rintro Z g ⟨rfl⟩
  exact hX

/-- An étale-local property of schemes descends along a surjective étale presheaf morphism, given a
pullback square whose source has the property. -/
private theorem property_of_surjective_etale_presheaf_map {P : ObjectProperty Scheme.{u}}
    [P.IsLocal Scheme.etalePrecoverage] {C : Type v} [Category.{u} C] (T : C ⥤ Scheme.{u})
    {U V W : C} {A : Cᵒᵖ ⥤ Type u} {f : yoneda.obj U ⟶ A} {g : yoneda.obj V ⟶ A}
    (hfₛ : (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) T).presheaf f)
    (hfₑ : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf f)
    (q : W ⟶ U) (r : W ⟶ V) (hpb : IsPullback (yoneda.map q) (yoneda.map r) f g)
    (hW : P (T.obj W)) : P (T.obj V) :=
  property_of_surjective_etale_map (T.map r) (hfₛ.property g _ r hpb) (hfₑ.property g _ r hpb) hW

/-- A relative morphism property is unchanged by postcomposition with an isomorphism of
presheaves. -/
private theorem presheaf_postcompose_iso_iff
    (Q : MorphismProperty Scheme.{u}) {C : Type v} [Category.{u} C]
    (T : C ⥤ Scheme.{u})
    {A B D : Cᵒᵖ ⥤ Type u} (f : A ⟶ B) (e : B ≅ D) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage Q T)) f ↔
      (MorphismProperty.presheaf (MorphismProperty.inverseImage Q T)) (f ≫ e.hom) :=
  (MorphismProperty.presheaf (MorphismProperty.inverseImage Q T)).arrow_mk_iso_iff
    (Arrow.isoMk (Iso.refl A) e (by simp))

/-- An isomorphism of presheaves has every relative morphism property whose underlying
scheme property holds for isomorphisms. -/
private theorem presheaf_property_of_iso
    (Q : MorphismProperty Scheme.{u}) {C : Type v} [Category.{u} C]
    (T : C ⥤ Scheme.{u}) (hQiso : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsIso f → Q f)
    {A D : Cᵒᵖ ⥤ Type u} (e : A ≅ D) :
    (MorphismProperty.presheaf (MorphismProperty.inverseImage Q T)) e.hom := by
  refine ⟨Functor.relativelyRepresentable.of_isIso yoneda e.hom,
    fun _ _ _ _ snd hpb => ?_⟩
  have : IsIso (yoneda.map snd) := hpb.isIso_snd_of_isIso
  have : IsIso snd := Functor.FullyFaithful.isIso_of_isIso_map Yoneda.fullyFaithful snd
  exact hQiso (T.map snd) inferInstance

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
variable (P : ObjectProperty Scheme.{u}) [P.IsLocal Scheme.etalePrecoverage]

/-- **Stacks 03E6.** An algebraic space has an étale-local property of schemes if it has a
surjective étale atlas by a scheme with that property. -/
@[stacks 03E6]
abbrev HasEtaleLocalProperty : Prop :=
  ∃ (U : BigFppfOver B S hS) (f : yoneda.obj U ⟶ F),
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f ∧
    (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) f ∧
    P ((BigFppfOver.toScheme B S hS).obj U)

/-- **Stacks 03E8.** An étale-local property holds on some surjective étale atlas exactly
when it holds on every étale scheme over the algebraic space. -/
@[stacks 03E8 "equivalence of atlas conditions"]
theorem exists_atlas_iff_forall_etale (hF : IsAlgebraicSpace B S hS F) :
    HasEtaleLocalProperty B S hS F P ↔
    (∀ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ F),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) g →
      P ((BigFppfOver.toScheme B S hS).obj V)) := by
  let T := BigFppfOver.toScheme B S hS
  let _ : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  constructor
  · rintro ⟨U, f, hfₛ, hfₑ, hPU⟩ V g hgₑ
    have hgRep : yoneda.relativelyRepresentable g :=
      (Functor.relativelyRepresentable.diag_iff (F := yoneda) (X := F)).mp
        hF.diagonal_representable g
    let p := hgRep.fst f
    let q := hgRep.snd f
    have hpull := hgRep.isPullback f
    let r : hgRep.pullback f ⟶ V := yoneda.preimage p
    have hrMap : yoneda.map r = p := yoneda.map_preimage p
    exact property_of_surjective_etale_presheaf_map T hfₛ hfₑ q r
      (by simpa [hrMap] using hpull.flip)
      (property_of_etale_map (T.map q) (hgₑ.property f p q hpull) hPU)
  · intro h
    obtain ⟨U, f, hfₛ, hfₑ⟩ := hF.exists_atlas
    exact ⟨U, f, hfₛ, hfₑ, h U f hfₑ⟩

omit [P.IsLocal Scheme.etalePrecoverage] in
/-- A presheaf isomorphic to one represented by an object of the site has an étale-local
property of schemes as soon as the underlying scheme of that object has it: the isomorphism
is itself a surjective étale atlas.

This is the easy direction of the representable case of Stacks 03E8, and unlike the other
direction it uses no locality of the property. It is what makes
`AlgebraicGeometry.Space.HasEtaleLocalProperty` usable for a property whose étale locality is
not available in this library. -/
theorem hasEtaleLocalProperty_of_representable
    (X : BigFppfOver B S hS) (e : F ≅ yoneda.obj X)
    (hX : P ((BigFppfOver.toScheme B S hS).obj X)) :
    HasEtaleLocalProperty B S hS F P :=
  ⟨X, e.inv, presheaf_property_of_iso (@Surjective.{u}) _ (fun _ _ => inferInstance) e.symm,
    presheaf_property_of_iso (@Etale.{u}) _ (fun _ _ => inferInstance) e.symm, hX⟩

/-- **Stacks 03E8.** For a represented algebraic space, the atlas condition is equivalent
to the property of its representing scheme. -/
@[stacks 03E8 "representable case"]
theorem exists_atlas_iff_of_representable
    (X : BigFppfOver B S hS) (e : F ≅ yoneda.obj X) :
    HasEtaleLocalProperty B S hS F P ↔ P ((BigFppfOver.toScheme B S hS).obj X) := by
  let T := BigFppfOver.toScheme B S hS
  refine ⟨fun ⟨U, f, hfₛ, hfₑ, hPU⟩ => ?_,
    hasEtaleLocalProperty_of_representable B S hS F P X e⟩
  let m : U ⟶ X := yoneda.preimage (f ≫ e.hom)
  have hm : yoneda.map m = f ≫ e.hom := yoneda.map_preimage (f ≫ e.hom)
  exact property_of_surjective_etale_presheaf_map T ((presheaf_postcompose_iso_iff _ T f e).mp hfₛ)
    ((presheaf_postcompose_iso_iff _ T f e).mp hfₑ) (𝟙 U) m
    (by simpa [hm] using IsPullback.of_id_fst (f := yoneda.map m)) hPU

end AlgebraicGeometry.Space

/-! ### Dimension of the local rings

The dimension of the local ring at a point is one of the properties the source records as
local in the étale topology: an étale ring map identifies the Krull dimension of the
localizations at corresponding primes, which is the stronger form of that assertion. -/

add_to_stacks 0BBL "dimension" RingHom.Etale.ringKrullDim_localization_atPrime_eq

end
