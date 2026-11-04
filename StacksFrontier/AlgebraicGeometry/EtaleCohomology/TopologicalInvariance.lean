module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Affine.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.TwoOutOfThree
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.Isomorphism
public import StacksFrontier.AlgebraicGeometry.Topologies.EtaleUniversalHomeomorphism
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Topological invariance of the small étale site: the fully faithful half

Let `g : S' ⟶ S` be a universal homeomorphism and let `X` be a scheme étale over `S`. Base
change along `g` is then a bijection from the `S`-morphisms `Y ⟶ X` to the `S'`-morphisms
between the base changes, for an arbitrary scheme `Y` over `S`. Equivalently, base change along
a universal homeomorphism is a fully faithful functor between the small étale sites.

The injectivity half is already available: an `S`-morphism into a scheme étale over `S` is
determined by its restriction along any surjection onto `S`. The content added here is
surjectivity, and it rests on a single geometric statement about sections. Let `p : W ⟶ U` be
étale and let `j : U' ⟶ U` be a universal homeomorphism. A section of the base change of `p`
along `j` is the same thing as a section of `p`: a section of an étale morphism is an open
immersion, and the base change `W ×_U U' ⟶ W` of `j` is a homeomorphism, so the image of the
section transports to an open subscheme `Z ⊆ W`. The structure morphism `Z ⟶ U` is then étale
and a universal homeomorphism — the latter because the section identifies `W ×_U U' ⊇ Z ×_U U'`
with `U'` — hence an isomorphism, and its inverse is the desired section of `p`.

Essential surjectivity, which would upgrade this to the equivalence of étale sites of Stacks
Project, Tag 04DZ, is *not* proved here; it needs effectivity of étale descent along a
surjective integral morphism (Stacks Project, Tag 0BTP).

## Main results

* `Stacks.Etale.existsUnique_section_of_universalHomeomorphism` — a section of an étale
  morphism, prescribed after a universal homeomorphism of the base, exists and is unique.
* `Stacks.Etale.surjective_baseChange_hom_of_universalHomeomorphism` — base change along a
  universal homeomorphism is surjective on morphisms into an étale scheme.
* `Stacks.Etale.bijective_baseChange_hom_of_universalHomeomorphism` — it is bijective. This is
  Stacks Project, Tag 0BTY.
* `Stacks.Etale.etalePullback_faithful_of_universalHomeomorphism` and
  `Stacks.Etale.etalePullback_full_of_universalHomeomorphism` — the base-change functor between
  small étale sites is fully faithful.

## Implementation notes

Schemes over a base are objects of the over category and base change is
`CategoryTheory.Over.pullback`; the small étale site is Mathlib's `AlgebraicGeometry.Scheme.Etale`
and the functor between two of them is `CategoryTheory.MorphismProperty.Over.pullback` for the
morphism property `AlgebraicGeometry.Etale`. The two instance arguments that functor needs are
supplied inline, as `AlgebraicGeometry.Etale` is stable under base change but the corresponding
`HasPullbacksAlong` instance is not found by unification.

A section of an étale morphism is a split monomorphism and is itself étale, hence flat, locally
of finite presentation and a monomorphism, so `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`
applies. The transport of the open subscheme is done with `CategoryTheory.Limits.pullback.fst`
rather than with a chosen open immersion, so that the resulting open subscheme of `W` is cut out
by the set-theoretic image of the section and `AlgebraicGeometry.isPullback_morphismRestrict`
exhibits its base change as a base change of that projection.

## References

* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open AlgebraicGeometry

/-- **Sections of an étale morphism are a topological invariant.** Let `p : W ⟶ U` be étale and
let `j : U' ⟶ U` be a universal homeomorphism. Every morphism `U' ⟶ W` lying over `j` is the
restriction along `j` of a unique section of `p`.

This is the geometric content of the fully faithful half of the topological invariance of the
small étale site, Stacks Project, Tag 0BTY. -/
theorem existsUnique_section_of_universalHomeomorphism
    {U U' W : Scheme.{u}} (j : U' ⟶ U) [UniversalHomeomorphism j]
    (p : W ⟶ U) [Etale p] (σ' : U' ⟶ W) (hσp : σ' ≫ p = j) :
    ∃! σ : U ⟶ W, σ ≫ p = 𝟙 U ∧ j ≫ σ = σ' := by
  -- The base change of `p` along `j`, and the section of it determined by `σ'`.
  set k := pullback.fst p j
  set p' := pullback.snd p j
  set s : U' ⟶ pullback p j := pullback.lift σ' (𝟙 U') (by rw [hσp, Category.id_comp])
  have hsk : s ≫ k = σ' := pullback.lift_fst _ _ _
  have hsp : s ≫ p' = 𝟙 U' := pullback.lift_snd _ _ _
  -- A section of an étale morphism is an open immersion.
  have : IsSplitMono s := IsSplitMono.mk' ⟨p', hsp⟩
  have : Etale (s ≫ p') := by rw [hsp]; infer_instance
  have : Etale s := Etale.of_comp s p'
  have : IsOpenImmersion s := IsOpenImmersion.of_flat_of_mono s
  -- The base change of `j` along `p` is a homeomorphism, so the image of the section is open.
  have hkUH : UniversalHomeomorphism k := by
    rw [universalHomeomorphism_iff]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback p j).flip
      ((universalHomeomorphism_iff j).mp inferInstance)
  have hkh : IsHomeomorph k.base := hkUH.universally_isHomeomorph _ _ _ .of_id_snd
  set Z : W.Opens := ⟨k.base '' Set.range s.base, hkh.isOpenMap _ s.isOpenEmbedding.isOpen_range⟩
  have hrange : Set.range s.base = Set.range ((k ⁻¹ᵁ Z).ι).base := by
    rw [Scheme.Opens.range_ι]
    exact (Set.preimage_image_eq _ hkh.injective).symm
  set e : U' ≅ (k ⁻¹ᵁ Z).toScheme :=
    IsOpenImmersion.isoOfRangeEq s (k ⁻¹ᵁ Z).ι hrange
  have hefac : e.hom ≫ (k ⁻¹ᵁ Z).ι = s :=
    IsOpenImmersion.isoOfRangeEq_hom_fac _ _ hrange
  -- `Z ⟶ U` is étale and a universal homeomorphism, hence an isomorphism.
  set q : Z.toScheme ⟶ U := Z.ι ≫ p with hq_def
  set τ : U' ⟶ Z.toScheme := e.hom ≫ (k ∣_ Z) with hτ_def
  have hτι : τ ≫ Z.ι = σ' := by
    rw [hτ_def, Category.assoc, morphismRestrict_ι, ← Category.assoc, hefac, hsk]
  have hτq : τ ≫ q = j := by rw [hq_def, ← Category.assoc, hτι, hσp]
  have hkZ : UniversalHomeomorphism (k ∣_ Z) := by
    rw [universalHomeomorphism_iff]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (isPullback_morphismRestrict k Z).flip ((universalHomeomorphism_iff k).mp hkUH)
  have h3 : MorphismProperty.HasTwoOutOfThreeProperty
      (@UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u}) := inferInstance
  have : MorphismProperty.IsStableUnderComposition
      (@UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u}) :=
    h3.toIsStableUnderComposition
  have : MorphismProperty.HasOfPrecompProperty
      (@UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u})
      (@UniversalHomeomorphism.{u} : MorphismProperty Scheme.{u}) :=
    h3.toHasOfPrecompProperty
  have hτUH : UniversalHomeomorphism τ :=
    MorphismProperty.comp_mem _ _ _ (AlgebraicGeometry.universalHomeomorphism_of_isIso e.hom) hkZ
  have : UniversalHomeomorphism q :=
    MorphismProperty.of_precomp (W := @UniversalHomeomorphism)
      (W' := @UniversalHomeomorphism) τ q hτUH (by rw [hτq]; infer_instance)
  have : Etale q := by rw [hq_def]; infer_instance
  have : IsIso q := isIso_of_weaklyEtale_of_universalHomeomorphism q
  have hjinv : j ≫ inv q ≫ Z.ι = σ' := by
    rw [← hτq, Category.assoc, Category.assoc, IsIso.hom_inv_id_assoc, ← Category.assoc]
    exact hτι
  refine ⟨inv q ≫ Z.ι, ⟨?_, hjinv⟩, ?_⟩
  · rw [Category.assoc, ← hq_def]
    exact IsIso.inv_hom_id q
  · rintro σ ⟨hσ, hjσ⟩
    refine hom_ext_of_surjective j (surjective_of_universalHomeomorphism j).surj p σ
      (inv q ≫ Z.ι) ?_ ?_
    · rw [hσ, Category.assoc, ← hq_def, IsIso.inv_hom_id]
    · rw [hjσ, hjinv]

/-- **Stacks Project, Tag 0BTY**, surjectivity. Base change along a universal homeomorphism
`g : S' ⟶ S` is surjective on morphisms from an arbitrary scheme over `S` to a scheme étale
over `S`. -/
@[sga "3 X 2.0" "fullness"]
theorem surjective_baseChange_hom_of_universalHomeomorphism
    {S S' : Scheme.{u}} (g : S' ⟶ S) [UniversalHomeomorphism g] (X Y : Over S) [Etale X.hom] :
    Function.Surjective (fun f : Y ⟶ X => (Over.pullback g).map f) := by
  intro φ
  have hφw : φ.left ≫ pullback.snd X.hom g = pullback.snd Y.hom g := by
    simpa only [Over.pullback_obj_hom] using φ.w
  -- Base change along `g` of the structure morphism of `Y` is a universal homeomorphism.
  have hjUH : UniversalHomeomorphism (pullback.fst Y.hom g) := by
    rw [universalHomeomorphism_iff]
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback Y.hom g).flip
      ((universalHomeomorphism_iff g).mp inferInstance)
  have hcond : (φ.left ≫ pullback.fst X.hom g) ≫ X.hom =
      pullback.fst Y.hom g ≫ Y.hom := by
    calc (φ.left ≫ pullback.fst X.hom g) ≫ X.hom
        = (φ.left ≫ pullback.snd X.hom g) ≫ g := by
          rw [Category.assoc, Category.assoc, pullback.condition]
      _ = pullback.snd Y.hom g ≫ g := by rw [hφw]
      _ = pullback.fst Y.hom g ≫ Y.hom := pullback.condition.symm
  set σ' : pullback Y.hom g ⟶ pullback X.hom Y.hom :=
    pullback.lift (φ.left ≫ pullback.fst X.hom g) (pullback.fst Y.hom g) hcond
  have hσ'fst : σ' ≫ pullback.fst X.hom Y.hom = φ.left ≫ pullback.fst X.hom g :=
    pullback.lift_fst _ _ _
  have hσ'snd : σ' ≫ pullback.snd X.hom Y.hom = pullback.fst Y.hom g :=
    pullback.lift_snd _ _ _
  obtain ⟨σ, ⟨hσ, hjσ⟩, -⟩ := existsUnique_section_of_universalHomeomorphism
    (pullback.fst Y.hom g) (pullback.snd X.hom Y.hom) σ' hσ'snd
  have hψ : (σ ≫ pullback.fst X.hom Y.hom) ≫ X.hom = Y.hom := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hσ, Category.id_comp]
  set ψ : Y ⟶ X := Over.homMk (σ ≫ pullback.fst X.hom Y.hom) hψ
  have hψleft : ψ.left = σ ≫ pullback.fst X.hom Y.hom := rfl
  refine ⟨ψ, ?_⟩
  show (Over.pullback g).map ψ = φ
  have hmapfst : ((Over.pullback g).map ψ).left ≫ pullback.fst X.hom g =
      pullback.fst Y.hom g ≫ ψ.left := by
    show (pullback.lift (pullback.fst Y.hom g ≫ ψ.left) (pullback.snd Y.hom g) _) ≫
      pullback.fst X.hom g = _
    exact pullback.lift_fst _ _ _
  have hmapsnd : ((Over.pullback g).map ψ).left ≫ pullback.snd X.hom g =
      pullback.snd Y.hom g := by
    show (pullback.lift (pullback.fst Y.hom g ≫ ψ.left) (pullback.snd Y.hom g) _) ≫
      pullback.snd X.hom g = _
    exact pullback.lift_snd _ _ _
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · rw [hmapfst, hψleft, ← Category.assoc, hjσ, hσ'fst]
  · rw [hmapsnd, hφw]

/-- **Stacks Project, Tag 0BTY.** Let `g : S' ⟶ S` be a universal homeomorphism and let `X` be
a scheme étale over `S`. For every scheme `Y` over `S`, base change along `g` is a bijection
from the `S`-morphisms `Y ⟶ X` to the `S'`-morphisms between the base changes of `Y` and `X`. -/
@[stacks 0BTY, ega "IV 18.1.3" "more general", sga "3 X 2.0" "full faithfulness"]
theorem bijective_baseChange_hom_of_universalHomeomorphism
    {S S' : Scheme.{u}} (g : S' ⟶ S) [UniversalHomeomorphism g] (X Y : Over S) [Etale X.hom] :
    Function.Bijective (fun f : Y ⟶ X => (Over.pullback g).map f) :=
  ⟨injective_baseChange_hom_of_universalHomeomorphism g X Y,
    surjective_baseChange_hom_of_universalHomeomorphism g X Y⟩

/-- Base change along a universal homeomorphism `f : X ⟶ Y` is a faithful functor from the
small étale site of `Y` to the small étale site of `X`. -/
theorem etalePullback_faithful_of_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f] :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show Y.Etale ⥤ X.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ f).Faithful := by
  have : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let F : Y.Etale ⥤ X.Etale :=
    MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ f
  show F.Faithful
  have key : ∀ {A B : Y.Etale} (c : A ⟶ B), (Scheme.Etale.forget X).map (F.map c) =
      (Over.pullback f).map ((Scheme.Etale.forget Y).map c) := fun _ => rfl
  refine ⟨fun {A B} a b hab => ?_⟩
  have : Etale ((Scheme.Etale.forget Y).obj B).hom := B.prop
  apply (Scheme.Etale.forgetFullyFaithful Y).map_injective
  refine injective_baseChange_hom_of_universalHomeomorphism f
    ((Scheme.Etale.forget Y).obj B) ((Scheme.Etale.forget Y).obj A) ?_
  show (Over.pullback f).map ((Scheme.Etale.forget Y).map a) =
    (Over.pullback f).map ((Scheme.Etale.forget Y).map b)
  rw [← key a, ← key b, hab]

/-- Base change along a universal homeomorphism `f : X ⟶ Y` is a full functor from the small
étale site of `Y` to the small étale site of `X`. -/
theorem etalePullback_full_of_universalHomeomorphism
    {X Y : Scheme.{u}} (f : X ⟶ Y) [UniversalHomeomorphism f] :
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) f :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show Y.Etale ⥤ X.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ f).Full := by
  have : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) f := ⟨fun _ _ ↦ inferInstance⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) f :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  let F : Y.Etale ⥤ X.Etale :=
    MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ f
  show F.Full
  have key : ∀ {A B : Y.Etale} (c : A ⟶ B), (Scheme.Etale.forget X).map (F.map c) =
      (Over.pullback f).map ((Scheme.Etale.forget Y).map c) := fun _ => rfl
  refine ⟨fun {A B} c => ?_⟩
  have : Etale ((Scheme.Etale.forget Y).obj B).hom := B.prop
  obtain ⟨h, hh⟩ := surjective_baseChange_hom_of_universalHomeomorphism f
    ((Scheme.Etale.forget Y).obj B) ((Scheme.Etale.forget Y).obj A)
    ((Scheme.Etale.forget X).map c)
  refine ⟨(Scheme.Etale.forgetFullyFaithful Y).preimage h, ?_⟩
  apply (Scheme.Etale.forgetFullyFaithful X).map_injective
  rwa [key, (Scheme.Etale.forgetFullyFaithful Y).map_preimage]

end Stacks.Etale

end

end
