module

public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending morphisms into an étale scheme along a universal homeomorphism

Let `f : X ⟶ Y` be a universal homeomorphism, let `V` be any scheme over `Y` and let `W` be a
scheme étale over `Y`. This file proves Stacks Project Tag 0BTY: base change along `f` is a
bijection from the `Y`-morphisms `V ⟶ W` to the `X`-morphisms between the base changes
`X ×_Y V ⟶ X ×_Y W`.

Injectivity is already available for any surjective `f`, as
`Stacks.Etale.injective_baseChange_hom_of_surjective`. The content added here is surjectivity,
i.e. that every morphism between the base changes descends. The proof does not go through
descent data: it descends the *graph* of the given morphism directly.

Concretely, a `Y`-morphism `V ⟶ W` is a section of the étale morphism `q : W ×_Y V ⟶ V`, and an
`X`-morphism `X ×_Y V ⟶ X ×_Y W` over `X` is the same as a section of the base change of `q`
along the universal homeomorphism `π : X ×_Y V ⟶ V`. So everything reduces to
`Stacks.Etale.exists_section_of_universalHomeomorphism`: a section of an étale morphism descends
along a universal homeomorphism.

## Main results

* `Stacks.Etale.tfae_isOpenImmersion`: Stacks Project, Tag 025G — a morphism of schemes is an
  open immersion exactly when it is universally injective and étale, and exactly when it is a
  flat monomorphism locally of finite presentation.
* `Stacks.Etale.isOpenImmersion_of_etale_of_universallyInjective` and
  `Stacks.Etale.isIso_of_etale_of_universallyInjective_of_surjective`: the two usable forms of
  Tag 025G.
* `Stacks.Etale.universallyInjective_of_comp_of_surjective`: universal injectivity of a
  composite `h ≫ g` with `h` surjective passes to `g`.
* `Stacks.Etale.universalHomeomorphism_of_isPullback`: being a universal homeomorphism is stable
  under base change.
* `Stacks.Etale.exists_section_of_universalHomeomorphism`: a section of an étale morphism
  descends along a universal homeomorphism.
* `Stacks.Etale.exists_hom_of_pullbackHom_of_universalHomeomorphism`: a morphism between the
  base changes of `V` and of an étale `W` along a universal homeomorphism is the base change of
  a `Y`-morphism `V ⟶ W`.
* `Stacks.Etale.bijective_pullbackHom_of_universalHomeomorphism`: Stacks Project, Tag 0BTY.

## Implementation notes

Write `π : X ×_Y V ⟶ V` for the base change of `f` along `V ⟶ Y`; it is again a universal
homeomorphism by `universalHomeomorphism_of_isPullback`. Let `q : E ⟶ V` be étale and let
`s : X ×_Y V ⟶ E` satisfy `s ≫ q = π`, i.e. let `s` be a section of `q` after base change.
The descended section is produced as follows.

The pullback `ρ : E ×_V (X ×_Y V) ⟶ E` of `π` along `q` is a homeomorphism, and `s` factors as
`σ ≫ ρ` where `σ` is the section of the base change `E ×_V (X ×_Y V) ⟶ X ×_Y V` determined by
`s`. A section of an étale morphism is itself étale, by `AlgebraicGeometry.Etale.of_comp`, hence
is an open map; so `Set.range σ` is open and therefore so is `Set.range s = ρ '' Set.range σ`.
Let `U ⊆ E` be that open subscheme. Then `s` factors through `U` by a surjection `h`, and
`g := U.ι ≫ q` satisfies `h ≫ g = π`. Surjectivity of `g` follows from surjectivity of `π`, and
universal injectivity of `g` from universal injectivity of `π` together with surjectivity of
`h`, by `universallyInjective_of_comp_of_surjective`. As `g` is étale, Tag 025G makes it an
isomorphism, and `inv g ≫ U.ι` is the required section.

No descent datum and no cocycle condition appear anywhere: the open subscheme `U` descends
because `ρ` is a homeomorphism, not because of an invariance hypothesis. This is why Tag 0BTY
needs no compatibility assumption on the given morphism, in contrast with descent of morphisms
along a general surjective universally closed morphism (Tag 0BTL).

## References

* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 0BTL](https://stacks.math.columbia.edu/tag/0BTL)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.Etale

/-- **Stacks Project, Tag 025G.** For a morphism of schemes, being an open immersion, being
universally injective and étale, and being a flat monomorphism locally of finite presentation
are all equivalent. -/
@[stacks 025G,
  ega "IV 17.9.1",
  sga "1 I 5.1" "more general",
  sga "3 X 3.7" "partial",
  sga "3 XXII 5.4.10" "Footnote (36)",
  sga "7 IX 3.1.3" "more general"]
theorem tfae_isOpenImmersion {A B : Scheme.{u}} (g : A ⟶ B) :
    List.TFAE [IsOpenImmersion g, UniversallyInjective g ∧ Etale g,
      Flat g ∧ Mono g ∧ LocallyOfFinitePresentation g] := by
  tfae_have 1 → 2 := fun _ => ⟨inferInstance, inferInstance⟩
  tfae_have 2 → 3 := by
    intro ⟨hinj, hetale⟩
    have hdiag : IsIso (pullback.diagonal g) :=
      (isIso_iff_isOpenImmersion_and_surjective _).mpr
        ⟨inferInstance, (UniversallyInjective.iff_diagonal g).mp hinj⟩
    exact ⟨inferInstance, (pullback.isIso_diagonal_iff g).mp hdiag, inferInstance⟩
  tfae_have 3 → 1 := by
    intro ⟨hflat, hmono, hfp⟩
    exact IsOpenImmersion.of_flat_of_mono g
  tfae_finish

/-- **Tag 025G, the direction that is used.** A universally injective étale morphism of schemes
is an open immersion. -/
@[sga "1 I 5.1" "sufficiency"]
theorem isOpenImmersion_of_etale_of_universallyInjective {A B : Scheme.{u}} (g : A ⟶ B)
    [Etale g] [UniversallyInjective g] : IsOpenImmersion g :=
  ((tfae_isOpenImmersion g).out 2 1).mp
    (⟨inferInstance, inferInstance⟩ : UniversallyInjective g ∧ Etale g)

/-- A universally injective, surjective, étale morphism of schemes is an isomorphism: by Tag
025G it is an open immersion, and a surjective open immersion is an isomorphism. -/
@[sga "1 I 5.1" "special case"]
theorem isIso_of_etale_of_universallyInjective_of_surjective {A B : Scheme.{u}} (g : A ⟶ B)
    [Etale g] [UniversallyInjective g] [Surjective g] : IsIso g :=
  (isIso_iff_isOpenImmersion_and_surjective g).mpr
    ⟨isOpenImmersion_of_etale_of_universallyInjective g, inferInstance⟩

/-- **Universal injectivity passes through a surjection on the left.** If `h` is surjective and
`h ≫ g` is universally injective, then `g` is universally injective.

For a base change `g' : B' ⟶ C'` of `g` along `C' ⟶ C`, the base change of `h` along `B' ⟶ B`
is a surjection onto `B'` whose composite with `g'` is a base change of `h ≫ g`, hence is
injective; injectivity of `g'` follows. -/
theorem universallyInjective_of_comp_of_surjective {A B C : Scheme.{u}} (h : A ⟶ B) (g : B ⟶ C)
    [Surjective h] [UniversallyInjective (h ≫ g)] : UniversallyInjective g := by
  rw [universallyInjective_iff]
  intro B' C' i₁ i₂ g' hg'
  have hinj : Function.Injective (pullback.snd h i₁ ≫ g').base :=
    UniversallyInjective.universally_injective _ _ _
      ((IsPullback.of_hasPullback h i₁).flip.paste_horiz hg')
  have hsurj : Surjective (pullback.snd h i₁) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Surjective) (IsPullback.of_hasPullback h i₁) ‹_›
  intro x₁ x₂ hx
  obtain ⟨y₁, rfl⟩ := hsurj.surj x₁
  obtain ⟨y₂, rfl⟩ := hsurj.surj x₂
  exact congrArg _ (hinj (a₁ := y₁) (a₂ := y₂) hx)

/-- Being a universal homeomorphism is stable under base change: any morphism fitting into a
cartesian square over a universal homeomorphism is again one. -/
theorem universalHomeomorphism_of_isPullback {X Y X' Y' : Scheme.{u}} {f : X ⟶ Y}
    [UniversalHomeomorphism f] {i₁ : X' ⟶ X} {i₂ : Y' ⟶ Y} {f' : X' ⟶ Y'}
    (h : IsPullback f' i₁ i₂ f) : UniversalHomeomorphism f' := by
  constructor
  intro A B j₁ j₂ g hg
  exact UniversalHomeomorphism.universally_isHomeomorph _ _ _
    (hg.flip.paste_horiz h.flip).flip

/-- A universal homeomorphism is universally injective. -/
theorem universallyInjective_of_universalHomeomorphism' {V V' : Scheme.{u}} (π : V' ⟶ V)
    [UniversalHomeomorphism π] : UniversallyInjective π := by
  rw [universallyInjective_iff]
  intro X' Y' i₁ i₂ f' hf'
  exact (UniversalHomeomorphism.universally_isHomeomorph i₁ i₂ f' hf').injective

/-- A universal homeomorphism is surjective. -/
theorem surjective_of_universalHomeomorphism' {V V' : Scheme.{u}} (π : V' ⟶ V)
    [UniversalHomeomorphism π] : Surjective π :=
  ⟨(UniversalHomeomorphism.universally_isHomeomorph _ _ _ IsPullback.of_id_snd).surjective⟩

/-- **A section of an étale morphism descends along a universal homeomorphism.** Let
`π : V' ⟶ V` be a universal homeomorphism and let `q : E ⟶ V` be étale. A morphism
`s : V' ⟶ E` with `s ≫ q = π`, that is a section of the base change of `q` along `π`, is the
restriction along `π` of a section of `q` itself.

This is the geometric heart of Stacks Project, Tag 0BTY. -/
theorem exists_section_of_universalHomeomorphism {V V' E : Scheme.{u}} (π : V' ⟶ V)
    [UniversalHomeomorphism π] (q : E ⟶ V) [Etale q] (s : V' ⟶ E) (hs : s ≫ q = π) :
    ∃ t : V ⟶ E, t ≫ q = 𝟙 V ∧ π ≫ t = s := by
  have hπinj : UniversallyInjective π := universallyInjective_of_universalHomeomorphism' π
  have hπsurj : Surjective π := surjective_of_universalHomeomorphism' π
  have hρ : IsHomeomorph (pullback.fst q π).base :=
    UniversalHomeomorphism.universally_isHomeomorph _ _ _ (IsPullback.of_hasPullback q π)
  obtain ⟨σ, hσρ, hσq⟩ : ∃ σ : V' ⟶ pullback q π,
      σ ≫ pullback.fst q π = s ∧ σ ≫ pullback.snd q π = 𝟙 V' :=
    ⟨pullback.lift s (𝟙 V') (by simpa using hs), pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  have hσEtale : Etale σ := by
    have : Etale (σ ≫ pullback.snd q π) := by rw [hσq]; infer_instance
    exact Etale.of_comp σ (pullback.snd q π)
  have hopen : IsOpen (Set.range s.base) := by
    rw [← hσρ]
    simpa [Set.range_comp] using
      hρ.isOpenMap _ (Scheme.Hom.isOpenMap σ).isOpen_range
  set U : E.Opens := ⟨Set.range s.base, hopen⟩ with hU
  have hsub : Set.range s.base ⊆ Set.range U.ι.base := by
    rw [Scheme.Opens.range_ι]
    exact fun x hx => hx
  set h := IsOpenImmersion.lift U.ι s hsub
  have hhU : h ≫ U.ι = s := IsOpenImmersion.lift_fac _ _ _
  have : Surjective h := by
    refine ⟨fun x => ?_⟩
    have hmem : U.ι.base x ∈ Set.range s.base := by
      have hx := Set.mem_range_self (f := U.ι.base) x
      rwa [Scheme.Opens.range_ι] at hx
    obtain ⟨y, hy⟩ := hmem
    refine ⟨y, U.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, hhU]
    exact hy
  have hcomp : h ≫ (U.ι ≫ q) = π := by rw [← Category.assoc, hhU, hs]
  have : Surjective (h ≫ (U.ι ≫ q)) := hcomp ▸ hπsurj
  have : UniversallyInjective (h ≫ (U.ι ≫ q)) := hcomp ▸ hπinj
  have : Surjective (U.ι ≫ q) := Surjective.of_comp h (U.ι ≫ q)
  have : UniversallyInjective (U.ι ≫ q) :=
    universallyInjective_of_comp_of_surjective h (U.ι ≫ q)
  have : IsIso (U.ι ≫ q) := isIso_of_etale_of_universallyInjective_of_surjective _
  refine ⟨inv (U.ι ≫ q) ≫ U.ι, by simp, ?_⟩
  rw [← hcomp]
  simp [hhU]

/-- **Morphisms into an étale scheme descend along a universal homeomorphism.** Let
`f : X ⟶ Y` be a universal homeomorphism, let `v : V ⟶ Y` be arbitrary and let `w : W ⟶ Y` be
étale. Every morphism `α : V ×_Y X ⟶ W ×_Y X` over `X` is induced by a `Y`-morphism
`b : V ⟶ W`.

This is the surjectivity half of Stacks Project, Tag 0BTY. Note that `v` is not assumed étale
and that no compatibility condition is imposed on `α`. -/
theorem exists_hom_of_pullbackHom_of_universalHomeomorphism {X Y V W : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] (v : V ⟶ Y) (w : W ⟶ Y) [Etale w]
    (α : pullback v f ⟶ pullback w f) (hα : α ≫ pullback.snd w f = pullback.snd v f) :
    ∃ b : V ⟶ W, b ≫ w = v ∧ pullback.fst v f ≫ b = α ≫ pullback.fst w f := by
  have hπ : UniversalHomeomorphism (pullback.fst v f) :=
    universalHomeomorphism_of_isPullback (IsPullback.of_hasPullback v f)
  have hcomm : (α ≫ pullback.fst w f) ≫ w = pullback.fst v f ≫ v := by
    calc (α ≫ pullback.fst w f) ≫ w = α ≫ pullback.snd w f ≫ f := by
          rw [Category.assoc, pullback.condition]
      _ = pullback.snd v f ≫ f := by rw [← Category.assoc, hα]
      _ = pullback.fst v f ≫ v := pullback.condition.symm
  obtain ⟨t, ht₁, ht₂⟩ := exists_section_of_universalHomeomorphism (pullback.fst v f)
    (pullback.snd w v) (pullback.lift (α ≫ pullback.fst w f) (pullback.fst v f) hcomm)
    (pullback.lift_snd _ _ _)
  refine ⟨t ≫ pullback.fst w v, ?_, ?_⟩
  · rw [Category.assoc, pullback.condition, ← Category.assoc, ht₁, Category.id_comp]
  · rw [← Category.assoc, ht₂, pullback.lift_fst]

/-- **Stacks Project, Tag 0BTY.** Let `f : X ⟶ Y` be a universal homeomorphism and let `A` be a
scheme étale over `Y`. For every scheme `B` over `Y`, base change along `f` is a bijection from
the `Y`-morphisms `B ⟶ A` to the `X`-morphisms between the base changes.

Injectivity holds for any surjective `f`, by
`Stacks.Etale.injective_baseChange_hom_of_universalHomeomorphism`; surjectivity is
`Stacks.Etale.exists_hom_of_pullbackHom_of_universalHomeomorphism`. -/
@[stacks 0BTY,
  ega "IV 18.1.3" "more general",
  ega "IV 2.2.16" "special case",
  sga "1 IX 3.1" "special case",
  sga "1 IX 4.10" "full faithfulness",
  sga "3 X 2.0" "full faithfulness"]
theorem bijective_pullbackHom_of_universalHomeomorphism {X Y : Scheme.{u}} (f : X ⟶ Y)
    [UniversalHomeomorphism f] (A B : Over Y) [Etale A.hom] :
    Function.Bijective (fun h : B ⟶ A => (Over.pullback f).map h) := by
  refine ⟨injective_baseChange_hom_of_universalHomeomorphism f A B, ?_⟩
  intro α
  obtain ⟨b, hb₁, hb₂⟩ := exists_hom_of_pullbackHom_of_universalHomeomorphism f B.hom A.hom
    α.left (Over.w α)
  refine ⟨Over.homMk b hb₁, ?_⟩
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simpa [Over.pullback_map_left, pullback.lift_fst] using hb₂
  · simpa [Over.pullback_map_left, pullback.lift_snd] using (Over.w α).symm

end Stacks.Etale

end
