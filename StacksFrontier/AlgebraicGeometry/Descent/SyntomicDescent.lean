module

public import Mathlib.AlgebraicGeometry.Morphisms.Descent
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.SyntomicAlgebra
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Comp
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties

/-!
# Descent of syntomicity along a surjective flat morphism

Let `X ⟶ Y ⟶ S` be morphisms of schemes with `X ⟶ Y` surjective, flat and locally of finite
presentation. If the composition `X ⟶ S` is syntomic, then so is `Y ⟶ S`. In particular
syntomicity descends along a surjective syntomic morphism.

## Main results

* `AlgebraicGeometry.syntomic_of_comp_of_fppf` descends syntomicity along a surjective flat
  morphism which is locally of finite presentation.
* `AlgebraicGeometry.syntomic_of_comp_surjective_syntomic` descends syntomicity along a
  surjective syntomic morphism.

Both are also available as `Stacks.Syntomic.syntomic_of_comp_of_fppf` and
`Stacks.Syntomic.syntomic_of_comp_surjective_syntomic`, which is how the algebraic-space
statements refer to them.

## Implementation notes

The source's commutative triangle is expressed by taking its morphism from `X` to `S` to be the
composite `f ≫ q`; this is equivalent to the formulation with a separately given `p : X ⟶ S` and
an equality `p = f ≫ q`.

The companion conclusion of the same source, that `f` itself is syntomic, is
`AlgebraicGeometry.syntomic_of_syntomic_comp_of_fppf`; it is obtained from the other half of
Avramov's criterion and lives in
`StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Descent.Fppf`, which argues on the local rings
of the fibres rather than by the affine reduction used here.

Syntomicity is the affine-local property attached to `RingHom.Syntomic`, so its defining condition
is a property of the maps `Γ(S, V) ⟶ Γ(Y, U)` for affine opens `U ⊆ Y` and `V ⊆ S` with
`q(U) ⊆ V`. The statement is therefore proved by restricting the whole situation to such a pair,
which is the content of `Scheme.Hom.resLE`: the restriction of `f` over `U` stays surjective, flat
and locally of finite presentation, and the restriction of `f ≫ q` is the composite of the two
restrictions by `Scheme.Hom.resLE_comp_resLE`.

With `Y` and `S` affine the morphism `f` is replaced by an affine one. Since `f` is flat and
locally of finite presentation it is open, so its image already comes from a quasi-compact open
`W ⊆ X` (`IsOpenMap.exists_opens_image_eq_of_prespectralSpace`), and `W` is dominated by an affine
scheme through a syntomic morphism because syntomicity is Zariski-local at the source and contains
the identities (`Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource`). The resulting `g : T ⟶ Y`
with `T` affine is surjective, flat and locally of finite presentation, and `g ≫ q` is syntomic as
soon as `f ≫ q` is, because the morphism `T ⟶ X` is syntomic. For affine schemes the surjectivity
and flatness of `g` are the faithful flatness of `Γ(Y) ⟶ Γ(T)`
(`Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine`), so the affine case is exactly the
algebra statement `Stacks.RingTheory.SyntomicDescent.ringHom_syntomic_of_faithfullyFlat`.

## References

* [Stacks Project, Tag 02KM](https://stacks.math.columbia.edu/tag/02KM)
* [Stacks Project, Tag 05B7](https://stacks.math.columbia.edu/tag/05B7)
* [Stacks Project, Tag 09Q7](https://stacks.math.columbia.edu/tag/09Q7)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {X Y S : Scheme.{u}}

/-- Syntomic morphisms contain the identities: an identity is an open immersion. -/
instance syntomic_containsIdentities :
    MorphismProperty.ContainsIdentities (@Syntomic.{u}) :=
  ⟨fun X ↦ syntomic_of_isOpenImmersion (𝟙 X)⟩

/-- A surjective flat morphism locally of finite presentation onto an affine scheme is dominated
by an affine scheme through a syntomic morphism: the image of a quasi-compact open `W ⊆ X` is
already all of `Y`, and `W` is covered by finitely many affine opens. -/
private theorem exists_affine_syntomic_cover (f : X ⟶ Y) [IsAffine Y] [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] :
    ∃ (T : Scheme.{u}) (h : T ⟶ X), IsAffine T ∧ Syntomic h ∧ Surjective (h ≫ f) := by
  obtain ⟨W : X.Opens, hW, hWsurj⟩ :=
    f.isOpenMap.exists_opens_image_eq_of_prespectralSpace f.continuous (by simp) isOpen_univ
      isCompact_univ
  have : CompactSpace (Scheme.Opens.toScheme W) := isCompact_iff_compactSpace.mp hW
  obtain ⟨T, hT, hTsurj, hTsyn, hTaff⟩ :=
    AlgebraicGeometry.Scheme.exists_hom_isAffine_of_isZariskiLocalAtSource
      @Syntomic.{u} (Scheme.Opens.toScheme W)
  have : Syntomic hT := hTsyn
  have : Surjective hT := hTsurj
  have hWf : Surjective (Scheme.Opens.ι W ≫ f) := by
    refine ⟨fun y ↦ ?_⟩
    obtain ⟨x, hxW, hxy⟩ : y ∈ f.base '' W := by rw [hWsurj]; trivial
    exact ⟨⟨x, hxW⟩, hxy⟩
  refine ⟨T, hT ≫ Scheme.Opens.ι W, hTaff,
    MorphismProperty.comp_mem _ _ _ hTsyn (syntomic_of_isOpenImmersion _), ?_⟩
  simpa only [Category.assoc] using
    (show Surjective (hT ≫ (Scheme.Opens.ι W ≫ f)) from inferInstance)

/-- The affine case of the descent: with `Y` and `S` affine, the statement is the algebra
statement for the global sections of an affine cover of `X`. -/
private theorem syntomic_of_comp_of_fppf_affine (f : X ⟶ Y) (q : Y ⟶ S) [IsAffine Y] [IsAffine S]
    [Surjective f] [Flat f] [LocallyOfFinitePresentation f] (hp : Syntomic (f ≫ q)) :
    Syntomic q := by
  obtain ⟨T, h, hT, hh, hs⟩ := exists_affine_syntomic_cover f
  have : IsAffine T := hT
  have : Surjective (h ≫ f) := hs
  have hsyn : Syntomic ((h ≫ f) ≫ q) := by
    rw [Category.assoc]
    exact MorphismProperty.comp_mem _ _ _ hh hp
  have : Flat h := AlgebraicGeometry.flat hh
  have : LocallyOfFinitePresentation h := AlgebraicGeometry.locallyOfFinitePresentation hh
  rw [HasRingHomProperty.iff_of_isAffine (P := @Syntomic)]
  refine Stacks.RingTheory.SyntomicDescent.ringHom_syntomic_of_faithfullyFlat q.appTop.hom
    (h ≫ f).appTop.hom ?_
    ((Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine (h ≫ f)).mp ⟨inferInstance, hs⟩)
    (HasRingHomProperty.appTop (P := @LocallyOfFinitePresentation) (h ≫ f) inferInstance)
  simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
    HasRingHomProperty.appTop (P := @Syntomic) ((h ≫ f) ≫ q) hsyn

/-- **Stacks Project, Tag 05B7.** Syntomicity descends along a surjective flat morphism which is
locally of finite presentation: if `f : X ⟶ Y` is surjective, flat and locally of finite
presentation and `f ≫ q` is syntomic, then `q : Y ⟶ S` is syntomic. -/
@[stacks 05B7 "q_syntomic"]
theorem syntomic_of_comp_of_fppf (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f] [Flat f]
    [LocallyOfFinitePresentation f] (hp : Syntomic (f ≫ q)) : Syntomic q := by
  refine (IsZariskiLocalAtSource.iff_exists_resLE (P := @Syntomic)).2 fun y ↦ ?_
  obtain ⟨V, hV, hyV, -⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens
    (Opens.mem_top (q y))
  obtain ⟨U, hU, hyU, hUV⟩ := Opens.isBasis_iff_nbhd.mp Y.isBasis_affineOpens
    (show y ∈ q ⁻¹ᵁ V from hyV)
  refine ⟨V, U, hyU, hUV, ?_⟩
  let f' := f.resLE U (f ⁻¹ᵁ U) le_rfl
  have : IsAffine (U : Scheme.{u}) := hU
  have : IsAffine (V : Scheme.{u}) := hV
  have : Surjective f' := surjective_resLE f U
  have : Flat f' := by dsimp only [f']; infer_instance
  have : LocallyOfFinitePresentation f' := by dsimp only [f']; infer_instance
  refine syntomic_of_comp_of_fppf_affine f' (q.resLE V U hUV) ?_
  show Syntomic (f.resLE U (f ⁻¹ᵁ U) le_rfl ≫ q.resLE V U hUV)
  rw [Scheme.Hom.resLE_comp_resLE]
  exact syntomic_resLE hp _ _ _

/-- **Stacks Project, Tag 02KM (syntomic case).** If `f` is surjective and syntomic and `f ≫ q`
is syntomic, then `q` is syntomic. -/
theorem syntomic_of_comp_surjective_syntomic (f : X ⟶ Y) (q : Y ⟶ S) [Surjective f]
    (hf : Syntomic f) (hp : Syntomic (f ≫ q)) : Syntomic q := by
  have : Flat f := AlgebraicGeometry.flat hf
  have : LocallyOfFinitePresentation f := AlgebraicGeometry.locallyOfFinitePresentation hf
  exact syntomic_of_comp_of_fppf f q hp

end AlgebraicGeometry

namespace Stacks.Syntomic

export AlgebraicGeometry (syntomic_of_comp_of_fppf syntomic_of_comp_surjective_syntomic)

end Stacks.Syntomic

end
