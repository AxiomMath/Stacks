module

public import StacksFrontier.AlgebraicGeometry.Descent.MorphismProperty.LocalFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable

/-!
# Permanence of local finite type for morphisms of algebraic spaces

An étale morphism of algebraic spaces over a scheme `S` is locally of finite type, and the
composite of two morphisms locally of finite type is again locally of finite type.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isEtale'`: an étale morphism of algebraic
  spaces over `S` is locally of finite type, with neither the source nor the target assumed to be
  an algebraic space.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_comp'`: morphisms locally of finite type are
  closed under composition, with the source not assumed to be an algebraic space.

## References

* [Stacks Project, Tag 03XG](https://stacks.math.columbia.edu/tag/03XG)
* [Stacks Project, Tag 06LT](https://stacks.math.columbia.edu/tag/06LT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- An étale morphism of presheaves on the big fppf site of `S` is locally of finite type; neither
the source nor the target has to be an algebraic space. -/
@[stacks 06LT]
theorem isLocallyOfFiniteType_of_isEtale' (f : F ⟶ G) (hf : IsEtale B S hS f) :
    IsLocallyOfFiniteType B S hS f := by
  intro U V a b h ha hb comm
  have : Etale ((BigFppfOver.toScheme B S hS).map h) :=
    etale_of_comp_etale_chart B S hS (hf U a ha) hb comm
  infer_instance

/-- The composite `f ≫ g` of two morphisms locally of finite type is locally of finite type, as
soon as the intermediate and final presheaves `G` and `H` are algebraic spaces over `S`. -/
@[stacks 03XG "locally of finite type"]
theorem isLocallyOfFiniteType_comp' (f : F ⟶ G) (g : G ⟶ H)
    (hG : IsAlgebraicSpace B S hS G) (hH : IsAlgebraicSpace B S hS H)
    (hf : IsLocallyOfFiniteType B S hS f) (hg : IsLocallyOfFiniteType B S hS g) :
    IsLocallyOfFiniteType B S hS (f ≫ g) := by
  intro U W a c h ha hc comm
  have := (isMultiplicative_presheaf_etale B S hS).toIsStableUnderComposition
  have hKalg : IsAlgebraicSpace B S hS (pullback g c) :=
    isAlgebraicSpace_pullback B S hS g c hG (isAlgebraicSpace_yoneda B S hS W) hH
  have comm' : (a ≫ f) ≫ g = yoneda.map h ≫ c := by rw [Category.assoc, ← comm]
  obtain ⟨u, hu₁, hu₂⟩ : ∃ u : yoneda.obj U ⟶ pullback g c,
      u ≫ pullback.fst g c = a ≫ f ∧ u ≫ pullback.snd g c = yoneda.map h :=
    ⟨pullback.lift (a ≫ f) (yoneda.map h) comm', pullback.lift_fst _ _ _,
      pullback.lift_snd _ _ _⟩
  obtain ⟨V, d, hdS, hdE⟩ := hKalg.exists_atlas
  obtain ⟨Z, p, q, hsq⟩ : ∃ (Z : BigFppfOver B S hS) (p : Z ⟶ V) (q : Z ⟶ U),
      IsPullback (yoneda.map p) (yoneda.map q) d u :=
    ⟨_, hdE.rep.fst' u, hdE.rep.snd u, hdE.rep.isPullback' u⟩
  have hqE' := presheaf_of_isPullback B S hS hsq hdE
  have hqS' := presheaf_of_isPullback B S hS hsq hdS
  have hqE : Etale ((BigFppfOver.toScheme B S hS).map q) :=
    MorphismProperty.of_relative_map (P := MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) hqE'
  have hqS : Surjective ((BigFppfOver.toScheme B S hS).map q) :=
    MorphismProperty.of_relative_map (P := MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) hqS'
  have hfstE : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.fst g c) :=
    presheaf_of_isPullback B S hS (IsPullback.of_hasPullback g c).flip hc
  have hdGE : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (d ≫ pullback.fst g c) :=
    MorphismProperty.IsStableUnderComposition.comp_mem _ _ hdE hfstE
  obtain ⟨β, hβ⟩ : ∃ β : V ⟶ W, yoneda.map β = d ≫ pullback.snd g c :=
    ⟨yoneda.preimage _, yoneda.map_preimage _⟩
  have hgβ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map β) := by
    refine hg V W (d ≫ pullback.fst g c) c β hdGE hc ?_
    rw [hβ, Category.assoc, Category.assoc, ← pullback.condition]
  have hAE : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map q ≫ a) :=
    MorphismProperty.IsStableUnderComposition.comp_mem _ _ hqE' ha
  have hfp : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map p) := by
    refine hf Z V (yoneda.map q ≫ a) (d ≫ pullback.fst g c) p hAE hdGE ?_
    rw [← Category.assoc, hsq.w, Category.assoc, hu₁, Category.assoc]
  have hcomp : p ≫ β = q ≫ h := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, hβ, ← Category.assoc, hsq.w,
      Category.assoc, hu₂]
  have hqh : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map q ≫
      (BigFppfOver.toScheme B S hS).map h) := by
    rw [← Functor.map_comp, ← hcomp, Functor.map_comp]
    infer_instance
  exact locallyOfFiniteType_of_comp_of_fppf
    ((BigFppfOver.toScheme B S hS).map q) ((BigFppfOver.toScheme B S hS).map h)

end AlgebraicGeometry.Space

end
