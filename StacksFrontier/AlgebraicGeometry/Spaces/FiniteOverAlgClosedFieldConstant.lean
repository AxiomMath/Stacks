module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import Mathlib.AlgebraicGeometry.Artinian
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ConstructiblePoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding

/-!
# A morphism from an irreducible space to a space finite over an algebraically closed field

Let `K` be an algebraically closed field, let `F` be an algebraic space over `Spec K` which is
*finite* over `Spec K`, and let `C` be an algebraic space over `Spec K` whose point space is
irreducible. This file proves that a morphism `t : C ⟶ F` takes the same value at every
`K`-rational point of `C`.

The reason is that a scheme finite over a field is the spectrum of an Artinian ring, hence has
discrete point space. Three steps:

* the finiteness of `F` over `Spec K`, tested at the base itself, represents `F` by an object
  `V` of the site finite over `Spec K` — the test object is affine, so the base change of `F`
  along the identity of the base, which is `F`, is represented;
* a morphism finite over a field is locally quasi-finite over an Artinian scheme, so `V` is
  locally Artinian and `|V| ≅ |F|` is discrete, in particular Hausdorff; the image of the
  irreducible `|C|` under `|t|` is irreducible, hence a single point;
* two `K`-rational points of `V` lying over the same point of `|V|` coincide, `K` being
  algebraically closed and `V` locally of finite type over `K`
  (`AlgebraicGeometry.ext_of_apply_closedPoint_eq`).

No reducedness of `C` enters: the conclusion is about the *rational points* of `C`, which is
the form in which [Stacks, Tag 0AEM] uses it — the source passes to the algebraic closure
precisely "so we may argue using rational points".

## Main results

* `AlgebraicGeometry.Space.exists_isIso_yoneda_of_isFinite_toBase`: an algebraic space finite
  over `Spec K` is represented by an object of the site finite over `Spec K`.
* `AlgebraicGeometry.Space.discreteTopology_points_of_isFinite_toBase`: its point space is
  discrete.
* `AlgebraicGeometry.Space.subsingleton_range_pointsMap_of_isFinite_toBase`: a morphism into it
  from a space with preirreducible point space has a single point as its whole image on points.
* `AlgebraicGeometry.Space.comp_eq_comp_of_isFinite_toBase`: **such a morphism is constant on
  rational points** — it takes the same value at any two `K`-rational points of its source.
* `AlgebraicGeometry.Space.preirreducibleSpace_points_of_isPreirreducible_range_pointsMap`: the
  point space of an immersed subspace whose point set is preirreducible is preirreducible,
  which is how the hypothesis above is met at a closed subspace supported on an irreducible
  closed set.

## References

* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03ZP](https://stacks.math.columbia.edu/tag/03ZP)
* [Stacks Project, Tag 0ABJ](https://stacks.math.columbia.edu/tag/0ABJ)
* [Stacks Project, Tag 0AEM](https://stacks.math.columbia.edu/tag/0AEM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Preirreducibility of the point space of an immersed subspace -/

/-- A topological embedding whose image is preirreducible has preirreducible source: the source
is homeomorphic to its image. -/
private theorem preirreducibleSpace_of_isEmbedding {α β : Type*} [TopologicalSpace α]
    [TopologicalSpace β] {g : α → β} (hg : Topology.IsEmbedding g)
    (h : IsPreirreducible (Set.range g)) : PreirreducibleSpace α :=
  let : PreirreducibleSpace (Set.range g) := Subtype.preirreducibleSpace h
  hg.toHomeomorph.symm.surjective.preirreducibleSpace hg.toHomeomorph.symm.continuous

section Immersion

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **The point space of an immersed subspace whose point set is preirreducible is
preirreducible.** The map on points of an immersion is a topological embedding by
[Stacks, Tag 0ABJ], so the point space of the subspace is homeomorphic to its point set. -/
theorem preirreducibleSpace_points_of_isPreirreducible_range_pointsMap
    (hX : IsAlgebraicSpace B S hS X) (i : Z ⟶ X) (hi : IsImmersion B S hS i)
    (h : IsPreirreducible (Set.range (pointsMap B S hS Z i))) :
    PreirreducibleSpace (points B S hS Z) :=
  preirreducibleSpace_of_isEmbedding
    (isEmbedding_pointsMap_of_isImmersion B S hS hX i hi) h

end Immersion

/-! ### A space finite over an algebraically closed field -/

section Finite

variable (B : BigFppfSite.{u}) (K : Type u) [Field K] [IsAlgClosed K]
  (hK : B.Contains (Spec (CommRingCat.of K)))

omit [IsAlgClosed K] in
/-- Any two morphisms to the functor of points of the base agree, that presheaf being
terminal. -/
private theorem hom_ext_toBase
    {W : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (a b : W ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hK)) :
      BigFppfOver B (Spec (CommRingCat.of K)) hK)) : a = b :=
  ((Over.mkIdTerminal :
      IsTerminal (Over.mk (𝟙 (B.obj hK)) :
        BigFppfOver B (Spec (CommRingCat.of K)) hK)).isTerminalObj yoneda _).hom_ext a b

omit [IsAlgClosed K] in
/-- **An algebraic space finite over `Spec K` is represented by an object of the site finite
over `Spec K`.** The finiteness predicate of [Stacks, Tag 03ZP] tests the base change along
every morphism from an affine object of the site; at the identity of the base itself the base
change *is* the space, so the representing object it produces represents the space. -/
theorem exists_isIso_yoneda_of_isFinite_toBase
    {F : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (q : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hK)) :
      BigFppfOver B (Spec (CommRingCat.of K)) hK))
    (hq : IsFinite B (Spec (CommRingCat.of K)) hK q) :
    ∃ (V : BigFppfOver B (Spec (CommRingCat.of K)) hK)
      (p : V ⟶ (Over.mk (𝟙 (B.obj hK)) : BigFppfOver B (Spec (CommRingCat.of K)) hK))
      (i : yoneda.obj V ⟶ F),
      IsIso i ∧
        _root_.AlgebraicGeometry.IsFinite
          ((BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).map p) ∧
        i ≫ q = yoneda.map p := by
  obtain ⟨V, p, i, _, hfin, hpb⟩ :=
    hq (Over.mk (𝟙 (B.obj hK)))
      (inferInstanceAs (IsAffine (Spec (CommRingCat.of K)))) (𝟙 _)
  refine ⟨V, p, i, hpb.isIso_fst_of_isIso, hfin, ?_⟩
  rw [hpb.w, Category.comp_id]

omit [IsAlgClosed K] in
/-- **The point space of an algebraic space finite over `Spec K` is discrete.** The
representing object of the site is finite, hence locally quasi-finite, over the Artinian
`Spec K`, so it is a locally Artinian scheme; its point space is therefore discrete, and so is
the point space of the presheaf it represents, by clause (1) of [Stacks, Tag 03BX]. -/
theorem discreteTopology_points_of_isFinite_toBase
    {F : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (q : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hK)) :
      BigFppfOver B (Spec (CommRingCat.of K)) hK))
    (hq : IsFinite B (Spec (CommRingCat.of K)) hK q) :
    DiscreteTopology (points B (Spec (CommRingCat.of K)) hK F) := by
  obtain ⟨V, p, i, hiso, hfin, _⟩ := exists_isIso_yoneda_of_isFinite_toBase B K hK q hq
  let := hiso
  let := hfin
  let : IsLocallyArtinian
      ((BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj
        (Over.mk (𝟙 (B.obj hK)))) :=
    Scheme.isLocallyArtinianScheme_Spec.mpr inferInstance
  let : IsLocallyArtinian ((BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).obj V) :=
    IsLocallyArtinian.of_locallyQuasiFinite
      ((BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).map p)
  let : DiscreteTopology (points B (Spec (CommRingCat.of K)) hK (yoneda.obj V)) :=
    (schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK V).symm.discreteTopology
  exact (pointsHomeomorphOfIso B (Spec (CommRingCat.of K)) hK (asIso i)).discreteTopology

omit [IsAlgClosed K] in
/-- **A morphism from a space with preirreducible point space into a space finite over
`Spec K` has a single point as its whole image on points.** The image of a preirreducible set
is preirreducible, and the point space of the target is discrete, hence Hausdorff. -/
theorem subsingleton_range_pointsMap_of_isFinite_toBase
    {C F : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (q : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hK)) :
      BigFppfOver B (Spec (CommRingCat.of K)) hK))
    (hq : IsFinite B (Spec (CommRingCat.of K)) hK q) (t : C ⟶ F)
    (hC : PreirreducibleSpace (points B (Spec (CommRingCat.of K)) hK C)) :
    (Set.range (pointsMap B (Spec (CommRingCat.of K)) hK C t)).Subsingleton := by
  let := discreteTopology_points_of_isFinite_toBase B K hK q hq
  have hpre : IsPreirreducible
      (Set.range (pointsMap B (Spec (CommRingCat.of K)) hK C t)) := by
    rw [← Set.image_univ]
    exact hC.isPreirreducible_univ.image _
      (continuous_pointsMap B (Spec (CommRingCat.of K)) hK t).continuousOn
  exact hpre.subsingleton

/-- **A morphism from a space with preirreducible point space to a space finite over an
algebraically closed field is constant on rational points.**

Let `K` be algebraically closed, let `q : F ⟶ Spec K` be finite and let `C` be a presheaf on
the big fppf site over `Spec K` whose point space is preirreducible. Then any two `K`-rational
points `l₁, l₂` of `C` have the same image under `t : C ⟶ F`.

This is the step of [Stacks, Tag 0AEM] which spends the finiteness produced by
[Stacks, Tag 0AEJ]: the contracted piece is irreducible and is carried by the translate of the
given morphism into a space finite over the field, so the two distinct rational points of the
piece have the same image. -/
theorem comp_eq_comp_of_isFinite_toBase
    {C F : (BigFppfOver B (Spec (CommRingCat.of K)) hK)ᵒᵖ ⥤ Type u}
    (q : F ⟶ yoneda.obj (Over.mk (𝟙 (B.obj hK)) :
      BigFppfOver B (Spec (CommRingCat.of K)) hK))
    (hq : IsFinite B (Spec (CommRingCat.of K)) hK q) (t : C ⟶ F)
    (hC : PreirreducibleSpace (points B (Spec (CommRingCat.of K)) hK C))
    (l₁ l₂ : yoneda.obj (Over.mk (𝟙 (B.obj hK)) :
      BigFppfOver B (Spec (CommRingCat.of K)) hK) ⟶ C) :
    l₁ ≫ t = l₂ ≫ t := by
  obtain ⟨V, p, i, _, _, -⟩ := exists_isIso_yoneda_of_isFinite_toBase B K hK q hq
  obtain ⟨sa, hsa⟩ :
      ∃ s : (Over.mk (𝟙 (B.obj hK)) : BigFppfOver B (Spec (CommRingCat.of K)) hK) ⟶ V,
        yoneda.map s = l₁ ≫ t ≫ inv i :=
    (yoneda (C := BigFppfOver B (Spec (CommRingCat.of K)) hK)).map_surjective _
  obtain ⟨sb, hsb⟩ :
      ∃ s : (Over.mk (𝟙 (B.obj hK)) : BigFppfOver B (Spec (CommRingCat.of K)) hK) ⟶ V,
        yoneda.map s = l₂ ≫ t ≫ inv i :=
    (yoneda (C := BigFppfOver B (Spec (CommRingCat.of K)) hK)).map_surjective _
  have hsec (s : (Over.mk (𝟙 (B.obj hK)) : BigFppfOver B (Spec (CommRingCat.of K)) hK) ⟶ V) :
      (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).map s ≫
        (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).map p = 𝟙 _ := by
    rw [← CategoryTheory.Functor.map_comp,
      (yoneda (C := BigFppfOver B (Spec (CommRingCat.of K)) hK)).map_injective
        (hom_ext_toBase B K hK (yoneda.map (s ≫ p)) (yoneda.map (𝟙 _))),
      CategoryTheory.Functor.map_id]
  have hpt : (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).map sa
        (IsLocalRing.closedPoint K) =
      (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).map sb
        (IsLocalRing.closedPoint K) := by
    have key : pointsMap B (Spec (CommRingCat.of K)) hK _ (yoneda.map sa)
          ((schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK
            (Over.mk (𝟙 (B.obj hK)))).symm (IsLocalRing.closedPoint K)) =
        pointsMap B (Spec (CommRingCat.of K)) hK _ (yoneda.map sb)
          ((schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK
            (Over.mk (𝟙 (B.obj hK)))).symm (IsLocalRing.closedPoint K)) := by
      rw [hsa, hsb, pointsMap_comp B (Spec (CommRingCat.of K)) hK _ l₁ (t ≫ inv i),
        pointsMap_comp B (Spec (CommRingCat.of K)) hK _ l₂ (t ≫ inv i), Function.comp_apply,
        Function.comp_apply, pointsMap_comp B (Spec (CommRingCat.of K)) hK _ t (inv i),
        Function.comp_apply, Function.comp_apply]
      exact congrArg _
        (subsingleton_range_pointsMap_of_isFinite_toBase B K hK q hq t hC
          ⟨_, rfl⟩ ⟨_, rfl⟩)
    have na := schemePointsHomeomorph_symm_naturality B (Spec (CommRingCat.of K)) hK sa
      (IsLocalRing.closedPoint K)
    have nb := schemePointsHomeomorph_symm_naturality B (Spec (CommRingCat.of K)) hK sb
      (IsLocalRing.closedPoint K)
    exact (schemePointsHomeomorph B (Spec (CommRingCat.of K)) hK V).symm.injective
      (na.symm.trans (key.trans nb))
  have hschemes : (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).map sa =
      (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).map sb :=
    AlgebraicGeometry.ext_of_apply_closedPoint_eq
      ((BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).map p) (hsec sa) (hsec sb) hpt
  rw [← cancel_mono (inv i), Category.assoc, Category.assoc, ← hsa, ← hsb,
    (BigFppfOver.toScheme B (Spec (CommRingCat.of K)) hK).map_injective hschemes]

end Finite

end AlgebraicGeometry.Space

end
