module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleCover

/-!
# A morphism into an algebraic space factors locally through an affine étale chart

Let `F` be an algebraic space over a scheme `S`, let `T` be an object of the big fppf category
over `S` and let `g : T ⟶ F` be a morphism, that is a section of `F` over `T`.  This file
proves that there is a covering family of `T` by objects with *affine* underlying scheme over
each of which `g` factors through an étale chart of `F` with *affine* underlying scheme.

This is the target-side companion of the source-side factorization
`AlgebraicGeometry.Space.exists_surjective_etale_chart_lift` ([Stacks Project, Tag 02X1]): that
statement produces a surjective étale cover of `T` over which `g` factors through one *given*
surjective étale chart, and says nothing about the underlying schemes; what is added here is
that both the members of the cover and the chart they map to may be taken affine.  That is the
form in which a statement about square-zero immersions of affine schemes — for instance the
affine case of [Stacks Project, Tag 02H5],
`Stacks.Thickenings.existsUnique_derivationAction` — can be applied to a morphism into an
algebraic space.

## Main results

* `AlgebraicGeometry.Space.exists_affine_etale_chart_factorization`: the factorization, with the
  covering family recorded as a presieve of the big fppf site over `S`.

## Implementation notes

The chart of `F` is an *affine open of the atlas*, not a member of the coproduct decomposition
of [Stacks Project, Tag 03FX]: an affine open immersion into the atlas is étale, so its
composite with the atlas is again an étale chart, and no coproduct bookkeeping is needed.

The covering family is produced in one step rather than by composing two covering sieves.  The
atlas `f : U ⟶ F` is relatively representable, so the fibre product `P = U ×_F T` is an object
of the site and its projection `b : P ⟶ T` is surjective and étale on underlying schemes.  The
members of the covering family are affine opens of `P` chosen so that each maps into an affine
open of the atlas, indexed by the points of the underlying scheme of `P`; the underlying family
of scheme morphisms is then étale and jointly surjective, hence an fppf covering family, and
`AlgebraicGeometry.BigFppfOver.sieve_generate_ofArrows_mem_topology` turns that into a covering
sieve of the site.  So the transitivity of the topology is not used.

The morphism from a member of the cover to its affine chart is the restriction
`AlgebraicGeometry.Scheme.Hom.resLE` of the projection `P ⟶ U`, and the commuting triangle it
satisfies is `AlgebraicGeometry.Scheme.Hom.resLE_comp_ι`; both are lifted to the site by the
fullness of the functor to schemes on morphisms over `S`,
`AlgebraicGeometry.BigFppfOver.exists_hom_of_comp_eq`.

## References

* [Stacks Project, Tag 02X1](https://stacks.math.columbia.edu/tag/02X1)
* [Stacks Project, Tag 03FR](https://stacks.math.columbia.edu/tag/03FR)
* [Stacks Project, Tag 03FX](https://stacks.math.columbia.edu/tag/03FX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A section of an algebraic space over an object of the site factors, over a covering
family of affine objects, through an affine étale chart of the space.**  Let `F` be an algebraic
space over `S`, let `T` be an object of the big fppf category over `S` and let
`g : yoneda.obj T ⟶ F`.  There is a covering family `π i : V i ⟶ T` of the big fppf site over
`S` whose members have affine underlying scheme, together with étale charts
`w i : yoneda.obj (W i) ⟶ F` with affine underlying scheme and morphisms `m i : V i ⟶ W i` of
the site, such that `g` restricted to `V i` is `w i` read along `m i`.

The target chart is affine, which is what makes a deformation-theoretic statement available
only for affine schemes applicable to `g`. -/
theorem exists_affine_etale_chart_factorization
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (T : BigFppfOver B S hS) (g : yoneda.obj T ⟶ F) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ T)
        (W : I → BigFppfOver B S hS) (w : ∀ i, yoneda.obj (W i) ⟶ F)
        (m : ∀ i, V i ⟶ W i),
      Sieve.generate (Presieve.ofArrows V π) ∈ BigFppfOver.topology B S hS T ∧
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧
        (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (W i))) ∧
        (∀ i, IsEtale B S hS (w i)) ∧
        ∀ i, yoneda.map (m i) ≫ w i = yoneda.map (π i) ≫ g := by
  classical
  obtain ⟨U, f, hfS, hfE⟩ := hF.exists_atlas
  -- The fibre product `P = U ×_F T`, an object of the site.
  set P : BigFppfOver B S hS := hfE.rep.pullback g with hPdef
  set a : P ⟶ U := hfE.rep.fst' g with hadef
  set b : P ⟶ T := hfE.rep.snd g with hbdef
  have hsq : yoneda.map a ≫ f = yoneda.map b ≫ g := (hfE.rep.isPullback' g).w
  have hbs : Surjective ((BigFppfOver.toScheme B S hS).map b) :=
    hfS.property g (hfE.rep.fst g) (hfE.rep.snd g) (hfE.rep.isPullback g)
  have hbe : Etale ((BigFppfOver.toScheme B S hS).map b) :=
    hfE.property g (hfE.rep.fst g) (hfE.rep.snd g) (hfE.rep.isPullback g)
  set α : (BigFppfOver.toScheme B S hS).obj P ⟶ (BigFppfOver.toScheme B S hS).obj U :=
    (BigFppfOver.toScheme B S hS).map a with hαdef
  -- Through every point of `P` an affine open of `P` mapping into an affine open of `U`.
  have hchoice : ∀ x : (BigFppfOver.toScheme B S hS).obj P,
      ∃ (A : ((BigFppfOver.toScheme B S hS).obj U).Opens)
        (C : ((BigFppfOver.toScheme B S hS).obj P).Opens),
        IsAffineOpen A ∧ IsAffineOpen C ∧ x ∈ C ∧ C ≤ α ⁻¹ᵁ A := by
    intro x
    obtain ⟨A, hA, hAx, -⟩ :=
      exists_isAffineOpen_mem_and_subset (X := (BigFppfOver.toScheme B S hS).obj U)
        (x := α.base x) (U := ⊤) trivial
    obtain ⟨C, hC, hCx, hCsub⟩ :=
      exists_isAffineOpen_mem_and_subset (X := (BigFppfOver.toScheme B S hS).obj P)
        (x := x) (U := α ⁻¹ᵁ A) hAx
    exact ⟨A, C, hA, hC, hCx, hCsub⟩
  choose A C hA hC hCx hCle using hchoice
  -- An open subscheme of an object of the site is again an object of the site.
  have hcont : ∀ (X : BigFppfOver B S hS) (D : ((BigFppfOver.toScheme B S hS).obj X).Opens),
      B.Contains D.toScheme := fun X D =>
    Scheme.size_lt_of_isOpenImmersion D.ι X.left.property
  set O : ∀ (X : BigFppfOver B S hS) (D : ((BigFppfOver.toScheme B S hS).obj X).Opens),
      BigFppfOver B S hS := fun X D =>
    Over.mk (ObjectProperty.homMk (D.ι ≫ B.inclusion.map X.hom) :
      B.obj (hcont X D) ⟶ B.obj hS)
  set ι : ∀ (X : BigFppfOver B S hS) (D : ((BigFppfOver.toScheme B S hS).obj X).Opens),
      O X D ⟶ X := fun X D => Over.homMk (ObjectProperty.homMk D.ι) rfl
  have hιmap : ∀ X D, (BigFppfOver.toScheme B S hS).map (ι X D) = D.ι := fun _ _ => rfl
  -- The structure morphism of `P` is the one read off `U`.
  have hPover : α ≫ B.inclusion.map U.hom = B.inclusion.map P.hom := by
    have h := congrArg B.inclusion.map (Over.w a)
    rw [B.inclusion.map_comp] at h
    exact h
  -- The restriction of `P ⟶ U` to the chosen affine opens, as a morphism of the site.
  have hm : ∀ x, ∃ ψ : O P (C x) ⟶ O U (A x),
      (BigFppfOver.toScheme B S hS).map ψ = α.resLE (A x) (C x) (hCle x) := by
    intro x
    refine BigFppfOver.exists_hom_of_comp_eq B S hS (X := O P (C x)) (Y := O U (A x))
      (α.resLE (A x) (C x) (hCle x)) ?_
    change α.resLE (A x) (C x) (hCle x) ≫ (A x).ι ≫ B.inclusion.map U.hom =
      (C x).ι ≫ B.inclusion.map P.hom
    rw [← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc, hPover]
  choose m hmmap using hm
  -- The triangle `m ≫ ι = ρ ≫ a` in the site.
  have htri : ∀ x, m x ≫ ι U (A x) = ι P (C x) ≫ a := by
    intro x
    refine (BigFppfOver.toScheme B S hS).map_injective ?_
    rw [Functor.map_comp, Functor.map_comp, hmmap, hιmap, hιmap, ← hαdef]
    exact Scheme.Hom.resLE_comp_ι α (hCle x)
  -- The charts of `F`: an affine open of the atlas, composed with the atlas.
  have hκetale : ∀ x, (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (yoneda.map (ι U (A x))) := by
    intro x
    refine (presheaf_yoneda_map_etale_iff B S hS (ι U (A x))).2 ?_
    rw [hιmap]
    infer_instance
  refine ⟨(BigFppfOver.toScheme B S hS).obj P, fun x => O P (C x), fun x => ι P (C x) ≫ b,
    fun x => O U (A x), fun x => yoneda.map (ι U (A x)) ≫ f, m, ?_, fun x => (hC x),
    fun x => (hA x), fun x => ?_, fun x => ?_⟩
  · -- The family is a covering family: it is étale and jointly surjective on schemes.
    refine BigFppfOver.sieve_generate_ofArrows_mem_topology (fun x => O P (C x))
      (fun x => ι P (C x) ≫ b) ?_
    have hjs : ∀ y : (BigFppfOver.toScheme B S hS).obj T,
        ∃ x, y ∈ Set.range ((BigFppfOver.toScheme B S hS).map (ι P (C x) ≫ b)) := by
      intro y
      have := hbs
      obtain ⟨p, hp⟩ :=
        Scheme.Hom.surjective ((BigFppfOver.toScheme B S hS).map b) y
      refine ⟨p, ⟨p, hCx p⟩, ?_⟩
      rw [Functor.map_comp, hιmap]
      exact hp
    have hje : ∀ x, AlgebraicGeometry.Etale
        ((BigFppfOver.toScheme B S hS).map (ι P (C x) ≫ b)) := by
      intro x
      rw [Functor.map_comp, hιmap]
      have := hbe
      infer_instance
    exact Scheme.etalePrecoverage_le_fppfPrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff _).2 ⟨hjs, hje⟩)
  · exact (isEtale_iff_presheaf_of_yoneda B S hS _).2
      (MorphismProperty.comp_mem _ _ _ (hκetale x) hfE)
  · have h1 : yoneda.map (m x) ≫ yoneda.map (ι U (A x)) =
        yoneda.map (ι P (C x)) ≫ yoneda.map a := by
      rw [← Functor.map_comp, ← Functor.map_comp, htri x]
    change yoneda.map (m x) ≫ yoneda.map (ι U (A x)) ≫ f = yoneda.map (ι P (C x) ≫ b) ≫ g
    rw [← Category.assoc, h1, Category.assoc, hsq, Functor.map_comp, Category.assoc]

end AlgebraicGeometry.Space

end
