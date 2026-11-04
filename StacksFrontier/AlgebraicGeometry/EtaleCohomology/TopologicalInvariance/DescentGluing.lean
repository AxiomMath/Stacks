module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.MorphismDescent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceEquivalence

/-!
# The gluing isomorphism of a descent along an étale covering of the target

Let `f : X ⟶ Y` be a universal homeomorphism, let `w : W ⟶ Y` be a morphism and let `t : T ⟶ W`
be étale. Write `W_X := X ×_Y W` for the base change of `W`, and suppose that the base change of
`T` to `W_X` is identified over `W_X` with the base change of a scheme `U` over `X`, by an
isomorphism `e : T ×_W W_X ≅ U ×_X W_X`.

This file produces, out of `e` alone, the **gluing isomorphism** `T ×_Y W ≅ W ×_Y T` over
`W ×_Y W`, that is the first of the two pieces of data a descent datum for `T` relative to `w`
consists of, together with the property of it which identifies it uniquely: that it preserves
the `U`-component of a generalized point of `T`.

## The mechanism

`w` is not assumed to be a universal homeomorphism — in the application it is étale and
surjective — so the canonical descent datum of
`StacksFrontier.AlgebraicGeometry.Topologies.EtaleUniversalHomeomorphismCocycle` does not apply:
its gluing isomorphism is produced by Stacks Project, Tag 025H along the diagonal of `w`, which
is a surjective closed immersion only when `w` itself is a universal homeomorphism.

What is a universal homeomorphism is the base change of `f` over `W ×_Y W`, and that is what
supplies the isomorphism. Both pullbacks of `T` to `W ×_Y W` become, after base change along
`X ×_Y (W ×_Y W) ⟶ W ×_Y W`, the base change of `U` along the projection
`X ×_Y (W ×_Y W) ⟶ X`, which is the *same* morphism for the two of them; so they are isomorphic
there, and the isomorphism descends by the rigidity of descent along a universal homeomorphism,
`Stacks.Etale.exists_iso_of_pullback_iso`.

A generalized point of `T` lying over a point of `W_X` has, through `e`, a `U`-component
(`Stacks.Etale.descentUComp`); the first half of the argument is that `e` turns *any* base
change of `T` to a scheme over `W_X` into a base change of `U` along the `X`-component, with
the `U`-component as the comparison map
(`Stacks.Etale.isPullback_descentUComp`). The gluing isomorphism is then characterised by
leaving the `U`-component of a generalized point unchanged while moving its `W`-component from
one of the two charts to the other.

## Main definitions

* `Stacks.Etale.descentUComp` — the `U`-component of a generalized point of `T` accompanied by a
  lift of its image in `W` to `W_X`.

## Main results

* `Stacks.Etale.comp_descentUComp` — the `U`-component is natural in the generalized point.
* `Stacks.Etale.isPullback_descentUComp` — a base change of `T` along a morphism to `W` which is
  accompanied by a compatible morphism to `X` is a base change of `U`, by the `U`-component.
* `Stacks.Etale.exists_gluing_of_descentIso` — **the gluing isomorphism**, in the shape in which
  `AlgebraicGeometry.exists_transition_of_pullbackIso_of_rel` and
  `AlgebraicGeometry.exists_gluingIso_of_pullbackIso` consume it: an isomorphism
  `T ×_Y W ≅ W ×_Y T` whose two `W`-components are the expected ones, and which preserves the
  `U`-component of every generalized point.

## Implementation notes

Nothing here carries a Stacks tag. The gluing isomorphism is one of the two pieces of data of a
descent datum; the cocycle condition is not proved here. It is proved in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective`, from the
third conclusion below, and with it Stacks Project, Tag 04E0 is closed there, at
`Stacks.Etale.affineEtalePullback_isEquivalence`.

No affineness, étaleness or surjectivity hypothesis is placed on `p : U ⟶ X` or on `w`: the
construction needs only that `t` is étale, so that the two pullbacks of `T` to `W ×_Y W` are
étale and the rigidity applies to them. `Stacks.Etale.descentUComp` and
`Stacks.Etale.isPullback_descentUComp` need no hypothesis at all, not even that `f` is a
universal homeomorphism.

The point of `W_X` is carried as a single morphism `ζ : Z ⟶ W_X` rather than as a pair of
morphisms to `X` and to `W` together with their compatibility, because the gluing isomorphism
changes the `W`-component and leaves the `X`-component alone, so the two components are never
varied together.

## References

* [Stacks Project, Tag 04E0](https://stacks.math.columbia.edu/tag/04E0)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 0BTY](https://stacks.math.columbia.edu/tag/0BTY)
* [Stacks Project, Tag 023V](https://stacks.math.columbia.edu/tag/023V)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Etale

variable {X Y : Scheme.{u}}

/-- **The `U`-component of a generalized point of `T`.** Let `e` identify the base change of `T`
to `W_X := X ×_Y W` with the base change of `U` to `W_X`. A generalized point `a : Z ⟶ T`
together with a lift `ζ : Z ⟶ W_X` of its image `a ≫ t` in `W` is a generalized point of
`T ×_W W_X`, hence of `U ×_X W_X`, whose `U`-component this is. -/
def descentUComp (f : X ⟶ Y) {U W T : Scheme.{u}} (p : U ⟶ X) (w : W ⟶ Y) (t : T ⟶ W)
    (e : pullback t (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    {Z : Scheme.{u}} (a : Z ⟶ T) (ζ : Z ⟶ pullback f w)
    (h : a ≫ t = ζ ≫ pullback.snd f w) : Z ⟶ U :=
  pullback.lift a ζ h ≫ e.hom ≫ pullback.fst p (pullback.fst f w)

/-- The `U`-component of a generalized point of `T` is natural in that point. -/
lemma comp_descentUComp (f : X ⟶ Y) {U W T : Scheme.{u}} (p : U ⟶ X) (w : W ⟶ Y) (t : T ⟶ W)
    (e : pullback t (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    {Z Z' : Scheme.{u}} (γ : Z' ⟶ Z) (a : Z ⟶ T) (ζ : Z ⟶ pullback f w)
    (h : a ≫ t = ζ ≫ pullback.snd f w) :
    γ ≫ descentUComp f p w t e a ζ h =
      descentUComp f p w t e (γ ≫ a) (γ ≫ ζ)
        (by rw [Category.assoc, h, Category.assoc]) := by
  have hl : γ ≫ pullback.lift a ζ h =
      pullback.lift (γ ≫ a) (γ ≫ ζ)
        (show (γ ≫ a) ≫ t = (γ ≫ ζ) ≫ pullback.snd f w by
          rw [Category.assoc, h, Category.assoc]) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd]
  simp only [descentUComp]
  rw [← Category.assoc, hl]

/-- **A base change of `T` accompanied by a lift to `W_X` is a base change of `U`.** Let `e`
identify the base change of `T` to `W_X := X ×_Y W` with the base change of `U` to `W_X`, over
`W_X`, let `ζ : Z ⟶ W_X` be a morphism, and let `Q` be the base change of `T` along the
`W`-component of `ζ`. Then `Q` is the base change of `U` along the `X`-component of `ζ`, and the
comparison morphism is the `U`-component of the tautological generalized point of `T` over `Q`.

The base change of `T` along the `W`-component of `ζ` is the base change along `ζ` of
`T ×_W W_X`, hence of `U ×_X W_X`, hence the base change of `U` along the `X`-component. -/
theorem isPullback_descentUComp (f : X ⟶ Y) {U W T : Scheme.{u}} (p : U ⟶ X) (w : W ⟶ Y)
    (t : T ⟶ W) (e : pullback t (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd t (pullback.snd f w))
    {Z Q : Scheme.{u}} {ζ : Z ⟶ pullback f w} {b : Q ⟶ T} {v : Q ⟶ Z}
    (hQ : IsPullback b v t (ζ ≫ pullback.snd f w)) :
    IsPullback (descentUComp f p w t e b (v ≫ ζ) (by rw [Category.assoc]; exact hQ.w)) v p
      (ζ ≫ pullback.fst f w) := by
  simp only [descentUComp]
  have s1 : IsPullback (pullback.lift b (v ≫ ζ) (by rw [Category.assoc]; exact hQ.w)) v
      (pullback.snd t (pullback.snd f w)) ζ := by
    refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback t (pullback.snd f w))
    rw [pullback.lift_fst]
    exact hQ
  have hiso : IsPullback e.hom (pullback.snd t (pullback.snd f w))
      (pullback.snd p (pullback.fst f w)) (𝟙 (pullback f w)) :=
    IsPullback.of_horiz_isIso ⟨by rw [Category.comp_id]; exact he⟩
  have s2 := s1.paste_horiz hiso
  rw [Category.comp_id] at s2
  have s3 := s2.paste_horiz (IsPullback.of_hasPullback p (pullback.fst f w))
  rw [Category.assoc] at s3
  exact s3

/-- **The gluing isomorphism of a descent along an étale covering of the target.** Let
`f : X ⟶ Y` be a universal homeomorphism, let `w : W ⟶ Y` be a morphism and let `t : T ⟶ W` be
étale. If the base change of `T` to `W_X := X ×_Y W` is identified, over `W_X`, with the base
change of a scheme `U` over `X`, then there is an isomorphism `Θ : T ×_Y W ≅ W ×_Y T` over
`W ×_Y W` which preserves the `U`-component of every generalized point: this is a candidate
gluing isomorphism for a descent datum on `T` relative to `w`.

Both `T ×_Y W` and `W ×_Y T` are base changes of `t` along the two projections of `W ×_Y W`,
hence étale over `W ×_Y W`; after base change along the universal homeomorphism
`X ×_Y (W ×_Y W) ⟶ W ×_Y W` both become the base change of `U` along one and the same
projection to `X`, by `Stacks.Etale.isPullback_descentUComp`, so they are isomorphic there, and
`Stacks.Etale.exists_iso_of_pullback_iso` descends that isomorphism. The third conclusion is the
comparison of the two `U`-components, pulled back from `X ×_Y (W ×_Y W)` to an arbitrary
generalized point by `Stacks.Etale.comp_descentUComp`.

The cocycle condition is *not* among the conclusions and does not follow from the isomorphism
alone. -/
theorem exists_gluing_of_descentIso (f : X ⟶ Y) [UniversalHomeomorphism f]
    {U W T : Scheme.{u}} (p : U ⟶ X) (w : W ⟶ Y) (t : T ⟶ W) [Etale t]
    (e : pullback t (pullback.snd f w) ≅ pullback p (pullback.fst f w))
    (he : e.hom ≫ pullback.snd p (pullback.fst f w) = pullback.snd t (pullback.snd f w)) :
    ∃ Θ : pullback (t ≫ w) w ≅ pullback w (t ≫ w),
      Θ.hom ≫ pullback.fst w (t ≫ w) = pullback.fst (t ≫ w) w ≫ t ∧
      Θ.hom ≫ pullback.snd w (t ≫ w) ≫ t = pullback.snd (t ≫ w) w ∧
      ∀ {Z : Scheme.{u}} (c : Z ⟶ pullback (t ≫ w) w) (ζ₀ ζ₁ : Z ⟶ pullback f w)
        (h₀ : (c ≫ pullback.fst (t ≫ w) w) ≫ t = ζ₀ ≫ pullback.snd f w)
        (h₁ : (c ≫ Θ.hom ≫ pullback.snd w (t ≫ w)) ≫ t = ζ₁ ≫ pullback.snd f w),
        ζ₀ ≫ pullback.fst f w = ζ₁ ≫ pullback.fst f w →
        descentUComp f p w t e (c ≫ Θ.hom ≫ pullback.snd w (t ≫ w)) ζ₁ h₁ =
          descentUComp f p w t e (c ≫ pullback.fst (t ≫ w) w) ζ₀ h₀ := by
  have hπ : pullback.fst w w ≫ w = pullback.snd w w ≫ w := pullback.condition
  -- the two pullbacks of `T` to `W ×_Y W`, as morphisms to `W ×_Y W`
  have hs₀c : (pullback.fst (t ≫ w) w ≫ t) ≫ w = pullback.snd (t ≫ w) w ≫ w := by
    rw [Category.assoc]
    exact pullback.condition
  have hs₁c : pullback.fst w (t ≫ w) ≫ w = (pullback.snd w (t ≫ w) ≫ t) ≫ w := by
    rw [Category.assoc]
    exact pullback.condition
  set s₀ : pullback (t ≫ w) w ⟶ pullback w w :=
    pullback.lift (pullback.fst (t ≫ w) w ≫ t) (pullback.snd (t ≫ w) w) hs₀c with hs₀def
  set s₁ : pullback w (t ≫ w) ⟶ pullback w w :=
    pullback.lift (pullback.fst w (t ≫ w)) (pullback.snd w (t ≫ w) ≫ t) hs₁c with hs₁def
  have hs₀0 : s₀ ≫ pullback.fst w w = pullback.fst (t ≫ w) w ≫ t := pullback.lift_fst _ _ _
  have hs₀1 : s₀ ≫ pullback.snd w w = pullback.snd (t ≫ w) w := pullback.lift_snd _ _ _
  have hs₁0 : s₁ ≫ pullback.fst w w = pullback.fst w (t ≫ w) := pullback.lift_fst _ _ _
  have hs₁1 : s₁ ≫ pullback.snd w w = pullback.snd w (t ≫ w) ≫ t := pullback.lift_snd _ _ _
  -- each of them is a base change of `t`, hence étale
  have sq₀ : IsPullback (pullback.fst (t ≫ w) w) s₀ t (pullback.fst w w) := by
    refine IsPullback.of_bot ?_ hs₀0.symm (IsPullback.of_hasPullback w w)
    rw [hs₀1]
    exact IsPullback.of_hasPullback (t ≫ w) w
  have sq₁ : IsPullback (pullback.snd w (t ≫ w)) s₁ t (pullback.snd w w) := by
    refine IsPullback.of_bot ?_ hs₁1.symm (IsPullback.of_hasPullback w w).flip
    rw [hs₁0]
    exact (IsPullback.of_hasPullback w (t ≫ w)).flip
  have hEt₀ : Etale s₀ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) sq₀ inferInstance
  have hEt₁ : Etale s₁ :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Etale) sq₁ inferInstance
  -- the base change of `f` over `W ×_Y W` is a universal homeomorphism
  set g : pullback (pullback.fst w w ≫ w) f ⟶ pullback w w :=
    pullback.fst (pullback.fst w w ≫ w) f with hgdef
  set ξ : pullback (pullback.fst w w ≫ w) f ⟶ X :=
    pullback.snd (pullback.fst w w ≫ w) f with hξdef
  have hgc : g ≫ pullback.fst w w ≫ w = ξ ≫ f := pullback.condition
  have hg : UniversalHomeomorphism g :=
    universalHomeomorphism_of_isPullback (IsPullback.of_hasPullback (pullback.fst w w ≫ w) f)
  -- the two tautological lifts of `X ×_Y (W ×_Y W)` to `W_X`
  have hz₀c : ξ ≫ f = (g ≫ pullback.fst w w) ≫ w := by
    rw [Category.assoc]
    exact hgc.symm
  have hz₁c : ξ ≫ f = (g ≫ pullback.snd w w) ≫ w := by
    rw [Category.assoc, ← hπ]
    exact hgc.symm
  set ζ₀ : pullback (pullback.fst w w ≫ w) f ⟶ pullback f w :=
    pullback.lift ξ (g ≫ pullback.fst w w) hz₀c with hζ₀def
  set ζ₁ : pullback (pullback.fst w w ≫ w) f ⟶ pullback f w :=
    pullback.lift ξ (g ≫ pullback.snd w w) hz₁c with hζ₁def
  have hζ₀1 : ζ₀ ≫ pullback.fst f w = ξ := pullback.lift_fst _ _ _
  have hζ₀2 : ζ₀ ≫ pullback.snd f w = g ≫ pullback.fst w w := pullback.lift_snd _ _ _
  have hζ₁1 : ζ₁ ≫ pullback.fst f w = ξ := pullback.lift_fst _ _ _
  have hζ₁2 : ζ₁ ≫ pullback.snd f w = g ≫ pullback.snd w w := pullback.lift_snd _ _ _
  -- both base changes are base changes of `U` along one and the same projection to `X`
  have hQ₀ : IsPullback (pullback.fst s₀ g ≫ pullback.fst (t ≫ w) w) (pullback.snd s₀ g) t
      (ζ₀ ≫ pullback.snd f w) := by
    rw [hζ₀2]
    exact (IsPullback.of_hasPullback s₀ g).paste_horiz sq₀
  have hQ₁ : IsPullback (pullback.fst s₁ g ≫ pullback.snd w (t ≫ w)) (pullback.snd s₁ g) t
      (ζ₁ ≫ pullback.snd f w) := by
    rw [hζ₁2]
    exact (IsPullback.of_hasPullback s₁ g).paste_horiz sq₁
  have ha₀ := isPullback_descentUComp f p w t e he hQ₀
  have ha₁ := isPullback_descentUComp f p w t e he hQ₁
  rw [hζ₀1] at ha₀
  rw [hζ₁1] at ha₁
  -- hence they are isomorphic over `X ×_Y (W ×_Y W)`, and the isomorphism descends
  obtain ⟨d, hd, hd2⟩ := exists_iso_of_pullback_iso g s₀ s₁
    (ha₀.isoIsPullback _ _ ha₁) (ha₀.isoIsPullback_hom_snd _ _ ha₁)
  have hd1 : d.hom ≫ pullback.fst w (t ≫ w) = pullback.fst (t ≫ w) w ≫ t := by
    rw [← hs₁0, ← hs₀0, ← Category.assoc, hd]
  have hd1' : d.hom ≫ pullback.snd w (t ≫ w) ≫ t = pullback.snd (t ≫ w) w := by
    rw [← hs₁1, ← hs₀1, ← Category.assoc, hd]
  refine ⟨d, hd1, hd1', ?_⟩
  intro Z c ζ₀' ζ₁' h₀ h₁ hX
  -- factor the generalized point through `X ×_Y (W ×_Y W)`
  have hmc : (c ≫ s₀) ≫ pullback.fst w w ≫ w = (ζ₀' ≫ pullback.fst f w) ≫ f :=
    calc (c ≫ s₀) ≫ pullback.fst w w ≫ w
        = ((c ≫ pullback.fst (t ≫ w) w) ≫ t) ≫ w := by
          simp only [Category.assoc]
          rw [← Category.assoc s₀, hs₀0]
          simp only [Category.assoc]
      _ = (ζ₀' ≫ pullback.snd f w) ≫ w := by rw [h₀]
      _ = (ζ₀' ≫ pullback.fst f w) ≫ f := by
          rw [Category.assoc, ← pullback.condition, Category.assoc]
  set m : Z ⟶ pullback (pullback.fst w w ≫ w) f :=
    pullback.lift (c ≫ s₀) (ζ₀' ≫ pullback.fst f w) hmc with hmdef
  have hm1 : m ≫ g = c ≫ s₀ := pullback.lift_fst _ _ _
  have hm2 : m ≫ ξ = ζ₀' ≫ pullback.fst f w := pullback.lift_snd _ _ _
  have hmζ₀ : m ≫ ζ₀ = ζ₀' := by
    apply pullback.hom_ext
    · rw [Category.assoc, hζ₀1, hm2]
    · rw [Category.assoc, hζ₀2, ← Category.assoc, hm1, Category.assoc, hs₀0, ← Category.assoc,
        ← h₀]
  have hmζ₁ : m ≫ ζ₁ = ζ₁' := by
    apply pullback.hom_ext
    · rw [Category.assoc, hζ₁1, hm2, hX]
    · rw [Category.assoc, hζ₁2, ← Category.assoc, hm1, Category.assoc, hs₀1, ← h₁]
      simp only [Category.assoc, hd1']
  set n : Z ⟶ pullback s₀ g := pullback.lift c m hm1.symm with hndef
  have hn1 : n ≫ pullback.fst s₀ g = c := pullback.lift_fst _ _ _
  have hn2 : n ≫ pullback.snd s₀ g = m := pullback.lift_snd _ _ _
  have hnΘ1 : (n ≫ (ha₀.isoIsPullback _ _ ha₁).hom) ≫ pullback.fst s₁ g = c ≫ d.hom := by
    rw [Category.assoc, ← hd2, ← Category.assoc, hn1]
  have hnΘ2 : (n ≫ (ha₀.isoIsPullback _ _ ha₁).hom) ≫ pullback.snd s₁ g = m := by
    rw [Category.assoc, ha₀.isoIsPullback_hom_snd _ _ ha₁, hn2]
  -- the `U`-components of the two sides are both read off the same square
  have hleft : descentUComp f p w t e (c ≫ pullback.fst (t ≫ w) w) ζ₀' h₀ =
      n ≫ descentUComp f p w t e (pullback.fst s₀ g ≫ pullback.fst (t ≫ w) w)
        (pullback.snd s₀ g ≫ ζ₀) (by rw [Category.assoc]; exact hQ₀.w) := by
    rw [comp_descentUComp]
    congr 1
    · rw [← Category.assoc, hn1]
    · rw [← Category.assoc, hn2, hmζ₀]
  have hright : descentUComp f p w t e (c ≫ d.hom ≫ pullback.snd w (t ≫ w)) ζ₁' h₁ =
      (n ≫ (ha₀.isoIsPullback _ _ ha₁).hom) ≫
        descentUComp f p w t e (pullback.fst s₁ g ≫ pullback.snd w (t ≫ w))
          (pullback.snd s₁ g ≫ ζ₁) (by rw [Category.assoc]; exact hQ₁.w) := by
    rw [comp_descentUComp]
    congr 1
    · simp only [← Category.assoc, hnΘ1]
    · simp only [← Category.assoc, hnΘ2, hmζ₁]
  rw [hleft, hright, Category.assoc, ha₀.isoIsPullback_hom_fst _ _ ha₁]

end Stacks.Etale

end

end
