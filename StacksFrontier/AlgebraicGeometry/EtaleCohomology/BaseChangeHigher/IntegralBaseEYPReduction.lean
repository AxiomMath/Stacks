module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.SmallEtaleBaseChangeAbBridge
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Existence

/-!
# [Stacks, Tag 0EYP] for abelian sheaves, from the sets-level statement

For a cartesian square `sq₂ : IsPullback π' f'' f' π` of bare schemes with `π` integral,

```
IsIso (smallEtaleBaseChangeAb f' π π' f'' sq₂.w)
```

is [Stacks, Tag 0EYP] for abelian sheaves on Mathlib's small étale sites — the assertion that the
base change map `(f')⁻¹ π_* ⟶ π'_* (f'')⁻¹` is invertible at *every* abelian sheaf.

It is not a hypothesis of anything in the library. In particular
`Stacks.EtaleCohomology.isIso_higherBaseChangeMapAb_app_of_isIso_collapsed`, the formalization of
[Stacks, Tag 0F05], does not assume it: that proof needs the base change map only at sheaves
annihilated by `n`, and there the source's own `BC(f, n, q - 1)` supplies it, by
`Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_app_of_annihilated`. What this file provides
is the unrestricted statement, for whoever wants it at an arbitrary abelian sheaf.

Tag 0EYP itself is stated for sheaves of **sets** on the size-bounded small étale sites of
[Stacks, Tag 021B], where the square lives in the underlying category of a big étale site of
[Stacks, Tag 021A]. This file crosses that gap: assuming the sets-level statement `H` for every
big étale site, the abelian statement holds at an *arbitrary* cartesian square of bare schemes
with integral bottom, with no size hypothesis at all.

The two steps are:

* the transport across sites and coefficients, which is
  `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleBaseChangeNatTrans`;
* the manufacture of a big étale site containing the four given schemes, which is
  `AlgebraicGeometry.BigEtaleSite.ofSet` applied to the four-element — hence `Small.{u}` — set
  `{X', S', X'', S''}`. The four given morphisms are then read as morphisms of `B.Scheme` by
  `CategoryTheory.ObjectProperty.homMk`, and `B.inclusion.map` sends them back to themselves
  definitionally, since `B.Scheme` is a full subcategory of `Scheme.{u}`.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_setsLevel0EYP` — the transport inside
  one fixed big étale site.
* `Stacks.EtaleCohomology.h0EYP_of_setsLevel0EYP` — the abelian [Stacks, Tag 0EYP] at an
  arbitrary cartesian square of bare schemes with integral bottom.

## References

* [Stacks Project, Tag 0F05](https://stacks.math.columbia.edu/tag/0F05)
* [Stacks Project, Tag 0EYP](https://stacks.math.columbia.edu/tag/0EYP)
* [Stacks Project, Tag 021A](https://stacks.math.columbia.edu/tag/021A)
* [Stacks Project, Tag 021B](https://stacks.math.columbia.edu/tag/021B)
-/

@[expose] public section

universe u

open CategoryTheory AlgebraicGeometry

namespace Stacks.EtaleCohomology

/-- **The sets-level [Stacks, Tag 0EYP] discharges the abelian one, inside a fixed big étale
site.** With the four morphisms of `B.Scheme` arranged as a commuting square whose image under
`B.inclusion` is cartesian with integral bottom `B.inclusion.map a`, the hypothesis `H` — the
sets-level comparison of [Stacks, Tag 021B] being invertible on each sheaf — forces the abelian
comparison `Stacks.EtaleCohomology.smallEtaleBaseChangeAb` of the image square to be invertible.

Everything here is formal: `H` is applied objectwise and promoted to invertibility of the natural
transformation, which the bridge lemma then transports to the abelian comparison. -/
public theorem isIso_smallEtaleBaseChangeAb_of_setsLevel0EYP (B : BigEtaleSite.{u})
    (H : ∀ {X' X Y' Y : B.Scheme}
           (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y),
           IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
             (B.inclusion.map g) →
           [IsIntegralHom (B.inclusion.map f)] → ∀ (h : g' ≫ f = f' ≫ g)
           (F : Sheaf (SmallEtale.topology B X.1 X.property) (Type (u + 1))),
           IsIso ((smallEtaleBaseChangeNatTrans B g' f' f g h).app F))
    {Z Z' W W' : B.Scheme} (a : Z ⟶ W) (b : W' ⟶ W) (b' : Z' ⟶ Z) (a' : Z' ⟶ W')
    (hcomm : b' ≫ a = a' ≫ b)
    (hsq : IsPullback (B.inclusion.map b') (B.inclusion.map a') (B.inclusion.map a)
      (B.inclusion.map b))
    (hint : IsIntegralHom (B.inclusion.map a))
    (w : B.inclusion.map a' ≫ B.inclusion.map b = B.inclusion.map b' ≫ B.inclusion.map a) :
    IsIso (Stacks.EtaleCohomology.smallEtaleBaseChangeAb (B.inclusion.map b) (B.inclusion.map a)
      (B.inclusion.map a') (B.inclusion.map b') w) := by
  have := hint
  have : ∀ F, IsIso ((smallEtaleBaseChangeNatTrans B b' a' a b hcomm).app F) :=
    fun F => H b' a' a b hsq hcomm F
  exact Stacks.EtaleCohomology.isIso_smallEtaleBaseChangeAb_of_isIso_smallEtaleBaseChangeNatTrans
    B a b b' a' hcomm (fun F => inferInstance) w

/-- **The abelian [Stacks, Tag 0EYP] follows from the sets-level [Stacks, Tag 0EYP].** Given `H`,
the statement of [Stacks, Tag 0EYP] for sheaves of sets on the size-bounded small étale sites of
[Stacks, Tag 021B] — for *every* big étale site of [Stacks, Tag 021A] — the abelian base change
comparison of an arbitrary cartesian square

```
X'' --π'--> X'
|f''        |f'
v           v
S'' --π---> S'
```

of bare schemes with `π` integral is an isomorphism. This is the unrestricted abelian form of the
tag.

No size hypothesis is needed on the square: the four schemes form a four-element, hence
`Small.{u}`, set of schemes, and `AlgebraicGeometry.BigEtaleSite.ofSet` produces a big étale site
containing all four. Their morphisms are morphisms of that site's full subcategory on the nose. -/
public theorem h0EYP_of_setsLevel0EYP
    (H : ∀ (B : AlgebraicGeometry.BigEtaleSite.{u}) {X' X Y' Y : B.Scheme}
           (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y),
           IsPullback (B.inclusion.map g') (B.inclusion.map f') (B.inclusion.map f)
             (B.inclusion.map g) →
           [IsIntegralHom (B.inclusion.map f)] → ∀ (h : g' ≫ f = f' ≫ g)
           (F : CategoryTheory.Sheaf (AlgebraicGeometry.SmallEtale.topology B X.1 X.property)
                  (Type (u + 1))),
           IsIso ((AlgebraicGeometry.smallEtaleBaseChangeNatTrans B g' f' f g h).app F))
    {X' S' X'' S'' : Scheme.{u}} (f' : X' ⟶ S') (π : S'' ⟶ S') (π' : X'' ⟶ X')
    (f'' : X'' ⟶ S'') (sq₂ : IsPullback π' f'' f' π) [IsIntegralHom π] :
    IsIso (Stacks.EtaleCohomology.smallEtaleBaseChangeAb f' π π' f'' sq₂.w) := by
  obtain ⟨B, hX', hS', hX'', hS''⟩ :
      ∃ B : BigEtaleSite.{u},
        B.Contains X' ∧ B.Contains S' ∧ B.Contains X'' ∧ B.Contains S'' := by
    have := small_single.{u} S''
    have : Small.{u} ({X', S', X'', S''} : Set Scheme.{u}) := inferInstance
    refine ⟨BigEtaleSite.ofSet ({X', S', X'', S''} : Set Scheme.{u}), ?_, ?_, ?_, ?_⟩ <;>
      exact BigEtaleSite.contains_ofSet _ (by simp)
  exact isIso_smallEtaleBaseChangeAb_of_setsLevel0EYP B (fun g' f' f g hsq => H B g' f' f g hsq)
    (Z := B.obj S'' hS'') (W := B.obj S' hS') (Z' := B.obj X'' hX'') (W' := B.obj X' hX')
    (ObjectProperty.homMk π) (ObjectProperty.homMk f') (ObjectProperty.homMk f'')
    (ObjectProperty.homMk π') (ObjectProperty.hom_ext _ sq₂.w.symm) sq₂.flip ‹_› sq₂.w

end Stacks.EtaleCohomology

end
