module

public import StacksFrontier.CategoryTheory.Sites.Point.Basic
public import StacksFrontier.CategoryTheory.Sites.Point.OfToposPoint
public import StacksFrontier.CategoryTheory.Sites.Point.PrecoveragePoint
public import StacksFrontier.CategoryTheory.Sites.Point.StalkFunctor

/-!
# Points of a site in the sense of Stacks 00Y5 and Mathlib's points

A point of the site `(C, K)` in the sense of the source (Stacks 00Y5,
`CategoryTheory.Precoverage.Point`) and a point of the Grothendieck topology `K.toGrothendieck`
in Mathlib's sense (`CategoryTheory.GrothendieckTopology.Point`, a fibre functor in the sense of
SGA 4 IV 6.3, whose category of elements is cofiltered) carry the same information:

* every point `p` of the site gives a point of the topos `Sh(C)` (Stacks 00YA (1),
  `CategoryTheory.Precoverage.Point.toPointOfTopos`), hence a Mathlib point
  `CategoryTheory.Precoverage.Point.toGrothendieckPoint` (Stacks 00YA (2)), whose fibre functor is
  isomorphic to the fibre functor `u` of `p` (`toGrothendieckPointFiberIso`) and whose stalk
  functor on sheaves is isomorphic to the stalk functor of `p` (`toGrothendieckPointSheafFiberIso`);
* conversely the fibre functor of a Mathlib point satisfies the three conditions of Stacks 00Y5
  (`CategoryTheory.GrothendieckTopology.Point.toPrecoveragePoint`), with the same stalk functor.

In particular the category of elements of the functor `u` of a point in the sense of the source
is cofiltered, although this is not among the conditions of Stacks 00Y5.

## References

* [Stacks Project, Tag 00Y5](https://stacks.math.columbia.edu/tag/00Y5)
* [Stacks Project, Tag 00YA](https://stacks.math.columbia.edu/tag/00YA)
-/

@[expose] public section

open CategoryTheory Limits Opposite

universe u

namespace CategoryTheory

variable {C : Type u} [SmallCategory C] {K : Precoverage C} [K.HasPullbacks]

/-- The fibre functor of a point of the Grothendieck topology `K.toGrothendieck`, in Mathlib's
sense, is a point of the site `(C, K)` in the sense of Stacks 00Y5. -/
noncomputable def GrothendieckTopology.Point.toPrecoveragePoint
    (Φ : K.toGrothendieck.Point.{u}) : K.Point where
  fiber := Φ.fiber
  jointly_surjective R hR x := by
    obtain ⟨Y, g, ⟨Z, h, f, hf, rfl⟩, y, hy⟩ :=
      Φ.jointly_surjective _ (Precoverage.generate_mem_toGrothendieck hR) x
    exact ⟨Z, f, hf, Φ.fiber.map h y, by simpa using hy⟩
  pullback_bijective R hR Y Z f hf g := by
    have := K.hasPullbacks_of_mem g hR
    have := Presieve.hasPullback g hf
    have hb := Φ.fiber_pullbackComparison_bijective f g
    have hi : Function.Bijective
        (Types.pullbackIsoPullback (Φ.fiber.map f) (Φ.fiber.map g)).hom :=
      (isIso_iff_bijective _).mp inferInstance
    convert hi.comp hb using 1
    funext w
    apply Subtype.ext
    apply Prod.ext
    · simp only [Function.comp_apply, Types.pullbackIsoPullback_hom_fst]
      exact (ConcreteCategory.congr_hom (pullbackComparison_comp_fst Φ.fiber f g) w).symm
    · simp only [Function.comp_apply, Types.pullbackIsoPullback_hom_snd]
      exact (ConcreteCategory.congr_hom (pullbackComparison_comp_snd Φ.fiber f g) w).symm
  preservesFiniteLimits_sheafStalk := Φ.sheafFiber_leftExact

/-- The stalk functor of `Φ.toPrecoveragePoint` on sheaves is Mathlib's stalk functor
`Φ.sheafFiber`. -/
theorem GrothendieckTopology.Point.toPrecoveragePoint_sheafStalk
    (Φ : K.toGrothendieck.Point.{u}) :
    Φ.toPrecoveragePoint.sheafStalk = Φ.sheafFiber (A := Type u) :=
  rfl

namespace Precoverage.Point

variable [K.IsStableUnderBaseChange] (p : K.Point)

/-- **Stacks 00YA (1).** The skyscraper functor `u^s` and the stalk functor of a point `p` of the
site are a morphism of topoi `Sh(pt) → Sh(C)`. -/
noncomputable def toPointOfTopos : PointOfTopos.{u} K.toGrothendieck where
  pushforward := p.sheafPushforward
  inverseImage := p.sheafStalk
  adj := p.sheafAdjunction
  preservesFiniteLimits := inferInstance

/-- The point of the Grothendieck topology `K.toGrothendieck`, in Mathlib's sense, attached to a
point `p` of the site `(C, K)` in the sense of Stacks 00Y5: the point of the site that Stacks
00YA (2) attaches to the point `p.toPointOfTopos` of the topos. -/
noncomputable def toGrothendieckPoint : K.toGrothendieck.Point.{u} :=
  p.toPointOfTopos.sitePoint

/-- The stalk functor on sheaves of `p.toGrothendieckPoint` is the stalk functor of `p`. -/
noncomputable def toGrothendieckPointSheafFiberIso :
    p.toGrothendieckPoint.sheafFiber (A := Type u) ≅ p.sheafStalk :=
  p.toPointOfTopos.sheafFiberIsoInverseImage

/-- The stalk `(h_U)_p` of a representable presheaf at a point `p` is `u(U)`, naturally in `U`
(Stacks 00Y6). -/
noncomputable def fiberIsoYonedaCompPresheafStalk : p.fiber ≅ yoneda ⋙ p.presheafStalk :=
  NatIso.ofComponents (fun U => (Equiv.ofBijective _ (Phi_bijective p.fiber U)).toIso)
    (fun g => by
      ext x
      exact Phi_naturality p.fiber g x)

/-- The fibre functor of `p.toGrothendieckPoint` is isomorphic to the functor `u` of `p`. -/
noncomputable def toGrothendieckPointFiberIso : p.toGrothendieckPoint.fiber ≅ p.fiber :=
  Functor.isoWhiskerLeft shrinkYoneda.{u} p.stalkSheafificationIso.symm ≪≫
    Functor.isoWhiskerRight shrinkYonedaIsoYoneda p.presheafStalk ≪≫
      p.fiberIsoYonedaCompPresheafStalk.symm

end Precoverage.Point

end CategoryTheory
