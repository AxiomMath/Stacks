module

public import StacksFrontier.CategoryTheory.FiberedCategory.PullbackPseudofunctorBaseChange
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.Dictionary

/-!
# The comparison of the two composites around a commutative square, in the chosen-pullback language

Let `p : 𝒳 ⥤ 𝒮` be a fibred category and let

```
  E --d--> X'
  |         |
  e         b
  |         |
  v         v
  Z --z--> X
```

be a commutative square of `𝒮`.  The two composites around it carry cartesian structures
`CategoryTheory.Functor.IsFibered.cartComp z e` and `cartComp b d`, the second read over the first
one's base morphism through the commutativity, and
`CategoryTheory.Functor.IsFibered.CartStruct.cmpMor` compares them.  This file identifies that
comparison.  The file supplies the tools that compute it in the chosen-pullback language, and the
dictionary between the two base-change operations on a morphism between chosen pullbacks.

Each of the two cartesian structures around the square is compared with the chosen cartesian
structure of a morphism `n : E ⟶ X` that both composites are equal to, and the comparison with a
chosen structure is pinned down by its own defining triangle: that is
`CategoryTheory.Functor.IsFibered.CartStruct.cmpMor_cartPullbackOfEq_eq_of_fac`, whose morphism is
an argument rather than inferred, so that the contraction
`CategoryTheory.Functor.pullbackFiberCompIso'` of an iterated chosen pullback can be handed to it
with `CategoryTheory.Functor.pullbackFiberCompIso'_hom_fac` as the triangle.  Composing the two
comparisons with `CategoryTheory.Functor.IsFibered.CartStruct.cmpMor_trans` then expresses the
comparison of the two composites by the two contractions.

Alongside this, two facts about `CategoryTheory.Functor.baseChangeFiberMor` are recorded.  Base
change over a named composite determines, and is determined by, the base change of
`CategoryTheory.Functor.pullbackFiberHom`, because the two differ by a contraction isomorphism on
each side; and conjugating a morphism between chosen pullbacks along a *named* composite into the
iterated chosen pullback commutes with further base change, which is the dictionary between a datum
given over an object of a slice and the same datum read in the fibre over a pullback of the base.
The second is proved from
`CategoryTheory.Functor.pullbackFiberCompIso'_pentagon`, the compatibility of the two ways of
contracting a threefold chosen pullback.

## Main results

* `CategoryTheory.Functor.pullbackFiberHom_eq_of_baseChangeFiberMor_eq` and
  `CategoryTheory.Functor.baseChangeFiberMor_eq_of_pullbackFiberHom_eq`: base change over a named
  composite and `pullbackFiberHom` determine each other.
* `CategoryTheory.Functor.baseChangeFiberMor_conj`: base change of a conjugated morphism.
* `CategoryTheory.Functor.IsFibered.CartStruct.cmpMor_cartPullbackOfEq_eq_of_fac`: the comparison
  against the chosen cartesian structure of a named composite, from its defining triangle.
* `CategoryTheory.Functor.fiberPullback_map_eq_pullbackFiberHom`: the pullback functor acts on
  morphisms by base change.

## References

* [Stacks Project, Tag 02XO](https://stacks.math.columbia.edu/tag/02XO)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor

universe v₁ u₁ v₂ u₂

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]
variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered]

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion IsFibered.fiberPullback

/-- Two morphisms between the chosen pullbacks of `x` and `y` along `F` whose base changes along
`g` over a named composite agree have equal base changes in the `pullbackFiberHom` sense.

The two operations differ by a contraction isomorphism on each side, which is what
`CategoryTheory.Functor.baseChangeFiberMor` composes `pullbackFiberHom` with. -/
public theorem pullbackFiberHom_eq_of_baseChangeFiberMor_eq {U V W : 𝒮} {x y : p.Fiber U}
    {F : V ⟶ U} (m m' : pullbackFiber p x F ⟶ pullbackFiber p y F) (g : W ⟶ V) {mx : W ⟶ U}
    (hmx : g ≫ F = mx)
    (h : baseChangeFiberMor m g mx hmx mx hmx = baseChangeFiberMor m' g mx hmx mx hmx) :
    pullbackFiberHom m g = pullbackFiberHom m' g := by
  rw [baseChangeFiberMor, baseChangeFiberMor, cancel_epi, cancel_mono] at h
  exact h

/-- The converse of `CategoryTheory.Functor.pullbackFiberHom_eq_of_baseChangeFiberMor_eq`: equal
base changes in the `pullbackFiberHom` sense give equal base changes over a named composite. -/
public theorem baseChangeFiberMor_eq_of_pullbackFiberHom_eq {U V W : 𝒮} {x y : p.Fiber U}
    {F : V ⟶ U} (m m' : pullbackFiber p x F ⟶ pullbackFiber p y F) (g : W ⟶ V) {mx : W ⟶ U}
    (hmx : g ≫ F = mx) (h : pullbackFiberHom m g = pullbackFiberHom m' g) :
    baseChangeFiberMor m g mx hmx mx hmx = baseChangeFiberMor m' g mx hmx mx hmx := by
  rw [baseChangeFiberMor, baseChangeFiberMor, h]

/-- **Base change of a conjugated morphism.** A morphism `m` between the chosen pullbacks of `x`
and `y` along a named composite `F' = g ≫ F` can be read, by conjugating with the contraction
isomorphisms, as a morphism between the chosen pullbacks along `g` of the chosen pullbacks along
`F`.  Its base change along a further `ε` is the same reading of the base change of `m` along `ε`.

Both sides are computed from `CategoryTheory.Functor.pullbackFiberCompIso'_pentagon`, which says
that contracting a threefold chosen pullback from the inside and from the outside agree. -/
public theorem baseChangeFiberMor_conj {U V V' Z : 𝒮} {x y : p.Fiber U} {F : V ⟶ U} {g : V' ⟶ V}
    {F' : V' ⟶ U} (hF' : g ≫ F = F') (m : pullbackFiber p x F' ⟶ pullbackFiber p y F')
    {ε : Z ⟶ V'} {q : Z ⟶ V} (hq : ε ≫ g = q) {r : Z ⟶ U} (hr : q ≫ F = r) (hr' : ε ≫ F' = r) :
    baseChangeFiberMor
        ((pullbackFiberCompIso' x F g F' hF').hom ≫ m ≫ (pullbackFiberCompIso' y F g F' hF').inv)
        ε q hq q hq =
      (pullbackFiberCompIso' x F q r hr).hom ≫ baseChangeFiberMor m ε r hr' r hr' ≫
        (pullbackFiberCompIso' y F q r hr).inv := by
  have key (w : p.Fiber U) : pullbackFiberHom (pullbackFiberCompIso' w F g F' hF').hom ε =
      (pullbackFiberCompIso' (pullbackFiber p w F) g ε q hq).hom ≫
        (pullbackFiberCompIso' w F q r hr).hom ≫
          (pullbackFiberCompIso' w F' ε r hr').inv := by
    rw [← Category.assoc, Iso.eq_comp_inv]
    exact pullbackFiberCompIso'_pentagon w F g ε F' hF' q hq r hr
  have hyiso : pullbackFiberIso (pullbackFiberCompIso' y F g F' hF') ε =
      (pullbackFiberCompIso' (pullbackFiber p y F) g ε q hq) ≪≫
        (pullbackFiberCompIso' y F q r hr) ≪≫ (pullbackFiberCompIso' y F' ε r hr').symm :=
    Iso.ext (by simpa using key y)
  have hy : pullbackFiberHom (pullbackFiberCompIso' y F g F' hF').inv ε =
      (pullbackFiberCompIso' y F' ε r hr').hom ≫
        (pullbackFiberCompIso' y F q r hr).inv ≫
          (pullbackFiberCompIso' (pullbackFiber p y F) g ε q hq).inv := by
    have h0 : pullbackFiberHom (pullbackFiberCompIso' y F g F' hF').inv ε =
        (pullbackFiberIso (pullbackFiberCompIso' y F g F' hF') ε).inv := rfl
    rw [h0, hyiso]
    simp
  rw [baseChangeFiberMor, baseChangeFiberMor, pullbackFiberHom_comp, pullbackFiberHom_comp,
    key x, hy]
  simp

namespace IsFibered

namespace CartStruct

/-- **The comparison against the chosen cartesian structure of a named composite, from its defining
triangle.** The comparison morphism from a cartesian structure `cA` over `ε ≫ f` to the chosen
cartesian structure of a morphism `q` that `ε ≫ f` is equal to is pinned down by its own
factorization: any morphism of the fibre whose composite with the chosen cartesian lift of `q` is
the projection of `cA` *is* that comparison.

This is the form in which the comparison of the two composites around a commutative square is
computed.  Each of the two cartesian structures around the square is compared with the chosen
structure of a morphism `n` that both composites are equal to, by this lemma with the contraction
`CategoryTheory.Functor.pullbackFiberCompIso'` of the corresponding iterated chosen pullback as the
morphism — its triangle being
`CategoryTheory.Functor.pullbackFiberCompIso'_hom_fac` — and
`CategoryTheory.Functor.IsFibered.CartStruct.cmpMor_trans` then composes the two comparisons.

Unlike `CategoryTheory.Functor.IsFibered.CartStruct.cmpUnderlying_uniq`, which this is a corollary
of, the morphism is an argument rather than inferred, so no verticality side condition has to be
discharged at the call site: the morphism is given as a morphism of the fibre and is therefore
vertical by construction. -/
public theorem cmpMor_cartPullbackOfEq_eq_of_fac {T V Z : 𝒮} {f : V ⟶ T} {ε : Z ⟶ V} {q : Z ⟶ T}
    (hq : ε ≫ f = q) {F : p.Fiber T ⥤ p.Fiber Z} (cA : CartStruct p (ε ≫ f) F) (w : p.Fiber T)
    (m : F.obj w ⟶ (fiberPullback (p := p) q).obj w)
    (hm : Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap w.2 q = cA.proj w) :
    cmpMor cA (cartPullbackOfEq hq) w = m := by
  refine fiberHom_ext_pullback q _ _ ?_
  rw [cmpMor_incl, hm]
  exact cmpUnderlying_fac cA (cartPullbackOfEq hq) w

end CartStruct

end IsFibered

/-- The action of a pullback functor on a morphism of a fibre is the base change of that morphism:
the two constructions are pinned down by the same factorization through the chosen cartesian lift,
`CategoryTheory.Functor.IsFibered.fiberPullbackMap_comm` for the one and
`CategoryTheory.Functor.pullbackFiberHom_fac` for the other. -/
public theorem fiberPullback_map_eq_pullbackFiberHom {U V : 𝒮} (f : V ⟶ U) {x y : p.Fiber U}
    (ψ : x ⟶ y) : (IsFibered.fiberPullback (p := p) f).map ψ = pullbackFiberHom ψ f :=
  pullbackFiberHom_uniq ψ f _ (IsFibered.fiberPullbackMap_comm f ψ)

end CategoryTheory.Functor

end
