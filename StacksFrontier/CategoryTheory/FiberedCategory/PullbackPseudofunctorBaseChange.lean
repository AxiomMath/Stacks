module

public import StacksFrontier.CategoryTheory.FiberedCategory.PullbackPseudofunctor
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberComp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of the comparison of two cartesian structures

Let `p : 𝒳 ⥤ 𝒮` be a fibred category and let `cF : CartStruct p f F` and `cG : CartStruct p f G`
be two cartesian structures over the same `f : W ⟶ U`, so that
`CategoryTheory.Functor.IsFibered.CartStruct.cmpIso` compares `F` and `G`.  Composing both with a
cartesian structure `cK : CartStruct p γ K` over a further `γ : W' ⟶ W` gives two cartesian
structures over `γ ≫ f`, and this file identifies their comparison: it is the image under `K` of
the comparison of `cF` with `cG`.

Both morphisms are vertical over `W'` and satisfy the triangle of
`CategoryTheory.Functor.IsFibered.CartStruct.cmpUnderlying_fac` for the composed structures — for
the image under `K` because the projections of `cK` are natural — so they agree by the uniqueness
clause `CategoryTheory.Functor.IsFibered.CartStruct.cmpUnderlying_uniq`.

Specialised to `cK = cartPullback γ` this says that the comparison morphism is compatible with the
base change `CategoryTheory.Functor.pullbackFiberHom` of a morphism of a fibre, which is the form
in which the comparison of the two composites around a cartesian square is restricted to a
covering of its exceptional corner.

Two further facts about the comparison are recorded here, both of which the base change is used
alongside.  Its commutation with a pair of morphisms of the two fibres is equivalent to a single
equation involving only the cartesian projections, which covers the pairs that do *not* come from
one morphism over the base and so are outside the reach of naturality; and the comparison of the
two chosen cartesian structures over a composite is the contraction
`CategoryTheory.Functor.pullbackFiberCompIso'` of an iterated chosen pullback, which is the
dictionary between the `cmpIso` language and the chosen-pullback language.

## Main results

* `CategoryTheory.Functor.IsFibered.CartStruct.cmpUnderlying_comp_right` and
  `CategoryTheory.Functor.IsFibered.CartStruct.cmpMor_comp_right`: the comparison of the two
  composed cartesian structures is the image of the comparison under `K`.
* `CategoryTheory.Functor.IsFibered.CartStruct.cmpIso_hom_app_comp_right`: the same for the
  components of `cmpIso`.
* `CategoryTheory.Functor.IsFibered.CartStruct.pullbackFiberHom_cmpMor`: the form with
  `cK = cartPullback γ`, stated with `CategoryTheory.Functor.pullbackFiberHom`.
* `CategoryTheory.Functor.IsFibered.CartStruct.cmpMor_trans`: transitivity of the comparison.
* `CategoryTheory.Functor.IsFibered.CartStruct.proj_cast`: the projections of a cartesian
  structure transported along an equality of its base morphism.
* `CategoryTheory.Functor.IsFibered.CartStruct.cmpIso_hom_app_comm`: the commutation criterion
  for a pair of morphisms across `cmpIso`.
* `CategoryTheory.Functor.IsFibered.CartStruct.cmpMor_cartPullbackOfEq`: the comparison of the
  two chosen cartesian structures over a composite is
  `CategoryTheory.Functor.pullbackFiberCompIso'`.
* `CategoryTheory.Functor.IsFibered.CartStruct.cmpMor_comp_cartPullback_cartPullbackOfEq`: a
  comparison against the chosen structure, after base change, is a base change followed by a
  contraction.

## References

* [Stacks Project, Tag 02XO](https://stacks.math.columbia.edu/tag/02XO)
-/

@[expose] public noncomputable section

namespace CategoryTheory.Functor.IsFibered

universe v₁ u₁ v₂ u₂

variable {𝒮 : Type u₁} {𝒳 : Type u₂} [Category.{v₁} 𝒮] [Category.{v₂} 𝒳]

attribute [local implicit_reducible] Fiber Fiber.fiberInclusion

namespace CartStruct

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {U W W' : 𝒮} {f : W ⟶ U} {γ : W' ⟶ W}
  {F G H : p.Fiber U ⥤ p.Fiber W} {K : p.Fiber W ⥤ p.Fiber W'}

/-- The comparison morphism of two cartesian structures, followed by the projection of the second,
is the projection of the first. -/
private theorem cmpMor_incl_comp_proj (cF : CartStruct p f F) (cG : CartStruct p f G)
    (a : p.Fiber U) :
    Fiber.fiberInclusion.map (cmpMor cF cG a) ≫ cG.proj a = cF.proj a := by
  rw [cmpMor_incl]
  exact cmpUnderlying_fac cF cG a

/-- **Transitivity of the comparison morphism.** Comparing `cF` with `cG` and then `cG` with `cH`
is comparing `cF` with `cH`.  This is `cmpUnderlying_comp` read in the fibre. -/
public theorem cmpMor_trans (cF : CartStruct p f F) (cG : CartStruct p f G)
    (cH : CartStruct p f H) (a : p.Fiber U) :
    cmpMor cF cG a ≫ cmpMor cG cH a = cmpMor cF cH a :=
  Fiber.fiberInclusion.map_injective <| by
    rw [Functor.map_comp, cmpMor_incl, cmpMor_incl, cmpMor_incl, cmpUnderlying_comp]

/-- **Base change of the underlying comparison morphism.** Composing two cartesian structures over
`f : W ⟶ U` with one over `γ : W' ⟶ W` multiplies their comparison by `K`: the comparison of the
composites is the image under `K` of the comparison of the two original structures.

Both sides are vertical over `W'` and compose with the projection of `CartStruct.comp cG cK` to the
projection of `CartStruct.comp cF cK`, so they agree by `cmpUnderlying_uniq`. -/
public theorem cmpUnderlying_comp_right (cF : CartStruct p f F) (cG : CartStruct p f G)
    (cK : CartStruct p γ K) (x : p.Fiber U) :
    cmpUnderlying (CartStruct.comp cF cK) (CartStruct.comp cG cK) x =
      Fiber.fiberInclusion.map (K.map (cmpMor cF cG x)) := by
  have hv : p.IsHomLift (𝟙 W') (Fiber.fiberInclusion.map (K.map (cmpMor cF cG x))) :=
    (K.map (cmpMor cF cG x)).2
  have hFx : (CartStruct.comp cF cK).proj x = cK.proj (F.obj x) ≫ cF.proj x := rfl
  have hGx : (CartStruct.comp cG cK).proj x = cK.proj (G.obj x) ≫ cG.proj x := rfl
  have hnat : Fiber.fiberInclusion.map (K.map (cmpMor cF cG x)) ≫ cK.proj (G.obj x) =
      cK.proj (F.obj x) ≫ Fiber.fiberInclusion.map (cmpMor cF cG x) :=
    cK.naturality (cmpMor cF cG x)
  refine (cmpUnderlying_uniq (CartStruct.comp cF cK) (CartStruct.comp cG cK) x _ ?_).symm
  rw [hGx, hFx, ← Category.assoc, hnat, Category.assoc, cmpMor_incl_comp_proj]

/-- **Base change of the comparison morphism of two cartesian structures**, in the fibre. This is
`cmpUnderlying_comp_right` read through `Fiber.fiberInclusion`. -/
public theorem cmpMor_comp_right (cF : CartStruct p f F) (cG : CartStruct p f G)
    (cK : CartStruct p γ K) (x : p.Fiber U) :
    cmpMor (CartStruct.comp cF cK) (CartStruct.comp cG cK) x = K.map (cmpMor cF cG x) :=
  Fiber.fiberInclusion.map_injective <| by
    rw [cmpMor_incl, cmpUnderlying_comp_right]

/-- **Base change of `cmpIso`.** The component at `x` of the comparison isomorphism of the two
composed cartesian structures is the image under `K` of the component at `x` of the comparison of
the two original ones. -/
public theorem cmpIso_hom_app_comp_right (cF : CartStruct p f F) (cG : CartStruct p f G)
    (cK : CartStruct p γ K) (x : p.Fiber U) :
    (cmpIso (CartStruct.comp cF cK) (CartStruct.comp cG cK)).hom.app x =
      K.map ((cmpIso cF cG).hom.app x) :=
  Fiber.fiberInclusion.map_injective <| by
    rw [cmpIso_hom_app_incl, cmpUnderlying_comp_right]
    exact congrArg (fun m ↦ Fiber.fiberInclusion.map (K.map m))
      (Fiber.fiberInclusion.map_injective (cmpIso_hom_app_incl cF cG x).symm)

/-- **The comparison morphism of two cartesian structures is compatible with base change.** The
base change along `γ` of the comparison of `cF` and `cG` is the comparison of the two structures
obtained by composing with the chosen cartesian structure of `γ`.

This is `cmpMor_comp_right` for `cK = cartPullback γ`, stated through
`CategoryTheory.Functor.pullbackFiberHom`. -/
public theorem pullbackFiberHom_cmpMor (cF : CartStruct p f F) (cG : CartStruct p f G)
    (γ : W' ⟶ W) (x : p.Fiber U) :
    Functor.pullbackFiberHom (cmpMor cF cG x) γ =
      cmpMor (CartStruct.comp cF (cartPullback γ)) (CartStruct.comp cG (cartPullback γ)) x := by
  have hcmp : cmpMor (CartStruct.comp cF (cartPullback γ)) (CartStruct.comp cG (cartPullback γ)) x =
      (fiberPullback γ).map (cmpMor cF cG x) :=
    cmpMor_comp_right cF cG (cartPullback γ) x
  rw [hcmp]
  exact (Functor.pullbackFiberHom_uniq (cmpMor cF cG x) γ _
    ((cartPullback γ).naturality (cmpMor cF cG x))).symm

omit [p.IsFibered] in
/-- The projections of a cartesian structure transported along an equality of its base morphism
are the projections of the structure itself: the type of the `proj` field does not mention the base
morphism.

This is what makes the structural isomorphism of a comparison functor attached to a *commutative*
square computable: that isomorphism compares the cartesian structure of one composite around the
square with the structure of the other composite, transported along the commutativity. -/
public theorem proj_cast {f f' : W ⟶ U} (h : f = f') {F : p.Fiber U ⥤ p.Fiber W}
    (c : CartStruct p f' F) (a : p.Fiber U) :
    (h ▸ c : CartStruct p f F).proj a = c.proj a := by
  subst h
  rfl

/-- **The commutation criterion for a pair of morphisms across `cmpIso`.** Let `cF` and `cG` be
cartesian structures over the same `f`, and let `α : F.obj a ⟶ F.obj b` and `δ : G.obj a ⟶ G.obj b`
be morphisms of the two fibres which need *not* come from a morphism `a ⟶ b`. They commute with the
comparison isomorphism as soon as the single equation below holds, which is their commutation read
after composition with the strongly cartesian projection of `cG`.

Naturality of `cmpIso` is the special case `α = F.map ψ`, `δ = G.map ψ`; the criterion covers the
pairs that are only locally of that form. -/
public theorem cmpIso_hom_app_comm (cF : CartStruct p f F) (cG : CartStruct p f G)
    {a b : p.Fiber U} (α : F.obj a ⟶ F.obj b) (δ : G.obj a ⟶ G.obj b)
    (h : Fiber.fiberInclusion.map α ≫ cF.proj b =
      cmpUnderlying cF cG a ≫ Fiber.fiberInclusion.map δ ≫ cG.proj b) :
    α ≫ (cmpIso cF cG).hom.app b = (cmpIso cF cG).hom.app a ≫ δ := by
  have hcart := cG.isCart b
  have hl : p.IsHomLift (𝟙 W) (Fiber.fiberInclusion.map α ≫ cmpUnderlying cF cG b) :=
    IsHomLift.comp_of_lift_id p W (Fiber.fiberInclusion.map α) (cmpUnderlying cF cG b)
  have hr : p.IsHomLift (𝟙 W) (cmpUnderlying cF cG a ≫ Fiber.fiberInclusion.map δ) :=
    IsHomLift.comp_of_lift_id p W (cmpUnderlying cF cG a) (Fiber.fiberInclusion.map δ)
  apply Fiber.fiberInclusion.map_injective
  rw [Functor.map_comp, Functor.map_comp, cmpIso_hom_app_incl, cmpIso_hom_app_incl]
  refine IsStronglyCartesian.ext p f (cG.proj b) (g := 𝟙 W) ?_
  rw [Category.assoc, cmpUnderlying_fac, h, Category.assoc]

/-! ### The comparison of the chosen structures is the contraction of an iterated pullback -/

section Contraction

variable {p : 𝒳 ⥤ 𝒮} [p.IsFibered] {T V Z : 𝒮}

/-- The chosen cartesian structure of `b`, read over a composite `ε ≫ f` that `b` is equal to. -/
public def cartPullbackOfEq {f : V ⟶ T} {ε : Z ⟶ V} {b : Z ⟶ T} (h : ε ≫ f = b) :
    CartStruct p (ε ≫ f) (fiberPullback (p := p) b) where
  proj w := IsPreFibered.pullbackMap w.2 b
  isCart w := by subst h; exact (cartPullback (p := p) (ε ≫ f)).isCart w
  naturality ψ := fiberPullbackMap_comm b ψ

/-- **The comparison of the two chosen cartesian structures over a composite is the contraction of
the iterated chosen pullback.** The comparison morphism from the composite of the chosen structures
of `f` and `ε` to the chosen structure of a morphism `b` equal to `ε ≫ f` is
`CategoryTheory.Functor.pullbackFiberCompIso'`.

Both are vertical and compose with the chosen cartesian lift of `b` to the composite of the chosen
lifts of `ε` and of `f` — for the contraction that is
`CategoryTheory.Functor.pullbackFiberCompIso'_hom_fac` — so they agree by `cmpUnderlying_uniq`.
This is the dictionary between the `cmpIso` language of the pullback pseudofunctor and the
`pullbackFiberCompIso'` language of the chosen pullbacks. -/
@[sga "1 VI 7.2" "partial"]
public theorem cmpMor_cartPullbackOfEq {f : V ⟶ T} {ε : Z ⟶ V} {b : Z ⟶ T} (h : ε ≫ f = b)
    (w : p.Fiber T) :
    cmpMor (CartStruct.comp (cartPullback f) (cartPullback ε)) (cartPullbackOfEq h) w =
      (Functor.pullbackFiberCompIso' w f ε b h).hom := by
  refine fiberHom_ext_pullback b _ _ ?_
  exact (cmpMor_incl_comp_proj (CartStruct.comp (cartPullback f) (cartPullback ε))
    (cartPullbackOfEq h) w).trans (Functor.pullbackFiberCompIso'_hom_fac w f ε b h).symm

/-- The chosen pullback of an object of a fibre is the value of the pullback functor.  Stated so
that `dsimp only` can force the two spellings of an iterated chosen pullback into one. -/
public theorem fiberPullback_obj_eq_pullbackFiber {V' U' : 𝒮} (g : V' ⟶ U') (a : p.Fiber U') :
    (fiberPullback (p := p) g).obj a = Functor.pullbackFiber p a g := rfl

/-- **The comparison against the chosen structure, after base change.** For a cartesian structure
`cA` over `f : V ⟶ T` and a morphism `γ : Z ⟶ V` with `γ ≫ f = q`, the comparison of `cA` composed
with the chosen structure of `γ` against the chosen structure of `q` is the base change along `γ`
of the comparison of `cA` against the chosen structure of `f`, followed by the contraction of the
iterated chosen pullback.

The comparison of `cA` against the chosen structure of `f` is passed as a morphism `m` satisfying
its defining triangle, rather than written out, so that the statement is about the chosen-pullback
spelling of the iterated pullback throughout.  Every comparison morphism appearing after a base
change is reduced by this to the two operations the chosen-pullback language has:
`CategoryTheory.Functor.pullbackFiberHom` and
`CategoryTheory.Functor.pullbackFiberCompIso'`. -/
public theorem cmpMor_comp_cartPullback_cartPullbackOfEq {f : V ⟶ T}
    {F : p.Fiber T ⥤ p.Fiber V} (cA : CartStruct p f F) {γ : Z ⟶ V} {q : Z ⟶ T}
    (hq : γ ≫ f = q) (w : p.Fiber T) (m : F.obj w ⟶ Functor.pullbackFiber p w f)
    (hm : Fiber.fiberInclusion.map m ≫ IsPreFibered.pullbackMap w.2 f = cA.proj w) :
    cmpMor (CartStruct.comp cA (cartPullback γ)) (cartPullbackOfEq hq) w =
      Functor.pullbackFiberHom m γ ≫ (Functor.pullbackFiberCompIso' w f γ q hq).hom := by
  have hL := cmpMor_incl_comp_proj (CartStruct.comp cA (cartPullback γ))
    (cartPullbackOfEq hq) w
  have hR : Fiber.fiberInclusion.map
        (Functor.pullbackFiberHom m γ ≫ (Functor.pullbackFiberCompIso' w f γ q hq).hom) ≫
        IsPreFibered.pullbackMap w.2 q =
      (CartStruct.comp cA (cartPullback γ)).proj w := by
    simp only [Functor.map_comp, Category.assoc]
    rw [Functor.pullbackFiberCompIso'_hom_fac, Functor.pullbackFiberHom_fac_assoc, hm]
    rfl
  refine fiberHom_ext_pullback q _ _ ?_
  exact hL.trans hR.symm

end Contraction

end CartStruct

end CategoryTheory.Functor.IsFibered

end
