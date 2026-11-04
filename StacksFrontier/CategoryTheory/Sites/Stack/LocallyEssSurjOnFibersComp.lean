module

public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberComp
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.PullbackFiberHom
public import StacksFrontier.CategoryTheory.Sites.Stack.FaithfulDescent
public import StacksFrontier.CategoryTheory.Sites.Stack.TwoFibreProductMorPresheafMap

/-!
# Cancelling and transporting local essential surjectivity on fibres

`CategoryTheory.Functor.LocallyEssSurjOnFibers` is the hypothesis of Stacks 06DV on a 1-morphism
of fibred categories over a site: every object of a fibre of the target is, over the members of a
covering sieve, in the essential image of the 1-morphism on fibres. This file records the two
structural properties of that condition which let it be checked after composing with a 1-morphism
that already has it, or after replacing a 1-morphism by a vertically 2-isomorphic one.

## Main results

* `CategoryTheory.Functor.locallyEssSurjOnFibers_comp_iff`: a first factor which is locally
  essentially surjective on fibres can be cancelled.
* `CategoryTheory.Functor.locallyEssSurjOnFibers_congr`: the condition depends on a 1-morphism
  only up to vertical natural isomorphism.
* `CategoryTheory.Functor.fiberIsoPullbackFiber`: a strongly cartesian morphism exhibits its
  domain as the chosen pullback, which is how a local preimage built by hand is turned into the
  datum the condition asks for.

## Implementation notes

The converse direction of the cancellation is where the work is: the covering sieve for the
composite is the bind of the covering sieve for the second factor with, over each of its members,
the covering sieve that the first factor's local essential surjectivity supplies at the chosen
local preimage. The three comparison isomorphisms of the chosen pullbacks —
`CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso`,
`CategoryTheory.Functor.pullbackFiberIso` and
`CategoryTheory.Functor.pullbackFiberCompIso` — then assemble the isomorphism wanted over a
member of the bind.

## References

* [Stacks Project, Tag 06DV](https://stacks.math.columbia.edu/tag/06DV)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.Functor

universe u₁ u₂ u₃ u₄ v₁ v₂


/-- Local essential surjectivity on fibres can be cancelled against a first factor that already
has it: if `F` is locally essentially surjective on fibres, then so is `F ⋙ G` exactly when `G`
is.

The forward direction only transports a local preimage along the fibre functor of `F`. The
converse binds the covering sieve for `G` with, over each of its members, the covering sieve for
`F` at the chosen local preimage. -/
theorem locallyEssSurjOnFibers_comp_iff
    {D : Type u₁} [Category.{v₁} D]
    {X : Type u₂} {Y : Type u₃} {Z : Type u₄}
    [Category.{v₂} X] [Category.{v₂} Y] [Category.{v₂} Z]
    {p : X ⥤ D} {q : Y ⥤ D} {r : Z ⥤ D}
    (hq : q.IsFibered) (hr : r.IsFibered)
    {F : X ⥤ Y} {G : Y ⥤ Z}
    (hF : p.IsFibredOneMorphism q F) (hG : q.IsFibredOneMorphism r G)
    (J : GrothendieckTopology D)
    (hess : Functor.LocallyEssSurjOnFibers hq hF.comp_eq J) :
    Functor.LocallyEssSurjOnFibers hr (hF.comp hG).comp_eq J ↔
      Functor.LocallyEssSurjOnFibers hr hG.comp_eq J := by
  have : q.IsFibered := hq
  have : r.IsFibered := hr
  have hobj : ∀ {V : D} (z : p.Fiber V),
      (Functor.fiberFunctorOfCompEq (hF.comp hG).comp_eq V).obj z =
        (Functor.fiberFunctorOfCompEq hG.comp_eq V).obj
          ((Functor.fiberFunctorOfCompEq hF.comp_eq V).obj z) := fun _ => Subtype.ext rfl
  refine ⟨fun h U x => ?_, fun h U x => ?_⟩
  · obtain ⟨R, hR, hloc⟩ := h U x
    refine ⟨R, hR, fun V f hf => ?_⟩
    obtain ⟨z, ⟨e⟩⟩ := hloc f hf
    exact ⟨_, ⟨(eqToIso (hobj z)).symm ≪≫ e⟩⟩
  · obtain ⟨R, hR, hGlocal⟩ := h U x
    let T : ∀ ⦃V⦄ (f : V ⟶ U), R.arrows f → Sieve V := fun {V} f hf =>
      (hess V (Classical.choose (hGlocal f hf))).choose
    refine ⟨Sieve.bind R T, J.transitive hR _ fun V f hf => J.superset_covering
      (Sieve.le_pullback_bind R T f hf)
        (hess V (Classical.choose (hGlocal f hf))).choose_spec.1, ?_⟩
    rintro W k ⟨V, g, f, hf, hg, rfl⟩
    let y := Classical.choose (hGlocal f hf)
    obtain ⟨eG⟩ := Classical.choose_spec (hGlocal f hf)
    have hgf : (hess V y).choose.arrows g := by
      simpa only [T, y] using hg
    obtain ⟨z, ⟨eF⟩⟩ := (hess V y).choose_spec.2 g hgf
    let hFf := Functor.fiberFunctorOfCompEq hF.comp_eq W
    let hGf := Functor.fiberFunctorOfCompEq hG.comp_eq W
    have e₁ : hGf.obj (hFf.obj z) ≅
        Functor.pullbackFiber r ((Functor.fiberFunctorOfCompEq hG.comp_eq V).obj y) g :=
      hGf.mapIso eF ≪≫ (hG.mapPullbackFiberIso y g).symm
    have e₂ : Functor.pullbackFiber r ((Functor.fiberFunctorOfCompEq hG.comp_eq V).obj y) g ≅
        Functor.pullbackFiber r (Functor.pullbackFiber r x f) g :=
      Functor.pullbackFiberIso eG g
    exact ⟨z, ⟨(eqToIso (hobj z)).symm ≪≫ e₁ ≪≫ e₂ ≪≫ Functor.pullbackFiberCompIso x f g⟩⟩

/-- Local essential surjectivity on fibres only depends on a 1-morphism up to vertical natural
isomorphism. -/
theorem locallyEssSurjOnFibers_congr
    {D : Type u₁} [Category.{v₁} D]
    {X : BasedCategory.{v₂, u₂} D} {Y : BasedCategory.{v₂, u₃} D}
    (hq : Y.p.IsFibered)
    {F G : X ⥤ᵇ Y} (e : F.toFunctor ≅ G.toFunctor)
    (he : ∀ (x : X.obj) {S : D} (_hx : X.p.obj x = S),
      Y.p.IsHomLift (𝟙 S) (e.hom.app x))
    (J : GrothendieckTopology D) :
    Functor.LocallyEssSurjOnFibers hq F.w J ↔
      Functor.LocallyEssSurjOnFibers hq G.w J := by
  constructor <;> intro h U y <;> obtain ⟨R, hR, hloc⟩ := h U y <;>
    refine ⟨R, hR, fun V f hf => ?_⟩ <;> obtain ⟨x, ⟨ex⟩⟩ := hloc f hf <;>
    have e₀ : (Functor.Fiber.mapOfComp X.p Y.p F.toFunctor F.w V).obj x ≅
        (Functor.Fiber.mapOfComp X.p Y.p G.toFunctor G.w V).obj x :=
      Functor.Fiber.isoMk (e.app x.1) (he x.1 x.2)
  exacts [⟨x, ⟨e₀.symm ≪≫ ex⟩⟩, ⟨x, ⟨e₀ ≪≫ ex⟩⟩]

/-- **A strongly cartesian morphism exhibits its domain as the chosen pullback.** Given an object
`x` of the fibre over `U`, an object `w` of the fibre over `V` and a strongly cartesian morphism
`ψ : w ⟶ x` over `f : V ⟶ U`, the comparison of `w` with the chosen cartesian lift of `f` at `x`
is an isomorphism of the fibre over `V`.

This is how a local preimage produced by a construction rather than by the chosen pullbacks is
turned into the datum that `CategoryTheory.Functor.LocallyEssSurjOnFibers` asks for. -/
noncomputable def fiberIsoPullbackFiber {𝒮 : Type u₁} [Category.{v₁} 𝒮] {𝒳 : Type u₂}
    [Category.{v₂} 𝒳] (p : 𝒳 ⥤ 𝒮) [p.IsFibered] {U V : 𝒮} (x : p.Fiber U) (f : V ⟶ U)
    (w : p.Fiber V) (ψ : w.1 ⟶ x.1) (hψ : p.IsStronglyCartesian f ψ) :
    w ≅ pullbackFiber p x f := by
  have := hψ
  have hbase : f = (Iso.refl V).hom ≫ f := by simp
  refine Fiber.isoMk
    (IsStronglyCartesian.domainIsoOfBaseIso p hbase (IsPreFibered.pullbackMap x.2 f) ψ) ?_
  rw [IsStronglyCartesian.domainIsoOfBaseIso_hom p hbase (IsPreFibered.pullbackMap x.2 f) ψ]
  simpa using IsStronglyCartesian.map_isHomLift p f (IsPreFibered.pullbackMap x.2 f) hbase ψ

end CategoryTheory.Functor

end
