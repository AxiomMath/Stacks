module

public import StacksFrontier.AlgebraicGeometry.Picard.TorsionRankDisjointCover
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSchemeCurve.PointedCurveStructureSheaf
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceMiddleExactness
public import StacksFrontier.AlgebraicGeometry.PicardScheme.PicardSequenceSplitExact
public import Mathlib.AlgebraicGeometry.AlgClosed.Basic

/-!
# The rational points of the Picard functor of a pointed curve

Let `X ⟶ S` be a morphism of a big fppf site with a section, such that `𝒪_T ⟶ f_{T,*}𝒪_{X_T}` is
an isomorphism for every `S`-scheme `T` of the site.  The Picard sequence
`0 ⟶ Pic(T) ⟶ Pic(X_T) ⟶ Pic_{X/S}(T) ⟶ 0` of [Stacks, Tag 0B9N] is then exact, so at a test
scheme `T` with trivial Picard group the canonical map `Pic(X_T) ⟶ Pic_{X/S}(T)` is an
isomorphism.

For `S = Spec k` with `k` a field, the test scheme `T = S` has a one-point underlying space, so
`Pic(S) = 0`, and `X_S ≅ X`.  Hence for a smooth projective curve `X` over `k` with a
`k`-rational point — which supplies both the section and, by [Stacks, Tag 0B9U], the
isomorphism condition — the Picard group of `X` is the group of `k`-points of the Picard
functor:

`Pic(X) ≃+ Pic_{X/k}(Spec k)`.

This is the identification through which the source reads `Pic⁰(X)` as the `k`-points of
`Pic⁰_{X/k}` in the proof of [Stacks, Tag 0C1Z].

## Main definitions

* `Stacks.Picard.ofSchemeAddEquivOfIso`: pullback along an isomorphism of schemes, as an
  isomorphism of Picard groups.
* `Stacks.PicardFunctor.picardAtAddEquivOfSubsingleton`: `Pic(X_T) ≃+ Pic_{X/S}(T)` when
  `Pic(T) = 0`.
* `Stacks.PicardFunctor.ofSchemeAddEquivPicardFunctorTerminal`: `Pic(X) ≃+ Pic_{X/S}(S)` for a
  base `S` with discrete underlying space.
* `Stacks.PicardFunctor.ofSchemeAddEquivPicardFunctorOfCurve`: the same for a smooth projective
  curve over a field with a rational point.

## References

* [Stacks Project, Tag 0B9N](https://stacks.math.columbia.edu/tag/0B9N)
* [Stacks Project, Tag 0B9M](https://stacks.math.columbia.edu/tag/0B9M)
* [Stacks Project, Tag 0B9U](https://stacks.math.columbia.edu/tag/0B9U)
* [Stacks Project, Tag 0C1Z](https://stacks.math.columbia.edu/tag/0C1Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Picard

/-- **Pullback along an isomorphism of schemes is an isomorphism of Picard groups**, with inverse
the pullback along the inverse isomorphism. -/
def ofSchemeAddEquivOfIso {Y Z : Scheme.{u}} (e : Y ≅ Z) : ofScheme Z ≃+ ofScheme Y where
  toFun := schemePullbackClass e.hom
  invFun := schemePullbackClass e.inv
  left_inv x := by
    rw [schemePullbackClass_comp, e.inv_hom_id, schemePullbackClass_id]
  right_inv x := by
    rw [schemePullbackClass_comp, e.hom_inv_id, schemePullbackClass_id]
  map_add' := schemePullbackClass_add e.hom

/-- The isomorphism `ofSchemeAddEquivOfIso e` sends a class to its pullback along `e.hom`. -/
@[simp] theorem ofSchemeAddEquivOfIso_apply {Y Z : Scheme.{u}} (e : Y ≅ Z) (x : ofScheme Z) :
    ofSchemeAddEquivOfIso e x = schemePullbackClass e.hom x := rfl

end Stacks.Picard

namespace Stacks.PicardFunctor

variable (B : BigFppfSite.{u}) {X S : Scheme.{u}} (hX : B.Contains X) (hS : B.Contains S)
  (f : B.obj hX ⟶ B.obj hS) (σ : S ⟶ X) (hσ : σ ≫ B.inclusion.map f = 𝟙 S)
  (hOiso : ∀ U : BigFppfOver B S hS, IsIso (baseChangeProj B hX hS f U).toLRSHom.toHom.c)

include σ hσ hOiso in
/-- **At a test scheme with trivial Picard group, `Pic(X_T) ⟶ Pic_{X/S}(T)` is bijective**: it is
onto by [Stacks, Tag 0B9N], and its kernel is the image of `Pic(T) = 0` by
[Stacks, Tag 0B9M]. -/
theorem bijective_toPicardFunctorHom_of_subsingleton_overBase (T : BigFppfOver B S hS)
    [Subsingleton (Stacks.Picard.ofScheme ((BigFppfOver.toScheme B S hS).obj T))] :
    Function.Bijective (toPicardFunctorHom B hX hS f T) := by
  refine ⟨?_, surjective_toPicardFunctorHom B hX hS f σ hσ hOiso T⟩
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨P, rfl⟩ :=
    (exact_schemePullbackClass_baseChangeProj_toPicardFunctorHom_of_isIso_c B hX hS f hOiso T
      c).1 hc
  rw [Subsingleton.elim P 0]
  exact map_zero (Stacks.Picard.schemePullbackClassHom (baseChangeProj B hX hS f T))

/-- **`Pic(X_T) ≃+ Pic_{X/S}(T)` at a test scheme `T` with trivial Picard group.** -/
def picardAtAddEquivOfSubsingleton (T : BigFppfOver B S hS)
    [Subsingleton (Stacks.Picard.ofScheme ((BigFppfOver.toScheme B S hS).obj T))] :
    picardAt B hX hS f T ≃+ (picardFunctor B hX hS f).obj (Opposite.op T) :=
  AddEquiv.ofBijective (toPicardFunctorHom B hX hS f T)
    (bijective_toPicardFunctorHom_of_subsingleton_overBase B hX hS f σ hσ hOiso T)

/-- The isomorphism `picardAtAddEquivOfSubsingleton` is the map `toPicardFunctorHom`. -/
@[simp] theorem picardAtAddEquivOfSubsingleton_apply (T : BigFppfOver B S hS)
    [Subsingleton (Stacks.Picard.ofScheme ((BigFppfOver.toScheme B S hS).obj T))]
    (x : picardAt B hX hS f T) :
    picardAtAddEquivOfSubsingleton B hX hS f σ hσ hOiso T x = toPicardFunctorHom B hX hS f T x :=
  rfl

/-- The base `S` as the terminal `S`-scheme of the site. -/
abbrev terminalTest : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

/-- The base change `X ×_S S` of `X` along the identity of `S` is `X`. -/
def baseChangeTerminalIso : baseChange B hX hS f (terminalTest B hS) ≅ X :=
  haveI : IsIso (B.inclusion.map (terminalTest B hS).hom) :=
    CategoryTheory.Functor.map_isIso B.inclusion (𝟙 (B.obj hS))
  asIso (pullback.fst (B.inclusion.map f) (B.inclusion.map (terminalTest B hS).hom))

/-- **`Pic(X) ≃+ Pic_{X/S}(S)`** for a morphism `X ⟶ S` of the site with a section, satisfying the
isomorphism condition of [Stacks, Tag 0B9N], over a base `S` whose underlying space is discrete
(for instance the spectrum of a field), so that `Pic(S) = 0`. -/
def ofSchemeAddEquivPicardFunctorTerminal [DiscreteTopology S] :
    Stacks.Picard.ofScheme X ≃+ (picardFunctor B hX hS f).obj (Opposite.op (terminalTest B hS)) :=
  haveI : Subsingleton (Stacks.Picard.ofScheme
      ((BigFppfOver.toScheme B S hS).obj (terminalTest B hS))) :=
    Stacks.Picard.subsingleton_ofScheme_of_discreteTopology S
  (Stacks.Picard.ofSchemeAddEquivOfIso (baseChangeTerminalIso B hX hS f)).trans
    (picardAtAddEquivOfSubsingleton B hX hS f σ hσ hOiso (terminalTest B hS))

/-- A nonempty quasi-compact scheme locally of finite type over an algebraically closed field `k`
has a `k`-rational point. -/
theorem exists_section_of_isAlgClosed (k : Type u) [Field k] [IsAlgClosed k] {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [LocallyOfFiniteType g] [CompactSpace Y] [Nonempty Y] :
    ∃ σ : Spec (.of k) ⟶ Y, σ ≫ g = 𝟙 _ := by
  obtain ⟨x, -, hx⟩ := (isClosed_univ (X := Y)).exists_closed_singleton Set.univ_nonempty
  exact ⟨pointOfClosedPoint g x hx, pointOfClosedPoint_comp g x hx⟩

section Curve

variable (k : Type u) [Field k] [IsAlgClosed k] {hk : B.Contains (Spec (.of k))}
  (g : B.obj hX ⟶ B.obj hk) [IsCurve k (B.inclusion.map g)]
  [IsProjectiveVariety k (B.inclusion.map g)] [Smooth (B.inclusion.map g)]

/-- **The Picard group of a smooth projective curve over an algebraically closed field is the
group of `k`-points of its Picard functor**, `Pic(X) ≃+ Pic_{X/k}(Spec k)`.  A rational point
exists because `k` is algebraically closed; with it, [Stacks, Tag 0B9U] gives the isomorphism
condition of [Stacks, Tag 0B9N], and `Pic(Spec k) = 0`. -/
def ofSchemeAddEquivPicardFunctorOfCurve :
    Stacks.Picard.ofScheme X ≃+
      (picardFunctor B hX hk g).obj (Opposite.op (terminalTest B hk)) :=
  haveI : CompactSpace (B.inclusion.obj (B.obj hk)) :=
    (inferInstance : CompactSpace (Spec (.of k)))
  haveI : CompactSpace (B.inclusion.obj (B.obj hX)) :=
    QuasiCompact.compactSpace_of_compactSpace (B.inclusion.map g)
  haveI : Nonempty (B.inclusion.obj (B.obj hX)) :=
    (inferInstance : IsIntegral (B.inclusion.obj (B.obj hX))).nonempty
  ofSchemeAddEquivPicardFunctorTerminal B hX hk g
    (exists_section_of_isAlgClosed k (B.inclusion.map g)).choose
    (exists_section_of_isAlgClosed k (B.inclusion.map g)).choose_spec
    (fun U => isIso_c_baseChange_of_isCurve_of_section (B.inclusion.map g)
      (exists_section_of_isAlgClosed k (B.inclusion.map g)).choose
      (exists_section_of_isAlgClosed k (B.inclusion.map g)).choose_spec
      (B.inclusion.map U.hom))

end Curve

end Stacks.PicardFunctor

end
