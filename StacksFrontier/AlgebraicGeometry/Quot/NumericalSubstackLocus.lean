module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack
public import StacksFrontier.AlgebraicGeometry.Properties.Noetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardIdIso
public import StacksFrontier.Topology.Connected.ClopenIntersectionLocallyConnected
public import StacksFrontier.Topology.Noetherian.LocallyConnected

/-!
# Open and closed conditions on the objects of `Coh_{X/Y}`

Let `f : X ⟶ Y` be a finitely presented morphism of algebraic spaces, the standing data of
Stacks 08KB, and let `Q` be a condition on the objects `(T, g, 𝓕)` of `Coh_{X/Y}`.  The strictly
full subcategory of `Coh_{X/Y}` cut out by `Q` is an *open and closed substack* when its
inclusion is representable by open and closed immersions: for every object `A = (T, g, 𝓕)` the
2-fibre product `T ×_{Coh_{X/Y}} Coh^Q` is represented by an open and closed subscheme
`U ⊆ T`.  Since `Coh_{X/Y}` is fibred in groupoids (Stacks 08W5), an object of that 2-fibre
product over a scheme `T'` is a morphism `A' ⟶ A` of `Coh_{X/Y}` with `A'` satisfying `Q`, so
the condition says: a morphism `A' ⟶ A` lying over `h : T' ⟶ T` has `Q A'` exactly when `h`
factors through `U`.

The conditions of Situation 0DNC are of the form "`χ_i(t) = P(i)` for all `i ∈ I` and
`t ∈ T`", for functions `χ_i : |T| → ℤ` attached to every object and compatible with
pullback.  Such a condition is open and closed as soon as, on every object, the locus of `|T|`
where all the `χ_i` take the prescribed values is open and closed.  Each `χ_i` being locally
constant, that locus is always closed; it is open when `I` is finite, and when the family
`(χ_i)` factors near every point through a locally Noetherian scheme, whose connected
components are open.  The latter is the form in which Stacks 0DNE reaches its conclusion, by
absolute Noetherian approximation.

## Main definitions

* `AlgebraicGeometry.Space.CoherentObject.testScheme`: the test scheme `T` of an object of
  `Coh_{X/Y}`, as a scheme.
* `AlgebraicGeometry.Space.CoherentHom.baseScheme`: the morphism of test schemes underlying a
  morphism of `Coh_{X/Y}`.
* `AlgebraicGeometry.Space.CoherentSituation.IsOpenAndClosedCondition`: a condition on the
  objects of `Coh_{X/Y}` cuts out an open and closed substack.

## Main results

* `AlgebraicGeometry.Scheme.Opens.exists_comp_ι_eq_iff_range_subset`: a morphism of schemes
  factors through an open subscheme exactly when its image lies in it.
* `AlgebraicGeometry.Space.CoherentSituation.IsOpenAndClosedCondition.of_hom`: such a condition
  is inherited along every morphism of `Coh_{X/Y}`, so the subcategory it cuts out is strictly
  full.
* `AlgebraicGeometry.Space.CoherentSituation.isOpenAndClosedCondition_of_isClopen`: a condition
  of the form "`χ_i = c i` for all `i`", for functions compatible with pullback, is open and
  closed when each of its loci is.
* `AlgebraicGeometry.Space.CoherentSituation.isOpenAndClosedCondition_of_locally_factors`: and
  this holds when, near every point of every test scheme and after pulling back along a morphism
  open on points, the family `(χ_i)` factors through a locally Noetherian scheme carrying locally
  constant functions.

## Implementation notes

Stacks 04YM defines an open (or closed) substack of an *algebraic* stack, through the open (or
closed) immersions of algebraic stacks of Stacks 04YL; those are 1-morphisms representable by
algebraic spaces whose base changes to schemes are open (or closed) immersions, the notion of
Stacks 04XB.  `AlgebraicGeometry.Space.CoherentSituation.IsOpenAndClosedCondition` is that
04XB condition for the inclusion of a strictly full subcategory of `Coh_{X/Y}`, written out on
the objects and morphisms of Stacks 08KB: the base change to the scheme `T` of an object is the
functor of morphisms `T' ⟶ T` along which the pulled back object satisfies the condition, and it
is represented by the open and closed subscheme `U`.  It does not presuppose that `Coh_{X/Y}` is
algebraic.

## References

* [Stacks Project, Tag 0DNE](https://stacks.math.columbia.edu/tag/0DNE)
* [Stacks Project, Tag 0DND](https://stacks.math.columbia.edu/tag/0DND)
* [Stacks Project, Tag 0DNC](https://stacks.math.columbia.edu/tag/0DNC)
* [Stacks Project, Tag 04YM](https://stacks.math.columbia.edu/tag/04YM)
* [Stacks Project, Tag 08W5](https://stacks.math.columbia.edu/tag/08W5)
-/

@[expose] public noncomputable section

open CategoryTheory Topology

universe u

namespace AlgebraicGeometry.Scheme.Opens

/-- A morphism of schemes factors through an open subscheme exactly when its image lies in it. -/
theorem exists_comp_ι_eq_iff_range_subset {X Y : Scheme.{u}} (U : X.Opens) (h : Y ⟶ X) :
    (∃ l : Y ⟶ U.toScheme, l ≫ U.ι = h) ↔ Set.range h ⊆ U := by
  refine ⟨?_, fun hU => ⟨IsOpenImmersion.lift U.ι h (by rwa [Scheme.Opens.range_ι]),
    IsOpenImmersion.lift_fac _ _ _⟩⟩
  rintro ⟨l, rfl⟩
  rw [← Scheme.Opens.range_ι U, Scheme.Hom.comp_base, TopCat.coe_comp]
  exact Set.range_comp_subset_range _ _

end AlgebraicGeometry.Scheme.Opens

namespace AlgebraicGeometry.Space

open Scheme.Opens

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {D : CoherentSituation B S hS}

/-- The test scheme `T` of an object `(T, g, 𝓕)` of `Coh_{X/Y}`, as a scheme. -/
abbrev CoherentObject.testScheme (A : CoherentObject D) : Scheme.{u} :=
  (BigFppfOver.toScheme B S hS).obj A.T.left

/-- The morphism of test schemes underlying a morphism of `Coh_{X/Y}`. -/
abbrev CoherentHom.baseScheme {A' A : CoherentObject D} (φ : CoherentHom A' A) :
    A'.testScheme ⟶ A.testScheme :=
  (BigFppfOver.toScheme B S hS).map φ.base.left

namespace CoherentSituation

variable (D) in
/-- A condition `Q` on the objects of `Coh_{X/Y}` cuts out an **open and closed substack**: for
every object `A = (T, g, 𝓕)` there is an open subscheme `U ⊆ T` whose underlying set is closed,
such that a morphism `A' ⟶ A` of `Coh_{X/Y}` has `Q A'` exactly when its morphism of test schemes
factors through `U`.

This says that the inclusion of the strictly full subcategory cut out by `Q` is representable by
open and closed immersions: the 2-fibre product `T ×_{Coh_{X/Y}} Coh^Q` is represented by `U`. -/
def IsOpenAndClosedCondition (Q : CoherentObject D → Prop) : Prop :=
  ∀ A : CoherentObject D, ∃ U : A.testScheme.Opens, IsClosed (U : Set A.testScheme) ∧
    ∀ (A' : CoherentObject D) (φ : CoherentHom A' A),
      Q A' ↔ ∃ l : A'.testScheme ⟶ U.toScheme, l ≫ U.ι = φ.baseScheme

/-- A condition that cuts out an open and closed substack is inherited along every morphism of
`Coh_{X/Y}`: if `A' ⟶ A` and `Q A`, then `Q A'`.  In particular it is invariant under
isomorphism, so the subcategory it cuts out is strictly full. -/
theorem IsOpenAndClosedCondition.of_hom {Q : CoherentObject D → Prop}
    (hQ : IsOpenAndClosedCondition D Q) {A' A : CoherentObject D} (φ : CoherentHom A' A)
    (hA : Q A) : Q A' := by
  obtain ⟨U, -, hU⟩ := hQ A
  have hid := (exists_comp_ι_eq_iff_range_subset U _).1
    ((hU A (CoherentHom.id (modulePushforwardCoherence B S hS) A)).1 hA)
  refine (hU A' φ).2 ((exists_comp_ι_eq_iff_range_subset U _).2 ?_)
  rintro _ ⟨t, rfl⟩
  exact hid ⟨φ.baseScheme t, by simp [CoherentHom.id]⟩

/-- **A condition of numerical type is open and closed as soon as its loci are.**  Let `χ` attach
to every object `A = (T, g, 𝓕)` of `Coh_{X/Y}` a family of functions `χ_A i` on `|T|`, compatible
with pullback along the morphisms of `Coh_{X/Y}`.  If on every object the locus where all
`χ_A i` take the prescribed values `c i` is open and closed, then the condition "`χ_A i t = c i`
for all `i` and all `t`" cuts out an open and closed substack, represented on `A` by that
locus. -/
theorem isOpenAndClosedCondition_of_isClopen {ι : Sort*} {β : Type*}
    (χ : ∀ A : CoherentObject D, ι → A.testScheme → β) (c : ι → β)
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : ι) (t : A'.testScheme),
      χ A' i t = χ A i (φ.baseScheme t))
    (hclopen : ∀ A : CoherentObject D, IsClopen {t : A.testScheme | ∀ i, χ A i t = c i}) :
    IsOpenAndClosedCondition D fun A => ∀ i t, χ A i t = c i := by
  intro A
  refine ⟨⟨_, (hclopen A).isOpen⟩, (hclopen A).isClosed, fun A' φ => ?_⟩
  rw [exists_comp_ι_eq_iff_range_subset]
  constructor
  · rintro h _ ⟨t, rfl⟩ i
    exact (hχ φ i t).symm.trans (h i t)
  · intro h i t
    exact (hχ φ i t).trans (h ⟨t, rfl⟩ i)

/-- **The Noetherian reduction.**  Let `χ` attach to every object `A = (T, g, 𝓕)` of `Coh_{X/Y}`
a family of functions `χ_A i` on `|T|`, compatible with pullback along the morphisms of
`Coh_{X/Y}`.  Suppose that every point `t` of every test scheme is the image of a point `t'` under
a morphism `p : T' ⟶ T` of schemes that is open on points (an open immersion, an étale or a
smooth morphism), and that near `t'` the family `χ_A ∘ p` factors, along a map continuous at
`t'`, through a locally Noetherian scheme carrying locally constant functions.  Then the
condition "`χ_A i t = c i` for all `i` and all `t`" cuts out an open and closed substack of
`Coh_{X/Y}`, however large the index set.

This is how the proof of Stacks 0DNE concludes: after absolute Noetherian approximation the
object comes from a locally Noetherian base, over which the family is pulled back from a
locally Noetherian scheme, and there the connected components are open. -/
theorem isOpenAndClosedCondition_of_locally_factors {ι : Sort*} {β : Type*}
    (χ : ∀ A : CoherentObject D, ι → A.testScheme → β) (c : ι → β)
    (hχ : ∀ {A' A : CoherentObject D} (φ : CoherentHom A' A) (i : ι) (t : A'.testScheme),
      χ A' i t = χ A i (φ.baseScheme t))
    (hfac : ∀ (A : CoherentObject D) (t : A.testScheme), ∃ (T' : Scheme.{u})
      (p : T' ⟶ A.testScheme) (t' : T'), p t' = t ∧ IsOpenMap p ∧ ∃ V ∈ 𝓝 t',
        ∃ (T₀ : Scheme.{u}) (_ : IsLocallyNoetherian T₀) (g : T' → T₀) (χ₀ : ι → T₀ → β),
          ContinuousAt g t' ∧ (∀ i, IsLocallyConstant (χ₀ i)) ∧
            ∀ i, ∀ y ∈ V, χ A i (p y) = χ₀ i (g y)) :
    IsOpenAndClosedCondition D fun A => ∀ i t, χ A i t = c i := by
  refine isOpenAndClosedCondition_of_isClopen χ c hχ fun A => ?_
  refine isClopen_setOf_forall_eq_of_locally_factors (fun t => ?_) c
  obtain ⟨T', p, t', hpt, hp, V, hV, T₀, hT₀, g, χ₀, hg, hχ₀, hfac⟩ := hfac A t
  exact ⟨T', inferInstance, p, t', hpt, hp, V, hV, T₀, inferInstance,
    TopologicalSpace.IsLocallyNoetherianSpace.locallyConnectedSpace T₀
      (isLocallyNoetherianSpace_of_isLocallyNoetherian T₀), g, χ₀, hg, hχ₀, hfac⟩

end CoherentSituation

end AlgebraicGeometry.Space

end
