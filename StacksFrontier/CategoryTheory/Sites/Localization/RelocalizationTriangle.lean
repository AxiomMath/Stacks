module
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Relocalization: the triangle `j_V = j_U ∘ j` of localization functors

Stacks tag 03EH. For a morphism `f : V ⟶ U` in a site `(C, J)` the localization functors
`j_V = Over.forget V`, `j_U = Over.forget U` and the relocalization functor
`j = Over.map f` form a commuting triangle `j_U ∘ j = j_V`; all three are continuous and
cocontinuous for the localized topologies, and under the identification
`(C/U)/(V/U) ≌ C/V` the functor `j` is the localization functor of `V/U` inside `C/U`.
On sheaves with values in an arbitrary category `A` this yields
`j_V⁻¹ = j⁻¹ ∘ j_U⁻¹` as a strict equality of pushforward-along-continuous functors,
whereas the left adjoints only satisfy `j_{V!} ≅ j_{U!} ∘ j_!`: `sheafPullback` is a
*chosen* left adjoint, so it is functorial in its source functor only up to the canonical
isomorphism supplied by uniqueness of left adjoints.  That isomorphism is identified by
`leftAdjointIso_hom_app_comp_map_comp_counit`: it is the comparison which carries the transpose
of a morphism across `j_{V!} ⊣ j_V⁻¹` to its transpose across `(j_! ∘ j_{U!}) ⊣ j_V⁻¹`.
-/

@[expose] public section

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {U V : C} (f : V ⟶ U)

/-- Commutativity of the relocalization triangle: `j_U ∘ j = j_V`, i.e.
`Over.map f ⋙ Over.forget U = Over.forget V`. -/
@[stacks 03EH "triangle", sga "4 I 5.10" "commutative triangle", sga "3 I 1.6"]
theorem comp_forget_eq_forget :
    Over.map f ⋙ Over.forget U = Over.forget V :=
  Over.mapForget_eq f

/-- `Over.map f` is a continuous functor of sites from `(C/V, J.over V)` to
`(C/U, J.over U)`. -/
theorem map_isContinuous :
    (Over.map f).IsContinuous (J.over V) (J.over U) :=
  inferInstance

/-- `Over.map f` is a cocontinuous functor of sites from `(C/V, J.over V)`
to `(C/U, J.over U)`. -/
theorem map_isCocontinuous :
    (Over.map f).IsCocontinuous (J.over V) (J.over U) :=
  inferInstance

/-- Under the identification `(C/U)/(V/U) ≅ C/V` given by
`Over.iteratedSliceEquiv (Over.mk f)`, the relocalization functor
`j = Over.map f` agrees with the localization functor
`j_{V/U} = Over.forget (Over.mk f)`. -/
@[stacks 03EH "j = j_{V/U}", sga "3 I 1.6" "partial"]
theorem map_eq_forget_iteratedSlice :
    (Over.iteratedSliceEquiv (Over.mk f)).functor ⋙ Over.map f =
      Over.forget (Over.mk f) := by
  fapply CategoryTheory.Functor.ext
  · intro X
    refine Comma.ext rfl rfl ?_
    exact heq_of_eq (Over.w X.hom)
  · intro X Y g
    apply Over.OverMorphism.ext
    rw [Over.comp_left, Over.comp_left, Over.eqToHom_left, Over.eqToHom_left,
      conj_eqToHom_iff_heq']
    rfl

section Sheaf

variable (A : Type*) [Category A]

/-- (Inverse image, strict equality.)
`j_V^{-1} = j^{-1} ∘ j_U^{-1}` as functors `Sheaf J A ⟶ Sheaf (J.over V) A`.

This is the strict equality of `sheafPushforwardContinuous` functors, valid
because the underlying functors satisfy `Over.map f ⋙ Over.forget U =
Over.forget V` strictly. -/
@[stacks 03EH "j_V^{-1} = j^{-1} ∘ j_U^{-1}"]
theorem inverseImage_eq :
    (Over.forget V).sheafPushforwardContinuous A (J.over V) J =
      (Over.forget U).sheafPushforwardContinuous A (J.over U) J ⋙
        (Over.map f).sheafPushforwardContinuous A (J.over V) (J.over U) := by
  refine CategoryTheory.Functor.hext (fun _ => rfl) ?_
  intro X Y g
  rfl

variable [((Over.forget V).sheafPushforwardContinuous A (J.over V) J).IsRightAdjoint]
  [((Over.forget U).sheafPushforwardContinuous A (J.over U) J).IsRightAdjoint]
  [((Over.map f).sheafPushforwardContinuous A (J.over V) (J.over U)).IsRightAdjoint]

/-- (Lower-shriek, natural isomorphism.)
`j_{V!} ≅ j_{U!} ∘ j_!` as functors `Sheaf (J.over V) A ⟶ Sheaf J A`.

Constructed from `inverseImage_eq` via uniqueness of left adjoints: each of
`sheafPullback` is a chosen left adjoint to the corresponding
`sheafPushforwardContinuous`, and the composition `j_!  ∘ j_U_!` is left
adjoint to `j_U^{-1} ∘ j^{-1} = j_V^{-1}` by `inverseImage_eq`. -/
@[stacks 03EH "j_{V!} = j_{U!} ∘ j_!"]
noncomputable def leftAdjointIso :
    (Over.forget V).sheafPullback A (J.over V) J ≅
      (Over.map f).sheafPullback A (J.over V) (J.over U) ⋙
        (Over.forget U).sheafPullback A (J.over U) J :=
  -- `adjV` : j_V_! ⊣ j_V^{-1}
  letI adjV := (Over.forget V).sheafAdjunctionContinuous A (J.over V) J
  -- `adjU` : j_U_! ⊣ j_U^{-1}
  letI adjU := (Over.forget U).sheafAdjunctionContinuous A (J.over U) J
  -- `adjj` : j_!  ⊣ j^{-1}
  letI adjj := (Over.map f).sheafAdjunctionContinuous A (J.over V) (J.over U)
  -- The composition j_!  ∘ j_U_! is left adjoint to j_U^{-1} ∘ j^{-1}.
  -- Note: `adjj.comp adjU` composes the adjoints in the order
  --   (j! ∘ j_U!) ⊣ (j_U^{-1} ∘ j^{-1}).
  -- We then use `inverseImage_eq` to identify the right-hand adjoint with
  -- `j_V^{-1}`, so both `adjV` and `adjj.comp adjU` are left adjoints to
  -- `j_V^{-1}`. By uniqueness of left adjoints they are isomorphic.
  letI adj1 := adjj.comp adjU
  letI eq : (Over.forget V).sheafPushforwardContinuous A (J.over V) J =
      (Over.forget U).sheafPushforwardContinuous A (J.over U) J ⋙
        (Over.map f).sheafPushforwardContinuous A (J.over V) (J.over U) :=
    inverseImage_eq J f A
  Adjunction.leftAdjointUniq (eq ▸ adjV) adj1

/-- **Stacks 03EH carries one transpose to the other.**  A morphism `u : T ⟶ j_V^{-1}Z`
transposes across `j_{V!} ⊣ j_V^{-1}` on the one hand and across `(j_! ∘ j_{U!}) ⊣ j_V^{-1}` on
the other, and the two transposes differ by `leftAdjointIso`.

This is what `leftAdjointIso` *means*: it is a `Adjunction.leftAdjointUniq`, so on its own it is
only an isomorphism of two chosen left adjoints, and the statement that identifies it is the
agreement of the transposes it induces.  It is also the only form in which the triangle can be
used inside an equation of morphisms out of a lower shriek, where one side is written with
`j_{V!}` and the other with `j_{U!} ∘ j_!`.

`Adjunction.leftAdjointUniq_hom_app_counit` is the case `u = 𝟙`; the general case is that one
followed by the naturality of `leftAdjointIso`. -/
@[stacks 03EH "j_{V!} = j_{U!} ∘ j_! carries one transpose to the other"]
theorem leftAdjointIso_hom_app_comp_map_comp_counit {T : Sheaf (J.over V) A} {Z : Sheaf J A}
    (u : T ⟶ ((Over.forget V).sheafPushforwardContinuous A (J.over V) J).obj Z) :
    ((Over.forget V).sheafPullback A (J.over V) J).map u ≫
        ((Over.forget V).sheafAdjunctionContinuous A (J.over V) J).counit.app Z =
      (leftAdjointIso J f A).hom.app T ≫
        ((Over.map f).sheafPullback A (J.over V) (J.over U) ⋙
            (Over.forget U).sheafPullback A (J.over U) J).map u ≫
          (((Over.map f).sheafAdjunctionContinuous A (J.over V) (J.over U)).comp
            ((Over.forget U).sheafAdjunctionContinuous A (J.over U) J)).counit.app Z := by
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg
    (fun z => z ≫ (((Over.map f).sheafAdjunctionContinuous A (J.over V) (J.over U)).comp
      ((Over.forget U).sheafAdjunctionContinuous A (J.over U) J)).counit.app Z)
    ((leftAdjointIso J f A).hom.naturality u))
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  exact congrArg (fun z => ((Over.forget V).sheafPullback A (J.over V) J).map u ≫ z)
    (Adjunction.leftAdjointUniq_hom_app_counit _ _ Z).symm

end Sheaf

