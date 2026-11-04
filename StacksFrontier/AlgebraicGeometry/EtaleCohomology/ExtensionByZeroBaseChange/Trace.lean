module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZeroBaseChange.FinitePushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# The trace map of a finite étale morphism

Let `j : U ⟶ X` be an étale morphism, viewed as an object of the small étale site of `X`.
Restriction `j^{-1}` of abelian étale sheaves along `j` has a left adjoint `j_!`, extension by
zero, so there is a counit `j_!j^{-1} ⟶ id`. When `j` is in addition finite the canonical
comparison `j_! ⟶ j_*` from extension by zero to the direct image is an isomorphism, and
transporting the counit across it gives a natural map

`j_*j^{-1}ℱ ⟶ ℱ`.

This is the **trace** of the finite étale morphism `j`.

Stated for the adjoint triple `j_! ⊣ j^{-1} ⊣ j_*`, the trace is the adjunction map of the
*left* adjoint of `j^{-1}`, read through the identification of that left adjoint with the right
one. Both halves are already available: the adjunction is
`AlgebraicGeometry.abelianExtensionByZeroAdjunction`, and the comparison map is
`AlgebraicGeometry.abelianExtensionByZeroToPushforward`, an isomorphism for a finite étale `j`
by `AlgebraicGeometry.abelianExtensionByZeroToPushforward_isIso`. The construction therefore
uses no local description of `j`: it does not pass through the presentation of a finite étale
morphism as, étale-locally on the base, a finite disjoint union of copies of the base
(Stacks 04HN).

The alternative characterisation of the trace — that it commutes with étale localisation on
`X` and equals the sum map `ℱ^{⊕d} ⟶ ℱ` whenever `j` is a disjoint union of `d` copies of the
identity — is not established here. What is established is the characterisation relative to
the comparison map, `AlgebraicGeometry.abelianTrace_eq_of_comp_eq`, which pins the trace
uniquely.

## Main definitions

* `AlgebraicGeometry.abelianExtensionByZeroIsoPushforward` — for a finite étale `j`, the
  comparison `j_! ≅ j_*` on abelian étale sheaves.
* `AlgebraicGeometry.abelianTrace` — the trace `j_*j^{-1} ⟶ id` on abelian étale sheaves.
* `AlgebraicGeometry.moduleExtensionByZeroIsoPushforward` and
  `AlgebraicGeometry.moduleTrace` — the same for sheaves of `Λ`-modules.

## Main results

* `AlgebraicGeometry.abelianExtensionByZeroToPushforward_comp_abelianTrace` and
  `AlgebraicGeometry.moduleExtensionByZeroToPushforward_comp_moduleTrace` — the trace is the
  unique map whose composite with the comparison `j_! ⟶ j_*`, restricted along `j^{-1}`, is the
  counit of the extension-by-zero adjunction. Since the comparison is an isomorphism this
  triangle determines the trace, and it is the form in which the trace is used.
* `AlgebraicGeometry.abelianTrace_app_eq_of_comp_eq` — the resulting uniqueness statement,
  spelt out: a natural map `j_*j^{-1} ⟶ id` making that triangle commute agrees with the
  trace.
* `AlgebraicGeometry.abelianPushforwardAdjunction` — for a finite étale `j`, the direct image
  is itself left adjoint to restriction, the trace being the counit of this adjunction. This is
  the sense in which the trace is canonical: it is an adjunction map, not a choice.

## Implementation notes

The comparison `j_! ⟶ j_*` is only known to be invertible, through
`AlgebraicGeometry.abelianExtensionByZeroToPushforward_isIso`, so the inverse appearing in the
trace is `CategoryTheory.inv`. The inverse of a map that is an isomorphism is uniquely
determined by that map, so nothing is chosen here; the characterising triangle
`AlgebraicGeometry.abelianExtensionByZeroToPushforward_comp_abelianTrace` records that the
trace depends on no datum beyond the comparison and the counit.

The morphism is presented as an object `U` of the small étale site of `X` inside a big étale
site, with its finiteness and étaleness read off the big-site inclusion, because that is the
form in which extension by zero, the comparison map and its invertibility are stated.

## References

* [Stacks Project, Tag 03SE](https://stacks.math.columbia.edu/tag/03SE)
* [Stacks Project, Tag 03S7](https://stacks.math.columbia.edu/tag/03S7)
* [Stacks Project, Tag 03S3](https://stacks.math.columbia.edu/tag/03S3)
* [Stacks Project, Tag 0F4L](https://stacks.math.columbia.edu/tag/0F4L)
* [Stacks Project, Tag 04HN](https://stacks.math.columbia.edu/tag/04HN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace AlgebraicGeometry

variable (B : AlgebraicGeometry.BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
  (U : SmallEtale B X hX) [IsFinite (B.inclusion.map U.obj.hom)]

/-- **Stacks 03S7.** For a finite étale `U ⟶ X` the canonical comparison from extension by
zero to the direct image of abelian étale sheaves is an isomorphism; this is that
isomorphism. -/
public def abelianExtensionByZeroIsoPushforward :
    let := smallEtaleBaseChange_isContinuous B U.obj.hom
    abelianExtensionByZero B X hX U ≅
      (smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X hX)
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property) :=
  @asIso _ _ _ _ (abelianExtensionByZeroToPushforward B X hX U)
    (abelianExtensionByZeroToPushforward_isIso B X hX U)

/-- The comparison isomorphism `j_! ≅ j_*` of a finite étale morphism is the canonical
comparison map. -/
public theorem abelianExtensionByZeroIsoPushforward_hom :
    (abelianExtensionByZeroIsoPushforward B X hX U).hom =
      abelianExtensionByZeroToPushforward B X hX U :=
  rfl

/-- **Stacks 03SE.** The trace map of the finite étale morphism `U ⟶ X` on abelian étale
sheaves: the counit `j_!j^{-1} ⟶ id` of the extension-by-zero adjunction, read as a map
`j_*j^{-1} ⟶ id` through the comparison isomorphism `j_! ≅ j_*` of Stacks 03S7. -/
@[stacks 03SE "abelian sheaves"]
public def abelianTrace :
    let := smallEtaleBaseChange_isContinuous B U.obj.hom
    abelianRestriction B X hX U ⋙
        (smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous
          AddCommGrpCat.{u + 1}
          (SmallEtale.topology B X hX)
          (SmallEtale.topology B U.obj.left.1 U.obj.left.property) ⟶
      𝟭 (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :=
  Functor.whiskerLeft (abelianRestriction B X hX U)
      (abelianExtensionByZeroIsoPushforward B X hX U).inv ≫
    (abelianExtensionByZeroAdjunction B X hX U).counit

/-- **The characterising triangle of the trace.** Composing the comparison map `j_! ⟶ j_*`,
restricted along `j^{-1}`, with the trace returns the counit of the extension-by-zero
adjunction. Since the comparison is an isomorphism, this determines the trace. -/
public theorem abelianExtensionByZeroToPushforward_comp_abelianTrace :
    Functor.whiskerLeft (abelianRestriction B X hX U)
        (abelianExtensionByZeroToPushforward B X hX U) ≫ abelianTrace B X hX U =
      (abelianExtensionByZeroAdjunction B X hX U).counit := by
  exact (Functor.isoWhiskerLeft (abelianRestriction B X hX U)
    (abelianExtensionByZeroIsoPushforward B X hX U)).hom_inv_id_assoc _

/-- The same triangle on sections: at a sheaf `ℱ` the comparison map, evaluated at `j^{-1}ℱ`,
followed by the trace, is the counit at `ℱ`. -/
public theorem abelianExtensionByZeroToPushforward_app_comp_abelianTrace_app
    (F : Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}) :
    (abelianExtensionByZeroToPushforward B X hX U).app
          ((abelianRestriction B X hX U).obj F) ≫
        (abelianTrace B X hX U).app F =
      (abelianExtensionByZeroAdjunction B X hX U).counit.app F :=
  congrArg (fun t => NatTrans.app t F)
    (abelianExtensionByZeroToPushforward_comp_abelianTrace B X hX U)

/-- **The trace is the unique map satisfying its characterising triangle.** A natural map
`t : j_*j^{-1} ⟶ id` whose composite with the comparison map is the counit of the
extension-by-zero adjunction is the trace. -/
public theorem abelianTrace_eq_of_comp_eq
    (t : let := smallEtaleBaseChange_isContinuous B U.obj.hom
      abelianRestriction B X hX U ⋙
          (smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous
            AddCommGrpCat.{u + 1}
            (SmallEtale.topology B X hX)
            (SmallEtale.topology B U.obj.left.1 U.obj.left.property) ⟶
        𝟭 (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u + 1}))
    (ht : Functor.whiskerLeft (abelianRestriction B X hX U)
        (abelianExtensionByZeroToPushforward B X hX U) ≫ t =
      (abelianExtensionByZeroAdjunction B X hX U).counit) :
    t = abelianTrace B X hX U := by
  have hiso : IsIso (Functor.whiskerLeft (abelianRestriction B X hX U)
      (abelianExtensionByZeroToPushforward B X hX U)) := by
    have := abelianExtensionByZeroToPushforward_isIso B X hX U
    exact inferInstanceAs (IsIso (Functor.whiskerLeft (abelianRestriction B X hX U)
      (asIso (abelianExtensionByZeroToPushforward B X hX U)).hom))
  exact (cancel_epi (Functor.whiskerLeft (abelianRestriction B X hX U)
    (abelianExtensionByZeroToPushforward B X hX U))).mp
    (ht.trans (abelianExtensionByZeroToPushforward_comp_abelianTrace B X hX U).symm)

/-- **For a finite étale morphism the direct image is a left adjoint of restriction**, being
isomorphic to extension by zero. The trace is the counit of this adjunction, which is the
precise sense in which it is canonical. -/
@[sga "4 XVII 6.2.11" "special case"]
public def abelianPushforwardAdjunction :
    let := smallEtaleBaseChange_isContinuous B U.obj.hom
    (smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous
        AddCommGrpCat.{u + 1}
        (SmallEtale.topology B X hX)
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property) ⊣
      abelianRestriction B X hX U :=
  (abelianExtensionByZeroAdjunction B X hX U).ofNatIsoLeft
    (abelianExtensionByZeroIsoPushforward B X hX U)

/-- The counit of the adjunction between the direct image along a finite étale morphism and
restriction is the trace. -/
public theorem abelianPushforwardAdjunction_counit :
    (abelianPushforwardAdjunction B X hX U).counit = abelianTrace B X hX U :=
  rfl

variable (Λ : Type v) [Ring Λ]

/-- **Stacks 03S7.** For a finite étale `U ⟶ X` the canonical comparison from extension by
zero to the direct image of sheaves of `Λ`-modules is an isomorphism; this is that
isomorphism. -/
public def moduleExtensionByZeroIsoPushforward :
    let := smallEtaleBaseChange_isContinuous B U.obj.hom
    moduleExtensionByZero B X hX U Λ ≅
      (smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous
        (ModuleCat.{max (u + 1) v} Λ)
        (SmallEtale.topology B X hX)
        (SmallEtale.topology B U.obj.left.1 U.obj.left.property) :=
  @asIso _ _ _ _ (moduleExtensionByZeroToPushforward B X hX U Λ)
    (moduleExtensionByZeroToPushforward_isIso B X hX U Λ)

/-- The comparison isomorphism `j_! ≅ j_*` of a finite étale morphism, on sheaves of
`Λ`-modules, is the canonical comparison map. -/
public theorem moduleExtensionByZeroIsoPushforward_hom :
    (moduleExtensionByZeroIsoPushforward B X hX U Λ).hom =
      moduleExtensionByZeroToPushforward B X hX U Λ :=
  rfl

/-- **Stacks 03SE.** The trace map of the finite étale morphism `U ⟶ X` on étale sheaves of
`Λ`-modules, constructed exactly as in the abelian case. -/
@[stacks 03SE "sheaves of modules"]
public def moduleTrace :
    let := smallEtaleBaseChange_isContinuous B U.obj.hom
    moduleRestriction B X hX U Λ ⋙
        (smallEtaleBaseChange B U.obj.hom).sheafPushforwardContinuous
          (ModuleCat.{max (u + 1) v} Λ)
          (SmallEtale.topology B X hX)
          (SmallEtale.topology B U.obj.left.1 U.obj.left.property) ⟶
      𝟭 (Sheaf (SmallEtale.topology B X hX) (ModuleCat.{max (u + 1) v} Λ)) :=
  Functor.whiskerLeft (moduleRestriction B X hX U Λ)
      (moduleExtensionByZeroIsoPushforward B X hX U Λ).inv ≫
    (moduleExtensionByZeroAdjunction B X hX U Λ).counit

/-- **The characterising triangle of the trace on sheaves of modules.** -/
public theorem moduleExtensionByZeroToPushforward_comp_moduleTrace :
    Functor.whiskerLeft (moduleRestriction B X hX U Λ)
        (moduleExtensionByZeroToPushforward B X hX U Λ) ≫ moduleTrace B X hX U Λ =
      (moduleExtensionByZeroAdjunction B X hX U Λ).counit := by
  exact (Functor.isoWhiskerLeft (moduleRestriction B X hX U Λ)
    (moduleExtensionByZeroIsoPushforward B X hX U Λ)).hom_inv_id_assoc _

end AlgebraicGeometry

end
