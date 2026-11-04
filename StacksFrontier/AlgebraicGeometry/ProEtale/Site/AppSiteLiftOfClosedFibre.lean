module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.JacobsonQuotientRetraction
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AppSiteClosedImmersion
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AppSiteClosedImmersionTopos
public import StacksCore.Tactic.StacksAttribute

/-!
# An object of the pro-étale site as the lift of its closed fibre

Let `i : Z ⟶ X` be a closed immersion of affine schemes, `u : X_app ⥤ Z_app` the base-change
functor `U ↦ U ×_X Z` and `v : Z_app ⥤ X_app` its fully faithful left adjoint of Stacks 09BK.
The counit `v(U ×_X Z) ⟶ U` is an isomorphism as soon as the corresponding comparison on
ind-étale algebras over `Γ(X, ⊤)` is one, namely the unit of the lifting adjunction for the
ideal cutting out `Z`.

## Main results

* `AlgebraicGeometry.ProEtale.appProetaleLiftBaseChangeObjIso`: the identification
  `v(U ×_X Z) ≅ U` from the comparison at the global sections of `U`.
* `AlgebraicGeometry.ProEtale.isIso_counit_app_appProetaleLiftAdjunction`: invertibility of the
  counit of `v ⊣ u` at such a `U`.
* `AlgebraicGeometry.ProEtale.appProetaleBaseChangeLiftIso`: from the comparison as a natural
  isomorphism, `u ⋙ v ≅ 𝟭`.
* `AlgebraicGeometry.ProEtale.appProetaleLiftBaseChangeObjIsoOfIsWContractible` and
  `AlgebraicGeometry.ProEtale.isIso_counit_app_of_isWContractible`: the identification and the
  invertibility of the counit under the hypotheses of Stacks 09AC, with no comparison assumed.

## Implementation notes

The transport between the site and the ind-étale algebras runs through the equivalences
`appSpec X` and `appSpec Z` and the presentation of `v` as the lift of ind-étale algebras along
the surjection `Γ(X, ⊤) → Γ(Z, ⊤)`; no naturality in `U` is needed, so the comparison is taken
as a hypothesis at the single object in play.

Together with Stacks 09BL part (1) this is the step to which Stacks 09AC is reduced. The
hypothesis is discharged, for `U` affine and weakly contractible all of whose points specialize
into the closed fibre, by
`AlgebraicGeometry.ProEtale.indEtaleQuotientLift_self_iso` and
`AlgebraicGeometry.ProEtale.existsUnique_algHom_comp_quotientMk_eq`.

## References

* [Stacks Project, Tag 09AC](https://stacks.math.columbia.edu/tag/09AC)
* [Stacks Project, Tag 09BK](https://stacks.math.columbia.edu/tag/09BK)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.ProEtale

variable {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsAffine X] [IsAffine Z]

/-- The ideal of the global sections of `X` cutting out the closed subscheme `Z`: the kernel of
the surjection `Γ(X, ⊤) → Γ(Z, ⊤)`. -/
public noncomputable abbrev appTopKer : Ideal Γ(X, ⊤) :=
  RingHom.ker i.appTop.hom

/-- The quotient of the global sections of `X` by the ideal of `Z` is the ring of global
sections of `Z`. -/
public noncomputable abbrev appTopKerEquiv : (Γ(X, ⊤) ⧸ appTopKer i) ≃+* Γ(Z, ⊤) :=
  i.appTop.hom.quotientKerEquivOfSurjective (surjective_appTop_hom i)

/-- The lift of the extension of scalars of the global sections of `U` along `Γ(X, ⊤) → Γ(Z, ⊤)`
is the algebra of global sections of `U`, given the comparison for the quotient presentation. -/
public noncomputable def liftBaseChangeAppAlgIso (U : AppSmallProetale X)
    (hring : (indEtaleQuotientLift Γ(X, ⊤) (appTopKer i)).obj
      ((indEtaleQuotientBaseChange Γ(X, ⊤) (appTopKer i)).obj (appAlg U)) ≅ appAlg U) :
    (indEtaleAlgebraBaseChange_rightAdjoint i.appTop.hom
        (surjective_appTop_hom i)).obj (bcAlg i U) ≅ appAlg U :=
  ((indEtaleAlgebraTransport (appTopKerEquiv i)).inverse ⋙
        indEtaleQuotientLift Γ(X, ⊤) (appTopKer i)).mapIso
      ((indEtaleAlgebraBaseChange_surjectiveIso i.appTop.hom (surjective_appTop_hom i)).app
        (appAlg U)) ≪≫
    (indEtaleQuotientLift Γ(X, ⊤) (appTopKer i)).mapIso
      ((indEtaleAlgebraTransport (appTopKerEquiv i)).unitIso.app
        ((indEtaleQuotientBaseChange Γ(X, ⊤) (appTopKer i)).obj (appAlg U))).symm ≪≫
    hring

/-- **The identification of `U` with `v(u(U))`.** For a closed immersion `i` of
affine schemes and `U` in `X_app`, the lift of the fibre product `U ×_X Z` is `U` itself, as
soon as the lift of the quotient base change of the global sections of `U` is those global
sections. -/
public noncomputable def appProetaleLiftBaseChangeObjIso (U : AppSmallProetale X)
    (hring : (indEtaleQuotientLift Γ(X, ⊤) (appTopKer i)).obj
      ((indEtaleQuotientBaseChange Γ(X, ⊤) (appTopKer i)).obj (appAlg U)) ≅ appAlg U) :
    (appProetaleLift i).obj ((appProetaleBaseChange i).obj U) ≅ U :=
  (appProetaleLift i).mapIso (appBaseChangeIso i U).symm ≪≫
    ((indEtaleAlgebraBaseChange_rightAdjoint i.appTop.hom (surjective_appTop_hom i)).op ⋙
        appSpec X).mapIso
      ((appSpecEquivalence Z).unitIso.app (op (bcAlg i U))).symm ≪≫
    (appSpec X).mapIso (Iso.op (liftBaseChangeAppAlgIso i U hring).symm) ≪≫
    appSpecAppAlgIso U

/-- **Invertibility of the counit at an object.** The counit `v(u(U)) → U` of the
adjunction `v ⊣ u` along a closed immersion of affine schemes is an isomorphism as soon as the
ring-level comparison holds at the global sections of `U`. -/
public theorem isIso_counit_app_appProetaleLiftAdjunction (U : AppSmallProetale X)
    (hring : (indEtaleQuotientLift Γ(X, ⊤) (appTopKer i)).obj
      ((indEtaleQuotientBaseChange Γ(X, ⊤) (appTopKer i)).obj (appAlg U)) ≅ appAlg U) :
    IsIso ((appProetaleLiftAdjunction i).counit.app U) :=
  (appProetaleLiftAdjunction i).isIso_counit_app_of_iso
    (appProetaleLiftBaseChangeObjIso i U hring).symm

/-- **Invertibility of the counit.** If the unit of the ring-level adjunction for
the ideal cutting out `Z` is a natural isomorphism, the counit `v ∘ u → 𝟭` is an isomorphism. -/
public theorem isIso_counit_appProetaleLiftAdjunction
    (hring : Nonempty (indEtaleQuotientBaseChange Γ(X, ⊤) (appTopKer i) ⋙
      indEtaleQuotientLift Γ(X, ⊤) (appTopKer i) ≅ 𝟭 (IndEtaleAlgebra Γ(X, ⊤)))) :
    IsIso (appProetaleLiftAdjunction i).counit := by
  obtain ⟨ε⟩ := hring
  have : ∀ U : AppSmallProetale X, IsIso ((appProetaleLiftAdjunction i).counit.app U) :=
    fun U ↦ isIso_counit_app_appProetaleLiftAdjunction i U (ε.app (appAlg U))
  exact NatIso.isIso_of_isIso_app _

/-- **The identification of `𝟭` with `u ⋙ v`.** If the unit of the ring-level
adjunction for the ideal cutting out `Z` is a natural isomorphism, then base change followed by
its left adjoint is the identity on `X_app`. -/
public theorem appProetaleBaseChangeLiftIso
    (hring : Nonempty (indEtaleQuotientBaseChange Γ(X, ⊤) (appTopKer i) ⋙
      indEtaleQuotientLift Γ(X, ⊤) (appTopKer i) ≅ 𝟭 (IndEtaleAlgebra Γ(X, ⊤)))) :
    Nonempty (appProetaleBaseChange i ⋙ appProetaleLift i ≅ 𝟭 (AppSmallProetale X)) := by
  have := isIso_counit_appProetaleLiftAdjunction i hring
  exact ⟨asIso (appProetaleLiftAdjunction i).counit⟩

/-- **Invertibility of the counit at an object, from the ring-level unit.** The
counit `v(u(U)) → U` is an isomorphism as soon as the unit of the ring-level adjunction for the
ideal cutting out `Z` is an isomorphism at the global sections of `U`. -/
public theorem isIso_counit_app_of_isIso_unit_app (U : AppSmallProetale X)
    (adj : indEtaleQuotientBaseChange Γ(X, ⊤) (appTopKer i) ⊣
      indEtaleQuotientLift Γ(X, ⊤) (appTopKer i)) (h : IsIso (adj.unit.app (appAlg U))) :
    IsIso ((appProetaleLiftAdjunction i).counit.app U) :=
  isIso_counit_app_appProetaleLiftAdjunction i U (asIso (adj.unit.app (appAlg U))).symm

/-- **The identification of `𝟭` with `u ⋙ v`, from the ring-level unit.** If the unit
of the ring-level adjunction for the ideal cutting out `Z` is an isomorphism, then base change
followed by its left adjoint is the identity on `X_app`. -/
public theorem appProetaleBaseChangeLiftIso_of_isIso_unit
    (adj : indEtaleQuotientBaseChange Γ(X, ⊤) (appTopKer i) ⊣
      indEtaleQuotientLift Γ(X, ⊤) (appTopKer i)) (h : IsIso adj.unit) :
    Nonempty (appProetaleBaseChange i ⋙ appProetaleLift i ≅ 𝟭 (AppSmallProetale X)) :=
  appProetaleBaseChangeLiftIso i ⟨(asIso adj.unit).symm⟩

/-! ### The unconditional identification for a weakly contractible object -/

/-- **Stacks 09AC.** Let `i : Z ⟶ X` be a closed immersion of affine schemes and let `U` be an
object of `X_app` which is affine and weakly contractible and every point of which specializes
to a point of `U ×_X Z`. Then `U` is the lift of its closed fibre: `v(U ×_X Z) ≅ U`. -/
@[stacks 09AC "the identification v(U x_X Z) = U, to which Stacks 09BL (1) reduces the lemma; \
hypothesis (1) is w-contractibility of Gamma(U, O_U) and hypothesis (2) is containment of the \
ideal of the closed fibre in its Jacobson radical"]
public noncomputable def appProetaleLiftBaseChangeObjIsoOfIsWContractible (U : AppSmallProetale X)
    (hU : ProetaleWContractible.IsWContractible.{u, u} (appAlg U).obj.right)
    (hjac : (appTopKer i).map (appAlg U).obj.hom.hom ≤ Ring.jacobson (appAlg U).obj.right) :
    (appProetaleLift i).obj ((appProetaleBaseChange i).obj U) ≅ U :=
  appProetaleLiftBaseChangeObjIso i U
    (indEtaleQuotientLiftBaseChangeIso Γ(X, ⊤) (appTopKer i) (appAlg U) hU hjac)

/-- **Invertibility of the counit at a weakly contractible object.** For `U` affine and weakly
contractible all of whose points specialize into the closed fibre, the counit `v(U ×_X Z) ⟶ U`
of the adjunction `v ⊣ u` is an isomorphism. -/
public theorem isIso_counit_app_of_isWContractible (U : AppSmallProetale X)
    (hU : ProetaleWContractible.IsWContractible.{u, u} (appAlg U).obj.right)
    (hjac : (appTopKer i).map (appAlg U).obj.hom.hom ≤ Ring.jacobson (appAlg U).obj.right) :
    IsIso ((appProetaleLiftAdjunction i).counit.app U) :=
  isIso_counit_app_appProetaleLiftAdjunction i U
    (indEtaleQuotientLiftBaseChangeIso Γ(X, ⊤) (appTopKer i) (appAlg U) hU hjac)

end AlgebraicGeometry.ProEtale

end
