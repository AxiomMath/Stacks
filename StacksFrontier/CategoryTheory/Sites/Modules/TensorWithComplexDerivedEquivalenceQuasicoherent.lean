module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedUnit
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.QuasicoherentImage
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.RegularExt

/-!
# The derived tensor product with a K-injective relatively compact generator, over a base ring

Let `(C, O)` be a ringed site over a base ring `R` (Tag 0CS6) and let `𝒬` be a strictly full
triangulated subcategory of `D(O)` closed under direct sums. Let `K` be a K-injective complex of
`O`-modules lying in `𝒬`, compact relative to `𝒬` and generating `𝒬`. With
`(E, d) = Hom_{Comp^dg(O)}(K, K)` the endomorphism differential graded `R`-algebra, the functor
`- ⊗_E^𝐋 K` of Tag 09LX is an equivalence of `D(E, d)` with `𝒬`. For `R = ℤ` this is
`AlgebraicGeometry.RingedSite.tensorWithComplexDerivedEquivalence`.

## Main results

* `AlgebraicGeometry.RingedSite.prop_tensorWithComplexDerived_objOver`: the image of `- ⊗_E^𝐋 K`
  lies in `𝒬`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_bijective_map_regularOver`: `- ⊗_E^𝐋 K` is
  bijective on `Hom(E, E[n])`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedFullyFaithfulOver`: `- ⊗_E^𝐋 K` is fully
  faithful.
* `AlgebraicGeometry.RingedSite.isIso_tensorWithComplexDerived_adj_counit_appOver`: the counit of
  `- ⊗_E^𝐋 K ⊣ RHom(K, -)` is invertible on `𝒬`.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedEquivalenceOver`: the equivalence
  `D(E, d) ≌ 𝒬`.

## References

* [Stacks Project, Tag 09MC](https://stacks.math.columbia.edu/tag/09MC)
* [Stacks Project, Tag 09LZ](https://stacks.math.columbia.edu/tag/09LZ)
* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

universe u v w t s

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type (max u v w t s)) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, max u v w t s} X R]
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
  (𝒬 : ObjectProperty (DerivedCategory (TensorModO.{u, v, w, t, s} X)))

/-- The adjunction `- ⊗_E^𝐋 K ⊣ RHom(K, -)` over `R` is compatible with the shifts by `ℤ`. -/
instance tensorWithComplexDerived_adj_derivedHomWithComplexOver_commShift :
    (tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s}
      X R K).CommShift ℤ :=
  (tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s}
    X R K).commShift_of_leftAdjoint ℤ

/-- `E ⊗_E^𝐋 K` is `K`. -/
def tensorWithComplexDerivedRegularIsoOver :
    (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).obj
        (repRegularDerivedOver.{u, v, w, t, s, max u v w t s} X R K) ≅
      DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K) :=
  (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).mapIso
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q.mapIso
        ((toHomotopyCategory (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).mapIso
          DGCategory.representableSelfIsoRegular)).symm ≪≫
    tensorWithComplexDerivedObjRegularIsoOver.{u, v, w, t, s, max u v w t s} X R K

/-- Every value of `- ⊗_E^𝐋 K` lies in any triangulated subcategory of `D(O)`, closed under
isomorphisms and direct sums, which contains `K`. -/
theorem prop_tensorWithComplexDerived_objOver [𝒬.IsClosedUnderIsomorphisms] [𝒬.IsTriangulated]
    (hcoprod : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, 𝒬 (Z i)) → 𝒬 c.pt)
    (hK : 𝒬 (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (M : DifferentialGradedModule.derivedCategory.{max u v w t s, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) :
    𝒬 ((tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).obj M) := by
  refine General.property_of_coproducts_of_two_out_of_three_of_shifts
    (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra
    (fun N => 𝒬 ((tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).obj N))
    ?_ ?_ ?_ M
  · intro ι Z hZ
    have hc := isColimitOfPreserves (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K)
      (coproductIsCoproduct Z)
    exact hcoprod _ _ ((isColimitMapCoconeCofanMkEquiv _ Z (Sigma.ι Z)) hc) hZ
  · intro Δ hΔ
    have := tensorWithComplexDerived_signTwist_isTriangulatedOver.{u, v, w, t, s, max u v w t s}
      X R K
    have hmap := (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⋙
      CategoryTheory.signTwist
        (DerivedCategory (TensorModO.{u, v, w, t, s} X))).map_distinguished Δ hΔ
    exact ⟨fun h₁ h₂ => 𝒬.ext_of_isTriangulatedClosed₃ _ hmap h₁ h₂,
      fun h₁ h₃ => 𝒬.ext_of_isTriangulatedClosed₂ _ hmap h₁ h₃,
      fun h₂ h₃ => 𝒬.ext_of_isTriangulatedClosed₁ _ hmap h₂ h₃⟩
  · intro k
    exact 𝒬.prop_of_iso
      (((tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).commShiftIso k).app _).symm
      (𝒬.le_shift k _
        (𝒬.prop_of_iso (tensorWithComplexDerivedRegularIsoOver.{u, v, w, t, s} X R K).symm hK))

/-- The `n`-th shift of `E` is the class of the `n`-th shift of the regular module. -/
def repRegularDerivedOverShiftIso (n : ℤ) :
    (repRegularDerivedOver.{u, v, w, t, s, max u v w t s} X R K)⟦n⟧ ≅
      (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q.obj
        ((toHomotopyCategory _).obj
          (shift (regularModule (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra) n)) :=
  (((quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q.commShiftIso n).app
      _).symm ≪≫
    (quasiIsomorphisms (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra).Q.mapIso
      (quotientShiftIso _ n).symm

/-- For `K` K-injective, `- ⊗_E^𝐋 K` is bijective on `Hom(E, E[n])`. -/
theorem tensorWithComplexDerived_bijective_map_regularOver
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective] (n : ℤ) :
    Function.Bijective
      (fun f : repRegularDerivedOver.{u, v, w, t, s, max u v w t s} X R K ⟶
          (repRegularDerivedOver.{u, v, w, t, s, max u v w t s} X R K)⟦n⟧ =>
        (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).map f) := by
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s,
    max u v w t s} X R K
  have hη : IsIso (adj.unit.app
      ((repRegularDerivedOver.{u, v, w, t, s, max u v w t s} X R K)⟦n⟧)) :=
    (NatTrans.isIso_app_iff_of_iso adj.unit
      (repRegularDerivedOverShiftIso.{u, v, w, t, s} X R K n)).2
      (isIso_tensorWithComplexDerived_adj_unit_app_shift.{u, v, w, t, s} X R K n)
  have key : (fun f : repRegularDerivedOver.{u, v, w, t, s, max u v w t s} X R K ⟶
        (repRegularDerivedOver.{u, v, w, t, s, max u v w t s} X R K)⟦n⟧ =>
          (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).map f) =
      (adj.homEquiv _ _).symm ∘
        (fun f => f ≫ adj.unit.app
          ((repRegularDerivedOver.{u, v, w, t, s, max u v w t s} X R K)⟦n⟧)) := by
    funext f
    apply (adj.homEquiv _ _).injective
    rw [Function.comp_apply, Equiv.apply_symm_apply, Adjunction.homEquiv_unit]
    exact (adj.unit.naturality f).symm
  rw [key]
  refine (adj.homEquiv _ _).symm.bijective.comp ⟨fun a b h => (cancel_mono _).1 h, fun g =>
    ⟨g ≫ inv (adj.unit.app
      ((repRegularDerivedOver.{u, v, w, t, s, max u v w t s} X R K)⟦n⟧)), by simp⟩⟩

/-- `- ⊗_E^𝐋 K` is fully faithful, for `K` K-injective, lying in a triangulated subcategory `𝒬` of
`D(O)` closed under isomorphisms and direct sums, and with its shifts compact relative to `𝒬`. -/
def tensorWithComplexDerivedFullyFaithfulOver [(liftComplex.{u, v, w, t, s} X K).IsKInjective]
    [𝒬.IsClosedUnderIsomorphisms] [𝒬.IsTriangulated]
    (hcoprod : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, 𝒬 (Z i)) → 𝒬 c.pt)
    (hK : 𝒬 (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsRelativelyCompactShifts.{u, v, w, t, s} X K 𝒬) :
    (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).FullyFaithful :=
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s,
    max u v w t s} X R K
  letI : (derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R K).Additive :=
    adj.right_adjoint_additive
  letI := tensorWithComplexDerived_signTwist_isTriangulatedOver.{u, v, w, t, s, max u v w t s}
    X R K
  letI : (CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) ⋙
      derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R K).IsTriangulated :=
    adj.compSignTwist.isTriangulated_rightAdjoint
  letI : IsGrothendieckAbelian.{max u v w t s} (TensorModO.{u, v, w, t, s} X) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, w, max t s} X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  letI : HasCoproducts.{max u v w t s} (DerivedCategory (TensorModO.{u, v, w, t, s} X)) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory
      (TensorModO.{u, v, w, t, s} X)
  have hgen :=
    Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule.{
      max u v w t s, max u v w t s} (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra
  show (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⋙
      CategoryTheory.signTwist
        (DerivedCategory (TensorModO.{u, v, w, t, s} X))).FullyFaithful from
    CategoryTheory.Adjunction.fullyFaithfulL_of_devissage_of_preservesColimit adj.compSignTwist
      (fun {ι} Z => by
        classical
        exact CategoryTheory.Pretriangulated.preservesColimit_discrete_of_bijective_cofanMap
          adj.compSignTwist (repRegularDerivedOver.{u, v, w, t, s, max u v w t s} X R K)
          hgen (General.isCompactObject_q_regularModule_arbitraryUniverse.{max u v w t s,
            max u v w t s, max u v w t s} (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra)
          (fun i => (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).obj (Z i))
          (fun A hA => by
            obtain ⟨A₀, n, e, hA₀⟩ := hA
            rw [ObjectProperty.singleton_iff] at hA₀
            subst hA₀
            refine hcompact _ ⟨_, n,
                (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).mapIso e ≪≫
                ((tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).commShiftIso
                  n).app _ ≪≫
                (CategoryTheory.shiftFunctor _ n).mapIso
                  (tensorWithComplexDerivedRegularIsoOver.{u, v, w, t, s} X R K),
                (ObjectProperty.singleton_iff _ _).2 rfl⟩ _
              (fun i => prop_tensorWithComplexDerived_objOver.{u, v, w, t, s} X R K 𝒬 hcoprod hK
                (Z i))
              _ (coproductIsCoproduct _)))
      hgen (tensorWithComplexDerived_bijective_map_regularOver.{u, v, w, t, s} X R K)
      (fun T => General.property_of_coproducts_of_two_out_of_three_of_shifts
        (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra T)

/-- The counit of `- ⊗_E^𝐋 K ⊣ RHom(K, -)` is invertible on `𝒬`, for `K` K-injective, lying in
`𝒬`, with its shifts compact relative to `𝒬`, and generating `𝒬`. -/
theorem isIso_tensorWithComplexDerived_adj_counit_appOver
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective]
    [𝒬.IsClosedUnderIsomorphisms] [𝒬.IsTriangulated]
    (hcoprod : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, 𝒬 (Z i)) → 𝒬 c.pt)
    (hK : 𝒬 (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsRelativelyCompactShifts.{u, v, w, t, s} X K 𝒬)
    (hgen : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), 𝒬 L →
      (∀ (n : ℤ) (f : (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ ⟶ L), f = 0) →
        IsZero L)
    (L : DerivedCategory (TensorModO.{u, v, w, t, s} X)) (hL : 𝒬 L) :
    IsIso ((tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s,
      max u v w t s} X R K).counit.app L) := by
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s,
    max u v w t s} X R K
  let : (derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R K).Additive :=
    adj.right_adjoint_additive
  let := tensorWithComplexDerived_signTwist_isTriangulatedOver.{u, v, w, t, s, max u v w t s}
    X R K
  let : (CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) ⋙
      derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R K).IsTriangulated :=
    adj.compSignTwist.isTriangulated_rightAdjoint
  let hff := tensorWithComplexDerivedFullyFaithfulOver.{u, v, w, t, s} X R K 𝒬 hcoprod hK
    hcompact
  have hF := prop_tensorWithComplexDerived_objOver.{u, v, w, t, s} X R K 𝒬 hcoprod hK
  have : (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⋙
      CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X))).Full :=
    hff.full
  have : (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⋙
      CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X))).Faithful :=
    hff.faithful
  have hker : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), 𝒬 L →
      IsZero ((CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) ⋙
        derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R K).obj L) → IsZero L := by
    intro L hL hz
    refine hgen L hL fun n f => ?_
    let e : (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).obj
        ((repRegularDerivedOver.{u, v, w, t, s, max u v w t s} X R K)⟦n⟧) ≅
          (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ :=
      ((tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).commShiftIso n).app _ ≪≫
        (CategoryTheory.shiftFunctor _ n).mapIso
          (tensorWithComplexDerivedRegularIsoOver.{u, v, w, t, s} X R K)
    have h0 : e.hom ≫ f = 0 :=
      (adj.homEquiv _ L).injective (hz.eq_of_tgt _ _)
    simpa using congrArg (e.inv ≫ ·) h0
  exact _root_.isIso_counit_app_of_fullyFaithful_of_ker_eq_zero
    (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K ⋙
      CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)))
    (CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) ⋙
      derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R K) adj.compSignTwist 𝒬 hF
    hker L hL

/-- The derived category of `E` is `𝒬`. Let `K` be a K-injective complex of `O`-modules, let `𝒬` be
a triangulated subcategory of `D(O)` closed under isomorphisms and direct sums, containing `K`, in
which the shifts of `K` are compact and which `K` generates. Then `- ⊗_E^𝐋 K` induces an
equivalence of `D(E, d)` with `𝒬`, for `E = Hom^•(K, K)` the endomorphism differential graded
`R`-algebra; its functor is the corestriction of `- ⊗_E^𝐋 K` to `𝒬`. -/
def tensorWithComplexDerivedEquivalenceOver [(liftComplex.{u, v, w, t, s} X K).IsKInjective]
    [𝒬.IsClosedUnderIsomorphisms] [𝒬.IsTriangulated]
    (hcoprod : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, 𝒬 (Z i)) → 𝒬 c.pt)
    (hK : 𝒬 (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsRelativelyCompactShifts.{u, v, w, t, s} X K 𝒬)
    (hgen : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), 𝒬 L →
      (∀ (n : ℤ) (f : (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ ⟶ L), f = 0) →
        IsZero L) :
    DifferentialGradedModule.derivedCategory.{max u v w t s, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, max u v w t s} X R K).algebra ≌ 𝒬.FullSubcategory := by
  let hff := tensorWithComplexDerivedFullyFaithfulOver.{u, v, w, t, s} X R K 𝒬 hcoprod hK
    hcompact
  haveI : (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).Full := hff.full
  haveI : (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K).Faithful := hff.faithful
  let F' := 𝒬.lift (tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K)
    (prop_tensorWithComplexDerived_objOver.{u, v, w, t, s} X R K 𝒬 hcoprod hK)
  haveI : F'.EssSurj := ⟨fun L => by
    have := isIso_tensorWithComplexDerived_adj_counit_appOver.{u, v, w, t, s} X R K 𝒬 hcoprod hK
      hcompact hgen L.obj L.property
    exact ⟨(derivedHomWithComplexOver.{u, v, w, t, s, max u v w t s} X R K).obj L.obj,
      ⟨ObjectProperty.isoMk _ (@asIso _ _ _ _
        ((tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s,
          max u v w t s} X R K).counit.app L.obj) this)⟩⟩⟩
  haveI : F'.IsEquivalence := { }
  exact F'.asEquivalence

/-- The functor of `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedEquivalenceOver` followed
by the inclusion of `𝒬` is `- ⊗_E^𝐋 K` itself. -/
theorem tensorWithComplexDerivedEquivalenceOver_functor_comp_ι
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective]
    [𝒬.IsClosedUnderIsomorphisms] [𝒬.IsTriangulated]
    (hcoprod : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, 𝒬 (Z i)) → 𝒬 c.pt)
    (hK : 𝒬 (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsRelativelyCompactShifts.{u, v, w, t, s} X K 𝒬)
    (hgen : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), 𝒬 L →
      (∀ (n : ℤ) (f : (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ ⟶ L), f = 0) →
        IsZero L) :
    (tensorWithComplexDerivedEquivalenceOver.{u, v, w, t, s} X R K 𝒬 hcoprod hK hcompact
      hgen).functor ⋙ 𝒬.ι = tensorWithComplexDerived.{u, v, w, t, s, max u v w t s} X R K :=
  rfl

end AlgebraicGeometry.RingedSite
