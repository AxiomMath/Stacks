module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedExtKInjective
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexDerivedFullyFaithfulDerivedHom
public import StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctors
public import StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctorsRelative
public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproducts

public import StacksFrontier.CategoryTheory.Triangulated.RightAdjointCoproductsDiscrete
/-!
# The derived category of a ringed site restricted to a compactly generated subcategory as a
module category

Let `(C, O)` be a ringed site and let `𝒬` be a strictly full triangulated subcategory of `D(O)`
closed under direct sums. Let `K` be a K-injective complex of `O`-modules lying in `𝒬`, compact
relative to `𝒬` (morphisms out of `K` commute with direct sums of objects of `𝒬`) and generating
`𝒬`. With `(E, d) = Hom_{Comp^dg(O)}(K, K)`, the functor `- ⊗_E^𝐋 K` of Tag 09LX is an equivalence
of `D(E, d)` with `𝒬`.

## Main results

* `AlgebraicGeometry.RingedSite.prop_tensorWithComplexDerived_obj`: the image of `- ⊗_E^𝐋 K` lies
  in every triangulated subcategory closed under direct sums which contains `K` (the argument of
  Stacks 09MA).
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedEquivalenceOfExt`: the equivalence
  `D(E, d) ≌ 𝒬` when `E` computes the ext groups of `K` (hypothesis (2) of Tag 09LZ).
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedEquivalence`: the same for `K`
  K-injective, where that hypothesis is 09MD.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated DifferentialGradedModule

universe u v w t s

namespace AlgebraicGeometry.RingedSite

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)
  (𝒬 : ObjectProperty (DerivedCategory (TensorModO.{u, v, w, t, s} X)))

/-- **Stacks 09MA, in the generality of a triangulated subcategory.** Every value of `- ⊗_E^𝐋 K`
lies in any triangulated subcategory of `D(O)`, closed under isomorphisms and direct sums, which
contains `K`. -/
theorem prop_tensorWithComplexDerived_obj [𝒬.IsClosedUnderIsomorphisms] [𝒬.IsTriangulated]
    (hcoprod : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, 𝒬 (Z i)) → 𝒬 c.pt)
    (hK : 𝒬 (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (M : DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) :
    𝒬 ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj M) := by
  refine General.property_of_coproducts_of_two_out_of_three_of_shifts
    (Rep.{u, v, w, t, s, 0} X ℤ K).algebra
    (fun N => 𝒬 ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj N)) ?_ ?_ ?_ M
  · intro ι Z hZ
    have hc := isColimitOfPreserves (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K)
      (coproductIsCoproduct Z)
    exact hcoprod _ _ ((isColimitMapCoconeCofanMkEquiv _ Z (Sigma.ι Z)) hc) hZ
  · intro Δ hΔ
    have := tensorWithComplexDerived_signTwist_isTriangulated.{u, v, w, t, s} X K
    have hmap := (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⋙
      CategoryTheory.signTwist
        (DerivedCategory (TensorModO.{u, v, w, t, s} X))).map_distinguished Δ hΔ
    exact ⟨fun h₁ h₂ => 𝒬.ext_of_isTriangulatedClosed₃ _ hmap h₁ h₂,
      fun h₁ h₃ => 𝒬.ext_of_isTriangulatedClosed₂ _ hmap h₁ h₃,
      fun h₂ h₃ => 𝒬.ext_of_isTriangulatedClosed₁ _ hmap h₂ h₃⟩
  · intro k
    have h0 : 𝒬 ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj
        ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
          (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).obj
            (regularModule (Rep.{u, v, w, t, s, 0} X ℤ K).algebra))) :=
      𝒬.prop_of_iso (((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso
          ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⋙
            (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q).mapIso
              DGCategory.representableSelfIsoRegular.symm) ≪≫
        tensorWithComplexDerivedObjRegularIso.{u, v, w, t, s} X K).symm) hK
    exact 𝒬.prop_of_iso
      (((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).commShiftIso k).app _).symm
      (𝒬.le_shift k _ h0)

/-- `𝒬`-compactness of the shifts of `K`: morphisms out of them commute with direct sums, taken in
`D(O)`, of objects of `𝒬`. -/
def IsRelativelyCompactShifts : Prop :=
  ∀ A : DerivedCategory (TensorModO.{u, v, w, t, s} X),
    (ObjectProperty.singleton
      (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))).shiftClosure ℤ A →
    ∀ {ι : Type (max u v w t s)} [DecidableEq ι]
      (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X)), (∀ i, 𝒬 (Z i)) →
    ∀ {T : DerivedCategory (TensorModO.{u, v, w, t, s} X)} (j : ∀ i, Z i ⟶ T),
      IsColimit (Cofan.mk T j) → Function.Bijective (cofanMap A j)

/-- **Full faithfulness of `- ⊗_E^𝐋 K` for `K` compact relative to `𝒬`.** This is Tag 09LZ with
compactness of `K` in `D(O)` replaced by compactness relative to `𝒬`, a triangulated subcategory
closed under isomorphisms and direct sums which contains `K`. `hExt` is hypothesis (2) of
Tag 09LZ, that `E` computes the ext groups of `K`. -/
def tensorWithComplexDerived_fullyFaithful_of_ext_of_isRelativelyCompactShifts
    [𝒬.IsClosedUnderIsomorphisms] [𝒬.IsTriangulated]
    (hcoprod : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, 𝒬 (Z i)) → 𝒬 c.pt)
    (hK : 𝒬 (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsRelativelyCompactShifts.{u, v, w, t, s} X K 𝒬)
    (hExt : ∀ n : ℤ, Function.Bijective
      (fun f : repRegularDerived.{u, v, w, t, s} X K ⟶
          (repRegularDerived.{u, v, w, t, s} X K)⟦n⟧ =>
        (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).map f)) :
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).FullyFaithful :=
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K
  letI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  letI : (derivedHomWithComplex.{u, v, w, t, s} X K).Additive := adj.right_adjoint_additive
  letI := tensorWithComplexDerived_signTwist_isTriangulated.{u, v, w, t, s} X K
  letI : (CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) ⋙
      derivedHomWithComplex.{u, v, w, t, s} X K).IsTriangulated :=
    adj.compSignTwist.isTriangulated_rightAdjoint
  letI : IsGrothendieckAbelian.{max u v w t s} (TensorModO.{u, v, w, t, s} X) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, w, max t s} X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  letI : HasCoproducts.{max u v w t s} (DerivedCategory (TensorModO.{u, v, w, t, s} X)) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory
      (TensorModO.{u, v, w, t, s} X)
  let eReg : (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj
        ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).obj
          ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K))) ≅
      repRegularDerived.{u, v, w, t, s} X K :=
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.mapIso
      ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).mapIso
        DGCategory.representableSelfIsoRegular)
  let eTensor : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj
        (repRegularDerived.{u, v, w, t, s} X K) ≅
      DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K) :=
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso eReg.symm ≪≫
      tensorWithComplexDerivedObjRegularIso.{u, v, w, t, s} X K
  show (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⋙
      CategoryTheory.signTwist
        (DerivedCategory (TensorModO.{u, v, w, t, s} X))).FullyFaithful from
    CategoryTheory.Adjunction.fullyFaithfulL_of_devissage_of_preservesColimit adj.compSignTwist
      (fun {ι} Z => by
        classical
        exact CategoryTheory.Pretriangulated.preservesColimit_discrete_of_bijective_cofanMap
          adj.compSignTwist (repRegularDerived.{u, v, w, t, s} X K) (
          Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule.{
            0, max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
          (General.isCompactObject_q_regularModule_arbitraryUniverse.{max u v w t s, 0,
            max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
          (fun i => (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj (Z i))
          (fun A hA => by
            obtain ⟨A₀, n, e, hA₀⟩ := hA
            rw [ObjectProperty.singleton_iff] at hA₀
            subst hA₀
            refine hcompact _ ⟨_, n, (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso e ≪≫
                ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).commShiftIso n).app _ ≪≫
                (CategoryTheory.shiftFunctor _ n).mapIso eTensor,
                (ObjectProperty.singleton_iff _ _).2 rfl⟩ _
              (fun i => prop_tensorWithComplexDerived_obj.{u, v, w, t, s} X K 𝒬 hcoprod hK (Z i))
              _ (coproductIsCoproduct _)))
      (Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule.{0,
        max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra)
      hExt
      (fun T => General.property_of_coproducts_of_two_out_of_three_of_shifts
        (Rep.{u, v, w, t, s, 0} X ℤ K).algebra T)

/-- **Full faithfulness of `- ⊗_E^𝐋 K` for `K` K-injective and compact relative to `𝒬`.** Here
`𝒬` is a triangulated subcategory of `D(O)` closed under isomorphisms and direct sums which
contains `K`. -/
def tensorWithComplexDerived_fullyFaithful_of_isKInjective
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective] [𝒬.IsClosedUnderIsomorphisms]
    [𝒬.IsTriangulated]
    (hcoprod : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, 𝒬 (Z i)) → 𝒬 c.pt)
    (hK : 𝒬 (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsRelativelyCompactShifts.{u, v, w, t, s} X K 𝒬) :
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).FullyFaithful :=
  tensorWithComplexDerived_fullyFaithful_of_ext_of_isRelativelyCompactShifts.{u, v, w, t, s} X K 𝒬
    hcoprod hK hcompact (tensorWithComplexDerived_map_bijective_of_isKInjective.{u, v, w, t, s} X K)

/-- **The derived category of `E` is `𝒬`.** Let `K` be a complex of `O`-modules, let `𝒬` be a
triangulated subcategory of `D(O)` closed under isomorphisms and direct sums, containing `K`, in
which `K` and its shifts are compact and which `K` generates, and assume that
`E = Hom^•(K, K)` computes the ext groups of `K` (`hExt`, hypothesis (2) of Tag 09LZ). Then
`- ⊗_E^𝐋 K` induces an equivalence of `D(E, d)` with `𝒬`; its functor is the corestriction of
`- ⊗_E^𝐋 K` to `𝒬`. -/
def tensorWithComplexDerivedEquivalenceOfExt
    [𝒬.IsClosedUnderIsomorphisms] [𝒬.IsTriangulated]
    (hcoprod : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, 𝒬 (Z i)) → 𝒬 c.pt)
    (hK : 𝒬 (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsRelativelyCompactShifts.{u, v, w, t, s} X K 𝒬)
    (hExt : ∀ n : ℤ, Function.Bijective
      (fun f : repRegularDerived.{u, v, w, t, s} X K ⟶
          (repRegularDerived.{u, v, w, t, s} X K)⟦n⟧ =>
        (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).map f))
    (hgen : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), 𝒬 L →
      (∀ (n : ℤ) (f : (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ ⟶ L), f = 0) →
        IsZero L) :
    DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ≌ 𝒬.FullSubcategory := by
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K
  letI : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  letI : (derivedHomWithComplex.{u, v, w, t, s} X K).Additive := adj.right_adjoint_additive
  letI := tensorWithComplexDerived_signTwist_isTriangulated.{u, v, w, t, s} X K
  letI : (CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) ⋙
      derivedHomWithComplex.{u, v, w, t, s} X K).IsTriangulated :=
    adj.compSignTwist.isTriangulated_rightAdjoint
  let hff :=
    tensorWithComplexDerived_fullyFaithful_of_ext_of_isRelativelyCompactShifts.{u, v, w, t, s}
      X K 𝒬 hcoprod hK hcompact hExt
  have hF := prop_tensorWithComplexDerived_obj.{u, v, w, t, s} X K 𝒬 hcoprod hK
  haveI : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⋙
      CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X))).Full :=
    hff.full
  haveI : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⋙
      CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X))).Faithful :=
    hff.faithful
  haveI : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).Full := hff.full
  haveI : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).Faithful := hff.faithful
  let eReg : (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.obj
        ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).obj
          ((Rep.{u, v, w, t, s, 0} X ℤ K).functor.obj (liftComplex.{u, v, w, t, s} X K))) ≅
      repRegularDerived.{u, v, w, t, s} X K :=
    (quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.mapIso
      ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).mapIso
        DGCategory.representableSelfIsoRegular)
  let eTensor : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj
        (repRegularDerived.{u, v, w, t, s} X K) ≅
      DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K) :=
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso eReg.symm ≪≫
      tensorWithComplexDerivedObjRegularIso.{u, v, w, t, s} X K
  have hker : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), 𝒬 L →
      IsZero ((CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) ⋙
        derivedHomWithComplex.{u, v, w, t, s} X K).obj L) → IsZero L := by
    intro L hL hz
    refine hgen L hL fun n f => ?_
    let e : (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj
        ((repRegularDerived.{u, v, w, t, s} X K)⟦n⟧) ≅
          (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ :=
      ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).commShiftIso n).app _ ≪≫
        (CategoryTheory.shiftFunctor _ n).mapIso eTensor
    have h0 : e.hom ≫ f = 0 :=
      (adj.homEquiv _ L).injective (hz.eq_of_tgt _ _)
    simpa using congrArg (e.inv ≫ ·) h0
  let F' := 𝒬.lift (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K) hF
  haveI : F'.EssSurj := ⟨fun L => by
    have := _root_.isIso_counit_app_of_fullyFaithful_of_ker_eq_zero
      (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⋙
        CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)))
      (CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) ⋙
        derivedHomWithComplex.{u, v, w, t, s} X K) adj.compSignTwist 𝒬 hF hker L.obj L.property
    exact ⟨(derivedHomWithComplex.{u, v, w, t, s} X K).obj L.obj,
      ⟨ObjectProperty.isoMk _ (@asIso _ _ _ _ (adj.compSignTwist.counit.app L.obj) this)⟩⟩⟩
  haveI : F'.IsEquivalence := { }
  exact F'.asEquivalence

/-- The functor of `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedEquivalenceOfExt` followed
by the inclusion of `𝒬` is `- ⊗_E^𝐋 K` itself. -/
theorem tensorWithComplexDerivedEquivalenceOfExt_functor_comp_ι
    [𝒬.IsClosedUnderIsomorphisms] [𝒬.IsTriangulated]
    (hcoprod : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, 𝒬 (Z i)) → 𝒬 c.pt)
    (hK : 𝒬 (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsRelativelyCompactShifts.{u, v, w, t, s} X K 𝒬)
    (hExt : ∀ n : ℤ, Function.Bijective
      (fun f : repRegularDerived.{u, v, w, t, s} X K ⟶
          (repRegularDerived.{u, v, w, t, s} X K)⟦n⟧ =>
        (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).map f))
    (hgen : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), 𝒬 L →
      (∀ (n : ℤ) (f : (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ ⟶ L), f = 0) →
        IsZero L) :
    (tensorWithComplexDerivedEquivalenceOfExt.{u, v, w, t, s} X K 𝒬 hcoprod hK hcompact hExt
      hgen).functor ⋙ 𝒬.ι = tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K :=
  rfl

/-- **The derived category of `E` is `𝒬`, for `K` K-injective.** Let `K` be a K-injective
complex of `O`-modules and let `𝒬` be a triangulated subcategory of `D(O)` closed under
isomorphisms and direct sums, containing `K`, in which `K` and its shifts are compact and which
`K` generates. Then `- ⊗_E^𝐋 K` induces an equivalence of `D(E, d)` with `𝒬`. -/
def tensorWithComplexDerivedEquivalence
    [(liftComplex.{u, v, w, t, s} X K).IsKInjective] [𝒬.IsClosedUnderIsomorphisms]
    [𝒬.IsTriangulated]
    (hcoprod : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, 𝒬 (Z i)) → 𝒬 c.pt)
    (hK : 𝒬 (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsRelativelyCompactShifts.{u, v, w, t, s} X K 𝒬)
    (hgen : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), 𝒬 L →
      (∀ (n : ℤ) (f : (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ ⟶ L), f = 0) →
        IsZero L) :
    DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ≌ 𝒬.FullSubcategory :=
  tensorWithComplexDerivedEquivalenceOfExt.{u, v, w, t, s} X K 𝒬 hcoprod hK hcompact
    (tensorWithComplexDerived_map_bijective_of_isKInjective.{u, v, w, t, s} X K) hgen

end AlgebraicGeometry.RingedSite

end
