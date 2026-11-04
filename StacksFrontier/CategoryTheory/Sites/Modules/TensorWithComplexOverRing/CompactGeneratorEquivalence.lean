module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexCompactGeneratorEquivalence
public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexOverRing.RegularExt

/-!
# A compact K-injective generator gives an equivalence with the derived category of its DGA, over
the base ring

Let `(C, O)` be a ringed site, let `R` be a commutative ring with a sheaf of commutative
`R`-algebra structures on `O`, let `K` be a K-injective complex of `O`-modules with endomorphism
differential graded `R`-algebra `(E, d) = Hom_{Comp^dg(O)}(K, K)`, and let `𝒟` be a strictly
full triangulated subcategory of `D(O)` closed under direct sums, containing the image of
`- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)`, in which `K` is a compact object and which `K` generates. Then
`- ⊗_E^𝐋 K : D(E, d) ⥤ 𝒟` is an equivalence, exact through the sign-twisted identity of `D(O)`.

This is `StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexCompactGeneratorEquivalence`
read over `R` instead of `ℤ`: the argument (Tags 09LZ, 09LY, 09J1) is that one, run against the
adjunction of Tag 09LY over `R`
(`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_adj_derivedHomWithComplexOver`).

## Main results

In the namespace `AlgebraicGeometry.RingedSite`:

* `tensorWithComplexDerived_lift_isEquivalence_of_isCompactGeneratorOver`: for a compact
  K-injective generator `K` of `𝒟`, `- ⊗_E^𝐋 K : D(E, d) ⥤ 𝒟` is an equivalence.
* `tensorWithComplexDerivedLiftEquivalenceOver`: that equivalence, as data.

## References

* [Stacks Project, Tag 09M5](https://stacks.math.columbia.edu/tag/09M5)
* [Stacks Project, Tag 09LZ](https://stacks.math.columbia.edu/tag/09LZ)
* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s o

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (R : Type o) [CommRing R] [Linear R (TensorModO.{u, v, w, t, s} X)]
  [ScalarSections.{u, v, w, t, s, o} X R]
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

variable (P : ObjectProperty (DerivedCategory (TensorModO.{u, v, w, t, s} X)))
  [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
  [(liftComplex.{u, v, w, t, s} X K).IsKInjective]
  (hP : ∀ M, P ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K).obj M))

omit [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
  [(liftComplex.{u, v, w, t, s} X K).IsKInjective] in
include hP in
/-- The values of `- ⊗_E^𝐋 K` composed with the sign-twisted identity lie in `𝒟`. -/
theorem tensorWithComplexDerived_signTwist_obj_propOver (M) :
    P ((tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⋙
      CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X))).obj M) :=
  hP M

/-- `- ⊗_E^𝐋 K`, with values in the subcategory `𝒟`, composed with the sign-twisted identity of
`D(O)`: the same functor as `ObjectProperty.lift`, with the commutation with the shift for which it
is exact. -/
abbrev tensorWithComplexDerivedLiftTwistOver : DifferentialGradedModule.derivedCategory.{o,
    max u v w t s, max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra ⥤ P.FullSubcategory :=
  P.lift (tensorWithComplexDerived.{u, v, w, t, s, o} X R K ⋙
    CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)))
    (tensorWithComplexDerived_signTwist_obj_propOver.{u, v, w, t, s, o} X R K P hP)

/-- `RHom(K, -)` restricted to `𝒟`, composed with the sign-twisted identity of `D(O)`. -/
abbrev derivedHomWithComplexRestrictTwistOver : P.FullSubcategory ⥤
    DifferentialGradedModule.derivedCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra :=
  P.ι ⋙ CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) ⋙
    derivedHomWithComplexOver.{u, v, w, t, s, o} X R K

/-- The adjunction of Tag 09LY, twisted and restricted to `𝒟`. -/
def tensorWithComplexDerivedLiftTwistAdjunctionOver :
    tensorWithComplexDerivedLiftTwistOver.{u, v, w, t, s, o} X R K P hP ⊣
      derivedHomWithComplexRestrictTwistOver.{u, v, w, t, s, o} X R K P :=
  (tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, o} X R K).compSignTwist
    |>.restrictFullyFaithful (iC := 𝟭 _) (iD := P.ι) (Functor.FullyFaithful.id _)
      P.fullyFaithfulι (Functor.leftUnitor _ ≪≫ (P.liftCompιIso _
        (tensorWithComplexDerived_signTwist_obj_propOver.{u, v, w, t, s, o} X R K P hP)).symm)
      (Iso.refl _)

/-- `E ⊗_E^𝐋 K = K`, for the regular module `E`. -/
def tensorWithComplexDerivedRepRegularIsoOver :
    (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).obj
        (repRegularDerivedOver.{u, v, w, t, s, o} X R K) ≅
      DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K) :=
  (tensorWithComplexDerived.{u, v, w, t, s, o} X R K).mapIso
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, o} X R K).algebra).Q.mapIso
        ((toHomotopyCategory (Rep.{u, v, w, t, s, o} X R K).algebra).mapIso
          DGCategory.representableSelfIsoRegular)).symm ≪≫
    tensorWithComplexDerivedObjRegularIsoOver.{u, v, w, t, s, o} X R K

/-- The derived tensor product, twisted and with values in `𝒟`, is exact. -/
instance tensorWithComplexDerived_lift_signTwist_isTriangulatedOver :
    (tensorWithComplexDerivedLiftTwistOver.{u, v, w, t, s, o} X R K P hP).IsTriangulated := by
  have := tensorWithComplexDerived_signTwist_isTriangulatedOver.{u, v, w, t, s, o} X R K
  infer_instance

/-- **A compact K-injective generator gives an equivalence with the derived category of its
endomorphism differential graded algebra.** Let `K` be a K-injective complex of `O`-modules with
endomorphism differential graded algebra `(E, d)`, and let `𝒟` (the property `P`) be a strictly
full triangulated subcategory of `D(O)` which

* contains every object `M ⊗_E^𝐋 K` (`hP`),
* is closed under direct sums (`hsum`),
* contains `K` (`hKP`), as a compact object of `𝒟` (`hcompact`), and
* is generated by `K`: an object `L` of `𝒟` with `Hom(K[n], L) = 0` for all `n` is zero (`hgen`).

Then `- ⊗_E^𝐋 K : D(E, d) ⥤ 𝒟` is an equivalence of categories. -/
theorem tensorWithComplexDerived_lift_isEquivalence_of_isCompactGeneratorOver
    (hsum : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, P (Z i)) → P c.pt)
    (hKP : P (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsCompactObject.{max u v w t s}
      (⟨DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K), hKP⟩ : P.FullSubcategory))
    (hgen : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), P L →
      (∀ (n : ℤ) (f : (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ ⟶ L),
        f = 0) → IsZero L) :
    (P.lift (tensorWithComplexDerived.{u, v, w, t, s, o} X R K) hP).IsEquivalence := by
  let F := tensorWithComplexDerived.{u, v, w, t, s, o} X R K
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplexOver.{u, v, w, t, s, o} X R K
  let L := tensorWithComplexDerivedLiftTwistOver.{u, v, w, t, s, o} X R K P hP
  let G := derivedHomWithComplexRestrictTwistOver.{u, v, w, t, s, o} X R K P
  let adjP : L ⊣ G := tensorWithComplexDerivedLiftTwistAdjunctionOver.{u, v, w, t, s, o} X R K P hP
  let : G.CommShift ℤ := adjP.rightAdjointCommShift ℤ
  let : adjP.CommShift ℤ := adjP.commShift_of_leftAdjoint ℤ
  have : G.IsTriangulated := adjP.isTriangulated_rightAdjoint
  have : L.Additive := ⟨fun {_ _ f g} => P.fullyFaithfulι.map_injective (by
    change F.map (f + g) = P.ι.map (L.map f + L.map g)
    rw [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_add]
    rfl)⟩
  have : G.Additive := adjP.right_adjoint_additive
  let : IsGrothendieckAbelian.{max u v w t s} (TensorModO.{u, v, w, t, s} X) :=
    Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, w, max t s} X.J
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let : HasCoproducts.{max u v w t s} (DerivedCategory (TensorModO.{u, v, w, t, s} X)) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory (TensorModO.{u, v, w, t, s} X)
  have := fun ι => isClosedUnderColimitsOfShape_discrete_of_sigma.{u, v, w, t, s} X P hsum ι
  have : HasCoproducts.{max u v w t s} P.FullSubcategory := fun _ => inferInstance
  have hgenE :=
    Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule.{o,
      max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra
  have hcompE := General.isCompactObject_q_regularModule_arbitraryUniverse.{max u v w t s, o,
    max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra
  let eT := tensorWithComplexDerivedRepRegularIsoOver.{u, v, w, t, s, o} X R K
  let eP : L.obj (repRegularDerivedOver.{u, v, w, t, s, o} X R K) ≅
      (⟨DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K), hKP⟩ : P.FullSubcategory) :=
    P.fullyFaithfulι.preimageIso eT
  have hmap : IsCompactObject.{max u v w t s}
      (L.obj (repRegularDerivedOver.{u, v, w, t, s, o} X R K)) :=
    isCompactObject_of_retract hcompact eP.hom eP.inv eP.hom_inv_id
  have : ∀ ι : Type (max u v w t s), PreservesColimitsOfShape (Discrete ι) G :=
    CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map adjP
      (repRegularDerivedOver.{u, v, w, t, s, o} X R K) hgenE hcompE hmap
  have hbij : ∀ n : ℤ, Function.Bijective
      (fun f : repRegularDerivedOver.{u, v, w, t, s, o} X R K ⟶
          (repRegularDerivedOver.{u, v, w, t, s, o} X R K)⟦n⟧ => L.map f) := fun n =>
    (Function.Bijective.of_comp_iff' P.fullyFaithfulι.homEquiv.bijective _).1
      (tensorWithComplexDerived_map_bijective_of_isKInjectiveOver.{u, v, w, t, s, o} X R K n)
  let hff := adjP.fullyFaithfulL_of_devissage hgenE hbij
    (fun T => General.property_of_coproducts_of_two_out_of_three_of_shifts
      (Rep.{u, v, w, t, s, o} X R K).algebra T)
  have := hff.full
  have := hff.faithful
  have hker : ∀ Y : P.FullSubcategory, IsZero (G.obj Y) → IsZero Y := by
    intro Y hY
    have hY' : IsZero ((derivedHomWithComplexOver.{u, v, w, t, s, o} X R K).obj Y.obj) := hY
    have hzero : ∀ (W : DifferentialGradedModule.derivedCategory.{o, max u v w t s,
        max u v w t s} (Rep.{u, v, w, t, s, o} X R K).algebra) (f : F.obj W ⟶ Y.obj), f = 0 :=
      fun W f => (adj.homEquiv W Y.obj).injective (hY'.eq_of_tgt _ _)
    refine IsZero.of_full_of_faithful_of_isZero P.ι Y (hgen Y.obj Y.property fun n f => ?_)
    let e : F.obj ((repRegularDerivedOver.{u, v, w, t, s, o} X R K)⟦n⟧) ≅
        (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ :=
      (F.commShiftIso n).app _ ≪≫ (CategoryTheory.shiftFunctor _ n).mapIso eT
    calc f = e.inv ≫ e.hom ≫ f := by rw [Iso.inv_hom_id_assoc]
      _ = 0 := by rw [hzero _ (e.hom ≫ f), comp_zero]
  exact isEquivalence_of_fullyFaithful_of_adjunction_of_ker_eq_zero L G adjP hker

/-- **The equivalence `D(E, d) ≌ 𝒟`** of
`tensorWithComplexDerived_lift_isEquivalence_of_isCompactGeneratorOver`, as data. Its functor is
`- ⊗_E^𝐋 K`. -/
def tensorWithComplexDerivedLiftEquivalenceOver
    (hsum : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, P (Z i)) → P c.pt)
    (hKP : P (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsCompactObject.{max u v w t s}
      (⟨DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K), hKP⟩ : P.FullSubcategory))
    (hgen : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), P L →
      (∀ (n : ℤ) (f : (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ ⟶ L),
        f = 0) → IsZero L) :
    DifferentialGradedModule.derivedCategory.{o, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, o} X R K).algebra ≌ P.FullSubcategory :=
  haveI := tensorWithComplexDerived_lift_isEquivalence_of_isCompactGeneratorOver.{u, v, w, t, s, o}
    X R K P hP hsum hKP hcompact hgen
  @Functor.asEquivalence _ _ _ _
    (tensorWithComplexDerivedLiftTwistOver.{u, v, w, t, s, o} X R K P hP) this


end AlgebraicGeometry.RingedSite

end
