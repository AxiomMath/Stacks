module

public import StacksFrontier.CategoryTheory.Sites.Modules.TensorWithComplexRegularExt
public import StacksFrontier.CategoryTheory.Triangulated.AdjointsForExactFunctors
public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentAdjoint.HomologyCoproducts

/-!
# A compact K-injective generator gives an equivalence with the derived category of its DGA

Let `(C, O)` be a ringed site and let `K` be a K-injective complex of `O`-modules, with
endomorphism differential graded algebra `(E, d) = Hom_{Comp^dg(O)}(K, K)`. Let `𝒟` be a strictly
full triangulated subcategory of `D(O)` closed under direct sums, containing the image of the
derived tensor product `- ⊗_E^𝐋 K : D(E, d) ⥤ D(O)` of Tag 09LX, in which `K` is a compact object
and which `K` generates: an object `L` of `𝒟` with `Hom(K[n], L) = 0` for all `n` is zero. Then

`- ⊗_E^𝐋 K : D(E, d) ⥤ 𝒟`

is an equivalence of categories, and it is an exact equivalence (for the triangulated structure
of `D(O)` read through the sign-twisted identity, see below).

## Main results

* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_lift_isEquivalence_of_isCompactGenerator`:
  the equivalence.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerived_lift_signTwist_isTriangulated`: its
  exactness.
* `AlgebraicGeometry.RingedSite.tensorWithComplexDerivedLiftEquivalence`: the equivalence as data.

## Implementation notes

The triangulated structure on `D(E, d)` carried by this library is the one whose distinguished
triangles are cone triangles, against which `- ⊗_E^𝐋 K` is exact only after composing with the
sign-twisted identity `CategoryTheory.signTwist` of `D(O)`
(`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_signTwist_isTriangulated`). That composite
is the same functor (the twist is the identity on objects and morphisms) with another commutation
with the shift, and it is the one used throughout.

## References

* [Stacks Project, Tag 09M5](https://stacks.math.columbia.edu/tag/09M5)
* [Stacks Project, Tag 09LZ](https://stacks.math.columbia.edu/tag/09LZ)
* [Stacks Project, Tag 09J1](https://stacks.math.columbia.edu/tag/09J1)
* [Stacks Project, Tag 0DJL](https://stacks.math.columbia.edu/tag/0DJL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open DifferentialGradedModule

namespace AlgebraicGeometry.RingedSite

universe u v w t s

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory

variable (X : AlgebraicGeometry.RingedSite.{u, v, w})
  (K : CochainComplex (ModO.{u, v, w, t} X) ℤ)

section

variable (P : ObjectProperty (DerivedCategory (TensorModO.{u, v, w, t, s} X)))

/-- A property of objects of `D(O)` closed under the direct sums indexed by the module universe
is closed under colimits of discrete shape. -/
theorem isClosedUnderColimitsOfShape_discrete_of_sigma [P.IsClosedUnderIsomorphisms]
    (hsum : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, P (Z i)) → P c.pt)
    (ι : Type (max u v w t s)) :
    P.IsClosedUnderColimitsOfShape (Discrete ι) where
  colimitsOfShape_le := by
    rintro Y ⟨h⟩
    let c : Cofan (fun i => h.diag.obj ⟨i⟩) :=
      (Cocone.precompose (Discrete.natIsoFunctor (F := h.diag)).inv).obj (Cocone.mk _ h.ι)
    exact hsum _ c ((IsColimit.precomposeInvEquiv (Discrete.natIsoFunctor (F := h.diag)) _).symm
      h.isColimit)
      (fun i => h.prop_diag_obj ⟨i⟩)

/-- The category of `O`-modules is Grothendieck abelian and `D(O)` has coproducts indexed by the
module universe. -/
private theorem isGrothendieckAbelian_and_hasCoproducts :
    IsGrothendieckAbelian.{max u v w t s} (TensorModO.{u, v, w, t, s} X) ∧
      HasCoproducts.{max u v w t s} (DerivedCategory (TensorModO.{u, v, w, t, s} X)) :=
  have := Stacks.SheafOfModules.sheafModulesGrothendieck.{u, v, w, max t s} X.J
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  ⟨this, Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory (TensorModO.{u, v, w, t, s} X)⟩

/-- `D_B(O)`, for a weak Serre class `B` of `O`-modules closed under direct sums, is closed under
the direct sums of `D(O)`, given as colimit cofans. -/
theorem derivedCategoryB_prop_of_isColimit (B : ObjectProperty (TensorModO.{u, v, w, t, s} X))
    (hB : WeakSerre.IsWeakSerre B)
    (hsumB : ∀ {ι : Type (max u v w t s)} (M : ι → TensorModO.{u, v, w, t, s} X),
      (∀ i, B (M i)) → B (∐ M))
    {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
    (c : Cofan Z) (hc : IsColimit c) (hZ : ∀ i, DerivedCategoryB.derivedCategoryB B (Z i)) :
    DerivedCategoryB.derivedCategoryB B c.pt := by
  obtain ⟨_, _⟩ := isGrothendieckAbelian_and_hasCoproducts.{u, v, w, t, s} X
  have hcl := DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms B hB
  exact (DerivedCategoryB.derivedCategoryB B).prop_of_iso
    (hc.coconePointUniqueUpToIso (colimit.isColimit _)).symm
    (Stacks.Duality.derivedCategoryB_prop_coproduct (TensorModO.{u, v, w, t, s} X) B hB
      (fun M hM => hsumB M hM) Z hZ)

end

variable (P : ObjectProperty (DerivedCategory (TensorModO.{u, v, w, t, s} X)))
  [P.IsClosedUnderIsomorphisms] [P.IsTriangulated]
  [(liftComplex.{u, v, w, t, s} X K).IsKInjective]
  (hP : ∀ M, P ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj M))

omit [P.IsClosedUnderIsomorphisms] [P.IsTriangulated] [(X.liftComplex K).IsKInjective] in
include hP in
/-- The values of `- ⊗_E^𝐋 K` composed with the sign-twisted identity lie in `𝒟`. -/
theorem tensorWithComplexDerived_signTwist_obj_prop (M) :
    P ((tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⋙
      CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X))).obj M) :=
  hP M

/-- `- ⊗_E^𝐋 K`, with values in the subcategory `𝒟`, composed with the sign-twisted identity of
`D(O)`: the same functor as `ObjectProperty.lift`, with the commutation with the shift for which it
is exact. -/
abbrev tensorWithComplexDerivedLiftTwist : DifferentialGradedModule.derivedCategory.{0,
    max u v w t s, max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ⥤ P.FullSubcategory :=
  P.lift (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K ⋙
    CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)))
    (tensorWithComplexDerived_signTwist_obj_prop.{u, v, w, t, s} X K P hP)

/-- `RHom(K, -)` restricted to `𝒟`, composed with the sign-twisted identity of `D(O)`. -/
abbrev derivedHomWithComplexRestrictTwist : P.FullSubcategory ⥤
    DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra :=
  P.ι ⋙ CategoryTheory.signTwist (DerivedCategory (TensorModO.{u, v, w, t, s} X)) ⋙
    derivedHomWithComplex.{u, v, w, t, s} X K

/-- The adjunction of Tag 09LY, twisted and restricted to `𝒟`. -/
def tensorWithComplexDerivedLiftTwistAdjunction :
    tensorWithComplexDerivedLiftTwist.{u, v, w, t, s} X K P hP ⊣
      derivedHomWithComplexRestrictTwist.{u, v, w, t, s} X K P :=
  (tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K).compSignTwist
    |>.restrictFullyFaithful (iC := 𝟭 _) (iD := P.ι) (Functor.FullyFaithful.id _)
      P.fullyFaithfulι (Functor.leftUnitor _ ≪≫ (P.liftCompιIso _
        (tensorWithComplexDerived_signTwist_obj_prop.{u, v, w, t, s} X K P hP)).symm)
      (Iso.refl _)

/-- `E ⊗_E^𝐋 K = K`, for the regular module `E`. -/
def tensorWithComplexDerivedRepRegularIso :
    (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).obj
        (repRegularDerived.{u, v, w, t, s} X K) ≅
      DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K) :=
  (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K).mapIso
      ((quasiIsomorphisms (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).Q.mapIso
        ((toHomotopyCategory (Rep.{u, v, w, t, s, 0} X ℤ K).algebra).mapIso
          DGCategory.representableSelfIsoRegular)).symm ≪≫
    tensorWithComplexDerivedObjRegularIso.{u, v, w, t, s} X K

/-- The derived tensor product, twisted and with values in `𝒟`, is exact. -/
instance tensorWithComplexDerived_lift_signTwist_isTriangulated :
    (tensorWithComplexDerivedLiftTwist.{u, v, w, t, s} X K P hP).IsTriangulated := by
  have := tensorWithComplexDerived_signTwist_isTriangulated.{u, v, w, t, s} X K
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
theorem tensorWithComplexDerived_lift_isEquivalence_of_isCompactGenerator
    (hsum : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, P (Z i)) → P c.pt)
    (hKP : P (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsCompactObject.{max u v w t s}
      (⟨DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K), hKP⟩ : P.FullSubcategory))
    (hgen : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), P L →
      (∀ (n : ℤ) (f : (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ ⟶ L),
        f = 0) → IsZero L) :
    (P.lift (tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K) hP).IsEquivalence := by
  let F := tensorWithComplexDerived.{u, v, w, t, s, 0} X ℤ K
  let adj := tensorWithComplexDerived_adj_derivedHomWithComplex.{u, v, w, t, s} X K
  let L := tensorWithComplexDerivedLiftTwist.{u, v, w, t, s} X K P hP
  let R := derivedHomWithComplexRestrictTwist.{u, v, w, t, s} X K P
  let adjP : L ⊣ R := tensorWithComplexDerivedLiftTwistAdjunction.{u, v, w, t, s} X K P hP
  let : R.CommShift ℤ := adjP.rightAdjointCommShift ℤ
  let : adjP.CommShift ℤ := adjP.commShift_of_leftAdjoint ℤ
  have : R.IsTriangulated := adjP.isTriangulated_rightAdjoint
  have : L.Additive := ⟨fun {_ _ f g} => P.fullyFaithfulι.map_injective (by
    show F.map (f + g) = P.ι.map (L.map f + L.map g)
    rw [CategoryTheory.Functor.map_add, CategoryTheory.Functor.map_add]
    rfl)⟩
  have : R.Additive := adjP.right_adjoint_additive
  obtain ⟨_, _⟩ := isGrothendieckAbelian_and_hasCoproducts.{u, v, w, t, s} X
  have := fun ι => isClosedUnderColimitsOfShape_discrete_of_sigma.{u, v, w, t, s} X P hsum ι
  have : HasCoproducts.{max u v w t s} P.FullSubcategory := fun _ => inferInstance
  have hgenE :=
    Stacks.AlgebraicGeometry.ProjectiveGenerator.isWeakTriangulatedGenerator_q_regularModule.{0,
      max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra
  have hcompE := General.isCompactObject_q_regularModule_arbitraryUniverse.{max u v w t s, 0,
    max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra
  let eT := tensorWithComplexDerivedRepRegularIso.{u, v, w, t, s} X K
  let eP : L.obj (repRegularDerived.{u, v, w, t, s} X K) ≅
      (⟨DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K), hKP⟩ : P.FullSubcategory) :=
    P.fullyFaithfulι.preimageIso eT
  have hmap : IsCompactObject.{max u v w t s} (L.obj (repRegularDerived.{u, v, w, t, s} X K)) :=
    isCompactObject_of_retract hcompact eP.hom eP.inv eP.hom_inv_id
  have : ∀ ι : Type (max u v w t s), PreservesColimitsOfShape (Discrete ι) R :=
    CategoryTheory.Pretriangulated.preservesCoproducts_of_isCompactObject_map adjP
      (repRegularDerived.{u, v, w, t, s} X K) hgenE hcompE hmap
  have hbij : ∀ n : ℤ, Function.Bijective
      (fun f : repRegularDerived.{u, v, w, t, s} X K ⟶
          (repRegularDerived.{u, v, w, t, s} X K)⟦n⟧ => L.map f) := by
    intro n
    exact (Function.Bijective.of_comp_iff' (P.fullyFaithfulι.map_bijective _ _) _).mp
      (tensorWithComplexDerived_map_bijective_of_isKInjective.{u, v, w, t, s} X K n)
  let hff := adjP.fullyFaithfulL_of_devissage hgenE hbij
    (fun T => General.property_of_coproducts_of_two_out_of_three_of_shifts
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra T)
  have := hff.full
  have := hff.faithful
  have hker : ∀ Y : P.FullSubcategory, IsZero (R.obj Y) → IsZero Y := by
    intro Y hY
    have hY' : IsZero ((derivedHomWithComplex.{u, v, w, t, s} X K).obj Y.obj) := hY
    have hzero : ∀ (W : DifferentialGradedModule.derivedCategory.{0, max u v w t s,
        max u v w t s} (Rep.{u, v, w, t, s, 0} X ℤ K).algebra) (f : F.obj W ⟶ Y.obj), f = 0 :=
      fun W f => (adj.homEquiv W Y.obj).injective (hY'.eq_of_tgt _ _)
    refine IsZero.of_full_of_faithful_of_isZero P.ι Y (hgen Y.obj Y.property fun n f => ?_)
    let e : F.obj ((repRegularDerived.{u, v, w, t, s} X K)⟦n⟧) ≅
        (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ :=
      (F.commShiftIso n).app _ ≪≫ (CategoryTheory.shiftFunctor _ n).mapIso eT
    calc f = e.inv ≫ e.hom ≫ f := by rw [Iso.inv_hom_id_assoc]
      _ = 0 := by rw [hzero _ (e.hom ≫ f), comp_zero]
  have : L.IsEquivalence :=
    isEquivalence_of_fullyFaithful_of_adjunction_of_ker_eq_zero L R adjP hker
  exact (inferInstance : L.IsEquivalence)

/-- **The equivalence `D(E, d) ≌ 𝒟`** of
`AlgebraicGeometry.RingedSite.tensorWithComplexDerived_lift_isEquivalence_of_isCompactGenerator`,
as data. Its functor is `- ⊗_E^𝐋 K`. -/
def tensorWithComplexDerivedLiftEquivalence
    (hsum : ∀ {ι : Type (max u v w t s)} (Z : ι → DerivedCategory (TensorModO.{u, v, w, t, s} X))
      (c : Cofan Z), IsColimit c → (∀ i, P (Z i)) → P c.pt)
    (hKP : P (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K)))
    (hcompact : IsCompactObject.{max u v w t s}
      (⟨DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K), hKP⟩ : P.FullSubcategory))
    (hgen : ∀ L : DerivedCategory (TensorModO.{u, v, w, t, s} X), P L →
      (∀ (n : ℤ) (f : (DerivedCategory.Q.obj (liftComplex.{u, v, w, t, s} X K))⟦n⟧ ⟶ L),
        f = 0) → IsZero L) :
    DifferentialGradedModule.derivedCategory.{0, max u v w t s, max u v w t s}
      (Rep.{u, v, w, t, s, 0} X ℤ K).algebra ≌ P.FullSubcategory :=
  haveI := tensorWithComplexDerived_lift_isEquivalence_of_isCompactGenerator.{u, v, w, t, s}
    X K P hP hsum hKP hcompact hgen
  @Functor.asEquivalence _ _ _ _ (tensorWithComplexDerivedLiftTwist.{u, v, w, t, s} X K P hP) this

end AlgebraicGeometry.RingedSite

end
