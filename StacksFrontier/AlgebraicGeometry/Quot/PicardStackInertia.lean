module

public import StacksCore.CategoryTheory.Inertia
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerConstraints
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Multiplicative
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackFibered
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackInertiaProduct
public import StacksFrontier.AlgebraicGeometry.Quot.PicardStackSection
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaPresheafProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Inertia

/-!
# The inertia stack of the Picard stack

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site, the
standing data of Stacks 0D25, and let `Picardstack_{X/B}` be the Picard stack of Section 0372.
Stacks 0375 computes the inertia stack of `Picardstack_{X/B}` when `f` has the property that for
*every* test scheme `T` the structure map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` of the base change is an
isomorphism: the inertia stack is then the product (Stacks 0DNH)

`I_{Picardstack_{X/B}} = 𝐆_{m, S} ×_S Picardstack_{X/B}`.

A point of the inertia stack over `T` is a pair `(L, α)` with `L` an invertible module on `X_T`
and `α` an automorphism of `L`; the automorphisms of an invertible module are the invertible
global functions `H^0(X_T, 𝒪_{X_T})^*`, a group independent of `L`; and the hypothesis
identifies those with `H^0(T, 𝒪_T^*)`, which is `𝐆_{m, S}(T)` by Stacks 022U.

## Main definitions

* `Stacks.SheafOfModules.autUnitMulEquivAut`: for an invertible sheaf of modules `L` on a ringed
  site, the automorphism group of the structure sheaf is the automorphism group of `L`.
* `AlgebraicGeometry.Space.PicardObject.Vertical`: the morphisms of `Picardstack_{X/B}` from an
  object to itself whose base map is the identity — the data `α` of the pairs `(L, α)`.
* `AlgebraicGeometry.Space.PicardSituation.StructureUnitsIso`: the assertion that, under the
  hypothesis of Stacks 0375, the invertible global functions on `X_T` are those on `T`.
* `AlgebraicGeometry.Space.testSchemeOver` and
  `AlgebraicGeometry.Space.multiplicativeGroupPointsAt`: a test scheme of the site read as a
  scheme over `S`, and the group `𝐆_{m, S}(T)` of its points of the multiplicative group over
  `S` of Stacks 022U.

## Main results

* `AlgebraicGeometry.Space.verticalEquivAut`: the data `α` of a point `(L, α)` of the inertia
  stack is an automorphism of the invertible module `L`.
* `AlgebraicGeometry.Space.autLineBundleMulEquivAutStructure`: that automorphism group is the
  automorphism group of the structure sheaf of `X_T`, so it does not depend on `L`.
* `AlgebraicGeometry.Space.autStructureMulEquivAut` and
  `AlgebraicGeometry.Space.nonempty_autMulEquiv_of_isInvertibleModule`: the same statement on the
  small étale site of an algebraic space, and the resulting independence of the module.
* `AlgebraicGeometry.Space.nonempty_autLineBundle_mulEquiv_multiplicativeGroupPoints`: under the
  hypothesis of the source and `AlgebraicGeometry.Space.PicardSituation.StructureUnitsIso`, the
  automorphism group of the invertible module of an object of `Picardstack_{X/B}` over `T` is
  `𝐆_{m, S}(T)`.
* `AlgebraicGeometry.Space.nonempty_vertical_equiv_multiplicativeGroupPoints`: under the same
  hypotheses, the points of the inertia stack of `Picardstack_{X/B}` above an object over `T` are
  `𝐆_{m, S}(T)`.
* `AlgebraicGeometry.Space.nonempty_autLineBundle_mulEquiv_of_eq_base`: the same group for any
  two objects over the same test scheme.
* `AlgebraicGeometry.Space.picardInertia_isFiberedInGroupoids`: the inertia stack of
  `Picardstack_{X/B}` is fibred in groupoids over `(Sch/S)_fppf`.
* `AlgebraicGeometry.Space.PicardObject.autMulEquivMultiplicativeGroupPoints`: **Stacks 0375**,
  the automorphism group of the invertible module of an object over `T` is `𝐆_{m, S}(T)`, by an
  explicit isomorphism (multiplication by invertible functions on `T`), under the hypothesis of the
  source alone.
* `AlgebraicGeometry.Space.picardInertiaEquivalenceOverMultiplicativeGroupProduct`:
  **Stacks 0DNH**, the inertia stack of `Picardstack_{X/B}` is `𝐆_{m, S} ×_S Picardstack_{X/B}`
  as categories over `(Sch/S)_fppf`, for the category of Section 0372, under the hypothesis of the
  source alone.

## Implementation notes

The category `Picardstack_{X/B}` of Section 0372 is specified by
`AlgebraicGeometry.Space.PicardCategoryData`. The statements below about the inertia *stack* take
a value of it as a hypothesis, as `AlgebraicGeometry.Space.picardProjection_isFiberedInGroupoids`
does, and the final statement is made for the value `AlgebraicGeometry.Space.picardCategoryData`.
The statements about the pairs `(L, α)` need no category at all: a vertical endomorphism is a
value of `AlgebraicGeometry.Space.PicardHom`.

Only condition (1) of Stacks 04WN, that `Picardstack_{X/B} ⟶ (Sch/S)_fppf` is fibred in
groupoids, is used. So `AlgebraicGeometry.Space.picardInertia_isFiberedInGroupoids` asserts that
the inertia is fibred in groupoids (Stacks 042I applied to condition (1)), and the identification
of Stacks 0DNH is an identification of fibred categories.

For a category over a base whose vertical automorphism groups are coordinatised by a presheaf of
sets, compatibly with the morphisms of the category, the inertia is the product of the category
of elements of that presheaf with the category, as categories over the base
(`CategoryTheory.inertiaEquivalenceOverPresheafProduct`). For `Picardstack_{X/B}` the coordinates
are those of `AlgebraicGeometry.Space.PicardObject.autMulEquivMultiplicativeGroupPoints`: an
automorphism of an invertible module on `X_T` is multiplication by a unique invertible function
on `T` (`AlgebraicGeometry.Space.PicardObject.bijective_unitsToAut`), and a morphism of
`Picardstack_{X/B}` commutes with two such automorphisms exactly when it pulls the one function
back to the other (`AlgebraicGeometry.Space.PicardHom.comp_vertical_eq_vertical_comp_iff` and
`AlgebraicGeometry.Space.PicardHom.pullback_unitsToAut_comp_eq_iff`).

The inertia stack is `CategoryTheory.AbsoluteInertia`. Its objects are the pairs `(x, α)` with
`α` an automorphism of `x` lying over an identity, which is the source's description of the
points of the inertia stack; the forgetful functor to `Picardstack_{X/B}` is
`CategoryTheory.RelativeInertia.π` and the structure functor to the site is
`CategoryTheory.relativeInertiaStruct`.

An invertible module on the small étale site of an algebraic space is an
`AlgebraicGeometry.Space.Modules.{u, u}`, so there is no second module universe.

## References

* [Stacks Project, Tag 0375](https://stacks.math.columbia.edu/tag/0375)
* [Stacks Project, Tag 0DNH](https://stacks.math.columbia.edu/tag/0DNH)
* [Stacks Project, Section 0372](https://stacks.math.columbia.edu/tag/0372)
* [Stacks Project, Tag 022U](https://stacks.math.columbia.edu/tag/022U)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 042I](https://stacks.math.columbia.edu/tag/042I)
* [Stacks Project, Tag 04WN](https://stacks.math.columbia.edu/tag/04WN)
* [Stacks Project, Tag 0D25](https://stacks.math.columbia.edu/tag/0D25)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/-! ### Automorphisms of an invertible sheaf of modules -/

namespace Stacks.SheafOfModules

universe w v' u'

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
  (O : Cᵒᵖ ⥤ CommRingCat.{w})
  (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]

/-- **The automorphism group of an invertible sheaf of modules is the automorphism group of the
structure sheaf.** The isomorphism is induced by the equivalence `- ⊗ L` of Stacks 01CS
together with the unit constraint `𝒪 ⊗ L ≅ L`. -/
def autUnitMulEquivAut (L : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    [IsInvertible O hO L] :
    Aut (_root_.SheafOfModules.unit (TensorSheafification.structureSheaf O hO)) ≃* Aut L :=
  letI F : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO) ⥤
      _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO) :=
    (Tensor.sheafTensor.{u', v', w, w, w}
      ⟨O, Presheaf.isSheaf_of_isSheaf_comp J O (forget₂ CommRingCat RingCat) hO⟩).obj L
  haveI : F.IsEquivalence := tensorLeftFunctor_isEquivalence O hO L
  ((Functor.FullyFaithful.ofFullyFaithful F).autMulEquivOfFullyFaithful
      (_root_.SheafOfModules.unit (TensorSheafification.structureSheaf O hO))).trans
    (Aut.autMulEquivOfIso (tensorLeftFunctorObjUnitIso O hO L))

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Vertical endomorphisms of an object of the Picard stack -/

/-- The *vertical endomorphisms* of an object `(U, b, L)` of `Picardstack_{X/B}`: the morphisms
to itself whose base map is the identity of `U`.  Together with the object these are the pairs
`(L, α)` that Stacks 0375 describes as the points of the inertia stack over `U`. -/
abbrev PicardObject.Vertical {s : PicardSituation B S hS} (A : PicardObject s) :=
  {m : PicardHom A A // m.base = 𝟙 A.T}

namespace PicardObject

variable {s : PicardSituation B S hS}

/-- The unit comparison `(X_{𝟙 U})^* ≅ 𝟭` of Stacks 03LU at the invertible module of an object,
with its target written as that module rather than as the value of the identity functor on
it. -/
def unitComparison (hc : ModulePushforwardCoherence B S hS) (A : PicardObject s) :
    (modulePullback B S hS (baseChangeMap s.f (𝟙 A.T))).obj A.lineBundle ≅ A.lineBundle :=
  (baseChangeIdComparison hc s.f A.T).app A.lineBundle

/-- The automorphism of the invertible module underlying a vertical endomorphism: the comparison
of modules of `m`, read through the comparison of two equal base maps and then through the unit
comparison `(X_{𝟙 U})^* ≅ 𝟭` of Stacks 03LU. -/
def Vertical.iso (hc : ModulePushforwardCoherence B S hS) {A : PicardObject s}
    (v : A.Vertical) : A.lineBundle ≅ A.lineBundle :=
  (unitComparison hc A).symm ≪≫
    ((baseChangeMapComparison s.f v.2).app A.lineBundle).symm ≪≫ asIso v.1.fibre

end PicardObject

/-- **The data `α` of a point `(L, α)` of the inertia stack of `Picardstack_{X/B}` is an
automorphism of the invertible module `L`.**

A morphism of `Picardstack_{X/B}` from `(U, b, L)` to itself consists of a base map and an
isomorphism `(X_{base})^*L ⟶ L`; when the base map is the identity the unit comparison
`(X_{𝟙 U})^* ≅ 𝟭` of Stacks 03LU turns that isomorphism into an automorphism of `L`, and every
automorphism of `L` arises from exactly one such morphism. -/
@[stacks 0375 "the points of the inertia stack of the Picard stack over a test scheme are the \
pairs of an invertible module on the base change and an automorphism of it"]
def verticalEquivAut (hc : ModulePushforwardCoherence B S hS) {s : PicardSituation B S hS}
    (A : PicardObject s) : A.Vertical ≃ (A.lineBundle ≅ A.lineBundle) where
  toFun v := PicardObject.Vertical.iso hc v
  invFun e :=
    ⟨{ base := 𝟙 A.T
       fibre := (PicardObject.unitComparison hc A ≪≫ e).hom
       isIso_fibre := Iso.isIso_hom _ }, rfl⟩
  left_inv v := by
    obtain ⟨⟨b, φ, hφ⟩, hb⟩ := v
    change b = 𝟙 A.T at hb
    subst hb
    refine Subtype.ext (PicardHom.ext rfl ?_)
    simp [PicardObject.Vertical.iso, baseChangeMapComparison]
  right_inv e := by
    refine Iso.ext ?_
    simp only [PicardObject.Vertical.iso, baseChangeMapComparison, eqToIso_refl, Iso.trans_hom,
      Iso.symm_hom, Iso.app_inv, Iso.refl_inv, NatTrans.id_app, asIso_hom, Category.id_comp]
    rw [Iso.inv_hom_id_assoc]

/-- **The identification of the data `α` with an automorphism of the line bundle is unital.**
The identity of an object of `Picardstack_{X/B}` is vertical, and it goes to the identity
automorphism of the invertible module. -/
@[simp]
theorem verticalEquivAut_id (hc : ModulePushforwardCoherence B S hS)
    {s : PicardSituation B S hS} (A : PicardObject s) :
    verticalEquivAut hc A ⟨PicardHom.id hc A, rfl⟩ = Iso.refl A.lineBundle := by
  refine Iso.ext ?_
  simp [verticalEquivAut, PicardObject.Vertical.iso, PicardObject.unitComparison,
    PicardHom.id, baseChangeMapComparison]

/-! ### The automorphism group is the one of the structure sheaf -/

/-- **The automorphism group of an invertible `𝒪_Z`-module is the automorphism group of the
structure sheaf of `Z`.**  This is `Stacks.SheafOfModules.autUnitMulEquivAut` on the small étale
site of an algebraic space.

On sections this is the statement of Stacks 0375 that an automorphism of an invertible module on
`Z` is an invertible global function on `Z`. -/
def autStructureMulEquivAut (Z : AlgebraicSpaces B S hS) (L : Modules.{u, u} B S hS Z.1 Z.2)
    (hL : IsInvertibleModule Z L) : Aut (structureModule Z) ≃* Aut L :=
  haveI := hL
  Stacks.SheafOfModules.autUnitMulEquivAut (structureSheaf B S hS Z.1 Z.2).obj
    (structureRingPresheaf_isSheaf B S hS Z.1 Z.2) L

/-- **The automorphism group of the invertible module of an object of `Picardstack_{X/B}` is the
automorphism group of the structure sheaf of the base change.** -/
@[stacks 0375 "an automorphism of an invertible module on the base change is an invertible \
global function on the base change, so the automorphism group is independent of the module"]
def autLineBundleMulEquivAutStructure {s : PicardSituation B S hS} (A : PicardObject s) :
    Aut A.lineBundle ≃* Aut (structureModule (s.baseChange A.T)) :=
  (autStructureMulEquivAut (s.baseChange A.T) A.lineBundle A.invertible).symm

/-! ### The points of the multiplicative group over `S` -/

/-- A test scheme of the big fppf site over `S`, regarded as a scheme over `S`. -/
abbrev testSchemeOver (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS) : Over S :=
  Over.mk (B.inclusion.map T.hom)

/-- **`𝐆_{m, S}(T)`**, the group of `T`-points of the multiplicative group over `S` of
Stacks 022U: the `S`-morphisms from the test scheme `T` to `𝐆_{m, S}`. -/
abbrev multiplicativeGroupPointsAt (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : BigFppfOver B S hS) : GrpCat.{u} :=
  (yonedaGrpObj (Scheme.asOver (multiplicativeGroupBaseChange S) S)).obj
    (Opposite.op (testSchemeOver B S hS T))

/-- **`𝐆_{m, S}(T)` is the group of invertible global functions on `T`.**  This is Stacks 022U,
in the form `AlgebraicGeometry.baseChangePointsIsoGlobalUnits` gives it. -/
def multiplicativeGroupPointsAtMulEquivUnits (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (T : BigFppfOver B S hS) :
    multiplicativeGroupPointsAt B S hS T ≃*
      (Scheme.Γ.obj (Opposite.op ((BigFppfOver.toScheme B S hS).obj T)))ˣ :=
  CategoryTheory.Iso.groupIsoToMulEquiv ((baseChangePointsIsoGlobalUnits S).app
    (Opposite.op (testSchemeOver B S hS T)))

/-! ### The hypothesis of Stacks 0375 and the step it is used for -/

/-- The assertion that the hypothesis `𝒪_T ≅ f_{T, *}𝒪_{X_T}` of Stacks 0375 identifies the
invertible global functions on the base change `X_T` with the invertible global functions on `T`.

The group on the left is the automorphism group of the structure sheaf of `X_T` as a module over
itself, which is `H^0(X_T, 𝒪_{X_T})^*`; the group on the right is `H^0(T, 𝒪_T^*)`. -/
def PicardSituation.StructureUnitsIso (s : PicardSituation B S hS) : Prop :=
  s.StructureSheafMapIso → ∀ T : s.SchemesOver,
    Nonempty (Aut (structureModule (s.baseChange T)) ≃*
      (Scheme.Γ.obj (Opposite.op ((BigFppfOver.toScheme B S hS).obj T.left)))ˣ)

/-- **Stacks 0375.** Assume that for every test scheme `T` over the base the structure map
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` of the base change is an isomorphism, and that this identifies the
invertible global functions on `X_T` with those on `T` (`hu`). Then for every object `(U, b, L)`
of `Picardstack_{X/B}` the automorphism group of `L` is the group `𝐆_{m, S}(U)` of `U`-points of
the multiplicative group over `S`. -/
theorem nonempty_autLineBundle_mulEquiv_multiplicativeGroupPoints
    {s : PicardSituation B S hS} (h : s.StructureSheafMapIso) (hu : s.StructureUnitsIso)
    (A : PicardObject s) :
    Nonempty (Aut A.lineBundle ≃* multiplicativeGroupPointsAt B S hS A.T.left) := by
  obtain ⟨e⟩ := hu h A.T
  exact ⟨(autLineBundleMulEquivAutStructure A).trans
    (e.trans (multiplicativeGroupPointsAtMulEquivUnits B S hS A.T.left).symm)⟩

/-- **Stacks 0375, the computation of the points of the inertia stack.** Assume that for every
test scheme `T` over the base the structure map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` of the base change is an
isomorphism, and that this identifies the invertible global functions on `X_T` with those on `T`
(`hu`). Then for every object `(U, b, L)` of `Picardstack_{X/B}` the endomorphisms of
`(U, b, L)` lying over the identity of `U` — the data `α` of the pairs `(L, α)`, which are the
points of the inertia stack of `Picardstack_{X/B}` over `U` above the object — are the points
`𝐆_{m, S}(U)` of the multiplicative group over `S`. -/
theorem nonempty_vertical_equiv_multiplicativeGroupPoints
    (hc : ModulePushforwardCoherence B S hS) {s : PicardSituation B S hS}
    (h : s.StructureSheafMapIso) (hu : s.StructureUnitsIso) (A : PicardObject s) :
    Nonempty (A.Vertical ≃ multiplicativeGroupPointsAt B S hS A.T.left) := by
  obtain ⟨e⟩ := nonempty_autLineBundle_mulEquiv_multiplicativeGroupPoints h hu A
  exact ⟨(verticalEquivAut hc A).trans (Aut.isoEquiv.symm.trans e.toEquiv)⟩

/-- **The automorphism group of an invertible module on an algebraic space does not depend on the
module.**  Any two invertible `𝒪_Z`-modules have isomorphic automorphism groups, with no
hypothesis at all: both are the automorphism group of `𝒪_Z`. -/
theorem nonempty_autMulEquiv_of_isInvertibleModule (Z : AlgebraicSpaces B S hS)
    (L L' : Modules.{u, u} B S hS Z.1 Z.2) (hL : IsInvertibleModule Z L)
    (hL' : IsInvertibleModule Z L') : Nonempty (Aut L ≃* Aut L') :=
  ⟨(autStructureMulEquivAut Z L hL).symm.trans (autStructureMulEquivAut Z L' hL')⟩

/-- **The automorphism group of the invertible module does not depend on the invertible
module.**  For any two objects of `Picardstack_{X/B}` over the same test scheme the automorphism
groups of their invertible modules are isomorphic, with no hypothesis at all. -/
theorem nonempty_autLineBundle_mulEquiv_of_eq_base {s : PicardSituation B S hS}
    (A C : PicardObject s) (hT : A.T = C.T) :
    Nonempty (Aut A.lineBundle ≃* Aut C.lineBundle) := by
  obtain ⟨TA, LA, hA⟩ := A
  obtain ⟨TC, LC, hC⟩ := C
  change TA = TC at hT
  subst hT
  exact nonempty_autMulEquiv_of_isInvertibleModule _ LA LC hA hC

/-! ### The inertia stack of the Picard stack -/

/-- **The inertia stack of `Picardstack_{X/B}` is fibred in groupoids over `(Sch/S)_fppf`**, by
Stacks 042I applied to condition (1) of Stacks 04WN. -/
theorem picardInertia_isFiberedInGroupoids (hc : ModulePushforwardCoherence B S hS)
    {s : PicardSituation B S hS} (cd : PicardCategoryData hc s) :
    letI : Category.{u + 1} (PicardObject s) := cd.category
    Functor.IsFiberedInGroupoids
      (relativeInertiaStruct
        (cd.projection ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base)
        (cd.projection ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base)) :=
  let _ : Category.{u + 1} (PicardObject s) := cd.category
  Functor.IsFiberedInGroupoids.absoluteInertia _
    (picardProjection_isFiberedInGroupoids hc cd)


/-! ### The inertia stack of the Picard stack is `𝐆_{m, S} ×_S Picardstack_{X/B}` -/

/-- **`𝐆_{m, S}` as a presheaf of sets on the big fppf site over `S`**: the functor of points of
the multiplicative group over `S` of Stacks 022U, read on the test schemes of the site.  Its
value at a test scheme `T` is `AlgebraicGeometry.Space.multiplicativeGroupPointsAt B S hS T`. -/
def multiplicativeGroupPresheaf (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  (Over.post (X := B.obj hS) B.inclusion : BigFppfOver B S hS ⥤ Over S).op ⋙
    yonedaGrpObj (Scheme.asOver (multiplicativeGroupBaseChange S) S) ⋙ forget GrpCat

/-- The value of `AlgebraicGeometry.Space.multiplicativeGroupPresheaf` at a test scheme is the
group `𝐆_{m, S}(T)` of its points of the multiplicative group over `S`. -/
theorem multiplicativeGroupPresheaf_obj (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (T : BigFppfOver B S hS) :
    (multiplicativeGroupPresheaf B S hS).obj (Opposite.op T)
      = multiplicativeGroupPointsAt B S hS T := rfl

namespace PicardCategoryData

variable {hc : ModulePushforwardCoherence B S hS} {s : PicardSituation B S hS}

/-- The functor `p` of Stacks 04WN: the projection of `Picardstack_{X/B}` to the schemes of the
big fppf site, which forgets the invertible module and the morphism to the base. -/
abbrev siteProjection (cd : PicardCategoryData hc s) :
    letI : Category.{u + 1} (PicardObject s) := cd.category
    PicardObject s ⥤ BigFppfOver B S hS :=
  letI : Category.{u + 1} (PicardObject s) := cd.category
  cd.projection ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) s.base

/-- **A morphism of `Picardstack_{X/B}` lies over the identity of its test scheme exactly when
its base map is the identity.** -/
theorem map_eq_id_iff (cd : PicardCategoryData hc s) {A : PicardObject s}
    (m : letI : Category.{u + 1} (PicardObject s) := cd.category; A ⟶ A) :
    letI : Category.{u + 1} (PicardObject s) := cd.category
    cd.siteProjection.map m = 𝟙 (cd.siteProjection.obj A) ↔
      (Equiv.cast (cd.hom_type A A) m).base = 𝟙 A.T := by
  let _ : Category.{u + 1} (PicardObject s) := cd.category
  have hA : cd.projection.obj A = A.T := cd.projection_obj A
  have key : cd.projection.map m
      = eqToHom hA ≫ (Equiv.cast (cd.hom_type A A) m).base ≫ eqToHom hA.symm :=
    cd.projection_map m
  constructor
  · intro h
    have h' : cd.projection.map m = 𝟙 (cd.projection.obj A) :=
      CostructuredArrow.hom_ext (cd.projection.map m) (𝟙 (cd.projection.obj A)) h
    rw [key] at h'
    have h2 := congrArg (fun t : cd.projection.obj A ⟶ cd.projection.obj A =>
      eqToHom hA.symm ≫ t ≫ eqToHom hA) h'
    simpa using h2
  · intro h
    have h' : cd.projection.map m = 𝟙 (cd.projection.obj A) := by
      rw [key, h]; simp
    exact congrArg (fun t : cd.projection.obj A ⟶ cd.projection.obj A => t.left) h'

/-- **The vertical automorphisms of `p : Picardstack_{X/B} ⟶ (Sch/S)_fppf` above an object are
the morphisms of `Picardstack_{X/B}` from that object to itself whose base map is the
identity.** -/
def verticalAutEquivVertical (cd : PicardCategoryData hc s) (A : PicardObject s) :
    letI : Category.{u + 1} (PicardObject s) := cd.category
    cd.siteProjection.VerticalAut A ≃ A.Vertical :=
  letI : Category.{u + 1} (PicardObject s) := cd.category
  have hp := picardProjection_isFiberedInGroupoids hc cd
  have hiso : ∀ m : A ⟶ A, cd.siteProjection.map m = 𝟙 (cd.siteProjection.obj A) → IsIso m := by
    intro m h
    have h1 : cd.siteProjection.IsHomLift (𝟙 (cd.siteProjection.obj A)) m := by
      rw [← h]; exact IsHomLift.map _ m
    have := hp.isStronglyCartesian_homLift (𝟙 (cd.siteProjection.obj A)) m
    exact Functor.IsStronglyCartesian.isIso_of_base_isIso (p := cd.siteProjection)
      (f := 𝟙 (cd.siteProjection.obj A)) m
  have hbase : ∀ v : A.Vertical,
      (Equiv.cast (cd.hom_type A A) ((Equiv.cast (cd.hom_type A A)).symm v.1)).base = 𝟙 A.T :=
    fun v => (congrArg (fun n : PicardHom A A => n.base)
      (Equiv.apply_symm_apply (Equiv.cast (cd.hom_type A A)) v.1)).trans v.2
  { toFun := fun α => ⟨Equiv.cast (cd.hom_type A A) α.1.asIso.hom,
      (cd.map_eq_id_iff α.1.asIso.hom).mp α.2⟩
    invFun := fun v =>
      ⟨(letI : IsIso ((Equiv.cast (cd.hom_type A A)).symm v.1) :=
          hiso _ ((cd.map_eq_id_iff _).mpr (hbase v));
        Aut.of (asIso ((Equiv.cast (cd.hom_type A A)).symm v.1))),
        (cd.map_eq_id_iff _).mpr (hbase v)⟩
    left_inv := fun α =>
      Subtype.ext (Aut.ext (Iso.ext
        (Equiv.symm_apply_apply (Equiv.cast (cd.hom_type A A)) α.1.asIso.hom)))
    right_inv := fun v =>
      Subtype.ext (Equiv.apply_symm_apply (Equiv.cast (cd.hom_type A A)) v.1) }

/-- **The vertical automorphisms of `p : Picardstack_{X/B} ⟶ (Sch/S)_fppf` above an object are
the automorphisms of its invertible module** (Stacks 0375). -/
def verticalAutEquivAut (cd : PicardCategoryData hc s) (A : PicardObject s) :
    letI : Category.{u + 1} (PicardObject s) := cd.category
    cd.siteProjection.VerticalAut A ≃ Aut A.lineBundle :=
  letI : Category.{u + 1} (PicardObject s) := cd.category
  (cd.verticalAutEquivVertical A).trans ((verticalEquivAut hc A).trans Aut.isoEquiv.symm)

/-- **A coordinatisation of the automorphism groups of the invertible modules of
`Picardstack_{X/B}` by `𝐆_{m, S}` which is compatible with the composition of
`Picardstack_{X/B}`**: for each object, an identification of the automorphism group of its
invertible module with the points of `𝐆_{m, S}` over its test scheme, such that a morphism
commutes with two vertical automorphisms exactly when it restricts the corresponding points. -/
structure MultiplicativeGroupCoordinates (cd : PicardCategoryData hc s) where
  /-- **Stacks 0375**: the automorphisms of the invertible module of an object are the points of
  `𝐆_{m, S}` over its test scheme. -/
  equiv (A : PicardObject s) :
    letI : Category.{u + 1} (PicardObject s) := cd.category
    Aut A.lineBundle ≃
      (multiplicativeGroupPresheaf B S hS).obj (Opposite.op (cd.siteProjection.obj A))
  /-- The commutation of a morphism of `Picardstack_{X/B}` with two vertical automorphisms is the
  restriction of the corresponding points of `𝐆_{m, S}` along its base map. -/
  comm : letI : Category.{u + 1} (PicardObject s) := cd.category
    ∀ {A C : PicardObject s} (m : A ⟶ C) (v : cd.siteProjection.VerticalAut A)
        (w : cd.siteProjection.VerticalAut C),
      m ≫ w.1.asIso.hom = v.1.asIso.hom ≫ m ↔
        (multiplicativeGroupPresheaf B S hS).map (Quiver.Hom.op (cd.siteProjection.map m))
            (equiv C (cd.verticalAutEquivAut C w))
          = equiv A (cd.verticalAutEquivAut A v)

/-- Under the hypothesis of Stacks 0DNH that `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for
*every* test scheme `T` over the base, the automorphism groups of the invertible modules of the
objects of `Picardstack_{X/B}` are the points of `𝐆_{m, S}`, compatibly with the composition of
`Picardstack_{X/B}`. -/
def MultiplicativeGroupCoordinatesIso (cd : PicardCategoryData hc s) : Prop :=
  s.StructureSheafMapIso → Nonempty cd.MultiplicativeGroupCoordinates

/-- **The vertical automorphisms of `Picardstack_{X/B} ⟶ (Sch/S)_fppf` are coordinatised by
`𝐆_{m, S}`.**  The coordinates are those of Stacks 0375: a vertical automorphism of an object is
an automorphism of its invertible module
(`AlgebraicGeometry.Space.PicardCategoryData.verticalAutEquivAut`), and that is a point of
`𝐆_{m, S}` over the test scheme. -/
def verticalAutCoordinates (cd : PicardCategoryData hc s)
    (hu : cd.MultiplicativeGroupCoordinates) :
    letI : Category.{u + 1} (PicardObject s) := cd.category
    cd.siteProjection.VerticalAutCoordinates (multiplicativeGroupPresheaf B S hS) :=
  letI : Category.{u + 1} (PicardObject s) := cd.category
  { equiv := fun A => (cd.verticalAutEquivAut A).trans (hu.equiv A)
    comm := fun {A C} m v w => by
      simpa only [Equiv.trans_apply] using hu.comm m v w }

end PicardCategoryData

/-- **Stacks 0DNH.** Assume that for every scheme `T` over the base the structure map
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` of the base change is an isomorphism, and that the vertical
automorphisms of `Picardstack_{X/B}` are coordinatised by `𝐆_{m, S}` compatibly with its
morphisms (`hu`). Then the inertia stack of
`Picardstack_{X/B}` is `𝐆_{m, S} ×_S Picardstack_{X/B}`: the two are equivalent as categories
over `(Sch/S)_fppf`, by an equivalence which is the identity on the `Picardstack_{X/B}`-factor
and sends a pair `(L, α)` to the point of `𝐆_{m, S}` that the automorphism `α` of `L` is.

"Equal" is read as an equivalence *over the site*
(`CategoryTheory.StacksRepresentableCFG.EquivalenceOver`): a 1-morphism of categories over
`(Sch/S)_fppf` with a quasi-inverse again over the site and unit and counit 2-cells that are
vertical.  The product is the 2-fibre product
`CategoryTheory.inertiaPresheafProduct` of the category of elements of `𝐆_{m, S}` with
`Picardstack_{X/B}`, taken over the site. -/
theorem nonempty_equivalenceOver_picardInertia_multiplicativeGroupProduct
    (hc : ModulePushforwardCoherence B S hS) {s : PicardSituation B S hS}
    (cd : PicardCategoryData hc s)
    (h : s.StructureSheafMapIso) (hu : cd.MultiplicativeGroupCoordinatesIso) :
    letI : Category.{u + 1} (PicardObject s) := cd.category
    Nonempty (StacksRepresentableCFG.EquivalenceOver
      (relativeInertiaStruct cd.siteProjection cd.siteProjection)
      (inertiaPresheafProductStruct cd.siteProjection
        (multiplicativeGroupPresheaf B S hS))) :=
  let _ : Category.{u + 1} (PicardObject s) := cd.category
  (hu h).elim fun hud =>
    ⟨inertiaEquivalenceOverPresheafProduct (cd.verticalAutCoordinates hud)⟩

/-! ### Stacks 0DNH under the hypothesis of the source alone -/

/-- Composing the second argument of a composite of comparisons of modules with a morphism is
composing the first argument with its image.  (The comparison `τ` reads `Lab` as `Lb ⋙ La`.) -/
theorem Functor.fibreComp_comp_map {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} [Category* C₀]
    [Category* C₁] [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀}
    (τ : Lab ≅ Lb ⋙ La) {M : C₀} {M' N' : C₁} {M'' : C₂} (a : La.obj N' ⟶ M)
    (b : Lb.obj M'' ⟶ M') (c : M' ⟶ N') :
    Functor.fibreComp τ a (b ≫ c) = Functor.fibreComp τ (La.map c ≫ a) b := by
  simp [Functor.fibreComp]

/-- A morphism after a transformation into the identity functor, in the first argument of a
composite of comparisons of modules, moves to the second argument. -/
theorem Functor.fibreComp_natTrans_app_comp {C₀ : Type*} {C₂ : Type*} [Category* C₀]
    [Category* C₂] {La : C₀ ⥤ C₀} {Lb : C₂ ⥤ C₀} {Lab : C₂ ⥤ C₀} (τ : Lab ≅ Lb ⋙ La)
    (η : La ⟶ 𝟭 C₀) {M N : C₀} {M'' : C₂} (c : M ⟶ N) (b : Lb.obj M'' ⟶ M) :
    Functor.fibreComp τ (η.app M ≫ c) b = Functor.fibreComp τ (η.app N) (b ≫ c) := by
  have hn := η.naturality c
  simp only [Functor.id_map] at hn
  simp only [Functor.fibreComp, Functor.map_comp, Category.assoc, hn]

/-- **The first step of Stacks 0375 is compatible with the composition of `Picardstack_{X/B}`.**
A morphism `m = (g, φ)` from `A` to `C` commutes with a vertical endomorphism `v` of `A` and a
vertical endomorphism `w` of `C` — that is, `m ∘ w = v ∘ m` — exactly when its comparison of
modules intertwines the automorphisms `α` of `L_A` and `β` of `L_C` that
`AlgebraicGeometry.Space.verticalEquivAut` attaches to them: `φ ∘ g^*β = α ∘ φ`. -/
theorem PicardHom.comp_vertical_eq_vertical_comp_iff (hc : ModulePushforwardCoherence B S hS)
    {s : PicardSituation B S hS} {A C : PicardObject s} (m : PicardHom A C) (v : A.Vertical)
    (w : C.Vertical) :
    PicardHom.comp m w.1 = PicardHom.comp v.1 m ↔
      (modulePullback B S hS (baseChangeMap s.f m.base)).map (verticalEquivAut hc C w).hom ≫
          m.fibre = m.fibre ≫ (verticalEquivAut hc A v).hom := by
  obtain ⟨α, rfl⟩ := (verticalEquivAut hc A).symm.surjective v
  obtain ⟨β, rfl⟩ := (verticalEquivAut hc C).symm.surjective w
  simp only [Equiv.apply_symm_apply]
  have hα : (verticalEquivAut hc A).symm α =
      ⟨⟨(PicardHom.id hc A).base, (PicardHom.id hc A).fibre ≫ α.hom, inferInstance⟩, rfl⟩ := rfl
  have hβ : (verticalEquivAut hc C).symm β =
      ⟨⟨(PicardHom.id hc C).base, (PicardHom.id hc C).fibre ≫ β.hom, inferInstance⟩, rfl⟩ := rfl
  rw [hα, hβ]
  have gen : ∀ {P Q : PicardHom A C} {g : A.T ⟶ C.T} (hP : P.base = g) (hQ : Q.base = g)
      (X Y : (modulePullback B S hS (baseChangeMap s.f g)).obj C.lineBundle ⟶ A.lineBundle),
      P.fibre = eqToHom (by rw [hP]) ≫ X → Q.fibre = eqToHom (by rw [hQ]) ≫ Y →
        (P = Q ↔ X = Y) := by
    intro P Q g hP hQ X Y hX hY
    obtain ⟨pb, pf, pi⟩ := P
    obtain ⟨qb, qf, qi⟩ := Q
    change pb = g at hP
    change qb = g at hQ
    subst hP hQ
    change pf = eqToHom rfl ≫ X at hX
    change qf = eqToHom rfl ≫ Y at hY
    rw [eqToHom_refl, Category.id_comp] at hX hY
    subst hX hY
    exact ⟨fun e ↦ eq_of_heq (PicardHom.mk.inj e).2, fun e ↦ by subst e; rfl⟩
  have hright : (PicardHom.comp m
      ⟨(PicardHom.id hc C).base, (PicardHom.id hc C).fibre ≫ β.hom, inferInstance⟩).fibre =
      (baseChangeMapComparison s.f (Category.comp_id m.base)).hom.app C.lineBundle ≫
        (modulePullback B S hS (baseChangeMap s.f m.base)).map β.hom ≫ m.fibre := by
    have h1 := (PicardHom.comp_fibre
      ({ base := m.base
         fibre := (modulePullback B S hS (baseChangeMap s.f m.base)).map β.hom ≫ m.fibre
         isIso_fibre := inferInstance } : PicardHom A C) (PicardHom.id hc C)).symm.trans
      (PicardHom.comp_id_right_fibre hc
        ({ base := m.base
           fibre := (modulePullback B S hS (baseChangeMap s.f m.base)).map β.hom ≫ m.fibre
           isIso_fibre := inferInstance } : PicardHom A C))
    dsimp only at h1
    rw [PicardHom.comp_fibre]
    dsimp only
    rw [Functor.fibreComp_comp_map]
    exact h1
  have hleft : (PicardHom.comp
      ⟨(PicardHom.id hc A).base, (PicardHom.id hc A).fibre ≫ α.hom, inferInstance⟩ m).fibre =
      (baseChangeMapComparison s.f (Category.id_comp m.base)).hom.app C.lineBundle ≫
        m.fibre ≫ α.hom := by
    have h1 := (PicardHom.comp_fibre (PicardHom.id hc A)
      ({ base := m.base
         fibre := m.fibre ≫ α.hom
         isIso_fibre := inferInstance } : PicardHom A C)).symm.trans
      (PicardHom.comp_id_left_fibre hc
        ({ base := m.base
           fibre := m.fibre ≫ α.hom
           isIso_fibre := inferInstance } : PicardHom A C))
    dsimp only [PicardHom.id] at h1
    rw [PicardHom.comp_fibre]
    dsimp only [PicardHom.id]
    rw [Functor.fibreComp_natTrans_app_comp]
    exact h1
  exact gen (P := PicardHom.comp m
      ⟨(PicardHom.id hc C).base, (PicardHom.id hc C).fibre ≫ β.hom, inferInstance⟩)
    (Q := PicardHom.comp
      ⟨(PicardHom.id hc A).base, (PicardHom.id hc A).fibre ≫ α.hom, inferInstance⟩ m)
    (Category.comp_id m.base) (Category.id_comp m.base) _ _
    (hright.trans (by simp only [baseChangeMapComparison, eqToIso.hom, eqToHom_app]; rfl))
    (hleft.trans (by simp only [baseChangeMapComparison, eqToIso.hom, eqToHom_app]; rfl))

namespace PicardObject

variable {s : PicardSituation B S hS}

/-- **Multiplication by invertible regular functions on the test scheme.**  For an object
`(T, b, L)` of `Picardstack_{X/B}`, an invertible regular function `u` on `T` pulls back to an
invertible global function on `X_T`, and multiplication by it is an automorphism of `L`; this is a
homomorphism `H^0(T, 𝒪_T^*) ⟶ Aut(L)`. -/
def unitsToAut (A : PicardObject s) :
    (Scheme.Γ.obj (Opposite.op ((BigFppfOver.toScheme B S hS).obj A.T.left)))ˣ →*
      Aut A.lineBundle where
  toFun u := Aut.of
    { hom := (globalFunctionSMul B S hS (s.baseChange A.T)
        (baseChangeGlobalFunctions s.f A.T u)).asHom.app A.lineBundle
      inv := (globalFunctionSMul B S hS (s.baseChange A.T)
        (baseChangeGlobalFunctions s.f A.T ↑u⁻¹)).asHom.app A.lineBundle
      hom_inv_id :=
        (globalFunctionSMul_app_comp (s.baseChange A.T) _ _
          (baseChangeGlobalFunctions s.f A.T (↑u⁻¹ * ↑u)) (fun U ↦ by rw [map_mul]; rfl) _).trans
          (globalFunctionSMul_app_eq_id (s.baseChange A.T) _
            (fun U ↦ by rw [Units.inv_mul, map_one]; rfl) _)
      inv_hom_id :=
        (globalFunctionSMul_app_comp (s.baseChange A.T) _ _
          (baseChangeGlobalFunctions s.f A.T (↑u * ↑u⁻¹)) (fun U ↦ by rw [map_mul]; rfl) _).trans
          (globalFunctionSMul_app_eq_id (s.baseChange A.T) _
            (fun U ↦ by rw [Units.mul_inv, map_one]; rfl) _) }
  map_one' := Aut.ext (Iso.ext (globalFunctionSMul_app_eq_id (s.baseChange A.T) _
    (fun U ↦ by rw [Units.val_one, map_one]; rfl) _))
  map_mul' u w := Aut.ext (Iso.ext (globalFunctionSMul_app_comp (s.baseChange A.T) _ _ _
    (fun U ↦ by rw [Units.val_mul, map_mul]; rfl) _).symm)

/-- The automorphism attached to an invertible function is multiplication by its pullback. -/
theorem unitsToAut_hom (A : PicardObject s)
    (u : (Scheme.Γ.obj (Opposite.op ((BigFppfOver.toScheme B S hS).obj A.T.left)))ˣ) :
    (A.unitsToAut u).asIso.hom = (globalFunctionSMul B S hS (s.baseChange A.T)
      (baseChangeGlobalFunctions s.f A.T u)).asHom.app A.lineBundle :=
  rfl

/-- **Every automorphism of the invertible module of an object over `T` is multiplication by
exactly one invertible regular function on `T`**, when `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism
for every test scheme `T`. -/
theorem bijective_unitsToAut (h : s.StructureSheafMapIso) (A : PicardObject s) :
    Function.Bijective A.unitsToAut := by
  have hπ : Function.Bijective (fun a ↦ (baseChangeGlobalFunctions s.f A.T a :
      globalFunctions B S hS (s.baseChange A.T).1)) := by
    simp only [baseChangeGlobalFunctions_eq_terminalChartPullback]
    exact bijective_terminalChartPullback B S hS (baseChangeInclusion s.f A.T)
      (idEtaleChart B S hS A.T.left)
      (by change IsIso (𝟙 ((schemeSpaceFunctor B S hS).obj A.T.left)); infer_instance) (h A.T)
  have hinj : ∀ a b : Scheme.Γ.obj (Opposite.op ((BigFppfOver.toScheme B S hS).obj A.T.left)),
      (globalFunctionSMul B S hS (s.baseChange A.T)
        (baseChangeGlobalFunctions s.f A.T a)).asHom.app A.lineBundle =
      (globalFunctionSMul B S hS (s.baseChange A.T)
        (baseChangeGlobalFunctions s.f A.T b)).asHom.app A.lineBundle → a = b := fun a b hab ↦
    hπ.1 (globalFunctionSMul_injective_of_isInvertibleModule (s.baseChange A.T) A.lineBundle
      A.invertible hab)
  refine ⟨fun u w huw ↦ Units.ext (hinj _ _ (by
    simpa only [unitsToAut_hom] using congrArg (fun a : Aut _ ↦ a.asIso.hom) huw)), fun α ↦ ?_⟩
  have key : ∀ f : A.lineBundle ⟶ A.lineBundle, ∃ c, f = (globalFunctionSMul B S hS
      (s.baseChange A.T) (baseChangeGlobalFunctions s.f A.T c)).asHom.app A.lineBundle := fun f ↦ by
    obtain ⟨b, hb⟩ := exists_eq_globalFunctionSMul_of_isInvertibleModule (s.baseChange A.T)
      A.lineBundle A.invertible f
    obtain ⟨c, hc⟩ := hπ.2 b
    exact ⟨c, hb.trans (by rw [← hc])⟩
  obtain ⟨c, hb₁⟩ := key α.asIso.hom
  obtain ⟨c', hb₂⟩ := key α.asIso.inv
  have h₁ : c' * c = 1 := by
    refine hinj _ _ ?_
    refine (globalFunctionSMul_app_comp (s.baseChange A.T) (baseChangeGlobalFunctions s.f A.T c)
      (baseChangeGlobalFunctions s.f A.T c') (baseChangeGlobalFunctions s.f A.T (c' * c))
      (fun U ↦ by rw [map_mul]; rfl) A.lineBundle).symm.trans (Eq.trans ?_
        (globalFunctionSMul_app_eq_id (s.baseChange A.T) (baseChangeGlobalFunctions s.f A.T 1)
          (fun U ↦ by rw [map_one]; rfl) A.lineBundle).symm)
    rw [← hb₁, ← hb₂, α.asIso.hom_inv_id]
  exact ⟨⟨c, c', mul_comm c c' ▸ h₁, h₁⟩, Aut.ext (Iso.ext ((unitsToAut_hom A _).trans hb₁.symm))⟩

/-- **The `𝐆_m` factor of the inertia stack, as an explicit isomorphism of groups.** When
`𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every test scheme `T`, the automorphism group of the
invertible module of an object of `Picardstack_{X/B}` over `T` is `𝐆_{m, S}(T)`: an automorphism
is multiplication by a unique invertible regular function on `T`
(`AlgebraicGeometry.Space.PicardObject.bijective_unitsToAut`), and `H^0(T, 𝒪_T^*)` is
`𝐆_{m, S}(T)` by Stacks 022U. -/
@[stacks 0375 "the 𝐆_m factor of the inertia stack: when 𝒪_T ⟶ f_{T,*}𝒪_{X_T} is an isomorphism \
for every test scheme T, the automorphism group of the invertible module of an object of the \
Picard stack over T is 𝐆_{m,S}(T)"]
def autMulEquivMultiplicativeGroupPoints (h : s.StructureSheafMapIso) (A : PicardObject s) :
    Aut A.lineBundle ≃* multiplicativeGroupPointsAt B S hS A.T.left :=
  (MulEquiv.ofBijective A.unitsToAut (A.bijective_unitsToAut h)).symm.trans
    (multiplicativeGroupPointsAtMulEquivUnits B S hS A.T.left).symm

/-- The point of `𝐆_{m, S}` of multiplication by an invertible regular function is that
function. -/
theorem autMulEquivMultiplicativeGroupPoints_unitsToAut (h : s.StructureSheafMapIso)
    (A : PicardObject s)
    (u : (Scheme.Γ.obj (Opposite.op ((BigFppfOver.toScheme B S hS).obj A.T.left)))ˣ) :
    A.autMulEquivMultiplicativeGroupPoints h (A.unitsToAut u) =
      (multiplicativeGroupPointsAtMulEquivUnits B S hS A.T.left).symm u := by
  simp only [autMulEquivMultiplicativeGroupPoints, MulEquiv.trans_apply]
  congr 1
  exact (MulEquiv.ofBijective A.unitsToAut (A.bijective_unitsToAut h)).symm_apply_apply u

/-- **The points of the inertia stack.** When `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an
isomorphism for every test scheme `T`, the endomorphisms of an object `(T, b, L)` of
`Picardstack_{X/B}` lying over the identity of `T` — the points `(L, α)` of the inertia stack above
it — are the points `𝐆_{m, S}(T)` of the multiplicative group: `α` is an automorphism of `L`
(`AlgebraicGeometry.Space.verticalEquivAut`, for the comparisons of Stacks 03LU of the library,
`AlgebraicGeometry.Space.modulePushforwardCoherence`), which is multiplication by a unique
invertible function on `T`
(`AlgebraicGeometry.Space.PicardObject.autMulEquivMultiplicativeGroupPoints`). -/
@[stacks 0375 "the points of the inertia stack above an object of the Picard stack over T are \
𝐆_{m,S}(T), when 𝒪_T ⟶ f_{T,*}𝒪_{X_T} is an isomorphism for every test scheme T"]
def verticalEquivMultiplicativeGroupPoints (h : s.StructureSheafMapIso) (A : PicardObject s) :
    A.Vertical ≃ multiplicativeGroupPointsAt B S hS A.T.left :=
  (verticalEquivAut (modulePushforwardCoherence B S hS) A).trans
    (Aut.isoEquiv.symm.trans (A.autMulEquivMultiplicativeGroupPoints h).toEquiv)

/-- Two invertible functions whose multiplications agree on the invertible module are equal. -/
theorem unitsToAut_injective_of_hom_eq (h : s.StructureSheafMapIso) (A : PicardObject s)
    {u w : (Scheme.Γ.obj (Opposite.op ((BigFppfOver.toScheme B S hS).obj A.T.left)))ˣ}
    (e : (A.unitsToAut u).asIso.hom = (A.unitsToAut w).asIso.hom) : u = w :=
  (A.bijective_unitsToAut h).1 (Aut.ext (Iso.ext e))

end PicardObject

/-- **The identification `𝐆_{m, S}(T) = H^0(T, 𝒪_T^*)` of Stacks 022U is natural in `T`**:
restriction of points of `𝐆_{m, S}` along a morphism of test schemes is pullback of invertible
regular functions. -/
theorem multiplicativeGroupPointsAtMulEquivUnits_presheaf_map {T T' : BigFppfOver B S hS}
    (g : T ⟶ T') (x : multiplicativeGroupPointsAt B S hS T') :
    multiplicativeGroupPointsAtMulEquivUnits B S hS T
        ((multiplicativeGroupPresheaf B S hS).map g.op x) =
      Units.map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map g).op).hom.toMonoidHom
        (multiplicativeGroupPointsAtMulEquivUnits B S hS T' x) :=
  ConcreteCategory.congr_hom ((baseChangePointsIsoGlobalUnits S).hom.naturality
    ((Over.post (X := B.obj hS) B.inclusion).map g).op) x

/-- **A morphism of `Picardstack_{X/B}` intertwines two multiplications by invertible functions
exactly when it pulls the one back to the other.**  For `m = (g, φ)` from `A` over `T` to `C` over
`T'`, an invertible function `u` on `T` and `w` on `T'`, the comparison `φ` satisfies
`φ ∘ g^*(w ·) = (u ·) ∘ φ` iff `g^* w = u`. -/
theorem PicardHom.pullback_unitsToAut_comp_eq_iff {s : PicardSituation B S hS}
    (h : s.StructureSheafMapIso) {A C : PicardObject s} (m : PicardHom A C)
    (u : (Scheme.Γ.obj (Opposite.op ((BigFppfOver.toScheme B S hS).obj A.T.left)))ˣ)
    (w : (Scheme.Γ.obj (Opposite.op ((BigFppfOver.toScheme B S hS).obj C.T.left)))ˣ) :
    (modulePullback B S hS (baseChangeMap s.f m.base)).map (C.unitsToAut w).asIso.hom ≫
        m.fibre = m.fibre ≫ (A.unitsToAut u).asIso.hom ↔
      Units.map (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m.base.left).op).hom.toMonoidHom
        w = u := by
  have e : (modulePullback B S hS (baseChangeMap s.f m.base)).map (C.unitsToAut w).asIso.hom ≫
      m.fibre = m.fibre ≫ (A.unitsToAut (Units.map
        (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m.base.left).op).hom.toMonoidHom
          w)).asIso.hom := by
    rw [PicardObject.unitsToAut_hom, PicardObject.unitsToAut_hom]
    refine (congrArg (fun k ↦ k ≫ m.fibre) (modulePullback_map_globalFunctionSMul
      (baseChangeMap s.f m.base) (baseChangeGlobalFunctions s.f C.T w) _
      (globalFunctionsCompatible_baseChangeGlobalFunctions s.f m.base (w : _))
      C.lineBundle)).trans ?_
    exact (NatTrans.naturality (globalFunctionSMul B S hS (s.baseChange A.T)
      (baseChangeGlobalFunctions s.f A.T
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m.base.left).op).hom w))).asHom
      m.fibre).symm
  rw [e]
  refine ⟨fun he ↦ A.unitsToAut_injective_of_hom_eq h
    (((asIso m.fibre).cancel_iso_hom_left _ _).mp he), ?_⟩
  rintro rfl
  rfl

/-- **The coordinates of Stacks 0375 are compatible with the morphisms of `Picardstack_{X/B}`.**
When `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` is an isomorphism for every test scheme `T`, a morphism `m` of
`Picardstack_{X/B}` from `A` over `T` to `C` over `T'` commutes with vertical endomorphisms `v` of
`A` and `w` of `C` exactly when the point of `𝐆_{m, S}(T')` of `w` restricts along the base map of
`m` to the point of `𝐆_{m, S}(T)` of `v`. -/
theorem PicardHom.comp_vertical_eq_iff_multiplicativeGroupPoints
    (hc : ModulePushforwardCoherence B S hS) {s : PicardSituation B S hS}
    (h : s.StructureSheafMapIso) {A C : PicardObject s} (m : PicardHom A C) (v : A.Vertical)
    (w : C.Vertical) :
    PicardHom.comp m w.1 = PicardHom.comp v.1 m ↔
      (multiplicativeGroupPresheaf B S hS).map m.base.left.op
          (C.autMulEquivMultiplicativeGroupPoints h (Aut.of (verticalEquivAut hc C w))) =
        A.autMulEquivMultiplicativeGroupPoints h (Aut.of (verticalEquivAut hc A v)) := by
  obtain ⟨u, hu⟩ := (A.bijective_unitsToAut h).2 (Aut.of (verticalEquivAut hc A v))
  obtain ⟨x, hx⟩ := (C.bijective_unitsToAut h).2 (Aut.of (verticalEquivAut hc C w))
  have hu' : (A.unitsToAut u).asIso = verticalEquivAut hc A v := congrArg Aut.asIso hu
  have hx' : (C.unitsToAut x).asIso = verticalEquivAut hc C w := congrArg Aut.asIso hx
  rw [PicardHom.comp_vertical_eq_vertical_comp_iff hc, ← hu, ← hx, ← hu', ← hx',
    PicardHom.pullback_unitsToAut_comp_eq_iff h,
    PicardObject.autMulEquivMultiplicativeGroupPoints_unitsToAut,
    PicardObject.autMulEquivMultiplicativeGroupPoints_unitsToAut]
  constructor
  · rintro rfl
    apply (multiplicativeGroupPointsAtMulEquivUnits B S hS A.T.left).injective
    refine (multiplicativeGroupPointsAtMulEquivUnits_presheaf_map _ _).trans ?_
    simp only [MulEquiv.apply_symm_apply]
  · intro e
    have e' := (multiplicativeGroupPointsAtMulEquivUnits_presheaf_map m.base.left
      ((multiplicativeGroupPointsAtMulEquivUnits B S hS C.T.left).symm x)).symm.trans
        (congrArg (multiplicativeGroupPointsAtMulEquivUnits B S hS A.T.left) e)
    simpa only [MulEquiv.apply_symm_apply] using e'

/-- Let `f : X ⟶ B` be a morphism of algebraic spaces over `S`, and assume that
for every scheme `T` over `B` the structure map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` of the base change
`f_T : X_T ⟶ T` is an isomorphism.  Then the inertia stack of the Picard stack
`Picardstack_{X/B}` of Section 0372 is equal to `𝐆_{m, S} ×_S Picardstack_{X/B}`: this is an
equivalence of the two over `(Sch/S)_fppf`, which is the identity on the
`Picardstack_{X/B}`-factor and sends a point `(L, α)` of the inertia over `T` to the point of
`𝐆_{m, S}(T) = H^0(T, 𝒪_T^*)` that the automorphism `α` of `L` is multiplication by.

The hypothesis `h` reads the source's `f_{T, *}𝒪_{X_T} ≅ 𝒪_T`, as in Stacks 0375, as the
canonical map `𝒪_T ⟶ f_{T, *}𝒪_{X_T}` being an isomorphism for every test scheme over the base.
The category `Picardstack_{X/B}` is `AlgebraicGeometry.Space.picardCategoryData`, with the
comparisons of inverse images of Stacks 03LU given by
`AlgebraicGeometry.Space.modulePushforwardCoherence`. The standing assumptions of the section that
`f` be flat, proper and of finite presentation are not needed.

"Equal" is read as an equivalence *over the site*
(`CategoryTheory.StacksRepresentableCFG.EquivalenceOver`), and the product is the 2-fibre product
`CategoryTheory.inertiaPresheafProduct` of the category of elements of `𝐆_{m, S}` with
`Picardstack_{X/B}` over the site. -/
@[stacks 0DNH "the inertia stack of the Picard stack is 𝐆_{m,S} ×_S Picardstack_{X/B}, as \
categories over the big fppf site, when 𝒪_T ⟶ f_{T,*}𝒪_{X_T} is an isomorphism for every \
scheme T over the base"]
def picardInertiaEquivalenceOverMultiplicativeGroupProduct (s : PicardSituation B S hS)
    (h : s.StructureSheafMapIso) :
    letI : Category.{u + 1} (PicardObject s) :=
      (picardCategoryData (modulePushforwardCoherence B S hS) s).category
    StacksRepresentableCFG.EquivalenceOver
      (relativeInertiaStruct
        (picardCategoryData (modulePushforwardCoherence B S hS) s).siteProjection
        (picardCategoryData (modulePushforwardCoherence B S hS) s).siteProjection)
      (inertiaPresheafProductStruct
        (picardCategoryData (modulePushforwardCoherence B S hS) s).siteProjection
        (multiplicativeGroupPresheaf B S hS)) :=
  letI : Category.{u + 1} (PicardObject s) :=
    (picardCategoryData (modulePushforwardCoherence B S hS) s).category
  inertiaEquivalenceOverPresheafProduct
    ((picardCategoryData (modulePushforwardCoherence B S hS) s).verticalAutCoordinates
      { equiv := fun A ↦ (A.autMulEquivMultiplicativeGroupPoints h).toEquiv
        comm := fun {A C} m v w ↦ by
          have e : ∀ {D : PicardObject s}
              (x : (picardCategoryData (modulePushforwardCoherence B S hS)
                s).siteProjection.VerticalAut D),
              (picardCategoryData (modulePushforwardCoherence B S hS) s).verticalAutEquivAut D x =
                Aut.of (verticalEquivAut (modulePushforwardCoherence B S hS) D
                  ((picardCategoryData (modulePushforwardCoherence B S hS)
                    s).verticalAutEquivVertical D x)) := fun x ↦ by
            rw [PicardCategoryData.verticalAutEquivAut]
            rfl
          rw [e, e]
          exact PicardHom.comp_vertical_eq_iff_multiplicativeGroupPoints
            (modulePushforwardCoherence B S hS) h m
            ((picardCategoryData (modulePushforwardCoherence B S hS) s).verticalAutEquivVertical
              A v)
            ((picardCategoryData (modulePushforwardCoherence B S hS) s).verticalAutEquivVertical
              C w) })

end AlgebraicGeometry.Space

end
