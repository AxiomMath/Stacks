module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackCategory
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackSectionFunctor
public import StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeSubcategory
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjects

/-!
# The category of relatively perfect complexes (Stacks 0DLE)

Let `f : X ⟶ Y` be a proper, flat, finitely presented morphism of algebraic spaces over a
scheme `S` of a big fppf site.  Stacks 0DLE introduces the category `Complexes_{X/Y}` whose
objects are the triples `(T, g, E)` with `T` a scheme of the site over `S`, `g : T ⟶ Y` a
morphism to the base and `E` an object of `D(𝒪_{X_T})` satisfying conditions (1) and (2) of
Lemma 0DLD, where `X_T = X ×_Y T`.  A morphism `(T, g, E) ⟶ (T', g', E')` is a pair `(h, φ)` of
a morphism `h : T ⟶ T'` over `Y` and an isomorphism `φ : L(X_h)^*E' ⟶ E` of `D(𝒪_{X_T})`, `X_h`
being the induced morphism of base changes.

Conditions (1) and (2) of Lemma 0DLD are *hypotheses* of that lemma, not its conclusions, and
they are spelled out here rather than imported: (1) is relative perfectness of Stacks 0DKN for
the projection `X_T ⟶ T`, which is `AlgebraicGeometry.Space.IsPerfectRelativeToCanonical`, and
(2) is the vanishing of `Ext^i_{𝒪_{X_y}}(E_y, E_y)` for `i < 0` at every point `y : Spec(k) ⟶ T`
with values in a field.

## Main definitions

* `AlgebraicGeometry.Space.ComplexesSituation`: **Stacks 0DLE**, the standing data — the proper,
  flat, finitely presented morphism of algebraic spaces.
* `AlgebraicGeometry.Space.ComplexesSituation.IsRelativelyPerfect`: **condition (1) of Stacks
  0DLD** for an object of `D(𝒪_{X_T})`.
* `AlgebraicGeometry.Space.ComplexesSituation.HasNoNegativeFibreExt`: **condition (2) of Stacks
  0DLD** for an object of `D(𝒪_{X_T})`.
* `AlgebraicGeometry.Space.ComplexesObject`: **Stacks 0DLE**, the objects of
  `Complexes_{X/Y}`.
* `AlgebraicGeometry.Space.ComplexesHom`: **Stacks 0DLE**, the morphisms of `Complexes_{X/Y}`.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesCategory`: **Stacks 0DLE**, the category
  structure, with the identity and the composition the tag designates.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesFunctor`: **Stacks 0DLE**, the functor
  `p : Complexes_{X/Y} ⥤ (Sch/S)_fppf`, `(T, g, E) ↦ T`.

## Main results

* `AlgebraicGeometry.Space.ComplexesSituation.projection_isFlat` and
  `AlgebraicGeometry.Space.ComplexesSituation.projection_isLocallyOfFinitePresentation`: the
  projection `X_T ⟶ T` of a base change is flat and locally of finite presentation, by the
  base-change stability of Stacks 03MO and Stacks 03XR.  These are what make condition (1)
  statable at `X_T ⟶ T` with no hypothesis beyond the ones Stacks 0DLE itself makes.
* `AlgebraicGeometry.Space.ComplexesHom.ext`: a morphism is determined by its base map and its
  comparison of complexes.
* `AlgebraicGeometry.Space.ComplexesSituation.isGroupoid_fiber_complexesFunctor`: **Stacks
  0DLE**, the fibre categories of `p` are groupoids.
* `AlgebraicGeometry.Space.ComplexesSituation.complexesCategory_spec`: **Stacks 0DLE**, the
  whole statement.

## Implementation notes

The standing data extends `AlgebraicGeometry.Space.CoherentSituation` of Stacks 08KB, which is
the same morphism with only finite presentation assumed, by the two further hypotheses of
Stacks 0DLE.  The base change `X_T`, its projection `X_T ⟶ T` and the induced morphism `X_h` of
base changes are therefore `AlgebraicGeometry.Space.CoherentSituation.space`,
`AlgebraicGeometry.Space.CoherentSituation.projection` and
`AlgebraicGeometry.Space.CoherentSituation.relativeMap`, and nothing about base change is
repeated here.

The derived pullback `L(X_h)^*` is the inverse image of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, which is
`AlgebraicGeometry.Space.derivedPull` — Stacks 06YY for the morphism of small étale ringed topoi
of Stacks 03G8 — at `AlgebraicGeometry.Space.hasDerivedModulePullbacks`, the theorem that it
exists along every morphism of algebraic spaces.  The unit law `L(𝟙)^* ≅ 𝟭` and the composition
comparison `L(h ≫ h')^* ≅ L(h')^* ⋙ L(h)^*` of Stacks 0D6D used by the identity and the
composition are the canonical comparisons of that datum, and their coherence is
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData_isCoherent`; both are constructed in
`StacksFrontier.AlgebraicGeometry.Quot.DerivedPullbackPseudofunctor`.

Condition (2) quantifies over the test schemes of the site whose underlying scheme is the
spectrum of a field, which is `AlgebraicGeometry.Stack.IsFieldObject`, together with a morphism
of test schemes to `T`.  The fibre `X_y` is then the base change `X_{T₀}` of the situation at
that test scheme, by the cartesian square
`AlgebraicGeometry.Space.isPullback_baseChangeMap`, and `E_y` is the derived pullback of `E`
along `X_y ⟶ X_T`.  The vanishing of `Ext^i` in a derived category is the hom-group of the
`i`-fold shift being zero, written as a `Subsingleton` as elsewhere in this development.

The comparison of complexes is recorded as a morphism together with
`CategoryTheory.IsIso` rather than as a `CategoryTheory.Iso`, for the reason recorded in the
implementation notes of `StacksFrontier.AlgebraicGeometry.Quot.CoherentStack`: the type of
the morphism depends on the base map, and transporting a single morphism is
`CategoryTheory.eqToHom` while transporting an isomorphism is not.

The abelian structure of the ambient-universe sheaves of modules is removed from instance
selection, as it is in
`StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPullback`: the sheaves of modules here
have their sections in the universe `u` of the schemes, which that instance cannot describe,
and left in place it is reached first and leaves the module universe unsolved.

## References

* [Stacks Project, Tag 0DLE](https://stacks.math.columbia.edu/tag/0DLE)
* [Stacks Project, Tag 0DLD](https://stacks.math.columbia.edu/tag/0DLD)
* [Stacks Project, Tag 0DKN](https://stacks.math.columbia.edu/tag/0DKN)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

universe u v₁ u₁ v₂ u₂

namespace CategoryTheory.Functor

/-- The composite of two fibre morphisms along a comparison of a functor with a composite is an
isomorphism as soon as both are: it is the composite of three isomorphisms.

Proving it once, at an abstract comparison, is what keeps the composition law of a category of
pairs of a test object and an object of a derived category on the corresponding base change
from asking the kernel to compute the underlying morphism of that comparison. -/
instance isIso_fibreComp {C₀ : Type*} {C₁ : Type*} {C₂ : Type*} [Category* C₀] [Category* C₁]
    [Category* C₂] {La : C₁ ⥤ C₀} {Lb : C₂ ⥤ C₁} {Lab : C₂ ⥤ C₀} (τ : Lab ≅ Lb ⋙ La)
    {M : C₀} {M' : C₁} {M'' : C₂} (a : La.obj M' ⟶ M) (b : Lb.obj M'' ⟶ M') [IsIso a]
    [IsIso b] : IsIso (fibreComp τ a b) := by
  dsimp only [fibreComp]
  infer_instance

end CategoryTheory.Functor

namespace CategoryTheory.PullbackData

variable {A : Type u₁} [Category.{v₁} A] {Dat : A → Type u₂}
    [∀ a, Category.{v₂} (Dat a)] (P : PullbackData A Dat)

/-- Replacing the composite by an equal morphism changes the comparison of
`CategoryTheory.PullbackData.triangle` only by the induced identification of the two inverse
images.  This is the companion of `CategoryTheory.PullbackData.triangle_congr_left` for the
composite itself. -/
theorem triangle_congr {a b c : A} {f : a ⟶ b} {g : b ⟶ c} {k k' : a ⟶ c}
    (hk : f ≫ g = k) (hk' : f ≫ g = k') (hkk : k = k') :
    P.triangle hk =
      eqToIso (congrArg (fun m : a ⟶ c => P.pull m) hkk) ≪≫ P.triangle hk' := by
  subst hkk
  have hE : P.triangle hk = P.triangle hk' := rfl
  rw [hE]
  simp

/-- Replacing the second factor of the composite by an equal morphism changes the comparison of
`CategoryTheory.PullbackData.triangle` only by the induced identification of the two inverse
images.  This is the companion of `CategoryTheory.PullbackData.triangle_congr_left` for the
other factor. -/
theorem triangle_congr_right {a b c : A} {f : a ⟶ b} {g g' : b ⟶ c} (hgg : g = g')
    {k : a ⟶ c} (hk : f ≫ g = k) (hk' : f ≫ g' = k) :
    P.triangle hk =
      P.triangle hk' ≪≫ Functor.isoWhiskerRight
        (eqToIso (congrArg (fun m : b ⟶ c => P.pull m) hgg.symm)) (P.pull f) := by
  subst hgg
  have hE : P.triangle hk = P.triangle hk' := rfl
  rw [hE]
  simp

variable {P}

/-- **The unit law at the target of a coherent pullback pseudofunctor datum.**  The comparison
for a composite whose second factor is an identity is the unit law.

`CategoryTheory.PullbackData.IsCoherent` asks for the unit law at the *source* only; this is
its companion at the target, which the two clauses imply.  Associativity instantiated at the
triple `(f, 𝟙 b, 𝟙 b)` identifies the comparison at the objects in the image of the inverse
image along the identity, and naturality of the comparison and of the unit law carries that
identification to every object. -/
theorem IsCoherent.triangle_id_right (hP : P.IsCoherent) {a b : A} {f : a ⟶ b}
    (hk : f ≫ 𝟙 b = f) :
    P.triangle hk = (Functor.leftUnitor (P.pull f)).symm ≪≫
      Functor.isoWhiskerRight (P.idIso b).symm (P.pull f) := by
  have hq : (𝟙 b : b ⟶ b) ≫ 𝟙 b = 𝟙 b := Category.id_comp _
  have key := hP.triangle_comp (f := f) (g := 𝟙 b) (p := 𝟙 b) hk hq hk hk
  apply Iso.ext
  ext N
  have hcomp : ∀ M : Dat b, (P.triangle hk).hom.app ((P.pull (𝟙 b)).obj M) =
      (P.pull f).map ((P.idIso b).inv.app ((P.pull (𝟙 b)).obj M)) := by
    intro M
    have h := NatTrans.congr_app (congrArg Iso.hom key) M
    rw [hP.triangle_id (𝟙 b) hq] at h
    simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
      Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
      Functor.associator_hom_app, Functor.rightUnitor_inv_app, Iso.symm_hom,
      Category.comp_id, Category.id_comp] at h
    exact (cancel_epi ((P.triangle hk).hom.app M)).mp h
  have hnat := (P.triangle hk).hom.naturality ((P.idIso b).hom.app N)
  have hinv := (P.idIso b).inv.naturality ((P.idIso b).hom.app N)
  dsimp at hnat hinv
  simp only [Functor.leftUnitor_inv_app, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom, Category.id_comp]
  refine (cancel_epi ((P.pull f).map ((P.idIso b).hom.app N))).mp ?_
  rw [hnat, hcomp N, ← Functor.map_comp, ← hinv, Functor.map_comp]

/-- The unit law at the target with the identity presented as an arbitrary morphism equal to
it, the shape a consumer indexed by a category of test objects has it in. -/
theorem IsCoherent.triangle_id_right' (hP : P.IsCoherent) {a b : A} {e : b ⟶ b}
    (he : e = 𝟙 b) {f : a ⟶ b} (hk : f ≫ e = f) :
    P.triangle hk = (Functor.leftUnitor (P.pull f)).symm ≪≫
      Functor.isoWhiskerRight
        ((P.idIso b).symm ≪≫ eqToIso (congrArg (fun m : b ⟶ b => P.pull m) he.symm))
        (P.pull f) := by
  have hk' : f ≫ 𝟙 b = f := Category.comp_id f
  rw [P.triangle_congr_right he hk hk', hP.triangle_id_right hk',
    Functor.isoWhiskerRight_trans, Iso.trans_assoc]

end CategoryTheory.PullbackData


namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### The instance context of relative perfectness

These are the instances that make the two clauses of `AlgebraicGeometry.Space.IsPerfectRelativeTo`
of Stacks 0DKN expressible, in the shape
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.Relative` asks for them.  Every one of them is
constructed here: the derived categories are the model
`CategoryTheory.HasDerivedCategory.standard`, the tensor bifunctors of the slices are additive in
each variable by `Stacks.SheafOfModules.Tensor.sheafTensor_additive` and
`Stacks.SheafOfModules.Tensor.sheafTensor_obj_additive`, and their total complexes exist by
`Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize`. -/

/-- Sheafification on the slices of the inverse-image ringed site of a morphism of algebraic
spaces, at the spelling of the localized ringed site. -/
local instance (priority := 2000) inverseImageRingedSite_hasWeakSheafify_over
    {Z W : AlgebraicSpaces B S hS} (f : Z ⟶ W) (U : (inverseImageRingedSite B S hS f).C) :
    HasWeakSheafify ((inverseImageRingedSite B S hS f).over U).J AddCommGrpCat.{u} :=
  smallEtaleRingedSite_hasWeakSheafify_over B S hS Z.1 Z.2 U

/-- Local bijectivity of the weak equivalences on the slices of the inverse-image ringed site, at
the spelling of the localized ringed site. -/
local instance (priority := 2000) inverseImageRingedSite_wEqualsLocallyBijective_over
    {Z W : AlgebraicSpaces B S hS} (f : Z ⟶ W) (U : (inverseImageRingedSite B S hS f).C) :
    ((inverseImageRingedSite B S hS f).over U).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
  smallEtaleRingedSite_wEqualsLocallyBijective_over B S hS Z.1 Z.2 U

/-- The derived category of the modules over the inverse image of the structure sheaf. -/
local instance inverseImageRingedSite_hasDerivedCategory {Z W : AlgebraicSpaces B S hS}
    (f : Z ⟶ W) :
    HasDerivedCategory.{u + 1} (RingedSite.Modules.{u + 1, u, u}
      (inverseImageRingedSite B S hS f)) :=
  HasDerivedCategory.standard _

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat
  RingedSite.sliceHasSheafify RingedSite.sliceWEqualsLocallyBijective
  RingedSite.sliceRestrictionPreservesFiniteLimits
  RingedSite.sliceRestrictionPreservesFiniteColimits

/-- The derived categories of the modules on the slices of the inverse-image ringed site. -/
local instance inverseImageRingedSite_slice_hasDerivedCategory {Z W : AlgebraicSpaces B S hS}
    (f : Z ⟶ W) (U : (inverseImageRingedSite B S hS f).C) :
    HasDerivedCategory.{u + 1} (RingedSite.Modules.{u + 1, u, u}
      ((inverseImageRingedSite B S hS f).over U)) :=
  HasDerivedCategory.standard _

attribute [local instance] RingedSite.sliceHasDerivedCategory
  Stacks.SheafOfModules.DerivedTensorProduct.sliceDerived

/-- The tensor bifunctor of a slice of the inverse-image ringed site is additive. -/
local instance inverseImageRingedSite_slice_sheafTensor_additive {Z W : AlgebraicSpaces B S hS}
    (f : Z ⟶ W) (U : (inverseImageRingedSite B S hS f).C) :
    (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((inverseImageRingedSite B S hS f).over U).O).Additive :=
  inferInstance

/-- The tensor bifunctor of a slice of the inverse-image ringed site is additive in its second
variable. -/
local instance inverseImageRingedSite_slice_sheafTensor_obj_additive
    {Z W : AlgebraicSpaces B S hS} (f : Z ⟶ W) (U : (inverseImageRingedSite B S hS f).C) M :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      ((inverseImageRingedSite B S hS f).over U).O).obj M).Additive :=
  inferInstance

/-- The total complexes of the tensor bifunctor of a slice of the inverse-image ringed site
exist. -/
local instance inverseImageRingedSite_slice_hasMapBifunctor {Z W : AlgebraicSpaces B S hS}
    (f : Z ⟶ W) (U : (inverseImageRingedSite B S hS f).C)
    (K L : CochainComplex
      (RingedSite.Modules.{u + 1, u, u} ((inverseImageRingedSite B S hS f).over U)) ℤ) :
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
        ((inverseImageRingedSite B S hS f).over U).O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.KFlatResolution.hasTotal_ofSize _ _

attribute [local instance] Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceTensorObjAdditive
  Stacks.SheafOfModules.DerivedTensorProduct.sliceHasMapBifunctor

/-- The derived category of `𝒪`-modules on an algebraic space, at the model
`CategoryTheory.HasDerivedCategory.standard` which
`AlgebraicGeometry.Space.derivedModules` is formed at.  Naming it keeps that model out of
instance search for the sheaves of modules of the inverse-image ringed sites, whose section
universe it cannot describe. -/
local instance instModulesHasDerivedCategory (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    HasDerivedCategory.{u + 1} (Modules.{u, u} B S hS F hF) :=
  HasDerivedCategory.standard _

/-! ### The standing data -/

/-- **Stacks 0DLE, the standing data.**  A morphism `f : X ⟶ Y` of algebraic spaces over `S`
which is proper, flat and of finite presentation: the relative algebraic space whose relatively
perfect complexes the category `Complexes_{X/Y}` classifies.

It is the standing datum `AlgebraicGeometry.Space.CoherentSituation` of Stacks 08KB, which
assumes only finite presentation, together with the two further hypotheses of Stacks 0DLE. -/
@[stacks 0DLE "the standing situation: a proper, flat, finitely presented morphism of algebraic
spaces"]
structure ComplexesSituation (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    extends CoherentSituation B S hS where
  /-- It is proper (Stacks 03ZM). -/
  proper : IsProper B S hS toCoherentSituation.f.hom
  /-- It is flat (Stacks 03ML). -/
  flat : IsFlat B S hS toCoherentSituation.f.hom

namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

/-- The projection `X_T ⟶ T` of a base change is flat, by the base-change stability of
Stacks 03MO applied to the cartesian square defining `X_T`. -/
theorem projection_isFlat (T : SchemesOver D.Y) : IsFlat B S hS (D.projection T).hom :=
  (isFlat_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) D.flat

/-- The projection `X_T ⟶ T` of a base change is locally of finite presentation, by the
base-change stability of Stacks 03XR applied to the cartesian square defining `X_T`. -/
theorem projection_isLocallyOfFinitePresentation (T : SchemesOver D.Y) :
    IsLocallyOfFinitePresentation B S hS (D.projection T).hom :=
  (isLocallyOfFinitePresentation_isStableUnderBaseChange B S hS).of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom) D.finitePresentation.1

/-- **Condition (1) of Stacks 0DLD** for an object `E` of `D(𝒪_{X_T})`: `E` is perfect relative
to the test scheme `T`, in the sense of Stacks 0DKN.

The two hypotheses of Stacks 0DKN on the projection `X_T ⟶ T` are not assumed: they are
`AlgebraicGeometry.Space.ComplexesSituation.projection_isFlat` and
`AlgebraicGeometry.Space.ComplexesSituation.projection_isLocallyOfFinitePresentation`, which
follow from flatness and finite presentation of `f` by base change. -/
abbrev IsRelativelyPerfect (T : SchemesOver D.Y) (E : derivedModules B S hS (D.space T)) :
    Prop :=
  IsPerfectRelativeToCanonical B S hS (D.projection T) (D.projection_isFlat T)
    (D.projection_isLocallyOfFinitePresentation T) E

/-- **Condition (2) of Stacks 0DLD** for an object `E` of `D(𝒪_{X_T})`: for every test scheme
`T₀` of the site whose underlying scheme is the spectrum of a field and every morphism
`y : T₀ ⟶ T` of test schemes over `Y`, the negative self-extensions
`Ext^i_{𝒪_{X_y}}(E_y, E_y)` vanish, where `X_y = X_{T₀}` is the fibre and `E_y` is the derived
pullback of `E` along `X_y ⟶ X_T`.

That `X_{T₀}` is the fibre `X_T ×_T T₀` is
`AlgebraicGeometry.Space.isPullback_baseChangeMap`.  Vanishing of `Ext^i` is the hom-group of
the `i`-fold shift being zero. -/
def HasNoNegativeFibreExt (T : SchemesOver D.Y) (E : derivedModules B S hS (D.space T)) : Prop :=
  ∀ (T₀ : SchemesOver D.Y), Stack.IsFieldObject B S hS T₀.left → ∀ (y : T₀ ⟶ T) (i : ℤ), i < 0 →
    Subsingleton (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj E ⟶
      (((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap y)).obj E)⟦i⟧)


section Comparisons


/-- The identification of the derived pullbacks along the morphisms of base changes induced by
two equal morphisms of test schemes. -/
def relativeMapComparison {T T' : SchemesOver D.Y} {h h' : T ⟶ T'} (e : h = h') :
    (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h) ≅
      (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h') :=
  eqToIso (congrArg (fun k : T ⟶ T' =>
    (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)) e)

/-- The component at a complex of the identification of the derived pullbacks along the
morphisms of base changes induced by two equal morphisms of test schemes: it is the transport
along the induced equality of complexes. -/
theorem relativeMapComparison_hom_app {T T' : SchemesOver D.Y} {h h' : T ⟶ T'} (e : h = h')
    (M : derivedModules B S hS (D.space T')) :
    (D.relativeMapComparison e).hom.app M =
      eqToHom (congrArg
        (fun k : T ⟶ T' =>
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj M) e) := by
  subst e
  rfl


/-- The identification `L(X_{𝟙 T})^* ≅ 𝟭` of the derived pullback along the morphism of base
changes induced by an identity with the identity functor.

It is the unit law of `AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, read through the
identification of the induced morphism of base changes with the identity. -/
def idComparison (T : SchemesOver D.Y) :
    (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (𝟙 T)) ≅
      𝟭 (derivedModules B S hS (D.space T)) :=
  eqToIso (congrArg (fun m => (smallEtaleDerivedPullbackData B S hS).pull m)
    (baseChangeMap_id D.f T)) ≪≫
    (smallEtaleDerivedPullbackData B S hS).idIso (D.space T)

/-- The comparison `L(X_{h ≫ h'})^* ≅ L(X_{h'})^* ⋙ L(X_h)^*` of the derived pullback along the
morphism of base changes induced by a composite with the iterated derived pullback.

It is the composition comparison of Stacks 0D6D of
`AlgebraicGeometry.Space.smallEtaleDerivedPullbackData`, at the equality
`X_h ≫ X_{h'} = X_{h ≫ h'}` of `AlgebraicGeometry.Space.baseChangeMap_comp`. -/
def compComparison {T T' T'' : SchemesOver D.Y} (h : T ⟶ T') (h' : T' ⟶ T'') :
    (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (h ≫ h')) ≅
      (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h') ⋙
        (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h) :=
  (smallEtaleDerivedPullbackData B S hS).triangle (baseChangeMap_comp D.f h h').symm

end Comparisons

/-! ### The coherences of the comparisons of derived pullbacks along morphisms of base changes -/

section Coherences


/-- The comparison for a composite equal to `k` is the triangle for `k` after the identification
of the derived pullbacks along the equal morphisms of test schemes. -/
private theorem compComparison_eq_relativeMapComparison_trans {T T' T'' : SchemesOver D.Y}
    (h : T ⟶ T') (h' : T' ⟶ T'') {k : T ⟶ T''} (e : h ≫ h' = k)
    (hk : D.relativeMap h ≫ D.relativeMap h' = D.relativeMap k) :
    D.compComparison h h' =
      D.relativeMapComparison e ≪≫ (smallEtaleDerivedPullbackData B S hS).triangle hk :=
  (smallEtaleDerivedPullbackData B S hS).triangle_congr _ hk (congrArg D.relativeMap e)

/-- The comparison for a composite whose first factor is an identity is the identity law. -/
theorem idComparison_comp_fac {T T' : SchemesOver D.Y} (h : T ⟶ T') :
    D.compComparison (𝟙 T) h ≪≫
        Functor.isoWhiskerLeft ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h))
          (D.idComparison T) ≪≫
        Functor.rightUnitor ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)) =
      D.relativeMapComparison (Category.id_comp h) := by
  have he : D.relativeMap (𝟙 T) = 𝟙 (D.space T) := baseChangeMap_id D.f T
  have hk2 : D.relativeMap (𝟙 T) ≫ D.relativeMap h = D.relativeMap h := by
    rw [he, Category.id_comp]
  have hfold : ∀ {F G : derivedModules B S hS (D.space T) ⥤ derivedModules B S hS (D.space T)}
      (p : F = G) (q : G = F) (α : F ≅ 𝟭 (derivedModules B S hS (D.space T))),
      α.symm ≪≫ eqToIso p ≪≫ eqToIso q ≪≫ α =
        Iso.refl (𝟭 (derivedModules B S hS (D.space T))) := by
    intro F G p q α
    subst p
    simp
  rw [D.compComparison_eq_relativeMapComparison_trans _ _ (Category.id_comp h) hk2,
    (smallEtaleDerivedPullbackData_isCoherent B S hS).triangle_id' he hk2]
  simp only [idComparison]
  rw [Functor.isoWhiskerLeft_trans]
  simp only [← Iso.trans_assoc, Functor.trans_isoWhiskerLeft_trans, relativeMapComparison]
  simp only [Iso.trans_assoc]
  rw [hfold]
  simp only [Functor.isoWhiskerLeft_refl, Iso.refl_trans, Iso.trans_refl, Iso.symm_self_id]

/-- The comparison for a composite whose second factor is an identity is the identity law. -/
theorem comp_idComparison_fac {T T' : SchemesOver D.Y} (h : T ⟶ T') :
    D.compComparison h (𝟙 T') ≪≫
        Functor.isoWhiskerRight (D.idComparison T')
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)) ≪≫
        Functor.leftUnitor ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)) =
      D.relativeMapComparison (Category.comp_id h) := by
  have he : D.relativeMap (𝟙 T') = 𝟙 (D.space T') := baseChangeMap_id D.f T'
  have hk2 : D.relativeMap h ≫ D.relativeMap (𝟙 T') = D.relativeMap h := by
    rw [he, Category.comp_id]
  rw [D.compComparison_eq_relativeMapComparison_trans _ _ (Category.comp_id h) hk2,
    (smallEtaleDerivedPullbackData_isCoherent B S hS).triangle_id_right' he hk2]
  simp only [idComparison, relativeMapComparison]
  apply Iso.ext
  ext M
  simp

/-- The associativity coherence of the comparisons for composites of morphisms of test
schemes. -/
theorem compComparison_assoc {T T' T'' T3 : SchemesOver D.Y} (h : T ⟶ T') (h' : T' ⟶ T'')
    (h'' : T'' ⟶ T3) :
    D.compComparison (h ≫ h') h'' ≪≫
        Functor.isoWhiskerLeft ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h''))
          (D.compComparison h h') =
      D.relativeMapComparison (Category.assoc h h' h'') ≪≫
        D.compComparison h (h' ≫ h'') ≪≫
        Functor.isoWhiskerRight (D.compComparison h' h'')
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)) ≪≫
        Functor.associator ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h''))
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h'))
          ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap h)) := by
  have hk : D.relativeMap h ≫ D.relativeMap h' = D.relativeMap (h ≫ h') :=
    (baseChangeMap_comp D.f h h').symm
  have hq : D.relativeMap h' ≫ D.relativeMap h'' = D.relativeMap (h' ≫ h'') :=
    (baseChangeMap_comp D.f h' h'').symm
  have hkr : D.relativeMap (h ≫ h') ≫ D.relativeMap h'' = D.relativeMap ((h ≫ h') ≫ h'') :=
    (baseChangeMap_comp D.f (h ≫ h') h'').symm
  have hr' : D.relativeMap h ≫ D.relativeMap (h' ≫ h'') = D.relativeMap (h ≫ h' ≫ h'') :=
    (baseChangeMap_comp D.f h (h' ≫ h'')).symm
  have hrr : D.relativeMap ((h ≫ h') ≫ h'') = D.relativeMap (h ≫ h' ≫ h'') :=
    congrArg (fun k : T ⟶ T3 => D.relativeMap k) (Category.assoc h h' h'')
  have hr : D.relativeMap h ≫ D.relativeMap (h' ≫ h'') = D.relativeMap ((h ≫ h') ≫ h'') :=
    hr'.trans hrr.symm
  have e1 : D.compComparison (h ≫ h') h'' =
      (smallEtaleDerivedPullbackData B S hS).triangle hkr := rfl
  have e2 : D.compComparison h h' = (smallEtaleDerivedPullbackData B S hS).triangle hk := rfl
  have e3 : D.compComparison h' h'' = (smallEtaleDerivedPullbackData B S hS).triangle hq := rfl
  have e4 : D.compComparison h (h' ≫ h'') =
      (smallEtaleDerivedPullbackData B S hS).triangle hr' := rfl
  rw [e1, e2, e3, e4, (smallEtaleDerivedPullbackData_isCoherent B S hS).triangle_comp' hk hq hr hkr,
    (smallEtaleDerivedPullbackData B S hS).triangle_congr hr hr' hrr]
  simp only [relativeMapComparison, Iso.trans_assoc, Iso.symm_self_id, Iso.trans_refl]

end Coherences

end ComplexesSituation

/-! ### Objects and morphisms -/

/-- **Stacks 0DLE, the objects.**  An object of `Complexes_{X/Y}`: a scheme `T` of the site over
`Y` together with an object of `D(𝒪_{X_T})` satisfying conditions (1) and (2) of Stacks
0DLD. -/
@[stacks 0DLE "objects"]
structure ComplexesObject (D : ComplexesSituation B S hS) where
  /-- The test scheme over `Y`, that is, the pair `(T, g)` of the source. -/
  T : SchemesOver D.Y
  /-- The object of the derived category of `𝒪_{X_T}`-modules on the base change `X_T`. -/
  E : derivedModules B S hS (D.space T)
  /-- It is perfect relative to the test scheme: condition (1) of Stacks 0DLD. -/
  relativelyPerfect : D.IsRelativelyPerfect T E
  /-- Its negative self-extensions vanish on every fibre over a point with values in a field:
  condition (2) of Stacks 0DLD. -/
  noNegativeFibreExt : D.HasNoNegativeFibreExt T E

/-- **Stacks 0DLE, the morphisms.**  A morphism of `Complexes_{X/Y}`: a morphism `h : T ⟶ T'` of
test schemes over `Y` together with an isomorphism `L(X_h)^*E' ⟶ E` of `D(𝒪_{X_T})`. -/
@[stacks 0DLE "morphisms"]
structure ComplexesHom {D : ComplexesSituation B S hS} (A A' : ComplexesObject D) where
  /-- The morphism of test schemes over `Y`. -/
  base : A.T ⟶ A'.T
  /-- The comparison of the derived pullback of the complex of the target with the complex of
  the source. -/
  fibre : ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap base)).obj A'.E ⟶ A.E
  /-- The comparison is an isomorphism. -/
  isIso_fibre : IsIso fibre

/-- **Two morphisms of `Complexes_{X/Y}` with the same base map and the same comparison of
complexes are equal**, the comparison being compared heterogeneously.

This is `AlgebraicGeometry.Space.ComplexesHom.ext` with the transport along the equality of base
maps replaced by a heterogeneous equality, which is what makes it usable when the two base maps
are only definitionally equal; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Quot.CoherentStackBaseChange` for why the transport cannot
be recognised as an identity. -/
theorem complexesHom_eq_of_heq
    {D : ComplexesSituation B S hS} {A A' : ComplexesObject D}
    {m n : ComplexesHom A A'} (hb : m.base = n.base)
    (h : HEq m.fibre n.fibre) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hb
  subst hb
  cases eq_of_heq h
  rfl

namespace ComplexesHom

variable {D : ComplexesSituation B S hS} {A A' : ComplexesObject D}

attribute [instance] isIso_fibre

/-- Two morphisms of `Complexes_{X/Y}` with the same base map and the same comparison of
complexes, read through the identification of the two derived pullbacks that the equality of
base maps induces, are equal. -/
@[ext (iff := false)]
theorem ext {m n : ComplexesHom A A'} (hbase : m.base = n.base)
    (hfibre : eqToHom (by rw [hbase]) ≫ m.fibre = n.fibre) : m = n := by
  obtain ⟨mb, mf, mi⟩ := m
  obtain ⟨nb, nf, ni⟩ := n
  change mb = nb at hbase
  subst hbase
  simp only [eqToHom_refl, Category.id_comp] at hfibre
  subst hfibre
  rfl


/-- Two morphisms with equal base maps are equal once one comparison of complexes is the other
one after a transport. -/
private theorem eq_of_fibre_eq_eqToHom_comp {m n : ComplexesHom A A'} (hb : m.base = n.base)
    (h : m.fibre = eqToHom (by rw [hb]) ≫ n.fibre) : m = n :=
  complexesHom_eq_of_heq hb (heq_of_eq_eqToHom_comp _ _ h)

/-- **Stacks 0DLE, the identity.**  The identity of an object of `Complexes_{X/Y}`: the identity
of its test scheme, with the unit law of the derived pullback as its comparison of complexes. -/
def id (A : ComplexesObject D) : ComplexesHom A A where
  base := 𝟙 A.T
  fibre := (D.idComparison A.T).hom.app A.E
  isIso_fibre := inferInstance

/-- **Stacks 0DLE, the composition.**  The composite of two morphisms of `Complexes_{X/Y}`: the
composite of the base maps, with the derived pullback of the second comparison followed by the
first, read through the composition comparison of the derived pullbacks. -/
def comp {A'' : ComplexesObject D} (m : ComplexesHom A A') (n : ComplexesHom A' A'') :
    ComplexesHom A A'' where
  base := m.base ≫ n.base
  fibre := Functor.fibreComp (D.compComparison m.base n.base) m.fibre n.fibre
  isIso_fibre := inferInstance

/-- The comparison of complexes of the identity of an object of `Complexes_{X/Y}` is the unit
law of the derived pullback at its complex. -/
@[simp]
theorem id_fibre (A : ComplexesObject D) :
    (ComplexesHom.id A).fibre = (D.idComparison A.T).hom.app A.E := rfl

/-- The comparison of complexes of a composite in `Complexes_{X/Y}` is the derived pullback of
the second comparison followed by the first, read through the composition comparison. -/
@[simp]
theorem comp_fibre {A'' : ComplexesObject D} (m : ComplexesHom A A')
    (n : ComplexesHom A' A'') :
    (m.comp n).fibre =
      Functor.fibreComp (D.compComparison m.base n.base) m.fibre n.fibre := rfl

/-- **Stacks 0DLE, the unit law at the source.**  Composing a morphism of `Complexes_{X/Y}` after
the identity of its source is that morphism.

It is the unit law `AlgebraicGeometry.Space.ComplexesSituation.idComparison_comp_fac` of the
comparisons of derived pullbacks along the morphisms of base changes. -/
theorem id_comp (m : ComplexesHom A A') : (ComplexesHom.id A).comp m = m := by
  have hb : ((ComplexesHom.id A).comp m).base = m.base := Category.id_comp m.base
  have key := Functor.fibreComp_id_left (D.idComparison A.T)
    (D.compComparison (𝟙 A.T) m.base)
    (D.relativeMapComparison (Category.id_comp m.base))
    (D.idComparison_comp_fac m.base) m.fibre
  rw [D.relativeMapComparison_hom_app] at key
  exact eq_of_fibre_eq_eqToHom_comp hb key

/-- **Stacks 0DLE, the unit law at the target.**  Composing a morphism of `Complexes_{X/Y}`
before the identity of its target is that morphism.

It is the unit law `AlgebraicGeometry.Space.ComplexesSituation.comp_idComparison_fac` of the
comparisons of derived pullbacks along the morphisms of base changes. -/
theorem comp_id (m : ComplexesHom A A') : m.comp (ComplexesHom.id A') = m := by
  have hb : (m.comp (ComplexesHom.id A')).base = m.base := Category.comp_id m.base
  have key := Functor.fibreComp_id_right (D.idComparison A'.T)
    (D.compComparison m.base (𝟙 A'.T))
    (D.relativeMapComparison (Category.comp_id m.base))
    (D.comp_idComparison_fac m.base) m.fibre
  rw [D.relativeMapComparison_hom_app] at key
  exact eq_of_fibre_eq_eqToHom_comp hb key

/-- **Stacks 0DLE, associativity.**  Composition of morphisms of `Complexes_{X/Y}` is
associative.

It is the associativity coherence
`AlgebraicGeometry.Space.ComplexesSituation.compComparison_assoc` of the comparisons of derived
pullbacks along the morphisms of base changes. -/
theorem assoc {A'' A3 : ComplexesObject D} (m : ComplexesHom A A')
    (n : ComplexesHom A' A'') (p : ComplexesHom A'' A3) :
    (m.comp n).comp p = m.comp (n.comp p) := by
  have hb : ((m.comp n).comp p).base = (m.comp (n.comp p)).base :=
    Category.assoc m.base n.base p.base
  have key := Functor.fibreComp_assoc (D.compComparison m.base n.base)
    (D.compComparison (m.base ≫ n.base) p.base)
    (D.compComparison n.base p.base)
    (D.compComparison m.base (n.base ≫ p.base))
    (D.relativeMapComparison (Category.assoc m.base n.base p.base))
    (D.compComparison_assoc m.base n.base p.base) m.fibre n.fibre p.fibre
  rw [D.relativeMapComparison_hom_app] at key
  exact eq_of_fibre_eq_eqToHom_comp hb key

end ComplexesHom

/-! ### The category and its projection -/


namespace ComplexesSituation

variable (D : ComplexesSituation B S hS)

/-- **The category `Complexes_{X/Y}` of Stacks 0DLE.**  The category structure on the objects
whose hom-sets are `AlgebraicGeometry.Space.ComplexesHom`, whose identity is
`AlgebraicGeometry.Space.ComplexesHom.id` and whose composition is
`AlgebraicGeometry.Space.ComplexesHom.comp`. -/
@[instance_reducible, stacks 0DLE "the category structure on the objects: the hom-sets are the
pairs (h, φ), with the identity and the composition the tag designates"]
def complexesCategory : Category.{u + 1} (ComplexesObject D) where
  Hom A A' := ComplexesHom A A'
  id A := ComplexesHom.id A
  comp m n := ComplexesHom.comp m n
  id_comp m := ComplexesHom.id_comp m
  comp_id m := ComplexesHom.comp_id m
  assoc m n p := ComplexesHom.assoc m n p

/-- **The projection of `Complexes_{X/Y}` to the test schemes over `Y` of Stacks 0DLE**,
`(T, g, E) ↦ (T, g)`: it forgets the complex and keeps the base map of a morphism. -/
@[stacks 0DLE "the functor (T, g, E) ↦ (T, g) to the test schemes over the base"]
def complexesProjection :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    ComplexesObject D ⥤ SchemesOver D.Y :=
  letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
  { obj := fun A => A.T
    map := fun m => m.base
    map_id := fun _ => rfl
    map_comp := fun _ _ => rfl }

/-- The hom-sets of `Complexes_{X/Y}` are the pairs of a base map and a comparison of
complexes. -/
theorem complexesCategory_hom (A A' : ComplexesObject D) :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    (A ⟶ A') = ComplexesHom A A' := rfl

/-- The identity of `Complexes_{X/Y}` is `AlgebraicGeometry.Space.ComplexesHom.id`. -/
theorem complexesCategory_id (A : ComplexesObject D) :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    (𝟙 A : ComplexesHom A A) = ComplexesHom.id A := rfl

/-- Composition in `Complexes_{X/Y}` is `AlgebraicGeometry.Space.ComplexesHom.comp`. -/
theorem complexesCategory_comp {A A' A'' : ComplexesObject D} (m : ComplexesHom A A')
    (n : ComplexesHom A' A'') :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    ((m ≫ n : A ⟶ A'') : ComplexesHom A A'') = ComplexesHom.comp m n := rfl

/-- The projection of `Complexes_{X/Y}` forgets the complex. -/
theorem complexesProjection_obj (A : ComplexesObject D) :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    (complexesProjection D).obj A = A.T := rfl

/-- The projection of `Complexes_{X/Y}` acts on morphisms by taking the base map. -/
theorem complexesProjection_map {A A' : ComplexesObject D} (m : ComplexesHom A A') :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    (complexesProjection D).map (m : A ⟶ A') = m.base := rfl

/-- **The functor `p : Complexes_{X/Y} ⥤ (Sch/S)_fppf` of Stacks 0DLE**, `(T, g, E) ↦ T`: the
projection to the test schemes over `Y` followed by forgetting the morphism to `Y`. -/
@[stacks 0DLE "the functor p : Complexes_{X/B} ⥤ (Sch/S)_fppf, (T, g, E) ↦ T"]
def complexesFunctor :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    ComplexesObject D ⥤ BigFppfOver B S hS :=
  letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
  complexesProjection D ⋙ CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y

/-- The functor `p` sends `(T, g, E)` to `T`. -/
theorem complexesFunctor_obj (A : ComplexesObject D) :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    (complexesFunctor D).obj A = A.T.left := rfl

/-- The functor `p` sends `(h, φ)` to `h`. -/
theorem complexesFunctor_map {A A' : ComplexesObject D} (m : ComplexesHom A A') :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    (complexesFunctor D).map (m : A ⟶ A') = m.base.left := rfl

section Groupoid

attribute [local instance] complexesCategory

variable {D}

/-- A morphism of `Complexes_{X/Y}` over an isomorphism of test schemes has a section, whose base
map is the inverse isomorphism: its comparison of complexes is the derived pullback of the
inverse of the given one, read through the composition comparison for `h⁻¹ ≫ h = 𝟙` and the
unit law. -/
theorem exists_section_of_isIso_base {A A' : ComplexesObject D} (m : ComplexesHom A A')
    [IsIso m.base] : ∃ n : ComplexesHom A' A, n.comp m = ComplexesHom.id A' ∧ IsIso n.base := by
  have he : inv m.base ≫ m.base = 𝟙 A'.T := IsIso.inv_hom_id m.base
  let L := (smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap (inv m.base))
  let γ : L.obj A.E ⟶ A'.E := L.map (inv m.fibre) ≫
    (D.compComparison (inv m.base) m.base).inv.app A'.E ≫
    (D.relativeMapComparison he).hom.app A'.E ≫ (D.idComparison A'.T).hom.app A'.E
  have : IsIso γ := by
    dsimp only [γ]
    infer_instance
  refine ⟨⟨inv m.base, γ, this⟩, ComplexesHom.eq_of_fibre_eq_eqToHom_comp he ?_,
    inferInstanceAs (IsIso (inv m.base))⟩
  have h1 : L.map m.fibre ≫ γ = (D.compComparison (inv m.base) m.base).inv.app A'.E ≫
      (D.relativeMapComparison he).hom.app A'.E ≫ (D.idComparison A'.T).hom.app A'.E := by
    dsimp only [γ]
    rw [← L.map_comp_assoc, IsIso.hom_inv_id, L.map_id, Category.id_comp]
  have key : Functor.fibreComp (D.compComparison (inv m.base) m.base) γ m.fibre =
      eqToHom (congrArg (fun k : A'.T ⟶ A'.T =>
        ((smallEtaleDerivedPullbackData B S hS).pull (D.relativeMap k)).obj A'.E) he) ≫
        (D.idComparison A'.T).hom.app A'.E := by
    rw [Functor.fibreComp, h1, Iso.hom_inv_id_app_assoc, D.relativeMapComparison_hom_app]
  exact key

/-- A morphism of `Complexes_{X/Y}` over an isomorphism of test schemes is an isomorphism. -/
theorem isIso_of_isIso_base {A A' : ComplexesObject D} (m : A ⟶ A')
    [IsIso (m : ComplexesHom A A').base] : IsIso m := by
  obtain ⟨n, hn, hb⟩ := exists_section_of_isIso_base (m : ComplexesHom A A')
  obtain ⟨n', hn', -⟩ := exists_section_of_isIso_base n
  let n₁ : A' ⟶ A := n
  let n₂ : A ⟶ A' := n'
  have hn₁ : n₁ ≫ m = 𝟙 A' := hn
  have hn₂ : n₂ ≫ n₁ = 𝟙 A := hn'
  have e : n₂ = m := by
    rw [← Category.comp_id n₂, ← hn₁, ← Category.assoc, hn₂, Category.id_comp]
  rw [e] at hn₂
  exact ⟨n₁, hn₂, hn₁⟩

variable (D)

/-- **The fibre categories of `p : Complexes_{X/Y} ⥤ (Sch/S)_fppf` are groupoids**, as Stacks
0DLE asserts. -/
@[stacks 0DLE "the fibre categories of p over the schemes T are groupoids"]
theorem isGroupoid_fiber_complexesFunctor (T : BigFppfOver B S hS) :
    IsGroupoid ((complexesFunctor D).Fiber T) where
  all_isIso {a b} φ := by
    have hφ : (complexesFunctor D).IsHomLift (𝟙 T) φ.1 := φ.2
    have hb : IsIso (φ.1 : ComplexesHom a.1 b.1).base.left := by
      have h := IsHomLift.fac' (complexesFunctor D) (𝟙 T) φ.1
      rw [complexesFunctor_map, Category.id_comp, eqToHom_trans] at h
      rw [h]
      exact (eqToIso (IsHomLift.domain_eq (complexesFunctor D) (𝟙 T) φ.1 |>.trans
        (IsHomLift.codomain_eq (complexesFunctor D) (𝟙 T) φ.1).symm)).isIso_hom
    have : IsIso ((CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y).map
        (φ.1 : ComplexesHom a.1 b.1).base) := hb
    have : IsIso (φ.1 : ComplexesHom a.1 b.1).base :=
      isIso_of_reflects_iso _ (CostructuredArrow.proj (schemeSpaceFunctor B S hS) D.Y)
    have : IsIso φ.1 := isIso_of_isIso_base φ.1
    exact ⟨⟨⟨inv φ.1, inferInstance⟩, Subtype.ext (IsIso.hom_inv_id φ.1),
      Subtype.ext (IsIso.inv_hom_id φ.1)⟩⟩

end Groupoid

/-- **Stacks 0DLE in full.**  `Complexes_{X/Y}` is a category whose objects are the triples
`(T, g, E)` of `AlgebraicGeometry.Space.ComplexesObject` — a scheme `T` over `S`, a morphism
`g : T ⟶ Y` and an object `E` of `D(𝒪_{X_T})` satisfying conditions (1) and (2) of Stacks
0DLD — and whose morphisms are the pairs `(h, φ)` of `AlgebraicGeometry.Space.ComplexesHom`,
with the identity and the composition the tag designates; the rule `(T, g, E) ↦ T` is a functor
`p` to `(Sch/S)_fppf`, and its fibre categories are groupoids.

The conjuncts are: the hom-sets, the identity, the composition, the two clauses saying that `p`
is the designated rule, and that the fibre categories of `p` are groupoids.  That the objects
and the morphisms are the designated data is the definition of
`AlgebraicGeometry.Space.ComplexesObject` and `AlgebraicGeometry.Space.ComplexesHom`, and that
the category laws hold is `AlgebraicGeometry.Space.ComplexesSituation.complexesCategory`, whose
existence is asserted by the statement being about it. -/
@[stacks 0DLE "the whole statement: the category Complexes_{X/B} of the triples (T, g, E) and the
pairs (h, φ), with the designated identity and composition, the functor p : (T, g, E) ↦ T to
(Sch/S)_fppf, and its fibre categories being groupoids"]
theorem complexesCategory_spec :
    letI : Category.{u + 1} (ComplexesObject D) := complexesCategory D
    (∀ A A' : ComplexesObject D, (A ⟶ A') = ComplexesHom A A') ∧
      (∀ A : ComplexesObject D, (𝟙 A : ComplexesHom A A) = ComplexesHom.id A) ∧
      (∀ {A A' A'' : ComplexesObject D} (m : ComplexesHom A A') (n : ComplexesHom A' A''),
        ((m ≫ n : A ⟶ A'') : ComplexesHom A A'') = ComplexesHom.comp m n) ∧
      (∀ A : ComplexesObject D, (complexesFunctor D).obj A = A.T.left) ∧
      (∀ {A A' : ComplexesObject D} (m : ComplexesHom A A'),
        (complexesFunctor D).map (m : A ⟶ A') = m.base.left) ∧
      ∀ T : BigFppfOver B S hS, IsGroupoid ((complexesFunctor D).Fiber T) :=
  ⟨complexesCategory_hom D, complexesCategory_id D,
    fun m n => complexesCategory_comp D m n, complexesFunctor_obj D,
    fun m => complexesFunctor_map D m, isGroupoid_fiber_complexesFunctor D⟩

end ComplexesSituation


end AlgebraicGeometry.Space

end
