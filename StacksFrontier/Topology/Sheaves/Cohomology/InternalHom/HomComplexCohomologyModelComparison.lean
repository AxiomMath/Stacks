module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.CompositionAssociativity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.QuasiIsoInvariance
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomQuasiIso
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyProduct

/-!
# The comparison of two models of a self-Ext algebra, as a map of modules

Let `(X, O_X)` be a ringed space, let `K` and `I` be complexes of `O_X`-modules and let
`κ : K ⟶ I` be a morphism of complexes. Precomposition and postcomposition with `κ` give two
morphisms of internal Hom complexes,

`SheafHom^•(I, I) ⟶ SheafHom^•(K, I)`  and  `SheafHom^•(K, K) ⟶ SheafHom^•(K, I)`,

and hence two maps on cohomology sheaves. This file proves that they are maps of modules for the
composition pairing `Stacks.SheafOfModules.homologyMul`: the first is a map of left modules over
`H^*(SheafHom^•(I, I))`, the second a map of right modules over `H^*(SheafHom^•(K, K))`, and
both carry the unit of their source to the class of `κ`.

When moreover `κ` is a quasi-isomorphism, `I` is K-injective and `K` is strictly perfect, both
maps are quasi-isomorphisms — each is an instance of a statement the library already has, Stacks
0A95 for the first and Stacks 08JH for the second — so `H^*(SheafHom^•(K, I))` is a bimodule on
which both sides act through isomorphisms, unitally, by the class of `κ`. That is the comparison
of two models of a self-Ext algebra; it is assembled into an isomorphism of sheaves of graded
algebras in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyModelIso`.

## Main definitions

* `Stacks.SheafOfModules.ofHomCycle`: **the degree-zero cocycle of `SheafHom^•(K, I)` named by
  `κ`**, as a morphism from the unit sheaf into the degree-zero cycles.
* `Stacks.SheafOfModules.homologyClassOfHom`: **the class of `κ` in `H⁰(SheafHom^•(K, I))`.**
* `Stacks.SheafOfModules.sourceComparison` and `Stacks.SheafOfModules.targetComparison`: the two
  morphisms of internal Hom complexes that `κ` induces.

## Main results

* `Stacks.SheafOfModules.homologyMap_sourceComparison_homologyMul`: **precomposition with `κ` is
  a map of left modules** over the composition product on `H^*(SheafHom^•(I, I))`.
* `Stacks.SheafOfModules.homologyMap_targetComparison_homologyMul`: **postcomposition with `κ`
  is a map of right modules** over the composition product on `H^*(SheafHom^•(K, K))`.
* `Stacks.SheafOfModules.homologyMap_sourceComparison_homologyOne` and
  `Stacks.SheafOfModules.homologyMap_targetComparison_homologyOne`: both maps send the unit to
  the class of `κ`, so both are unital.
* `Stacks.SheafOfModules.homologyMul_homologyClassOfHom` and
  `Stacks.SheafOfModules.homologyClassOfHom_homologyMul`: **each comparison map is
  multiplication by the class of `κ`** — on the right for precomposition, on the left for
  postcomposition.
* `Stacks.SheafOfModules.quasiIso_sourceComparison`,
  `Stacks.SheafOfModules.quasiIso_targetComparison` and
  `Stacks.SheafOfModules.isIso_homologyMap_comparison`: **for `κ` a quasi-isomorphism from a
  strictly perfect complex into a K-injective one, both comparison maps are
  quasi-isomorphisms**, hence isomorphisms on cohomology sheaves in every degree.

## Implementation notes

The two module laws are the cohomology transport of
`AlgebraicGeometry.RingedSite.compositionMap_natural_source` and
`AlgebraicGeometry.RingedSite.compositionMap_natural_target`, and they are proved by the same
two-step descent that `Stacks.SheafOfModules.homologyMul_assoc` uses. On classes of cocycles the
pairing is computed by `Stacks.SheafOfModules.homologyMul_app_homologyπ`, the cycle it produces
is computed inside the complex by
`Stacks.SheafOfModules.iCycles_cycleComposition_pureSection`, the induced maps on cycles and
classes are moved past `homologyπ` and `iCycles` by `HomologicalComplex.homologyπ_naturality` and
`HomologicalComplex.cyclesMap_i`, and there the identity is the section-level functoriality
`AlgebraicGeometry.RingedSite.compositionSection_homMap`. The two cocycles are then compared by
`SheafOfModules.injective_app_of_mono` applied to the inclusion of cycles. Arbitrary cohomology
sections are lifted to cocycles on a common refinement by
`Stacks.SheafOfModules.eq_of_forall_lift₂'`, the two-morphism companion of
`Stacks.SheafOfModules.eq_of_forall_lift₃`.

**The two module laws carry no degree transport.** Each relates a pairing in total degree
`i + j` to another pairing in total degree `i + j`, so nothing has to be moved along an equality
of degrees; associativity, by contrast, has to compare `(i + j) + k` with `i + (j + k)` and
therefore carries `SheafOfModules.castHom`.

**The two quasi-isomorphism statements needed no new mathematics: the library already had
both.** Precomposition is Stacks 0A95, `AlgebraicGeometry.RingedSite.homMap_quasiIso`, read at
the identity of `I` in the covariant variable; postcomposition is Stacks 08JH,
`AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand`, read at `E = K`. The
module laws above hold for an arbitrary morphism of complexes and use neither hypothesis; the
two hypotheses enter only in `quasiIso_sourceComparison` and `quasiIso_targetComparison`.

**The two identifications of a comparison map with multiplication by the class of `κ` are the
only statements here that do carry a degree transport**, along `add_zero i` and `zero_add j`
respectively, because one factor sits in degree `0`; their section-level inputs
`AlgebraicGeometry.RingedSite.compositionSection_ofHomSection` and
`AlgebraicGeometry.RingedSite.ofHomSection_compositionSection` are stated at total degree `p`
and `q` rather than `p + 0` and `0 + q` for the same reason that
`AlgebraicGeometry.RingedSite.compositionSection_idSection_right` is, and are its
generalisation from the identity to an arbitrary `κ`.

**The isomorphism of graded algebras itself is assembled elsewhere.** No declaration *in this
file* asserts that `Stacks.SheafOfModules.homologyGradedAlgebra Rc K` and
`Stacks.SheafOfModules.homologyGradedAlgebra Rc I` agree; no morphism-of-graded-algebras API is
used below. The assembly is `Stacks.SheafOfModules.modelComparison` of
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.HomComplexCohomologyModelIso`, which
inverts `HomologicalComplex.homologyMap (targetComparison …)` degreewise and transports the
algebra laws across that inverse. The one input it needs beyond what is proved here is
`Stacks.SheafOfModules.homologyMul_assoc` read at the class of `κ`, which turns the two module
laws into multiplicativity.

## References

* [Stacks Project, Tag 0A90](https://stacks.math.columbia.edu/tag/0A90)
* [Stacks Project, Tag 0A91](https://stacks.math.columbia.edu/tag/0A91)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Category Limits TopologicalSpace Opposite
open AlgebraicGeometry

universe u

attribute [local implicit_reducible] TopCat.Sheaf CategoryTheory.sheafCompose
  Stacks.SheafOfModules.Tensor.ringSheaf

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive monoidalSpace' symmetricSpace'
  monoidalPreadditiveSpace' monoidalClosedSpace' preservesColimitTensorRightSpace'
  preservesFiniteColimitsTensorRight' preservesFiniteColimitsTensorLeft'

attribute [local instance] RingedSite.ringSheafSectionsCommRing
  RingedSite.presheafOfModulesMonoidalCategory
  RingedSite.curriedTensorPreservesZeroMorphisms
  RingedSite.curriedTensorObjPreservesZeroMorphisms

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The internal Hom complex of two complexes of `O_X`-modules, abbreviated for the statements
below. `Stacks.SheafOfModules.endComplex` is its diagonal case. -/
abbrev homComplex (K I : CochainComplex (StructureSheafModules Rc) ℤ) :
    CochainComplex (StructureSheafModules Rc) ℤ :=
  (RingedSite.sheafHomComplex (ringedSite Rc) K I).obj

/-! ### Two descents -/

/-- **Two-section, two-morphism version of `Stacks.eq_of_forall_lift`.** Two sections of a
separated presheaf of modules agree as soon as they agree after restriction along every
*simultaneous* local lift of two given sections along two locally surjective morphisms.

`Stacks.eq_of_forall_lift₂` lifts two sections along *one* morphism, which a product of two
classes in two different cohomology sheaves cannot use; this is
`Stacks.SheafOfModules.eq_of_forall_lift₃` with its third slot repeated. -/
theorem eq_of_forall_lift₂'
    {Q M₁ M₂ N₁ N₂ : PresheafOfModules.{u} (structureSheaf Rc).obj}
    (hQ : Presheaf.IsSeparated (Opens.grothendieckTopology ↥X) Q.presheaf)
    (α₁ : M₁ ⟶ N₁) (α₂ : M₂ ⟶ N₂)
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥X) α₁]
    [PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥X) α₂]
    {V : (Opens ↥X)ᵒᵖ} (a₁ : N₁.obj V) (a₂ : N₂.obj V) (u v : Q.obj V)
    (h : ∀ {W : (Opens ↥X)ᵒᵖ} (f : V ⟶ W) (m₁ : M₁.obj W) (m₂ : M₂.obj W),
      α₁.app W m₁ = N₁.map f a₁ → α₂.app W m₂ = N₂.map f a₂ →
      Q.map f u = Q.map f v) :
    u = v :=
  -- The local surjectivity is handed over positionally: `eq_of_forall_lift₃` asks for it at the
  -- ringed-site spelling `Tensor.ringSheaf Rc` of the ring sheaf, which instance search does not
  -- identify with the `structureSheaf Rc` of `StructureSheafModules Rc`, while unification does.
  @eq_of_forall_lift₃ X Rc Q M₁ M₂ M₂ N₁ N₂ N₂ hQ α₁ α₂ α₂
    (by assumption) (by assumption) (by assumption) V a₁ a₂ a₂ u v
    fun f m₁ m₂ _ hm₁ hm₂ _ => h f m₁ m₂ hm₁ hm₂

/-! ### Transporting an induced map through cycles and classes -/

section InducedMaps

variable {E F : CochainComplex (StructureSheafModules Rc) ℤ}

/-- The map induced on cohomology by a morphism of complexes sends the class of a cocycle to the
class of its image. This is `HomologicalComplex.homologyπ_naturality` read on local
sections. -/
theorem homologyMap_homologyπ_app (c : E ⟶ F) (n : ℤ) (V : (Opens ↥X)ᵒᵖ)
    (m : (E.cycles n).val.obj V) :
    (HomologicalComplex.homologyMap c n).val.app V ((E.homologyπ n).val.app V m) =
      (F.homologyπ n).val.app V ((HomologicalComplex.cyclesMap c n).val.app V m) :=
  congrArg (fun z => (_root_.SheafOfModules.Hom.val z).app V m)
    (HomologicalComplex.homologyπ_naturality c n)

/-- The image of a cocycle under the induced map on cycles is, inside the complex, its image
under the morphism of complexes. This is `HomologicalComplex.cyclesMap_i` read on local
sections. -/
theorem iCycles_cyclesMap_app (c : E ⟶ F) (n : ℤ) (V : (Opens ↥X)ᵒᵖ)
    (m : (E.cycles n).val.obj V) :
    ((F.iCycles n).val.app V) ((HomologicalComplex.cyclesMap c n).val.app V m) =
      (c.f n).val.app V (((E.iCycles n).val.app V) m) :=
  congrArg (fun z => (_root_.SheafOfModules.Hom.val z).app V m)
    (HomologicalComplex.cyclesMap_i c n)

end InducedMaps

/-- Two cocycles with the same image in the complex have the same class. -/
private theorem homologyπ_app_congr (C : CochainComplex (StructureSheafModules Rc) ℤ) (n : ℤ)
    (V : (Opens ↥X)ᵒᵖ) (m m' : (C.cycles n).val.obj V)
    (h : (C.iCycles n).val.app V m = (C.iCycles n).val.app V m') :
    (C.homologyπ n).val.app V m = (C.homologyπ n).val.app V m' :=
  congrArg _ (injective_app_of_mono (C.iCycles n) V h)

/-- `Stacks.eq_of_forall_lift` for the classes of cocycles of one complex. -/
private theorem eq_of_forall_homologyπ_lift (C : CochainComplex (StructureSheafModules Rc) ℤ)
    {Q : PresheafOfModules.{u} (structureSheaf Rc).obj}
    (hQ : Presheaf.IsSeparated (Opens.grothendieckTopology ↥X) Q.presheaf) (n : ℤ)
    {V : (Opens ↥X)ᵒᵖ} (x : ((C.homology n)).val.obj V) (u v : Q.obj V)
    (h : ∀ {W : (Opens ↥X)ᵒᵖ} (f : V ⟶ W) (m : (C.cycles n).val.obj W),
      (C.homologyπ n).val.app W m = (C.homology n).val.map f x → Q.map f u = Q.map f v) :
    u = v :=
  have : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥X)
    (C.homologyπ n).val := ImageSubsheaf.isLocallySurjective_of_epi _
  _root_.Stacks.eq_of_forall_lift hQ (C.homologyπ n).val x u v h

/-- `eq_of_forall_lift₂'` for the classes of cocycles of two complexes. -/
private theorem eq_of_forall_homologyπ_lift₂ (C D : CochainComplex (StructureSheafModules Rc) ℤ)
    {Q : PresheafOfModules.{u} (structureSheaf Rc).obj}
    (hQ : Presheaf.IsSeparated (Opens.grothendieckTopology ↥X) Q.presheaf) (i j : ℤ)
    {V : (Opens ↥X)ᵒᵖ} (x : (C.homology i).val.obj V) (y : (D.homology j).val.obj V)
    (u v : Q.obj V)
    (h : ∀ {W : (Opens ↥X)ᵒᵖ} (f : V ⟶ W) (m₁ : (C.cycles i).val.obj W)
      (m₂ : (D.cycles j).val.obj W),
      (C.homologyπ i).val.app W m₁ = (C.homology i).val.map f x →
      (D.homologyπ j).val.app W m₂ = (D.homology j).val.map f y → Q.map f u = Q.map f v) :
    u = v :=
  have : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥X)
    (C.homologyπ i).val := ImageSubsheaf.isLocallySurjective_of_epi _
  have : PresheafOfModules.IsLocallySurjective (Opens.grothendieckTopology ↥X)
    (D.homologyπ j).val := ImageSubsheaf.isLocallySurjective_of_epi _
  eq_of_forall_lift₂' Rc hQ (C.homologyπ i).val (D.homologyπ j).val x y u v h

section Comparison

variable (K I : CochainComplex (StructureSheafModules Rc) ℤ) (κ : K ⟶ I)

/-! ### The class of a morphism of complexes -/

/-- The sections of `κ` over all the objects of the site, as a global section of the degree-zero
term of `SheafHom^•(K, I)`. -/
def ofHomSections : ((homComplex Rc K I).X 0).sections :=
  PresheafOfModules.sectionsMk
    (fun U => RingedSite.ofHomSection (ringedSite Rc) κ U.unop)
    (fun {_ _} f => RingedSite.ofHomSection_restrict (ringedSite Rc) κ f.unop)

/-- `κ`, as a morphism from the unit sheaf of modules into the degree-zero term of
`SheafHom^•(K, I)`. -/
def ofHomMor : _root_.SheafOfModules.unit (structureSheaf Rc) ⟶ (homComplex Rc K I).X 0 :=
  ((homComplex Rc K I).X 0).unitHomEquiv.symm (ofHomSections Rc K I κ)

/-- On every object `U` of the site, `ofHomMor` sends the section `1` of the structure sheaf to
the section of `κ` over `U`. -/
theorem ofHomMor_val_app_one (U : (Opens ↥X)ᵒᵖ) :
    (ofHomMor Rc K I κ).val.app U (1 : (structureSheaf Rc).obj.obj U) =
      RingedSite.ofHomSection (ringedSite Rc) κ U.unop :=
  congrFun (congrArg Subtype.val
    (((homComplex Rc K I).X 0).unitHomEquiv.apply_symm_apply (ofHomSections Rc K I κ))) U

/-- The morphism named by `κ` is killed by the differential: the section of `κ` is a cocycle. -/
theorem ofHomMor_comp_d : ofHomMor Rc K I κ ≫ (homComplex Rc K I).d 0 1 = 0 := by
  refine ((homComplex Rc K I).X 1).unitHomEquiv.injective ?_
  refine PresheafOfModules.sections_ext _ _ fun U => ?_
  change ((homComplex Rc K I).d 0 1).val.app U
    ((ofHomMor Rc K I κ).val.app U (1 : (structureSheaf Rc).obj.obj U)) = _
  rw [ofHomMor_val_app_one, RingedSite.d_ofHomSection]
  rfl

/-- **The cocycle of `κ`**: `κ`, as a morphism from the unit sheaf into the degree-zero cycles of
`SheafHom^•(K, I)`. For `κ` the identity this is `Stacks.SheafOfModules.oneCycle`. -/
def ofHomCycle : _root_.SheafOfModules.unit (structureSheaf Rc) ⟶ (homComplex Rc K I).cycles 0 :=
  (homComplex Rc K I).liftCycles (ofHomMor Rc K I κ) 1 (by simp) (ofHomMor_comp_d Rc K I κ)

/-- On every object `U` of the site, the cocycle `ofHomCycle` evaluated at the section `1`,
followed by the inclusion of cycles, is the section of `κ` over `U`. -/
theorem iCycles_ofHomCycle (U : (Opens ↥X)ᵒᵖ) :
    (((homComplex Rc K I).iCycles 0).val.app U)
        ((ofHomCycle Rc K I κ).val.app U (1 : (structureSheaf Rc).obj.obj U)) =
      RingedSite.ofHomSection (ringedSite Rc) κ U.unop :=
  (congrArg (fun z => (_root_.SheafOfModules.Hom.val z).app U
      (1 : (structureSheaf Rc).obj.obj U))
    ((homComplex Rc K I).liftCycles_i (ofHomMor Rc K I κ) 1 (by simp)
      (ofHomMor_comp_d Rc K I κ))).trans (ofHomMor_val_app_one Rc K I κ U)

/-- **The class of `κ` in `H⁰(SheafHom^•(K, I))`.** For `κ` the identity this is
`Stacks.SheafOfModules.homologyOne`, the unit of the composition product. -/
def homologyClassOfHom : ((homComplex Rc K I).homology 0).sections :=
  ((homComplex Rc K I).homology 0).unitHomEquiv
    (ofHomCycle Rc K I κ ≫ (homComplex Rc K I).homologyπ 0)

/-- The class of `κ` is the class of its cocycle, on every object of the site. -/
theorem homologyClassOfHom_eval (U : (Opens ↥X)ᵒᵖ) :
    (homologyClassOfHom Rc K I κ).val U =
      (((homComplex Rc K I).homologyπ 0).val.app U)
        ((ofHomCycle Rc K I κ).val.app U (1 : (structureSheaf Rc).obj.obj U)) :=
  rfl

/-! ### The two comparison maps -/

/-- **Precomposition with `κ`**, as a morphism `SheafHom^•(I, I) ⟶ SheafHom^•(K, I)`. -/
abbrev sourceComparison : homComplex Rc I I ⟶ homComplex Rc K I :=
  RingedSite.homMap (ringedSite Rc) κ (𝟙 I)

/-- **Postcomposition with `κ`**, as a morphism `SheafHom^•(K, K) ⟶ SheafHom^•(K, I)`. -/
abbrev targetComparison : homComplex Rc K K ⟶ homComplex Rc K I :=
  RingedSite.homMap (ringedSite Rc) (𝟙 K) κ

/-- **Precomposition with `κ` absorbs a composite on the right**, on homogeneous local sections.
This is `AlgebraicGeometry.RingedSite.compositionSection_homMap` at `k = κ` and both other
morphisms the identity, which is the section-level form of
`AlgebraicGeometry.RingedSite.compositionMap_natural_source`. -/
theorem compositionSection_sourceComparison (U : Opens ↥X) (p q : ℤ)
    (β : ((homComplex Rc I I).X p).val.obj (op U))
    (γ : ((homComplex Rc I I).X q).val.obj (op U)) :
    RingedSite.compositionSection (ringedSite Rc) U p q (p + q) rfl β
        (((sourceComparison Rc K I κ).f q).val.app (op U) γ) =
      ((sourceComparison Rc K I κ).f (p + q)).val.app (op U)
        (RingedSite.compositionSection (ringedSite Rc) U p q (p + q) rfl β γ) := by
  have h := RingedSite.compositionSection_homMap (ringedSite Rc) κ (𝟙 I) (𝟙 I) U p q β γ
  rw [RingedSite.homMap_id] at h
  simpa using h

/-- **Postcomposition with `κ` absorbs a composite on the left**, on homogeneous local sections.
This is `AlgebraicGeometry.RingedSite.compositionSection_homMap` at `m = κ` and both other
morphisms the identity, which is the section-level form of
`AlgebraicGeometry.RingedSite.compositionMap_natural_target`. -/
theorem compositionSection_targetComparison (U : Opens ↥X) (p q : ℤ)
    (β : ((homComplex Rc K K).X p).val.obj (op U))
    (γ : ((homComplex Rc K K).X q).val.obj (op U)) :
    RingedSite.compositionSection (ringedSite Rc) U p q (p + q) rfl
        (((targetComparison Rc K I κ).f p).val.app (op U) β) γ =
      ((targetComparison Rc K I κ).f (p + q)).val.app (op U)
        (RingedSite.compositionSection (ringedSite Rc) U p q (p + q) rfl β γ) := by
  have h := RingedSite.compositionSection_homMap (ringedSite Rc) (𝟙 K) (𝟙 K) κ U p q β γ
  rw [RingedSite.homMap_id] at h
  simpa using h

/-! ### Multiplicativity -/

/-- **Precomposition with `κ` is a map of left modules, on classes of cocycles.** -/
theorem homologyMap_sourceComparison_homologyMul_of_cycles (i j : ℤ) (W : Opens ↥X)
    (m₁ : ((homComplex Rc I I).cycles i).val.obj (op W))
    (m₂ : ((homComplex Rc I I).cycles j).val.obj (op W)) :
    (HomologicalComplex.homologyMap (sourceComparison Rc K I κ) (i + j)).val.app (op W)
        ((homologyMul Rc I I I i j).app (op W)
          (((homComplex Rc I I).homologyπ i).val.app (op W) m₁)
          (((homComplex Rc I I).homologyπ j).val.app (op W) m₂)) =
      (homologyMul Rc K I I i j).app (op W)
        (((homComplex Rc I I).homologyπ i).val.app (op W) m₁)
        ((HomologicalComplex.homologyMap (sourceComparison Rc K I κ) j).val.app (op W)
          (((homComplex Rc I I).homologyπ j).val.app (op W) m₂)) := by
  rw [homologyMul_app_homologyπ, homologyMap_homologyπ_app, homologyMap_homologyπ_app,
    homologyMul_app_homologyπ]
  refine homologyπ_app_congr Rc _ _ _ _ _ ?_
  rw [iCycles_cyclesMap_app, iCycles_cycleComposition_pureSection,
    iCycles_cycleComposition_pureSection, iCycles_cyclesMap_app,
    compositionSection_sourceComparison]

/-- **Postcomposition with `κ` is a map of right modules, on classes of cocycles.** -/
theorem homologyMap_targetComparison_homologyMul_of_cycles (i j : ℤ) (W : Opens ↥X)
    (m₁ : ((homComplex Rc K K).cycles i).val.obj (op W))
    (m₂ : ((homComplex Rc K K).cycles j).val.obj (op W)) :
    (HomologicalComplex.homologyMap (targetComparison Rc K I κ) (i + j)).val.app (op W)
        ((homologyMul Rc K K K i j).app (op W)
          (((homComplex Rc K K).homologyπ i).val.app (op W) m₁)
          (((homComplex Rc K K).homologyπ j).val.app (op W) m₂)) =
      (homologyMul Rc K K I i j).app (op W)
        ((HomologicalComplex.homologyMap (targetComparison Rc K I κ) i).val.app (op W)
          (((homComplex Rc K K).homologyπ i).val.app (op W) m₁))
        (((homComplex Rc K K).homologyπ j).val.app (op W) m₂) := by
  rw [homologyMul_app_homologyπ, homologyMap_homologyπ_app, homologyMap_homologyπ_app,
    homologyMul_app_homologyπ]
  refine homologyπ_app_congr Rc _ _ _ _ _ ?_
  rw [iCycles_cyclesMap_app, iCycles_cycleComposition_pureSection,
    iCycles_cycleComposition_pureSection, iCycles_cyclesMap_app,
    compositionSection_targetComparison]

/-- **Precomposition with `κ` is a map of left modules** over the composition product on
`H^*(SheafHom^•(I, I))`:

`cmp(a · b) = a · cmp(b)` for `a, b` classes in `H^*(SheafHom^•(I, I))`.

This is the cohomology transport of
`AlgebraicGeometry.RingedSite.compositionMap_natural_source`. The two cohomology sections are
lifted to cocycles simultaneously on a common refinement -- `homologyπ` is an epimorphism, hence
locally surjective, and `eq_of_forall_lift₂'` intersects the two resulting covering sieves -- and
on those lifts the identity is `homologyMap_sourceComparison_homologyMul_of_cycles`. -/
theorem homologyMap_sourceComparison_homologyMul (i j : ℤ) (V : (Opens ↥X)ᵒᵖ)
    (x : ((homComplex Rc I I).homology i).val.obj V)
    (y : ((homComplex Rc I I).homology j).val.obj V) :
    (HomologicalComplex.homologyMap (sourceComparison Rc K I κ) (i + j)).val.app V
        ((homologyMul Rc I I I i j).app V x y) =
      (homologyMul Rc K I I i j).app V x
        ((HomologicalComplex.homologyMap (sourceComparison Rc K I κ) j).val.app V y) := by
  refine eq_of_forall_homologyπ_lift₂ Rc _ _
    (((homComplex Rc K I).homology (i + j)).isSheaf.isSeparated) i j x y _ _ ?_
  intro W f m₁ m₂ hm₁ hm₂
  rw [← PresheafOfModules.naturality_apply, _root_.Stacks.BilinearMap.naturality,
    _root_.Stacks.BilinearMap.naturality, ← PresheafOfModules.naturality_apply, ← hm₁, ← hm₂]
  exact homologyMap_sourceComparison_homologyMul_of_cycles Rc K I κ i j W.unop m₁ m₂

/-- **Postcomposition with `κ` is a map of right modules** over the composition product on
`H^*(SheafHom^•(K, K))`:

`cmp(a · b) = cmp(a) · b` for `a, b` classes in `H^*(SheafHom^•(K, K))`.

This is the cohomology transport of
`AlgebraicGeometry.RingedSite.compositionMap_natural_target`, by the same descent as
`homologyMap_sourceComparison_homologyMul`. -/
theorem homologyMap_targetComparison_homologyMul (i j : ℤ) (V : (Opens ↥X)ᵒᵖ)
    (x : ((homComplex Rc K K).homology i).val.obj V)
    (y : ((homComplex Rc K K).homology j).val.obj V) :
    (HomologicalComplex.homologyMap (targetComparison Rc K I κ) (i + j)).val.app V
        ((homologyMul Rc K K K i j).app V x y) =
      (homologyMul Rc K K I i j).app V
        ((HomologicalComplex.homologyMap (targetComparison Rc K I κ) i).val.app V x) y := by
  refine eq_of_forall_homologyπ_lift₂ Rc _ _
    (((homComplex Rc K I).homology (i + j)).isSheaf.isSeparated) i j x y _ _ ?_
  intro W f m₁ m₂ hm₁ hm₂
  rw [← PresheafOfModules.naturality_apply, _root_.Stacks.BilinearMap.naturality,
    _root_.Stacks.BilinearMap.naturality, ← PresheafOfModules.naturality_apply, ← hm₁, ← hm₂]
  exact homologyMap_targetComparison_homologyMul_of_cycles Rc K I κ i j W.unop m₁ m₂

/-! ### Unitality -/

/-- **Precomposition with `κ` sends the unit to the class of `κ`.** -/
theorem homologyMap_sourceComparison_homologyOne (V : (Opens ↥X)ᵒᵖ) :
    (HomologicalComplex.homologyMap (sourceComparison Rc K I κ) 0).val.app V
        ((homologyOne Rc I).val V) = (homologyClassOfHom Rc K I κ).val V := by
  rw [homologyOne_eval, homologyMap_homologyπ_app, homologyClassOfHom_eval]
  refine homologyπ_app_congr Rc _ _ _ _ _ ?_
  rw [iCycles_cyclesMap_app, iCycles_oneCycle, iCycles_ofHomCycle]
  exact RingedSite.homMap_idSection_precomp (ringedSite Rc) κ V.unop

/-- **Postcomposition with `κ` sends the unit to the class of `κ`.** -/
theorem homologyMap_targetComparison_homologyOne (V : (Opens ↥X)ᵒᵖ) :
    (HomologicalComplex.homologyMap (targetComparison Rc K I κ) 0).val.app V
        ((homologyOne Rc K).val V) = (homologyClassOfHom Rc K I κ).val V := by
  rw [homologyOne_eval, homologyMap_homologyπ_app, homologyClassOfHom_eval]
  refine homologyπ_app_congr Rc _ _ _ _ _ ?_
  rw [iCycles_cyclesMap_app, iCycles_oneCycle, iCycles_ofHomCycle]
  exact RingedSite.homMap_idSection_postcomp (ringedSite Rc) κ V.unop

/-! ### Each comparison map is multiplication by the class of `κ` -/

/-- **Right multiplication by the class of `κ` is precomposition with `κ`**, on a class of
cocycles. -/
theorem homologyMul_homologyClassOfHom_of_cycles (i : ℤ) (W : Opens ↥X)
    (m : ((homComplex Rc I I).cycles i).val.obj (op W)) :
    _root_.SheafOfModules.castHom
        (fun d => (homComplex Rc K I).homology d) (add_zero i) (op W)
        ((homologyMul Rc K I I i 0).app (op W)
          (((homComplex Rc I I).homologyπ i).val.app (op W) m)
          ((homologyClassOfHom Rc K I κ).val (op W))) =
      (HomologicalComplex.homologyMap (sourceComparison Rc K I κ) i).val.app (op W)
        (((homComplex Rc I I).homologyπ i).val.app (op W) m) := by
  rw [homologyClassOfHom_eval, homologyMul_app_homologyπ, castHom_homologyπ,
    homologyMap_homologyπ_app]
  refine congrArg (fun w => ((homComplex Rc K I).homologyπ i).val.app (op W) w) ?_
  refine injective_app_of_mono ((homComplex Rc K I).iCycles i) (op W) ?_
  rw [castHom_iCycles, iCycles_cycleComposition_pureSection, iCycles_ofHomCycle,
    castHom_compositionSection Rc K I I i 0 (i + 0) i rfl (add_zero i) (add_zero i) W,
    iCycles_cyclesMap_app]
  exact RingedSite.compositionSection_ofHomSection (ringedSite Rc) κ I W i _

/-- **Left multiplication by the class of `κ` is postcomposition with `κ`**, on a class of
cocycles. -/
theorem homologyClassOfHom_homologyMul_of_cycles (j : ℤ) (W : Opens ↥X)
    (m : ((homComplex Rc K K).cycles j).val.obj (op W)) :
    _root_.SheafOfModules.castHom
        (fun d => (homComplex Rc K I).homology d) (zero_add j) (op W)
        ((homologyMul Rc K K I 0 j).app (op W)
          ((homologyClassOfHom Rc K I κ).val (op W))
          (((homComplex Rc K K).homologyπ j).val.app (op W) m)) =
      (HomologicalComplex.homologyMap (targetComparison Rc K I κ) j).val.app (op W)
        (((homComplex Rc K K).homologyπ j).val.app (op W) m) := by
  rw [homologyClassOfHom_eval, homologyMul_app_homologyπ, castHom_homologyπ,
    homologyMap_homologyπ_app]
  refine congrArg (fun w => ((homComplex Rc K I).homologyπ j).val.app (op W) w) ?_
  refine injective_app_of_mono ((homComplex Rc K I).iCycles j) (op W) ?_
  rw [castHom_iCycles, iCycles_cycleComposition_pureSection, iCycles_ofHomCycle,
    castHom_compositionSection Rc K K I 0 j (0 + j) j rfl (zero_add j) (zero_add j) W,
    iCycles_cyclesMap_app]
  exact RingedSite.ofHomSection_compositionSection (ringedSite Rc) κ K W j _

/-- **Right multiplication by the class of `κ` is precomposition with `κ`.** Together with
`homologyMap_sourceComparison_homologyMul` this is what makes the comparison of the two models
multiplicative and not merely a map of modules. -/
theorem homologyMul_homologyClassOfHom (i : ℤ) (V : (Opens ↥X)ᵒᵖ)
    (x : ((homComplex Rc I I).homology i).val.obj V) :
    _root_.SheafOfModules.castHom
        (fun d => (homComplex Rc K I).homology d) (add_zero i) V
        ((homologyMul Rc K I I i 0).app V x ((homologyClassOfHom Rc K I κ).val V)) =
      (HomologicalComplex.homologyMap (sourceComparison Rc K I κ) i).val.app V x := by
  refine eq_of_forall_homologyπ_lift Rc _
    (((homComplex Rc K I).homology i).isSheaf.isSeparated) i x _ _ ?_
  intro W f m hm
  refine (castHom_map Rc (fun d => (homComplex Rc K I).homology d) (add_zero i) f _).trans
    ((congrArg (fun w => _root_.SheafOfModules.castHom
        (fun d => (homComplex Rc K I).homology d) (add_zero i) W w)
      ((homologyMul Rc K I I i 0).naturality f x
        ((homologyClassOfHom Rc K I κ).val V))).trans ?_)
  rw [PresheafOfModules.sections_property (homologyClassOfHom Rc K I κ) f,
    ← PresheafOfModules.naturality_apply, ← hm]
  exact homologyMul_homologyClassOfHom_of_cycles Rc K I κ i W.unop m

/-- **Left multiplication by the class of `κ` is postcomposition with `κ`.** Together with
`homologyMap_targetComparison_homologyMul` this is what makes the comparison of the two models
multiplicative and not merely a map of modules. -/
theorem homologyClassOfHom_homologyMul (j : ℤ) (V : (Opens ↥X)ᵒᵖ)
    (y : ((homComplex Rc K K).homology j).val.obj V) :
    _root_.SheafOfModules.castHom
        (fun d => (homComplex Rc K I).homology d) (zero_add j) V
        ((homologyMul Rc K K I 0 j).app V ((homologyClassOfHom Rc K I κ).val V) y) =
      (HomologicalComplex.homologyMap (targetComparison Rc K I κ) j).val.app V y := by
  refine eq_of_forall_homologyπ_lift Rc _
    (((homComplex Rc K I).homology j).isSheaf.isSeparated) j y _ _ ?_
  intro W f m hm
  refine (castHom_map Rc (fun d => (homComplex Rc K I).homology d) (zero_add j) f _).trans
    ((congrArg (fun w => _root_.SheafOfModules.castHom
        (fun d => (homComplex Rc K I).homology d) (zero_add j) W w)
      ((homologyMul Rc K K I 0 j).naturality f
        ((homologyClassOfHom Rc K I κ).val V) y)).trans ?_)
  rw [PresheafOfModules.sections_property (homologyClassOfHom Rc K I κ) f,
    ← PresheafOfModules.naturality_apply, ← hm]
  exact homologyClassOfHom_homologyMul_of_cycles Rc K I κ j W.unop m

/-! ### Quasi-isomorphy of the two comparison maps -/

/-- **Precomposition with a quasi-isomorphism into a K-injective complex is a
quasi-isomorphism.** This is Stacks 0A95, `AlgebraicGeometry.RingedSite.homMap_quasiIso`, at
`i = 𝟙 I`: the covariant variable is the identity of `I`, a quasi-isomorphism between K-injective
complexes, and the contravariant variable is `κ`. Only K-injectivity of `I` is used; `K` is
arbitrary. -/
theorem quasiIso_sourceComparison [QuasiIso κ] [I.IsKInjective] :
    QuasiIso (sourceComparison Rc K I κ) :=
  RingedSite.homMap_quasiIso (ringedSite Rc) (𝟙 I) κ

/-- **Postcomposition with a quasi-isomorphism is a quasi-isomorphism when the source is
strictly perfect.** This is Stacks 08JH,
`AlgebraicGeometry.RingedSite.homMap_quasiIso_of_isFiniteFreeSummand`, at `E = K`: the internal
Hom complex out of a complex with finitely many nonzero terms, each a direct summand of a finite
free `O_X`-module, carries a quasi-isomorphism of targets to a quasi-isomorphism. Nothing is
asked of `I`. -/
theorem quasiIso_targetComparison [QuasiIso κ]
    (hbdd : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (hterm : ∀ i, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (K.X i)) :
    QuasiIso (targetComparison Rc K I κ) :=
  RingedSite.homMap_quasiIso_of_isFiniteFreeSummand (ringedSite Rc) κ K hbdd hterm

/-- **Both comparison maps are isomorphisms on cohomology sheaves in every degree**, for a
quasi-isomorphism `κ : K ⟶ I` from a strictly perfect complex into a K-injective one. Together
with `homologyMap_sourceComparison_homologyMul`,
`homologyMap_targetComparison_homologyMul` and the two unit identities this is the model
independence of the composition product: each side acts on `H^*(SheafHom^•(K, I))` through an
isomorphism, unitally and multiplicatively. -/
theorem isIso_homologyMap_comparison [QuasiIso κ] [I.IsKInjective]
    (hbdd : {i : ℤ | ¬ IsZero (K.X i)}.Finite)
    (hterm : ∀ i, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (K.X i)) (n : ℤ) :
    IsIso (HomologicalComplex.homologyMap (sourceComparison Rc K I κ) n) ∧
      IsIso (HomologicalComplex.homologyMap (targetComparison Rc K I κ) n) := by
  haveI := quasiIso_sourceComparison Rc K I κ
  haveI := quasiIso_targetComparison Rc K I κ hbdd hterm
  exact ⟨inferInstance, inferInstance⟩

end Comparison

end Stacks.SheafOfModules

end
