module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.ComparisonDiagram
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.MilnorSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationLocality
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.RlimBasic
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleInjectiveComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimitHomologySequence
public import Mathlib.CategoryTheory.Abelian.RightDerived
import StacksCore.Tactic.StacksAttribute

/-! # Cohomology of a derived inverse limit over an acyclic covering family

Let `(C, O)` be a ringed site, `(Kₙ)` an inverse system in the unbounded derived category of
`O`-modules with derived limit `L`, and `B` a family of objects of `C` covering every object of
`C`. If every cohomology sheaf `Hᵖ(Kₙ)` has vanishing higher cohomology over the members of `B`,
and the inverse systems of their sections over the members of `B` have vanishing `R¹lim`, then
`Hᵖ(L) = lim Hᵖ(Kₙ)`. This is Tag 0A09.

The proof follows the source. Over a member `U` of `B` the hypercohomology `Hᵖ(U, Kₙ)` is the
module of sections of `Hᵖ(Kₙ)` over `U`, which is Tag 0BKZ; the Milnor sequence of Tag 0BKX then
computes `Hᵖ(U, L)` as `lim Hᵖ(U, Kₙ)`, its `R¹lim` term vanishing by hypothesis. So the
comparison of cohomology presheaves is invertible on sections over every member of `B`, hence
invertible after sheafification, and the commuting square of Tag 0BKW transports that to the
comparison of cohomology sheaves.

Tag 0BKZ enters here as the explicit hypothesis `h0BKZ` of
`Stacks.Cohomology.DerivedLimitAcyclic.cohomology_isLimit_of_isDerivedLimit_of_acyclic_cover`,
which is the only input these results take beyond the hypotheses of Tag 0A09 itself. It is
discharged by
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover`, and Tag
0A09 itself is therefore stated and proved in
`StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.CohomologyCommutesWithDerivedLimit`.

## Main definitions

* `Stacks.Cohomology.DerivedLimitAcyclic.cokernelInverseSystemDifferenceIso`,
  `Stacks.Cohomology.DerivedLimitAcyclic.mapCokernelInverseSystemDifferenceIso`: transport of the
  cokernel of `Stacks.DerivedLimit.inverseSystemDifference` -- the presentation of `R¹lim` -- along
  an isomorphism of systems, and along a functor preserving countable products and finite colimits.
* `Stacks.Cohomology.DerivedLimitAcyclic.cohomologyPresheafComparison`: the comparison from the
  degree-`q` cohomology presheaf to the underlying presheaf of the degree-`q` cohomology sheaf.
* `Stacks.Cohomology.DerivedLimitAcyclic.limitComparisonPresheaf`: the comparison from the
  degree-`q` cohomology presheaf of the derived limit to the underlying presheaf of the inverse
  limit of the degree-`q` cohomology sheaves.

## Main results

* `Stacks.Cohomology.DerivedLimitAcyclic.isIso_evaluation_cohomologyPresheafComparison`: sections
  over `U` of the sheafification comparison are invertible wherever the hypercohomology edge
  morphism over `U` is -- the two differ by the isomorphism of Tag 0BKV.
* `Stacks.Cohomology.DerivedLimitAcyclic.isZero_cokernel_difference_hypercohomologySystem`: the
  `R¹lim` term of the Milnor sequence vanishes, transported across the edge morphisms from the
  hypothesis of Tag 0A09 about sections of the cohomology sheaves.
* `Stacks.Cohomology.DerivedLimitAcyclic.isIso_cohomologyLimitComparison`: the comparison from
  the degree-`q` cohomology sheaf of the derived limit to the inverse limit of the degree-`q`
  cohomology sheaves is an isomorphism. This is the content of Tag 0A09, and it exhibits the
  limit cone rather than merely asserting that one exists.
* `Stacks.Cohomology.DerivedLimitAcyclic.cohomology_isLimit_of_isDerivedLimit_of_acyclic_cover`:
  Tag 0A09 with Tag 0BKZ taken as the hypothesis `h0BKZ`; discharging it is
  `Stacks.Cohomology.DerivedLimitAcyclic.isLimit_cohomology_of_isDerivedLimit_of_acyclic_cover`.

## Implementation notes

The hypothesis of Tag 0A09 on first derived inverse limits is about sections of the cohomology
*sheaves*, with values in abelian groups, while the Milnor sequence available here is about
*hypercohomology*, with values in modules over the ring of sections. The two are matched by
the two cokernel-transport isomorphisms above, applied to
`Stacks.DerivedLimit.inverseSystemDifference`: across the edge morphisms as an isomorphism of
systems, and across the forgetful functor from modules to abelian groups. The target of the
Milnor sequence is `Rlim.firstDerivedLimit`'s cokernel presentation by
`Rlim.delta_eq_lift`.

The universes of the site, its morphisms, the structure ring and the modules all coincide, as in
the tagged statement; the general lemmas of the first two sections are universe-polymorphic, and
`cohomologyPresheafComparison` carries independent ring and module universes, as the
hypercohomology edge morphism does.

## References

* [Stacks Project, Tag 0A09](https://stacks.math.columbia.edu/tag/0A09)
* [Stacks Project, Tag 0BKW](https://stacks.math.columbia.edu/tag/0BKW)
* [Stacks Project, Tag 0BKX](https://stacks.math.columbia.edu/tag/0BKX)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open AlgebraicGeometry

namespace Stacks.Cohomology.DerivedLimitAcyclic

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.HypercohomologyEdge
open Stacks.DerivedLimit

attribute [local instance] evaluation_additive

section Difference

variable {D : Type*} [Category* D] [Abelian D] [HasProductsOfShape ℕ D]
  {D' : Type*} [Category* D'] [Abelian D'] [HasProductsOfShape ℕ D']

/-- An isomorphism of sequential inverse systems commutes with the difference maps `1 - shift`
whose cokernels present the first derived inverse limit. -/
lemma inverseSystemDifference_comm {F G : ℕᵒᵖ ⥤ D} (e : F ≅ G) :
    inverseSystemDifference F ≫ (Pi.mapIso fun n : ℕ ↦ e.app ⟨n⟩).hom =
      (Pi.mapIso fun n : ℕ ↦ e.app ⟨n⟩).hom ≫ inverseSystemDifference G := by
  refine Pi.hom_ext _ _ fun n ↦ ?_
  have hπ : ∀ m : ℕ, (Pi.mapIso fun i : ℕ ↦ e.app (⟨i⟩ : ℕᵒᵖ)).hom ≫
      Pi.π (fun i : ℕ ↦ G.obj ⟨i⟩) m =
        Pi.π (fun i : ℕ ↦ F.obj ⟨i⟩) m ≫ e.hom.app ⟨m⟩ := fun m ↦ by
    simp [Pi.mapIso_hom_π]
  have hL : (inverseSystemDifference F ≫ (Pi.mapIso fun i : ℕ ↦ e.app (⟨i⟩ : ℕᵒᵖ)).hom) ≫
      Pi.π (fun i : ℕ ↦ G.obj ⟨i⟩) n =
        Pi.π (fun i : ℕ ↦ F.obj ⟨i⟩) n ≫ e.hom.app ⟨n⟩ -
          Pi.π (fun i : ℕ ↦ F.obj ⟨i⟩) (n + 1) ≫ e.hom.app ⟨n + 1⟩ ≫
            G.map (homOfLE (Nat.le_succ n)).op := by
    rw [Category.assoc, hπ n, ← Category.assoc, inverseSystemDifference_comp_π,
      Preadditive.sub_comp, Category.assoc, e.hom.naturality (homOfLE (Nat.le_succ n)).op]
  have hR : ((Pi.mapIso fun i : ℕ ↦ e.app (⟨i⟩ : ℕᵒᵖ)).hom ≫ inverseSystemDifference G) ≫
      Pi.π (fun i : ℕ ↦ G.obj ⟨i⟩) n =
        Pi.π (fun i : ℕ ↦ F.obj ⟨i⟩) n ≫ e.hom.app ⟨n⟩ -
          Pi.π (fun i : ℕ ↦ F.obj ⟨i⟩) (n + 1) ≫ e.hom.app ⟨n + 1⟩ ≫
            G.map (homOfLE (Nat.le_succ n)).op := by
    rw [Category.assoc, inverseSystemDifference_comp_π, Preadditive.comp_sub, hπ n,
      ← Category.assoc, hπ (n + 1), Category.assoc]
  exact hL.trans hR.symm

/-- The cokernels of the difference maps of two isomorphic sequential inverse systems agree, so
an isomorphism of systems identifies their first derived inverse limits. -/
def cokernelInverseSystemDifferenceIso {F G : ℕᵒᵖ ⥤ D} (e : F ≅ G) :
    cokernel (inverseSystemDifference F) ≅ cokernel (inverseSystemDifference G) :=
  cokernel.mapIso _ _ (Pi.mapIso fun n : ℕ ↦ e.app ⟨n⟩)
    (Pi.mapIso fun n : ℕ ↦ e.app ⟨n⟩) (inverseSystemDifference_comm e)

/-- An additive functor preserving countable products and finite colimits carries the cokernel of
the difference map of a system to the cokernel of the difference map of the image system, so it
carries the first derived inverse limit to that of the image system. -/
def mapCokernelInverseSystemDifferenceIso (F : ℕᵒᵖ ⥤ D) (E : D ⥤ D') [E.Additive]
    [PreservesLimitsOfShape (Discrete ℕ) E] [PreservesFiniteColimits E] :
    E.obj (cokernel (inverseSystemDifference F)) ≅
      cokernel (inverseSystemDifference (F ⋙ E)) :=
  PreservesCokernel.iso E (inverseSystemDifference F) ≪≫
    cokernel.mapIso _ _ (PreservesProduct.iso E fun n : ℕ ↦ F.obj ⟨n⟩)
      (PreservesProduct.iso E fun n : ℕ ↦ F.obj ⟨n⟩) (by
        rw [PreservesProduct.iso_hom]
        exact map_inverseSystemDifference_comp_piComparison E F)

end Difference

section Adjunction

variable {P' : Type*} [Category* P'] {A' : Type*} [Category* A']
  {L' : P' ⥤ A'} {R' : A' ⥤ P'}

/-- A left adjoint carries a component of the unit to an isomorphism whenever the counit is
invertible there: the left triangle identity exhibits it as a factor of an identity whose other
factor is invertible. -/
lemma isIso_map_unit_app (adj : L' ⊣ R') (Y : P')
    (h : IsIso (adj.counit.app (L'.obj Y))) : IsIso (L'.map (adj.unit.app Y)) := by
  have hid : L'.map (adj.unit.app Y) ≫ adj.counit.app (L'.obj Y) = 𝟙 _ :=
    adj.left_triangle_components Y
  have : IsIso (L'.map (adj.unit.app Y) ≫ adj.counit.app (L'.obj Y)) := by
    rw [hid]; infer_instance
  exact IsIso.of_isIso_comp_right _ (adj.counit.app (L'.obj Y))

end Adjunction

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing})
  [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]

/-- The comparison from the degree-`q` cohomology presheaf of `K` to the underlying presheaf of
its degree-`q` cohomology sheaf: the unit of sheafification followed by the Tag 0BKV
identification of the sheafified cohomology presheaf with the cohomology sheaf.

Unlike `Stacks.Cohomology.HypercohomologyEdge.hypercohomologyEdge` this is not read on sections
over one object, so it can be sheafified; `isIso_evaluation_cohomologyPresheafComparison` is what
connects the two. -/
def cohomologyPresheafComparison (q : ℤ) :
    derivedSectionsPresheaf O ⋙
        DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q ⟶
      DerivedCategory.homologyFunctor (SheafOfModules.{wModule} O) q ⋙
        SheafOfModules.forget O :=
  Functor.whiskerLeft (derivedSectionsPresheaf O ⋙
      DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q)
    (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).unit ≫
  Functor.whiskerRight (sheafificationCohomologyPresheafIso O q).hom (SheafOfModules.forget O)

/-- The two factors of `cohomologyPresheafComparison` at a derived object. -/
lemma cohomologyPresheafComparison_app (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) :
    (cohomologyPresheafComparison O q).app K =
      (PresheafOfModules.sheafificationAdjunction (𝟙 O.obj)).unit.app
          ((derivedSectionsPresheaf O ⋙
            DerivedCategory.homologyFunctor (PresheafOfModules.{wModule} O.obj) q).obj K) ≫
        (SheafOfModules.forget O).map
          ((sheafificationCohomologyPresheafIso O q).hom.app K) :=
  rfl

/-- Sections over `U` of the comparison `cohomologyPresheafComparison` are the hypercohomology
edge morphism, up to the isomorphism identifying the sections of the cohomology presheaf with
hypercohomology. -/
lemma evaluation_map_cohomologyPresheafComparison_app (U : C) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{wModule} O)) :
    (PresheafOfModules.evaluation O.obj (op U)).map
        ((cohomologyPresheafComparison O q).app K) =
      (sectionsEvaluationIso O U q).hom.app K ≫ (hypercohomologyEdge O U q).app K := by
  rw [hypercohomologyEdge_app, ← Category.assoc, Iso.hom_inv_id_app, Category.id_comp,
    cohomologyPresheafUnit_app]
  exact (PresheafOfModules.evaluation O.obj (op U)).map_comp _ _

/-- Where the hypercohomology edge morphism at `K` is invertible, so is the sheafification
comparison on the degree-`q` cohomology presheaf, read on sections over the same object. -/
lemma isIso_evaluation_cohomologyPresheafComparison (U : C) (q : ℤ)
    (K : DerivedCategory (SheafOfModules.{wModule} O))
    (hK : IsIso ((hypercohomologyEdge O U q).app K)) :
    IsIso ((PresheafOfModules.evaluation O.obj (op U)).map
      ((cohomologyPresheafComparison O q).app K)) := by
  rw [evaluation_map_cohomologyPresheafComparison_app]
  exact IsIso.comp_isIso' inferInstance hK

section RingedSite

open Stacks.Cohomology.Localization

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [IsGrothendieckAbelian.{g} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]

/-- The system of degree-`q` hypercohomology modules over `U` of an inverse system of objects
of the derived category of `O`-modules. -/
abbrev hypercohomologySystem (U : X.C)
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (q : ℤ) :
    ℕᵒᵖ ⥤ ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) :=
  K ⋙ derivedSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U ⋙
    DerivedCategory.homologyFunctor
      (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) q

/-- Where the hypercohomology edge morphism is invertible at every term of the system, the
vanishing of the first derived inverse limit of the sections of the cohomology sheaves transfers
to the vanishing of the cokernel of the difference map on hypercohomology.

This is what feeds the Milnor sequence of Tag 0BKX: that sequence presents `R¹lim` of the
hypercohomology system as this cokernel, so the hypothesis of Tag 0A09, which is about sections
of the cohomology sheaves, reaches it only across the edge morphism. -/
lemma isZero_cokernel_difference_hypercohomologySystem (U : X.C)
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (q : ℤ)
    (hedge : ∀ n : ℕ,
      IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U q).app
        (K.obj ⟨n⟩)))
    (hlimOne : IsZero (Rlim.firstDerivedLimit
      (K ⋙ DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q ⋙
        sectionsOverObject X U))) :
    IsZero (cokernel (inverseSystemDifference (hypercohomologySystem X U K q))) := by
  let G := forget₂ (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)))
    AddCommGrpCat.{u}
  let A := K ⋙ DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q ⋙
    sectionsOverObject X U
  let α := Functor.whiskerLeft K
    (Functor.whiskerRight (hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U q) G)
  have hα (n : ℕᵒᵖ) : IsIso (α.app n) := by
    have := hedge n.unop
    dsimp only [α, Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  let e : hypercohomologySystem X U K q ⋙ G ≅ A :=
    NatIso.ofComponents (fun n ↦ have := hα n; asIso (α.app n)) fun f ↦ α.naturality f
  have hdelta : inverseSystemDifference A = Rlim.delta A := (Rlim.delta_eq_lift A).symm
  have hzero :
      IsZero (G.obj (cokernel (inverseSystemDifference (hypercohomologySystem X U K q)))) :=
    hlimOne.of_iso (mapCokernelInverseSystemDifferenceIso (hypercohomologySystem X U K q) G ≪≫
      cokernelInverseSystemDifferenceIso e ≪≫ cokernelIsoOfEq hdelta)
  refine (IsZero.iff_id_eq_zero _).2 (G.map_injective ?_)
  rw [G.map_id, G.map_zero]
  exact (IsZero.iff_id_eq_zero _).1 hzero

/-- Sections over `U` of the comparison from the degree-`q` cohomology presheaf of a derived
limit to the limit of the degree-`q` cohomology presheaves of the system is invertible, as soon
as the hypercohomology edge morphisms in degree `q - 1` are and the first derived inverse limit
of the degree-`(q-1)` sections vanishes.

The Milnor sequence of Tag 0BKX identifies these sections with the limit of the hypercohomology
modules up to the `R¹lim` term, and that term is the cokernel killed by
`isZero_cokernel_difference_hypercohomologySystem`. -/
lemma isIso_evaluation_cohomologyLimitMap (U : X.C)
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (q : ℤ)
    (hedge : ∀ n : ℕ,
      IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U (q - 1)).app
        (K.obj ⟨n⟩)))
    (hlimOne : IsZero (Rlim.firstDerivedLimit
      (K ⋙ DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (q - 1) ⋙
        sectionsOverObject X U)))
    (a : (derivedSectionsPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q).obj L ⟶
      limit (K ⋙ derivedSectionsPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q))
    (ha : ∀ n : ℕ, a ≫ limit.π _ ⟨n⟩ =
      (derivedSectionsPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
        DerivedCategory.homologyFunctor
          (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q).map
          (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) :
    IsIso ((PresheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)).map a) := by
  let RG := derivedSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  let P := derivedSectionsPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    DerivedCategory.homologyFunctor
      (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q
  let E := PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)
  let H := DerivedCategory.homologyFunctor
    (ModuleCat.{u} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) q
  obtain ⟨hprod, ar, br, htr, har, ep, i, r, hz, hep, hi, hseq, hr⟩ :=
    exists_milnor_shortExact_derivedSections (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U K L p
      hp q
  have : IsIso r := hseq.isIso_g_iff.mpr
    (isZero_cokernel_difference_hypercohomologySystem X U K (q - 1) hedge hlimOne)
  let e := sectionsEvaluationIso (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U q
  let eK : (K ⋙ P) ⋙ E ≅ (K ⋙ RG) ⋙ H := Functor.isoWhiskerLeft K e
  let t : E.obj (limit (K ⋙ P)) ≅ limit ((K ⋙ RG) ⋙ H) :=
    preservesLimitIso E (K ⋙ P) ≪≫ HasLimit.isoOfNatIso eK
  have ht : E.map a ≫ t.hom = e.hom.app L ≫ r := by
    refine limit.hom_ext fun n ↦ ?_
    obtain ⟨n⟩ := n
    simp only [t, Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π,
      preservesLimitIso_hom_π_assoc]
    rw [← Category.assoc, ← E.map_comp, ha n, hr n]
    exact e.hom.naturality (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)
  have : IsIso (E.map a ≫ t.hom) := by rw [ht]; infer_instance
  exact IsIso.of_isIso_comp_right (E.map a) t.hom

/-- The degree-`q` cohomology presheaf functor: the degree-`q` cohomology of derived sections
taken over every object of the site at once. -/
abbrev cohomologyPresheafFunctor (q : ℤ) :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj :=
  derivedSectionsPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⋙
    DerivedCategory.homologyFunctor
      (PresheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj) q

/-- The comparison from the degree-`q` cohomology presheaf of a derived limit to the underlying
presheaf of the inverse limit of the degree-`q` cohomology sheaves, assembled from a cone map `a`
into the limit of the cohomology presheaves and the sheafification comparison. -/
def limitComparisonPresheaf
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (q : ℤ)
    (a : (cohomologyPresheafFunctor X q).obj L ⟶ limit (K ⋙ cohomologyPresheafFunctor X q)) :
    (cohomologyPresheafFunctor X q).obj L ⟶
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).obj
        (limit (K ⋙ DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q)) :=
  a ≫ limMap (Functor.whiskerLeft K
      (cohomologyPresheafComparison (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q) :
      K ⋙ cohomologyPresheafFunctor X q ⟶
        (K ⋙ DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q) ⋙
          SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ≫
    (preservesLimitIso (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (K ⋙ DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q)).inv

/-- Sections over a member of the covering collection of the comparison
`limitComparisonPresheaf` are invertible. All three of its factors are: the cone map by the
Milnor sequence, the sheafification comparison by Tag 0BKZ, and the product comparison because
the forgetful functor preserves limits. -/
theorem isIso_evaluation_limitComparisonPresheaf
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (B : ObjectProperty X.C)
    (hedge : ∀ U, B U → ∀ (m : ℤ) (n : ℕ),
      IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U m).app
        (K.obj ⟨n⟩)))
    (hlimOne : ∀ U, B U → ∀ m : ℤ,
      IsZero (Rlim.firstDerivedLimit
        (K ⋙ DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m ⋙
          sectionsOverObject X U)))
    (q : ℤ)
    (a : (cohomologyPresheafFunctor X q).obj L ⟶ limit (K ⋙ cohomologyPresheafFunctor X q))
    (ha : ∀ n : ℕ, a ≫ limit.π _ ⟨n⟩ =
      (cohomologyPresheafFunctor X q).map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))
    (U : X.C) (hU : B U) :
    IsIso ((PresheafOfModules.evaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)).map
      (limitComparisonPresheaf X K L q a)) := by
  let E := PresheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj (op U)
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q
  let ηK : K ⋙ cohomologyPresheafFunctor X q ⟶
      (K ⋙ H) ⋙ SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
    Functor.whiskerLeft K
      (cohomologyPresheafComparison (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q)
  have hA : IsIso (E.map a) :=
    isIso_evaluation_cohomologyLimitMap X U K L p hp q
      (fun n ↦ hedge U hU (q - 1) n) (hlimOne U hU (q - 1)) a ha
  have hW : IsIso (Functor.whiskerRight ηK E) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    exact isIso_evaluation_cohomologyPresheafComparison (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      U q (K.obj n) (hedge U hU q n.unop)
  have hM : IsIso (E.map (limMap ηK)) :=
    Stacks.HomologyComparison.isIso_map_limMap_of_isIso_whiskerRight E ηK
  have hT : IsIso (E.map (preservesLimitIso
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (K ⋙ H)).inv) :=
    E.map_isIso _
  have hsplit : E.map (limitComparisonPresheaf X K L q a) =
      E.map a ≫ E.map (limMap ηK) ≫
        E.map (preservesLimitIso
          (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (K ⋙ H)).inv := by
    rw [show limitComparisonPresheaf X K L q a =
        a ≫ limMap ηK ≫
          (preservesLimitIso (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (K ⋙ H)).inv from rfl,
      E.map_comp, E.map_comp]
  change IsIso (E.map (limitComparisonPresheaf X K L q a))
  rw [hsplit]
  exact IsIso.comp_isIso' hA (IsIso.comp_isIso' hM hT)

/-- The sheafification of `limitComparisonPresheaf` is an isomorphism: it is invertible on
sections over every member of a collection covering the site. -/
theorem isIso_sheafification_map_limitComparisonPresheaf
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (hedge : ∀ U, B U → ∀ (m : ℤ) (n : ℕ),
      IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U m).app
        (K.obj ⟨n⟩)))
    (hlimOne : ∀ U, B U → ∀ m : ℤ,
      IsZero (Rlim.firstDerivedLimit
        (K ⋙ DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m ⋙
          sectionsOverObject X U)))
    (q : ℤ)
    (a : (cohomologyPresheafFunctor X q).obj L ⟶ limit (K ⋙ cohomologyPresheafFunctor X q))
    (ha : ∀ n : ℕ, a ≫ limit.π _ ⟨n⟩ =
      (cohomologyPresheafFunctor X q).map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) :
    IsIso ((PresheafOfModules.sheafification
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).map
      (limitComparisonPresheaf X K L q a)) :=
  PresheafOfModules.isIso_sheafification_map_of_isIso_evaluation hB _
    fun U hU ↦ isIso_evaluation_limitComparisonPresheaf X K L p hp B hedge hlimOne q a ha U hU

/-- The comparison from the degree-`q` cohomology sheaf of a derived limit to the inverse limit
of the degree-`q` cohomology sheaves of the system is an isomorphism, as soon as the
hypercohomology edge morphisms over a covering collection are invertible and the first derived
inverse limits of the sections there vanish.

This is the content of Tag 0A09. The comparison of cohomology presheaves is an isomorphism after
sheafification, and the Tag 0BKW square then transports that to the comparison of cohomology
sheaves, the sheafification of the unit factor being invertible because the counit of
sheafification is. -/
theorem isIso_cohomologyLimitComparison
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩)
    (hp : ∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
      Triangle.mk p (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
            K.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang
          (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))))
    (B : ObjectProperty X.C) (hB : X.J.HasEnoughObjects B)
    (hedge : ∀ U, B U → ∀ (m : ℤ) (n : ℕ),
      IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U m).app
        (K.obj ⟨n⟩)))
    (hlimOne : ∀ U, B U → ∀ m : ℤ,
      IsZero (Rlim.firstDerivedLimit
        (K ⋙ DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m ⋙
          sectionsOverObject X U)))
    (q : ℤ)
    (a : (cohomologyPresheafFunctor X q).obj L ⟶ limit (K ⋙ cohomologyPresheafFunctor X q))
    (b : (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj L ⟶
      limit (K ⋙ DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q))
    (ha : ∀ n : ℕ, a ≫ limit.π _ ⟨n⟩ =
      (cohomologyPresheafFunctor X q).map (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n))
    (hb : ∀ n : ℕ, b ≫ limit.π _ ⟨n⟩ =
      (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).map
        (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) :
    IsIso b := by
  let P := cohomologyPresheafFunctor X q
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q
  let F := SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  let S := PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  let adj :=
    PresheafOfModules.sheafificationAdjunction (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)
  let η := cohomologyPresheafComparison (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q
  let ηK : K ⋙ P ⟶ (K ⋙ H) ⋙ F := Functor.whiskerLeft K η
  let t := preservesLimitIso F (K ⋙ H)
  have hd : IsIso (S.map (limitComparisonPresheaf X K L q a)) :=
    isIso_sheafification_map_limitComparisonPresheaf X K L p hp B hB hedge hlimOne q a ha
  have hfac : η.app L ≫ F.map b = limitComparisonPresheaf X K L q a := by
    rw [show limitComparisonPresheaf X K L q a = a ≫ limMap ηK ≫ t.inv from rfl]
    refine (cancel_mono t.hom).1 (limit.hom_ext fun n ↦ ?_)
    obtain ⟨n⟩ := n
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [preservesLimitIso_hom_π, ← F.map_comp, hb n, limMap_π, ← Category.assoc, ha n]
    exact (η.naturality (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)).symm
  have hunit : IsIso (S.map (η.app L)) := by
    rw [show S.map (η.app L) =
        S.map (adj.unit.app (P.obj L)) ≫
          S.map (F.map ((sheafificationCohomologyPresheafIso
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q).hom.app L)) from
      S.map_comp _ _]
    have h₁ : IsIso (S.map (adj.unit.app (P.obj L))) :=
      isIso_map_unit_app adj (P.obj L) inferInstance
    have h₂ : IsIso (S.map (F.map
        ((sheafificationCohomologyPresheafIso
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) q).hom.app L))) := inferInstance
    exact IsIso.comp_isIso' h₁ h₂
  have hcomp : IsIso (S.map (η.app L) ≫ S.map (F.map b)) := by
    rw [← S.map_comp, hfac]
    exact hd
  have hFb : IsIso (S.map (F.map b)) := IsIso.of_isIso_comp_left (S.map (η.app L)) _
  have hnat : S.map (F.map b) ≫ adj.counit.app (limit (K ⋙ H)) =
      adj.counit.app (H.obj L) ≫ b := adj.counit.naturality b
  have hcounit : IsIso (adj.counit.app (limit (K ⋙ H))) := inferInstance
  have hLHS : IsIso (S.map (F.map b) ≫ adj.counit.app (limit (K ⋙ H))) :=
    IsIso.comp_isIso' hFb hcounit
  rw [hnat] at hLHS
  exact @IsIso.of_isIso_comp_left _ _ _ _ _ (adj.counit.app (H.obj L)) b inferInstance hLHS

/-- **Stacks Project Tag 0A09, modulo Tag 0BKZ.** Cohomology commutes with a derived inverse
limit if there is a covering collection on which all positive cohomology of the cohomology
sheaves vanishes and the towers of their sections have vanishing first derived inverse limit.

The hypothesis `h0BKZ` is the statement of Tag 0BKZ: the hypercohomology edge morphism is
invertible on an object of the covering collection as soon as the cohomology sheaves are acyclic
there. It is the only input this proof takes beyond the hypotheses of Tag 0A09 itself, and
`Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover` discharges
it; the tag therefore sits on
`Stacks.Cohomology.DerivedLimitAcyclic.isLimit_cohomology_of_isDerivedLimit_of_acyclic_cover`. -/
theorem cohomology_isLimit_of_isDerivedLimit_of_acyclic_cover
    [EnoughInjectives (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    (K : ℕᵒᵖ ⥤ DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    [HasProduct fun n : ℕ ↦ K.obj ⟨n⟩]
    (hL : IsDerivedLimit K L)
    (B : ObjectProperty X.C)
    (hB : X.J.HasEnoughObjects B)
    (hacyclic : ∀ U, B U → ∀ q : ℤ, ∀ n : ℕ, ∀ r : ℕ, 0 < r →
      IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        (op U)).rightDerived r).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj
          (K.obj ⟨n⟩))))
    (hlimOne : ∀ U, B U → ∀ q : ℤ,
      IsZero (Rlim.firstDerivedLimit
        (K ⋙ DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q ⋙
          sectionsOverObject X U)))
    (h0BKZ : ∀ M : DerivedCategory
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)), ∀ U, B U →
      (∀ V, B V → ∀ r : ℕ, 0 < r → ∀ m : ℤ,
        IsZero (((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          (op V)).rightDerived r).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) m).obj M))) →
      ∀ m : ℤ, IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U m).app M))
    (q : ℤ) :
    ∃ p : L ⟶ ∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩,
      (∃ δ : (∏ᶜ fun n : ℕ ↦ K.obj ⟨n⟩) ⟶ L⟦(1 : ℤ)⟧,
        Triangle.mk p (Pi.lift fun n : ℕ ↦
          Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n -
            Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) (n + 1) ≫
              K.map (homOfLE (Nat.le_succ n)).op) δ ∈
          distTriang
            (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))) ∧
      ∃ τ : (Functor.const ℕᵒᵖ).obj
          ((DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).obj L) ⟶
          K ⋙ DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q,
        (∀ n : ℕ, τ.app ⟨n⟩ =
          (DerivedCategory.homologyFunctor
            (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q).map
            (p ≫ Pi.π (fun n : ℕ ↦ K.obj ⟨n⟩) n)) ∧
        Nonempty (IsLimit (Cone.mk _ τ)) := by
  obtain ⟨p, δ, hδ⟩ := hL
  have hedge : ∀ U, B U → ∀ (m : ℤ) (n : ℕ),
      IsIso ((hypercohomologyEdge (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U m).app
        (K.obj ⟨n⟩)) := fun U hU m n ↦
    h0BKZ (K.obj ⟨n⟩) U hU (fun V hV r hr i ↦ hacyclic V hV i n r hr) m
  obtain ⟨a, b, c, ha, hb, hc, hsquare⟩ :=
    Stacks.Cohomology.DerivedLimitDiagram.cohomologyDerivedLimitDiagram X K L p ⟨δ, hδ⟩ q
  have hbIso : IsIso b :=
    isIso_cohomologyLimitComparison X K L p ⟨δ, hδ⟩ B hB hedge hlimOne q a b ha hb
  refine ⟨p, ⟨δ, hδ⟩, (Functor.const ℕᵒᵖ).map b ≫ (limit.cone (K ⋙
    DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q)).π, fun n ↦ hb n, ?_⟩
  have := hbIso
  refine ⟨IsLimit.ofIsoLimit (limit.isLimit _) (Cone.ext (asIso b).symm fun n ↦ ?_)⟩
  simp

end RingedSite

end Stacks.Cohomology.DerivedLimitAcyclic

end
