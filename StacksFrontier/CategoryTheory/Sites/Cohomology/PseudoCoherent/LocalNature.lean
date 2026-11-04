module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CokernelFinitePresentation
public import StacksFrontier.CategoryTheory.Sites.Localization.RingedSiteLocalization
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Representatives
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Pseudo-coherence of a derived object is local on the site

Let `(C, O)` be a ringed site and let `E` be an object of `D(O)`. If every object `U` of `C`
admits a covering `{V → U}` such that each restriction `E|_V` is `m`-pseudo-coherent on the
localized ringed site `(C/V, O|_V)`, then `E` is itself `m`-pseudo-coherent. This is part (3)
of Stacks 08FU.

## Main results

* `AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally`: Stacks 08FU, part (3).

## Implementation notes

The source dismisses this as a formal consequence of the definitions and of the transitivity
axiom for a Grothendieck topology. Two pieces of bookkeeping make it work in Lean.

* Pseudo-coherence of `E|_V` is a statement about the *derived object* `E|_V`; to get a
  strictly perfect approximation of a complex one first passes to part (2) of Stacks 08FU,
  `isPseudoCoherentComplexFrom_of_iso`, applied on the localized ringed site `X.over V`, with
  the restriction `K|_V` of a fixed representative `K` of `E` as the representing complex.
  That `K|_V` represents `E|_V` is `Functor.mapDerivedCategoryFactors` for restriction.
  Instantiating part (2) at a localized site is what forces the sheafification hypotheses on
  the *iterated* slices `(C/V)/W`, which are supplied below by transport along
  `CategoryTheory.Over.iteratedSliceEquiv`.
* The definition of `m`-pseudo-coherence of the complex `K|_V` on `C/V` is a statement about
  all objects of `C/V`; it is used here only at the terminal object `Over.mk (𝟙 V)`, whose
  covering presieves are exactly the covering presieves of `V` in `C`
  (`CategoryTheory.Sieve.generate_map_eq_functorPushforward` and
  `CategoryTheory.GrothendieckTopology.mem_over_iff`). The approximation it provides over an
  object `Z` of `C/V` lives on the iterated slice `(C/V)/Z`, and is carried down to `C/Z.left`
  by `Stacks.SheafOfModules.sliceBackward`, whose exactness and compatibility with strict
  perfectness are established below by the same arguments as for
  `Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits`.

The two coverings are then composed into a single presieve on `U`, rather than into
`Sieve.bind` of two sieves: carrying an approximation is a property of the *source object* of
an arrow, so no restriction-stability of the data is needed, and the composite presieve
generates a covering sieve by transitivity alone.

Stacks 08FU (3) is stated twice: `isPseudoCoherentFrom_of_locally_general` has the objects of
the site, its morphisms and the sections of the structure sheaf at independent universes, and
`isPseudoCoherentFrom_of_locally` is its instance at `RingedSite.{u, u, 0}`.

## References

* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v u d d'

namespace Stacks.SheafOfModules

section SliceBackward

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{w}} {U V : C} (f : V ⟶ U)

/-- Transport of sheaves of modules from an iterated slice preserves finite limits: limits of
sheaves of modules are computed objectwise, and the transport reindexes objects. -/
theorem sliceBackward_preservesFiniteLimits :
    PreservesFiniteLimits (sliceBackward.{w} R f) := by
  refine ⟨fun K _ _ => ⟨fun {F} => ⟨fun {c} hc => ?_⟩⟩⟩
  refine ⟨isLimitOfReflects (SheafOfModules.forget (R.over V)) ?_⟩
  apply PresheafOfModules.evaluationJointlyReflectsLimits
  intro W
  exact isLimitOfPreserves
    (SheafOfModules.evaluation ((R.over U).over (Over.mk f))
      (Opposite.op ((Over.mk f).iteratedSliceBackward.obj W.unop))) hc

/-- Transport of sheaves of modules from an iterated slice preserves epimorphisms: an
epimorphism is a locally surjective map of underlying abelian sheaves, and local surjectivity
is stable under whiskering along a cocontinuous functor. -/
theorem sliceBackward_preservesEpimorphisms
    [((J.over U).over (Over.mk f)).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify ((J.over U).over (Over.mk f)) AddCommGrpCat.{w}] :
    (sliceBackward.{w} R f).PreservesEpimorphisms := by
  refine ⟨fun {A B} g _ => ?_⟩
  have : Presheaf.IsLocallySurjective ((J.over U).over (Over.mk f))
      ((SheafOfModules.toSheaf ((R.over U).over (Over.mk f))).map g).hom :=
    LocalCokernel.locallySurjective_of_epi g
  have hlocal : Presheaf.IsLocallySurjective (J.over V)
      ((SheafOfModules.toSheaf (R.over V)).map ((sliceBackward.{w} R f).map g)).hom :=
    Presheaf.isLocallySurjective_whisker (J.over (Over.mk f).left)
      ((J.over U).over (Over.mk f)) (Over.mk f).iteratedSliceBackward
      ((SheafOfModules.toSheaf ((R.over U).over (Over.mk f))).map g).hom
  have : Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf (R.over V)).map ((sliceBackward.{w} R f).map g)) :=
    (Sheaf.isLocallySurjective_sheafToPresheaf_map_iff _).2 hlocal
  have : Epi ((SheafOfModules.toSheaf (R.over V)).map ((sliceBackward.{w} R f).map g)) :=
    Sheaf.epi_of_isLocallySurjective _
  exact (SheafOfModules.toSheaf (R.over V)).epi_of_epi_map this

/-- Transport of sheaves of modules from an iterated slice preserves finite colimits. -/
theorem sliceBackward_preservesFiniteColimits
    [((J.over U).over (Over.mk f)).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify ((J.over U).over (Over.mk f)) AddCommGrpCat.{w}]
    [HasWeakSheafify (J.over V) AddCommGrpCat.{w}]
    [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify (J.over V) AddCommGrpCat.{w}] :
    PreservesFiniteColimits (sliceBackward.{w} R f) := by
  have : PreservesFiniteLimits (sliceBackward.{w} R f) :=
    sliceBackward_preservesFiniteLimits f
  have : (sliceBackward.{w} R f).PreservesEpimorphisms :=
    sliceBackward_preservesEpimorphisms f
  exact LocalCokernel.finiteColimits_of_finiteLimits_epi _

/-- The transport of the unit sheaf of an iterated slice is the unit sheaf of the slice: the
two sheaves of modules agree on the nose. -/
noncomputable def sliceBackwardUnitIso :
    SheafOfModules.unit (R.over V) ≅
      (sliceBackward.{w} R f).obj
        (SheafOfModules.unit ((R.over U).over (Over.mk f))) :=
  Iso.refl _

end SliceBackward

section UnitIso

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) (U : C)

/-- Restriction of the unit sheaf to a slice is the unit sheaf of the slice: the two sheaves
of modules agree on the nose. -/
noncomputable def overFunctorUnitIso :
    SheafOfModules.unit (R.over U) ≅
      (SheafOfModules.overFunctor.{w} R U).obj (SheafOfModules.unit R) :=
  Iso.refl _

end UnitIso

section StrictlyPerfectMap

/-- An exact functor of sheaves of modules carrying the unit sheaf to the unit sheaf carries a
strictly perfect complex to a strictly perfect complex: it preserves vanishing of a term, and
it carries a finite free module to a finite free module. -/
theorem isStrictlyPerfect_mapHomologicalComplex
    {C D : Type*} [Category* C] [Category* D]
    {J : GrothendieckTopology C} {K : GrothendieckTopology D}
    {R : Sheaf J RingCat.{w}} {S : Sheaf K RingCat.{w}}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasSheafify K AddCommGrpCat.{w}] [K.WEqualsLocallyBijective AddCommGrpCat.{w}]
    (F : SheafOfModules.{w} R ⥤ SheafOfModules.{w} S) [F.Additive]
    [Limits.PreservesFiniteColimits F]
    (η : SheafOfModules.unit S ≅ F.obj (SheafOfModules.unit R))
    {P : CochainComplex (SheafOfModules.{w} R) ℤ} (hP : IsStrictlyPerfect R P) :
    IsStrictlyPerfect S ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj P) := by
  refine ⟨hP.bounded.subset ?_, fun i => ?_⟩
  · intro i hi
    simp only [Set.mem_ofPred_eq] at hi ⊢
    exact fun hz => hi (F.map_isZero hz)
  · obtain ⟨n, j, r, hjr⟩ :=
      (isDirectSummandOfFiniteFree_iff_free R (P.X i)).mp (hP.termDirectSummand i)
    let eFree := SheafOfModules.mapFreeIso F (ULift.{w} (Fin n)) η
    refine (isDirectSummandOfFiniteFree_iff_free S _).mpr
      ⟨n, F.map j ≫ eFree.inv, eFree.hom ≫ F.map r, ?_⟩
    rw [Category.assoc, ← Category.assoc eFree.inv, eFree.inv_hom_id, Category.id_comp,
      ← Functor.map_comp, hjr, CategoryTheory.Functor.map_id]
    rfl

end StrictlyPerfectMap

end Stacks.SheafOfModules

namespace AlgebraicGeometry.RingedSite

section Transfer

/-- An isomorphism of complexes is invertible on cohomology in every degree. -/
theorem isIso_homologyMap_of_iso {A : Type*} [Category A] [Abelian A]
    {P Q : CochainComplex A ℤ} (e : P ≅ Q) (j : ℤ) :
    IsIso (HomologicalComplex.homologyMap e.hom j) := by
  show IsIso ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) j).map e.hom)
  infer_instance

variable {A B : Type*} [Category A] [Abelian A] [Category B] [Abelian B]
  (F : A ⥤ B) [F.Additive] [F.PreservesHomology]

/-- Composing with an isomorphism of complexes preserves invertibility on cohomology in a
degree. Stated once generically, because at the use site the two spellings of the source
complex agree only at default transparency, where `simp` cannot see them. -/
theorem isIso_homologyMap_comp_iso {A : Type*} [Category A] [Abelian A]
    {P Q R : CochainComplex A ℤ} (φ : P ⟶ Q) (e : Q ≅ R) (j : ℤ)
    (h : IsIso (HomologicalComplex.homologyMap φ j)) :
    IsIso (HomologicalComplex.homologyMap (φ ≫ e.hom) j) := by
  rw [HomologicalComplex.homologyMap_comp]
  have := isIso_homologyMap_of_iso e j
  infer_instance

/-- Composing with an isomorphism of complexes preserves epimorphy on cohomology in a
degree. -/
theorem epi_homologyMap_comp_iso {A : Type*} [Category A] [Abelian A]
    {P Q R : CochainComplex A ℤ} (φ : P ⟶ Q) (e : Q ≅ R) (j : ℤ)
    (h : Epi (HomologicalComplex.homologyMap φ j)) :
    Epi (HomologicalComplex.homologyMap (φ ≫ e.hom) j) := by
  rw [HomologicalComplex.homologyMap_comp]
  have := isIso_homologyMap_of_iso e j
  infer_instance

end Transfer

section StrictlyPerfect

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{w}) {U V : C} (f : V ⟶ U)
  [HasSheafify (J.over V) AddCommGrpCat.{w}]
  [(J.over V).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify ((J.over U).over (Over.mk f)) AddCommGrpCat.{w}]
  [((J.over U).over (Over.mk f)).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Transport from an iterated slice carries a complex which is strictly perfect there to a
strictly perfect complex on the slice. -/
private theorem isStrictlyPerfect_sliceBackward
    {P : CochainComplex (SheafOfModules.{w} ((R.over U).over (Over.mk f))) ℤ}
    (hP : IsStrictlyPerfect ((R.over U).over (Over.mk f)) P) :
    IsStrictlyPerfect (R.over V)
      (((Stacks.SheafOfModules.sliceBackward.{w} R f).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  have : Limits.PreservesFiniteColimits (Stacks.SheafOfModules.sliceBackward.{w} R f) :=
    Stacks.SheafOfModules.sliceBackward_preservesFiniteColimits f
  Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex _
    (Stacks.SheafOfModules.sliceBackwardUnitIso.{w} f) hP

end StrictlyPerfect

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.RingedSite

section Main

variable (X : RingedSite.{u, v, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective

/-- The forgetful functor to rings composes with the sheaf condition on each slice of the site,
at the spelling `(X.over U).J` of the localized topology. -/
local instance ovSheafCompose
    [∀ U : X.C, (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})] (U : X.C) :
    (X.over U).J.HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0}) :=
  (inferInstance : ∀ U : X.C,
    (X.J.over U).HasSheafCompose (forget₂ CommRingCat.{0} RingCat.{0})) U

/-- Sheafification of abelian-group presheaves exists on each iterated slice
`(J.over U).over W`. -/
local instance iterHasSheafify (U : X.C) (W : Over U) :
    HasSheafify ((X.J.over U).over W) AddCommGrpCat.{w} :=
  W.iteratedSliceEquiv.hasSheafify ((X.J.over U).over W) (X.J.over W.left) AddCommGrpCat.{w}

/-- On each iterated slice `(J.over U).over W`, the morphisms of abelian-group presheaves that
become isomorphisms after sheafification are exactly the locally bijective ones. -/
local instance iterWEq (U : X.C) (W : Over U) :
    ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{w} := by
  have : (W.iteratedSliceEquiv.inverse.sheafPushforwardContinuous AddCommGrpCat.{w}
      (X.J.over W.left) ((X.J.over U).over W)).EssSurj :=
    inferInstanceAs ((W.iteratedSliceEquiv.sheafCongr ((X.J.over U).over W)
      (X.J.over W.left) AddCommGrpCat.{w}).functor.EssSurj)
  exact GrothendieckTopology.WEqualsLocallyBijective.transport
    ((X.J.over U).over W) (X.J.over W.left) W.iteratedSliceEquiv.inverse
    (Functor.IsDenseSubsite.coverPreserving _ _ _)

/-- Sheafification of abelian-group presheaves exists on each slice of the site `X.over U`. -/
local instance iterHasSheafifyAll (U : X.C) :
    ∀ W : (X.over U).C, HasSheafify ((X.over U).J.over W) AddCommGrpCat.{w} :=
  fun W => iterHasSheafify X U W

/-- On each slice of the site `X.over U`, the morphisms of abelian-group presheaves that become
isomorphisms after sheafification are exactly the locally bijective ones. -/
local instance iterWEqAll (U : X.C) :
    ∀ W : (X.over U).C, ((X.over U).J.over W).WEqualsLocallyBijective AddCommGrpCat.{w} :=
  fun W => iterWEq X U W

/-- Restriction of sheaves of modules to the slice over `U` preserves finite limits. -/
local instance ovFunctorLimits (R : Sheaf X.J RingCat.{w}) (U : X.C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{w} R U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits U

/-- Restriction of sheaves of modules on `X.over U` to each of its slices preserves finite
limits. -/
local instance ovFunctorLimitsAll (U : X.C) :
    ∀ W : (X.over U).C,
      PreservesFiniteLimits
        (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) W) :=
  fun W => Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits W

/-- Restriction of sheaves of modules to the slice over `U` preserves finite colimits. -/
local instance ovFunctorColimits (U : X.C) :
    PreservesFiniteColimits
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits U

/-- Restriction of sheaves of modules on `X.over U` to each of its slices preserves finite
colimits. -/
local instance ovFunctorColimitsAll (U : X.C) :
    ∀ W : (X.over U).C,
      PreservesFiniteColimits
        (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O) W) :=
  fun W => Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits W

/-- Restriction along an arrow of the site preserves finite limits. -/
local instance overMapLimits {U V : X.C} (g : V ⟶ U) :
    PreservesFiniteLimits
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteLimits g

/-- Restriction along an arrow of the site preserves finite colimits. -/
local instance overMapColimits {U V : X.C} (g : V ⟶ U) :
    PreservesFiniteColimits
      (SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) g) :=
  Stacks.SheafOfModules.LocalCokernel.overMap_preservesFiniteColimits g

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hDer : ∀ U : X.C,
  HasDerivedCategory.{d'}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

/-- The category of sheaves of modules over the restriction of the structure sheaf to `U` has
a derived category. -/
local instance locallyOverRingSheafHasDerivedCategory (U : X.C) :
    HasDerivedCategory.{d'}
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U)) :=
  hDer U

/-- The category of sheaves of modules over the structure sheaf of the ringed site `X.over U`
has a derived category. -/
local instance ovHasDerived (U : X.C) :
    HasDerivedCategory.{d'}
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (X.over U).O)) :=
  hDer U

/-- **Stacks 08FU, part (3)**, with the site, its morphisms and the sections of the structure
sheaf at independent universes. Let `(C, O)` be a ringed site and let `E` be an object of
`D(O)`. If every object `U` of `C` admits a covering `{V → U}` over each member of which the
restriction of `E` is `m`-pseudo-coherent, then `E` is `m`-pseudo-coherent. -/
theorem isPseudoCoherentFrom_of_locally_general
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (h : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        (X.over V).IsPseudoCoherentFrom
          ((SheafOfModules.overFunctor.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj E) m) :
    X.IsPseudoCoherentFrom E m := by
  classical
  obtain ⟨K, eK⟩ : Σ' K : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      DerivedCategory.Q.obj K ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  refine ⟨K, ?_, ⟨eK⟩⟩
  have key : ∀ V : X.C,
      (X.over V).IsPseudoCoherentFrom
        ((SheafOfModules.overFunctor.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj E) m →
      ∃ T : Presieve V, Sieve.generate T ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
          ∃ P : CochainComplex
              (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P ∧
            ∃ α : P ⟶ X.restrictComplex K W,
              (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
              Epi (HomologicalComplex.homologyMap α m) := by
    intro V hV
    have erep : DerivedCategory.Q.obj (X.restrictComplex K V) ≅
        (SheafOfModules.overFunctor.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj E :=
      ((SheafOfModules.overFunctor.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategoryFactors.app K).symm ≪≫
        (SheafOfModules.overFunctor.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.mapIso eK
    have hc : (X.over V).IsPseudoCoherentComplexFrom (X.restrictComplex K V) m :=
      isPseudoCoherentComplexFrom_of_iso_general (X.over V) _ m hV (X.restrictComplex K V) erep
    obtain ⟨S₁, hS₁, hdata₁⟩ := hc (Over.mk (𝟙 V))
    refine ⟨Presieve.map (Over.forget V) S₁, ?_, ?_⟩
    · rw [Sieve.generate_map_eq_functorPushforward]
      exact hS₁
    · rintro W g @⟨Z, u, hv⟩
      obtain ⟨P, hP, α, hgt, hep⟩ := hdata₁ u hv
      let Sb :=
        Stacks.SheafOfModules.sliceBackward.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom
      let Sbc := Sb.mapHomologicalComplex (ComplexShape.up ℤ)
      let e₁ := (Stacks.SheafOfModules.sliceBackwardComplexIso.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom).app (X.restrictComplex K V)
      let e₂ := (Stacks.SheafOfModules.overFunctorMapComplexIso.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom).app K
      let e := e₁ ≪≫ e₂
      have : PreservesFiniteLimits Sb :=
        Stacks.SheafOfModules.sliceBackward_preservesFiniteLimits Z.hom
      have : PreservesFiniteColimits Sb :=
        Stacks.SheafOfModules.sliceBackward_preservesFiniteColimits Z.hom
      have : Sb.PreservesHomology := Functor.preservesHomologyOfExact Sb
      refine ⟨Sbc.obj P,
        isStrictlyPerfect_sliceBackward (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom hP,
        Sbc.map α ≫ e.hom, ?_, ?_⟩
      · exact fun j hj =>
          isIso_homologyMap_comp_iso _ e j (isIso_homologyMap_map Sb α j (hgt j hj))
      · exact epi_homologyMap_comp_iso _ e m (epi_homologyMap_map Sb α m hep)
  intro U
  obtain ⟨S, hS, hdata⟩ := h U
  have key2 := fun ⦃V : X.C⦄ (f : V ⟶ U) (hf : S f) => key V (hdata f hf)
  refine ⟨fun {Z} p => ∃ (V : X.C) (f : V ⟶ U) (hf : S f) (g : Z ⟶ V),
    (key2 f hf).choose g ∧ p = g ≫ f, ?_, ?_⟩
  · refine X.J.transitive hS _ ?_
    rintro Z p ⟨V, a, f, hf, rfl⟩
    refine X.J.superset_covering ?_ (X.J.pullback_stable a (key2 f hf).choose_spec.1)
    rintro Y k ⟨Y', b, g, hg, hbg⟩
    exact ⟨Y', b, g ≫ f, ⟨V, f, hf, g, hg, rfl⟩, by rw [← Category.assoc, hbg, Category.assoc]⟩
  · rintro W p ⟨V, f, hf, g, hg, rfl⟩
    exact (key2 f hf).choose_spec.2 g hg

section DiagonalUniverses

variable (X : RingedSite.{u, u, 0})
variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hDer : ∀ U : X.C,
  HasDerivedCategory.{d'}
    (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

/-- **Stacks 08FU, part (3).** Let `(C, O)` be a ringed site and let `E` be an object of
`D(O)`. If every object `U` of `C` admits a covering `{V → U}` over each member of which the
restriction of `E` is `m`-pseudo-coherent, then `E` is `m`-pseudo-coherent. -/
@[stacks 08FU "part (3)"]
theorem isPseudoCoherentFrom_of_locally
    (E : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) (m : ℤ)
    (h : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        (X.over V).IsPseudoCoherentFrom
          ((SheafOfModules.overFunctor.{0}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapDerivedCategory.obj E) m) :
    X.IsPseudoCoherentFrom E m :=
  isPseudoCoherentFrom_of_locally_general X E m h

end DiagonalUniverses

end Main

end AlgebraicGeometry.RingedSite

end
