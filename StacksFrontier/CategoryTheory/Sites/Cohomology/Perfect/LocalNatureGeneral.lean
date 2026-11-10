module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedLocalApproximationsGeneral

/-!
# Perfectness of a derived object is local on the site, at any module universe

Let `(C, O)` be a ringed site and let `E` be an object of `D(O)`. If every object `U` of `C`
admits a covering `{V → U}` such that each restriction `E|_V` is perfect on the localized ringed
site `(C/V, O|_V)`, then `E` is itself perfect.

This is `AlgebraicGeometry.RingedSite.isPerfect_of_locally` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalNature` with the module universe free:
that statement is at `RingedSite.{u, u, 0}`, and nothing in its proof uses the `0`. It is
restated here, at `RingedSite.{u, u, w}`, rather than generalized in place because the statement
of a declaration of the base library is not changed; the proof is the same, with the restriction
comparison read from `Stacks.SheafOfModules.restrictComplexAlongOverIsoGeneral`. It is what the
perfectness criterion of Stacks 08G8 needs on the diagonal `RingedSite.{u, u, u}`, the seat of
the monoidal development of Stacks 0FPT and of Stacks 0FPY.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_of_locally_general`: perfectness descends along a
  covering.
* `AlgebraicGeometry.RingedSite.exists_covering_strictlyPerfect_of_isPerfect_over`: a perfect
  restriction `E|_V` is locally represented by strictly perfect complexes on `C`.

## Implementation notes

See the implementation notes of
`StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalNature`:
the hypothesis is used only at the terminal object `Over.mk (𝟙 V)` of `C/V`, the strictly perfect
model on an iterated slice `(C/V)/Z` is carried down to `C/Z.left` by
`Stacks.SheafOfModules.sliceBackward`, and it is compared with the restriction of a chosen
representative of `E` as a quasi-isomorphism of complexes.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u w d

namespace AlgebraicGeometry.RingedSite

section Transfer

/-- **An exact functor carries a quasi-isomorphism to a quasi-isomorphism.** Stated generically
with the quasi-isomorphism as an explicit hypothesis: at the use site the source complex is
written at one of the two spellings of the structure sheaf of a slice and the functor at the
other, and the two agree at default transparency but not at the transparency typeclass synthesis
uses. -/
private theorem perfLocGenQuasiIsoMap {A B : Type*} [Category A] [Abelian A] [Category B]
    [Abelian B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P Q : CochainComplex A ℤ} (φ : P ⟶ Q) (h : QuasiIso φ) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := by
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  infer_instance

end Transfer

section Main

variable (X : RingedSite.{u, u, w})
variable [HasSheafify X.J AddCommGrpCat.{w}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
variable [∀ (U : X.C) (W : Over U), HasSheafify ((X.J.over U).over W) AddCommGrpCat.{w}]
variable [∀ (U : X.C) (W : Over U),
  ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective

/-- On the localized site `C/U`, every slice `(C/U)/W` admits sheafification of abelian-group
presheaves. -/
local instance perfLocGenOvHasSheafifyIterAll (U : X.C) :
    ∀ W : (X.over U).C, HasSheafify ((X.over U).J.over W) AddCommGrpCat.{w} :=
  fun W => (inferInstance : ∀ (U : X.C) (W : Over U),
    HasSheafify ((X.J.over U).over W) AddCommGrpCat.{w}) U W

/-- On the localized site `C/U`, on every slice `(C/U)/W` the morphisms of abelian-group
presheaves inverted by sheafification are the locally bijective ones. -/
local instance perfLocGenOvWEqIterAll (U : X.C) :
    ∀ W : (X.over U).C, ((X.over U).J.over W).WEqualsLocallyBijective AddCommGrpCat.{w} :=
  fun W => (inferInstance : ∀ (U : X.C) (W : Over U),
    ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{w}) U W

attribute [local instance] ovFunctorLimits ovFunctorColimits overMapLimits overMapColimits

omit [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] in
/-- Transport from an iterated slice `(C/V)/Z` to `C/Z.left` preserves finite colimits. -/
private instance perfLocGenSliceBackwardColimits {V : X.C} (W : Over V) :
    PreservesFiniteColimits (Stacks.SheafOfModules.sliceBackward.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W.hom) :=
  Stacks.SheafOfModules.sliceBackward_preservesFiniteColimits W.hom

variable [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hPerfLocDer : ∀ U : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

attribute [local instance] locallyOverRingSheafHasDerivedCategory ovHasDerived

/-- If the restriction `E|_V` is perfect on `(C/V, O|_V)`, then `V` admits a covering over each
member `W` of which `E|_W` is represented by a strictly perfect complex. -/
theorem exists_covering_strictlyPerfect_of_isPerfect_over
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {V : X.C} (hV : (X.over V).IsPerfect
      ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.obj E)) :
    ∃ T : Presieve V, Sieve.generate T ∈ X.J V ∧
      ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
        ∃ P : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
          IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P ∧
            Nonempty (DerivedCategory.Q.obj P ≅
              (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                W).mapDerivedCategory.obj E) := by
  obtain ⟨K, eK⟩ : Σ' K : CochainComplex
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      DerivedCategory.Q.obj K ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  have hrepr : ∀ V : X.C, DerivedCategory.Q.obj (X.restrictComplex K V) ≅
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.obj E := fun V =>
    ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategoryFactors.app K).symm ≪≫
      (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.mapIso eK
  obtain ⟨Ecpx, hEcpx, ⟨eE⟩⟩ := hV
  have eE' : DerivedCategory.Q.obj (Ecpx : CochainComplex
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ) ≅
        DerivedCategory.Q.obj (X.restrictComplex K V) := eE ≪≫ (hrepr V).symm
  obtain ⟨S₁, hS₁, hdata₁⟩ := hEcpx (Over.mk (𝟙 V))
  refine ⟨Presieve.map (Over.forget V) S₁, ?_, ?_⟩
  · rwa [Sieve.generate_map_eq_functorPushforward]
  rintro W g @⟨Z, u, hv⟩
  obtain ⟨P, hP, q, hq⟩ := hdata₁ u hv
  let Om := SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom
  let Sb := Stacks.SheafOfModules.sliceBackward.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom
  let Sbc := Sb.mapHomologicalComplex (ComplexShape.up ℤ)
  have : PreservesFiniteLimits Sb := Stacks.SheafOfModules.sliceBackward_preservesFiniteLimits Z.hom
  let e₁ : Sbc.obj ((X.over V).restrictComplex Ecpx Z) ≅
      ((Om.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Ecpx : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)) :=
    (Stacks.SheafOfModules.sliceBackwardComplexIso.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom).app Ecpx
  let β := Sbc.map q ≫ e₁.hom
  have : QuasiIso (Sbc.map q) := perfLocGenQuasiIsoMap Sb q hq
  have : IsIso (DerivedCategory.Q.map β) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso
      (C := SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Z.left)) β).2
      inferInstance
  exact ⟨Sbc.obj P,
    Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex _
      (Stacks.SheafOfModules.sliceBackwardUnitIso.{w} Z.hom) hP,
    ⟨asIso (DerivedCategory.Q.map β) ≪≫ (Om.mapDerivedCategoryFactors.app _).symm ≪≫
      Om.mapDerivedCategory.mapIso eE' ≪≫ Om.mapDerivedCategoryFactors.app _ ≪≫
      DerivedCategory.Q.mapIso (Stacks.SheafOfModules.restrictComplexAlongOverIsoGeneral
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom K) ≪≫ hrepr Z.left⟩⟩

/-- **Perfectness descends along a covering**, at any module universe. Let `E` be an object of
`D(O)` and suppose that every object `U` of `C` admits a covering `{V → U}` over each member of
which the restriction `E|_V` is perfect on the localized ringed site `(C/V, O|_V)`. Then `E` is
perfect.

This is the local-to-global half of Stacks 08G5 read through the local models of Stacks 08G6,
part (1). -/
theorem isPerfect_of_locally_general
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        (X.over V).IsPerfect
          ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            V).mapDerivedCategory.obj E)) :
    X.IsPerfect E := by
  refine isPerfect_of_forall_coveringFamily_strictlyPerfect X E (fun U => ?_)
  obtain ⟨S, hS, hdata⟩ := h U
  have key ⦃V : X.C⦄ (f : V ⟶ U) (hf : S f) :=
    exists_covering_strictlyPerfect_of_isPerfect_over X E (hdata f hf)
  refine ⟨fun {Z} p => ∃ (V : X.C) (f : V ⟶ U) (hf : S f) (g : Z ⟶ V),
    (key f hf).choose g ∧ p = g ≫ f, ?_, ?_⟩
  · refine X.J.transitive hS _ ?_
    rintro Z p ⟨V, a, f, hf, rfl⟩
    refine X.J.superset_covering ?_ (X.J.pullback_stable a (key f hf).choose_spec.1)
    rintro Y k ⟨Y', b, g, hg, hbg⟩
    exact ⟨Y', b, g ≫ f, ⟨V, f, hf, g, hg, rfl⟩, by rw [← Category.assoc, hbg, Category.assoc]⟩
  · rintro W p ⟨V, f, hf, g, hg, rfl⟩
    exact (key f hf).choose_spec.2 g hg

end Main

end AlgebraicGeometry.RingedSite

end
