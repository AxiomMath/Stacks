module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension
import StacksCore.Tactic.StacksAttribute

/-!
# Perfectness of a derived object is local on the site

Let `(C, O)` be a ringed site and let `E` be an object of `D(O)`. If every object `U` of `C`
admits a covering `{V → U}` such that each restriction `E|_V` is perfect on the localized ringed
site `(C/V, O|_V)`, then `E` is itself perfect.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_of_locally`: perfectness descends along a covering.

## Implementation notes

The shape of the argument is that of
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally`, Stacks 08FU part (3): the
hypothesis is a statement about the objects of the slices `C/V`, and it is used only at the
terminal object `Over.mk (𝟙 V)` of `C/V`, whose covering presieves are the covering presieves of
`V` in `C` (`CategoryTheory.Sieve.generate_map_eq_functorPushforward`). The strictly perfect
model it provides over an object `Z` of `C/V` lives on the iterated slice `(C/V)/Z` and is
carried down to `C/Z.left` by `Stacks.SheafOfModules.sliceBackward`, which is exact and matches
up the two structure sheaves, so it preserves strict perfectness
(`Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex`) and quasi-isomorphisms.

Perfectness, unlike pseudo-coherence, asks for its local models to be isomorphic to the
restriction in the *derived* category rather than merely to map to a chosen representative of
it. No derived category of an iterated slice is needed for that: the model is compared with the
restriction of a chosen representative `K` of `E` as a quasi-isomorphism of complexes on
`C/Z.left`, and the two restrictions of `K` are identified by
`AlgebraicGeometry.RingedSite.restrictComplexAlongOverIso` after the comparison with the chosen
representative of `E|_V` has been pushed along the exact restriction
`SheafOfModules.overMap O Z.hom`.

The two coverings are composed into a single presieve on `U` rather than into a `Sieve.bind`,
since carrying a model is a property of the source object of an arrow; the composite presieve
generates a covering sieve by transitivity alone.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u d

namespace AlgebraicGeometry.RingedSite

section Transfer

/-- **An exact functor carries a quasi-isomorphism to a quasi-isomorphism, up to a chosen
isomorphism of its target.** Stated generically with the quasi-isomorphism as an explicit
hypothesis: at the use site the source complex is written at one of the two spellings of the
structure sheaf of a slice and the functor at the other, and the two agree at default
transparency but not at the transparency typeclass synthesis uses. -/
private theorem perfLocQuasiIsoMapCompIso {A B : Type*} [Category A] [Abelian A] [Category B]
    [Abelian B] (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    {P Q : CochainComplex A ℤ} {R : CochainComplex B ℤ} (φ : P ⟶ Q)
    (e : (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj Q ≅ R) (h : QuasiIso φ) :
    QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ ≫ e.hom) := by
  have := h
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  have : QuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map φ) := inferInstance
  have : IsIso e.hom := e.isIso_hom
  infer_instance

end Transfer

section Main

variable (X : RingedSite.{u, u, 0})
variable [HasSheafify X.J AddCommGrpCat.{0}]
variable [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{0}]
variable [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{0}]
variable [∀ (U : X.C) (W : Over U), HasSheafify ((X.J.over U).over W) AddCommGrpCat.{0}]
variable [∀ (U : X.C) (W : Over U),
  ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}]

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective

/-- For every object `U` of `C` and every object `W` of the slice `C/U`, the iterated slice
topology on `(C/U)/W` admits sheafification of abelian-group-valued presheaves. -/
local instance perfLocOvHasSheafifyIterAll (U : X.C) :
    ∀ W : (X.over U).C, HasSheafify ((X.over U).J.over W) AddCommGrpCat.{0} :=
  fun W => (inferInstance : ∀ (U : X.C) (W : Over U),
    HasSheafify ((X.J.over U).over W) AddCommGrpCat.{0}) U W

/-- For every object `U` of `C` and every object `W` of the slice `C/U`, the weak equivalences
of abelian-group-valued presheaves on the iterated slice `(C/U)/W` are the locally bijective
morphisms. -/
local instance perfLocOvWEqIterAll (U : X.C) :
    ∀ W : (X.over U).C, ((X.over U).J.over W).WEqualsLocallyBijective AddCommGrpCat.{0} :=
  fun W => (inferInstance : ∀ (U : X.C) (W : Over U),
    ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{0}) U W

attribute [local instance] preservesFiniteLimitsOverFunctor preservesFiniteColimitsOverFunctor
  preservesFiniteLimitsOverMap' preservesFiniteColimitsOverMap'

omit [HasSheafify X.J AddCommGrpCat.{0}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{0}] in
/-- A strictly perfect complex on an iterated slice `(C/V)/Z` transports to a strictly perfect
complex on the slice `C/Z.left`, the transport being exact and matching up the two structure
sheaves. -/
private theorem perfLocIsStrictlyPerfectSliceBackward {V : X.C} (W : Over V)
    {P : CochainComplex
      (SheafOfModules.{0}
        (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V).over (Over.mk W.hom))) ℤ}
    (hP : IsStrictlyPerfect
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V).over (Over.mk W.hom)) P) :
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W.left)
      (((Stacks.SheafOfModules.sliceBackward.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        W.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj P) :=
  have : PreservesFiniteColimits
      (Stacks.SheafOfModules.sliceBackward.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        W.hom) :=
    Stacks.SheafOfModules.sliceBackward_preservesFiniteColimits W.hom
  Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex _
    (Stacks.SheafOfModules.sliceBackwardUnitIso.{0} W.hom) hP

variable [HasDerivedCategory.{d} (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
variable [hPerfLocDer : ∀ U : X.C,
  HasDerivedCategory.{d} (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

attribute [local instance] locallyOverRingSheafHasDerivedCategory ovHasDerived

/-- **Perfectness descends along a covering.** Let `E` be an object of `D(O)` and suppose that
every object `U` of `C` admits a covering `{V → U}` over each member of which the restriction
`E|_V` is perfect on the localized ringed site `(C/V, O|_V)`. Then `E` is perfect.

This is the local-to-global half of Stacks 08G5 read through the local models of Stacks 08G6,
part (1). -/
theorem isPerfect_of_locally
    (E : DerivedCategory (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        (X.over V).IsPerfect
          ((SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            V).mapDerivedCategory.obj E)) :
    X.IsPerfect E := by
  classical
  obtain ⟨K, eK⟩ : Σ' K : CochainComplex
      (SheafOfModules.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ,
      DerivedCategory.Q.obj K ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  have hrepr : ∀ V : X.C, DerivedCategory.Q.obj (X.restrictComplex K V) ≅
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.obj E := fun V =>
    ((SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategoryFactors.app K).symm ≪≫
      (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        V).mapDerivedCategory.mapIso eK
  refine isPerfect_of_forall_coveringFamily_strictlyPerfect X E (fun U => ?_)
  obtain ⟨S, hS, hdata⟩ := h U
  have key : ∀ V : X.C,
      (X.over V).IsPerfect
        ((SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          V).mapDerivedCategory.obj E) →
      ∃ T : Presieve V, Sieve.generate T ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
          ∃ P : CochainComplex
              (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P ∧
              Nonempty (DerivedCategory.Q.obj P ≅
                (SheafOfModules.overFunctor.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                  W).mapDerivedCategory.obj E) := by
    intro V hV
    obtain ⟨Ecpx, hEcpx, ⟨eE⟩⟩ := hV
    have eE' : DerivedCategory.Q.obj
        (Ecpx : CochainComplex
          (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ) ≅
          DerivedCategory.Q.obj (X.restrictComplex K V) := eE ≪≫ (hrepr V).symm
    obtain ⟨S₁, hS₁, hdata₁⟩ := hEcpx (Over.mk (𝟙 V))
    refine ⟨Presieve.map (Over.forget V) S₁, ?_, ?_⟩
    · rwa [Sieve.generate_map_eq_functorPushforward]
    · rintro W g @⟨Z, u, hv⟩
      obtain ⟨P, hP, q, hq⟩ := hdata₁ u hv
      let Om := SheafOfModules.overMap.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom
      let Sb :=
        Stacks.SheafOfModules.sliceBackward.{0} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom
      let Sbc := Sb.mapHomologicalComplex (ComplexShape.up ℤ)
      have : PreservesFiniteLimits Sb :=
        Stacks.SheafOfModules.sliceBackward_preservesFiniteLimits Z.hom
      have : PreservesFiniteColimits Sb :=
        Stacks.SheafOfModules.sliceBackward_preservesFiniteColimits Z.hom
      let e₁ : Sbc.obj ((X.over V).restrictComplex Ecpx Z) ≅
          ((Om.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            (Ecpx : CochainComplex
              (SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)) :=
        (Stacks.SheafOfModules.sliceBackwardComplexIso.{0}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom).app Ecpx
      let β := Sbc.map q ≫ e₁.hom
      have : IsIso (DerivedCategory.Q.map β) :=
        (DerivedCategory.isIso_Q_map_iff_quasiIso
          (C := SheafOfModules.{0} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Z.left)) β).2
          (perfLocQuasiIsoMapCompIso Sb q e₁ hq)
      refine ⟨Sbc.obj P, perfLocIsStrictlyPerfectSliceBackward X Z hP, ⟨?_⟩⟩
      refine asIso (DerivedCategory.Q.map β) ≪≫ ?_
      refine (Om.mapDerivedCategoryFactors.app _).symm ≪≫ Om.mapDerivedCategory.mapIso eE' ≪≫ ?_
      refine Om.mapDerivedCategoryFactors.app _ ≪≫ ?_
      exact DerivedCategory.Q.mapIso
        (Stacks.SheafOfModules.restrictComplexAlongOverIso
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom K) ≪≫
        hrepr Z.left
  refine ⟨fun {Z} p => ∃ (V : X.C) (f : V ⟶ U) (hf : S f) (g : Z ⟶ V),
    (key V (hdata f hf)).choose g ∧ p = g ≫ f, ?_, ?_⟩
  · refine X.J.transitive hS _ ?_
    rintro Z p ⟨V, a, f, hf, rfl⟩
    refine X.J.superset_covering ?_ (X.J.pullback_stable a (key V (hdata f hf)).choose_spec.1)
    rintro Y k ⟨Y', b, g, hg, hbg⟩
    exact ⟨Y', b, g ≫ f, ⟨V, f, hf, g, hg, rfl⟩, by rw [← Category.assoc, hbg, Category.assoc]⟩
  · rintro W p ⟨V, f, hf, g, hg, rfl⟩
    exact (key V (hdata f hf)).choose_spec.2 g hg

end Main

end AlgebraicGeometry.RingedSite

end
