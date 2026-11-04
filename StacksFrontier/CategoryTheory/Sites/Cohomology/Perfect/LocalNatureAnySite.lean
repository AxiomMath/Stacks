module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalModelsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.LocalNature
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.LocallyFiniteTorDimension

/-!
# Perfectness of a derived object is local on the site, on a site of any size

Let `(C, O)` be a ringed site and let `E` be an object of `D(O)`. If every object `U` of `C`
admits a covering `{V → U}` such that each restriction `E|_V` is perfect on the localized ringed
site `(C/V, O|_V)`, then `E` is itself perfect. This is the local-to-global half of Stacks 08G5
read through the local models of Stacks 08G6, part (1), with the objects of the site, its
morphisms and the sections of its structure sheaf in three independent universes.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_of_locally_anySite`: perfectness descends along a
  covering.  `AlgebraicGeometry.RingedSite.isPerfect_of_locally_general` is the case where the
  objects and the morphisms of the site share a universe.

## Implementation notes

`AlgebraicGeometry.RingedSite.isPerfect_of_locally` is this statement with the objects of the
site tied to its morphisms and the sections of the structure sheaf pinned to `Type`. Both
restrictions were inherited rather than needed. The tie came from Stacks 08FR, which
`AlgebraicGeometry.RingedSite.exists_coveringSieve_complexMap_general` now carries at
independent universes, and with it
`AlgebraicGeometry.RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect_general`;
the pin to `Type` was never used by the argument at all. The proof below is the proof of the
pinned statement with the universes opened up, and the shape of the argument is still that of
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_of_locally_general`, Stacks 08FU part (3).

The hypothesis is a statement about the objects of the slices `C/V`, and it is used only at the
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

The motivating consumer is the small étale site of an algebraic space,
`AlgebraicGeometry.Space.smallEtaleRingedSite`, a `RingedSite.{u + 1, u, u}` whose objects are
étale morphisms to the space and so live one universe above the morphisms between them; neither
of the two restrictions of the pinned statement holds there.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 08FU](https://stacks.math.columbia.edu/tag/08FU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v w d

namespace AlgebraicGeometry.RingedSite

section Transfer

/-- **An exact functor carries a quasi-isomorphism to a quasi-isomorphism, up to a chosen
isomorphism of its target.** The quasi-isomorphism is an explicit hypothesis rather than an
instance: at the use site the source complex is written at one of the two spellings of the
structure sheaf of a slice and the functor at the other, and the two agree at default
transparency but not at the transparency typeclass synthesis uses. -/
private theorem quasiIsoMapCompIsoGeneral {A D : Type*} [Category A] [Abelian A] [Category D]
    [Abelian D] (T : A ⥤ D) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
    {K L : CochainComplex A ℤ} {M : CochainComplex D ℤ} (ψ : K ⟶ L)
    (ε : (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj L ≅ M) (hψ : QuasiIso ψ) :
    QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ ≫ ε.hom) := by
  have := hψ
  have : T.PreservesHomology := Functor.preservesHomologyOfExact T
  have : QuasiIso ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map ψ) := inferInstance
  have : IsIso ε.hom := ε.isIso_hom
  infer_instance

end Transfer

section GeneralUniverses

attribute [local instance] sliceHasSheafify sliceWEqualsLocallyBijective

local instance perfGenOvHasSheafifyIterAll (X : RingedSite.{u, v, w})
    [∀ (U : X.C) (W : Over U), HasSheafify ((X.J.over U).over W) AddCommGrpCat.{w}] (U : X.C) :
    ∀ W : (X.over U).C, HasSheafify ((X.over U).J.over W) AddCommGrpCat.{w} :=
  fun W => (inferInstance : ∀ (U : X.C) (W : Over U),
    HasSheafify ((X.J.over U).over W) AddCommGrpCat.{w}) U W

local instance perfGenOvWEqIterAll (X : RingedSite.{u, v, w})
    [∀ (U : X.C) (W : Over U),
      ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{w}] (U : X.C) :
    ∀ W : (X.over U).C, ((X.over U).J.over W).WEqualsLocallyBijective AddCommGrpCat.{w} :=
  fun W => (inferInstance : ∀ (U : X.C) (W : Over U),
    ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{w}) U W

-- Exactness of restriction to a slice and of restriction along an arrow of the site. These are
-- the universe-general local instances `ovFunctorLimits`, `ovFunctorColimits`, `overMapLimits`
-- and `overMapColimits` of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/LocalNature.lean`, whose
-- declarations are imported, so only the instance attribute is re-enabled here. The
-- `AddCommGrpCat.{0}` instances of
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/PseudoCoherent/BoundedLocalApproximations.lean`,
-- which the statement pinned to `Type` borrows, restate the same content for sections in
-- `Type`.
attribute [local instance] ovFunctorLimits ovFunctorColimits overMapLimits overMapColimits

/-- Transport of sheaves of modules from an iterated slice `(C/V)/Z` down to `C/Z.left`
preserves finite limits. This names the instance at the spelling of the arrow that the
descent argument below produces, `W.hom` for `W` an object of the slice: synthesizing the
sheafification hypotheses of
`Stacks.SheafOfModules.sliceBackward_preservesFiniteLimits` against the iterated-slice
hypotheses of this section is what costs, and here it is paid once. -/
private theorem perfGenSliceBackwardLimits (X : RingedSite.{u, v, w})
    [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ (U : X.C) (W : Over U), HasSheafify ((X.J.over U).over W) AddCommGrpCat.{w}]
    [∀ (U : X.C) (W : Over U),
      ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {V : X.C} (W : Over V) :
    PreservesFiniteLimits
      (Stacks.SheafOfModules.sliceBackward.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        W.hom) :=
  Stacks.SheafOfModules.sliceBackward_preservesFiniteLimits W.hom

/-- Transport of sheaves of modules from an iterated slice `(C/V)/Z` down to `C/Z.left`
preserves finite colimits, named at the same spelling and for the same reason as
`perfGenSliceBackwardLimits`. -/
private theorem perfGenSliceBackwardColimits (X : RingedSite.{u, v, w})
    [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ (U : X.C) (W : Over U), HasSheafify ((X.J.over U).over W) AddCommGrpCat.{w}]
    [∀ (U : X.C) (W : Over U),
      ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {V : X.C} (W : Over V) :
    PreservesFiniteColimits
      (Stacks.SheafOfModules.sliceBackward.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        W.hom) :=
  Stacks.SheafOfModules.sliceBackward_preservesFiniteColimits W.hom

/-- A strictly perfect complex on an iterated slice `(C/V)/Z` transports to a strictly perfect
complex on the slice `C/Z.left`, the transport being exact and matching up the two structure
sheaves. -/
private theorem perfGenIsStrictlyPerfectSliceBackward (X : RingedSite.{u, v, w})
    [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ (U : X.C) (W : Over U), HasSheafify ((X.J.over U).over W) AddCommGrpCat.{w}]
    [∀ (U : X.C) (W : Over U),
      ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
    {V : X.C} (W : Over V)
    {P : CochainComplex (SheafOfModules.{w}
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V).over (Over.mk W.hom))) ℤ}
    (hP : IsStrictlyPerfect
      (((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V).over (Over.mk W.hom)) P) :
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W.left)
      (((Stacks.SheafOfModules.sliceBackward.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
        W.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
  have : PreservesFiniteColimits (Stacks.SheafOfModules.sliceBackward.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W.hom) :=
    perfGenSliceBackwardColimits X W
  Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex _
    (Stacks.SheafOfModules.sliceBackwardUnitIso.{w} W.hom) hP


attribute [local instance] locallyOverRingSheafHasDerivedCategory ovHasDerived

/-- **Perfectness descends along a covering.** Let `E` be an object of `D(O)` and suppose that
every object `U` of `C` admits a covering `{V → U}` over each member of which the restriction
`E|_V` is perfect on the localized ringed site `(C/V, O|_V)`. Then `E` is perfect.

This is the local-to-global half of Stacks 08G5 read through the local models of Stacks 08G6,
part (1). -/
theorem isPerfect_of_locally_anySite (X : RingedSite.{u, v, w})
    [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
    [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ (U : X.C) (W : Over U), HasSheafify ((X.J.over U).over W) AddCommGrpCat.{w}]
    [∀ (U : X.C) (W : Over U),
      ((X.J.over U).over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasDerivedCategory.{d} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
    [∀ U : X.C, HasDerivedCategory.{d}
      (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (h : ∀ U : X.C, ∃ S : Presieve U, Sieve.generate S ∈ X.J U ∧
      ∀ ⦃V : X.C⦄ (f : V ⟶ U), S f →
        (X.over V).IsPerfect
          ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            V).mapDerivedCategory.obj E)) :
    X.IsPerfect E := by
  classical
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
  refine isPerfect_of_forall_coveringFamily_strictlyPerfect_general X E (fun U => ?_)
  obtain ⟨S, hS, hdata⟩ := h U
  have key : ∀ V : X.C,
      (X.over V).IsPerfect
        ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          V).mapDerivedCategory.obj E) →
      ∃ T : Presieve V, Sieve.generate T ∈ X.J V ∧
        ∀ ⦃W : X.C⦄ (g : W ⟶ V), T g →
          ∃ P : CochainComplex
              (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)) ℤ,
            IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W) P ∧
              Nonempty (DerivedCategory.Q.obj P ≅
                (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
                  W).mapDerivedCategory.obj E) := by
    intro V hV
    obtain ⟨Ecpx, hEcpx, ⟨eE⟩⟩ := hV
    have eE' : DerivedCategory.Q.obj (Ecpx : CochainComplex
        (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ) ≅
          DerivedCategory.Q.obj (X.restrictComplex K V) := eE ≪≫ (hrepr V).symm
    obtain ⟨S₁, hS₁, hdata₁⟩ := hEcpx (Over.mk (𝟙 V))
    refine ⟨Presieve.map (Over.forget V) S₁, ?_, ?_⟩
    · rw [Sieve.generate_map_eq_functorPushforward]
      exact hS₁
    · rintro W g @⟨Z, u, hv⟩
      obtain ⟨P, hP, q, hq⟩ := hdata₁ u hv
      let Om := SheafOfModules.overMap.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom
      let Sb :=
        Stacks.SheafOfModules.sliceBackward.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom
      let Sbc := Sb.mapHomologicalComplex (ComplexShape.up ℤ)
      have : PreservesFiniteLimits Sb := perfGenSliceBackwardLimits X Z
      have : PreservesFiniteColimits Sb := perfGenSliceBackwardColimits X Z
      have : Sb.PreservesHomology := Functor.preservesHomologyOfExact Sb
      let e₁ : Sbc.obj ((X.over V).restrictComplex Ecpx Z) ≅
          ((Om.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Ecpx : CochainComplex
            (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ)) :=
        (Stacks.SheafOfModules.sliceBackwardComplexIso.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O) Z.hom).app Ecpx
      let β := Sbc.map q ≫ e₁.hom
      have hβ : QuasiIso β := quasiIsoMapCompIsoGeneral Sb q e₁ hq
      have : IsIso (DerivedCategory.Q.map β) :=
        (DerivedCategory.isIso_Q_map_iff_quasiIso
          (C := SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over Z.left))
          β).2 hβ
      refine ⟨Sbc.obj P, perfGenIsStrictlyPerfectSliceBackward X Z hP, ⟨?_⟩⟩
      refine asIso (DerivedCategory.Q.map β) ≪≫ ?_
      refine (Om.mapDerivedCategoryFactors.app _).symm ≪≫ Om.mapDerivedCategory.mapIso eE' ≪≫ ?_
      refine Om.mapDerivedCategoryFactors.app _ ≪≫ ?_
      exact DerivedCategory.Q.mapIso
        (Stacks.SheafOfModules.restrictComplexAlongOverIsoGeneral
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

end GeneralUniverses

end AlgebraicGeometry.RingedSite

end
