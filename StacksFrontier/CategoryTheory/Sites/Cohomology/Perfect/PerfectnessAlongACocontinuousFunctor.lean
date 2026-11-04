module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.BoundedLocalApproximationsGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalNatureAnySite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.LocalNatureGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.PerfectnessAlongAnExactFunctor

/-!
# Perfectness along a restriction functor, and its descent along a covering family

Let `(C, O)` and `(D, O')` be ringed sites, with independent object and morphism universes.
This file proves two transfer principles for perfect objects of the derived categories.

* **Restriction.**  Let `v : C ⥤ D` be cocontinuous and let `F : Mod(O') ⥤ Mod(O)` be an exact
  additive functor which, over every object `W` of `C`, is an exact functor
  `G_W : Mod(O'|_{v W}) ⥤ Mod(O|_W)` carrying the unit to the unit applied to the restriction to
  `v W`.  Then `F` carries perfect objects of `D(O')` to perfect objects of `D(O)`.  This is the
  shape of the pullback of modules along an étale morphism of algebraic spaces, where `v` is
  postcomposition of étale charts and `G_W` is the comparison of slices of Stacks 04M0.
* **Descent.**  Let `v_i : D_i ⥤ C` be continuous functors whose images cover the final object of
  `C`, let `F_i : Mod(O) ⥤ Mod(O_i)` be exact, and suppose that over every object `W` of `D_i`
  an exact functor `H_{i,W} : Mod(O_i|_W) ⥤ Mod(O|_{v_i W})` carrying the unit to the unit
  recovers the restriction of a module to `v_i W` from the restriction of its image under `F_i`
  to `W`.  If every `F_i E` is perfect then `E` is perfect.  This is the statement that
  perfectness on an algebraic space is local for the étale topology.

The first principle differs from
`AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory`, which needs a functor between the
sites in the direction of `F` and whose images cover the final object: a restriction functor
comes with a functor of sites in the opposite direction, and cocontinuity replaces the covering
hypothesis.  The second principle rests on Stacks 08G6 (1) at independent universes,
`AlgebraicGeometry.RingedSite.isPerfect_of_forall_coveringFamily_strictlyPerfect_general`.

## Main results

* `AlgebraicGeometry.RingedSite.isPerfect_mapDerivedCategory_of_isCocontinuous_of_sliceFunctors`:
  restriction.
* `AlgebraicGeometry.RingedSite.isPerfect_of_forall_isPerfect_mapDerivedCategory`: descent.

## References

* [Stacks Project, Tag 08G5](https://stacks.math.columbia.edu/tag/08G5)
* [Stacks Project, Tag 08G6](https://stacks.math.columbia.edu/tag/08G6)
* [Stacks Project, Tag 04M0](https://stacks.math.columbia.edu/tag/04M0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe uX vX uY vY w dX dY t u₀ v₀

namespace AlgebraicGeometry.RingedSite

attribute [local instance] overMapLimits overMapColimits

/-- Restriction to a slice preserves finite limits. -/
local instance perfCocontOverFunctorLimits {C : Type u₀} [Category.{v₀} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] (V : C) :
    PreservesFiniteLimits (SheafOfModules.overFunctor.{w} R V) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteLimits V

/-- Restriction to a slice preserves finite colimits. -/
local instance perfCocontOverFunctorColimits {C : Type u₀} [Category.{v₀} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : C, HasSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}] (V : C) :
    PreservesFiniteColimits (SheafOfModules.overFunctor.{w} R V) :=
  Stacks.SheafOfModules.LocalCokernel.overFunctor_preservesFiniteColimits V

/-! ### Derived models -/

section DerivedModel

variable (X : RingedSite.{uX, vX, w})
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [hDX : ∀ U : X.C, HasDerivedCategory.{dX}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]

/-- The datum that Stacks 08G6 (1) asks for over one object `V`: a strictly perfect complex on the
slice over `V` isomorphic, in `D(O|_V)`, to the restriction of `E`. -/
def HasStrictlyPerfectDerivedModel
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (V : X.C) : Prop :=
  ∃ P : CochainComplex (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V)) ℤ,
    IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over V) P ∧
      Nonempty (DerivedCategory.Q.obj P ≅
        (SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
          V).mapDerivedCategory.obj E)

/-- **A derived model descends along an arrow of the site.**  Restriction along `k : V ⟶ A` is
exact and carries strictly perfect complexes to strictly perfect complexes, and restricting the
restriction of `E` to `A` along `k` is the restriction of `E` to `V`. -/
theorem hasStrictlyPerfectDerivedModel_of_hom
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {A V : X.C} (k : V ⟶ A) (h : X.HasStrictlyPerfectDerivedModel E A) :
    X.HasStrictlyPerfectDerivedModel E V := by
  obtain ⟨P, hP, ⟨e⟩⟩ := h
  let R := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  let Om := SheafOfModules.overMap.{w} R k
  obtain ⟨K, eK⟩ : Σ' K : CochainComplex (SheafOfModules.{w} R) ℤ, DerivedCategory.Q.obj K ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  let oA := SheafOfModules.overFunctor.{w} R A
  let oV := SheafOfModules.overFunctor.{w} R V
  -- `E|_A` and `E|_V` read on the representative `K`.
  let rA : DerivedCategory.Q.obj ((oA.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      oA.mapDerivedCategory.obj E :=
    (oA.mapDerivedCategoryFactors.app K).symm ≪≫ oA.mapDerivedCategory.mapIso eK
  let rV : DerivedCategory.Q.obj ((oV.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      oV.mapDerivedCategory.obj E :=
    (oV.mapDerivedCategoryFactors.app K).symm ≪≫ oV.mapDerivedCategory.mapIso eK
  refine ⟨(Om.mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    Stacks.SheafOfModules.isStrictlyPerfect_restrictComplexAlong_general R k hP, ⟨?_⟩⟩
  exact (Om.mapDerivedCategoryFactors.app P).symm ≪≫ Om.mapDerivedCategory.mapIso (e ≪≫ rA.symm) ≪≫
    Om.mapDerivedCategoryFactors.app _ ≪≫
    DerivedCategory.Q.mapIso ((Stacks.SheafOfModules.overFunctorMapComplexIso R k).app K) ≪≫ rV

/-- A strictly perfect quasi-isomorphic model of the restriction of a representative is a derived
model. -/
theorem hasStrictlyPerfectDerivedModel_of_hasStrictlyPerfectQuasiIso
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ)
    (V : X.C) (h : X.HasStrictlyPerfectQuasiIso K V) :
    X.HasStrictlyPerfectDerivedModel (DerivedCategory.Q.obj K) V := by
  obtain ⟨P, hP, q, hq⟩ := h
  have : IsIso (DerivedCategory.Q.map q) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := q)).2 hq
  exact ⟨P, hP, ⟨asIso (DerivedCategory.Q.map q) ≪≫
    ((SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
      V).mapDerivedCategoryFactors.app K).symm⟩⟩

end DerivedModel

/-! ### Restriction along a cocontinuous functor -/

section Restriction

variable {X : RingedSite.{uX, vX, w}} {Y : RingedSite.{uY, vY, w}}
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ W : Y.C, HasSheafify (Y.J.over W) AddCommGrpCat.{w}]
  [∀ W : Y.C, (Y.J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]

variable (v : X.C ⥤ Y.C)
  (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⥤
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) [F.Additive]
  (G : ∀ W : X.C, SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj W)) ⥤
    SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))

/-- **A strictly perfect local model over `v W` gives one over `W`.**  Apply `G_W` degreewise:
strict perfectness is preserved because `G_W` is additive, right exact and carries the unit to
the unit, the quasi-isomorphism because `G_W` is exact, and the target is identified with the
restriction of `F K` to `W` by the square. -/
theorem hasStrictlyPerfectQuasiIso_map_of_square_of_sliceFunctors (W : X.C) [(G W).Additive]
    [PreservesFiniteLimits (G W)] [PreservesFiniteColimits (G W)]
    (ηG : (G W).obj (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj W))) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))
    (sq : SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (v.obj W) ⋙
        G W ≅
      F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W)
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (h : Y.HasStrictlyPerfectQuasiIso K (v.obj W)) :
    X.HasStrictlyPerfectQuasiIso ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) W := by
  obtain ⟨P, hP, q, hq⟩ := h
  have hSP : IsStrictlyPerfect ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)
      (((G W).mapHomologicalComplex (ComplexShape.up ℤ)).obj P) :=
    SheafOfModules.isStrictlyPerfect_map.{max uY vY, max uX vX, vY, vX, w} (G W) ηG hP
  let hcmp : ((G W).mapHomologicalComplex (ComplexShape.up ℤ)).obj (Y.restrictComplex K (v.obj W)) ≅
      X.restrictComplex ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) W :=
    (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex sq (ComplexShape.up ℤ) ≪≫
      (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ)).symm).app K
  have := hq
  exact ⟨_, hSP, ((G W).mapHomologicalComplex (ComplexShape.up ℤ)).map q ≫ hcmp.hom,
    inferInstance⟩

/-- **Perfectness of complexes transfers along a restriction functor.**  If `K` is a perfect
complex of `O'`-modules and `v` is cocontinuous, then `F K` is a perfect complex of `O`-modules:
over an object `W` of `C`, a covering of `v W` carrying local models pulls back along `v` to a
covering of `W`, and over each of its members the model descends and is carried across by
`G`. -/
theorem isPerfectComplex_mapHomologicalComplex_of_isCocontinuous_of_sliceFunctors
    [v.IsCocontinuous X.J Y.J]
    [∀ W : X.C, (G W).Additive]
    [∀ W : X.C, PreservesFiniteLimits (G W)]
    [∀ W : X.C, PreservesFiniteColimits (G W)]
    (ηG : ∀ W : X.C, (G W).obj (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj W))) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))
    (sq : ∀ W : X.C,
      SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (v.obj W) ⋙ G W ≅
        F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W)
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ)
    (hK : Y.IsPerfectComplex K) :
    X.IsPerfectComplex ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) := by
  rw [isPerfectComplex_iff]
  intro W
  obtain ⟨S', hS', hmod⟩ := hK (v.obj W)
  refine ⟨(Sieve.functorPullback v (Sieve.generate S')).arrows, ?_, ?_⟩
  · rw [Sieve.generate_sieve]
    exact v.cover_lift X.J Y.J hS'
  · rintro W' g ⟨Z, h, s, hs, -⟩
    exact hasStrictlyPerfectQuasiIso_map_of_square_of_sliceFunctors v F G W' (ηG W') (sq W') K
      (hasStrictlyPerfectQuasiIso_of_hom Y K h (hmod s hs))

variable [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dY} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **Perfectness in the derived category transfers along a restriction functor.**  If `E` is a
perfect object of `D(O')` then `F.mapDerivedCategory.obj E` is a perfect object of `D(O)`. -/
theorem isPerfect_mapDerivedCategory_of_isCocontinuous_of_sliceFunctors
    [v.IsCocontinuous X.J Y.J]
    [∀ W : X.C, (G W).Additive]
    [∀ W : X.C, PreservesFiniteLimits (G W)]
    [∀ W : X.C, PreservesFiniteColimits (G W)]
    (ηG : ∀ W : X.C, (G W).obj (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).over (v.obj W))) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W))
    (sq : ∀ W : X.C,
      SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) (v.obj W) ⋙ G W ≅
        F ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W)
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hE : Y.IsPerfect E) :
    X.IsPerfect (F.mapDerivedCategory.obj E) := by
  obtain ⟨K, hK, ⟨e⟩⟩ := hE
  exact ⟨(F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K,
    isPerfectComplex_mapHomologicalComplex_of_isCocontinuous_of_sliceFunctors v F G ηG sq K hK,
    ⟨(F.mapDerivedCategoryFactors.app K).symm ≪≫ F.mapDerivedCategory.mapIso e⟩⟩

end Restriction

/-! ### Descent along a covering family -/

section Descent

variable {X : RingedSite.{uX, vX, w}} {ι : Type t} {Y : ι → RingedSite.{uY, vY, w}}
  [∀ U : X.C, HasSheafify (X.J.over U) AddCommGrpCat.{w}]
  [∀ U : X.C, (X.J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ i, ∀ W : (Y i).C, HasSheafify ((Y i).J.over W) AddCommGrpCat.{w}]
  [∀ i, ∀ W : (Y i).C, ((Y i).J.over W).WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [∀ i, HasSheafify (Y i).J AddCommGrpCat.{w}]
  [∀ i, (Y i).J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasDerivedCategory.{dX} (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [hDX : ∀ U : X.C, HasDerivedCategory.{dX}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over U))]
  [∀ i, HasDerivedCategory.{dY}
    (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (Y i).O))]
  [∀ i, ∀ W : (Y i).C, HasDerivedCategory.{dY}
    (SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (Y i).O).over W))]

variable (v : ∀ i, (Y i).C ⥤ X.C)
  (F : ∀ i, SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⥤
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (Y i).O))
  [∀ i, (F i).Additive] [∀ i, PreservesFiniteLimits (F i)] [∀ i, PreservesFiniteColimits (F i)]
  (H : ∀ i, ∀ W : (Y i).C,
    SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf (Y i).O).over W) ⥤
      SheafOfModules.{w} ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((v i).obj W)))
  [∀ i W, (H i W).Additive] [∀ i W, PreservesFiniteLimits (H i W)]
  [∀ i W, PreservesFiniteColimits (H i W)]

/-- **A local model on `Y_i` over `W` gives a derived model of `E` over `v_i W`.** -/
theorem hasStrictlyPerfectDerivedModel_of_square (i : ι) (W : (Y i).C)
    (ηH : (H i W).obj (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (Y i).O).over W)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((v i).obj W)))
    (sq : F i ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (Y i).O) W ⋙
        H i W ≅
      SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((v i).obj W))
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (K : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (Y i).O)) ℤ)
    (θ : DerivedCategory.Q.obj K ≅ (F i).mapDerivedCategory.obj E)
    (h : (Y i).HasStrictlyPerfectQuasiIso K W) :
    X.HasStrictlyPerfectDerivedModel E ((v i).obj W) := by
  obtain ⟨P, hP, q, hq⟩ := h
  let RX := Stacks.SheafOfModules.Tensor.ringSheaf X.O
  let RY := Stacks.SheafOfModules.Tensor.ringSheaf (Y i).O
  let Hc := (H i W).mapHomologicalComplex (ComplexShape.up ℤ)
  let oW := SheafOfModules.overFunctor.{w} RY W
  let oV := SheafOfModules.overFunctor.{w} RX ((v i).obj W)
  obtain ⟨L, eL⟩ : Σ' L : CochainComplex (SheafOfModules.{w} RX) ℤ, DerivedCategory.Q.obj L ≅ E :=
    ⟨DerivedCategory.Q.objPreimage E, DerivedCategory.Q.objObjPreimageIso E⟩
  -- `K` and `F L` represent the same object of `D(O_i)`.
  let θ' : DerivedCategory.Q.obj K ≅
      DerivedCategory.Q.obj (((F i).mapHomologicalComplex (ComplexShape.up ℤ)).obj L) :=
    θ ≪≫ (F i).mapDerivedCategory.mapIso eL.symm ≪≫ (F i).mapDerivedCategoryFactors.app L
  -- Restrict that comparison to `W` and carry it across by `H`.
  let θW : DerivedCategory.Q.obj ((oW.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≅
      DerivedCategory.Q.obj ((oW.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((F i).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) :=
    (oW.mapDerivedCategoryFactors.app K).symm ≪≫ oW.mapDerivedCategory.mapIso θ' ≪≫
      oW.mapDerivedCategoryFactors.app _
  let θH : DerivedCategory.Q.obj (Hc.obj ((oW.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)) ≅
      DerivedCategory.Q.obj (Hc.obj ((oW.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((F i).mapHomologicalComplex (ComplexShape.up ℤ)).obj L))) :=
    ((H i W).mapDerivedCategoryFactors.app _).symm ≪≫ (H i W).mapDerivedCategory.mapIso θW ≪≫
      (H i W).mapDerivedCategoryFactors.app _
  -- The square, read on complexes.
  let sqc : Hc.obj ((oW.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (((F i).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) ≅
      (oV.mapHomologicalComplex (ComplexShape.up ℤ)).obj L :=
    ((Functor.isoWhiskerLeft ((F i).mapHomologicalComplex (ComplexShape.up ℤ))
        (Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ))) ≪≫
      Functor.mapHomologicalComplexCompIso (Iso.refl _) (ComplexShape.up ℤ) ≪≫
      NatIso.mapHomologicalComplex sq (ComplexShape.up ℤ)).app L
  have hqH : QuasiIso (Hc.map q) := by
    have := hq
    have : (H i W).PreservesHomology := Functor.preservesHomologyOfExact _
    infer_instance
  have : IsIso (DerivedCategory.Q.map (Hc.map q)) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso (φ := Hc.map q)).2 hqH
  refine ⟨Hc.obj P, SheafOfModules.isStrictlyPerfect_map.{max uY vY, max uX vX, vY, vX, w}
    (H i W) ηH hP, ⟨?_⟩⟩
  exact asIso (DerivedCategory.Q.map (Hc.map q)) ≪≫ θH ≪≫ DerivedCategory.Q.mapIso sqc ≪≫
    (oV.mapDerivedCategoryFactors.app L).symm ≪≫ oV.mapDerivedCategory.mapIso eL

/-- **Perfectness descends along a covering family of exact restriction functors.**  Let
`v_i : D_i ⥤ C` be continuous functors whose images jointly cover the final object of `C`, and
let `F_i : Mod(O) ⥤ Mod(O_i)` be exact functors such that over every object `W` of `D_i` an
exact functor `H_{i,W}` carrying the unit to the unit recovers the restriction of a module to
`v_i W` from the restriction of its image under `F_i` to `W`.  An object `E` of `D(O)` whose
images `F_i E` are all perfect is perfect. -/
theorem isPerfect_of_forall_isPerfect_mapDerivedCategory
    [∀ i, (v i).IsContinuous (Y i).J X.J]
    (hTop : X.J.CoversTop (fun p : Σ i, (Y i).C => (v p.1).obj p.2))
    (ηH : ∀ i W, (H i W).obj (SheafOfModules.unit
        ((Stacks.SheafOfModules.Tensor.ringSheaf (Y i).O).over W)) ≅
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over ((v i).obj W)))
    (sq : ∀ i W,
      F i ⋙ SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf (Y i).O) W ⋙
        H i W ≅
      SheafOfModules.overFunctor.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ((v i).obj W))
    (E : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hE : ∀ i, (Y i).IsPerfect ((F i).mapDerivedCategory.obj E)) :
    X.IsPerfect E := by
  choose K hK θ using hE
  -- The objects `v_i W` over which a local model of `K_i` exists cover the final object.
  have hcov : X.J.CoversTop
      (fun p : Σ i, {W : (Y i).C // (Y i).HasStrictlyPerfectQuasiIso (K i) W} =>
        (v p.1).obj p.2.1) := by
    intro U
    apply X.J.transitive (hTop U)
    rintro V g ⟨⟨i, W⟩, ⟨k⟩⟩
    obtain ⟨S, hS, hpS⟩ := hK i W
    apply X.J.superset_covering _ (X.J.pullback_stable k
      ((CoverPreserving.of_isContinuous (v i) (Y i).J X.J).cover_preserve hS))
    rintro Z q ⟨A, a, b, ⟨A', l, a', ha', -⟩, -⟩
    exact ⟨⟨i, A', hpS a' ha'⟩, ⟨b ≫ (v i).map l⟩⟩
  refine isPerfect_of_forall_coveringFamily_strictlyPerfect_general X E fun U => ?_
  refine ⟨(Sieve.ofObjects _ U).arrows, by rw [Sieve.generate_sieve]; exact hcov U, ?_⟩
  rintro V g ⟨⟨i, W, hW⟩, ⟨k⟩⟩
  exact hasStrictlyPerfectDerivedModel_of_hom X E k
    (hasStrictlyPerfectDerivedModel_of_square v F H i W (ηH i W) (sq i W) E (K i) (θ i).some hW)

end Descent

end AlgebraicGeometry.RingedSite

end
