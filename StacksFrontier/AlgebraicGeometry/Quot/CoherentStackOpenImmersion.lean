module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStack
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionFactorizationLocus

/-!
# An open immersion is open on the stacks of coherent sheaves

Let `B` be an algebraic space and let `π : X ⟶ Y` be an open immersion of algebraic spaces
separated and of finite presentation over `B`. For an object `(T, g, F)` of `Coh_{Y/B}`, the points
`t ∈ T` with `Supp(F_t) ⊆ |X_t|` form an open subspace `W ⊆ T`, and a morphism `T' ⟶ T` factors
through `W` exactly when the base change of `Supp(F)` to `T'` lands in `X_{T'}`. This is the
geometric content of the assertion that `Coh_{X/B} ⟶ Coh_{Y/B}` is an open immersion; the
morphism of stacks itself is not constructed here.

## Main definitions

* `AlgebraicGeometry.Space.CoherentSituation.baseChangeOfMap`: the base change
  `π_T : X_T ⟶ Y_T` of `π` to a test scheme over the base.
* `AlgebraicGeometry.Space.CoherentSituation.supportSubspace`: the reduced induced closed
  subspace of `Y_T` supported on the support of the module of an object of `Coh_{Y/B}`.
* `AlgebraicGeometry.Space.CoherentSituation.supportFactorizationLocus`: the locus `W ⊆ T`
  above which that support lands in `X_T`.

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.isOpenImmersion_baseChangeOfMap`: the base change
  of `π` to a test scheme over the base is an open immersion.
* `AlgebraicGeometry.Space.CoherentSituation.isClosedMorphism_supportSubspace`: the structure
  morphism `Supp(F) ⟶ T` of the support of the module of an object of `Coh_{Y/B}` is closed.
* `AlgebraicGeometry.Space.CoherentSituation.mem_supportFactorizationLocus_iff`: the locus read
  on points: a point `t` of `T` lies in it exactly when every point of `Supp(F)` above `t`
  lies in `X_T`.
* `AlgebraicGeometry.Space.CoherentSituation.isOpenSubspace_supportFactorizationLocus`: the
  locus is an open subspace of `T`.
* `AlgebraicGeometry.Space.CoherentSituation.factorsThrough_supportFactorizationLocus_iff`: a
  test object `T' ⟶ T` factors through the locus exactly when the base change of the support
  lands in `X_{T'}`.

## References

* [Stacks Project, Tag 0DNA](https://stacks.math.columbia.edu/tag/0DNA)
* [Stacks Project, Tag 0DN9](https://stacks.math.columbia.edu/tag/0DN9)
* [Stacks Project, Tag 0DPE](https://stacks.math.columbia.edu/tag/0DPE)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace CoherentSituation

variable (D : CoherentSituation B S hS) {X : AlgebraicSpaces B S hS}
    {π : X ⟶ D.X} {bX : X ⟶ D.Y}

/-! ### The base change of the open immersion to a test scheme -/

/-- The base change `π_T : X_T ⟶ Y_T` of a morphism `π : X ⟶ Y` over the base `B` of the
standing data `D` to a test scheme `T` over `B`. -/
def baseChangeOfMap (hπ : π ≫ D.f = bX) (T : SchemesOver D.Y) :
    baseChangeSpace bX T ⟶ D.space T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom).lift
    (baseChangeProjection bX T ≫ π) (baseChangeInclusion bX T) (by
      rw [Category.assoc, hπ]
      exact (AlgebraicSpaces.isPullback_fiberProduct B S hS bX T.hom).w)

/-- The composite of `π_T : X_T ⟶ Y_T` with the projection `Y_T ⟶ Y` is the composite of the
projection `X_T ⟶ X` with `π`. -/
@[reassoc (attr := simp)]
theorem baseChangeOfMap_comp_projection (hπ : π ≫ D.f = bX) (T : SchemesOver D.Y) :
    baseChangeOfMap D hπ T ≫ baseChangeProjection D.f T = baseChangeProjection bX T ≫ π :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom).lift_fst _ _ _

/-- The composite of `π_T : X_T ⟶ Y_T` with the map `Y_T ⟶ T` is the map `X_T ⟶ T`. -/
@[reassoc (attr := simp)]
theorem baseChangeOfMap_comp_inclusion (hπ : π ≫ D.f = bX) (T : SchemesOver D.Y) :
    baseChangeOfMap D hπ T ≫ D.projection T = baseChangeInclusion bX T :=
  (AlgebraicSpaces.isPullback_fiberProduct B S hS D.f T.hom).lift_snd _ _ _

/-- `X_T` is the fibre product of `Y_T` and `X` over `Y`: the base change of a morphism over the
base is a base change in the strict sense. -/
theorem isPullback_baseChangeOfMap (hπ : π ≫ D.f = bX) (T : SchemesOver D.Y) :
    IsPullback (baseChangeOfMap D hπ T).hom (baseChangeProjection bX T).hom
      (baseChangeProjection D.f T).hom π.hom := by
  have hsnd : (baseChangeOfMap D hπ T).hom ≫ (D.projection T).hom =
      (baseChangeInclusion bX T).hom :=
    congrArg (fun m ↦ m.hom) (baseChangeOfMap_comp_inclusion D hπ T)
  have outer : IsPullback ((baseChangeOfMap D hπ T).hom ≫ (D.projection T).hom)
      (baseChangeProjection bX T).hom T.hom.hom (π.hom ≫ D.f.hom) := by
    rw [hsnd, show π.hom ≫ D.f.hom = bX.hom from congrArg (fun m ↦ m.hom) hπ]
    exact (IsPullback.of_hasPullback bX.hom T.hom.hom).flip
  exact outer.of_right (congrArg (fun m ↦ m.hom) (baseChangeOfMap_comp_projection D hπ T))
    (IsPullback.of_hasPullback D.f.hom T.hom.hom).flip

/-- The base change of an open immersion over the base to a test scheme is an open
immersion. -/
theorem isOpenImmersion_baseChangeOfMap (hπ : π ≫ D.f = bX)
    (hopen : IsOpenImmersion B S hS π.hom) (T : SchemesOver D.Y) :
    IsOpenImmersion B S hS (baseChangeOfMap D hπ T).hom := by
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange _
  exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_baseChangeOfMap D hπ T).flip hopen

/-! ### The support of the module of an object, as a closed subspace proper over the base -/

/-- The support of the module of an object of `Coh_{Y/B}` is a closed subset of `|Y_T|`. -/
theorem isClosed_support (obj : CoherentObject D) : IsClosed (D.support obj.T obj.F) :=
  obj.properSupport.snd.fst

/-- The reduced induced closed subspace of `Y_T` supported on the support of the module of an
object of `Coh_{Y/B}`. -/
abbrev supportSubspace (obj : CoherentObject D) (hU : IsClosed (D.support obj.T obj.F)) :
    Subfunctor (D.space obj.T).1 :=
  reducedClosedSubspace B S hS (D.space obj.T).1 (D.space obj.T).2
    (D.support obj.T obj.F) hU

/-- The support subspace of the module of an object of `Coh_{Y/B}` is proper over the test
scheme. -/
theorem isProper_supportSubspace (obj : CoherentObject D)
    (hU : IsClosed (D.support obj.T obj.F)) :
    IsProper B S hS ((supportSubspace D obj hU).ι ≫ (D.projection obj.T).hom) :=
  obj.properSupport.snd.snd

/-- The structure morphism `Supp(F) ⟶ T` of the support subspace is closed. -/
theorem isClosedMorphism_supportSubspace (obj : CoherentObject D)
    (hU : IsClosed (D.support obj.T obj.F)) :
    IsClosedMorphism B S hS ((supportSubspace D obj hU).ι ≫ (D.projection obj.T).hom) :=
  isClosed_of_universallyClosed B S hS
    ((schemeSpaceFunctor B S hS).obj obj.T.left).2 _
    (isProper_supportSubspace D obj hU).universallyClosed

/-! ### The locus above which the support lands in the open subspace -/

/-- The locus `W ⊆ T` above which the support of the module of an object of `Coh_{Y/B}` lands in
the open subspace `X_T ⊆ Y_T`. -/
def supportFactorizationLocus (hπ : π ≫ D.f = bX) (obj : CoherentObject D)
    (hU : IsClosed (D.support obj.T obj.F)) :
    Subfunctor ((schemeSpaceFunctor B S hS).obj obj.T.left).1 :=
  factorizationLocus B S hS (baseChangeOfMap D hπ obj.T).hom (supportSubspace D obj hU).ι
    ((supportSubspace D obj hU).ι ≫ (D.projection obj.T).hom)

/-- A point `t` of `T` lies in the locus exactly when every point of `Supp(F)` lying over `t`
lies in `X_T`. -/
theorem mem_supportFactorizationLocus_iff (hπ : π ≫ D.f = bX) (obj : CoherentObject D)
    (hU : IsClosed (D.support obj.T obj.F))
    (t : points B S hS ((schemeSpaceFunctor B S hS).obj obj.T.left).1) :
    t ∈ Set.range (pointsMap B S hS (supportFactorizationLocus D hπ obj hU).toFunctor
        (supportFactorizationLocus D hπ obj hU).ι) ↔
      ∀ z : points B S hS (supportSubspace D obj hU).toFunctor,
        pointsMap B S hS _ ((supportSubspace D obj hU).ι ≫ (D.projection obj.T).hom) z = t →
          pointsMap B S hS _ (supportSubspace D obj hU).ι z ∈
            Set.range (pointsMap B S hS (baseChangeSpace bX obj.T).1
              (baseChangeOfMap D hπ obj.T).hom) := by
  rw [supportFactorizationLocus, range_pointsMap_ι_factorizationLocus]
  exact ⟨fun h z hz ↦ by_contra fun hn ↦ h ⟨z, hn, hz⟩, fun h ⟨z, hz, hzt⟩ ↦ hz (h z hzt)⟩

/-- For an object `(T, g, F)` of `Coh_{Y/B}` the locus in `T` above which `Supp(F)` lands in
the open subspace `X_T ⊆ Y_T` is an open subspace of `T`. -/
@[stacks 0DNA "an ingredient only: the open locus of the source's hint, namely the locus in T \
above which Supp(F) lands in X_T.  The conclusion itself is not stated, the 1-morphism \
Coh_{X/B} ⟶ Coh_{Y/B} of 0DN9 not being constructed in this development"]
theorem isOpenSubspace_supportFactorizationLocus (hπ : π ≫ D.f = bX)
    (hopen : IsOpenImmersion B S hS π.hom) (obj : CoherentObject D)
    (hU : IsClosed (D.support obj.T obj.F)) :
    IsOpenSubspace B S hS (supportFactorizationLocus D hπ obj hU) :=
  isOpenSubspace_factorizationLocus B S hS
    ((schemeSpaceFunctor B S hS).obj obj.T.left).2
    (isOpenImmersion_baseChangeOfMap D hπ hopen obj.T) _
    (isClosedMorphism_supportSubspace D obj hU)

/-- A morphism `T' ⟶ T` from an algebraic space factors through the locus exactly when the
base change of `Supp(F)` to `T'` lands in `X_T`. -/
@[stacks 0DNA "an ingredient only: the universal property of that locus, a test object \
factoring through it exactly when the base change of Supp(F) lands in X_T.  The residues are the \
1-morphism of 0DN9 and the algebraicity of Coh of 09DS"]
theorem factorsThrough_supportFactorizationLocus_iff (hπ : π ≫ D.f = bX)
    (hopen : IsOpenImmersion B S hS π.hom) (obj : CoherentObject D)
    (hU : IsClosed (D.support obj.T obj.F))
    {T' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hT' : IsAlgebraicSpace B S hS T')
    (g : T' ⟶ ((schemeSpaceFunctor B S hS).obj obj.T.left).1) :
    (∃ l : T' ⟶ (supportFactorizationLocus D hπ obj hU).toFunctor,
        l ≫ (supportFactorizationLocus D hπ obj hU).ι = g) ↔
      ∃ l : pullback ((supportSubspace D obj hU).ι ≫ (D.projection obj.T).hom) g ⟶
          (baseChangeSpace bX obj.T).1,
        l ≫ (baseChangeOfMap D hπ obj.T).hom =
          pullback.fst ((supportSubspace D obj hU).ι ≫ (D.projection obj.T).hom) g ≫
            (supportSubspace D obj hU).ι :=
  factorsThrough_factorizationLocus_iff B S hS (baseChangeSpace bX obj.T).2
    (D.space obj.T).2
    (isClosedSubspace_reducedClosedSubspace B S hS (D.space obj.T).1 (D.space obj.T).2
      (D.support obj.T obj.F) hU).1
    ((schemeSpaceFunctor B S hS).obj obj.T.left).2
    (isOpenImmersion_baseChangeOfMap D hπ hopen obj.T) _
    (isClosedMorphism_supportSubspace D obj hU) hT' g

end CoherentSituation

end AlgebraicGeometry.Space

end
