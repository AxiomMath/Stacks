module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperFrobeniusLeray
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FrobeniusRestrictionQuasiIso
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.PullbackStalkFrobenius

/-!
# Fibres over rational points and stalks of inverse images to `Spec k`

Let `π : W' ⟶ W` be a morphism of schemes over a finite field `k` and `y : Spec k ⟶ W` a point.
This file sets up the fibre `W'_y = W' ×_W Spec k` as a scheme over `k`, with its projection to
`Spec k` (proper when `π` is), and proves the stalk side of the comparison of the local term of
`Rπ_* M` at `y` with the trace on the geometric fibre in the proof of [Stacks, Tag 03V3]: for a
complex `D` on `W` with perfect stalks, the local term at the unique rational point of `Spec k` of
`y⁻¹ D` is the local term `Tr(π_y | D_ȳ)` of `D` at `y`
(`Stacks.EtaleCohomology.rationalPointStalkPullbackIso`, compatible with the geometric Frobenius).

For `π` proper and `M` a bounded below complex of injectives, the local term of `Rπ_* M` at `y` is
then the trace of the geometric Frobenius on the cohomology of the geometric fibre: the dimension
zero trace formula on `Spec k` for `y⁻¹ π_* M`, proper base change along `y`
(`Stacks.EtaleCohomology.quasiIso_etaleModuleBaseChange_comp_of_isProper`) making
`y⁻¹ π_* M ⟶ (π_y)_* T` a quasi-isomorphism for an injective resolution `T` of `M|_{W'_y}`,
invariance of `T''` under quasi-isomorphism, and the Leray step along the proper morphism
`π_y : W'_y ⟶ Spec k`. This is the step `(Rf_! K)_ȳ = RΓ_c(X_ȳ, K)` of the reduction of
[Stacks, Tag 03V3] to curves.

The quasi-isomorphism produced by proper base change is consumed through the named predicate
`CategoryTheory.Functor.BaseChangeQuasiIsoAt`, by a lemma whose functors are variables: restating
it for the concrete étale functors makes the kernel compare two elaborations of the same morphism
of complexes, which unfolds the étale direct and inverse images.

The standard model `HasDerivedCategory.standard` is used because the traced objects are defined
there.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_rationalPointStalkFrobenius_inverseImage_point`: the
  stalk side, `Tr(π_pt | (y⁻¹ D)_pt) = Tr(π_y | D_ȳ)`.
* `Stacks.EtaleCohomology.rationalFibre`, `Stacks.EtaleCohomology.rationalFibreToPoint`: the fibre
  over a rational point and its proper projection to `Spec k`.
* `perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_baseChangeQuasiIsoAt`
  (`T''` transports along a base change quasi-isomorphism on resolutions).
* `Stacks.EtaleCohomology.perfectDerivedTrace_rationalPointStalkFrobenius_directImage_eq_fibre`:
  for `π` proper, `Tr(π_y | (Rπ_* M)_ȳ) = Tr(π_{W'_y}^* | RΓ((W'_y)_k̄, M|_{W'_y}))`.

## References

* [Stacks Project, Tag 03V3](https://stacks.math.columbia.edu/tag/03V3)
* [Stacks Project, Tag 0DDF](https://stacks.math.columbia.edu/tag/0DDF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.FilteredDerived Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme Stacks.Frobenius

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

attribute [local instance 10000] CategoryTheory.Abelian.toPreadditive
  Preadditive.preadditiveHasZeroMorphisms

variable {k : Type u} [Field k] [Fintype k]

/-- `Spec k` as a scheme over itself. -/
abbrev fieldPointOver (k : Type u) [Field k] : Over (Spec (.of k)) := Over.mk (𝟙 (Spec (.of k)))

/-- `Spec k` has exactly one `k`-rational point. -/
instance (k : Type u) [Field k] : Unique (rationalPoints (fieldPointOver k).hom) where
  default := ⟨𝟙 _, Category.id_comp _⟩
  uniq x := Subtype.ext ((Category.comp_id x.1).symm.trans x.2)

/-- The `k`-rational points of `Spec k` form a finite type. -/
instance (k : Type u) [Field k] : Fintype (rationalPoints (fieldPointOver k).hom) :=
  Fintype.ofFinite _

/-- The structure morphism of `Spec k` over itself is étale. -/
instance (k : Type u) [Field k] : Etale (fieldPointOver k).hom :=
  inferInstanceAs (Etale (𝟙 _))

/-- The structure morphism of `Spec k` over itself is finite. -/
instance (k : Type u) [Field k] : IsFinite (fieldPointOver k).hom :=
  inferInstanceAs (IsFinite (𝟙 _))

variable {W' W : Over (Spec (.of k))} (π : W' ⟶ W) (y : Spec (.of k) ⟶ W.left)

/-- The fibre `W'_y = W' ×_W Spec k` of `π` over a rational point `y`, as a scheme over `k`. -/
abbrev rationalFibre : Over (Spec (.of k)) := Over.mk (pullback.snd π.left y)

/-- The projection of the fibre to `Spec k`, as a morphism over `k`. -/
abbrev rationalFibreToPoint : rationalFibre π y ⟶ fieldPointOver k :=
  Over.homMk (pullback.snd π.left y) (Category.comp_id _)

/-- If `π` is proper, then the projection of the fibre `W'_y` to `Spec k` is proper. -/
instance [IsProper π.left] : IsProper (rationalFibreToPoint π y).left :=
  inferInstanceAs (IsProper (pullback.snd π.left y))

section Trace

variable (Λ : Type) [Ring Λ] [Finite Λ] (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (p q : ℕ) [Fact p.Prime] [CharP k p] [CharP kbar p]
  (hcard : Fintype.card k = p ^ q)

omit [Finite Λ] [CharP k p] in
/-- **The stalk at the rational point of `Spec k` of an inverse image along `y : Spec k ⟶ W`** is
the stalk at `ȳ`, compatibly with the geometric Frobenius: the traces agree. -/
theorem perfectDerivedTrace_rationalPointStalkFrobenius_inverseImage_point
    (D : CochainComplex.Plus (EtaleModules.{u, 0} Λ W.left))
    (hD : HasPerfectStalks Λ D)
    (hE : HasPerfectStalks Λ ((etaleModuleInverseImage.{u, 0} Λ y).mapCochainComplexPlus.obj D)) :
    perfectDerivedTrace.{0, u + 1} Λ ⟨_, hE (rationalGeometricPoint kbar (𝟙 (Spec (.of k))))⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard
          (𝟙 (Spec (.of k))) ((etaleModuleInverseImage.{u, 0} Λ y).mapCochainComplexPlus.obj D))) =
      perfectDerivedTrace.{0, u + 1} Λ ⟨_, hD (rationalGeometricPoint kbar y)⟩
        (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y D)) := by
  let e := rationalPointStalkPullbackIso Λ y kbar (𝟙 (Spec (.of k))) y (Category.id_comp y)
  let eC : rationalPointStalkComplex.{u, 0} Λ kbar (𝟙 (Spec (.of k)))
        ((etaleModuleInverseImage.{u, 0} Λ y).mapCochainComplexPlus.obj D) ≅
      rationalPointStalkComplex.{u, 0} Λ kbar y D :=
    HomologicalComplex.Hom.isoOfComponents (fun n => e.app (D.obj.X n))
      (fun a b _ => (e.hom.naturality (D.obj.d a b)).symm)
  refine perfectDerivedTrace_congr Λ _ _ (DerivedCategory.Q.mapIso eC) _ _ ?_
  have h : rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard (𝟙 (Spec (.of k)))
        ((etaleModuleInverseImage.{u, 0} Λ y).mapCochainComplexPlus.obj D) ≫ eC.hom =
      eC.hom ≫ rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y D := by
    ext n : 1
    exact geometricFrobeniusStalkFunctor_comp_rationalPointStalkPullbackIso_hom Λ y kbar
      (𝟙 (Spec (.of k))) y (Category.id_comp y) p q hcard (D.obj.X n)
  exact (DerivedCategory.Q.map_comp _ _).symm.trans ((congrArg DerivedCategory.Q.map h).trans
    (DerivedCategory.Q.map_comp _ _))

omit [Finite Λ] [IsAlgClosed kbar] [CharP kbar p] in
/-- **`T''` transports along a base change quasi-isomorphism on resolutions.**  Let
`βn : I ⋙ g ⟶ g' ⋙ G` be a natural transformation of functors between categories of sheaves of
`Λ`-modules, `g` landing on a scheme `Y` over `k`, and `M` a bounded below complex such that
`βn_M ≫ G(ψ)` is a quasi-isomorphism for every injective resolution `ψ : g'(M) ⟶ T`
(`CategoryTheory.Functor.BaseChangeQuasiIsoAt`; proper base change, in the application). Then
`RΓ(Y_k̄, -)` of `g(I(M))` and of `G(T)` are perfect together, with the same trace of the canonical
geometric Frobenius. The functors are variables, so that the kernel never unfolds the étale
functors they are instantiated with. -/
theorem perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_baseChangeQuasiIsoAt
    {X₁ X₂ Z : Scheme.{u}} {Y : Over (Spec (.of k))}
    {I : EtaleModules.{u, 0} Λ X₁ ⥤ EtaleModules.{u, 0} Λ X₂}
    {g : EtaleModules.{u, 0} Λ X₂ ⥤ EtaleModules.{u, 0} Λ Y.left}
    {g' : EtaleModules.{u, 0} Λ X₁ ⥤ EtaleModules.{u, 0} Λ Z}
    {G : EtaleModules.{u, 0} Λ Z ⥤ EtaleModules.{u, 0} Λ Y.left}
    [I.Additive] [g.Additive] [g'.Additive] [G.Additive] {βn : I ⋙ g ⟶ g' ⋙ G}
    {M : CochainComplex.Plus (EtaleModules.{u, 0} Λ X₁)}
    (h : Functor.BaseChangeQuasiIsoAt G I g g' βn M)
    (T : CochainComplex.Plus (EtaleModules.{u, 0} Λ Z))
    (ψ : g'.mapCochainComplexPlus.obj M ⟶ T) (hψ : QuasiIso ψ.hom)
    (hT : ∀ n, Injective (T.obj.X n))
    (hp : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar
            (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M))))))) :
    ∃ hp' : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ Y kbar (G.mapCochainComplexPlus.obj T))))),
      perfectDerivedTrace.{0, u + 1} Λ ⟨_, hp⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard
            (g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M)))) =
        perfectDerivedTrace.{0, u + 1} Λ ⟨_, hp'⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ Y kbar p q hcard
            (G.mapCochainComplexPlus.obj T))) :=
  perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso Λ kbar p q hcard
    (C := g.mapCochainComplexPlus.obj (I.mapCochainComplexPlus.obj M))
    (C' := G.mapCochainComplexPlus.obj T) _ (h T ψ hψ hT) hp

/-- **The local term of `Rπ_* M` at a rational point is the trace on the fibre.** For `π : W' ⟶ W`
proper over `k`, a bounded below complex `M` of injectives on `W'_étale` (so that `π_* M = Rπ_* M`)
whose direct image has perfect stalks, and `y : Spec k ⟶ W`, the cohomology of the geometric
fibre `(W'_y)_k̄` with coefficients in `M|_{W'_y}` is perfect and
`Tr(π_y | (π_* M)_ȳ) = Tr(π_{W'_y}^* | RΓ((W'_y)_k̄, M|_{W'_y}))`. -/
theorem perfectDerivedTrace_rationalPointStalkFrobenius_directImage_eq_fibre [IsProper π.left]
    (M : CochainComplex.Plus (EtaleModules.{u, 0} Λ W'.left)) [∀ n, Injective (M.obj.X n)]
    (hD : HasPerfectStalks Λ
      ((etaleModuleDirectImage.{u, 0} Λ π.left).mapCochainComplexPlus.obj M)) :
    ∃ hF : StacksDraft.Perfect.IsPerfect.{0, u + 1, u + 2} (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} Λ
            (pullback.snd (rationalFibre π y).hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} Λ (rationalFibre π y) kbar
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst π.left y)).mapCochainComplexPlus.obj
              M))))),
      perfectDerivedTrace.{0, u + 1} Λ ⟨_, hD (rationalGeometricPoint kbar y)⟩
          (DerivedCategory.Q.map (rationalPointStalkFrobenius.{u, 0} Λ kbar p q hcard y
            ((etaleModuleDirectImage.{u, 0} Λ π.left).mapCochainComplexPlus.obj M))) =
        perfectDerivedTrace.{0, u + 1} Λ ⟨_, hF⟩ (DerivedCategory.Plus.ι.map
          (frobeniusRestrictionCohomologyEndo.{u, 0} Λ (rationalFibre π y) kbar p q hcard
            ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst π.left y)).mapCochainComplexPlus.obj
              M))) := by
  let D := (etaleModuleDirectImage.{u, 0} Λ π.left).mapCochainComplexPlus.obj M
  let E := (etaleModuleInverseImage.{u, 0} Λ y).mapCochainComplexPlus.obj D
  have hE : HasPerfectStalks Λ E := isPerfect_stalk_inverseImage Λ y D hD
  obtain ⟨hpE, htE⟩ := cohomologicalTraceFormula_of_etale Λ kbar p q hcard (fieldPointOver k) E hE
  let K' := (etaleModuleInverseImage.{u, 0} Λ (pullback.fst π.left y)).mapCochainComplexPlus.obj M
  obtain ⟨T, ψ, hψ, hT, -, -⟩ :=
    Functor.exists_twist_lift_of_injectiveResolution (𝟭 _) K' (𝟙 _)
  have : ∀ n, Injective (T.obj.X n) := hT
  have hP := quasiIso_etaleModuleBaseChange_comp_of_isProper Λ π.left
    (IsPullback.of_hasPullback π.left y) pullback.condition.symm M (isTorsionPlus_of_finite Λ _ _)
  obtain ⟨hpS, htS⟩ :=
    perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_baseChangeQuasiIsoAt Λ kbar p q
      hcard (Y := fieldPointOver k) hP T ψ hψ hT hpE
  have hL := perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_directImage_of_isProper Λ kbar
    p q hcard (rationalFibreToPoint π y) T hpS
  have hpK := isPerfect_frobeniusRestriction_of_quasiIso Λ kbar (Y := rationalFibre π y) ψ.hom hψ
    ((isPerfect_frobeniusRestriction_directImage_iff_of_isProper Λ kbar
      (rationalFibreToPoint π y) T).1 hpS)
  obtain ⟨hpT', htKT⟩ :=
    perfectDerivedTrace_frobeniusRestrictionCohomologyEndo_eq_of_quasiIso Λ kbar p q hcard
      (Y := rationalFibre π y) ψ.hom hψ hpK
  exact ⟨hpK, (perfectDerivedTrace_rationalPointStalkFrobenius_inverseImage_point y Λ kbar p q
    hcard D hD hE).symm.trans ((Fintype.sum_unique _).symm.trans (htE.symm.trans
      (htS.trans (hL.trans htKT.symm))))⟩

end Trace

end Stacks.EtaleCohomology

end
