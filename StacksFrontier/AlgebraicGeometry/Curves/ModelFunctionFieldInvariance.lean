module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Curves.FunctionFieldCategories
public import StacksFrontier.AlgebraicGeometry.Curves.SmoothModelPurelyInseparable
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.DenseOpenGeometricallyIrreducible

/-!
# The nonsingular projective model of `(X_K)_red`, with nothing carried

Let `k` be a field, let `X` be a geometrically irreducible curve over `k` and let `K/k` be a
field extension. The reduction `(X_K)_red` of the base change is again a geometrically
irreducible curve, over `K`, and this file proves part (2) of [Stacks, Tag 0BY4] about its
nonsingular projective models `Y_K`: there is a finite purely inseparable extension `K/k` for
which `Y_K` is smooth.

The statement carries no hypothesis: no stand-in for [Stacks, Tag 09NZ], and no properness of
`X`. Part (1), that `Y_K` is the normalization of `X_K` when `X` is proper, is
`AlgebraicGeometry.exists_nonsingularProjectiveModel_iso_normalization_reducedBaseChange'` in
`StacksFrontier/AlgebraicGeometry/Curves/ModelNormalization.lean`, where the model
`AlgebraicGeometry.normalizationModel'` used here is built.

## Main definitions

* `AlgebraicGeometry.NonsingularProjectiveModel.ofFunctionFieldAlgEquiv`: a model of a curve is a
  model of any curve with the same function field over the base field.
* `AlgebraicGeometry.reducedBaseChangeMap`: the morphism `(X_K)_red ⟶ (Y_K)_red` induced by a
  morphism `X ⟶ Y` of schemes over `k`.

## Main results

* `AlgebraicGeometry.exists_isPurelyInseparable_smooth_nonsingularProjectiveModel_of_isCurve`:
  **[Stacks, Tag 0BY4], part (2)**, with nothing carried and `X` not assumed proper.
* `exists_isPurelyInseparable_isGeometricallyNormal_normalization_reducedBaseChange`:
  [Stacks, Tag 0BXT] read on the reduced base change — after a finite purely inseparable
  extension `K/k` the normalization of `(X_K)_red` is geometrically normal over `K`.
* `AlgebraicGeometry.functionFieldAlgEquivOfIsOpenImmersion`: the isomorphism of function fields
  of a dominant open immersion of curves, as an isomorphism of algebras over the base field.

## Why nothing is carried

**Tag 09NZ is not needed.** [Stacks, Tag 09NZ] — a Noetherian separated scheme of dimension at
most one has an ample invertible sheaf — is assumed by
`AlgebraicGeometry.isProjectiveMorphism_of_topologicalKrullDim_le_one`, a special case of the
library's Tag 0A26 whose hypothesis is superfluous, and it is not needed here either: the
model `AlgebraicGeometry.normalizationModel'` is built from a *normalization*, which is normal,
hence an integral scheme of dimension one, and for those Tag 0A25 is proved outright from
Tag 09ND, which is
`Stacks.HQuasiProjectiveDimensionOne.isHQuasiProjective_of_isIntegral`. The step "a proper curve
is projective" is therefore unconditional, as it is in
`AlgebraicGeometry.isProjectiveMorphism_of_isProper_of_isCurve` for a curve itself, and that step
is the only point at which Tag 09NZ entered.

**Properness of `X` is not needed in part (2).** The source reduces the general case to the
projective one by replacing `X` by a nonsingular projective model, which is legitimate because
`Y_K` depends only on the function field of `X`. Both halves of that reduction are available
unconditionally. A curve over `k` is a dense open subscheme of a projective curve over `k` by
`AlgebraicGeometry.exists_isCurve_isProjectiveMorphism_isOpenImmersion`, the compactification
behind the essential surjectivity half of [Stacks, Tag 0BY1]
(`AlgebraicGeometry.normalProjectiveCurveToCurve_essSurj`); and the dependence of the model only
on the function field is `AlgebraicGeometry.NonsingularProjectiveModel.ofFunctionFieldAlgEquiv`
here, fed by the observation that the reduced base change of a dense open immersion is again a
dominant open immersion, so that `(X_K)_red` and `(X̄_K)_red` have the same function field over
`K`.

## Implementation notes

The reduced base change `(X_K)_red` is a curve over `K` by
`AlgebraicGeometry.isCurve_reducedBaseChangeStructureMap'`: reduced by construction, irreducible
because the base change of a geometrically irreducible scheme over a one-point base is
irreducible, and one-dimensional by [Stacks, Tag 0BY9].

Dominance of the reduced base change of a dense open immersion is obtained from irreducibility
rather than from the range formula: the source `(X_K)_red` is nonempty and the target
`(X̄_K)_red` is irreducible, and a nonempty open subset of an irreducible space is dense.

The `k`-algebra structure on a function field is `AlgebraicGeometry.functionFieldAlgebra`; that
the map of function fields induced by a dominant morphism over `k` is a map of `k`-algebras is
`AlgebraicGeometry.functionFieldMap_functionFieldAlgebraMap`, read through
`AlgebraicGeometry.functionFieldAlgebraMap_eq_germToFunctionField` to pass between the stalk and
the global-sections description of that algebra structure.

## References

* [Stacks Project, Tag 0BY4](https://stacks.math.columbia.edu/tag/0BY4)
* [Stacks Project, Tag 0BY1](https://stacks.math.columbia.edu/tag/0BY1)
* [Stacks Project, Tag 0BXT](https://stacks.math.columbia.edu/tag/0BXT)
* [Stacks Project, Tag 0BXV](https://stacks.math.columbia.edu/tag/0BXV)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
* [Stacks Project, Tag 0A25](https://stacks.math.columbia.edu/tag/0A25)
* [Stacks Project, Tag 0A26](https://stacks.math.columbia.edu/tag/0A26)
* [Stacks Project, Tag 09ND](https://stacks.math.columbia.edu/tag/09ND)
* [Stacks Project, Tag 035O](https://stacks.math.columbia.edu/tag/035O)
* [Stacks Project, Tag 0380](https://stacks.math.columbia.edu/tag/0380)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Finite type of the structure morphism of the reduced base change -/

/-- The structure morphism of `(X_K)_red` is locally of finite type: it is the reduction
morphism, a closed immersion and hence proper, followed by the base change of `sX`.

Recorded as an instance so that the normalization of `(X_K)_red` can be named without properness
of `sX`: typeclass inference does not reach finite type of a closed immersion on its own. -/
public instance locallyOfFiniteType_reducedBaseChangeStructureMap
    (k K : Type u) [Field k] [Field K] [Algebra k K] {X : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) [LocallyOfFiniteType sX] :
    LocallyOfFiniteType (reducedBaseChangeStructureMap k K sX) := by
  have hLi : LocallyOfFiniteType
      (pullback sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))).reductionι :=
    IsProper.toLocallyOfFiniteType
  infer_instance

/-! ### A nonsingular projective model depends only on the function field -/

/-- A dominant morphism of curves over `k` induces a map of function fields which is a map of
`k`-algebras: both structure maps are the germ at the generic point of the global sections of the
structure morphism, and the morphism is over `k`. -/
public theorem functionFieldMap_algebraMap_of_isCurve (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsCurve k sX] [IsCurve k sY]
    (g : X ⟶ Y) [IsDominant g] (hg : g ≫ sY = sX) (a : k) :
    letI : Algebra k X.functionField := functionFieldAlgebra k sX
    letI : Algebra k Y.functionField := functionFieldAlgebra k sY
    (Scheme.Hom.functionFieldMap g).hom (algebraMap k Y.functionField a) =
      algebraMap k X.functionField a := by
  let _ : Algebra k X.functionField := functionFieldAlgebra k sX
  let _ : Algebra k Y.functionField := functionFieldAlgebra k sY
  let V : Variety k := { toScheme := X, structureMap := sX }
  let W : Variety k := { toScheme := Y, structureMap := sY }
  have h : (Scheme.Hom.functionFieldMap g).hom (functionFieldAlgebraMap W a) =
      functionFieldAlgebraMap V a :=
    functionFieldMap_functionFieldAlgebraMap V W g hg a
  rwa [DFunLike.congr_fun (functionFieldAlgebraMap_eq_germToFunctionField V) a,
    DFunLike.congr_fun (functionFieldAlgebraMap_eq_germToFunctionField W) a] at h

/-- The isomorphism of function fields induced by a dominant open immersion of curves over `k`,
as an isomorphism of `k`-algebras. -/
public def functionFieldAlgEquivOfIsOpenImmersion (k : Type u) [Field k] {X Y : Scheme.{u}}
    (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) [IsCurve k sX] [IsCurve k sY]
    (g : X ⟶ Y) [IsOpenImmersion g] [IsDominant g] (hg : g ≫ sY = sX) :
    letI : Algebra k X.functionField := functionFieldAlgebra k sX
    letI : Algebra k Y.functionField := functionFieldAlgebra k sY
    Y.functionField ≃ₐ[k] X.functionField := by
  let _ : Algebra k X.functionField := functionFieldAlgebra k sX
  let _ : Algebra k Y.functionField := functionFieldAlgebra k sY
  let _ : IsIso (Scheme.Hom.functionFieldMap g) := isIso_functionFieldMap_of_isOpenImmersion g
  exact AlgEquiv.ofRingEquiv (R := k)
    (f := RingEquiv.ofBijective (Scheme.Hom.functionFieldMap g).hom
      (ConcreteCategory.bijective_of_isIso (Scheme.Hom.functionFieldMap g)))
    (functionFieldMap_algebraMap_of_isCurve k sX sY g hg)

/-- **A nonsingular projective model depends only on the function field.** A nonsingular
projective model of a curve `X'` over `k` is a nonsingular projective model of any curve `X`
over `k` whose function field is `k`-isomorphic to that of `X'`: the model's comparison of
function fields is composed with the given isomorphism, and the regular projective curve
carrying it is unchanged. -/
public def NonsingularProjectiveModel.ofFunctionFieldAlgEquiv (k : Type u) [Field k]
    {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k))
    [IsCurve k sX] [IsCurve k sX'] (M : NonsingularProjectiveModel k X' sX')
    (e : letI : Algebra k X.functionField := functionFieldAlgebra k sX
      letI : Algebra k X'.functionField := functionFieldAlgebra k sX'
      X.functionField ≃ₐ[k] X'.functionField) :
    NonsingularProjectiveModel k X sX := by
  let _ : IsCurve k M.structureMap := M.isCurve
  let _ : Algebra k X.functionField := functionFieldAlgebra k sX
  let _ : Algebra k X'.functionField := functionFieldAlgebra k sX'
  let _ : Algebra k M.Y.functionField := functionFieldAlgebra k M.structureMap
  exact
    { Y := M.Y
      structureMap := M.structureMap
      isCurve := M.isCurve
      isProjectiveVariety := M.isProjectiveVariety
      isRegular := M.isRegular
      functionFieldEquiv := e.trans M.functionFieldEquiv }

/-- The structure morphism of the transported model is that of the original. -/
@[simp]
public theorem NonsingularProjectiveModel.ofFunctionFieldAlgEquiv_structureMap (k : Type u)
    [Field k] {X X' : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sX' : X' ⟶ Spec (.of k))
    [IsCurve k sX] [IsCurve k sX'] (M : NonsingularProjectiveModel k X' sX')
    (e : letI : Algebra k X.functionField := functionFieldAlgebra k sX
      letI : Algebra k X'.functionField := functionFieldAlgebra k sX'
      X.functionField ≃ₐ[k] X'.functionField) :
    (NonsingularProjectiveModel.ofFunctionFieldAlgEquiv k sX sX' M e).structureMap =
      M.structureMap := rfl

/-! ### The reduced base change of a morphism of schemes over the base field -/

/-- The morphism `(X_K)_red ⟶ (Y_K)_red` induced by a morphism `X ⟶ Y` of schemes over `k`: the
base change of the morphism along `K/k`, read on the reductions. -/
public def reducedBaseChangeMap (k K : Type u) [Field k] [Field K] [Algebra k K]
    {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k)) (g : X ⟶ Y)
    (hg : g ≫ sY = sX) :
    reducedBaseChange k K sX ⟶ reducedBaseChange k K sY :=
  Scheme.reductionMap' (pullback.map sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))
    sY (Spec.map (CommRingCat.ofHom (algebraMap k K))) g (𝟙 _) (𝟙 _)
    ((Category.comp_id _).trans hg.symm)
    ((Category.comp_id _).trans (Category.id_comp _).symm))

/-- `AlgebraicGeometry.reducedBaseChangeMap` is a morphism over the extension field. -/
public theorem reducedBaseChangeMap_comp_structureMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (g : X ⟶ Y) (hg : g ≫ sY = sX) :
    reducedBaseChangeMap k K sX sY g hg ≫ reducedBaseChangeStructureMap k K sY =
      reducedBaseChangeStructureMap k K sX := by
  refine (Scheme.reductionMap'_comp_subschemeι_assoc _ _).trans ?_
  rw [pullback.lift_snd, Category.comp_id]
  rfl

/-- The reduced base change of an open immersion is an open immersion: an open immersion is
stable under base change, and the reduction of an open immersion is an open immersion. -/
public theorem isOpenImmersion_reducedBaseChangeMap (k K : Type u) [Field k] [Field K]
    [Algebra k K] {X Y : Scheme.{u}} (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    (g : X ⟶ Y) [IsOpenImmersion g] (hg : g ≫ sY = sX) :
    IsOpenImmersion (reducedBaseChangeMap k K sX sY g hg) := by
  let _ : IsOpenImmersion (pullback.map sX (Spec.map (CommRingCat.ofHom (algebraMap k K)))
      sY (Spec.map (CommRingCat.ofHom (algebraMap k K))) g (𝟙 _) (𝟙 _)
      ((Category.comp_id _).trans hg.symm)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) :=
    MorphismProperty.pullbackMap (P := @IsOpenImmersion) inferInstance inferInstance
      hg.symm (Category.id_comp _).symm
  exact Scheme.reductionMap'_isOpenImmersion _

/-! ### Geometric normality of the normalization after a purely inseparable extension -/

/-- **[Stacks, Tag 0BXT] read on the reduced base change.** For an algebraic `k`-scheme `X` there
is a finite purely inseparable extension `K/k` such that the normalization of `(X_K)_red` is
geometrically normal over `K`.

Tag 0BXT produces the extension together with geometric normality of the normalization of
`pullback (Spec K ⟶ Spec k) sX`, whose structure morphism is the *first* projection, whereas
`AlgebraicGeometry.reducedBaseChange` is the reduction of `pullback sX (Spec K ⟶ Spec k)`, whose
structure morphism is the *second* projection. The two are matched in three steps: the symmetry
isomorphism of the pullback, transported to the reductions by the functoriality
`AlgebraicGeometry.Scheme.reductionMap'`; the transport of the normalization along that
isomorphism, `AlgebraicGeometry.exists_iso_normalizationSchemeOverField_of_iso`; and
`AlgebraicGeometry.Scheme.exists_normalizationScheme_iso_reduction` ([Stacks, Tag 035O]), which
identifies the normalization of a scheme with that of its reduction. The resulting isomorphism of
normalizations over `Spec K` carries geometric normality across. -/
@[ega "IV 17.15.14.2" "partial"]
public theorem exists_isPurelyInseparable_isGeometricallyNormal_normalization_reducedBaseChange
    (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [QuasiCompact sX] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Module.Finite k K)
      (_ : IsPurelyInseparable k K),
      IsGeometricallyNormal (normalizationOverField K (reducedBaseChangeStructureMap k K sX) ≫
        reducedBaseChangeStructureMap k K sX) := by
  obtain ⟨k', _, _, hfin, hpi, hgn⟩ :=
    exists_isPurelyInseparable_isGeometricallyNormal_normalization k sX
  refine ⟨k', inferInstance, inferInstance, hfin, hpi, ?_⟩
  have hgn' : IsGeometricallyNormal
      (normalizationOverField k' (pullback.fst (spectrumMap k k') sX) ≫
        pullback.fst (spectrumMap k k') sX) := hgn
  have hLi' : LocallyOfFiniteType (pullback (spectrumMap k k') sX).nilradical.subschemeι :=
    IsProper.toLocallyOfFiniteType
  have hLi : LocallyOfFiniteType (pullback sX (spectrumMap k k')).nilradical.subschemeι :=
    IsProper.toLocallyOfFiniteType
  have hRed : IsReduced (pullback (spectrumMap k k') sX).nilradical.subscheme :=
    Scheme.isReduced_reduction _
  have hIsoRed : IsIso (Scheme.reductionMap' (pullbackSymmetry (spectrumMap k k') sX).hom) :=
    inferInstance
  have hτ : (asIso (Scheme.reductionMap' (pullbackSymmetry (spectrumMap k k') sX).hom)).hom ≫
      ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
        pullback.snd sX (spectrumMap k k')) =
      (pullback (spectrumMap k k') sX).nilradical.subschemeι ≫
        pullback.fst (spectrumMap k k') sX := by
    change Scheme.reductionMap' (pullbackSymmetry (spectrumMap k k') sX).hom ≫
      ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
        pullback.snd sX (spectrumMap k k')) = _
    rw [Scheme.reductionMap'_comp_subschemeι_assoc, pullbackSymmetry_hom_comp_snd]
  obtain ⟨ε, hε⟩ := exists_iso_normalizationSchemeOverField_of_iso k'
    ((pullback (spectrumMap k k') sX).nilradical.subschemeι ≫
      pullback.fst (spectrumMap k k') sX)
    ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
      pullback.snd sX (spectrumMap k k'))
    (asIso (Scheme.reductionMap' (pullbackSymmetry (spectrumMap k k') sX).hom)) hτ
  obtain ⟨e', he'⟩ := Scheme.exists_normalizationScheme_iso_reduction
    (pullback (spectrumMap k k') sX)
    (finite_irreducibleComponents_of_locallyOfFiniteType k' (pullback.fst (spectrumMap k k') sX))
  have he'' : e'.hom ≫ normalizationOverField k'
        ((pullback (spectrumMap k k') sX).nilradical.subschemeι ≫
          pullback.fst (spectrumMap k k') sX) ≫
        (pullback (spectrumMap k k') sX).nilradical.subschemeι =
      normalizationOverField k' (pullback.fst (spectrumMap k k') sX) := he'
  have hchain : (e' ≪≫ ε).hom ≫
      normalizationOverField k'
          ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
            pullback.snd sX (spectrumMap k k')) ≫
        ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
          pullback.snd sX (spectrumMap k k')) =
      normalizationOverField k' (pullback.fst (spectrumMap k k') sX) ≫
        pullback.fst (spectrumMap k k') sX := by
    rw [Iso.trans_hom, Category.assoc, hε, ← he'']
    simp only [Category.assoc]
  have hgnZ : IsGeometricallyNormal
      (normalizationOverField k'
          ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
            pullback.snd sX (spectrumMap k k')) ≫
        ((pullback sX (spectrumMap k k')).nilradical.subschemeι ≫
          pullback.snd sX (spectrumMap k k'))) :=
    isGeometricallyNormal_of_iso k' (e' ≪≫ ε).symm
      (normalizationOverField k' (pullback.fst (spectrumMap k k') sX) ≫
        pullback.fst (spectrumMap k k') sX) _
      (by rw [Iso.symm_hom, Iso.inv_comp_eq, hchain]) hgn'
  exact hgnZ

/-! ### Tag 0BY4, part (2) -/

/-- **Stacks Project, Tag 0BY4, part (2).** Let `k` be a field and let `X` be a geometrically
irreducible curve over `k`. There is a finite purely inseparable extension `K/k` for which
`(X_K)_red` has a smooth nonsingular projective model.

Nothing is carried and `X` is not assumed proper. The general case is reduced to the proper one
exactly as in the source: `X` is a dense open subscheme of a projective curve `X̄` over `k`
(`AlgebraicGeometry.exists_isCurve_isProjectiveMorphism_isOpenImmersion`, the compactification
behind the essential surjectivity half of [Stacks, Tag 0BY1]), which is again geometrically
irreducible; the proper case,
`AlgebraicGeometry.exists_isPurelyInseparable_smooth_nonsingularProjectiveModel'`, applied to `X̄`
supplies `K` and a smooth model of `(X̄_K)_red`; and that is a model of `(X_K)_red` as well,
because the reduced base change of a dense open immersion is a dominant open immersion, so the
two have the same function field over `K`, and a nonsingular projective model depends only on
the function field. -/
@[stacks 0BY4 "part (2), with nothing carried and `X` not assumed proper. Tag 09NZ is not \
needed: the compactification of a curve is Tag 0BXV for an integral scheme of dimension one, \
where Tag 0A25 holds outright, and the model of a proper curve is its normalization, again \
integral of dimension one. The source's reduction of the general case to the projective case is \
carried out with the compactification behind \
`AlgebraicGeometry.normalProjectiveCurveToCurve_essSurj` (Tag 0BY1) together with \
`AlgebraicGeometry.NonsingularProjectiveModel.ofFunctionFieldAlgEquiv`, that a nonsingular \
projective model depends only on the function field"]
public theorem exists_isPurelyInseparable_smooth_nonsingularProjectiveModel_of_isCurve
    (k : Type u) [Field k] {X : Scheme.{u}} (sX : X ⟶ Spec (.of k))
    [IsCurve k sX] [GeometricallyIrreducible sX] :
    ∃ (K : Type u) (_ : Field K) (_ : Algebra k K) (_ : Module.Finite k K)
      (_ : IsPurelyInseparable k K),
      ∃ M : NonsingularProjectiveModel K (reducedBaseChange k K sX)
          (reducedBaseChangeStructureMap k K sX),
        Smooth M.structureMap := by
  obtain ⟨Y, q, j, hj, hdom, hjq, hCq, hprojq⟩ :=
    exists_isCurve_isProjectiveMorphism_isOpenImmersion k sX
  have hPq : IsProper q := isProper_of_isProjectiveMorphism q hprojq
  have hGjq : GeometricallyIrreducible (j ≫ q) := by
    rw [hjq]
    infer_instance
  have _ : GeometricallyIrreducible q :=
    geometricallyIrreducible_of_dense_isOpenImmersion j q hdom.denseRange hGjq
  obtain ⟨K, _, _, hfin, hpi, M, hsm⟩ :=
    exists_isPurelyInseparable_smooth_nonsingularProjectiveModel' k q
  refine ⟨K, inferInstance, inferInstance, hfin, hpi, ?_⟩
  have hVX : IsVariety K (reducedBaseChangeStructureMap k K sX) := inferInstance
  have _ : IsIntegral (reducedBaseChange k K sX) := hVX.toIsIntegral
  have hVq : IsVariety K (reducedBaseChangeStructureMap k K q) := inferInstance
  have _ : IsIntegral (reducedBaseChange k K q) := hVq.toIsIntegral
  have _ : IsOpenImmersion (reducedBaseChangeMap k K sX q j hjq) :=
    isOpenImmersion_reducedBaseChangeMap k K sX q j hjq
  have _ : IsDominant (reducedBaseChangeMap k K sX q j hjq) :=
    ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _
      (reducedBaseChangeMap k K sX q j hjq).isOpenEmbedding.isOpenMap⟩
  let _ : Algebra K (reducedBaseChange k K sX).functionField :=
    functionFieldAlgebra K (reducedBaseChangeStructureMap k K sX)
  let _ : Algebra K (reducedBaseChange k K q).functionField :=
    functionFieldAlgebra K (reducedBaseChangeStructureMap k K q)
  exact ⟨NonsingularProjectiveModel.ofFunctionFieldAlgEquiv K
    (reducedBaseChangeStructureMap k K sX) (reducedBaseChangeStructureMap k K q) M
    (functionFieldAlgEquivOfIsOpenImmersion K (reducedBaseChangeStructureMap k K sX)
      (reducedBaseChangeStructureMap k K q) (reducedBaseChangeMap k K sX q j hjq)
      (reducedBaseChangeMap_comp_structureMap k K sX q j hjq)).symm, hsm⟩

end AlgebraicGeometry

end
