module

public import StacksFrontier.AlgebraicGeometry.Spaces.VectorBundle.SymmetricAlgebraAffineSections
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectSumSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.LinearAlgebra.SymmetricAlgebra.AdjoinDegreeOneGraded
public import StacksFrontier.LinearAlgebra.SymmetricAlgebra.FibrePolynomial

/-!
# The comparison `Sym(ℰ(U)) ⟶ Γ(U, Sym(ℰ))` over an arbitrary chart

Let `W` be an algebraic space and `ℰ` an `𝒪_W`-module on its small étale site. Over every étale
chart `U` of `W` the degree-one inclusion `ℰ ⟶ Sym(ℰ)` induces a morphism of `𝒪(U)`-algebras

`θ_U : Sym_{𝒪(U)}(ℰ(U)) ⟶ Γ(U, Sym(ℰ))`,

compatible with restriction along morphisms of charts. Over an affine chart on which `ℰ` is free
it is the identification `AlgebraicGeometry.Space.SymAlgSections.symSectionsRingEquiv`. Over an
arbitrary affine chart `U` it need not be computable directly, but for a morphism `V ⟶ U` of
affine charts with `ℰ` free over `V` and `ℰ`, `Sym(ℰ)` quasi-coherent, the base change of `θ_U`
to `𝒪(V)` is bijective: it is identified with `θ_V` through the base-change comparisons of the
two quasi-coherent modules (Stacks 01M1 for the symmetric algebra of a base change).

## Main definitions

* `AlgebraicGeometry.Space.SymAlgSections.chartSymAlgHom`: the comparison `θ_U`, over the
  functions on the chart in the spelling of `AlgebraicGeometry.Space.chartRing`.
* `AlgebraicGeometry.Space.SymAlgSections.chartSectionsBasis` and
  `AlgebraicGeometry.Space.SymAlgSections.baseChangeSectionsBasis`: the bases of `ℰ(V)` and of
  `𝒪(V) ⊗_{𝒪(U)} ℰ(U)` given by a trivialization of `ℰ` over `V`.

## Main results

* `AlgebraicGeometry.Space.SymAlgSections.symSectionsRingHom_ι` and
  `AlgebraicGeometry.Space.SymAlgSections.map_symSectionsRingHom_ι`: the comparison sends `ι m`
  to the degree-one section `m`, compatibly with restriction.
* `AlgebraicGeometry.Space.SymAlgSections.chartSymAlgHom_apply`: the comparison over the chart
  ring is the comparison `AlgebraicGeometry.Space.SymAlgSections.symSectionsRingHom`.
* `AlgebraicGeometry.Space.SymAlgSections.bijective_chartSymAlgHom`: it is bijective over an
  affine chart trivializing `ℰ`.
* `AlgebraicGeometry.Space.SymAlgSections.bijective_baseChange_chartSymAlgHom`: its base change
  to an affine chart trivializing `ℰ` is bijective.

## Implementation notes

The functions on a chart carry three spellings: `AlgebraicGeometry.Space.vectorBundleChartRing`,
over which the sectionwise symmetric powers are formed; `AlgebraicGeometry.Space.chartRing`, over
which the base-change comparison `AlgebraicGeometry.Space.sectionsBaseChange` of a module on the
site is stated; and `Γ(chartScheme U, ⊤)`. They agree definitionally but not reducibly, so instance
search does not pass between them. The comparison is therefore built twice, as
`AlgebraicGeometry.Space.SymAlgSections.symSectionsRingHom` and as
`AlgebraicGeometry.Space.SymAlgSections.chartSymAlgHom`, the second as the map
`SymmetricAlgebra.lift` of the degree-one inclusion, and the two are identified elementwise. The
base change statement is the abstract
`SymmetricAlgebra.bijective_baseChange_of_comparison`, instantiated once.

## References

* [Stacks Project, Tag 01M1](https://stacks.math.columbia.edu/tag/01M1)
* [Stacks Project, Tag 01CG](https://stacks.math.columbia.edu/tag/01CG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite PresheafOfModules

universe u

namespace AlgebraicGeometry.Space.SymAlgSections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (W : AlgebraicSpaces B S hS)
  (F : SheafOfModules.{u} (structureRingSheaf B S hS W))

/-- The degree-one generator of `Sym(ℰ)` at a section `m` of `ℰ` is the sheafification unit
applied to the generator `ι m` of the sectionwise symmetric algebra. -/
theorem symmetricAlgebraGen_app (V : SmallEtale B S hS W.1) (m : F.val.obj (op V)) :
    ((symmetricAlgebraGen B S hS W F).val.app (op V)) m =
      pieceUnitHom B S hS W F V 1
        ⟨SymmetricAlgebra.ι (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) m,
        SymPow.ι_mem_symmetricPowerInt_one _ _ m⟩ := by
  have htri : ((symmetricAlgebraSheafificationIso B S hS W F).hom.val.app (op V))
      (Hom.app ((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (structureRingSheaf B S hS W).obj)).unit.app F.val) (op V) m) = m := by
    have h := (PresheafOfModules.sheafificationAdjunction.{u}
      (𝟙 (structureRingSheaf B S hS W).obj)).right_triangle_components F
    exact congrArg (fun g => Hom.app g (op V) m) h
  have hinv : (symmetricAlgebraSheafificationIso B S hS W F).inv.val.app (op V) m =
      Hom.app ((PresheafOfModules.sheafificationAdjunction.{u}
        (𝟙 (structureRingSheaf B S hS W).obj)).unit.app F.val) (op V) m := by
    conv_lhs => rw [← htri]
    exact congrArg (fun g => (SheafOfModules.Hom.val g).app (op V) _)
      (symmetricAlgebraSheafificationIso B S hS W F).hom_inv_id
  show (@PresheafOfModules.symmetricAlgebraSheafifyGen.{u, u + 1, u, u} _ _
      (SmallEtale.topology B S hS W.1) (structureSheaf B S hS W.1 W.2).obj
      (structureRingSheaf B S hS W) (𝟙 _) (isLocallyInjective_id_structureRingSheaf B S hS W)
      (isLocallySurjective_id_structureRingSheaf B S hS W)
      (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W)
      F.val).val.app
    (op V) ((symmetricAlgebraSheafificationIso B S hS W F).inv.val.app (op V) m) = _
  rw [hinv]
  exact @PresheafOfModules.unit_naturality_apply _ _ _ _ _ _
    (isLocallyInjective_id_structureRingSheaf B S hS W)
    (isLocallySurjective_id_structureRingSheaf B S hS W)
    (wEqualsLocallyBijective_smallEtale B S hS W) (hasWeakSheafify_smallEtale B S hS W) _ _
    (symPowIntGen F.val) (op V) m

/-- **The comparison carries the generator `ι m` to the degree-one section `m`.** -/
theorem symSectionsRingHom_ι (V : SmallEtale B S hS W.1) (m : F.val.obj (op V)) :
    symSectionsRingHom B S hS W F V
        (SymmetricAlgebra.ι (vectorBundleChartRing B S hS W V) (F.val.obj (op V)) m) =
      (symmetricAlgebra B S hS W F).ungradedIncl 1
        (((symmetricAlgebraGen B S hS W F).val.app (op V)) m) := by
  rw [symmetricAlgebraGen_app B S hS W F V m]
  exact symSectionsRingHom_of_mem B S hS W F V 1
    ⟨_, SymmetricAlgebra.ι_mem_symmetricPower_one (R := vectorBundleChartRing B S hS W V)
      (M := F.val.obj (op V)) m⟩

/-- Restricting the degree-one section `m` along a morphism of charts gives the degree-one section
of the restriction of `m`. -/
private theorem map_ungradedIncl_symmetricAlgebraGen {U V : SmallEtale B S hS W.1} (f : V ⟶ U)
    (m : F.val.obj (op U)) :
    ((symmetricAlgebraSheaf B S hS W F).right.obj.map f.op).hom
        ((symmetricAlgebra B S hS W F).ungradedIncl 1
          (((symmetricAlgebraGen B S hS W F).val.app (op U)) m)) =
      (symmetricAlgebra B S hS W F).ungradedIncl 1
        (((symmetricAlgebraGen B S hS W F).val.app (op V)) (F.val.map f.op m)) :=
  ((symmetricAlgebra B S hS W F).ungradedIncl_naturality f.op 1 _).trans
    (congrArg ((symmetricAlgebra B S hS W F).ungradedIncl 1)
      (PresheafOfModules.naturality_apply (symmetricAlgebraGen B S hS W F).val f.op m).symm)

/-- **The comparison is compatible with restriction on generators**: restricting the image of
`ι m` along a morphism of charts gives the image of `ι` of the restriction of `m`. -/
theorem map_symSectionsRingHom_ι {U V : SmallEtale B S hS W.1} (f : V ⟶ U)
    (m : F.val.obj (op U)) :
    ((symmetricAlgebraSheaf B S hS W F).right.obj.map f.op).hom
        (symSectionsRingHom B S hS W F U
          (SymmetricAlgebra.ι (vectorBundleChartRing B S hS W U) (F.val.obj (op U)) m)) =
      symSectionsRingHom B S hS W F V
        (SymmetricAlgebra.ι (vectorBundleChartRing B S hS W V) (F.val.obj (op V))
          (F.val.map f.op m)) := by
  rw [symSectionsRingHom_ι B S hS W F U m, symSectionsRingHom_ι B S hS W F V (F.val.map f.op m)]
  exact map_ungradedIncl_symmetricAlgebraGen B S hS W F f m

/-- The coordinates of the sections of `ℰ` over a chart on which it is free. -/
def chartCoords (V : SmallEtale B S hS W.1) {ι : Type u} [DecidableEq ι] [Finite ι]
    (e : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι) :
    F.val.obj (op V) ≃ (ι → vectorBundleChartRing B S hS W V) :=
  (sectionsEquivFun B S hS W F V e).toEquiv

/-- The coordinates of a sum of sections are the sum of their coordinates. -/
theorem chartCoords_add (V : SmallEtale B S hS W.1) {ι : Type u} [DecidableEq ι] [Finite ι]
    (e : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι)
    (m m' : F.val.obj (op V)) :
    chartCoords B S hS W F V e (m + m') =
      chartCoords B S hS W F V e m + chartCoords B S hS W F V e m' :=
  (sectionsEquivFun B S hS W F V e).map_add m m'

/-- The coordinates of a scalar multiple of a section are the scalar multiple of its
coordinates. -/
theorem chartCoords_smul (V : SmallEtale B S hS W.1) {ι : Type u} [DecidableEq ι] [Finite ι]
    (e : F.over V ≅ SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι)
    (r : vectorBundleChartRing B S hS W V) (m : F.val.obj (op V)) :
    chartCoords B S hS W F V e (r • m) = r • chartCoords B S hS W F V e m :=
  (sectionsEquivFun B S hS W F V e).map_smul r m

/-! ### The comparison over the functions on a chart -/

section ChartRing

variable (F : Modules.{u, u} B S hS W.1 W.2)

/-- `Γ(U, Sym(ℰ))` as an algebra over the functions on the chart. Not an instance: the functions
on a chart carry several spellings, and this one is that of the base-change comparison of
`AlgebraicGeometry.Space.sectionsBaseChange`. -/
@[instance_reducible]
def chartSymAlgebra (U : SmallEtale B S hS W.1) :
    Algebra (chartRing B S hS W.1 W.2 U)
      ((symmetricAlgebraSheaf B S hS W F).right.obj.obj (op U)) :=
  @RingHom.toAlgebra (chartRing B S hS W.1 W.2 U)
    ((symmetricAlgebraSheaf B S hS W F).right.obj.obj (op U)) _ _
    ((symmetricAlgebraSheaf B S hS W F).algebraMap (op U))

/-- The degree-one inclusion `ℰ(U) ⟶ Γ(U, Sym(ℰ))`, a linear map over the functions on the
chart. -/
def chartSymGen (U : SmallEtale B S hS W.1) :
    letI := chartSymAlgebra B S hS W F U
    F.val.obj (op U) →ₗ[chartRing B S hS W.1 W.2 U]
      (symmetricAlgebraSheaf B S hS W F).right.obj.obj (op U) :=
  letI := chartSymAlgebra B S hS W F U
  { toFun := fun m => (symmetricAlgebra B S hS W F).ungradedIncl 1
      (((symmetricAlgebraGen B S hS W F).val.app (op U)) m)
    map_add' := fun m m' =>
      (congrArg ((symmetricAlgebra B S hS W F).ungradedIncl 1)
        (map_add ((symmetricAlgebraGen B S hS W F).val.app (op U)).hom m m')).trans
        ((symmetricAlgebra B S hS W F).ungradedIncl_add 1 (op U) _ _)
    map_smul' := fun r m =>
      (congrArg ((symmetricAlgebra B S hS W F).ungradedIncl 1)
        (((symmetricAlgebraGen B S hS W F).val.app (op U)).hom.map_smul r m)).trans
        ((symmetricAlgebra B S hS W F).ungradedIncl_smul 1 (op U) r _) }

/-- **The comparison `Sym_{𝒪(U)}(ℰ(U)) ⟶ Γ(U, Sym(ℰ))` over the functions on a chart**, as a
morphism of algebras: the map induced by the degree-one inclusion. -/
def chartSymAlgHom (U : SmallEtale B S hS W.1) :
    letI := chartSymAlgebra B S hS W F U
    SymmetricAlgebra (chartRing B S hS W.1 W.2 U) (F.val.obj (op U)) →ₐ[chartRing B S hS W.1 W.2 U]
      (symmetricAlgebraSheaf B S hS W F).right.obj.obj (op U) :=
  letI := chartSymAlgebra B S hS W F U
  SymmetricAlgebra.lift (chartSymGen B S hS W F U)

/-- The comparison over the functions on a chart sends the generator `ι m` to the degree-one
section `m`. -/
theorem chartSymAlgHom_ι (U : SmallEtale B S hS W.1) (m : F.val.obj (op U)) :
    letI := chartSymAlgebra B S hS W F U
    chartSymAlgHom B S hS W F U (SymmetricAlgebra.ι _ _ m) =
      (symmetricAlgebra B S hS W F).ungradedIncl 1
        (((symmetricAlgebraGen B S hS W F).val.app (op U)) m) := by
  let := chartSymAlgebra B S hS W F U
  exact SymmetricAlgebra.lift_ι_apply _ m

/-- The comparison over the functions on a chart sends the image of a function `r` in the
symmetric algebra to the image of `r` in `Γ(U, Sym(ℰ))`. -/
theorem chartSymAlgHom_algebraMap (U : SmallEtale B S hS W.1) (r : chartRing B S hS W.1 W.2 U) :
    letI := chartSymAlgebra B S hS W F U
    chartSymAlgHom B S hS W F U (algebraMap _ _ r) =
      (symmetricAlgebraSheaf B S hS W F).algebraMap (op U) r := by
  let := chartSymAlgebra B S hS W F U
  exact (chartSymAlgHom B S hS W F U).commutes r

/-- **The comparison over the functions on a chart is the comparison of
`AlgebraicGeometry.Space.SymAlgSections.symSectionsRingHom`**, read through the two spellings of
those functions. -/
theorem chartSymAlgHom_apply (U : SmallEtale B S hS W.1)
    (s : SymmetricAlgebra (chartRing B S hS W.1 W.2 U) (F.val.obj (op U))) :
    chartSymAlgHom B S hS W F U s = symSectionsRingHom B S hS W F U s := by
  let := chartSymAlgebra B S hS W F U
  induction s using SymmetricAlgebra.induction with
  | algebraMap r =>
    exact (chartSymAlgHom_algebraMap B S hS W F U r).trans
      (symSectionsRingHom_algebraMap B S hS W F U r).symm
  | ι m =>
    exact (chartSymAlgHom_ι B S hS W F U m).trans (symSectionsRingHom_ι B S hS W F U m).symm
  | mul a b ha hb =>
    exact ((map_mul (chartSymAlgHom B S hS W F U) a b).trans (congrArg₂ (· * ·) ha hb)).trans
      (map_mul (symSectionsRingHom B S hS W F U) a b).symm
  | add a b ha hb =>
    exact ((map_add (chartSymAlgHom B S hS W F U) a b).trans (congrArg₂ (· + ·) ha hb)).trans
      (map_add (symSectionsRingHom B S hS W F U) a b).symm

/-- **The comparison is compatible with restriction on generators.** -/
theorem map_chartSymAlgHom_ι {U V : SmallEtale B S hS W.1} (f : V ⟶ U) (m : F.val.obj (op U)) :
    letI := chartSymAlgebra B S hS W F U
    letI := chartSymAlgebra B S hS W F V
    ((symmetricAlgebraSheaf B S hS W F).right.obj.map f.op).hom
        (chartSymAlgHom B S hS W F U (SymmetricAlgebra.ι _ _ m)) =
      chartSymAlgHom B S hS W F V (SymmetricAlgebra.ι _ _ (F.val.map f.op m)) := by
  let := chartSymAlgebra B S hS W F U
  let := chartSymAlgebra B S hS W F V
  exact ((congrArg (((symmetricAlgebraSheaf B S hS W F).right.obj.map f.op).hom)
    (chartSymAlgHom_ι B S hS W F U m)).trans
      (map_ungradedIncl_symmetricAlgebraGen B S hS W F f m)).trans
    (chartSymAlgHom_ι B S hS W F V _).symm

/-- **Over an affine chart trivializing `ℰ` the comparison is bijective**: it is the
identification `AlgebraicGeometry.Space.SymAlgSections.symSectionsRingEquiv`. -/
theorem bijective_chartSymAlgHom (V : SmallEtale B S hS W.1)
    (hV : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    {ι : Type u} [DecidableEq ι] [Finite ι]
    (e : SheafOfModules.over (R := structureRingSheaf B S hS W) F V ≅
      SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι) :
    Function.Bijective (chartSymAlgHom B S hS W F V) := by
  have h : ⇑(chartSymAlgHom B S hS W F V) = ⇑(symSectionsRingEquiv B S hS W F V e hV) :=
    funext fun s => (chartSymAlgHom_apply B S hS W F V s).trans
      (symSectionsRingEquiv_apply B S hS W F V e hV s).symm
  rw [h]
  exact (symSectionsRingEquiv B S hS W F V e hV).bijective

/-- A trivialization of `ℰ` over a chart is a basis of its sections over the functions on the
chart. -/
def chartSectionsBasis (V : SmallEtale B S hS W.1) {ι : Type u} [DecidableEq ι] [Finite ι]
    (e : SheafOfModules.over (R := structureRingSheaf B S hS W) F V ≅
      SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι) :
    Module.Basis ι (chartRing B S hS W.1 W.2 V) (F.val.obj (op V)) :=
  Module.Basis.ofEquivFun
    { toFun := chartCoords B S hS W F V e
      invFun := (chartCoords B S hS W F V e).symm
      map_add' := chartCoords_add B S hS W F V e
      map_smul' := chartCoords_smul B S hS W F V e
      left_inv := (chartCoords B S hS W F V e).left_inv
      right_inv := (chartCoords B S hS W F V e).right_inv }

/-- **The base change of the sections of `ℰ` over an affine chart to an affine chart above it
trivializing `ℰ` on `ι ≃ n` is free on `n`**, `ℰ` being quasi-coherent. -/
def baseChangeSectionsBasis {U V : SmallEtale B S hS W.1} (f : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (hFq : SheafOfModules.IsQuasicoherentOnSite.{u + 1, u, u, u} F)
    {ι : Type u} [DecidableEq ι] [Finite ι]
    (e : SheafOfModules.over (R := structureRingSheaf B S hS W) F V ≅
      SheafOfModules.free (R := (structureRingSheaf B S hS W).over V) ι) {n : Type u} (ε : ι ≃ n) :
    letI := chartAlgebra (hF := W.2) f
    Module.Basis n (chartRing B S hS W.1 W.2 V)
      (TensorProduct (chartRing B S hS W.1 W.2 U) (chartRing B S hS W.1 W.2 V)
        (F.val.obj (op U))) :=
  letI := chartAlgebra (hF := W.2) f
  ((chartSectionsBasis B S hS W F V e).reindex ε).map
    (LinearEquiv.ofBijective (sectionsBaseChange F f)
      (bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS W.1 W.2 F hFq hU hV f)).symm

/-- **The comparison becomes bijective after base change to an affine chart trivializing `ℰ`.**
For a morphism `f : V ⟶ U` of affine charts with `ℰ` and `Sym(ℰ)` quasi-coherent and the
comparison over `V` bijective, the base change of the comparison over `U` along
`𝒪(U) ⟶ 𝒪(V)` is bijective: both sides are carried to the sections over `V` by the base-change
comparisons of the two quasi-coherent modules, and `Sym` commutes with base change. -/
theorem bijective_baseChange_chartSymAlgHom {U V : SmallEtale B S hS W.1} (f : V ⟶ U)
    (hU : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj U))
    (hV : IsAffine ((SmallEtale.toOver B S hS W.1 ⋙ BigFppfOver.toScheme B S hS).obj V))
    (hFq : SheafOfModules.IsQuasicoherentOnSite.{u + 1, u, u, u} F)
    (hAq : AlgebraSheaf.IsQuasicoherent (symmetricAlgebraSheaf B S hS W F))
    (hbij : Function.Bijective (chartSymAlgHom B S hS W F V)) :
    letI := chartAlgebra (hF := W.2) f
    letI := chartSymAlgebra B S hS W F U
    Function.Bijective
      ((chartSymAlgHom B S hS W F U).toLinearMap.baseChange (chartRing B S hS W.1 W.2 V)) := by
  let := chartAlgebra (hF := W.2) f
  let := chartSymAlgebra B S hS W F U
  let := chartSymAlgebra B S hS W F V
  let := chartSectionsModule F f
  have := chartSections_isScalarTower F f
  let : Algebra (chartRing B S hS W.1 W.2 U)
      ((symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V)) :=
    @RingHom.toAlgebra (chartRing B S hS W.1 W.2 U)
      ((symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V)) _ _
      (((symmetricAlgebraSheaf B S hS W F).algebraMap (op V)).comp (chartRestrict (hF := W.2) f))
  have : IsScalarTower (chartRing B S hS W.1 W.2 U) (chartRing B S hS W.1 W.2 V)
      ((symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V)) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  let resA : (symmetricAlgebraSheaf B S hS W F).right.obj.obj (op U) →ₐ[chartRing B S hS W.1 W.2 U]
      (symmetricAlgebraSheaf B S hS W F).right.obj.obj (op V) :=
    { ((symmetricAlgebraSheaf B S hS W F).right.obj.map f.op).hom with
      commutes' := fun r => (symmetricAlgebraSheaf B S hS W F).algebraMap_natural f.op r }
  exact SymmetricAlgebra.bijective_baseChange_of_comparison (chartSymAlgHom B S hS W F U)
    (chartSymAlgHom B S hS W F V) (chartRestrictLinear F f) resA
    (bijective_sectionsBaseChange_of_isQuasicoherentOnSite B S hS W.1 W.2 F hFq hU hV f)
    (AlgebraSheaf.bijective_sectionsBaseChange_of_isQuasicoherent
      (symmetricAlgebraSheaf B S hS W F) hAq hU hV f) hbij
    (map_chartSymAlgHom_ι B S hS W F f)

end ChartRing

end AlgebraicGeometry.Space.SymAlgSections

end
