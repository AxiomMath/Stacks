module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleChartSchemeSite
public import StacksFrontier.AlgebraicGeometry.Topologies.AmbientTensorPresheaf

/-!
# The coefficient comparison `Γ(-, 𝒪) ⊗_R M ⟶ sections` on the slice at a chart

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `W` be an
étale chart of `F`, let `R = Γ(chartScheme W, 𝒪)` and let `G` be an `𝒪_F`-module whose sections
live at an arbitrary universe `max u m`.  Write `M = G(W)`, an `R`-module.  This file builds the
comparison

`Γ(Z, 𝒪) ⊗_R M ⟶ G(Z)`,  `a ⊗ x ↦ a • x|_Z`,

as a morphism of abelian presheaves on the slice of the small étale site at `W`, from the
ambient coefficient presheaf `AlgebraicGeometry.overTensorPresheaf` of the *bare* module `M`
read on the slice through `AlgebraicGeometry.Space.SmallEtale.sliceToOver`, to the abelian
presheaf underlying `G`; and it proves that the comparison is an isomorphism at every object of
the slice whose underlying scheme is affine, as soon as `G` is cartesian on affine charts.

## Why it is needed

The transport of [Stacks, Tag 03FJ] to the small étale site of an algebraic space at the
enlarged module universe,
`AlgebraicGeometry.Space.SmallEtale.isZero_cechCohomology_succ_of_overTensorPresheafIso`, takes
its coefficients as an identification of the restriction of an abelian presheaf to the slice at
`W` with `AlgebraicGeometry.overTensorPresheaf (chartScheme W) M`.  Producing that
identification for the abelian presheaf underlying an `𝒪_F`-module is what this file supplies,
and it is the step that
`AlgebraicGeometry.Space.exists_sliceAssociatedModule_iso_of_isQuasicoherentOnSite` cannot
supply: that statement produces an `Mᵃ` for a module `M` on the chart's *scheme*, whose sections
lie at the universe `u` of the schemes, so it is available only for a
`AlgebraicGeometry.Space.Modules.{u, u}`.  The comparison below is free in the universe of the
sections, because it is built from a bare module and the base change comparison
`AlgebraicGeometry.Space.sectionsBaseChange`, both of which are.

## Main definitions

* `AlgebraicGeometry.Space.SmallEtale.chartAbelianPresheaf`: the abelian presheaf underlying an
  `𝒪_F`-module, as a presheaf on the small étale site.
* `AlgebraicGeometry.Space.SmallEtale.tensorToChartSectionsApp`: the comparison at one object of
  the slice.
* `AlgebraicGeometry.Space.SmallEtale.tensorToChartSections`: **the comparison**, as a morphism
  of abelian presheaves on the slice at `W`.

## Main results

* `AlgebraicGeometry.Space.SmallEtale.tensorToChartSectionsApp_tmul`: the comparison sends
  `a ⊗ x` to `a • x|_Z`.
* `AlgebraicGeometry.Space.SmallEtale.isIso_tensorToChartSectionsApp`: **the comparison is an
  isomorphism at an object of the slice with affine underlying scheme**, when `W` is an affine
  chart and `G` is cartesian on affine charts.

## Implementation notes

**The comparison is an isomorphism only at the affine objects, and that is not an artefact.**
At a non-affine `Z` étale over an affine `W` the comparison genuinely fails to be an
isomorphism — the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/ChartSections.lean` give the example
`W = Spec k[x, y]`, `Z = W ∖ {(x, y)}` — so the isomorphism clause is stated pointwise and not
as a `CategoryTheory.NatIso`.  The same split is what `Stacks.Sites.tensorToSections` and
`Stacks.Sites.isIso_tensorToSectionsApp` carry for the associated presheaf of a quasi-coherent
module on a scheme, and for the same reason.

**The iso clause is `AlgebraicGeometry.Space.IsCartesianOnAffineCharts` directly.**  The
comparison at `Z` is, up to the identification of the two base rings, the base change
comparison `AlgebraicGeometry.Space.sectionsBaseChange` over the structure morphism of `Z`, and
that is precisely what `IsCartesianOnAffineCharts` asserts to be bijective.  No affine
base-change comparison on the chart's scheme is involved.

**The one base-change bookkeeping step.**  `AlgebraicGeometry.overTensorPresheaf` tensors over
the universe lift `ULift R` of the base ring, because the Amitsur side of [Stacks, Tag 023L]
does (`AlgebraicTopology.algebraMapArrow` lifts the base ring to a common universe with the
algebra), whereas `AlgebraicGeometry.Space.sectionsBaseChange` tensors over `R` itself.  The
bridge is `Stacks.Sites.uliftBaseTensorAddEquiv`, whose module argument is free in its universe.

**The comparison is built from the abelian presheaf, not from the presheaf of modules.**  The
values of `G` are modules over *varying* chart rings, so only their underlying abelian groups
form a presheaf; the restriction maps are then plain functorial maps and the semilinearity is a
single lemma, `AlgebraicGeometry.Space.SmallEtale.chartAbelianPresheaf_map_smul`.  This is the
arrangement of `Stacks.Sites.coeffFunctor` and `Stacks.Sites.coeffRestrict`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX), part (2)
* [Stacks Project, Tag 03FJ](https://stacks.math.columbia.edu/tag/03FJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct

universe m u

namespace AlgebraicGeometry.Space.SmallEtale

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (W : SmallEtale B S hS F) (G : Modules.{u, max u m} B S hS F hF)

/-! ### The two sides of the comparison -/

/-- The abelian presheaf underlying an `𝒪_F`-module: the underlying abelian sheaf of the module,
read as a presheaf on the small étale site.  Its sections over a chart are the sections of the
module, with their module structure forgotten. -/
abbrev chartAbelianPresheaf : (SmallEtale B S hS F)ᵒᵖ ⥤ AddCommGrpCat.{max u m} :=
  (sheafToPresheaf (SmallEtale.topology B S hS F) AddCommGrpCat.{max u m}).obj
    ((SheafOfModules.toSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)).obj G)

/-- The sections of `G` over a chart are a module over the chart ring, in the abelian-presheaf
spelling. -/
instance instModuleChartSections (V : SmallEtale B S hS F) :
    Module (chartRing B S hS F hF V)
      ((chartAbelianPresheaf B S hS F hF G).obj (op V) : Type (max u m)) :=
  inferInstanceAs (Module (chartRing B S hS F hF V) (G.val.obj (op V)))

/-- The sections of `G` over the chart `W` are a module over the coordinate ring of the chart's
scheme, in the `AlgebraicGeometry.Scheme.Γ` spelling that
`AlgebraicGeometry.overTensorPresheaf` asks for.  This is the module structure over
`AlgebraicGeometry.Space.chartRing`, the two spellings of the coordinate ring being equal by
`AlgebraicGeometry.Space.chartRing_eq_gammaTop`. -/
instance instModuleChartGammaSections :
    Module (Scheme.Γ.obj (op (chartScheme W)) : Type u)
      ((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m)) :=
  inferInstanceAs (Module (chartRing B S hS F hF W)
    ((chartAbelianPresheaf B S hS F hF G).obj (op W)))

/-- The coordinate algebra of an object of the slice at `W`: the value of
`AlgebraicGeometry.overGammaAlg` at its image under
`AlgebraicGeometry.Space.SmallEtale.sliceToOver`, which is the algebra the coefficient presheaf
tensors with. -/
abbrev sliceGammaAlg :
    (Over W)ᵒᵖ ⥤ CommAlgCat.{u} (ULift.{u} (Scheme.Γ.obj (op (chartScheme W)) : Type u)) :=
  (sliceToOver B S hS F W).op ⋙ overGammaAlg (chartScheme W)

/-- The sections of `G` over an object of the slice are a module over its coordinate algebra:
the carrier of `AlgebraicGeometry.Space.SmallEtale.sliceGammaAlg` is the chart ring. -/
instance instModuleSliceGammaAlg (Z : (Over W)ᵒᵖ) :
    Module (((sliceGammaAlg B S hS F W).obj Z : CommAlgCat.{u} _) : Type u)
      ((chartAbelianPresheaf B S hS F hF G).obj (op Z.unop.left) : Type (max u m)) :=
  inferInstanceAs (Module (chartRing B S hS F hF Z.unop.left)
    ((chartAbelianPresheaf B S hS F hF G).obj (op Z.unop.left)))

/-- **Restriction of sections of an `𝒪_F`-module along a chart morphism is semilinear**, the
scalar being carried across by `AlgebraicGeometry.Space.chartRestrict`.  This is the
semilinearity of `AlgebraicGeometry.Space.chartRestrictLinear`, read on the abelian presheaf. -/
theorem chartAbelianPresheaf_map_smul {U V : SmallEtale B S hS F} (f : V ⟶ U)
    (r : chartRing B S hS F hF U)
    (x : ((chartAbelianPresheaf B S hS F hF G).obj (op U) : Type (max u m))) :
    (chartAbelianPresheaf B S hS F hF G).map f.op (r • x) =
      chartRestrict (hF := hF) f r •
        (chartAbelianPresheaf B S hS F hF G).map f.op x := by
  let := chartSectionsModule G f
  exact map_smul (chartRestrictLinear G f) r x

/-- Restriction of a section of `G` over `W` to an object of the slice at `W`. -/
abbrev chartCoeffRestrict (Z : (Over W)ᵒᵖ) :
    (chartAbelianPresheaf B S hS F hF G).obj (op W) ⟶
      (chartAbelianPresheaf B S hS F hF G).obj (op Z.unop.left) :=
  (chartAbelianPresheaf B S hS F hF G).map Z.unop.hom.op

/-- Restriction is semilinear over the lifted base ring, which acts on the sections at `Z`
through the coordinate algebra of `Z`. -/
theorem chartCoeffRestrict_smul (Z : (Over W)ᵒᵖ)
    (c : ULift.{u} (Scheme.Γ.obj (op (chartScheme W)) : Type u))
    (x : ((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m))) :
    chartCoeffRestrict B S hS F hF W G Z (c • x) =
      algebraMap (ULift.{u} (Scheme.Γ.obj (op (chartScheme W)) : Type u))
          (((sliceGammaAlg B S hS F W).obj Z : CommAlgCat.{u} _) : Type u) c •
        chartCoeffRestrict B S hS F hF W G Z x :=
  chartAbelianPresheaf_map_smul B S hS F hF G Z.unop.hom c.down x

/-- The restriction maps of the abelian presheaf are semilinear for the coordinate-algebra
actions along a morphism of the slice. -/
theorem chartCoeffMap_smul {Z Z' : (Over W)ᵒᵖ} (g : Z ⟶ Z')
    (a : (((sliceGammaAlg B S hS F W).obj Z : CommAlgCat.{u} _) : Type u))
    (x : ((chartAbelianPresheaf B S hS F hF G).obj (op Z.unop.left) : Type (max u m))) :
    (chartAbelianPresheaf B S hS F hF G).map g.unop.left.op (a • x) =
      (sliceGammaAlg B S hS F W).map g a •
        (chartAbelianPresheaf B S hS F hF G).map g.unop.left.op x :=
  chartAbelianPresheaf_map_smul B S hS F hF G g.unop.left a x

/-! ### The comparison -/

/-- The bilinear data of the comparison: `(a, x) ↦ a • x|_Z`. -/
def chartTensorBilin (Z : (Over W)ᵒᵖ) :
    (((sliceGammaAlg B S hS F W).obj Z : CommAlgCat.{u} _) : Type u) →+
      (((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m)) →+
        ((chartAbelianPresheaf B S hS F hF G).obj (op Z.unop.left) : Type (max u m))) where
  toFun a :=
    { toFun := fun x => a • chartCoeffRestrict B S hS F hF W G Z x
      map_zero' := by simp only [map_zero, smul_zero]
      map_add' := fun x y => by simp only [map_add, smul_add] }
  map_zero' := AddMonoidHom.ext fun x => zero_smul _ _
  map_add' a b := AddMonoidHom.ext fun x => add_smul _ _ _

/-- The bilinear data on an argument pair. -/
theorem chartTensorBilin_apply (Z : (Over W)ᵒᵖ)
    (a : (((sliceGammaAlg B S hS F W).obj Z : CommAlgCat.{u} _) : Type u))
    (x : ((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m))) :
    chartTensorBilin B S hS F hF W G Z a x =
      a • chartCoeffRestrict B S hS F hF W G Z x := rfl

/-- The bilinear data is balanced over the lifted base ring, so it descends to the tensor
product. -/
theorem chartTensorBilin_balanced (Z : (Over W)ᵒᵖ)
    (c : ULift.{u} (Scheme.Γ.obj (op (chartScheme W)) : Type u))
    (a : (((sliceGammaAlg B S hS F W).obj Z : CommAlgCat.{u} _) : Type u))
    (x : ((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m))) :
    chartTensorBilin B S hS F hF W G Z (c • a) x =
      chartTensorBilin B S hS F hF W G Z a (c • x) := by
  rw [chartTensorBilin_apply, chartTensorBilin_apply, chartCoeffRestrict_smul,
    Algebra.smul_def, smul_smul, mul_comm]

/-- The comparison at one object of the slice at `W`. -/
def tensorToChartSectionsApp (Z : (Over W)ᵒᵖ) :
    ((sliceToOver B S hS F W).op ⋙
        overTensorPresheaf (chartScheme W)
          ((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m))).obj Z ⟶
      ((Over.forget W).op ⋙ chartAbelianPresheaf B S hS F hF G).obj Z :=
  AddCommGrpCat.ofHom (TensorProduct.liftAddHom (chartTensorBilin B S hS F hF W G Z)
    (chartTensorBilin_balanced B S hS F hF W G Z))

/-- The comparison sends the generator `a ⊗ x` to `a • x|_Z`. -/
theorem tensorToChartSectionsApp_tmul (Z : (Over W)ᵒᵖ)
    (a : (((sliceGammaAlg B S hS F W).obj Z : CommAlgCat.{u} _) : Type u))
    (x : ((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m))) :
    tensorToChartSectionsApp B S hS F hF W G Z
        (a ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op (chartScheme W)) : Type u)] x) =
      a • chartCoeffRestrict B S hS F hF W G Z x :=
  (TensorProduct.liftAddHom_tmul (chartTensorBilin B S hS F hF W G Z)
    (chartTensorBilin_balanced B S hS F hF W G Z) a x).trans
    (chartTensorBilin_apply B S hS F hF W G Z a x)

/-- The structure maps of the source of the comparison act on the first tensor factor only. -/
theorem overTensorPresheaf_slice_map_tmul {Z Z' : (Over W)ᵒᵖ} (g : Z ⟶ Z')
    (a : (((sliceGammaAlg B S hS F W).obj Z : CommAlgCat.{u} _) : Type u))
    (x : ((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m))) :
    ((sliceToOver B S hS F W).op ⋙
          overTensorPresheaf (chartScheme W)
            ((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m))).map g
        (a ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op (chartScheme W)) : Type u)] x) =
      (sliceGammaAlg B S hS F W).map g a
        ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op (chartScheme W)) : Type u)] x :=
  rfl

/-- **Naturality of the comparison, on generators.**  Stated with the tensor product spelled
out, so that the rewrites act on a type-correct goal, as in
`Stacks.Sites.tensorToSectionsApp_naturality`. -/
theorem tensorToChartSectionsApp_naturality {Z Z' : (Over W)ᵒᵖ} (g : Z ⟶ Z')
    (a : (((sliceGammaAlg B S hS F W).obj Z : CommAlgCat.{u} _) : Type u))
    (x : ((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m))) :
    tensorToChartSectionsApp B S hS F hF W G Z'
        ((sliceGammaAlg B S hS F W).map g a
          ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op (chartScheme W)) : Type u)] x) =
      (chartAbelianPresheaf B S hS F hF G).map g.unop.left.op
        (tensorToChartSectionsApp B S hS F hF W G Z
          (a ⊗ₜ[ULift.{u} (Scheme.Γ.obj (op (chartScheme W)) : Type u)] x)) := by
  rw [tensorToChartSectionsApp_tmul, tensorToChartSectionsApp_tmul, chartCoeffMap_smul]
  congr 1
  simp only [chartCoeffRestrict, ← ConcreteCategory.comp_apply,
    ← (chartAbelianPresheaf B S hS F hF G).map_comp, ← op_comp, Over.w g.unop]

/-- Two additive maps out of a tensor product agree as soon as they agree on the generators.
This is `Stacks.Sites.addHom_ext_tmul` with the second factor and the target at a universe
independent of the base ring's. -/
theorem addHom_ext_tmul_chart {Rr Aa : Type u} {Nn Pp : Type (max u m)} [CommRing Rr]
    [AddCommGroup Aa] [Module Rr Aa] [AddCommGroup Nn] [Module Rr Nn] [AddCommGroup Pp]
    {f h : Aa ⊗[Rr] Nn →+ Pp} (hfh : ∀ a n, f (a ⊗ₜ[Rr] n) = h (a ⊗ₜ[Rr] n)) : f = h := by
  refine AddMonoidHom.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul a n => exact hfh a n
  | add z w hz hw => rw [map_add, map_add, hz, hw]

/-- **The comparison, on all of the slice at `W`.**  The map
`Γ(Z, 𝒪) ⊗_R G(W) ⟶ G(Z)`, `a ⊗ x ↦ a • x|_Z`, from the ambient coefficient presheaf of the
bare module `G(W)`, read on the slice, to the abelian presheaf underlying `G`.

The naturality costs nothing beyond the semilinearity of the restriction maps and
functoriality of the abelian presheaf, because the comparison is given by the same formula at
*every* object of the slice; only the statement that it is an isomorphism needs affineness, and
that is `AlgebraicGeometry.Space.SmallEtale.isIso_tensorToChartSectionsApp`. -/
def tensorToChartSections :
    (sliceToOver B S hS F W).op ⋙
        overTensorPresheaf (chartScheme W)
          ((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m)) ⟶
      (Over.forget W).op ⋙ chartAbelianPresheaf B S hS F hF G where
  app Z := tensorToChartSectionsApp B S hS F hF W G Z
  naturality Z Z' g := by
    apply AddCommGrpCat.hom_ext
    refine addHom_ext_tmul_chart
      (Rr := ULift.{u} (Scheme.Γ.obj (op (chartScheme W)) : Type u))
      (Aa := (((sliceGammaAlg B S hS F W).obj Z : CommAlgCat.{u} _) : Type u))
      (Nn := ((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m)))
      (Pp := ((chartAbelianPresheaf B S hS F hF G).obj (op Z'.unop.left) : Type (max u m)))
      (fun a x => ?_)
    exact (congrArg (fun y => tensorToChartSectionsApp B S hS F hF W G Z' y)
        (overTensorPresheaf_slice_map_tmul B S hS F hF W G g a x)).trans
      (tensorToChartSectionsApp_naturality B S hS F hF W G g a x)

/-! ### The comparison is an isomorphism at an affine object of the slice -/

/-- **The comparison is an isomorphism at an object of the slice at `W` whose underlying scheme
is affine**, when `W` is an affine chart and `G` is cartesian on affine charts.

Both sides are additive maps out of `Γ(Z, 𝒪) ⊗_{ULift R} G(W)` and agree on the generators
`a ⊗ x`: the comparison sends `a ⊗ x` to `a • x|_Z` by
`AlgebraicGeometry.Space.SmallEtale.tensorToChartSectionsApp_tmul`, and so does
`AlgebraicGeometry.Space.sectionsBaseChange` over the structure morphism of `Z`, by
`AlgebraicGeometry.Space.chartBaseChange_tmul`, once the base ring is moved across
`Stacks.Sites.uliftBaseTensorAddEquiv`.  Bijectivity of the latter is exactly
`AlgebraicGeometry.Space.IsCartesianOnAffineCharts` at the structure morphism of `Z`. -/
theorem isIso_tensorToChartSectionsApp (hG : IsCartesianOnAffineCharts G)
    (hW : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W))
    (Z : (Over W)ᵒᵖ)
    (hZ : IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj
      Z.unop.left)) :
    IsIso (tensorToChartSectionsApp B S hS F hF W G Z) := by
  classical
  let := chartAlgebra (hF := hF) Z.unop.hom
  let := chartSectionsModule G Z.unop.hom
  let iA : Module (Scheme.Γ.obj (op (chartScheme W)) : Type u)
      (chartRing B S hS F hF Z.unop.left) := (chartAlgebra (hF := hF) Z.unop.hom).toModule
  let e := Stacks.Sites.uliftBaseTensorAddEquiv
    (Scheme.Γ.obj (op (chartScheme W)) : Type u) (chartRing B S hS F hF Z.unop.left)
    ((chartAbelianPresheaf B S hS F hF G).obj (op W)) iA
    (instModuleChartGammaSections B S hS F hF W G)
  obtain ⟨Ψ, hbij, hΨ⟩ : ∃ Ψ : _ →+ _, Function.Bijective Ψ ∧
      tensorToChartSectionsApp B S hS F hF W G Z = AddCommGrpCat.ofHom Ψ := by
    refine ⟨(sectionsBaseChange G Z.unop.hom).toAddMonoidHom.comp
        e.toAddMonoidHom, ?_, ?_⟩
    · exact (hG W Z.unop.left hW hZ Z.unop.hom).comp
        e.bijective
    · apply AddCommGrpCat.hom_ext
      refine addHom_ext_tmul_chart
        (Rr := ULift.{u} (Scheme.Γ.obj (op (chartScheme W)) : Type u))
        (Aa := (((sliceGammaAlg B S hS F W).obj Z : CommAlgCat.{u} _) : Type u))
        (Nn := ((chartAbelianPresheaf B S hS F hF G).obj (op W) : Type (max u m)))
        (Pp := ((chartAbelianPresheaf B S hS F hF G).obj (op Z.unop.left) : Type (max u m)))
        (fun a x => ?_)
      exact (tensorToChartSectionsApp_tmul B S hS F hF W G Z a x).trans
        (chartBaseChange_tmul G Z.unop.hom a x).symm
  rw [hΨ]
  exact (ConcreteCategory.isIso_iff_bijective _).2 hbij

end AlgebraicGeometry.Space.SmallEtale

end
