module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionReadingsIso
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionTwistSectionsReadBack
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartTopSectionReadings
public import StacksFrontier.AlgebraicGeometry.Spaces.IntTensorPowUntwist
public import StacksFrontier.AlgebraicGeometry.Spaces.InvertibleQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesTensorQuasicoherent

/-!
# The twist `𝓕 ⊗ L^{⊗ n}` in the proof of Stacks 0GUT: its module theory and its chart sections

Let `X` be an algebraic space over a scheme `S` and `L` an **invertible** `𝒪_X`-module on its
small étale site, with integer tensor powers `AlgebraicGeometry.Space.intTensorPowModule`.  The
proof of Stacks 0GUT runs over a twist `𝓗 = 𝓕 ⊗ L^{⊗ n}` of the quasi-coherent module `𝓕` whose
resolution is sought, and this file collects everything about that twist which does not mention
the morphism `f : X ⟶ Y`:

* the twist is quasi-coherent, and every tensor power of `L` is finite locally free;
* a family of global sections generating the twist on the scheme of an étale chart — which is
  what Stacks 01Q3 (7) produces there — yields a family of sections of the twist *over the
  chart* whose readings span over every affine open of the chart's scheme, which is the shape the
  epimorphism criterion of Stacks 03G3 consumes;
* a morphism `ψ : 𝒢 ⟶ 𝓕 ⊗ L^{⊗ n}` is turned into a morphism `𝒢 ⊗ L^{⊗ -n} ⟶ 𝓕`, an
  epimorphism as soon as `ψ` is.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_sheafTensor_intTensorPowModule`: the twist of a
  quasi-coherent module by a tensor power of `L` is quasi-coherent.
* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_intTensorPowModule`: every integer tensor
  power of `L` is finite locally free.
* `AlgebraicGeometry.Space.restrictToChartSchemeSheafTensorIntTensorPowModuleIso`: the two
  readings of the twist on the scheme of an étale chart agree — the monoidal one
  `(𝓕|_A) ⊗ (L|_A)^{⊗ n}` that Stacks 01Q3 is written in, and the chart restriction
  `AlgebraicGeometry.Space.restrictToChartScheme` of the twist that the chart-section machinery
  of Stacks 03G3 is written in.
* `AlgebraicGeometry.Space.exists_chartSections_hgen_sheafTensor_intTensorPowModule_of_isAmple`:
  **steps 1–3 of the remaining proof of Stacks 0GUT.**  For an étale chart `A` on whose scheme
  `L` restricts to an ample module, and a quasi-coherent `𝓕` of finite type, there is an `n₀`
  such that for every `n ≥ n₀` the twist `𝓕 ⊗ L^{⊗ n}` admits finitely many sections over `A`
  whose readings span its chart restriction over every affine open of the chart's scheme.
* `AlgebraicGeometry.Space.sheafTensorIntTensorPowUntwistMap` and
  `AlgebraicGeometry.Space.epi_sheafTensorIntTensorPowUntwistMap`: **step 6, untwisting.**

## Implementation notes

**Invertibility of `L` is the only hypothesis on `L`.**  It is a hypothesis of Stacks 0D31 and
hence of Stacks 0GUT, and it is what makes `AlgebraicGeometry.Space.intTensorPowModule` — and so
every statement below — definable at all.  Nothing here uses relative ampleness of `L`; the
ampleness that appears is ampleness of the *restriction* of `L` to the scheme of the chart, taken
as a hypothesis, because that is what relative ampleness supplies on a chart lying over an affine
chart of the target, through
`AlgebraicGeometry.Space.isAmple_chartRestrictionSchemeModule_of_isRelativelyAmple`.

**Which spanning statement is produced.**  Step 3,
`AlgebraicGeometry.Space.exists_generatingSections_chartTwistSections_of_isAmple`, hands over a
`SheafOfModules.GeneratingSections` of the monoidal reading `(𝓕|_A) ⊗ (L|_A)^{⊗ n}` *together*
with sections of the twist over `A` inducing its members.  Only the generating sections are used
below: `AlgebraicGeometry.Space.exists_chartSections_hgen_of_generatingSections` re-chooses
sections over the chart through `AlgebraicGeometry.Space.surjective_chartTopRead`, so no
compatibility between `AlgebraicGeometry.Space.chartTwistTopSection` and
`AlgebraicGeometry.Space.chartSectionsToRestrict` is needed, and the index type — hence its
finiteness — is carried through unchanged by
`SheafOfModules.GeneratingSections.equivOfIso`.

**Why the index type is existentially bound.**  Step 3's index type is that of the generating
sections it produces, which lives inside its own existential; the statement below therefore
produces `I` with `Finite I` rather than quantifying over a fixed finite type.

**Instances are supplied explicitly where `Epi` is concerned.**  Instance search for `Epi` and
for `IsIso` in `AlgebraicGeometry.Space.Modules` fails, getting stuck on universe constraints
raised while trying candidate instances for sheaves of modules — even on `Iso.refl`.  The two
isomorphisms appearing in `AlgebraicGeometry.Space.epi_sheafTensorIntTensorPowUntwistMap` are
therefore shown to be epimorphisms by applying `CategoryTheory.IsIso.epi_of_iso` to
`CategoryTheory.Iso.isIso_hom` by hand rather than by `inferInstance`, and the composite is
assembled with `CategoryTheory.epi_comp'`, which takes its two inputs as arguments.

**No tag is claimed.**  Stacks 0GUT is registered on the theorem that proves it, in
`StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ResolutionPropertyRelativeAmpleMain`; these are
steps of its proof.

## References

* [Stacks Project, Tag 0GUT](https://stacks.math.columbia.edu/tag/0GUT)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 0B8Q](https://stacks.math.columbia.edu/tag/0B8Q)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.MonoidalCategory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory
attribute [local instance] Stacks.SheafInternalHom.schemeMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)
  (L : Modules.{u, u} B S hS X.1 X.2) [IsInvertibleModule X L]

/-! ### The module theory of a twist by a tensor power -/

/-- **Stacks 03M1 (5) for a twist.**  The tensor product of a quasi-coherent `𝒪_X`-module with an
integer tensor power of an invertible module is quasi-coherent, in the
`Stacks.SheafOfModules.Tensor.sheafTensor` spelling.

Every tensor power of `L` is quasi-coherent by Stacks 0B8Q
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_intTensorPowModule`), the monoidal tensor product
of two quasi-coherent modules is quasi-coherent by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorObj`, and
`AlgebraicGeometry.Space.modulesTensorObjIso` identifies that tensor product with this one. -/
theorem isQuasicoherentOnSite_sheafTensor_intTensorPowModule
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (n : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS X.1 X.2)).obj F).obj
        (intTensorPowModule B S hS X L n)).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (modulesTensorObjIso B S hS X.1 X.2 F (intTensorPowModule B S hS X L n))
    (isQuasicoherentOnSite_tensorObj B S hS X.1 X.2 F (intTensorPowModule B S hS X L n))

/-- **Every integer tensor power of an invertible `𝒪_X`-module is finite locally free.**  The
power is invertible by Stacks 01CT (`AlgebraicGeometry.SheafOfModules.isInvertible_tensorPow`),
and an invertible module on the small étale site of an algebraic space is finite locally free of
rank one by Stacks 0B8Q
(`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_one_of_isInvertible`). -/
theorem isFiniteLocallyFreeOnSite_intTensorPowModule (n : ℤ) :
    SheafOfModules.IsFiniteLocallyFreeOnSite (intTensorPowModule B S hS X L n) :=
  (isFiniteLocallyFreeOfRank_one_of_isInvertible B S hS X (intTensorPowModule B S hS X L n)
    (AlgebraicGeometry.SheafOfModules.isInvertible_tensorPow (structureSheaf B S hS X.1 X.2).obj
      (structureRingPresheaf_isSheaf B S hS X.1 X.2) L n)).isFiniteLocallyFreeOnSite

/-! ### Steps 1–3: the chart sections of a twist -/

/-- **The two readings of a twist on the scheme of an étale chart agree.**  The monoidal reading
`(𝓕|_A) ⊗ (L|_A)^{⊗ n}`, in which Stacks 01Q3 states global generation on the chart's scheme, is
isomorphic to the chart restriction `AlgebraicGeometry.Space.restrictToChartScheme` of the twist
`𝓕 ⊗ L^{⊗ n}`, in which the chart-section machinery of Stacks 03G3 is written.

This is `AlgebraicGeometry.Space.chartRestrictionSchemeModuleTensorPowModuleIso` reversed,
followed by `AlgebraicGeometry.Space.restrictToChart_eq_restrictToChartScheme`, which identifies
the two parallel restrictions of a module to the chart's scheme. -/
def restrictToChartSchemeSheafTensorIntTensorPowModuleIso (A : SmallEtale B S hS X.1)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (n : ℤ) :
    (chartRestrictionSchemeModule B S hS X F A ⊗
        Stacks.Ample.tensorPowModule (chartScheme A)
          (chartRestrictionSchemeModule B S hS X L A) n) ≅
      restrictToChartScheme B S hS X.1 X.2
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS X.1 X.2)).obj F).obj (intTensorPowModule B S hS X L n)) A :=
  (chartRestrictionSchemeModuleTensorPowModuleIso B S hS X L A F n).symm ≪≫
    eqToIso (restrictToChart_eq_restrictToChartScheme B S hS X.2 _ A)

/-- **Steps 1–3 of the remaining proof of Stacks 0GUT.**  Let `L` be an invertible `𝒪_X`-module
whose restriction to the scheme of an étale chart `A` is ample, and let `𝓕` be a quasi-coherent
`𝒪_X`-module of finite type.  Then there is an `n₀` such that for every `n ≥ n₀` there are a
finite index type `I` and sections `a i` of the twist `𝓕 ⊗ L^{⊗ n}` over the chart `A` whose
readings over every affine open of `chartScheme A` span the sections of the chart restriction of
the twist there.

That spanning statement is, verbatim, the hypothesis `hgen` of
`AlgebraicGeometry.Space.spanSieve_moduleFMapSpanningSet_mem_of_span_chartSectionsToRestrict`,
the local-generation criterion over a surjective étale chart.

The proof is Stacks 01Q3 (7) on the chart's scheme, in the form
`AlgebraicGeometry.Space.exists_generatingSections_chartTwistSections_of_isAmple`, whose
generating sections are carried to the chart restriction of the twist along
`AlgebraicGeometry.Space.restrictToChartSchemeSheafTensorIntTensorPowModuleIso` and handed to
`AlgebraicGeometry.Space.exists_chartSections_hgen_of_generatingSections`.  The sections over the
chart which step 3 itself produces are not used: the index type is all that is transported, and
the sections over the chart are re-chosen from the global sections of the chart restriction. -/
theorem exists_chartSections_hgen_sheafTensor_intTensorPowModule_of_isAmple
    (A : SmallEtale B S hS X.1)
    (hamp : Stacks.Ample.IsAmple (chartScheme A) (chartRestrictionSchemeModule B S hS X L A))
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hFft : SheafOfModules.IsFiniteTypeOnSite F) :
    ∃ n₀ : ℤ, ∀ n : ℤ, n₀ ≤ n →
      ∃ (I : Type u) (_ : Finite I)
        (a : I → (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
          (structureSheaf B S hS X.1 X.2)).obj F).obj
            (intTensorPowModule B S hS X L n)).val.obj (op A)),
        ∀ O : (chartScheme A).Opens, IsAffineOpen O →
          ∀ y : (restrictToChartScheme B S hS X.1 X.2
              (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
                (structureSheaf B S hS X.1 X.2)).obj F).obj
                  (intTensorPowModule B S hS X L n)) A).val.obj (op O),
            y ∈ Submodule.span ((chartScheme A).ringCatSheaf.obj.obj (op O))
              (Set.range fun i => chartSectionsToRestrict X _ A O
                ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
                  (structureSheaf B S hS X.1 X.2)).obj F).obj
                    (intTensorPowModule B S hS X L n)).val.map
                  (openChartInclusion B S hS X.1 A O).op (a i))) := by
  obtain ⟨n₀, hn₀⟩ :=
    exists_generatingSections_chartTwistSections_of_isAmple B S hS X L A hamp F hFft
  refine ⟨n₀, fun n hn => ?_⟩
  obtain ⟨σ, hσfin, -⟩ := hn₀ n hn
  refine ⟨σ.I, hσfin, ?_⟩
  exact exists_chartSections_hgen_of_generatingSections X _ A
    (isQuasicoherentOnSite_sheafTensor_intTensorPowModule B S hS X L F n)
    (SheafOfModules.GeneratingSections.equivOfIso
      (restrictToChartSchemeSheafTensorIntTensorPowModuleIso B S hS X L A F n) σ)

/-! ### Step 6: untwisting -/

/-- **Untwisting a morphism into a twist.**  A morphism `ψ : 𝒢 ⟶ 𝓕 ⊗ L^{⊗ n}` tensored by
`L^{⊗ -n}` and read through the untwisting isomorphism is a morphism `𝒢 ⊗ L^{⊗ -n} ⟶ 𝓕`, with
the source formed by `AlgebraicGeometry.Space.modulesMonoidalCategory` — the tensor product for
which `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_tensorObj` is stated.

The bridge between the two tensor products is `AlgebraicGeometry.Space.modulesTensorObjIso` and
the untwisting isomorphism is
`AlgebraicGeometry.Space.sheafTensorIntTensorPowUntwistIso`. -/
def sheafTensorIntTensorPowUntwistMap (F G : Modules.{u, u} B S hS X.1 X.2) (n : ℤ)
    (ψ : G ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS X.1 X.2)).obj F).obj (intTensorPowModule B S hS X L n))) :
    G ⊗ intTensorPowModule B S hS X L (-n) ⟶ F :=
  (modulesTensorObjIso B S hS X.1 X.2 G (intTensorPowModule B S hS X L (-n))).hom ≫
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS X.1 X.2)).map ψ).app (intTensorPowModule B S hS X L (-n))) ≫
    (sheafTensorIntTensorPowUntwistIso B S hS X L F n).hom

/-- **Step 6 of the remaining proof of Stacks 0GUT: untwisting preserves surjectivity.**  If
`ψ : 𝒢 ⟶ 𝓕 ⊗ L^{⊗ n}` is an epimorphism then so is the untwisted morphism
`𝒢 ⊗ L^{⊗ -n} ⟶ 𝓕`.

Tensoring by `L^{⊗ -n}` is an equivalence, hence preserves epimorphisms
(`AlgebraicGeometry.Space.epi_sheafTensor_map_app_intTensorPowModule_iff`), and the two
isomorphisms the untwisted morphism is composed with are epimorphisms. -/
theorem epi_sheafTensorIntTensorPowUntwistMap (F G : Modules.{u, u} B S hS X.1 X.2) (n : ℤ)
    (ψ : G ⟶ (((Stacks.SheafOfModules.Tensor.sheafTensor.{u + 1, u, u, u, u}
      (structureSheaf B S hS X.1 X.2)).obj F).obj (intTensorPowModule B S hS X L n)))
    (hψ : Epi ψ) :
    Epi (sheafTensorIntTensorPowUntwistMap B S hS X L F G n ψ) :=
  epi_comp' (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _))
    (epi_comp' ((epi_sheafTensor_map_app_intTensorPowModule_iff B S hS X L (-n) ψ).mpr hψ)
      (@IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_hom _)))

end AlgebraicGeometry.Space

end
