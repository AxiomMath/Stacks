module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.AffineOpenSections
public import StacksFrontier.AlgebraicGeometry.AffineBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.AffineOpenSectionsBaseChange.Basic
public import StacksFrontier.AlgebraicGeometry.PullbackSections.Stalk
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartPushBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSchemeAlgebraBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SubalgebraChartSections
public import StacksFrontier.LinearAlgebra.TensorProduct.BaseRingAddEquiv

/-!
# Invertibility of the chart base-change comparison of a quasi-coherent algebra sheaf

Let `X` be an algebraic space over a scheme `S` in a big fppf site `B`, let `A` be a
*quasi-coherent* sheaf of commutative `𝒪_X`-algebras on the small étale site of `X`, and let
`h : V' ⟶ V` be a morphism of étale scheme charts of `X`.  This file proves that the module-level
chart base-change comparison `AlgebraicGeometry.Space.chartSchemeModuleBaseChangeHom` is an
isomorphism, and hence — through
`AlgebraicGeometry.Space.isIso_chartSchemeAlgebraBaseChangeHom_of_isIso_module` — that the
algebra-level comparison `AlgebraicGeometry.Space.chartSchemeAlgebraBaseChangeHom` is one too.

This is Descent, Proposition [Stacks, Tag 03DX] (2) in sheafified form: the restriction of a
quasi-coherent sheaf to the smaller chart scheme is the base change along `chartSchemeMap h` of
its restriction to the larger one.

## Main results

* `AlgebraicGeometry.Space.isIso_chartSchemeModuleBaseChangeHom`: **the module-level chart
  base-change comparison of a quasi-coherent algebra sheaf is invertible.**
* `AlgebraicGeometry.Space.isIso_chartSchemeAlgebraBaseChangeHom`: the algebra-level comparison
  is invertible.
* `AlgebraicGeometry.Space.bijective_chartSchemeModuleBaseChangeHom_app`: the comparison is
  bijective on sections over an affine open lying over an affine open, which is the local
  statement the global one is glued from.

## Implementation notes

**The shape of the argument.**  Affine opens are a basis on both chart schemes, so the affine
opens `U'` of `chartScheme V'` contained in the preimage of an affine open `V₀` of
`chartScheme V` cover `chartScheme V'`
(`AlgebraicGeometry.Space.exists_affineOpens_le_preimage_chartSchemeMap`), and
`Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover` reduces
invertibility to bijectivity on sections over such a `U'`.  Both modules are quasi-coherent, the
target by `AlgebraicGeometry.Space.isQuasicoherent_chartSchemeAlgebra` and the source by that
together with `Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback`
([Stacks, Tag 01BG]).

Over such a pair of affine opens there are two base changes of one and the same module of
sections `Γ(A|_V, V₀)`, both along the restriction of regular functions:

* the sections of the module pullback, by `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`
  read as a base change through
  `AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso`, and
* the sections of `A|_{V'}`, by Descent, Proposition [Stacks, Tag 03DX] (2) over the pair of
  étale charts the two opens cut out,
  `AlgebraicGeometry.Space.bijective_sectionsBaseChange_openChartRestrict`.

The comparison intertwines them: it carries a pulled-back section to the restriction map of `A`,
which is `AlgebraicGeometry.Space.chartSchemeModuleBaseChangeHom_app_pullbackSection`.  Two base
changes of one module along one ring map differing by a map of the targets force that map to be
bijective, which is the final step.

**Transporting the base change across the two base rings is the one step with content.**  The
chart-level statement is over `AlgebraicGeometry.Space.chartRing` of the étale charts cut out by
`V₀` and `U'`, the pullback-sections statement over `Γ(chartScheme V, V₀)` and
`Γ(chartScheme V', U')`.  The carriers of the module sections agree on the nose, and the two base
rings are isomorphic — by `AlgebraicGeometry.Scheme.restrictFunctorΓ`, packaged here as
`AlgebraicGeometry.Space.chartOpenRingEquiv` — compatibly with the two restriction maps, which is
`AlgebraicGeometry.Space.chartOpenRingEquiv_appLE` and is
`AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict` together with the
naturality of `AlgebraicGeometry.Space.chartSchemeRestrictionRingHom` in the open.  The tensor
products over the two base rings are then identified by `TensorProduct.addEquivOfRingEquiv`, which
moves the base ring and is exactly what `IsBaseChange.iff_of_equiv_comm` does not do.

**No scalar structure is created as an instance.**  The `Γ(chartScheme V, V₀)`-structures on the
functions on `U'` and on the sections of the pullback over `U'` are restrictions of scalars along
`AlgebraicGeometry.Scheme.Hom.appLE`, seated by `letI` in the shape
`AlgebraicGeometry.Scheme.Modules.pullbackSectionsModule` already uses, and the scalar tower is
`IsScalarTower.of_algebraMap_smul fun _ _ => rfl`.  The `chartRing`-action on a module of
sections of the chart restriction is the canonical
`AlgebraicGeometry.Space.AlgebraSheaf.sectionsModule`, seated by `letI` at the `Γ(A|_W, O)`
spelling of the carrier rather than at the
`A.right.obj.obj (op (openChart … W O))` spelling instance search would need; it is the same
structure, and seating it by name is what lets the two actions be compared by `rfl`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
* [Stacks Project, Tag 01SA](https://stacks.math.columbia.edu/tag/01SA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    {V' V : SmallEtale B S hS X.1} (h : V' ⟶ V)

/-! ### The two base rings -/

/-- **The functions on a Zariski open of a chart scheme are the functions on the étale chart that
open cuts out.**  This is `AlgebraicGeometry.Scheme.restrictFunctorΓ`, read through
`AlgebraicGeometry.Space.openChartFunctor_comp_toScheme`, as a ring isomorphism. -/
def chartOpenRingEquiv (W : SmallEtale B S hS X.1) (O : (chartScheme W).Opens) :
    Γ(chartScheme W, O) ≃+* chartRing B S hS X.1 X.2 (openChart B S hS X.1 W O) :=
  ((Scheme.restrictFunctorΓ (X := chartScheme W)).app (op O)).symm.commRingCatIsoToRingEquiv

/-- `chartOpenRingEquiv` is evaluation of the inverse of the component of
`AlgebraicGeometry.Scheme.restrictFunctorΓ` at `O`. -/
theorem chartOpenRingEquiv_apply (W : SmallEtale B S hS X.1) (O : (chartScheme W).Opens)
    (r : Γ(chartScheme W, O)) :
    chartOpenRingEquiv B S hS X W O r =
      ((Scheme.restrictFunctorΓ (X := chartScheme W)).inv.app (op O)).hom r :=
  rfl

/-- **The two base rings are identified compatibly with the two restriction maps.**  Restricting a
regular function from a Zariski open `V₀` of `chartScheme V` to a Zariski open `U'` of
`chartScheme V'` lying over it and then reading it on the étale chart `U'` cuts out is reading it
on the étale chart `V₀` cuts out and then restricting along the morphism of charts.

This is `AlgebraicGeometry.Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict` for the
restriction of `chartSchemeMap h` to `V₀` and its preimage, followed by the naturality of
`AlgebraicGeometry.Space.chartSchemeRestrictionRingHom` in the open for the inclusion
`U' ≤ chartSchemeMap h ⁻¹ᵁ V₀`. -/
theorem chartOpenRingEquiv_appLE {V₀ : (chartScheme V).Opens} {U' : (chartScheme V').Opens}
    (hle : U' ≤ chartSchemeMap h ⁻¹ᵁ V₀) (r : Γ(chartScheme V, V₀)) :
    chartOpenRingEquiv B S hS X V' U' (((chartSchemeMap h).appLE V₀ U' hle).hom r) =
      chartRestrict (hF := X.2)
          (openChartHomOfLE B S hS X.1 V' hle ≫ openChartRestrict B S hS X.1 h V₀)
        (chartOpenRingEquiv B S hS X V V₀ r) := by
  have hsq := ConcreteCategory.congr_hom
    (Scheme.restrictFunctorΓ_inv_app_comp_Γ_map_morphismRestrict (chartSchemeMap h) V₀) r
  have hnat := ConcreteCategory.congr_hom
    ((chartSchemeRestrictionRingHom B S hS X.1 V').naturality (homOfLE hle).op)
    (((chartSchemeMap h).app V₀).hom r)
  refine (hnat.trans (congrArg (fun w => chartRestrict (hF := X.2)
    (openChartHomOfLE B S hS X.1 V' hle) w) hsq.symm)).trans ?_
  exact (congrArg (fun φ => φ (chartOpenRingEquiv B S hS X V V₀ r))
    (chartRestrict_comp (hF := X.2) (openChartRestrict B S hS X.1 h V₀)
      (openChartHomOfLE B S hS X.1 V' hle))).symm

/-! ### The comparison on a pulled-back section -/

/-- **The module-level chart base-change comparison on a pulled-back section is the restriction
map of `A`** along the morphism of étale charts cut out by the two Zariski opens.

This is `AlgebraicGeometry.Space.chartSchemeModuleBaseChangeHom_app_unit` — which computes the
comparison on the image of the unit over `V₀` — followed by the naturality of the comparison for
the inclusion `U' ≤ chartSchemeMap h ⁻¹ᵁ V₀`, `AlgebraicGeometry.Scheme.Modules.pullbackSection`
being that image restricted to `U'`. -/
theorem chartSchemeModuleBaseChangeHom_app_pullbackSection
    {V₀ : (chartScheme V).Opens} {U' : (chartScheme V').Opens}
    (hle : U' ≤ chartSchemeMap h ⁻¹ᵁ V₀)
    (a : Γ((chartSchemeAlgebra B S hS X A V).underlyingModule, V₀)) :
    (chartSchemeModuleBaseChangeHom B S hS X A h).val.app (op U')
        (Scheme.Modules.pullbackSection (chartSchemeMap h)
          (chartSchemeAlgebra B S hS X A V).underlyingModule V₀ U' hle a) =
      A.right.obj.map (openChartHomOfLE B S hS X.1 V' hle ≫
          openChartRestrict B S hS X.1 h V₀).op
        (a : A.right.obj.obj (op (openChart B S hS X.1 V V₀))) := by
  have hnat := PresheafOfModules.naturality_apply
    (chartSchemeModuleBaseChangeHom B S hS X A h).val (homOfLE hle).op
    (PresheafOfModules.Hom.app ((Scheme.Modules.pullbackPushforwardAdjunction
        (chartSchemeMap h)).unit.app
      (chartSchemeAlgebra B S hS X A V).underlyingModule).val (op V₀) a)
  refine Eq.trans hnat ?_
  rw [chartSchemeModuleBaseChangeHom_app_unit B S hS X A h V₀ a]
  exact (ConcreteCategory.congr_hom
    (A.right.obj.map_comp (openChartRestrict B S hS X.1 h V₀).op
      (openChartHomOfLE B S hS X.1 V' hle).op) a).symm

/-! ### Bijectivity on sections over a pair of affine opens -/

/-- **The module-level chart base-change comparison of a quasi-coherent algebra sheaf is bijective
on sections over an affine open lying over an affine open.**

Both the sections of the pullback and the sections of `A|_{V'}` are base changes of
`Γ(A|_V, V₀)` along the restriction map `Γ(chartScheme V, V₀) ⟶ Γ(chartScheme V', U')` — the
first by `AlgebraicGeometry.affinePullbackSectionsBaseChangeIso`, the second by Descent,
Proposition [Stacks, Tag 03DX] (2) transported to that pair of rings — and the comparison is the
map of the two targets through which the two base-change maps factor. -/
theorem bijective_chartSchemeModuleBaseChangeHom_app (hA : A.IsQuasicoherent)
    {V₀ : (chartScheme V).Opens} {U' : (chartScheme V').Opens}
    (hV₀ : IsAffineOpen V₀) (hU' : IsAffineOpen U') (hle : U' ≤ chartSchemeMap h ⁻¹ᵁ V₀) :
    Function.Bijective
      ((chartSchemeModuleBaseChangeHom B S hS X A h).val.app (op U')) := by
  have : ((chartSchemeAlgebra B S hS X A V).underlyingModule).IsQuasicoherent :=
    isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  -- the scalar structures over the functions on `V₀` and on the chart it cuts out
  let algRT : Algebra Γ(chartScheme V, V₀) Γ(chartScheme V', U') :=
    ((chartSchemeMap h).appLE V₀ U' hle).hom.toAlgebra
  let modRP := Scheme.Modules.pullbackSectionsModule (chartSchemeMap h)
    (chartSchemeAlgebra B S hS X A V).underlyingModule V₀ U' hle
  have towerP : IsScalarTower Γ(chartScheme V, V₀) Γ(chartScheme V', U')
      Γ((Scheme.Modules.pullback (chartSchemeMap h)).obj
        (chartSchemeAlgebra B S hS X A V).underlyingModule, U') :=
    IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let modM : Module (chartRing B S hS X.1 X.2 (openChart B S hS X.1 V V₀))
      Γ((chartSchemeAlgebra B S hS X A V).underlyingModule, V₀) :=
    AlgebraSheaf.sectionsModule A (openChart B S hS X.1 V V₀)
  let modN : Module (chartRing B S hS X.1 X.2 (openChart B S hS X.1 V' U'))
      Γ((chartSchemeAlgebra B S hS X A V').underlyingModule, U') :=
    AlgebraSheaf.sectionsModule A (openChart B S hS X.1 V' U')
  let algChart := chartAlgebra (hF := X.2)
    (openChartHomOfLE B S hS X.1 V' hle ≫ openChartRestrict B S hS X.1 h V₀)
  -- the two scalar actions on a module of sections agree through `chartOpenRingEquiv`
  have hsmulM : ∀ (r : Γ(chartScheme V, V₀))
      (m : Γ((chartSchemeAlgebra B S hS X A V).underlyingModule, V₀)),
      r • m = chartOpenRingEquiv B S hS X V V₀ r • m := fun _ _ => rfl
  have hsmulN : ∀ (t : Γ(chartScheme V', U'))
      (y : Γ((chartSchemeAlgebra B S hS X A V').underlyingModule, U')),
      t • y = chartOpenRingEquiv B S hS X V' U' t • y := fun _ _ => rfl
  -- the comparison, as a map of the two modules of sections over `U'`
  set u := Scheme.Modules.sectionsLinearMap (chartSchemeModuleBaseChangeHom B S hS X A h) U'
    with hudef
  -- the sections of the pullback are a base change
  have hbc : IsBaseChange Γ(chartScheme V', U')
      (Scheme.Modules.pullbackSectionₗ (chartSchemeMap h)
        (chartSchemeAlgebra B S hS X A V).underlyingModule V₀ U' hle) :=
    AlgebraicGeometry.ModuleCat.isBaseChange_of_extendScalarsIso
      ((chartSchemeMap h).appLE V₀ U' hle).hom rfl
      (affinePullbackSectionsBaseChangeIso (chartSchemeMap h)
        (chartSchemeAlgebra B S hS X A V).underlyingModule hV₀ hU' hle) _
      fun m => affinePullbackSectionsBaseChangeIso_one_tmul (chartSchemeMap h)
        (chartSchemeAlgebra B S hS X A V).underlyingModule hV₀ hU' hle m
  -- the transport of the chart-level base change to the two rings of regular functions
  set Ψ := TensorProduct.addEquivOfRingEquiv (chartOpenRingEquiv B S hS X V V₀)
    (chartOpenRingEquiv B S hS X V' U').toAddEquiv
    (AddEquiv.refl Γ((chartSchemeAlgebra B S hS X A V).underlyingModule, V₀))
    (fun r p => (map_mul (chartOpenRingEquiv B S hS X V' U')
      (((chartSchemeMap h).appLE V₀ U' hle).hom r) p).trans
      (congrArg (fun z => z * chartOpenRingEquiv B S hS X V' U' p)
        (chartOpenRingEquiv_appLE B S hS X h hle r))) hsmulM with hΨdef
  set sbc := sectionsBaseChange A.underlyingModule
    (openChartHomOfLE B S hS X.1 V' hle ≫ openChartRestrict B S hS X.1 h V₀) with hsbc
  -- the comparison intertwines the two base changes
  have hcomm : ∀ z, u (hbc.equiv z) = sbc (Ψ z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero =>
      exact (congrArg u (map_zero hbc.equiv)).trans
        ((map_zero u).trans ((congrArg sbc (map_zero Ψ)).trans (map_zero sbc)).symm)
    | tmul t a =>
      refine Eq.trans (congrArg u (hbc.equiv_tmul t a)) ?_
      refine Eq.trans (u.map_smul t _) ?_
      refine Eq.trans (hsmulN t _) ?_
      exact congrArg
        (fun w : Γ((chartSchemeAlgebra B S hS X A V').underlyingModule, U') =>
          chartOpenRingEquiv B S hS X V' U' t • w)
        (chartSchemeModuleBaseChangeHom_app_pullbackSection B S hS X A h hle a)
    | add z z' hz hz' =>
      refine Eq.trans (congrArg u (map_add hbc.equiv z z')) ?_
      refine Eq.trans (map_add u _ _) ?_
      refine Eq.trans (congrArg₂ (· + ·) hz hz') ?_
      exact ((congrArg sbc (map_add Ψ z z')).trans (map_add sbc (Ψ z) (Ψ z'))).symm
  have hbijI := bijective_sectionsBaseChange_openChartRestrict B S hS X.1 X.2
    A.underlyingModule hA h hV₀ hU' hle
  have h2 : Function.Bijective fun z => sbc (Ψ z) := hbijI.comp Ψ.bijective
  refine (Function.Bijective.of_comp_iff u hbc.equiv.bijective).1 ?_
  rw [show u ∘ hbc.equiv = fun z => sbc (Ψ z) from funext hcomm]
  exact h2

/-! ### The cover and the global statement -/

/-- **The affine opens of a chart scheme lying over an affine open of a larger one cover it.**
Affine opens are a basis of both chart schemes, so every point has an affine open neighbourhood
lying over an affine open of the target. -/
theorem exists_affineOpens_le_preimage_chartSchemeMap (x : chartScheme V') :
    ∃ (V₀ : (chartScheme V).affineOpens) (U' : (chartScheme V').affineOpens),
      x ∈ U'.1 ∧ U'.1 ≤ chartSchemeMap h ⁻¹ᵁ V₀.1 := by
  obtain ⟨V₀, hV₀, hxV₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (chartScheme V).isBasis_affineOpens
    (show (chartSchemeMap h).base x ∈ (⊤ : (chartScheme V).Opens) from trivial)
  obtain ⟨U', hU', hxU', hU'le⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.mp
    (chartScheme V').isBasis_affineOpens
    (show x ∈ chartSchemeMap h ⁻¹ᵁ V₀ from hxV₀)
  exact ⟨⟨V₀, hV₀⟩, ⟨U', hU'⟩, hxU', hU'le⟩

/-- **The module-level chart base-change comparison of a quasi-coherent algebra sheaf is
invertible**: the module underlying the restriction of `A` to the smaller chart scheme is the
pullback along `chartSchemeMap h` of the module underlying its restriction to the larger one.

This is Descent, Proposition [Stacks, Tag 03DX] (2) in sheafified form.  It carries no hypothesis
beyond quasi-coherence of `A`. -/
theorem isIso_chartSchemeModuleBaseChangeHom (hA : A.IsQuasicoherent) :
    IsIso (chartSchemeModuleBaseChangeHom B S hS X A h) := by
  have : ((chartSchemeAlgebra B S hS X A V).underlyingModule).IsQuasicoherent :=
    isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  have : ((chartSchemeAlgebra B S hS X A V').underlyingModule).IsQuasicoherent :=
    isQuasicoherent_chartSchemeAlgebra B S hS X A hA V'
  have : ((Scheme.Modules.pullback (chartSchemeMap h)).obj
      (chartSchemeAlgebra B S hS X A V).underlyingModule).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback _ _
  choose V₀ U' hmem hle using exists_affineOpens_le_preimage_chartSchemeMap B S hS X h
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_bijective_app_of_isOpenCover
    (chartSchemeModuleBaseChangeHom B S hS X A h) (fun x => (U' x).1)
    (TopologicalSpace.IsOpenCover.mk (eq_top_iff.2 fun z _ =>
      TopologicalSpace.Opens.mem_iSup.2 ⟨z, hmem z⟩))
    (fun x => (U' x).2) fun x =>
      bijective_chartSchemeModuleBaseChangeHom_app B S hS X A h hA (V₀ x).2 (U' x).2 (hle x)

/-- **The algebra-level chart base-change comparison of a quasi-coherent algebra sheaf is
invertible**: the restriction of `A` to the smaller chart scheme is the base change along
`chartSchemeMap h` of its restriction to the larger one, as sheaves of commutative algebras.

This is `AlgebraicGeometry.Space.isIso_chartSchemeAlgebraBaseChangeHom_of_isIso_module` with its
hypothesis discharged by `AlgebraicGeometry.Space.isIso_chartSchemeModuleBaseChangeHom`. -/
theorem isIso_chartSchemeAlgebraBaseChangeHom (hA : A.IsQuasicoherent) :
    IsIso (chartSchemeAlgebraBaseChangeHom B S hS X A h) :=
  isIso_chartSchemeAlgebraBaseChangeHom_of_isIso_module B S hS X A h
    (isIso_chartSchemeModuleBaseChangeHom B S hS X A h hA)

end AlgebraicGeometry.Space

end
