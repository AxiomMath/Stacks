module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.FactorThroughOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.MorphismKernelIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentableOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedQuotientNoSupportedSections
import all StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsPushforward

/-!
# Supported functions and the kernel ideal of a morphism

Let `W` be an algebraic space over a scheme `S` contained in a big fppf site `B`, let `T` be a
closed set of points of `W` and let `n : W' ⟶ W` be a morphism of algebraic spaces.  This file
proves that **a regular function supported on `T` is killed by the structure map
`n♯ : 𝒪_W ⟶ n_*𝒪_{W'}` as soon as `𝒪_{W'}` has no nonzero local section supported on
`|n|^{-1}T`**:  the ideal of sections of `𝒪_W` supported on `T` is then contained in the kernel
ideal sheaf `AlgebraicGeometry.Space.kernelIdealSheaf` of `n`.

For `n` a closed immersion the kernel ideal sheaf is the defining ideal sheaf of Stacks 03MB,
`AlgebraicGeometry.Space.kernelIdealSheaf_eq_definingIdealSheaf`, so this is the statement that
the closed subspace `W'` is *contained in* the closed subspace cut out by the `T`-supported
functions — the half of such an identification that the geometry of `W'` supplies.

## Main results

* `AlgebraicGeometry.Space.eq_zero_of_sectionSupportedIn_of_range_subset_compl`: a regular
  function on an étale scheme chart `U` of `W` supported on `T` is killed by pullback along any
  morphism `p` of the site into `U` no point of whose source lies over `T`; the morphism is not
  required to be étale over `W`.
* `AlgebraicGeometry.Space.sectionSupportedIn_gamma_map_of_comp_eq`: the pullback of such a
  function along a chart of `W'` lying over `U` is supported on `|n|^{-1}T`.
* `AlgebraicGeometry.Space.supportedSectionsSubmodule_le_kernelIdealSheaf`: the conclusion,
  chartwise.

## Implementation notes

The first statement is the only place where the support condition has to be unwound.  A section
supported on the closed `T` dies on the open part of its chart lying off `T`, which is again an
étale chart by the correspondence of Stacks 03BZ between open subspaces and open sets of points
together with representability of an open subspace of a representable
(`AlgebraicGeometry.Space.isOpenSubspace_range_of_isOpenImmersion`); and a morphism of the site
into the chart whose points avoid `T` factors through that open part, by Stacks 03BZ again in the
form `AlgebraicGeometry.Space.factorsThrough_openSubspace_iff_points` followed by full
faithfulness of Yoneda.  Pullback of regular functions along the factorisation then kills the
function.

Everything after that is formal:  the support of the pullback is read off through
`AlgebraicGeometry.Space.sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen`, and the kernel
of the structure map over a chart is the set of functions whose pullback to every chart of `W'`
above the base-changed chart vanishes
(`AlgebraicGeometry.Space.mem_ker_structureSharp_iff`), each of which is such a pullback.

## References

* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `s` be a regular function on an étale chart `U` of `W` supported on the closed set `T`,
and let `p : a ⟶ U` be a morphism of the site, not necessarily étale over `W`, such that no point
of `a` maps into `T`. Then the pullback of `s` along `p` is zero. -/
theorem eq_zero_of_sectionSupportedIn_of_range_subset_compl
    (W : AlgebraicSpaces B S hS) (T : Set (points B S hS W.1)) (hT : IsClosed T)
    (U : SmallEtale B S hS W.1)
    (s : ToType ((SheafOfModules.unit (structureRingSheaf B S hS W)).val.obj (op U)))
    (hs : SectionSupportedIn B S hS W.1 W.2 T
      (SheafOfModules.unit (structureRingSheaf B S hS W)) U s)
    {a : BigFppfOver B S hS} (p : a ⟶ (SmallEtale.toOver B S hS W.1).obj U)
    (hp : Set.range (pointsMap B S hS (yoneda.obj a) (yoneda.map p ≫ U.1.hom)) ⊆ Tᶜ) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map p).op).hom s = 0 := by
  obtain ⟨U₀, i, hioi, hirange⟩ := exists_openSubchart B S hS W U
    (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS W.1).obj U)) U.1.hom ⁻¹' Tᶜ)
    (hT.isOpen_compl.preimage ((pointTopologyFamily B S hS).continuous
      (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _) W.2 U.1.hom))
  replace hioi : IsOpenImmersion B S hS (yoneda.map ((SmallEtale.toOver B S hS W.1).map i)) :=
    hioi
  have himage : ImageInOpen B S hS W.1
      (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS W.1).obj U)) U.1.hom ⁻¹' Tᶜ) i :=
    fun y => hirange ▸ Set.mem_range_self y
  have hzero : (SheafOfModules.unit (structureRingSheaf B S hS W)).val.map i.op s = 0 :=
    restrict_eq_zero_of_sectionSupportedIn_of_imageInOpen B S hS W T _ U s hs U₀ i himage
  have _ : Mono (yoneda.map ((SmallEtale.toOver B S hS W.1).map i)) :=
    mono_of_presheaf_isOpenImmersion hioi
  have hle : Set.range (pointsMap B S hS (yoneda.obj a) (yoneda.map p)) ⊆
      Set.range (pointsMap B S hS _
        (Subfunctor.range (yoneda.map ((SmallEtale.toOver B S hS W.1).map i))).ι) := by
    rw [range_pointsMap_ι_range B S hS _, hirange]
    rintro y ⟨z, rfl⟩
    have h1 : pointsMap B S hS (yoneda.obj a) (yoneda.map p ≫ U.1.hom) z ∈ Tᶜ := hp ⟨z, rfl⟩
    rw [pointsMap_comp] at h1
    exact h1
  obtain ⟨h, hh⟩ := (factorsThrough_openSubspace_iff_points B S hS
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS _)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS a) _
    (isOpenSubspace_range_of_isOpenImmersion _ _ hioi) (yoneda.map p)).2 hle
  set e := rangeIsoOfIsOpenImmersion _ (yoneda.map ((SmallEtale.toOver B S hS W.1).map i))
    hioi with he
  have hei := e.inv_comp_eq.2
    (Subfunctor.toRange_ι (yoneda.map ((SmallEtale.toOver B S hS W.1).map i))).symm
  obtain ⟨p', hp'⟩ : ∃ p' : a ⟶ (SmallEtale.toOver B S hS W.1).obj U₀,
      yoneda.map p' = h ≫ e.inv :=
    ⟨Functor.preimage _ (h ≫ e.inv), Functor.map_preimage _ _⟩
  have hfac : p' ≫ (SmallEtale.toOver B S hS W.1).map i = p :=
    Functor.map_injective yoneda
      (by rw [Functor.map_comp, hp', Category.assoc, hei, hh])
  rw [← hfac]
  exact ker_le_ker_comp B S hS p' ((SmallEtale.toOver B S hS W.1).map i) hzero

private theorem gamma_map_comp_apply {T₁ T₂ T₃ : BigFppfOver B S hS} (m : T₁ ⟶ T₂) (n : T₂ ⟶ T₃)
    (x : ToType (Scheme.Γ.obj (op ((BigFppfOver.toScheme B S hS).obj T₃)))) :
    (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map (m ≫ n)).op).hom x =
      (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map m).op).hom
        ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map n).op).hom x) := by
  rw [Functor.map_comp, op_comp, Functor.map_comp]
  rfl

/-- Let `n : W' ⟶ W` be a morphism of algebraic spaces, `s` a regular function on an étale chart
`U` of `W` supported on the closed set `T`, and `k : V ⟶ U` a morphism from an étale chart `V` of
`W'` lying over `n`. Then the pullback of `s` along `k` is supported on `|n|⁻¹ T`. -/
theorem sectionSupportedIn_gamma_map_of_comp_eq
    {W' W : AlgebraicSpaces B S hS} (n : W' ⟶ W)
    (T : Set (points B S hS W.1)) (hT : IsClosed T)
    (U : SmallEtale B S hS W.1)
    (s : ToType ((SheafOfModules.unit (structureRingSheaf B S hS W)).val.obj (op U)))
    (hs : SectionSupportedIn B S hS W.1 W.2 T
      (SheafOfModules.unit (structureRingSheaf B S hS W)) U s)
    (V : SmallEtale B S hS W'.1)
    (k : (SmallEtale.toOver B S hS W'.1).obj V ⟶ (SmallEtale.toOver B S hS W.1).obj U)
    (hk : yoneda.map k ≫ U.1.hom = V.1.hom ≫ n.hom) :
    SectionSupportedIn B S hS W'.1 W'.2 (pointsMap B S hS W'.1 n.hom ⁻¹' T)
      (SheafOfModules.unit (structureRingSheaf B S hS W')) V
      ((Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map k).op).hom s) := by
  refine sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen B S hS W' _
    (hT.preimage ((pointTopologyFamily B S hS).continuous W'.2 W.2 n.hom)) _ V _
    fun V₀ i hi => ?_
  have h0 : (Scheme.Γ.map ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS W'.1).map i ≫ k)).op).hom s = 0 := by
    refine eq_zero_of_sectionSupportedIn_of_range_subset_compl B S hS W T hT U s hs _ ?_
    rintro y ⟨z, rfl⟩
    have hcomp : yoneda.map ((SmallEtale.toOver B S hS W'.1).map i ≫ k) ≫ U.1.hom =
        yoneda.map ((SmallEtale.toOver B S hS W'.1).map i) ≫ V.1.hom ≫ n.hom := by
      rw [Functor.map_comp, Category.assoc, hk]
    have hz := hi z
    rw [Set.mem_preimage] at hz
    have hz' : pointsMap B S hS W'.1 n.hom
        (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS W'.1).obj V)) V.1.hom
          (pointsMap B S hS _ (yoneda.map ((SmallEtale.toOver B S hS W'.1).map i)) z)) ∉ T :=
      fun hmem => hz (Set.mem_preimage.2 hmem)
    rw [hcomp, pointsMap_comp, Function.comp_apply, pointsMap_comp, Function.comp_apply]
    exact hz'
  exact (gamma_map_comp_apply B S hS ((SmallEtale.toOver B S hS W'.1).map i) k s).symm.trans h0

/-- Let `n : W' ⟶ W` be a morphism of algebraic spaces and `T` a closed set of points of `W`. If
`𝒪_{W'}` has no nonzero local section supported on `|n|⁻¹ T`, then on every étale chart of `W` the
sections of `𝒪_W` supported on `T` lie in the kernel ideal sheaf of `n`. -/
theorem supportedSectionsSubmodule_le_kernelIdealSheaf
    {W' W : AlgebraicSpaces B S hS} (n : W' ⟶ W)
    (T : Set (points B S hS W.1)) (hT : IsClosed T)
    (hW' : HasNoSectionsSupportedIn B S hS W' (pointsMap B S hS W'.1 n.hom ⁻¹' T)
      (SheafOfModules.unit (structureRingSheaf B S hS W')))
    (U : (SmallEtale B S hS W.1)ᵒᵖ) :
    (supportedSectionsSubmodule B S hS W.1 W.2 T
        (SheafOfModules.unit (structureRingSheaf B S hS W))).toSubmodule.obj U ≤
      (kernelIdealSheaf B S hS n).toSubmodule.obj U := by
  intro s hs
  refine (mem_ker_structureSharp_iff B S hS n U.unop s).2 fun j => ?_
  have hsupp := (mem_supportedSectionsSubmodule_iff B S hS W.1 W.2 T
    (SheafOfModules.unit (structureRingSheaf B S hS W)) U.unop s).1 hs
  exact hW' j.right.unop _ (sectionSupportedIn_gamma_map_of_comp_eq B S hS n T hT U.unop s hsupp
    j.right.unop (chartBaseChangeMap B S hS n U.unop j)
    (chartDiagramOfIndex B S hS n U.unop j).comm.symm)

end AlgebraicGeometry.Space

end
