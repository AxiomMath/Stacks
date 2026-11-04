module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedQuotientNoSupportedSections
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsSubsheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSectionsEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.StrictTransformUniversalProperty

/-!
# Sections supported on a union, and supported sections after an étale pullback

Let `X` be an algebraic space over `S` and let `T₁` and `T₂` be subsets of its points.  A
section of an `𝒪_X`-module supported on `T₁ ∪ T₂` need not be supported on `T₂` alone; it is
so as soon as, over the part of `X` lying off `T₂`, the module has no nonzero local section
supported on `T₁`.  That is the reduction proved here, together with the two facts about
supported sections and étale pullback that the hypothesis is checked with in practice.

## Main results

* `AlgebraicGeometry.Space.supportedSectionsSubmodule_union_eq_of_isEtale`: for `T₂` closed and
  an étale `j : V ⟶ X` carrying exactly the points off `T₂`, if `M|_V` has no nonzero local
  section supported on `|j|⁻¹T₁` then the sections of `M` supported on `T₁ ∪ T₂` are those
  supported on `T₂`.  This is the space-level counterpart of the scheme-level
  `AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule_union_eq`.
* `AlgebraicGeometry.Space.supportedSectionsSubmodule_union_eq`: the same reduction with no
  morphism in sight — for `T` closed and `W` arbitrary, if every section supported on `W` over a
  chart whose points avoid `T` vanishes, then the sections supported on `T ∪ W` are those
  supported on `T`.  This is the form the enlargement of a blowup centre by a divisor uses.
* `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_etaleModulePullback`: having no nonzero
  local section supported on `T` passes to the étale pullback, at the inverse image of `T`.
* `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_of_iso`: it is invariant under an
  isomorphism of modules.
* `AlgebraicGeometry.Space.etaleModulePullbackModulePullbackIso`: the étale pullback of a
  pullback is the pullback along the composite, as the étale pullback of Stacks 03LV.
* `AlgebraicGeometry.Space.etaleModulePullback_map_supportedSections_ι_eq_zero` and
  `AlgebraicGeometry.Space.isIso_etaleModulePullback_map_modulePullback_map_cokernelProjection`:
  along a pullback no point of whose source lies over `T`, the inclusion of the sections
  supported on `T` becomes zero and the projection onto the quotient by them becomes an
  isomorphism.

## Implementation notes

The reduction is the maximality of the open zero locus of Stacks 04KA in the two directions
already recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/SupportedQuotientNoSupportedSections.lean`: a section is
supported on the closed `T₂` exactly when it dies on every subchart lying over `T₂ᶜ`
(`AlgebraicGeometry.Space.sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen`), and such a
subchart comes from a chart of `V`
(`AlgebraicGeometry.Space.exists_factorisation_smallEtalePostcomp`), on which the restricted
section is supported on `T₁` because its support lies in `T₁ ∪ T₂` and the chart misses `T₂`.

The hypothesis is phrased with an étale `j : V ⟶ X` and the factorisation property rather than
with an open subspace, as in the module just cited: the open subspace is substituted by the
consumer, and keeping `j` opaque is what makes the statement elaborate.

## References

* [Stacks Project, Tag 0859](https://stacks.math.columbia.edu/tag/0859)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-! ### Supported sections and étale pullback -/

/-- **Having no nonzero local section supported on `T` passes to an étale pullback.**  For an
étale `h : V ⟶ X` and an `𝒪_X`-module `M` with no nonzero local section supported on `T`, the
pullback `M|_V` has no nonzero local section supported on `|h|⁻¹T`.

A section of `M|_V` over a chart `W` of `V` *is* a section of `M` over the composite chart, and
being supported on `|h|⁻¹T` there is being supported on `T` here, by
`AlgebraicGeometry.Space.sectionSupportedIn_etaleModulePullback_iff`. -/
theorem hasNoSectionsSupportedIn_etaleModulePullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V X : AlgebraicSpaces B S hS} (h : V ⟶ X) (hh : IsEtale B S hS h.hom)
    (T : Set (points B S hS X.1)) (M : Modules.{u, u} B S hS X.1 X.2)
    (hM : HasNoSectionsSupportedIn B S hS X T M) :
    HasNoSectionsSupportedIn B S hS V (pointsMap B S hS V.1 h.hom ⁻¹' T)
      ((etaleModulePullback B S hS h hh).obj M) := fun W s hs =>
  hM ((smallEtalePostcomp B S hS h hh).obj W) s
    ((sectionSupportedIn_etaleModulePullback_iff B S hS h hh T M W s).mp hs)

/-- **Having no nonzero local section supported on `T` is invariant under an isomorphism of
modules**, being the case of
`AlgebraicGeometry.Space.hasNoSectionsSupportedIn_of_injective` at an isomorphism. -/
theorem hasNoSectionsSupportedIn_of_iso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : AlgebraicSpaces B S hS} (T : Set (points B S hS X.1))
    {M N : Modules.{u, u} B S hS X.1 X.2} (ψ : M ≅ N)
    (hN : HasNoSectionsSupportedIn B S hS X T N) :
    HasNoSectionsSupportedIn B S hS X T M :=
  hasNoSectionsSupportedIn_of_injective T ψ.hom
    (fun W => PresheafOfModules.injective_of_mono
      ((SheafOfModules.forget _).map ψ.hom) (op W)) hN

/-- **The étale pullback of a pullback is the pullback along the composite.**  For an étale
`j : V ⟶ Q`, a morphism `q : Q ⟶ X` whose composite with `j` is étale, and an `𝒪_X`-module `M`,
the étale restriction to `V` of `q^*M` is the étale restriction of `M` along `j ≫ q`.

Both étale pullbacks are compared with the pullback of Stacks 03LU by Stacks 03LW,
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`, and in between the two
pullbacks compose by `AlgebraicGeometry.Space.modulePullbackCompIso`. -/
def etaleModulePullbackModulePullbackIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V Q X : AlgebraicSpaces B S hS} (j : V ⟶ Q) (hj : IsEtale B S hS j.hom) (q : Q ⟶ X)
    (hjq : IsEtale B S hS (j ≫ q).hom) (M : Modules.{u, u} B S hS X.1 X.2) :
    (etaleModulePullback B S hS j hj).obj ((modulePullback B S hS q).obj M) ≅
      (etaleModulePullback B S hS (j ≫ q) hjq).obj M :=
  (((modulePullbackIsoEtaleModulePullback B S hS j hj).app
      ((modulePullback B S hS q).obj M)).symm.trans
    ((modulePullbackCompIso B S hS j q).app M)).trans
      ((modulePullbackIsoEtaleModulePullback B S hS (j ≫ q) hjq).app M)

/-- **A pullback inherits having no nonzero local section supported on `T`, étale-locally.**
For an étale `j : V ⟶ Q`, a morphism `q : Q ⟶ X` with `j ≫ q` étale and an `𝒪_X`-module `M`
with no nonzero local section supported on `T`, the étale restriction of `q^*M` to `V` has no
nonzero local section supported on `|j|⁻¹|q|⁻¹T`.

This is `AlgebraicGeometry.Space.hasNoSectionsSupportedIn_etaleModulePullback` along `j ≫ q`,
carried across `AlgebraicGeometry.Space.etaleModulePullbackModulePullbackIso`. -/
theorem hasNoSectionsSupportedIn_etaleModulePullback_modulePullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V Q X : AlgebraicSpaces B S hS} (j : V ⟶ Q) (hj : IsEtale B S hS j.hom) (q : Q ⟶ X)
    (hjq : IsEtale B S hS (j ≫ q).hom) (T : Set (points B S hS X.1))
    (M : Modules.{u, u} B S hS X.1 X.2) (hM : HasNoSectionsSupportedIn B S hS X T M) :
    HasNoSectionsSupportedIn B S hS V
      (pointsMap B S hS V.1 j.hom ⁻¹' (pointsMap B S hS Q.1 q.hom ⁻¹' T))
      ((etaleModulePullback B S hS j hj).obj ((modulePullback B S hS q).obj M)) := by
  have hset : pointsMap B S hS V.1 (j ≫ q).hom ⁻¹' T =
      pointsMap B S hS V.1 j.hom ⁻¹' (pointsMap B S hS Q.1 q.hom ⁻¹' T) := by
    rw [show (j ≫ q).hom = j.hom ≫ q.hom from rfl, pointsMap_comp]
    rfl
  refine hasNoSectionsSupportedIn_of_iso B S hS _
    (etaleModulePullbackModulePullbackIso B S hS j hj q hjq M) ?_
  exact hset ▸ hasNoSectionsSupportedIn_etaleModulePullback B S hS (j ≫ q) hjq T M hM

/-! ### Sections supported on a union -/

/-- **Sections supported on `T₁ ∪ T₂` are those supported on `T₂`, when `T₁` carries no
sections off `T₂`.**  Let `T₂` be a closed subset of the points of an algebraic space `X`, let
`j : V ⟶ X` be an étale monomorphism whose points lie off `T₂` and through which every morphism
from a representable presheaf with all points off `T₂` factors, and let `M` be an `𝒪_X`-module
whose étale restriction to `V` has no nonzero local section supported on `|j|⁻¹T₁`.  Then the
submodule of sections of `M` supported on `T₁ ∪ T₂` is the submodule of those supported on
`T₂`.

One inclusion is monotonicity of the support condition.  For the other, a section supported on
`T₁ ∪ T₂` is supported on the closed `T₂` as soon as it dies on every subchart lying over
`T₂ᶜ`, by `AlgebraicGeometry.Space.sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen`; such
a subchart comes from a chart of `V`, where the restricted section is supported on `T₁` — its
support lies in `T₁ ∪ T₂` and the chart misses `T₂` — hence is zero by hypothesis.

This is the space-level counterpart of the scheme-level
`AlgebraicGeometry.Scheme.Modules.supportedSectionsSubmodule_union_eq`. -/
theorem supportedSectionsSubmodule_union_eq_of_isEtale
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {V X : AlgebraicSpaces B S hS} (j : V ⟶ X) (hj : IsEtale B S hS j.hom) [Mono j.hom]
    (T₁ T₂ : Set (points B S hS X.1)) (hT₂ : IsClosed T₂)
    (hfac : ∀ (A : BigFppfOver B S hS) (f : yoneda.obj A ⟶ X.1),
      Set.range (pointsMap B S hS (yoneda.obj A) f) ⊆ T₂ᶜ → ∃ g, g ≫ j.hom = f)
    (hVrange : Set.range (pointsMap B S hS V.1 j.hom) ⊆ T₂ᶜ)
    (M : Modules.{u, u} B S hS X.1 X.2)
    (hV : HasNoSectionsSupportedIn B S hS V (pointsMap B S hS V.1 j.hom ⁻¹' T₁)
      ((etaleModulePullback B S hS j hj).obj M)) :
    supportedSectionsSubmodule B S hS X.1 X.2 (T₁ ∪ T₂) M =
      supportedSectionsSubmodule B S hS X.1 X.2 T₂ M := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun W₀ => ?_)
  obtain ⟨W⟩ := W₀
  ext s
  refine Iff.trans (mem_supportedSectionsSubmodule_iff B S hS X.1 X.2 (T₁ ∪ T₂) M W s)
    (Iff.trans ?_ (mem_supportedSectionsSubmodule_iff B S hS X.1 X.2 T₂ M W s).symm)
  refine ⟨fun hs => ?_, fun hs x hx => Or.inr (hs hx)⟩
  refine sectionSupportedIn_of_restrict_eq_zero_of_imageInOpen B S hS X T₂ hT₂ M W s
    fun U i hi => ?_
  have hrange : Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj U)) U.1.hom) ⊆ T₂ᶜ := by
    rintro y ⟨z, rfl⟩
    have hw : yoneda.map i.hom.left ≫ W.1.hom = U.1.hom := CostructuredArrow.w i.hom
    have hz := hi z
    rw [← hw, pointsMap_comp]
    exact hz
  obtain ⟨g, hg⟩ := hfac ((SmallEtale.toOver B S hS X.1).obj U) U.1.hom hrange
  obtain ⟨U', m, e, he⟩ := exists_factorisation_smallEtalePostcomp B S hS j hj i g hg
  have hsm : SectionSupportedIn B S hS X.1 X.2 (T₁ ∪ T₂) M
      ((smallEtalePostcomp B S hS j hj).obj U') (M.val.map m.op s) :=
    sectionSupportedIn_restrict m s hs
  have hpostrange : Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS X.1).obj
        ((smallEtalePostcomp B S hS j hj).obj U')))
      ((smallEtalePostcomp B S hS j hj).obj U').1.hom) ⊆ T₂ᶜ := by
    rintro y ⟨z, rfl⟩
    exact hVrange ⟨pointsMap B S hS _ U'.1.hom z,
      (congrFun (pointsMap_comp B S hS _ U'.1.hom j.hom) z).symm⟩
  have hsm1 : SectionSupportedIn B S hS X.1 X.2 T₁ M
      ((smallEtalePostcomp B S hS j hj).obj U') (M.val.map m.op s) := by
    intro x hx
    rcases hsm hx with h | h
    · exact h
    · exact absurd h (hpostrange ⟨x, rfl⟩)
  have h0 : M.val.map m.op s = 0 :=
    hV U' _ ((sectionSupportedIn_etaleModulePullback_iff B S hS j hj T₁ M U' _).mpr hsm1)
  have hop : i.op = m.op ≫ e.op := by rw [← he]; rfl
  exact (M.val.congr_map_apply hop s).trans
    ((M.val.map_comp_apply m.op e.op s).trans
      ((congrArg (fun y => M.val.map e.op y) h0).trans (map_zero _)))

/-! ### The quotient by the supported sections after an étale pullback missing the subset -/

/-- **The inclusion of the sections supported on `T` dies under an étale pullback no point of
whose source lies over `T`.**  A section of the submodule over a chart of `V` is a section of
`N` supported on `T` over the composite chart, and no point of that chart lies over `T`, so its
support is empty and it is zero. -/
theorem etaleModulePullback_map_supportedSections_ι_eq_zero
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Vb P₁ : AlgebraicSpaces B S hS} (h : Vb ⟶ P₁) (hh : IsEtale B S hS h.hom)
    (T : Set (points B S hS P₁.1)) (N : Modules.{u, u} B S hS P₁.1 P₁.2)
    (hempty : pointsMap B S hS Vb.1 h.hom ⁻¹' T = ∅) :
    (etaleModulePullback.{u, u} B S hS h hh).map
      (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T N).ι = 0 := by
  ext U x
  have hsupp : supportOfSection B S hS P₁.1 (moduleAddSheaf B S hS P₁.1 P₁.2 N)
      ((smallEtalePostcomp B S hS h hh).obj U.unop) x.1 = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun y hy => ?_
    have hT := (mem_supportedSectionsSubmodule_iff B S hS P₁.1 P₁.2 T N
      ((smallEtalePostcomp B S hS h hh).obj U.unop) x.1).mp x.2 hy
    refine (Set.eq_empty_iff_forall_notMem.1 hempty) (pointsMap B S hS _ U.unop.1.hom y) ?_
    have he : pointsMap B S hS Vb.1 h.hom (pointsMap B S hS _ U.unop.1.hom y) =
        pointsMap B S hS _ ((smallEtalePostcomp B S hS h hh).obj U.unop).1.hom y :=
      (congrFun (pointsMap_comp B S hS _ U.unop.1.hom h.hom) y).symm
    exact Set.mem_preimage.mpr (by rw [he]; exact hT)
  exact eq_zero_of_supportOfSection_eq_empty (F := moduleAddSheaf B S hS P₁.1 P₁.2 N)
    ((smallEtalePostcomp B S hS h hh).obj U.unop) x.1 hsupp

/-- **The projection onto the quotient by the sections supported on `T` becomes an isomorphism
after a pullback no point of whose source lies over `T`.**  Let `j : Vb ⟶ Q` be étale, let
`q : Q ⟶ P₁` be arbitrary with `j ≫ q` étale and with no point of `Vb` lying over `T`, and let
`N` be an `𝒪_{P₁}`-module.  Then the étale restriction to `Vb` of the pullback along `q` of the
projection `N ⟶ N/Γ_T(N)` is an isomorphism.

Along `j ≫ q` the inclusion of the supported sections becomes zero, by
`AlgebraicGeometry.Space.etaleModulePullback_map_supportedSections_ι_eq_zero`, so the étale
pullback of the projection is the cokernel projection of a zero morphism, which is invertible;
the statement is then carried to the composite of the two pullbacks across Stacks 03LW and
`AlgebraicGeometry.Space.modulePullbackCompIso`. -/
theorem isIso_etaleModulePullback_map_modulePullback_map_cokernelProjection
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Vb Q P₁ : AlgebraicSpaces B S hS} (j : Vb ⟶ Q) (hj : IsEtale B S hS j.hom)
    (q : Q ⟶ P₁) (hjq : IsEtale B S hS (j ≫ q).hom)
    (T : Set (points B S hS P₁.1)) (N : Modules.{u, u} B S hS P₁.1 P₁.2)
    (hempty : pointsMap B S hS Vb.1 (j ≫ q).hom ⁻¹' T = ∅) :
    IsIso ((etaleModulePullback B S hS j hj).map
      ((modulePullback B S hS q).map
        (cokernel.π (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T N).ι))) := by
  have hzero := etaleModulePullback_map_supportedSections_ι_eq_zero B S hS (j ≫ q) hjq T N hempty
  have hpres := preservesFiniteColimits_etaleModulePullback B S hS (j ≫ q) hjq
  have hiso1 : IsIso ((etaleModulePullback.{u, u} B S hS (j ≫ q) hjq).map
      (cokernel.π (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T N).ι)) := by
    have hcok : IsIso (cokernel.π ((etaleModulePullback.{u, u} B S hS (j ≫ q) hjq).map
        (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T N).ι)) := cokernel.π_of_zero hzero
    have hcok2 : IsIso ((etaleModulePullback.{u, u} B S hS (j ≫ q) hjq).map
        (cokernel.π (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T N).ι) ≫
      (PreservesCokernel.iso (etaleModulePullback.{u, u} B S hS (j ≫ q) hjq)
        (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T N).ι).hom) := by
      rw [PreservesCokernel.π_iso_hom]
      exact hcok
    exact IsIso.of_isIso_comp_right _
      (PreservesCokernel.iso (etaleModulePullback.{u, u} B S hS (j ≫ q) hjq)
        (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T N).ι).hom
  have hiso2 : IsIso ((modulePullback B S hS (j ≫ q)).map
      (cokernel.π (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T N).ι)) :=
    (NatIso.isIso_map_iff (modulePullbackIsoEtaleModulePullback B S hS (j ≫ q) hjq) _).mpr hiso1
  have hiso3 : IsIso ((modulePullback B S hS q ⋙ modulePullback B S hS j).map
      (cokernel.π (supportedSectionsSubmodule B S hS P₁.1 P₁.2 T N).ι)) :=
    (NatIso.isIso_map_iff (modulePullbackCompIso B S hS j q) _).mpr hiso2
  exact (NatIso.isIso_map_iff (modulePullbackIsoEtaleModulePullback B S hS j hj) _).mp hiso3


/-! ### Sections supported on a union, over charts avoiding the closed part -/

section AvoidingCharts

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- The chart point-map sends the scheme point of `x` to the point of `F` under `x`. -/
private theorem chartPointsMap_pointsToScheme (V : SmallEtale B S hS F)
    (x : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj V))) :
    chartPointsMap V (pointsToScheme B S hS ((SmallEtale.toOver B S hS F).obj V) x) =
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj V)) V.1.hom x :=
  congrArg (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj V)) V.1.hom)
    ((schemePointsHomeomorph B S hS ((SmallEtale.toOver B S hS F).obj V)).symm_apply_apply x)

/-- A point of a chart comes from an open subchart exactly when it lies in the open. -/
private theorem mem_range_pointsMap_openChartInclusion_iff (V : SmallEtale B S hS F)
    (O : (chartScheme V).Opens)
    (x : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj V))) :
    x ∈ Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS F).obj (openChart B S hS F V O)))
      (yoneda.map ((SmallEtale.toOver B S hS F).map (openChartInclusion B S hS F V O)))) ↔
    pointsToScheme B S hS ((SmallEtale.toOver B S hS F).obj V) x ∈ (O : Set (chartScheme V)) := by
  rw [range_pointsMap_yoneda_eq_preimage,
    toScheme_map_toOver_map_openChartInclusion, Set.mem_preimage]
  exact Set.ext_iff.mp (Scheme.Opens.range_ι O) _

/-- **Enlarging the supported set by a set carrying no sections.**  Let `T ⊆ |F|` be closed and
`W ⊆ |F|` arbitrary, and suppose every section of `G` over an étale chart whose points avoid `T`
and which is supported on `W` vanishes.  Then the subsheaf of sections supported on `T ∪ W` is
the subsheaf of sections supported on `T`.

One inclusion holds for any pair of sets.  For the other, a section supported on `T ∪ W` is,
over the open part of its chart lying outside the closed set `T`, supported on `W`, hence zero
by hypothesis; so the support of the section misses that open part and lies in the inverse image
of `T`. -/
theorem supportedSectionsSubmodule_union_eq (T W : Set (points B S hS F)) (hT : IsClosed T)
    (G : Modules.{u, u} B S hS F hF)
    (hW : ∀ V : SmallEtale B S hS F,
      Disjoint (Set.range (pointsMap B S hS
        (yoneda.obj ((SmallEtale.toOver B S hS F).obj V)) V.1.hom)) T →
      ∀ s : G.val.obj (op V), SectionSupportedIn B S hS F hF W G V s → s = 0) :
    supportedSectionsSubmodule B S hS F hF (T ∪ W) G =
      supportedSectionsSubmodule B S hS F hF T G := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun V =>
    Submodule.ext fun s => ?_)
  show SectionSupportedIn B S hS F hF (T ∪ W) G V.unop s ↔
    SectionSupportedIn B S hS F hF T G V.unop s
  refine ⟨fun hs => ?_, fun hs x hx => Or.inl (hs hx)⟩
  -- The open part of the chart lying outside the closed set `T`.
  set O : (chartScheme V.unop).Opens :=
    ⟨(chartPointsMap V.unop ⁻¹' T)ᶜ,
      (hT.preimage (continuous_chartPointsMap V.unop)).isOpen_compl⟩ with hO
  set V₀ := openChart B S hS F V.unop O with hV₀
  set ι₀ := openChartInclusion B S hS F V.unop O with hι₀
  have hO' : ∀ x, pointsToScheme B S hS ((SmallEtale.toOver B S hS F).obj V.unop) x ∈
      (O : Set (chartScheme V.unop)) ↔
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj V.unop)) V.unop.1.hom x ∉ T :=
    fun x => by rw [← chartPointsMap_pointsToScheme V.unop x]; rfl
  have hmap : ∀ y : points B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj V₀)),
      pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj V.unop)) V.unop.1.hom
        (pointsMap B S hS (yoneda.obj ((SmallEtale.toOver B S hS F).obj V₀))
          (yoneda.map ((SmallEtale.toOver B S hS F).map ι₀)) y) ∉ T :=
    fun y => (hO' _).mp ((mem_range_pointsMap_openChartInclusion_iff _ O _).mp ⟨y, rfl⟩)
  -- The chart `V₀` has no point over `T`, so the hypothesis applies to the restriction of `s`.
  have hdisj : Disjoint (Set.range (pointsMap B S hS
      (yoneda.obj ((SmallEtale.toOver B S hS F).obj V₀)) V₀.1.hom)) T :=
    Set.disjoint_left.2 (by
      rintro _ ⟨y, rfl⟩ h
      exact hmap y ((pointsMap_chart_hom B S hS F ι₀ y) ▸ h))
  have hsuppW : SectionSupportedIn B S hS F hF W G V₀ (G.val.map ι₀.op s) := by
    intro y hy
    have hy' := (supportOfSection_restrict B S hS F (moduleAddSheaf B S hS F hF G)
      V.unop s V₀ ι₀).le hy
    rcases hs hy' with h | h
    · exact absurd h (hmap y)
    · rw [Set.mem_preimage]
      exact (pointsMap_chart_hom B S hS F ι₀ y) ▸ h
  have hzero : G.val.map ι₀.op s = 0 := hW V₀ hdisj _ hsuppW
  -- A point of the support outside `T` would be a point of the support of the zero section.
  intro x hx
  by_contra hxT
  obtain ⟨y, hy⟩ := (mem_range_pointsMap_openChartInclusion_iff _ O x).mpr ((hO' x).mpr hxT)
  have hyzero : y ∈ supportOfSection B S hS F (moduleAddSheaf B S hS F hF G) V₀
      (G.val.map ι₀.op s) :=
    (supportOfSection_restrict B S hS F (moduleAddSheaf B S hS F hF G) V.unop s V₀ ι₀).ge
      (by rw [Set.mem_preimage, hy]; exact hx)
  have hyzero0 : y ∈ supportOfSection B S hS F (moduleAddSheaf B S hS F hF G) V₀ 0 :=
    hzero ▸ hyzero
  exact (supportOfSection_zero B S hS F (moduleAddSheaf B S hS F hF G) V₀).le hyzero0

end AvoidingCharts

end AlgebraicGeometry.Space

end
