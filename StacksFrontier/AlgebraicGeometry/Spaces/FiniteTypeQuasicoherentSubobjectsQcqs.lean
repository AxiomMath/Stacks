module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsDirected

/-!
# A quasi-coherent module on a qcqs algebraic space is the colimit of its finite type submodules

Let `X` be a quasi-compact and quasi-separated algebraic space over a scheme `S` and let `F` be a
quasi-coherent `𝒪_X`-module.  This file proves **the colimit assertion of Stacks 0829**: `F` is
the colimit of the canonical diagram of its finite type quasi-coherent submodules, with no
hypothesis beyond the source's.

## The proof

The source deduces the assertion from Stacks 07V9, which rests on absolute Noetherian
approximation, Stacks 07SU.  As the remark preceding Stacks 07V9 notes, the assertion can be
deduced from Decent Spaces, Lemma 07ST instead, and that is the route taken here: the
induction principle of Stacks 08GP, built on 07ST, propagates the étale extension property
`AlgebraicGeometry.Space.ChartExtensionProperty` — every section over an affine chart lies in a
finite type quasi-coherent submodule — from the affine algebraic spaces étale over `X` to `X`
itself (`AlgebraicGeometry.Space.chartExtensionProperty_id`).  Since directedness is already
known (`AlgebraicGeometry.Space.isFiltered_finiteTypeQuasicoherentSubobject`), the colimit
assertion reduces to the statement that the finite type quasi-coherent submodules of `F` have
supremum `⊤` (`AlgebraicGeometry.Space.isColimitSubobjectCocone_of_iSup_eq_top`), and the
inclusion of that supremum is locally surjective because every section over an affine chart
lies in one of them.

## Main results

* `AlgebraicGeometry.Space.ChartSubmodule.finiteTypeQuasicoherentSubobjectProperty_mk`: the
  submodule of `F` given by a chart submodule over the identity of `X` is a finite type
  quasi-coherent subobject of `F`.
* `AlgebraicGeometry.Space.nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_qcqs`:
  **the colimit assertion of Stacks 0829.**

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 07V9](https://stacks.math.columbia.edu/tag/07V9)
* [Stacks Project, Tag 07ST](https://stacks.math.columbia.edu/tag/07ST)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/- The global instance `Abelian (SheafOfModules.{max u v r w} O)` of the cohomology of modules
leaves a stuck universe constraint against `Modules.{u, u}`; the abelian structure used here is the
one at the pinned universes. -/
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}
    {F : Modules.{u, u} B S hS X hX}

set_option synthInstance.maxHeartbeats 400000 in
/-- The submodule of `F` given by a chart submodule over the identity of `X` is a finite type
quasi-coherent subobject of `F`: it is cartesian on affine charts, hence quasi-coherent by
Stacks 03DX(2), and finitely generated over affine charts, hence of finite type. -/
theorem ChartSubmodule.finiteTypeQuasicoherentSubobjectProperty_mk
    (hF : IsCartesianOnAffineCharts F) (D : ChartSubmodule F (𝟙 X)) :
    finiteTypeQuasicoherentSubobjectProperty B S hS X hX F (Subobject.mk (D.toSubmodule F).ι) := by
  have hqc : (D.toSubmodule F).toSheafOfModules.IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS X hX _).2
      (D.isCartesianOnAffineCharts_toSubmodule hF)
  have hft : (D.toSubmodule F).toSheafOfModules.IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite _
      (D.isFiniteTypeOnSite_toSubmodule hF)
  let e := Subobject.underlyingIso (D.toSubmodule F).ι
  have h1 : SheafOfModules.IsQuasicoherentOnSite
      ((Subobject.mk (D.toSubmodule F).ι : Modules.{u, u} B S hS X hX)) :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso e.symm hqc
  have he : Epi e.inv := @IsIso.epi_of_iso _ _ _ _ e.inv (Iso.isIso_inv e)
  have h2 : SheafOfModules.IsFiniteType
      ((Subobject.mk (D.toSubmodule F).ι : Modules.{u, u} B S hS X hX)) :=
    Stacks.SheafOfModules.SliceFinite.isFiniteType_of_epi
      (Rs := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))
      e.inv hft
  exact ⟨h1, h2⟩

set_option synthInstance.maxHeartbeats 400000 in
/-- **Stacks 0829, the colimit assertion.**  Let `X` be a quasi-compact and quasi-separated
algebraic space over a scheme `S` and let `F` be a quasi-coherent `𝒪_X`-module.  Then `F` is the
colimit of the canonical diagram of its finite type quasi-coherent submodules.

The diagram is directed by `AlgebraicGeometry.Space.isFiltered_finiteTypeQuasicoherentSubobject`,
which together with this declaration covers the whole of Stacks 0829. -/
@[stacks 0829 "the colimit clause"]
theorem nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_qcqs
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u})) (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X) (hqc : IsQuasiCompactSpace B S hS X)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X)
    (F : Modules.{u, u} B S hS X hX) [F.IsQuasicoherentOnSite] :
    Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS X hX F)) := by
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X hX).C := by
    show EssentiallySmall.{u} (SmallEtale B S hS X)
    infer_instance
  have _ : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X hX) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have _ : IsFiltered (FiniteTypeQuasicoherentSubobject B S hS X hX F) :=
    isFiltered_finiteTypeQuasicoherentSubobject B S hS X hX F
  -- the finite type quasi-coherent submodules have supremum `⊤`
  have htop : (⨆ G : FiniteTypeQuasicoherentSubobject B S hS X hX F, G.obj) = ⊤ := by
    classical
    have hF := isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS X hX F ‹_›
    have hP := chartExtensionProperty_id (hX := hX) hZ hqc hqs hF
    set T := ⨆ G : FiniteTypeQuasicoherentSubobject B S hS X hX F, G.obj with hT
    have hle : ∀ D : ChartSubmodule F (𝟙 X), Subobject.mk (D.toSubmodule F).ι ≤ T := fun D =>
      le_iSup_of_le (⟨Subobject.mk (D.toSubmodule F).ι,
        D.finiteTypeQuasicoherentSubobjectProperty_mk hF⟩ :
          FiniteTypeQuasicoherentSubobject B S hS X hX F) le_rfl
    have hfac : ∀ D : ChartSubmodule F (𝟙 X),
        ((Subobject.underlyingIso (D.toSubmodule F).ι).inv ≫ Subobject.ofLE _ T (hle D)) ≫
          T.arrow = (D.toSubmodule F).ι := by
      intro D
      rw [Category.assoc, Subobject.ofLE_arrow, Subobject.underlyingIso_arrow]
    have hepi : Epi T.arrow := by
      refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {Z} x => ?_⟩
      refine (SmallEtale.topology B S hS X).superset_covering ?_
        (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS X Z)
      intro Y g hg
      obtain ⟨O, e, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ g).1 hg
      refine Sieve.downward_closed _ ?_ e
      obtain ⟨D, hD⟩ := hP (openChart B S hS X Z O.down.1) _ (Category.comp_id _)
        (isAffine_chartScheme_openChart B S hS X Z O.down)
        (chartRes F (openChartInclusion B S hS X Z O.down.1) x)
      let k : (D.toSubmodule F).toSheafOfModules.val.obj (op (openChart B S hS X Z O.down.1)) :=
        (⟨_, hD⟩ : (D.toSubmodule F).obj (op (openChart B S hS X Z O.down.1)))
      refine ⟨(((Subobject.underlyingIso (D.toSubmodule F).ι).inv ≫
        Subobject.ofLE _ T (hle D)).val.app (op (openChart B S hS X Z O.down.1))) k, ?_⟩
      exact congrArg (fun φ => φ.val.app (op (openChart B S hS X Z O.down.1)) k) (hfac D)
    have : IsIso T.arrow := isIso_of_mono_of_epi _
    exact Subobject.eq_top_of_isIso_arrow T
  exact ⟨isColimitSubobjectCocone_of_iSup_eq_top
    (finiteTypeQuasicoherentSubobjectProperty B S hS X hX F) htop⟩

end AlgebraicGeometry.Space

end
