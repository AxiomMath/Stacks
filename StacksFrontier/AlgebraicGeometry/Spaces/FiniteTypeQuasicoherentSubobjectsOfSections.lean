module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSubmoduleSup
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjectsAffine

/-!
# Quasi-coherent submodules of finite type containing given sections

Two facts about the quasi-coherent submodules of finite type of a quasi-coherent module `ℋ` on
an algebraic space, phrased through sections.

* On an algebraic space `V` isomorphic to a representable presheaf, so that its small étale site
  has a terminal chart, a section of `ℋ` over the terminal chart determines a morphism
  `𝒪_V ⟶ ℋ`, whose image is a quasi-coherent submodule of finite type containing the section.
* If every section of `ℋ` over an affine chart lies in a quasi-coherent submodule of finite type,
  then `ℋ` is the colimit of the canonical diagram of its quasi-coherent submodules of finite
  type: the inclusion of their supremum is locally surjective, the affine charts covering every
  chart, hence an isomorphism.  This is the argument of
  `nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_isAffineSpace`, with its
  hypothesis isolated.

## Main results

The declarations below lie in the namespace `AlgebraicGeometry.Space`.

* `exists_submodule_mem_invIsoChart`: a section over the terminal chart lies in a quasi-coherent
  submodule of finite type.
* `nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_forall_isAffine`: the colimit
  assertion of Stacks 0829 from sections over affine charts.

## References

* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A section over the terminal chart lies in a quasi-coherent submodule of finite type**: the
image of the morphism `𝒪_V ⟶ ℋ` it determines, on an algebraic space `V` isomorphic to a
representable presheaf. -/
theorem exists_submodule_mem_invIsoChart {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hV : IsAlgebraicSpace B S hS V) {T₀ : BigFppfOver B S hS} (e : V ≅ yoneda.obj T₀)
    (H : Modules.{u, u} B S hS V hV) [H.IsQuasicoherentOnSite]
    (n : H.val.obj (op (invIsoChart B S hS e))) :
    ∃ N : H.Submodule, N.toSheafOfModules.IsQuasicoherentOnSite ∧
      N.toSheafOfModules.IsFiniteType ∧ n ∈ N.obj (op (invIsoChart B S hS e)) := by
  let v := isoChartSectionHom B S hS hV e H n
  have hI := imageSubobject_unit_mem B S hS hV H v
  obtain ⟨hNq, hNf⟩ := isQuasicoherentOnSite_isFiniteType_monoRangeSubmodule_of_mono B S hS
    (X := ⟨V, hV⟩) (imageSubobject v).arrow hI.1 hI.2
  refine ⟨ImageSubsheaf.monoRangeSubmodule (imageSubobject v).arrow, hNq, hNf,
    (factorThruImageSubobject v).val.app (op (invIsoChart B S hS e))
      (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V hV).O).obj.obj
        (op (invIsoChart B S hS e))), ?_⟩
  have h₁ := isoChartSectionHom_app_one B S hS hV e H n (invIsoChart B S hS e)
  have h₂ : toIsoChart B S hS e (invIsoChart B S hS e) = 𝟙 _ := toIsoChart_unique B S hS e _ _
  rw [h₂] at h₁
  have h₃ : (factorThruImageSubobject v ≫ (imageSubobject v).arrow) = v :=
    imageSubobject_arrow_comp v
  refine Eq.trans ?_ (h₁.trans (moduleMap_id_apply' B S hS (X := ⟨V, hV⟩) H _ n))
  exact congrArg (fun φ => φ.val.app (op (invIsoChart B S hS e))
    (1 : (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS V hV).O).obj.obj
      (op (invIsoChart B S hS e)))) h₃

/-- **The colimit assertion of Stacks 0829 from affine charts.**  A quasi-coherent module every
section of which over an affine chart lies in a quasi-coherent submodule of finite type is the
colimit of the canonical diagram of its quasi-coherent submodules of finite type. -/
theorem nonempty_isColimit_finiteTypeQuasicoherentSubobjectCocone_of_forall_isAffine
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (H : Modules.{u, u} B S hS X hX) [hH : H.IsQuasicoherentOnSite]
    (h : ∀ (W : SmallEtale B S hS X),
      IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj W) →
      ∀ s : H.val.obj (op W), ∃ K : H.Submodule, K.toSheafOfModules.IsQuasicoherentOnSite ∧
        K.toSheafOfModules.IsFiniteType ∧ s ∈ K.obj (op W)) :
    Nonempty (IsColimit (finiteTypeQuasicoherentSubobjectCocone B S hS X hX H)) := by
  classical
  let habX : Abelian (Modules.{u, u} B S hS X hX) :=
    SheafOfModules.instAbelian.{u, u, u, u + 1}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS X hX).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS X)
    infer_instance
  have hgr : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS X hX) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  have hfiltered : IsFiltered (FiniteTypeQuasicoherentSubobject B S hS X hX H) :=
    isFiltered_finiteTypeQuasicoherentSubobject B S hS X hX H
  let T : Subobject H := ⨆ G : FiniteTypeQuasicoherentSubobject B S hS X hX H, G.obj
  -- every section over an affine chart lies in the supremum
  have hgen : ∀ (W : SmallEtale B S hS X),
      IsAffine ((SmallEtale.toOver B S hS X ⋙ BigFppfOver.toScheme B S hS).obj W) →
      ∀ s : H.val.obj (op W), s ∈ LinearMap.range (T.arrow.val.app (op W)).hom := by
    intro W hW s
    obtain ⟨K, hKq, hKf, hs⟩ := h W hW s
    have : Epi (Subobject.underlyingIso K.ι).inv :=
      @IsIso.epi_of_iso _ _ _ _ _ (Iso.isIso_inv (Subobject.underlyingIso K.ι))
    let GK : FiniteTypeQuasicoherentSubobject B S hS X hX H :=
      ⟨Subobject.mk K.ι, SheafOfModules.IsQuasicoherentOnSite.of_iso
        (Subobject.underlyingIso K.ι).symm hKq,
        Stacks.SheafOfModules.isFiniteType_of_epi
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X hX).O))
          (Subobject.underlyingIso K.ι).inv hKf⟩
    have hle : Subobject.mk K.ι ≤ T :=
      le_iSup (fun G : FiniteTypeQuasicoherentSubobject B S hS X hX H => G.obj) GK
    refine ⟨(Subobject.ofMkLE K.ι T hle).val.app (op W) ⟨s, hs⟩, ?_⟩
    exact congrArg (fun φ => φ.val.app (op W) ⟨s, hs⟩) (Subobject.ofMkLE_arrow hle)
  have hepi : Epi T.arrow := by
    refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective T.arrow ⟨fun {W} s => ?_⟩
    refine (SmallEtale.topology B S hS X).superset_covering ?_
      (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS X W)
    intro W' g hg
    obtain ⟨O, a, rfl⟩ := (Sieve.mem_ofArrows_iff _ _ _).1 hg
    refine (Presheaf.imageSieve _ s).downward_closed ?_ a
    obtain ⟨t, ht⟩ := hgen _ (isAffine_chartScheme_openChart B S hS X W O.down)
      (H.val.map (openChartInclusion B S hS X W O.down.1).op s)
    exact ⟨t, ht⟩
  have : IsIso T.arrow := isIso_of_mono_of_epi T.arrow
  have htop : T = ⊤ := by
    simpa only [T, Subobject.mk_arrow] using Subobject.mk_eq_top_of_isIso T.arrow
  exact ⟨isColimitSubobjectCocone_of_iSup_eq_top
    (finiteTypeQuasicoherentSubobjectProperty B S hS X hX H) htop⟩

end AlgebraicGeometry.Space

end
