module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.ChangeOfBaseScheme
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedAtlas

/-!
# Absolute quasi-separatedness from an étale atlas

An algebraic space over a scheme `S` is quasi-separated over the terminal scheme as soon as it
admits a surjective étale morphism from an object of the site whose underlying scheme is
quasi-separated and one of whose kernel-pair projections is quasi-compact.

## Main results

* `AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection`:
  an algebraic space with an étale atlas whose source is a quasi-separated scheme and whose
  second kernel-pair projection is quasi-compact is absolutely quasi-separated.
* `AlgebraicGeometry.Space.isQuasiSeparated_of_etaleAtlas_quasiCompact_projection`: the same
  criterion with the atlas data given as a single existential, the condition on the source
  given as quasi-separatedness of its underlying space, and either projection of the kernel
  pair allowed to be the quasi-compact one.

## References

* [Stacks Project, Tag 07S4](https://stacks.math.columbia.edu/tag/07S4)
* [Stacks Project, Tag 03I4](https://stacks.math.columbia.edu/tag/03I4)
* [Stacks Project, Tag 03BS](https://stacks.math.columbia.edu/tag/03BS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.OverShriek

universe u

namespace AlgebraicGeometry.Space

/-- A scheme is a quasi-separated space iff its map to the terminal scheme is quasi-separated. -/
private theorem quasiSeparatedSpace_iff_quasiSeparated_of_hom_terminal {X : Scheme.{u}}
    (f : X ⟶ ⊤_ Scheme.{u}) : QuasiSeparatedSpace X ↔ QuasiSeparated f := by
  rw [quasiSeparatedSpace_iff_quasiSeparated, terminal.hom_ext (terminal.from X) f]

/-- **Absolute quasi-separatedness from an étale atlas.** An algebraic space over `S` which
admits a surjective étale morphism from an object of the site whose underlying scheme is
quasi-separated, and whose kernel pair is represented with quasi-compact second projection,
is quasi-separated over the terminal scheme. -/
theorem isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F)
    {U : BigFppfOver B S hS} {q : yoneda.obj U ⟶ F}
    (hq_surj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q)
    (hq_etale : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) q)
    (hU : QuasiSeparated (B.inclusion.map U.hom ≫ terminal.from S))
    {R : BigFppfOver B S hS} {r₁ r₂ : R ⟶ U}
    (hR : IsPullback (yoneda.map r₁) (yoneda.map r₂) q q)
    (hr : QuasiCompact ((BigFppfOver.toScheme B S hS).map r₂)) :
    IsAbsolutelyQuasiSeparated B S hS hZ F := by
  set g : B.obj hS ⟶ B.obj hZ := ⟨terminal.from S⟩ with hg
  have halg := isAlgebraicSpace_relocalize B (B.obj hS) (B.obj hZ) g F hF
  have hpb := isPullback_relocalize_atlas B (B.obj hS) (B.obj hZ) g (q := q) (r₁ := r₁)
    (r₂ := r₂) hR
  have key (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
      (hq : (MorphismProperty.presheaf (MorphismProperty.inverseImage P
        (BigFppfOver.toScheme B S hS))) q) :=
    MorphismProperty.RespectsIso.precomp _ ((relocalizeYonedaIso g).app U).inv _
      (@presheaf_map_relocalize _ _ _ _ g
        (MorphismProperty.inverseImage P (BigFppfOver.toScheme B S hS))
        (MorphismProperty.inverseImage P (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))
        (MorphismProperty.RespectsIso.inverseImage _ _) (fun _ hk => hk) _ _ _ hq)
  have _ : MorphismProperty.RespectsIso (@Surjective.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have _ : MorphismProperty.RespectsIso (@Etale.{u} : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have hUqs : QuasiSeparatedSpace ((BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ).obj
      ((Over.map g).obj U)) :=
    (quasiSeparatedSpace_iff_quasiSeparated_of_hom_terminal _).2 hU
  have _ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B (⊤_ Scheme.{u}) hZ))).RespectsIso :=
    (MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _).respectsIso
  have hr' := presheaf_yoneda_map_of_inverseImage B (⊤_ Scheme.{u}) hZ
    (P := @QuasiCompact.{u}) inferInstance ((Over.map g).map r₂) hr
  refine isQuasiSeparatedOver_of_etaleAtlas_quasiCompact_projection B (⊤_ Scheme.{u}) hZ _ halg
    ⟨(Over.map g).obj U, _, hUqs, key _ hq_surj, key _ hq_etale, Or.inr ?_⟩
  refine (MorphismProperty.cancel_left_of_respectsIso _ hpb.isoPullback.hom _).1 ?_
  rw [hpb.isoPullback_hom_snd]
  exact hr'

/-- An algebraic space over `S` which admits a surjective étale morphism `q` from an object of
the site whose underlying scheme is quasi-separated, and one of whose two kernel-pair
projections `pullback.fst q q`, `pullback.snd q q` is quasi-compact, is quasi-separated over the
terminal scheme. -/
@[stacks 07S4]
theorem isQuasiSeparated_of_etaleAtlas_quasiCompact_projection
    (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS X)
    (hAtlas : ∃ (U : BigFppfOver B S hS)
        (q : yoneda.obj U ⟶ X),
      QuasiSeparatedSpace ((BigFppfOver.toScheme B S hS).obj U) ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) q ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) q ∧
      ((MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (pullback.fst q q) ∨
       (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) (pullback.snd q q))) :
    IsAbsolutelyQuasiSeparated B S hS hZ X := by
  obtain ⟨U, q, hUqs, hq_surj, hq_etale, hdisj⟩ := hAtlas
  have hU : QuasiSeparated (B.inclusion.map U.hom ≫ terminal.from S) :=
    (quasiSeparatedSpace_iff_quasiSeparated_of_hom_terminal _).1 hUqs
  obtain ⟨R, r₁, r₂, hR⟩ : ∃ (R : BigFppfOver B S hS) (r₁ r₂ : R ⟶ U),
      IsPullback (yoneda.map r₁) (yoneda.map r₂) q q :=
    ⟨_, _, _, hq_surj.rep.isPullback' q⟩
  have key {f : pullback q q ⟶ yoneda.obj U} {g : R ⟶ U}
      (hf : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) f)
      (hfg : hR.isoPullback.hom ≫ f = yoneda.map g) :
      QuasiCompact ((BigFppfOver.toScheme B S hS).map g) := by
    have h := MorphismProperty.RespectsIso.precomp _ hR.isoPullback.hom _ hf
    rw [hfg] at h
    have h' := MorphismProperty.of_relative_map (F := yoneda) h
    exact h'
  rcases hdisj with hfst | hsnd
  · exact isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection B S hS hZ hX
      hq_surj hq_etale hU hR.flip (key hfst hR.isoPullback_hom_fst)
  · exact isAbsolutelyQuasiSeparated_of_etaleAtlas_quasiCompact_projection B S hS hZ hX
      hq_surj hq_etale hU hR (key hsnd hR.isoPullback_hom_snd)

end AlgebraicGeometry.Space

end
