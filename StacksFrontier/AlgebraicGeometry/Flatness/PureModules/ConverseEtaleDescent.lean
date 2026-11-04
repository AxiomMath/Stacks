module

public import StacksFrontier.AlgebraicGeometry.AffineBaseChangeLocality.GlobalSectionsAffineCase
public import StacksFrontier.AlgebraicGeometry.Flatness.PureModules.ProjectivePushforwardConverseAux
public import StacksFrontier.AlgebraicGeometry.Properties.LocallyProjectivePullback
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Coverings

/-!
# Local projectivity from projective sections on an étale cover

The converse of Tag 05MD produces, at each point of the base, an étale neighbourhood and an
affine open of it on which the sections of the direct image are projective. This file assembles
such a family into local projectivity of the direct image on the base itself, and records the
transport of the direct image along a base change that the assembly needs.

Two mechanisms are used. Tag 05JZ
(`AlgebraicGeometry.isLocallyProjective_of_pullback_fpqc`) descends local projectivity along an
fpqc covering; the family here is étale, hence fpqc by Tag 022C
(`AlgebraicGeometry.Scheme.etalePrecoverage_le_fpqcPrecoverage`), so no quasi-compactness is
owed. And an affine open of an étale neighbourhood is itself étale over the base, its structure
morphism being an open immersion followed by the étale structure morphism, so the affine opens
appearing in the local statement are already members of an étale covering family; their
contribution to the descent is Tag 05JQ in the one-element affine cover
`{⊤}` together with `AlgebraicGeometry.projective_sections_pullback_of_le`.

## Main results

* `AlgebraicGeometry.projective_sections_pullback_opens_ι`: projectivity of the sections on an
  affine open passes to the global sections of the pullback to that open.
* `AlgebraicGeometry.isLocallyProjective_of_forall_exists_etale_affineOpen`: the assembly.
* `AlgebraicGeometry.projective_sections_pullback_pushforward`: Tag 02KG, assertion 3, in the
  form the assembly consumes — projectivity of the sections of a base-changed direct image from
  projectivity of the sections of the direct image along the base change.

## References

* [Stacks Project, Tag 05JZ](https://stacks.math.columbia.edu/tag/05JZ)
* [Stacks Project, Tag 05JQ](https://stacks.math.columbia.edu/tag/05JQ)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- The sections of a pullback on an affine open of the source are the global sections of the
pullback to that open, so projectivity of the former gives projectivity of the latter.

The identification is `AlgebraicGeometry.Scheme.Modules.pullbackComp` for the factorization of
the structure morphism of the open through the open immersion, and the base change of the
sections is `AlgebraicGeometry.projective_sections_pullback_of_le`. -/
theorem projective_sections_pullback_opens_ι {T S : Scheme.{u}} (w : T ⟶ S) (G : S.Modules)
    [G.IsQuasicoherent] {W : T.Opens} (hW : IsAffineOpen W)
    (hproj : Module.Projective Γ(T, W) Γ((Scheme.Modules.pullback w).obj G, W)) :
    Module.Projective Γ(W.toScheme, ⊤)
      Γ((Scheme.Modules.pullback (W.ι ≫ w)).obj G, ⊤) := by
  have : IsAffine W.toScheme := hW
  have hq : ((Scheme.Modules.pullback w).obj G).IsQuasicoherent :=
    isQuasicoherent_pullback_obj w G
  have hle : (⊤ : W.toScheme.Opens) ≤ W.ι ⁻¹ᵁ W := by simp
  exact projective_sections_of_iso_at ((Scheme.Modules.pullbackComp W.ι w).app G) ⊤
    (projective_sections_pullback_of_le W.ι _ hW (isAffineOpen_top _) hle hproj)

/-- **Local projectivity from an étale family of affine opens with projective sections.** A
quasi-coherent module on `S` is locally projective as soon as every point of `S` has an étale
neighbourhood carrying an affine open, whose image contains that point, on which the sections of
the pullback are projective.

The family of affine opens, viewed through its structure morphisms to `S`, is an étale covering
family of `S`, hence fpqc by Tag 022C, and the pullback to each member is locally projective
because the member is affine; Tag 05JZ then descends local projectivity to `S`. -/
theorem isLocallyProjective_of_forall_exists_etale_affineOpen {S : Scheme.{u}} (G : S.Modules)
    [G.IsQuasicoherent]
    (hloc : ∀ s : S, ∃ (T : Scheme.{u}) (w : T ⟶ S) (_ : Etale w) (W : T.Opens),
      IsAffineOpen W ∧ s ∈ w.base '' (W : Set T) ∧
      Module.Projective Γ(T, W) Γ((Scheme.Modules.pullback w).obj G, W)) :
    Scheme.Modules.IsLocallyProjective G := by
  choose T w hw W hWaff hmem hproj using hloc
  refine isLocallyProjective_of_pullback_fpqc G inferInstance (fun s => (W s).toScheme)
    (fun s => (W s).ι ≫ w s) ?_ ?_
  · refine Scheme.etalePrecoverage_le_fpqcPrecoverage _
      ((Scheme.ofArrows_mem_precoverage_iff (P := @Etale)).2 ⟨fun s => ⟨s, ?_⟩, fun s => ?_⟩)
    · obtain ⟨x, hxW, hxs⟩ := hmem s
      exact ⟨⟨x, hxW⟩, hxs⟩
    · have := hw s
      infer_instance
  · intro s
    have : IsAffine (W s).toScheme := hWaff s
    have : ((Scheme.Modules.pullback ((W s).ι ≫ w s)).obj G).IsQuasicoherent :=
      isQuasicoherent_pullback_obj _ G
    refine (isLocallyProjective_iff_exists_affineOpen_cover _).2
      ⟨PUnit, fun _ => ⊤, TopologicalSpace.IsOpenCover.mk (by simp),
        fun _ => isAffineOpen_top _, fun _ => ?_⟩
    exact projective_sections_pullback_opens_ι (w s) G (hWaff s) (hproj s)

/-- **Stacks Tag 02KG, assertion 3**, read on the sections over an affine open of the new base.
For `f : X ⟶ S` affine, `ℱ` quasi-coherent and `q : T ⟶ S` arbitrary, the pullback along `q` of
`f_*ℱ` is the direct image along the base change of `q^*ℱ`, so projectivity of the sections of the
latter on `W ⊆ T` gives projectivity of the sections of the former.

This is the base-change isomorphism
`Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeIso`, transported with
`AlgebraicGeometry.projective_sections_of_iso_at`. -/
theorem projective_sections_pullback_pushforward {X S T : Scheme.{u}} (f : X ⟶ S) [IsAffineHom f]
    (q : T ⟶ S) (F : X.Modules) [F.IsQuasicoherent] (W : T.Opens)
    (hN : Module.Projective Γ(T, W)
      Γ((Scheme.Modules.pushforward (pullback.snd f q)).obj
        ((Scheme.Modules.pullback (pullback.fst f q)).obj F), W)) :
    Module.Projective Γ(T, W)
      Γ((Scheme.Modules.pullback q).obj ((Scheme.Modules.pushforward f).obj F), W) :=
  projective_sections_of_iso_at
    (Stacks.AlgebraicGeometry.AffineBaseChangeLocality.baseChangeIso
      (pullback.fst f q) (pullback.snd f q) f q (IsPullback.of_hasPullback f q)
      inferInstance F inferInstance).symm W hN

end AlgebraicGeometry

end
