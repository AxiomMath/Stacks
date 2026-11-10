module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CoherentColimitPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentCompactQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentFlatPresentationEquivalence

/-!
# Coherent approximation on an algebraic stack through a flat presentation

Let `𝒳` be a locally Noetherian algebraic stack and `f : U → 𝒳` a surjective, flat morphism,
locally of finite presentation, from an algebraic space, with groupoid `(U, R, s, t, c)`
(`AlgebraicGeometry.Stack.SelfIntersection.flatPresentationGroupoid`).  Stacks 0GRC identifies
`QCoh(𝒪_𝒳)` with `QCoh(U, R, s, t, c)` and `Coh(𝒪_𝒳)` with `Coh(U, R, s, t, c)`.  When moreover
`U`, `R` are Noetherian and `s`, `t` are flat, quasi-compact and quasi-separated, Stacks 0GPS
writes every object of `QCoh(U, R, s, t, c)` as a filtered colimit of coherent submodules.  This
file transports that statement to `𝒳` along the equivalence: this is the reduction step of the
proof of Stacks 0GRF.

## Main results

* `Stack.SelfIntersection.exists_colimitPresentation_mono_coherent_of_flatPresentation`:
  every quasi-coherent `𝒪_𝒳`-module has a colimit presentation indexed by a small filtered
  category, by monomorphisms out of coherent `𝒪_𝒳`-modules.
* `AlgebraicGeometry.Stack.SelfIntersection.ind_coherentQuasicoherent_of_flatPresentation`: the
  same, in the form `ObjectProperty.ind.{u}` of `AlgebraicGeometry.Stack.coherentQuasicoherent`.

## References

* [Stacks Project, Tag 0GRF](https://stacks.math.columbia.edu/tag/0GRF)
* [Stacks Project, Tag 0GRC](https://stacks.math.columbia.edu/tag/0GRC)
* [Stacks Project, Tag 0GPS](https://stacks.math.columbia.edu/tag/0GPS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u t

namespace AlgebraicGeometry.Stack.SelfIntersection

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : AlgebraicStacks.{u, t} B S hS)
  (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
  (f : algebraicSpaceStack.{u, t} B S hS F hF ⟶ 𝒳)

/-- The coherent modules on the groupoid `(U, R, s, t, c)` are closed under isomorphisms. -/
instance isClosedUnderIsomorphisms_coherentModules {A : AlgebraicSpaces B S hS}
    (G : GroupoidInAlgebraicSpaces B S hS A) :
    (Space.QuasicoherentModule.coherentModules B S hS G).IsClosedUnderIsomorphisms where
  of_iso e h :=
    Space.isCoherent_of_iso B S hS G.objects.2 ((Space.QuasicoherentModule.forget G).mapIso e) h

/-- **A coherent module on the groupoid of a flat presentation comes from a coherent
`𝒪_𝒳`-module** (the "vice versa" of Stacks 0GRC): the inverse of the equivalence
`QCoh(𝒪_𝒳) ≌ QCoh(U, R, s, t, c)` sends `Coh(U, R, s, t, c)` into `Coh(𝒪_𝒳)`. -/
theorem coherentQuasicoherent_inverse_obj
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hsurj : IsSurjective B S hS f)
    (N : Space.QuasicoherentModule B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f))
    (hN : Space.QuasicoherentModule.coherentModules B S hS _ N) :
    coherentQuasicoherent B S hS 𝒳
      ((quasicoherentFlatPresentationEquivalence B S hS 𝒳 F hF f hlfp hflat hsurj).inverse.obj
        N) := by
  let E := quasicoherentFlatPresentationEquivalence B S hS 𝒳 F hF f hlfp hflat hsurj
  change quasicoherentCoherentModules B S hS 𝒳 (E.inverse.obj N)
  rw [← inverseImage_coherentModules_eq_quasicoherentCoherentModules B S hS 𝒳
    (flatPresentationGroupoid B S hS 𝒳 F hF f) h𝒳 f hlfp hflat hsurj E
    (fun ℱ => Classical.choice
      (nonempty_quasicoherentFlatPresentationEquivalence_functor_obj_iso B S hS 𝒳 F hF f hlfp
        hflat hsurj ℱ))]
  exact (Space.QuasicoherentModule.coherentModules B S hS _).prop_of_iso
    (E.counitIso.app N).symm hN

/-- **Every quasi-coherent `𝒪_𝒳`-module is a small filtered colimit of coherent submodules, given
a flat presentation with Noetherian groupoid** (the reduction step of Stacks 0GRF).  Let `𝒳` be
locally Noetherian and `f : U → 𝒳` surjective, flat and locally of finite presentation from an
algebraic space, whose groupoid `(U, R, s, t, c)` has `U`, `R` Noetherian and `s`, `t` flat,
quasi-compact and quasi-separated.  Then every quasi-coherent `𝒪_𝒳`-module `M` has a colimit
presentation indexed by a small filtered category whose colimit maps are monomorphisms and whose
terms are coherent: the image under Stacks 0GRC of the presentation of Stacks 0GPS. -/
theorem exists_colimitPresentation_mono_coherent_of_flatPresentation
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hsurj : IsSurjective B S hS f)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (objects_noetherian :
      Space.IsNoetherian B S hS hZ (flatPresentationGroupoid B S hS 𝒳 F hF f).objects.1)
    (arrows_noetherian :
      Space.IsNoetherian B S hS hZ (flatPresentationGroupoid B S hS 𝒳 F hF f).arrows.1)
    (source_flat : Space.IsFlat B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom)
    (source_quasiCompact :
      Space.IsQuasiCompact B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom)
    (source_quasiSeparated :
      Space.IsQuasiSeparated B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom)
    (target_flat : Space.IsFlat B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).target.hom)
    (M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    ∃ (I : Type u) (_ : SmallCategory I) (_ : IsFiltered I) (pres : ColimitPresentation I M),
      (∀ i, Mono (pres.ι.app i)) ∧ ∀ i, coherentQuasicoherent B S hS 𝒳 (pres.diag.obj i) := by
  let E := quasicoherentFlatPresentationEquivalence B S hS 𝒳 F hF f hlfp hflat hsurj
  obtain ⟨I, _, _, pres, hmono, hcoh⟩ :=
    Space.QuasicoherentModule.exists_colimitPresentation_mono_isCoherent hZ objects_noetherian
      arrows_noetherian source_flat source_quasiCompact source_quasiSeparated target_flat
      (E.functor.obj M)
  refine ⟨I, inferInstance, inferInstance, (pres.map E.inverse).ofIso (E.unitIso.app M).symm,
    fun i => ?_, fun i => ?_⟩
  · have := hmono i
    change Mono ((E.inverse.map (pres.ι.app i) ≫
      (E.inverse.constComp I (E.functor.obj M)).hom.app i) ≫ (E.unitIso.app M).symm.hom)
    infer_instance
  · exact coherentQuasicoherent_inverse_obj B S hS 𝒳 F hF f h𝒳 hlfp hflat hsurj _ (hcoh i)

/-- **Every quasi-coherent `𝒪_𝒳`-module is a small filtered colimit of coherent modules, given a
flat presentation with Noetherian groupoid**, in the form `ObjectProperty.ind.{u}` of
`AlgebraicGeometry.Stack.coherentQuasicoherent`. -/
theorem ind_coherentQuasicoherent_of_flatPresentation
    (h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (hlfp : AlgebraicStacks.IsLocallyOfFinitePresentation B S hS f)
    (hflat : AlgebraicStacks.IsFlat B S hS f) (hsurj : IsSurjective B S hS f)
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (objects_noetherian :
      Space.IsNoetherian B S hS hZ (flatPresentationGroupoid B S hS 𝒳 F hF f).objects.1)
    (arrows_noetherian :
      Space.IsNoetherian B S hS hZ (flatPresentationGroupoid B S hS 𝒳 F hF f).arrows.1)
    (source_flat : Space.IsFlat B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom)
    (source_quasiCompact :
      Space.IsQuasiCompact B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom)
    (source_quasiSeparated :
      Space.IsQuasiSeparated B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).source.hom)
    (target_flat : Space.IsFlat B S hS (flatPresentationGroupoid B S hS 𝒳 F hF f).target.hom)
    (M : FibredSite.quasicoherentModules.{u, u + 1, u, u} B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids) :
    (coherentQuasicoherent B S hS 𝒳).ind.{u} M := by
  obtain ⟨I, _, _, pres, -, hcoh⟩ := exists_colimitPresentation_mono_coherent_of_flatPresentation
    B S hS 𝒳 F hF f h𝒳 hlfp hflat hsurj hZ objects_noetherian arrows_noetherian source_flat
    source_quasiCompact source_quasiSeparated target_flat M
  exact ⟨I, inferInstance, inferInstance, pres, hcoh⟩

end AlgebraicGeometry.Stack.SelfIntersection

end
