module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Pullback
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Restriction
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Modules.AffineSections
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.AffineTilde
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import Mathlib.Algebra.Module.Projective
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A surjection onto a finite locally free module on an affine scheme splits globally

Let `X` be an affine scheme and let `φ : ℱ ⟶ 𝒢` be an epimorphism of `𝒪_X`-modules with `ℱ`
quasi-coherent and `𝒢` finite locally free. Then `φ` admits a *global* section `s : 𝒢 ⟶ ℱ`,
`s ≫ φ = 𝟙 𝒢`; consequently a short exact sequence of `𝒪_X`-modules with finite locally free
third term splits over all of `X`.

This is the step "since `Z` is affine this sequence is split" in the proof of
[Stacks Project, Tag 06D8].

## Main results

* `AlgebraicGeometry.Scheme.Modules.finite_and_projective_moduleSpecΓ_of_isFiniteLocallyFree`:
  the module of global sections of a finite locally free quasi-coherent module on a spectrum is
  a finitely generated projective module.
* `AlgebraicGeometry.Scheme.Modules.exists_section_of_epi_of_isFiniteLocallyFree_spec` and
  `AlgebraicGeometry.Scheme.Modules.exists_section_of_epi_of_isFiniteLocallyFree`: the global
  section, on a spectrum and on an arbitrary affine scheme.
* `AlgebraicGeometry.Scheme.Modules.nonempty_splitting_of_shortExact_of_isFiniteLocallyFree`: a
  short exact sequence of `𝒪_X`-modules on an affine scheme whose third term is finite locally
  free carries a `CategoryTheory.ShortComplex.Splitting`.

## Implementation notes

The whole content is the projectivity of the module of global sections. On a spectrum the
quasi-coherent module `ℱ` is the sheaf associated with `Γ(ℱ, ⊤)`, by invertibility of the counit
`AlgebraicGeometry.Scheme.Modules.fromTildeΓ` of the tilde–sections adjunction; finite local
freeness of the sheaf is finite local freeness of that module, by Tag 05JM in the form
`tilde_isFiniteLocallyFree_iff`; and a finite locally free module is finitely generated
projective, Tag 00NX, in the form `Module.isFiniteLocallyFree_iff_finite_projective`. The
surjection on global sections is `AlgebraicGeometry.epi_moduleSpecΓFunctor_map`, so
`LinearMap.exists_rightInverse_of_surjective` produces a linear section, and the counit carries
the sheafification of that section back to a section of `φ` itself — no comparison of `Hom`
groups is needed, only naturality of the counit.

The passage from a spectrum to an arbitrary affine scheme is along
`AlgebraicGeometry.Scheme.isoSpec`: inverse image along an isomorphism of schemes is an
equivalence of module categories (`AlgebraicGeometry.Scheme.Modules.pullbackEquivOfIso`), it
preserves epimorphisms, quasi-coherence (Tag 01BG) and finite local freeness, so the section
produced on `Spec Γ(X, ⊤)` is the image of a unique morphism on `X`, which is a section of `φ`
by faithfulness.

Only a *local* splitting is available without affineness, and that is
`AlgebraicGeometry.Scheme.Modules.exists_nonempty_splitting_restrict_of_isFiniteLocallyFree` of
`StacksFrontier.AlgebraicGeometry.Modules.LocallySplitShortExact`; this file is the global statement
on an affine scheme, and is not a strengthening of that one by a covering argument — the lift of
a section through the surjection is only local, and what replaces the covering argument here is
the projectivity of the module of global sections.

## References

* [Stacks Project, Tag 06D8](https://stacks.math.columbia.edu/tag/06D8)
* [Stacks Project, Tag 00NX](https://stacks.math.columbia.edu/tag/00NX)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
* [Stacks Project, Tag 01BG](https://stacks.math.columbia.edu/tag/01BG)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Scheme.Modules

/-- **The module of global sections of a finite locally free quasi-coherent module on a spectrum
is finitely generated projective.** The sheaf is the one associated with its module of global
sections, so [Stacks Project, Tag 05JM] turns finite local freeness of the sheaf into finite
local freeness of that module, and [Stacks Project, Tag 00NX] turns the latter into finite
generation together with projectivity. -/
theorem finite_and_projective_moduleSpecΓ_of_isFiniteLocallyFree {R : Type u} [CommRing R]
    (F : (Spec (CommRingCat.of R)).Modules) [F.IsQuasicoherent]
    (hF : Scheme.Modules.IsFiniteLocallyFree F) :
    Module.Finite R (moduleSpecΓFunctor.obj F) ∧
      Module.Projective R (moduleSpecΓFunctor.obj F) := by
  have hfrom : IsIso F.fromTildeΓ :=
    Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent (R := CommRingCat.of R) F
  let e : tilde (R := CommRingCat.of R) (ModuleCat.of R (moduleSpecΓFunctor.obj F)) ≅ F :=
    @asIso _ _ _ _ F.fromTildeΓ hfrom
  have htilde : (tilde (R := CommRingCat.of R)
      (ModuleCat.of R (moduleSpecΓFunctor.obj F))).IsFiniteLocallyFree := by
    intro x
    obtain ⟨U, hx, I, hI, ⟨eU⟩⟩ := hF x
    exact ⟨U, hx, I, hI, ⟨(Scheme.Modules.restrictFunctor (Scheme.Opens.ι U)).mapIso e ≪≫ eU⟩⟩
  exact (Module.isFiniteLocallyFree_iff_finite_projective R
    (moduleSpecΓFunctor.obj F)).mp
    ((tilde_isFiniteLocallyFree_iff R (moduleSpecΓFunctor.obj F)).mp htilde)

/-- **A surjection onto a finite locally free module on a spectrum admits a global section.**
The induced map of modules of global sections is surjective onto a projective module, so it has
a linear right inverse; the counit of the tilde–sections adjunction carries that right inverse
to a section of the original morphism. -/
theorem exists_section_of_epi_of_isFiniteLocallyFree_spec {R : CommRingCat.{u}}
    {M N : (Spec R).Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) [Epi φ] (hN : SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) :
    ∃ s : N ⟶ M, s ≫ φ = 𝟙 N := by
  have hNi : IsIso ((Scheme.Modules.fromTildeΓNatTrans (R := R)).app N) :=
    (Scheme.Modules.isIso_fromTildeΓ_of_isQuasicoherent N :)
  have hproj : Module.Projective R (moduleSpecΓFunctor.obj N) :=
    (finite_and_projective_moduleSpecΓ_of_isFiniteLocallyFree (R := R) N
      ((Scheme.Modules.isFiniteLocallyFree_iff N).mpr hN)).2
  have hprojObj : Projective (moduleSpecΓFunctor.obj N) :=
    (inferInstance : Projective (ModuleCat.of R (moduleSpecΓFunctor.obj N)))
  have hepi : Epi (moduleSpecΓFunctor.map φ) := epi_moduleSpecΓFunctor_map φ
  have hnat : (moduleSpecΓFunctor ⋙ tilde.functor R).map φ ≫
      Scheme.Modules.fromTildeΓNatTrans.app N =
      Scheme.Modules.fromTildeΓNatTrans.app M ≫ φ :=
    Scheme.Modules.fromTildeΓNatTrans.naturality φ
  refine ⟨inv (Scheme.Modules.fromTildeΓNatTrans.app N) ≫ (tilde.functor R).map
    (Projective.factorThru (𝟙 (moduleSpecΓFunctor.obj N)) (moduleSpecΓFunctor.map φ)) ≫
      Scheme.Modules.fromTildeΓNatTrans.app M, ?_⟩
  rw [Category.assoc, Category.assoc, ← hnat, Functor.comp_map, ← Functor.map_comp_assoc,
    Projective.factorThru_comp, CategoryTheory.Functor.map_id, Category.id_comp, IsIso.inv_hom_id]

/-- **A surjection onto a finite locally free module on an affine scheme admits a global
section.** The previous statement, transported along `AlgebraicGeometry.Scheme.isoSpec`: inverse
image along an isomorphism of schemes is an equivalence of module categories, it preserves
epimorphisms and carries quasi-coherence ([Stacks Project, Tag 01BG]) and finite local freeness
to the spectrum, and it is faithful, so a section upstairs descends. -/
theorem exists_section_of_epi_of_isFiniteLocallyFree {X : Scheme.{u}} [IsAffine X]
    {M N : X.Modules} [M.IsQuasicoherent] [N.IsQuasicoherent]
    (φ : M ⟶ N) [Epi φ] (hN : SheafOfModules.IsFiniteLocallyFree.{u, u, u} N) :
    ∃ s : N ⟶ M, s ≫ φ = 𝟙 N := by
  have hpe : (Scheme.Modules.pullback X.isoSpec.inv).PreservesEpimorphisms :=
    Functor.preservesEpimorphisms_of_adjunction
      (Scheme.Modules.pullbackPushforwardAdjunction X.isoSpec.inv)
  have : Epi ((Scheme.Modules.pullback X.isoSpec.inv).map φ) := hpe.preserves φ
  obtain ⟨t, ht⟩ := exists_section_of_epi_of_isFiniteLocallyFree_spec
    ((Scheme.Modules.pullback X.isoSpec.inv).map φ)
    (SheafOfModules.IsFiniteLocallyFree.pullback_scheme X.isoSpec.inv N hN)
  refine ⟨(Scheme.Modules.pullback X.isoSpec.inv).preimage t,
    (Scheme.Modules.pullback X.isoSpec.inv).map_injective ?_⟩
  rwa [Functor.map_comp, Functor.map_preimage, CategoryTheory.Functor.map_id]

/-- **A short exact sequence of modules on an affine scheme whose third term is finite locally
free splits.** The section of the surjection produced by
`AlgebraicGeometry.Scheme.Modules.exists_section_of_epi_of_isFiniteLocallyFree` determines a
retraction of the monomorphism, by
`CategoryTheory.ShortComplex.Splitting.ofExactOfSection`. -/
@[sga "6 I 1.3" "special case"]
theorem nonempty_splitting_of_shortExact_of_isFiniteLocallyFree {X : Scheme.{u}} [IsAffine X]
    (S : ShortComplex X.Modules) (hS : S.ShortExact) [S.X₂.IsQuasicoherent]
    [S.X₃.IsQuasicoherent] (hX₃ : SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃) :
    Nonempty S.Splitting := by
  have := hS.epi_g
  obtain ⟨s, hs⟩ := exists_section_of_epi_of_isFiniteLocallyFree S.g hX₃
  exact ⟨ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hS.mono_f⟩

end AlgebraicGeometry.Scheme.Modules

end
