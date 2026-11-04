module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraEquivalenceReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackQuasicoherentFromChartDiagrams
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentSheavesProperties
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsExactness

/-!
# The quasi-inverse of Stacks 08AI preserves quasi-coherence, given one change-of-rings fact

Let `f : Y ⟶ X` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, let `𝒜 = f_*𝒪_Y`, and let `L : 𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢` be the left adjoint of the
direct image over `𝒜`.  The hypothesis `hL` of
`AlgebraicGeometry.Space.isEquivalence_quasicoherentDirectImage` is that `L` carries
quasi-coherent `𝒜`-modules to quasi-coherent `𝒪_Y`-modules.  This file reduces it to a single
statement about **extension of scalars along `f♯ : 𝒪_X ⟶ 𝒜` alone**, with no comparison of `L`
with restriction to a slice and no colimit preservation by `f_*`:

> extension of scalars along `f♯`, read back as a functor to `𝒪_X`-modules, carries
> quasi-coherent `𝒪_X`-modules to quasi-coherent `𝒪_X`-modules.

That statement is `AlgebraicGeometry.Space.ExtendScalarsPreservesQuasicoherence`.  It is
clause (5) of Stacks 03M1 —
`AlgebraicGeometry.Space.isQuasicoherentOnSite_tensorModule_schemeUniverse`, the tensor product of
two quasi-coherent `𝒪_X`-modules is quasi-coherent — once `𝒢 ↦ 𝒜 ⊗_{𝒪_X} 𝒢` is identified
with extension followed by restriction of scalars, `𝒜` being quasi-coherent as an `𝒪_X`-module
for an affine `f` by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_restrictScalars_structureRingSheafDirectImage`.
For an affine morphism it is proved as
`AlgebraicGeometry.Space.extendScalarsPreservesQuasicoherence`, and `hL` with it as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback`.

This is the argument that the scheme-level case of the tag, Stacks 01SB, uses for its own `hL`:
`Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_pullbackModules`.  It is global
on `X` — nothing below is local on either site.

## Main definitions

* `AlgebraicGeometry.Space.directImageAlgebraExtendScalars` and
  `AlgebraicGeometry.Space.directImageAlgebraRestrictScalars` — extension and restriction of
  scalars along the structure map `f♯ : 𝒪_X ⟶ 𝒜` of Stacks 03G8, and
  `AlgebraicGeometry.Space.directImageAlgebraExtendRestrictAdjunction` the adjunction between
  them, which is Stacks 03CZ.
* `AlgebraicGeometry.Space.ExtendScalarsPreservesQuasicoherence` — the one statement this
  reduction takes.

## Main results

* `AlgebraicGeometry.Space.directImageAlgebraPullbackExtendScalarsIso` — **the quasi-inverse of
  Stacks 08AI precomposed with extension of scalars along `f♯` is the pullback of `𝒪_X`-modules
  of Stacks 03LU**: both are left adjoint to `AlgebraicGeometry.Space.modulePushforward`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback_extendScalars` —
  consequently `L` carries the extension of scalars of a quasi-coherent `𝒪_X`-module to a
  quasi-coherent `𝒪_Y`-module.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback_of_extendScalars` —
  **`hL` from `ExtendScalarsPreservesQuasicoherence`**, for an affine morphism.
* `AlgebraicGeometry.Space.affineDirectImageEquivalence_of_extendScalars_of_isIso_unit_counit` —
  `AlgebraicGeometry.Space.AffineDirectImageEquivalence` with `hL` replaced by
  `ExtendScalarsPreservesQuasicoherence`, so that the first assertion of Stacks 08AI rests on
  that statement together with the invertibility of the unit and the counit.

## The argument

Write `E` for extension of scalars along `f♯`, `Rs` for restriction of scalars along it, and `L`
for the quasi-inverse.  Two things carry the proof.

* `L ∘ E` is the pullback of modules `f^*` of Stacks 03LU.  Both are left adjoints of
  `AlgebraicGeometry.Space.modulePushforward`: the right adjoint of `E ⋙ L` is
  `AlgebraicGeometry.Space.moduleDirectImage` followed by `Rs`, which is `f_*` read over `𝒪_X`
  on the nose by `AlgebraicGeometry.Space.restrictScalars_moduleDirectImage`, and `f^*` is left
  adjoint to the same functor by `AlgebraicGeometry.Space.modulePullbackAdjunction`.  So `L`
  carries `E 𝒢` to a quasi-coherent module whenever `𝒢` is quasi-coherent, by
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite`.
* Every `𝒜`-module `G` is a cokernel of a morphism between two modules of that form.  The
  counit `E (Rs G) ⟶ G` is a split epimorphism after restriction of scalars, by the triangle
  identity, hence an epimorphism because restriction of scalars reflects them
  (`Stacks.AlgebraicGeometry.QcohOverAlgebra.reflectsEpimorphisms_restrictScalars`); `G` is
  therefore the cokernel of the kernel `K` of that counit, and precomposing with the counit at
  `K` — again an epimorphism — rewrites it as the cokernel of a morphism `E (Rs K) ⟶ E (Rs G)`.
  `L` preserves that cokernel, being a left adjoint, and quasi-coherence of `𝒪_Y`-modules is
  closed under colimits by clause (2) of Stacks 03M1,
  `AlgebraicGeometry.Space.isClosedUnderColimitsOfShape_quasicoherentSheaves_of_essentiallySmall`.

What that needs on top of the two is quasi-coherence of `Rs K`, and `Rs` preserves kernels, so it
is enough that `Rs (E (Rs G))` is quasi-coherent — which is exactly
`ExtendScalarsPreservesQuasicoherence` at `Rs G`, quasi-coherent by the second assertion of the
tag, `AlgebraicGeometry.Space.isQuasicoherentOnSite_restrictScalars_structureSharp_iff`.

## Implementation notes

### The abelian structure of `𝒜`-modules

`Stacks.Cohomology.SiteModules.moduleSheavesAbelian` is the instance instance search finds for
`Abelian (SheafOfModules.{u} 𝒜)`, and it does not apply: it asks for a module universe at least
the universe of the objects of the site, which on the small étale site is one above the universe
of the coefficient rings.  It is removed in this file, and the abelian structure is supplied as
`SheafOfModules.instAbelian`, which needs only the sheafification conditions that the small étale
site has at the universe of the coefficient rings.  Without that the kernel and the cokernel of a
morphism of `𝒜`-modules do not elaborate.

## References

* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

noncomputable section

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS} (f : Y ⟶ X)

/-- **Extension of scalars along the structure map `f♯ : 𝒪_X ⟶ 𝒜`** of Stacks 03G8, for
`𝒜 = f_*𝒪_Y`: the functor `𝒢 ↦ 𝒜 ⊗_{𝒪_X} 𝒢` from `𝒪_X`-modules to `𝒜`-modules on the small
étale site of `X`. -/
noncomputable abbrev directImageAlgebraExtendScalars :
    Modules.{u, u} B S hS X.1 X.2 ⥤
      SheafOfModules.{u} (structureRingSheafDirectImage B S hS f) :=
  Stacks.NoncommChangeOfRings.Sheaf.extendScalars.{u} (structureSharp B S hS f)

/-- **Restriction of scalars along the structure map `f♯ : 𝒪_X ⟶ 𝒜`** of Stacks 03G8: an
`𝒜`-module read as an `𝒪_X`-module. -/
noncomputable abbrev directImageAlgebraRestrictScalars :
    SheafOfModules.{u} (structureRingSheafDirectImage B S hS f) ⥤
      Modules.{u, u} B S hS X.1 X.2 :=
  SheafOfModules.restrictScalars.{u} (structureSharp B S hS f)

/-- **Stacks 03CZ at the structure map `f♯ : 𝒪_X ⟶ 𝒜`**: extension of scalars along `f♯` is left
adjoint to restriction of scalars along it. -/
noncomputable def directImageAlgebraExtendRestrictAdjunction :
    directImageAlgebraExtendScalars B S hS f ⊣ directImageAlgebraRestrictScalars B S hS f :=
  Stacks.NoncommChangeOfRings.Sheaf.extendRestrictScalarsAdjunction.{u}
    (structureSharp B S hS f)

/-- **The quasi-inverse of Stacks 08AI precomposed with extension of scalars along `f♯` is the
pullback of modules of Stacks 03LU.**

Both are left adjoints of `AlgebraicGeometry.Space.modulePushforward`: the right adjoint of
`E ⋙ L` is `AlgebraicGeometry.Space.moduleDirectImage` followed by restriction of scalars along
`f♯`, which is `AlgebraicGeometry.Space.modulePushforward` on the nose by
`AlgebraicGeometry.Space.restrictScalars_moduleDirectImage`, and the pullback of modules is left
adjoint to the same functor by `AlgebraicGeometry.Space.modulePullbackAdjunction`. -/
noncomputable def directImageAlgebraPullbackExtendScalarsIso :
    directImageAlgebraExtendScalars B S hS f ⋙ directImageAlgebraPullback B S hS f ≅
      modulePullback B S hS f :=
  Adjunction.leftAdjointUniq
    ((directImageAlgebraExtendRestrictAdjunction B S hS f).comp
      (directImageAlgebraPullbackAdjunction B S hS f))
    (modulePullbackAdjunction B S hS f)

/-- **The quasi-inverse of Stacks 08AI carries the extension of scalars of a quasi-coherent
`𝒪_X`-module to a quasi-coherent `𝒪_Y`-module**, for an arbitrary morphism of algebraic spaces:
it is the pullback of that module by
`AlgebraicGeometry.Space.directImageAlgebraPullbackExtendScalarsIso`, and the pullback of a
quasi-coherent module is quasi-coherent. -/
theorem isQuasicoherentOnSite_directImageAlgebraPullback_extendScalars
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    ((directImageAlgebraPullback B S hS f).obj
      ((directImageAlgebraExtendScalars B S hS f).obj F)).IsQuasicoherentOnSite :=
  (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
    ((directImageAlgebraPullbackExtendScalarsIso B S hS f).app F).symm
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS f F hF)

/-- **The counit of extension and restriction of scalars along `f♯` is an epimorphism**: it
becomes a split epimorphism after restriction of scalars, by the triangle identity, and
restriction of scalars reflects epimorphisms. -/
instance epi_directImageAlgebraExtendRestrictAdjunction_counit
    (G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f)) :
    Epi ((directImageAlgebraExtendRestrictAdjunction B S hS f).counit.app G) := by
  have hsplit : IsSplitEpi ((directImageAlgebraRestrictScalars B S hS f).map
      ((directImageAlgebraExtendRestrictAdjunction B S hS f).counit.app G)) :=
    ⟨⟨_, (directImageAlgebraExtendRestrictAdjunction B S hS f).right_triangle_components G⟩⟩
  have hepi := hsplit.epi
  have hreflects : (directImageAlgebraRestrictScalars B S hS f).ReflectsEpimorphisms :=
    Stacks.AlgebraicGeometry.QcohOverAlgebra.reflectsEpimorphisms_restrictScalars.{u}
      (structureSharp B S hS f)
  exact (directImageAlgebraRestrictScalars B S hS f).epi_of_epi_map hepi

/-- **Extension of scalars along `f♯ : 𝒪_X ⟶ 𝒜`, read back as a functor to `𝒪_X`-modules,
preserves quasi-coherence**, as a statement: the single input of
`AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback_of_extendScalars`.

This is `𝒢 ↦ 𝒜 ⊗_{𝒪_X} 𝒢` preserving quasi-coherence. -/
def ExtendScalarsPreservesQuasicoherence : Prop :=
  ∀ F : Modules.{u, u} B S hS X.1 X.2, F.IsQuasicoherentOnSite →
    ((directImageAlgebraRestrictScalars B S hS f).obj
      ((directImageAlgebraExtendScalars B S hS f).obj F)).IsQuasicoherentOnSite

/-- **The quasi-inverse of Stacks 08AI preserves quasi-coherence, given
`AlgebraicGeometry.Space.ExtendScalarsPreservesQuasicoherence`.**  For an affine morphism
`f : Y ⟶ X` of algebraic spaces this is the hypothesis `hL` of
`AlgebraicGeometry.Space.isEquivalence_quasicoherentDirectImage`, and the argument is global on
`X`: it uses no comparison of the quasi-inverse with restriction to a slice and no colimit
preservation by `f_*`.

A quasi-coherent `𝒜`-module `G` is the cokernel of a morphism `E (Rs K) ⟶ E (Rs G)`, where `K` is
the kernel of the counit at `G`; the quasi-inverse preserves that cokernel and carries both ends
to quasi-coherent modules by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback_extendScalars`, and
quasi-coherence is closed under colimits by clause (2) of Stacks 03M1. -/
theorem isQuasicoherentOnSite_directImageAlgebraPullback_of_extendScalars
    (hf : IsAffineHom B S hS f.hom)
    (hE : ExtendScalarsPreservesQuasicoherence B S hS f)
    (G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f))
    (hG : G.IsQuasicoherentOnSite) :
    ((directImageAlgebraPullback B S hS f).obj G).IsQuasicoherentOnSite := by
  let : Abelian (SheafOfModules.{u} (structureRingSheafDirectImage B S hS f)) :=
    SheafOfModules.instAbelian _
  let : PreservesColimitsOfSize.{0, 0} (directImageAlgebraPullback B S hS f) :=
    (directImageAlgebraPullbackAdjunction B S hS f).leftAdjoint_preservesColimits
  let : PreservesFiniteLimits (directImageAlgebraRestrictScalars B S hS f) :=
    Stacks.AlgebraicGeometry.QcohOverAlgebra.preservesFiniteLimits_restrictScalars.{u}
      (structureSharp B S hS f)
  set ε := (directImageAlgebraExtendRestrictAdjunction B S hS f).counit.app G with hε
  have hRsG : ((directImageAlgebraRestrictScalars B S hS f).obj G).IsQuasicoherentOnSite :=
    (isQuasicoherentOnSite_restrictScalars_structureSharp_iff B S hS f hf G).2 hG
  have hRsERsG := hE _ hRsG
  have hRsK : ((directImageAlgebraRestrictScalars B S hS f).obj
      (kernel ε)).IsQuasicoherentOnSite := by
    have hker := (isQuasicoherentOnSite_kernel_and_cokernel B S hS X.1 X.2
      ((directImageAlgebraRestrictScalars B S hS f).map ε) hRsERsG hRsG).1
    exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
      (asIso (kernelComparison ε (directImageAlgebraRestrictScalars B S hS f))).symm hker
  set η := (directImageAlgebraExtendRestrictAdjunction B S hS f).counit.app (kernel ε)
  have hcoker := isCokernelEpiComp (Abelian.epiIsCokernelOfKernel _ (kernelIsKernel ε))
    (g := η) (h := η ≫ kernel.ι ε) rfl
  have := isClosedUnderColimitsOfShape_quasicoherentSheaves_of_essentiallySmall B S hS Y.1 Y.2
    WalkingParallelPair
  have hc := isColimitOfPreserves (directImageAlgebraPullback B S hS f) hcoker
  have : HasColimit (parallelPair (η ≫ kernel.ι ε) 0 ⋙ directImageAlgebraPullback B S hS f) :=
    ⟨⟨⟨_, hc⟩⟩⟩
  have hD : ∀ k, ((parallelPair (η ≫ kernel.ι ε) 0 ⋙
      directImageAlgebraPullback B S hS f).obj k).IsQuasicoherentOnSite := by
    intro k
    obtain _ | _ := k
    · exact isQuasicoherentOnSite_directImageAlgebraPullback_extendScalars B S hS f _ hRsK
    · exact isQuasicoherentOnSite_directImageAlgebraPullback_extendScalars B S hS f _ hRsG
  exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
    (IsColimit.coconePointUniqueUpToIso (colimit.isColimit _) hc)
    (ObjectProperty.prop_colimit _ _ hD)

/-- **The first assertion of Stacks 08AI, reduced to three statements one of which is about
extension of scalars alone.**  For an affine morphism of algebraic spaces,
`AlgebraicGeometry.Space.AffineDirectImageEquivalence` holds as soon as extension of scalars
along `f♯` preserves quasi-coherence and the unit and counit of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` are invertible at quasi-coherent
modules.

This is `AlgebraicGeometry.Space.affineDirectImageEquivalence_of_isIso_unit_counit` with its
hypothesis `hL` replaced by
`AlgebraicGeometry.Space.ExtendScalarsPreservesQuasicoherence`. -/
theorem affineDirectImageEquivalence_of_extendScalars_of_isIso_unit_counit
    (hf : IsAffineHom B S hS f.hom)
    (hE : ExtendScalarsPreservesQuasicoherence B S hS f)
    (hunit : ∀ G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f),
      G.IsQuasicoherentOnSite →
        IsIso ((directImageAlgebraPullbackAdjunction B S hS f).unit.app G))
    (hcounit : ∀ M : Modules.{u, u} B S hS Y.1 Y.2, M.IsQuasicoherentOnSite →
      IsIso ((directImageAlgebraPullbackAdjunction B S hS f).counit.app M)) :
    AffineDirectImageEquivalence B S hS f :=
  affineDirectImageEquivalence_of_isIso_unit_counit B S hS f
    (fun G hGqc ↦ isQuasicoherentOnSite_directImageAlgebraPullback_of_extendScalars
      B S hS f hf hE G hGqc)
    hf hunit hcounit

end AlgebraicGeometry.Space

end

end
