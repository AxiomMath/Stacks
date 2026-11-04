module

public import StacksFrontier.AlgebraicGeometry.CommonDegreeTwist.AffineSectionBasis
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartAlphaGluing
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGluing
public import StacksFrontier.AlgebraicGeometry.Properties.AmpleProjOpenImmersion
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The geometric input for `α` in Stacks Tag 01N8

Let `A = ⨁_{n ≥ 0} 𝒜 n` be a graded ring, `X = Proj(A)`, `d > 0`, and let `U_d ⊆ X` be the open
of Equation 27.12.0.1. Let `Y` be a scheme, `L` an invertible `𝒪_Y`-module, `ψ` a degreewise
graded map `A^{(d)} → Γ_*(Y, L)` and `φ : Y ⟶ U_d` the morphism glued from the charts of `ψ`.
The existence half of [Stacks, Tag 01N8] also asserts an isomorphism

`α : φ⁎𝒪_{U_d}(d) ≅ L`

carrying the pullback of the degree-`d` section of `f ∈ 𝒜 d` to `ψ(f)`. The abstract machinery
that glues the per-chart isomorphisms into `α` is
`Stacks.AlgebraicGeometry.ProjChartAlpha.glueIso`; it needs, besides the matching condition, two
geometric facts about `φ⁎𝒪_{U_d}(d)` that this file supplies:

* that `φ⁎𝒪_{U_d}(d)` is an *invertible* `𝒪_Y`-module, and
* that the pulled-back degree-`d` section of `f` is *nonvanishing* on `W f`,

and then instantiates `glueIso` to produce `α` itself as data.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjChartAlphaInstance.pullbackDegreeSection`: **`m f`**, the
  pullback along `φ` of the global section of `𝒪_X(d)` attached to `f ∈ 𝒜 d`, in the
  `AlgebraicGeometry.pullbackSectionHom` spelling that
  `Stacks.AlgebraicGeometry.MorphismsIntoProj.psiPullbackHom` uses.
* `Stacks.AlgebraicGeometry.ProjChartAlphaInstance.alpha`: **the isomorphism `α` itself**,
  `glueIso` instantiated at `M = φ⁎𝒪_{U_d}(d)`, `m = pullbackDegreeSection`, `t f = ψ(f)`.

## Main results

* `Stacks.AlgebraicGeometry.ProjChartAlphaInstance.isInvertibleModule_pullbackTwist`:
  **`φ⁎𝒪_{U_d}(d)` is invertible**, in the `Stacks.Ample.IsInvertibleModule` spelling that
  `glueIso` asks for.
* `Stacks.AlgebraicGeometry.ProjChartAlphaInstance.le_nonvanishingOpen_pullbackDegreeSection`:
  **the trivialisation statement.** An open mapping into `D₊(f)` lies in the nonvanishing open of
  `m f`; so `m f` trivialises `φ⁎𝒪_{U_d}(d)` there, by [Stacks, Tag 01CY].
* `Stacks.AlgebraicGeometry.ProjChartAlphaInstance`'s
  `le_nonvanishingOpen_pullbackDegreeSection_of_glue`: the same with the inclusion into
  `φ ⁻¹ᵁ D₊(f)` read off clause (a) of the tag,
  `Stacks.AlgebraicGeometry.ProjChartGluing.preimage_basicOpen_eq_nonvanishingOpen`.
* `Stacks.AlgebraicGeometry.ProjChartAlphaInstance.alpha_hom_app_top`: **the normalisation of
  `α`**, `α (m f) = ψ(f)` for every `f ∈ 𝒜 d`.
* `Stacks.AlgebraicGeometry.ProjChartAlphaInstance.eq_alpha`: `α` is the only isomorphism with
  that normalisation.
* `Stacks.AlgebraicGeometry.ProjChartAlphaInstance.mem_nonvanishingLocus_pullbackSectionHom`:
  [Stacks, Tag 0H78] in the scheme spelling, for a global section pulled back by
  `AlgebraicGeometry.pullbackSectionHom`.
* `Stacks.AlgebraicGeometry.ProjChartAlphaInstance.mem_nonvanishingLocus_degreeSection`:
  [Stacks, Tag 01MV] at `n = 1`, with the degree index left free so that `d` need not be spelled
  `1 * d`.

## Implementation notes

**Nothing of the two chain steps is reproved.** The Proj-side nonvanishing statement is
`Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'`
([Stacks, Tag 01MV], already in the `Stacks.Ample.nonvanishingLocus` spelling), and Tag 0H78 is
`Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff`, which is stated for an
arbitrary morphism of schemes and an arbitrary global section. Only two spelling bridges are
needed, and both are one step: `Stacks.NonvanishingOpen.nonvanishingOpen` is by definition the
bundle of `Stacks.Ample.nonvanishingLocus`, so an inclusion of opens is a statement about the
loci and nothing has to be transported; and
`AlgebraicGeometry.pullbackSectionHom f M ⊤ ⊤ h` differs from
`Stacks.NonvanishingPullback.pullbackGlobalSection f M` by the restriction along `⊤ ⟶ f ⁻¹ᵁ ⊤`,
which is the identity because `f ⁻¹ᵁ ⊤ = ⊤` by `rfl`.

**The degree index of Tag 01MV.** `mem_nonvanishingLocus_degreeSection_iff'` is stated for
`f ∈ 𝒮 (n * d)`, and here `n = 1`; but `1 * d` is not `d` for a variable `d`, and the twist and
the section are indexed by that natural number. Rather than transporting the section,
`mem_nonvanishingLocus_degreeSection` takes the degree `k` and the equation `k = 1 * d` as
separate arguments and substitutes, so that the caller supplies `k = d` and `one_mul d`.

**Invertibility is assembled, not assumed.** `𝒪_X(d)` is *not* invertible on all of `Proj A`, so
`Stacks.InvertiblePullback.isInvertibleModule_pullback` cannot be applied to `φ ≫ U_d.ι`
directly. The twist becomes invertible only after restriction to `U_d`, which is
`Stacks.AlgebraicGeometry.MorphismsIntoProj.isInvertible_pullback_twistingSheaf_degreeOpen`
([Stacks, Tag 01MU]); the pullback along `φ` of *that* is invertible by Tag 0B8L, and
`AlgebraicGeometry.Scheme.Modules.pullbackComp` identifies it with the pullback along the
composite.

**The indexing of the sections is left alone.** `t f` is `ψ.pow f.2 1`, a global section of
`L ^⊗ 1` and not of `L`; the two differ by the left unitor, and no transport along it appears
here, exactly as in `Stacks.AlgebraicGeometry.Constructions.MorphismToProjRatios` and
`ProjChartGluing`. For the same reason `α` lands in `L ^⊗ 1`. The family `W` is left free: only
`⨆ f, W f = ⊤` and `W f ≤ Y_{ψ(f)}` are used, and taking `W f = Y_{ψ(f)}` recovers the source's
charts.

**`pullbackDegreeSection` versus `psiPullbackHom`.** The two are the same construction, but
`Stacks.AlgebraicGeometry.MorphismsIntoProj.psiPullbackHom 𝒜 φ 1` has `𝒜 (1 * d)` as its source
and `φ⁎𝒪_X((1 * d : ℕ))` as its target, so identifying them is again a transport along
`1 * d = d`. It belongs with the assembly of the combined statement, not here.

**No `@[stacks 01N8]` attribute is attached here, because it is attached elsewhere.** Tag 01N8 is
the conjunction of the existence of the pair `(φ, α)` with its uniqueness; neither is asserted
below on its own, so the attribute belongs on the combined statement, and the combined statement
exists: it is `Stacks.AlgebraicGeometry.MorphismToProjUniversal.existsUnique_pair`, which carries
`@[stacks 01N8]` and is the one registration of the tag in this repository. What this file
supplies to it is the per-chart trivialization `α`.

## References

* [Stacks Project, Tag 01N8](https://stacks.math.columbia.edu/tag/01N8)
* [Stacks Project, Section 01N4](https://stacks.math.columbia.edu/tag/01N4)
* [Stacks Project, Equation 01N5](https://stacks.math.columbia.edu/tag/01N5)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01MV](https://stacks.math.columbia.edu/tag/01MV)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry
open AlgebraicGeometry.Proj (degreeOpen)
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.MorphismsIntoProj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.TensorPowers (natTensorPow)
open Stacks.NonvanishingOpen (nonvanishingOpen)

universe u w

namespace Stacks.AlgebraicGeometry.ProjChartAlphaInstance

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Tag 0H78 for a section pulled back by `pullbackSectionHom` -/

/-- **[Stacks, Tag 0H78] in the scheme spelling, for `AlgebraicGeometry.pullbackSectionHom`.**
The pullback of a global section does not vanish wherever the section does not vanish.

`Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff` is this statement for
`Stacks.NonvanishingPullback.pullbackGlobalSection`; the two spellings of the pulled-back section
differ by the restriction along `⊤ ⟶ f ⁻¹ᵁ ⊤`, which is the identity. -/
theorem mem_nonvanishingLocus_pullbackSectionHom {X Y : Scheme.{u}} (f : Y ⟶ X) (M : X.Modules)
    (h : (⊤ : Y.Opens) ≤ f ⁻¹ᵁ ⊤) (s : Γ(M, ⊤)) {y : Y}
    (hy : f.base y ∈ Stacks.Ample.nonvanishingLocus M s) :
    y ∈ Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback f).obj M)
      (pullbackSectionHom f M ⊤ ⊤ h s) := by
  have hsec : pullbackSectionHom f M ⊤ ⊤ h s =
      Stacks.NonvanishingPullback.pullbackGlobalSection f M s := by
    show ((Scheme.Modules.pullback f).obj M).presheaf.map
        (eqToHom (show f ⁻¹ᵁ (⊤ : X.Opens) = ⊤ from rfl)).op
        (Stacks.NonvanishingPullback.pullbackGlobalSection f M s) = _
    exact Functor.map_id_apply _ _ _
  rw [hsec]
  exact (Stacks.NonvanishingPullback.mem_nonvanishingLocus_pullback_iff f M s y).mpr hy

section Proj

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜]

/-! ### Tag 01MV in degree `d` -/

/-- **[Stacks, Tag 01MV] at `n = 1`**: on the invertible locus `W_d`, the global section of
`𝒪_X(d)` attached to a homogeneous `f` of degree `d` is nonvanishing at every point of `D₊(f)`.

The degree is carried by a separate argument `k` together with the equation `k = 1 * d`, because
the twist and the section are indexed by a natural number and `1 * d` is not `d`; a caller passes
`k = d` and `(one_mul d).symm`. -/
theorem mem_nonvanishingLocus_degreeSection {d k : ℕ} (hk : k = 1 * d) (f : 𝒜 k)
    {x : ProjectiveSpectrum.top 𝒜}
    (hx : x ∈ Stacks.AlgebraicGeometry.ProjInvertibleLocus.whereInvertible 𝒜 d)
    (hf : x ∈ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) :
    x ∈ Stacks.Ample.nonvanishingLocus (X := AlgebraicGeometry.Proj 𝒜)
      (twistingSheaf 𝒜 (k : ℤ)) (degreeSection 𝒜 k f) := by
  subst hk
  exact (Stacks.AlgebraicGeometry.CommonDegreeTwist.mem_nonvanishingLocus_degreeSection_iff'
    𝒜 d 1 f hx).mpr hf

/-! ### Invertibility of the pulled-back twist -/

variable {Y : Scheme.{u}} {d : ℕ}

/-- **`𝒪_{U_d}(d)` is an invertible `𝒪_{U_d}`-module**, in the
`Stacks.Ample.IsInvertibleModule` spelling. This is
`Stacks.AlgebraicGeometry.MorphismsIntoProj.isInvertible_pullback_twistingSheaf_degreeOpen`
([Stacks, Tag 01MU]) at `n = 1`. -/
@[ega "II 2.6.1" "more general"]
instance isInvertibleModule_restrict_twistingSheaf_degreeOpen :
    Stacks.Ample.IsInvertibleModule (degreeOpen 𝒜 d).toScheme
      ((Scheme.Modules.pullback (degreeOpen 𝒜 d).ι).obj (twistingSheaf 𝒜 (d : ℤ))) := by
  have h := isInvertible_pullback_twistingSheaf_degreeOpen 𝒜 d 1
  rwa [mul_one] at h

/-- **`φ⁎𝒪_{U_d}(d)` is an invertible `𝒪_Y`-module.** The twist `𝒪_X(d)` is invertible only after
restriction to `U_d` ([Stacks, Tag 01MU]), the pullback along `φ` of an invertible module is
invertible ([Stacks, Tag 0B8L]), and
`AlgebraicGeometry.Scheme.Modules.pullbackComp` identifies the iterated pullback with the
pullback along `φ ≫ U_d.ι`. At `φ = 𝟙` this is the invertibility of `𝒪_{U_d}(d)`, the module of
the universal family of [Stacks, Tag 01N9]. -/
@[stacks 01N9 "the universal family (d, 𝒪_{U_d}(d), ψ^d): 𝒪_{U_d}(d) is an invertible \
𝒪_{U_d}-module"]
instance isInvertibleModule_pullbackTwist (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) :
    Stacks.Ample.IsInvertibleModule Y (pullbackTwist 𝒜 φ (d : ℤ)) :=
  letI : Stacks.Ample.IsInvertibleModule Y
      ((Scheme.Modules.pullback (degreeOpen 𝒜 d).ι ⋙ Scheme.Modules.pullback φ).obj
        (twistingSheaf 𝒜 (d : ℤ))) :=
    Stacks.InvertiblePullback.isInvertibleModule_pullback φ _
  Stacks.AlgebraicGeometry.ProjAmpleTwist.isInvertibleModule_of_iso
    ((Scheme.Modules.pullbackComp φ (degreeOpen 𝒜 d).ι).app (twistingSheaf 𝒜 (d : ℤ)))

/-! ### The pulled-back degree-`d` sections -/

/-- **`m f`**: the pullback along `φ : Y ⟶ U_d` of the global section of `𝒪_X(d)` attached to a
homogeneous element `f` of degree `d`. This is the degree-one value of `ψ^d_φ`, in the spelling
`Stacks.AlgebraicGeometry.MorphismsIntoProj.psiPullbackHom` uses. -/
def pullbackDegreeSection (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) (f : 𝒜 d) :
    Γ(pullbackTwist 𝒜 φ (d : ℤ), ⊤) :=
  pullbackSectionHom (toProj 𝒜 φ) (twistingSheaf 𝒜 (d : ℤ)) ⊤ ⊤ (by simp)
    (degreeSection 𝒜 d f)

/-- A morphism through `U_d` lands in `U_d`. -/
theorem mem_degreeOpen_toProj (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) (y : Y) :
    (toProj 𝒜 φ).base y ∈ degreeOpen 𝒜 d :=
  (Scheme.Opens.range_ι (U := degreeOpen 𝒜 d)).le ⟨φ.base y, rfl⟩

/-- **The trivialisation statement.** If an open `W` of `Y` maps into the standard open `D₊(f)`
under `φ`, then the pulled-back degree-`d` section `m f` is nonvanishing on `W`; by
[Stacks, Tag 01CY] it therefore trivialises `φ⁎𝒪_{U_d}(d)` there.

Two inputs: `m f` is nonvanishing at the image point because that point lies in `D₊(f)` and in
`U_d ⊆ W_d` ([Stacks, Tag 01MV], `mem_nonvanishingLocus_degreeSection`), and the nonvanishing
locus of a pulled-back section is the preimage of the nonvanishing locus ([Stacks, Tag 0H78],
`mem_nonvanishingLocus_pullbackSectionHom`). -/
theorem le_nonvanishingOpen_pullbackDegreeSection (φ : Y ⟶ (degreeOpen 𝒜 d).toScheme) (f : 𝒜 d)
    {W : Y.Opens} (hW : W ≤ toProj 𝒜 φ ⁻¹ᵁ AlgebraicGeometry.Proj.basicOpen 𝒜 (f : A)) :
    W ≤ nonvanishingOpen Y (pullbackTwist 𝒜 φ (d : ℤ)) (pullbackDegreeSection 𝒜 φ f) := by
  intro y hy
  refine mem_nonvanishingLocus_pullbackSectionHom (toProj 𝒜 φ) (twistingSheaf 𝒜 (d : ℤ)) _
    (degreeSection 𝒜 d f) ?_
  exact mem_nonvanishingLocus_degreeSection 𝒜 (one_mul d).symm f
    (degreeOpen_le_whereInvertible 𝒜 d (mem_degreeOpen_toProj 𝒜 φ y)) (hW hy)

end Proj

/-! ### The isomorphism `α` -/

section Alpha

open Stacks.AlgebraicGeometry.ProjChartFromRatios
open Stacks.AlgebraicGeometry.ProjChartAlpha

variable {σ : Type w} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {d : ℕ} {Y : Scheme.{u}} {L : Y.Modules}
  [Stacks.Ample.IsInvertibleModule Y L]

/-- **The trivialisation statement, with the inclusion read off clause (a) of
[Stacks, Tag 01N8].** For `φ` glued from the charts of `ψ`, the preimage of `D₊(f)` is `Y_{ψ(f)}`
(`Stacks.AlgebraicGeometry.ProjChartGluing.preimage_basicOpen_eq_nonvanishingOpen`), and `W f`
lies inside it; so `m f` is nonvanishing on `W f`. -/
theorem le_nonvanishingOpen_pullbackDegreeSection_of_glue (hd : 0 < d)
    (ψ : VeroneseSections 𝒜 d L) {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {W : 𝒜 d → Y.Opens}
    (hWle : ∀ g : 𝒜 d, W g ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1))
    (hcover : ⨆ g : 𝒜 d, W g = ⊤)
    (hglue : ∀ g : 𝒜 d, (W g).ι ≫ φ = ψ.toDegreeOpen g.2 (hWle g) hd) (f : 𝒜 d) :
    W f ≤ nonvanishingOpen Y (pullbackTwist 𝒜 φ (d : ℤ)) (pullbackDegreeSection 𝒜 φ f) :=
  le_nonvanishingOpen_pullbackDegreeSection 𝒜 φ f
    ((hWle f).trans
      (Stacks.AlgebraicGeometry.ProjChartGluing.preimage_basicOpen_eq_nonvanishingOpen 𝒜 hd ψ
        hWle hcover hglue f).ge)

/-- **The isomorphism `α : φ⁎𝒪_{U_d}(d) ≅ L^{⊗ 1}` of the existence half of
[Stacks, Tag 01N8].** It is `Stacks.AlgebraicGeometry.ProjChartAlpha.glueIso` instantiated at
`M = φ⁎𝒪_{U_d}(d)`, `m f` the pullback of the degree-`d` section of `f` and `t f = ψ(f)`: the
per-chart isomorphisms divide by `m f` and multiply by `ψ(f)`, and they glue because the two
families have the same transition functions, which is `hmatch`.

The invertibility of `φ⁎𝒪_{U_d}(d)` is `isInvertibleModule_pullbackTwist` and the trivialisation
is `le_nonvanishingOpen_pullbackDegreeSection_of_glue`; `hmatch` is the source's sentence "the
`α_f` agree because the regular functions `s/s'` and `ψ_{(f')}(f/f')` agree". -/
def alpha (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {W : 𝒜 d → Y.Opens}
    (hWle : ∀ g : 𝒜 d, W g ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1))
    (hcover : ⨆ g : 𝒜 d, W g = ⊤)
    (hglue : ∀ g : 𝒜 d, (W g).ι ≫ φ = ψ.toDegreeOpen g.2 (hWle g) hd)
    (hmatch : Matching (pullbackDegreeSection 𝒜 φ) (fun g : 𝒜 d => ψ.pow g.2 1) W) :
    pullbackTwist 𝒜 φ (d : ℤ) ≅ natTensorPow L 1 :=
  glueIso (pullbackDegreeSection 𝒜 φ) (fun g : 𝒜 d => ψ.pow g.2 1) W
    (le_nonvanishingOpen_pullbackDegreeSection_of_glue 𝒜 hd ψ hWle hcover hglue) hWle hcover
    hmatch

/-- **The normalisation of `α`**: it carries the pullback of the degree-`d` section of `f` to
`ψ(f)`, for every `f ∈ 𝒜 d`. This is the pinning the source states, and the shape
`Stacks.AlgebraicGeometry.ProjSectionsUnique.iso_eq_of_app_eq` consumes. -/
theorem alpha_hom_app_top (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {W : 𝒜 d → Y.Opens}
    (hWle : ∀ g : 𝒜 d, W g ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1))
    (hcover : ⨆ g : 𝒜 d, W g = ⊤)
    (hglue : ∀ g : 𝒜 d, (W g).ι ≫ φ = ψ.toDegreeOpen g.2 (hWle g) hd)
    (hmatch : Matching (pullbackDegreeSection 𝒜 φ) (fun g : 𝒜 d => ψ.pow g.2 1) W) (f : 𝒜 d) :
    (alpha 𝒜 hd ψ hWle hcover hglue hmatch).hom.app ⊤ (pullbackDegreeSection 𝒜 φ f) =
      ψ.pow f.2 1 :=
  glueIso_hom_app_top (pullbackDegreeSection 𝒜 φ) (fun g : 𝒜 d => ψ.pow g.2 1) W
    (le_nonvanishingOpen_pullbackDegreeSection_of_glue 𝒜 hd ψ hWle hcover hglue) hWle hcover
    hmatch f

/-- **`α` is the only isomorphism with that normalisation.** Uniqueness is
`Stacks.AlgebraicGeometry.ProjChartAlpha.eq_glueIso`, i.e. the omitted verification of
[Stacks, Tag 01N8] supplied by
`Stacks.AlgebraicGeometry.ProjSectionsUnique.iso_eq_of_app_eq`. -/
theorem eq_alpha (hd : 0 < d) (ψ : VeroneseSections 𝒜 d L)
    {φ : Y ⟶ (degreeOpen 𝒜 d).toScheme} {W : 𝒜 d → Y.Opens}
    (hWle : ∀ g : 𝒜 d, W g ≤ nonvanishingOpen Y (natTensorPow L 1) (ψ.pow g.2 1))
    (hcover : ⨆ g : 𝒜 d, W g = ⊤)
    (hglue : ∀ g : 𝒜 d, (W g).ι ≫ φ = ψ.toDegreeOpen g.2 (hWle g) hd)
    (hmatch : Matching (pullbackDegreeSection 𝒜 φ) (fun g : 𝒜 d => ψ.pow g.2 1) W)
    (β : pullbackTwist 𝒜 φ (d : ℤ) ≅ natTensorPow L 1)
    (hβ : ∀ f : 𝒜 d, β.hom.app ⊤ (pullbackDegreeSection 𝒜 φ f) = ψ.pow f.2 1) :
    β = alpha 𝒜 hd ψ hWle hcover hglue hmatch :=
  eq_glueIso (pullbackDegreeSection 𝒜 φ) (fun g : 𝒜 d => ψ.pow g.2 1) W
    (le_nonvanishingOpen_pullbackDegreeSection_of_glue 𝒜 hd ψ hWle hcover hglue) hWle hcover
    hmatch β hβ

end Alpha

end Stacks.AlgebraicGeometry.ProjChartAlphaInstance

end
