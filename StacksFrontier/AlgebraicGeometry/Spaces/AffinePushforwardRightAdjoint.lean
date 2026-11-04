module

public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraCoextendScalarsInternalHom
public import StacksFrontier.AlgebraicGeometry.Spaces.ResolutionPropertyIdealPowSum

/-!
# The right adjoint of the direct image along an affine morphism, and the trace of Stacks 0GUZ

Let `π : Y ⟶ X` be an affine morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and let `𝒜 = π_*𝒪_Y` be the direct-image algebra of Stacks 03G8.  Write `Res`
and `Coext` for restriction and coextension of scalars along `π♯ : 𝒪_X ⟶ 𝒜`, and `L` for the
quasi-inverse `𝒢 ↦ 𝒪_Y ⊗_{π⁻¹𝒜} π⁻¹𝒢` of the affine direct image equivalence of
[Stacks, Tag 08AI].  This file constructs the functor

`π^! : 𝓝 ↦ L(Coext 𝓝) = L(𝓗om_{𝒪_X}(π_*𝒪_Y, 𝓝))`

from `𝒪_X`-modules to `𝒪_Y`-modules and proves that it is **right adjoint to `π_*` on
quasi-coherent modules**:

`Hom_{𝒪_Y}(𝒩, π^!ℱ) ≃ Hom_{𝒪_X}(π_*𝒩, ℱ)`.

Its value at `𝒪_X` is the relative dualizing module `ω_{Y/X}` of [Stacks, Tag 0GUZ], already
constructed as `AlgebraicGeometry.Space.relativeDualizingModule`, and the trace
`Tr_π : π_*ω_{Y/X} ⟶ 𝒪_X` of that tag is assembled below out of the characterising isomorphism
`π_*ω_{Y/X} ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` and
`AlgebraicGeometry.Space.dualizingTrace`.

## Why this replaces the projection formula

Steps (1)–(4) of the proof of [Stacks, Tag 0GUZ] turn a section of `π^*ℱ ⊗_{𝒪_Y} ω_{Y/X}` over
the chart `V` into a map `σ : π_*(ℐ^n) ⟶ ℱ`, and the source performs the last move with the
projection formula `π_*(π^*ℱ ⊗_{𝒪_Y} 𝒢) ≅ ℱ ⊗_{𝒪_X} π_*𝒢` of [Stacks, Tag 0DK4] followed by
the trace.  For a finite morphism of algebraic spaces that isomorphism is *not* available in
this development: the canonical map of Stacks 0DK4 is
`AlgebraicGeometry.Space.tensorPushforwardMap`, and the only unconditional proof that it is
invertible is for a closed immersion
(`AlgebraicGeometry.Space.isIso_tensorPushforwardMap_of_isClosedImmersion`, Stacks 04G0), the
stalk route needing the direct-image stalk of Stacks 0DK3, which reduces to Stacks 03QP for
schemes and is absent.

The adjunction below reaches the same maps `σ` without it.  Composing the hom-set bijection of
[Stacks, Tag 03D4] with the invertibility of its unit and counit at quasi-coherent modules
(Stacks 08AI) and with `Res ⊣ Coext` gives

`Hom_{𝒪_Y}(𝒩, L(Coext ℱ)) ≃ Hom_𝒜(π_*^𝒜𝒩, Coext ℱ) ≃ Hom_{𝒪_X}(Res(π_*^𝒜𝒩), ℱ)`,

and `Res ∘ π_*^𝒜` is the direct image of `𝒪_X`-modules of Stacks 03LU on the nose
(`AlgebraicGeometry.Space.restrictScalars_moduleDirectImage`).  No tensor product and no
projection formula appear anywhere in the chain.

## Main definitions

* `AlgebraicGeometry.Space.affinePushforwardRightAdjoint` — the functor `π^!`.
* `AlgebraicGeometry.Space.relativeDualizingTrace` — the trace
  `Tr_π : π_*ω_{Y/X} ⟶ 𝒪_X` of [Stacks, Tag 0GUZ].
* `AlgebraicGeometry.Space.resolutionSituationSigma` — the maps `σ : π_*(ℐ^n) ⟶ ℱ` of
  [Stacks, Tag 0GUZ], in the situation of [Stacks, Tag 0GUY].

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraCoextendScalars` —
  **`𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)` is quasi-coherent as an `𝒜`-module** for every quasi-coherent `ℱ`,
  when `π` is affine and `π_*𝒪_Y` is of finite presentation.  This is Stacks 03M1(6) read
  through `AlgebraicGeometry.Space.restrictCoextendNatIsoInternalHom` and the second assertion
  of Stacks 08AI; at `ℱ = 𝒪_X` it is
  `AlgebraicGeometry.Space.isQuasicoherentOnSite_dualizingAlgebraModule`.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_affinePushforwardRightAdjoint_obj` — `π^!ℱ` is
  quasi-coherent.
* `AlgebraicGeometry.Space.moduleDirectImage_affinePushforwardRightAdjointIso` and
  `AlgebraicGeometry.Space.modulePushforward_affinePushforwardRightAdjointIso` — the
  characterising isomorphism `π_*(π^!ℱ) ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)`, over `𝒜` and over `𝒪_X`.  At
  `ℱ = 𝒪_X` these are the two isomorphisms of [Stacks, Tag 0GUZ] for `ω_{Y/X}`.
* `AlgebraicGeometry.Space.homEquivAffinePushforwardRightAdjoint` — **`π^!` is right adjoint to
  `π_*` on quasi-coherent modules.**

## Implementation notes

`AlgebraicGeometry.Space.affinePushforwardRightAdjoint_obj_unit` records that `π^!𝒪_X` *is*
`AlgebraicGeometry.Space.relativeDualizingModule`, by `rfl`:
`AlgebraicGeometry.Space.dualizingAlgebraModule` is the coextension of `𝒪_X` by definition.  So
the hom-set bijection applies to `ω_{Y/X}` with no transport, and
`AlgebraicGeometry.Space.relativeDualizingTrace` is a map out of `π_*ω_{Y/X}` in the spelling
the bijection produces.

The trace is built from the already constructed `AlgebraicGeometry.Space.dualizingTrace`, which
is evaluation at `1 ∈ π_*𝒪_Y`, rather than from the counit of
`AlgebraicGeometry.Space.directImageAlgebraRestrictCoextendAdjunction`.  The two agree — the
counit at `𝒪_X` is evaluation at `1` under
`AlgebraicGeometry.Space.restrictScalars_dualizingAlgebraModuleIso` — but that identification is
a computation with the abstractly produced right adjoint of
`StacksFrontier/AlgebraicGeometry/Spaces/DualizingAlgebraModule.lean` and is not carried out here;
nothing below depends on it.

Each hom-set bijection is assembled with `CategoryTheory.Iso.homCongr` and
`CategoryTheory.Adjunction.homEquiv` rather than by exhibiting `π^!` as a right adjoint of `π_*`
as functors.  The reason is that `π_*` is a right adjoint of
`AlgebraicGeometry.Space.modulePullback` already, and is not a left adjoint on the whole
category of `𝒪_Y`-modules: the bijection holds only where the counit of Stacks 03D4 is
invertible, that is at quasi-coherent `𝒩`, which is a condition on the object and not on the
functor.

The two global instances `Stacks.Cohomology.SiteModules.moduleSheavesAbelian` and its
Grothendieck counterpart hold only at a module universe which is a `max` of the site universes
and leave a stuck universe constraint at the pinned module universe `u`; they are removed here,
exactly as in `StacksFrontier/AlgebraicGeometry/Spaces/DualizingAlgebraModule.lean`.

## Where [Stacks, Tag 0GUZ] is proved

The surjectivity of the direct sum of the maps below is proved in
`StacksFrontier/AlgebraicGeometry/Spaces/ResolutionPropertySurjection.lean`, as
`AlgebraicGeometry.Space.exists_epi_biproduct_idealSheafPowPushforward`, which carries
`@[stacks 0GUZ]`.  It uses `π^!` and the counit `π_*π^!ℱ ⟶ ℱ` of this file in place of
`π^*ℱ ⊗ ω_{Y/X}` and its trace; the étale-local splitting of the source is
`AlgebraicGeometry.Space.exists_etale_split_section_factorsThrough_idealSheafPow`.

## References

* [Stacks Project, Tag 0GUZ](https://stacks.math.columbia.edu/tag/0GUZ), Lemma 76.56.2, whose
  proof constructs `ω_{Y/X}`, `Tr_π` and the maps `σ_i` inline.
* [Stacks Project, Tag 0GUY](https://stacks.math.columbia.edu/tag/0GUY), Situation 76.56.1.
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
* [Stacks Project, Tag 0DK4](https://stacks.math.columbia.edu/tag/0DK4)
* [Stacks Project, Tag 0ADU](https://stacks.math.columbia.edu/tag/0ADU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

section General

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-! ### Quasi-coherence of the coextension of scalars -/

/-- **`𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)` is quasi-coherent as a `π_*𝒪_Y`-module**, for an affine morphism of
algebraic spaces whose `π_*𝒪_Y` is of finite presentation and a quasi-coherent `𝒪_X`-module
`ℱ`.

Its underlying `𝒪_X`-module is the internal Hom `𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)` by
`AlgebraicGeometry.Space.restrictCoextendNatIsoInternalHom`, which is quasi-coherent by
Stacks 03M1(6), and the second assertion of Stacks 08AI turns quasi-coherence over `𝒪_X` into
quasi-coherence over `π_*𝒪_Y`.

At `ℱ = 𝒪_X` this is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_dualizingAlgebraModule`. -/
theorem isQuasicoherentOnSite_directImageAlgebraCoextendScalars (π : Y ⟶ X)
    (hπ : IsAffineHom B S hS π.hom)
    (hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    ((directImageAlgebraCoextendScalars B S hS π).obj F).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_restrictScalars_structureSharp_iff B S hS π hπ
      ((directImageAlgebraCoextendScalars B S hS π).obj F)).1
    (SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((restrictCoextendNatIsoInternalHom B S hS π).app F).symm
      (isQuasicoherentOnSite_internalHomSheafSmall B S hS X.1 X.2
        (pushforwardStructureModule B S hS π) F
        (isQuasicoherentOnSite_restrictScalars_structureRingSheafDirectImage B S hS π hπ)
        hF hfp))

/-! ### The functor `π^!` -/

/-- **The right adjoint `π^!` of the direct image along an affine morphism of algebraic
spaces**: coextension of scalars along `π♯ : 𝒪_X ⟶ π_*𝒪_Y` followed by the quasi-inverse of the
affine direct image equivalence of [Stacks, Tag 08AI], that is
`ℱ ↦ 𝒪_Y ⊗_{π⁻¹𝒜} π⁻¹𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)`.

The construction needs no hypothesis on `π`; it is the hom-set bijection
`AlgebraicGeometry.Space.homEquivAffinePushforwardRightAdjoint` that does.  Its value at `𝒪_X`
is the relative dualizing module `ω_{Y/X}` of [Stacks, Tag 0GUZ], by
`AlgebraicGeometry.Space.affinePushforwardRightAdjoint_obj_unit`. -/
def affinePushforwardRightAdjoint (π : Y ⟶ X) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ Modules.{u, u} B S hS Y.1 Y.2 :=
  directImageAlgebraCoextendScalars B S hS π ⋙ directImageAlgebraPullback B S hS π

/-- **`π^!𝒪_X` is the relative dualizing module `ω_{Y/X}`** of [Stacks, Tag 0GUZ].  This holds on
the nose: `AlgebraicGeometry.Space.dualizingAlgebraModule` is by definition the coextension of
scalars of `𝒪_X` along `π♯`, and `AlgebraicGeometry.Space.relativeDualizingModule` is the value
of the quasi-inverse of [Stacks, Tag 08AI] at it. -/
theorem affinePushforwardRightAdjoint_obj_unit (π : Y ⟶ X) :
    (affinePushforwardRightAdjoint B S hS π).obj
        (SheafOfModules.unit (structureRingSheaf B S hS X)) =
      relativeDualizingModule B S hS π := rfl

/-- **`π^!ℱ` is quasi-coherent**, for an affine morphism whose `π_*𝒪_Y` is of finite presentation
and a quasi-coherent `ℱ`: the quasi-inverse of Stacks 08AI carries quasi-coherent
`π_*𝒪_Y`-modules to quasi-coherent `𝒪_Y`-modules. -/
theorem isQuasicoherentOnSite_affinePushforwardRightAdjoint_obj (π : Y ⟶ X)
    (hπ : IsAffineHom B S hS π.hom)
    (hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    ((affinePushforwardRightAdjoint B S hS π).obj F).IsQuasicoherentOnSite :=
  isQuasicoherentOnSite_directImageAlgebraPullback B S hS π hπ
    ((directImageAlgebraCoextendScalars B S hS π).obj F)
    (isQuasicoherentOnSite_directImageAlgebraCoextendScalars B S hS π hπ hfp F hF)

/-- **The characterising isomorphism `π_*(π^!ℱ) ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)` over `𝒜 = π_*𝒪_Y`.**

It is the unit of Stacks 03D4 at `𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)`, invertible because that module is
quasi-coherent and `π` is affine.  At `ℱ = 𝒪_X` it is
`AlgebraicGeometry.Space.moduleDirectImage_relativeDualizingModuleIso`, the isomorphism
[Stacks, Tag 0GUZ] characterises `ω_{Y/X}` by. -/
def moduleDirectImage_affinePushforwardRightAdjointIso (π : Y ⟶ X)
    (hπ : IsAffineHom B S hS π.hom)
    (hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    (directImageAlgebraCoextendScalars B S hS π).obj F ≅
      (moduleDirectImage B S hS π).obj
        ((affinePushforwardRightAdjoint B S hS π).obj F) :=
  @asIso _ _ _ _
    ((directImageAlgebraPullbackAdjunction B S hS π).unit.app
      ((directImageAlgebraCoextendScalars B S hS π).obj F))
    (isIso_directImageAlgebraPullbackAdjunction_unit_app_of_isAffineHom B S hS π hπ
      ((directImageAlgebraCoextendScalars B S hS π).obj F)
      (isQuasicoherentOnSite_directImageAlgebraCoextendScalars B S hS π hπ hfp F hF))

/-- **The characterising isomorphism `π_*(π^!ℱ) ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)` over `𝒪_X`**, with the
direct image of Stacks 03LU on the left.

It is `AlgebraicGeometry.Space.moduleDirectImage_affinePushforwardRightAdjointIso` read over
`𝒪_X` — the two readings of the direct image differ only by restriction of scalars along `π♯` —
followed by `AlgebraicGeometry.Space.restrictCoextendNatIsoInternalHom`. -/
def modulePushforward_affinePushforwardRightAdjointIso (π : Y ⟶ X)
    (hπ : IsAffineHom B S hS π.hom)
    (hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) :
    (modulePushforward B S hS π).obj
        ((affinePushforwardRightAdjoint B S hS π).obj F) ≅
      smallEtaleInternalHomSmall B S hS X.1 X.2 (pushforwardStructureModule B S hS π) F :=
  ((directImageAlgebraRestrictScalars B S hS π).mapIso
      (moduleDirectImage_affinePushforwardRightAdjointIso B S hS π hπ hfp F hF)).symm ≪≫
    (restrictCoextendNatIsoInternalHom B S hS π).app F

/-! ### The adjunction -/

/-- **`π^!` is right adjoint to the direct image `π_*` on quasi-coherent modules**, for an affine
morphism `π : Y ⟶ X` of algebraic spaces whose `π_*𝒪_Y` is of finite presentation:

`Hom_{𝒪_Y}(𝒩, π^!ℱ) ≃ Hom_{𝒪_X}(π_*𝒩, ℱ)`

for quasi-coherent `𝒩` on `Y` and quasi-coherent `ℱ` on `X`.

The chain is: precomposition with the counit of Stacks 03D4 at `𝒩`, invertible because `𝒩` is
quasi-coherent and `π` affine; the hom-set bijection of Stacks 03D4 itself; postcomposition with
the inverse of its unit at `𝓗om_{𝒪_X}(π_*𝒪_Y, ℱ)`; and the hom-set bijection of
`AlgebraicGeometry.Space.directImageAlgebraRestrictCoextendAdjunction`, that is `Res ⊣ Coext`.
The composite lands on `Res(π_*^𝒜𝒩)`, which is the direct image of Stacks 03LU on the nose by
`AlgebraicGeometry.Space.restrictScalars_moduleDirectImage`.

This is the step of [Stacks, Tag 0GUZ] that produces its maps `σ : π_*(ℐ^n) ⟶ ℱ` out of
sections over the chart, and it replaces the projection formula of [Stacks, Tag 0DK4] that the
source uses for the same purpose; see the module documentation. -/
def homEquivAffinePushforwardRightAdjoint (π : Y ⟶ X)
    (hπ : IsAffineHom B S hS π.hom)
    (hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite)
    (N : Modules.{u, u} B S hS Y.1 Y.2) (hN : N.IsQuasicoherentOnSite) :
    (N ⟶ (affinePushforwardRightAdjoint B S hS π).obj F) ≃
      ((modulePushforward B S hS π).obj N ⟶ F) :=
  (Iso.homCongr
        (@asIso _ _ _ _ ((directImageAlgebraPullbackAdjunction B S hS π).counit.app N)
          (isIso_directImageAlgebraPullbackAdjunction_counit_app_of_isAffineHom B S hS π hπ N hN))
        (Iso.refl ((affinePushforwardRightAdjoint B S hS π).obj F))).symm.trans
    (((directImageAlgebraPullbackAdjunction B S hS π).homEquiv
          ((moduleDirectImage B S hS π).obj N)
          ((affinePushforwardRightAdjoint B S hS π).obj F)).trans
      ((Iso.homCongr (Iso.refl ((moduleDirectImage B S hS π).obj N))
            (moduleDirectImage_affinePushforwardRightAdjointIso B S hS π hπ hfp F hF).symm).trans
        ((directImageAlgebraRestrictCoextendAdjunction B S hS π).homEquiv
          ((moduleDirectImage B S hS π).obj N) F).symm))

/-! ### The trace -/

/-- **The trace `Tr_π : π_*ω_{Y/X} ⟶ 𝒪_X` of [Stacks, Tag 0GUZ]**, for an affine morphism of
algebraic spaces whose `π_*𝒪_Y` is of finite presentation.

The source obtains it from the map `𝒪_X ⟶ π_*𝒪_Y` of [Stacks, Tag 03G8]: the characterising
isomorphism `π_*ω_{Y/X} ≅ 𝓗om_{𝒪_X}(π_*𝒪_Y, 𝒪_X)` identifies `π_*ω_{Y/X}` with the dual of
`π_*𝒪_Y`, and `Tr_π` is evaluation at `1`, which is
`AlgebraicGeometry.Space.dualizingTrace`. -/
def relativeDualizingTrace (π : Y ⟶ X) (hπ : IsAffineHom B S hS π.hom)
    (hfp : (pushforwardStructureModule B S hS π).IsFinitePresentationOnSite) :
    (modulePushforward B S hS π).obj (relativeDualizingModule B S hS π) ⟶
      SheafOfModules.unit
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) :=
  (modulePushforward_relativeDualizingModuleIso B S hS π hπ hfp).hom ≫
    dualizingTrace B S hS π

end General

/-! ### The maps `σ` of Stacks 0GUZ -/

section Situation

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (hZ : B.Contains (⊤_ Scheme.{u}))

attribute [local instance] pointTopology

variable (X : AlgebraicSpaces B S hS) (hqc : IsQuasiCompactSpace B S hS X.1)
    (hqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (D : ResolutionPropertyDescentSituation B S hS hZ X hqc hqs)

/-- **The maps `σ : π_*(ℐ^n) ⟶ ℱ` of [Stacks, Tag 0GUZ].**

In the situation of [Stacks, Tag 0GUY] with `X` Noetherian, a morphism `ℐ^n ⟶ π^!ℱ` of
`𝒪_Y`-modules into the right adjoint of `π_*` at a quasi-coherent `ℱ` is the same datum as a
morphism `π_*(ℐ^n) ⟶ ℱ` of `𝒪_X`-modules, by
`AlgebraicGeometry.Space.homEquivAffinePushforwardRightAdjoint`: the power `ℐ^n` is coherent,
hence quasi-coherent, by
`AlgebraicGeometry.Space.isCoherent_idealSheafPow_of_resolutionSituation`, and the finite
morphism `π` is affine.

These are the maps whose direct sum [Stacks, Tag 0GUZ] asserts to be surjective; the
surjectivity is `AlgebraicGeometry.Space.exists_epi_biproduct_idealSheafPowPushforward`. -/
def resolutionSituationSigma (hX : IsNoetherian B S hS hZ X.1)
    (hfp : (pushforwardStructureModule B S hS
      (D.piHom B S hS hZ X hqc hqs)).IsFinitePresentationOnSite)
    (F : Modules.{u, u} B S hS X.1 X.2) (hF : F.IsQuasicoherentOnSite) (n : ℕ)
    (s : (SheafOfModules.idealSheafPow D.I n).toSheafOfModules ⟶
      (affinePushforwardRightAdjoint B S hS (D.piHom B S hS hZ X hqc hqs)).obj F) :
    idealSheafPowPushforward B S hS (D.piHom B S hS hZ X hqc hqs) D.I n ⟶ F :=
  homEquivAffinePushforwardRightAdjoint B S hS (D.piHom B S hS hZ X hqc hqs)
    D.isFinite_π.isAffineHom hfp F hF
    (SheafOfModules.idealSheafPow D.I n).toSheafOfModules
    (isCoherent_idealSheafPow_of_resolutionSituation B S hS hZ X hqc hqs D hX
      n).toIsQuasicoherentOnSite s

end Situation

end AlgebraicGeometry.Space

end
