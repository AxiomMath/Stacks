module

public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange

/-!
# Finiteness of the sections of a finite-type quasi-coherent module on an affine open

This file proves [Stacks, Tag 01PB]: for a quasi-coherent `𝒪_X`-module `F` of finite type on a
scheme `X` and an **arbitrary** affine open `U` of `X`, the sections `Γ(F, U)` form a finite
`Γ(X, U)`-module. Equivalently — and this is the form in which it is consumed —
`Stacks.AlgebraicGeometry.CoherentTFAE.specModule F hU` is a finite `Γ(X, U)`-module, which is
exactly the hypothesis of
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_finite_specModule`. So this file
supplies the implication (2) ⇒ (4) of [Stacks, Tag 01XZ].

The difficulty the statement hides is that finite type only provides finitely many generating
sections on the members of *some* open covering, which has nothing to do with `U`; the content of
the tag is the upgrade of that to every affine open.

## The route

1. **Off the slice site.** `SheafOfModules.IsFiniteType` hands out generating sections of
   `F.over V` for `V` in a covering, i.e. sections of a sheaf of modules on the slice site over
   `V`. `generatingSectionsOfOver` carries them to generating sections of `F.restrict V.ι` on the
   open subscheme `V`, with the same index type, along `Scheme.Modules.overFunctorEquiv`.
   This is the inverse direction of
   `Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsOver`.

2. **Shrinking the open.** `generatingSectionsRestrictLE` restricts generating sections from `V`
   to any smaller open `W ≤ V`, along `AlgebraicGeometry.Scheme.homOfLE`. Together with
   `IsAffineOpen.exists_basicOpen_le` this produces, around any point of `U`, a *basic* open
   `X.basicOpen g` with `g : Γ(X, U)` on which `F` has finitely many generating sections.

3. **Sections of a quasi-coherent module on an affine open.** `specSectionsEquiv` is the
   `Γ(X, U)`-linear equivalence `specModule F hU ≃ₗ Γ(F, U)`. With it,
   `Stacks.AlgebraicGeometry.CoherentTFAE.finite_specModule_of_generatingSections` becomes
   `finite_sections_of_generatingSections`: finitely many generating sections of `F|_W` make
   `Γ(F, W)` a finite `Γ(X, W)`-module, for `W` affine.

4. **Local-to-global.** The elements `g : Γ(X, U)` for which `Γ(F, X.basicOpen g)` is a finite
   `Γ(X, X.basicOpen g)`-module generate the unit ideal, by step 2 and
   `IsAffineOpen.self_le_iSup_basicOpen_iff`. Feeding that set to
   `Module.Finite.of_localizationSpan'`, with
   `Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ` as the
   localization data, gives `Module.Finite Γ(X, U) Γ(F, U)`.

No Noetherian hypothesis is used anywhere: [Stacks, Tag 01PB] holds on an arbitrary scheme.

## Main results

* `Stacks.AlgebraicGeometry.CoherentFinite.finite_sections`: [Stacks, Tag 01PB] as stated in the
  source — `Γ(F, U)` is a finite `Γ(X, U)`-module.
* `Stacks.AlgebraicGeometry.CoherentFinite.finite_specModule`: the same, read through
  `U ≅ Spec Γ(X, U)`.
* `Stacks.AlgebraicGeometry.CoherentFinite.exists_finite_generatingSections_restrict`: the form
  in which the source cites the tag — `F` is generated on `U` by finitely many sections.
* `Stacks.AlgebraicGeometry.CoherentFinite.isFiniteTildeOn` and
  `Stacks.AlgebraicGeometry.CoherentFinite.forall_isFiniteTildeOn_of_isQuasicoherent_isFiniteType`:
  the implication (2) ⇒ (4) of [Stacks, Tag 01XZ].

## Implementation notes

**Transparency.** `AlgebraicGeometry.Scheme.Modules` is a `def` for `SheafOfModules _`, so
instances about functors between these categories are not found at the transparency instance
synthesis uses. Checked here rather than assumed: `PreservesColimitsOfSize` for
`(Scheme.Modules.overEquiv V).functor` is **not** synthesized — the plain application
`SheafOfModules.GeneratingSections.map σ (Scheme.Modules.overEquiv V).functor _` fails with
`failed to synthesize PreservesColimitsOfSize ...` — so `generatingSectionsOfOver` passes it
positionally, with the thirteen leading implicits of
`SheafOfModules.GeneratingSections.map` spelled as `_`, in the style of
`Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsRestrict`. No option is set and no
transparency attribute is used.

Also checked: the `Scheme.Modules.restrictFunctorCongr` step one might expect in
`specRestrictIso` is unnecessary. `AlgebraicGeometry.IsAffineOpen.fromSpec` is by definition
`hU.isoSpec.inv ≫ U.ι` (`IsAffineOpen.isoSpec_inv_ι` is `rfl`), and
`(Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app F` elaborates directly at the type
`F.restrict hU.fromSpec ≅ specRestrict F hU`.

**Scalar structures.** The two `Γ(X, U)`-module structures that have to be reconciled are the
one on `specModule F hU`, which `AlgebraicGeometry.moduleSpecΓFunctor` builds by restricting
scalars along `(Scheme.ΓSpecIso Γ(X, U)).inv`, and the one on `Γ(F, U)` coming from the sheaf of
modules. `specSectionsEquiv` reconciles them by composing the image of `specRestrictIso` under
`moduleSpecΓFunctor` — which is where the restriction of scalars is handled, and the reason the
sheaf-level isomorphism is pushed through that functor rather than evaluated at `⊤` by hand —
with
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictSectionsEquiv` and
`Stacks.AlgebraicGeometry.QuasicoherentBaseChange.sectionsCongrSelf`. No `change` or `show` is
needed: `moduleSpecΓFunctor.obj N` and `Γ(N, ⊤)` share their carrier and their `Module`
instance definitionally, the latter being `inferInstanceAs` of the former.

For `U ≤ V` the ring `Γ(X, U)` is not a `Γ(X, V)`-algebra by instance search, so the data fed to
`Module.Finite.of_localizationSpan'` is supplied by the `let`s in the proof of `finite_sections`,
out of `QuasicoherentBaseChange.algebraOfLE`, `moduleOfLE`, `isScalarTowerOfLE` and
`isLocalizedModule_restrictₗ`.

## What is not done here

Nothing about *coherence* is proved. [Stacks, Tag 01XZ] also needs the implications whose
conclusion is its condition (1), `SheafOfModules.IsCoherent` — these are the ones that use the
locally Noetherian hypothesis, and they are not in this file. Nor are the consequences the source
draws from the equivalence (coherence of the structure sheaf, of invertible modules, and of
finite locally free modules).

The literal statement of [Stacks, Tag 01PB] is the affine equivalence
`(tilde M).IsFiniteType ↔ Module.Finite R M` on `Spec R`, and that biconditional is not stated
here: only the scheme-level form the equivalence of [Stacks, Tag 01XZ] consumes. Its backward
direction is `Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_tilde`; its forward direction is
`finite_sections` at `U = ⊤`, followed by a transport of both the ring and the module along
`AlgebraicGeometry.Scheme.ΓSpecIso` and `AlgebraicGeometry.tilde.toTildeΓNatIso`, which is the
only piece of bookkeeping separating the two forms.

## References

* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public section

open CategoryTheory Limits SheafOfModules TopologicalSpace
open AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.CoherentFinite

open Stacks.AlgebraicGeometry.CoherentTFAE
open Stacks.AlgebraicGeometry.QuasicoherentBaseChange

variable {X : Scheme.{u}}

/-! ### Generating sections off the slice site -/

/-- **The equivalence `Scheme.Modules.overEquiv` carries the structure sheaf to the structure
sheaf**, in the direction needed to transport generating sections out of the slice site. This is
the counterpart of `Stacks.AlgebraicGeometry.AffinePushforward.overInverseUnitIso` for the
functor rather than the inverse. -/
noncomputable def overFunctorUnitIso (V : X.Opens) :
    SheafOfModules.unit.{u} V.toScheme.ringCatSheaf ≅
      (Scheme.Modules.overEquiv V).functor.obj
        (SheafOfModules.unit.{u} (Sheaf.over X.ringCatSheaf V)) :=
  (Scheme.Modules.restrictUnitIso V.ι).symm ≪≫
    ((Scheme.Modules.overFunctorEquiv V).app (SheafOfModules.unit.{u} X.ringCatSheaf)).symm

/-- **Generating sections of `M.over V` give generating sections of `M.restrict V.ι`**, with the
same index type. This is the direction opposite to
`Stacks.AlgebraicGeometry.CoherentTFAE.generatingSectionsOver`, and is what turns the output of
`SheafOfModules.IsFiniteType` — which lives on the slice site over a member of a covering — into
sections of a module on an open subscheme. -/
noncomputable def generatingSectionsOfOver (V : X.Opens) (M : X.Modules)
    (σ : (M.over V).GeneratingSections) : (M.restrict V.ι).GeneratingSections :=
  GeneratingSections.equivOfIso ((Scheme.Modules.overFunctorEquiv V).app M)
    (@GeneratingSections.map _ _ _ _ _ _ _ _ _ _ _ _ _ σ
      (Scheme.Modules.overEquiv V).functor
      (inferInstance : PreservesColimitsOfSize.{u, u} (Scheme.Modules.overEquiv V).functor)
      (overFunctorUnitIso V))

/-- The generating sections `generatingSectionsOfOver V M σ` have the same index type as `σ`. -/
@[simp]
theorem generatingSectionsOfOver_I (V : X.Opens) (M : X.Modules)
    (σ : (M.over V).GeneratingSections) : (generatingSectionsOfOver V M σ).I = σ.I :=
  rfl

/-! ### Restriction of generating sections to a smaller open -/

/-- Restricting `M` to `W` is restricting it to `V` and then to `W`, for `W ≤ V`. -/
noncomputable def restrictLEIso (M : X.Modules) {W V : X.Opens} (h : W ≤ V) :
    M.restrict W.ι ≅ (M.restrict V.ι).restrict (X.homOfLE h) :=
  ((Scheme.Modules.restrictFunctorCongr (X.homOfLE_ι h)).app M).symm ≪≫
    (Scheme.Modules.restrictFunctorComp (X.homOfLE h) V.ι).app M

/-- **Generating sections restrict to a smaller open**, with the same index type. -/
noncomputable def generatingSectionsRestrictLE (M : X.Modules) {W V : X.Opens} (h : W ≤ V)
    (σ : (M.restrict V.ι).GeneratingSections) : (M.restrict W.ι).GeneratingSections :=
  (GeneratingSections.equivOfIso (restrictLEIso M h)).symm
    (generatingSectionsRestrict (X.homOfLE h) σ)

/-- The generating sections `generatingSectionsRestrictLE M h σ` have the same index type as
`σ`. -/
@[simp]
theorem generatingSectionsRestrictLE_I (M : X.Modules) {W V : X.Opens} (h : W ≤ V)
    (σ : (M.restrict V.ι).GeneratingSections) :
    (generatingSectionsRestrictLE M h σ).I = σ.I :=
  rfl

/-! ### What finite type gives at a point -/

/-- **A module of finite type has finitely many generating sections near every point**, on an
open subscheme rather than on a slice site. -/
theorem exists_generatingSections_of_isFiniteType (M : X.Modules) [M.IsFiniteType] (x : X) :
    ∃ (V : X.Opens) (_ : x ∈ V) (σ : (M.restrict V.ι).GeneratingSections), Finite σ.I := by
  obtain ⟨d, hd⟩ := SheafOfModules.IsFiniteType.exists_localGeneratorsData M
  have hcov : IsOpenCover d.X := (Opens.coversTop_iff _ d.X).mp d.coversTop
  obtain ⟨i, hi⟩ : ∃ i, x ∈ d.X i := by
    have hx : x ∈ (⨆ i, d.X i) := by rw [hcov]; trivial
    exact Opens.mem_iSup.mp hx
  have hfin : Finite (d.generators i).I := (hd.isFiniteType i).finite
  exact ⟨d.X i, hi, generatingSectionsOfOver (d.X i) M (d.generators i), hfin⟩

/-! ### The sections over an affine open as a module -/

/-- The restriction of `F` along `Spec Γ(X, U) ⟶ X` is the restriction to `U` read on the
spectrum. -/
noncomputable def specRestrictIso (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    F.restrict hU.fromSpec ≅ specRestrict F hU :=
  (Scheme.Modules.restrictFunctorComp hU.isoSpec.inv U.ι).app F

/-- **The `Γ(X, U)`-module `specModule F hU` is the module of sections `Γ(F, U)`.** This is the
identification of the two scalar structures described in the implementation notes; it holds for
an arbitrary module `F`, quasi-coherent or not. -/
noncomputable def specSectionsEquiv (F : X.Modules) {U : X.Opens} (hU : IsAffineOpen U) :
    specModule F hU ≃ₗ[Γ(X, U)] Γ(F, U) :=
  have hTop : hU.fromSpec ''ᵁ (⊤ : (Spec Γ(X, U)).Opens) = U :=
    (Scheme.Hom.image_top_eq_opensRange _).trans hU.opensRange_fromSpec
  (moduleSpecΓFunctor.mapIso (specRestrictIso F hU).symm).toLinearEquiv.trans
    ((restrictSectionsEquiv F hU ⊤).trans
      (sectionsCongrSelf F hTop (fromSpec_image_le hU ⊤)))

/-- **Finitely many generating sections of `F|_V` make `Γ(F, V)` a finite module**, for `V` an
affine open and `F` quasi-coherent. -/
theorem finite_sections_of_generatingSections (F : X.Modules) [F.IsQuasicoherent] {V : X.Opens}
    (hV : IsAffineOpen V) (σ : (F.restrict V.ι).GeneratingSections) [Finite σ.I] :
    Module.Finite Γ(X, V) Γ(F, V) :=
  have := finite_specModule_of_generatingSections F hV σ
  Module.Finite.equiv (specSectionsEquiv F hV)

/-! ### Stacks 01PB -/

/-- **[Stacks, Tag 01PB].** For a quasi-coherent module of finite type on a scheme and an
arbitrary affine open `U`, the sections over `U` form a finite `Γ(X, U)`-module.

Finite type only provides generating sections on the members of some covering of `X`, so the
proof covers `U` by basic opens `X.basicOpen g`, `g : Γ(X, U)`, small enough to sit inside a
member of that covering; on each of those `F` has finitely many generating sections, hence finite
sections by `finite_sections_of_generatingSections`, and `Γ(F, X.basicOpen g)` is the
localization of `Γ(F, U)` away from `g`. Finiteness of modules is local on the base. -/
theorem finite_sections (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] {U : X.Opens}
    (hU : IsAffineOpen U) : Module.Finite Γ(X, U) Γ(F, U) := by
  set t : Set Γ(X, U) := {g | Module.Finite Γ(X, X.basicOpen g) Γ(F, X.basicOpen g)}
  have hspan : Ideal.span t = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    obtain ⟨V, hxV, σ, hσ⟩ := exists_generatingSections_of_isFiniteType F x
    obtain ⟨g, hgV, hxg⟩ := hU.exists_basicOpen_le (⟨x, hxV⟩ : V) hx
    have hfin : Finite (generatingSectionsRestrictLE F hgV σ).I := hσ
    have hg : Module.Finite Γ(X, X.basicOpen g) Γ(F, X.basicOpen g) :=
      @finite_sections_of_generatingSections _ F _ _ (hU.basicOpen g)
        (generatingSectionsRestrictLE F hgV σ) hfin
    exact Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hxg⟩
  let _ : ∀ g : t, Algebra Γ(X, U) Γ(X, X.basicOpen (g : Γ(X, U))) :=
    fun g => algebraOfLE X (X.basicOpen_le (g : Γ(X, U)))
  let _ : ∀ g : t, IsLocalization.Away (g : Γ(X, U)) Γ(X, X.basicOpen (g : Γ(X, U))) :=
    fun _ => hU.isLocalization_basicOpen _
  let _ : ∀ g : t, Module Γ(X, U) Γ(F, X.basicOpen (g : Γ(X, U))) :=
    fun g => moduleOfLE F (X.basicOpen_le (g : Γ(X, U)))
  let _ : ∀ g : t, IsScalarTower Γ(X, U) Γ(X, X.basicOpen (g : Γ(X, U)))
      Γ(F, X.basicOpen (g : Γ(X, U))) :=
    fun g => isScalarTowerOfLE F (X.basicOpen_le (g : Γ(X, U)))
  let _ : ∀ g : t, IsLocalizedModule.Away (g : Γ(X, U))
      (restrictₗ F (X.basicOpen_le (g : Γ(X, U)))) :=
    fun _ => isLocalizedModule_restrictₗ F hU _ rfl _
  exact Module.Finite.of_localizationSpan' t hspan
    (fun g => restrictₗ F (X.basicOpen_le (g : Γ(X, U)))) (fun g => g.2)

/-- **[Stacks, Tag 01PB], read on the spectrum.** This is the hypothesis of
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteTildeOn_of_finite_specModule`. -/
theorem finite_specModule (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] {U : X.Opens}
    (hU : IsAffineOpen U) : Module.Finite Γ(X, U) (specModule F hU) :=
  have := finite_sections F hU
  Module.Finite.equiv (specSectionsEquiv F hU).symm

/-- **A quasi-coherent module of finite type is generated by finitely many sections on every
affine open.** This is the form in which the source cites [Stacks, Tag 01PB]. -/
theorem exists_finite_generatingSections_restrict (F : X.Modules) [F.IsQuasicoherent]
    [F.IsFiniteType] {U : X.Opens} (hU : IsAffineOpen U) :
    ∃ σ : (F.restrict U.ι).GeneratingSections, Finite σ.I := by
  obtain ⟨τ, hτ⟩ :=
    @exists_finite_generatingSections_tilde _ (specModule F hU) (finite_specModule F hU)
  exact ⟨GeneratingSections.equivOfIso (restrictIsoSpecTilde F hU).symm
    (generatingSectionsPullbackTilde hU.isoSpec.hom (specModule F hU) τ), hτ⟩

/-! ### (2) ⇒ (4) of Stacks 01XZ -/

/-- **Condition (4) of [Stacks, Tag 01XZ] holds at every affine open** for a quasi-coherent
module of finite type. -/
theorem isFiniteTildeOn (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (U : X.Opens)
    (hU : IsAffineOpen U) : IsFiniteTildeOn F U hU :=
  isFiniteTildeOn_of_finite_specModule F U hU (finite_specModule F hU)

/-- **(2) ⇒ (4) of [Stacks, Tag 01XZ].** -/
theorem forall_isFiniteTildeOn_of_isQuasicoherent_isFiniteType (F : X.Modules)
    (h : F.IsQuasicoherent ∧ F.IsFiniteType) :
    ∀ (U : X.Opens) (hU : IsAffineOpen U), IsFiniteTildeOn F U hU :=
  fun U hU => @isFiniteTildeOn _ F h.1 h.2 U hU

end Stacks.AlgebraicGeometry.CoherentFinite

end
