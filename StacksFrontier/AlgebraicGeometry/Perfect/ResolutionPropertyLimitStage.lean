module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.FiniteLocallyFreeUnconditional
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MorphismDescentGlue
public import StacksFrontier.AlgebraicGeometry.Perfect.ResolutionPropertyIdealCovering

/-!
# Descending a resolution from a limit of schemes to a stage

Let `D` be a cofiltered diagram of quasi-compact, quasi-separated schemes with affine transition
morphisms and let `c` be a limit cone on it.  The substantial direction of [Stacks, Tag 0F8B]
asserts that if the limit `c.pt` has the resolution property then some stage `D.obj i` does.  Its
proof fixes a stage `i`, a finite affine open covering of `D.obj i` and finite type quasi-coherent
ideals cutting out the complements ([Stacks, Tag 01PH]), resolves the pullbacks of those ideals on
`c.pt` by the resolution property there, and **descends those resolutions to a stage**, where
[Stacks, Tag 0F89] then applies.

This file carries out the descent step, unconditionally.  Given a finite type quasi-coherent
module `A` on a stage `D.obj i` together with a morphism `α : A ⟶ 𝒪_{D.obj i}`, the pullback of
`A` to `c.pt` is of finite type and quasi-coherent, so the resolution property of `c.pt` resolves
it; [Stacks, Tag 0B8W] (1) descends the resolving finite locally free module to a stage and
[Stacks, Tag 01ZR] (3) descends the composite morphism to `𝒪`.  What comes out is a stage `l`
over `i`, a finite locally free `𝒪_{D.obj l}`-module `E` and a morphism `θ : E ⟶ 𝒪_{D.obj l}`
whose pullback to the limit is an epimorphism onto the pullback of `A` followed by the pullback of
`α`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_map_hom`: the composition rule for
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso` solved for the inner leg, which is the form
  in which the descent below uses the coherence
  `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq`.
* `AlgebraicGeometry.exists_stage_isFiniteLocallyFree_hom_pt_of_isLimit`: the descent step for a
  finite locally free module on the *limit* carrying a morphism to the structure sheaf, which is
  the shape the substantial direction of [Stacks, Tag 0F89] descends.
* `AlgebraicGeometry.exists_stage_isFiniteLocallyFree_hom_of_isLimit`: the descent step, for a
  finite type quasi-coherent module with a morphism to the structure sheaf.
* `AlgebraicGeometry.exists_stage_isFiniteLocallyFree_hom_idealSheafData_of_isLimit`: the same for
  a finite type quasi-coherent sheaf of ideals, which is the shape in which the proof of
  [Stacks, Tag 0F8B] uses it.

## Implementation notes

**Why the conclusion carries the epimorphism and the equation.**  Without them the statement would
be satisfied by `E = 0` and `θ = 0`; the content is that the pullback of `θ` to the limit *is* a
resolution of the pullback of `α`.  The equation is stated with the comparison isomorphisms in the
shape the two descent theorems produce them, rather than in a tidier one obtained by transport:
both sides' types are then already in the environment.

**What this is used for.**

Steps (1), (2) and (3) below are all **done**.  Together with this file they prove the
substantial direction of the tag at Noetherian stages —
`AlgebraicGeometry.exists_hasResolutionProperty_of_isLimit` in
`StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyLimitStageNoetherian.lean` — and, at
the quasi-compact quasi-separated stages the tag states,
`AlgebraicGeometry.exists_hasResolutionProperty_of_isLimit_of_quasiSeparated` in
`StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyLimitStageQcqs.lean`.

(1) *The vanishing locus of the image of a descended morphism is the one it was built to cut
out.*  Rather than making two finitely presented quotients agree at a stage, this is done at the
level of vanishing loci: `AlgebraicGeometry.coe_support_idealSheafDataOfHom_of_epi` removes the
epimorphism `ε` above, `AlgebraicGeometry.coe_support_idealSheafDataOfHom_pullback` commutes the
vanishing locus with both pullbacks, and [Stacks, Tag 01Z4] (2),
`AlgebraicGeometry.exists_map_preimage_eq_map_preimage`, makes the resulting equality of
quasi-compact opens on the limit an equality at a stage.

(2) *The vanishing locus of a pulled-back ideal.*
`AlgebraicGeometry.coe_support_idealSheafDataOfHom_pullback` of
`StacksFrontier/AlgebraicGeometry/Properties/ExtendFiniteType/ImageIdealPullback.lean`:

```lean
theorem coe_support_idealSheafDataOfHom_pullback {X' X : Scheme.{u}} (f : X' ⟶ X)
    (A : X.Modules) [A.IsQuasicoherent] (φ : A ⟶ structureModule X) :
    (((idealSheafDataOfHom ((Scheme.Modules.pullback f).obj A)
        ((Scheme.Modules.pullback f).map φ ≫
          (Scheme.Modules.pullbackUnitIso f).hom)).support : Set X'))
      = f.base ⁻¹' ((idealSheafDataOfHom A φ).support : Set X)
```

It needs no finiteness hypothesis on `A` and no hypothesis on `f`, and it needs neither
`AlgebraicGeometry.Scheme.IdealSheafData.comap` nor Mathlib's `support_comap`: the inclusion `⊆`
is `AlgebraicGeometry.notMem_support_idealSheafDataOfHom_of_mem_basicOpen` applied to a
pulled-back section, and `⊇` is the unconditional
`AlgebraicGeometry.span_pullbackSection_eq_top` — over an affine pair the sections whose value
vanishes at a point form a submodule containing every pulled-back section, hence everything.

(3) *The substantial direction of [Stacks, Tag 0F89]*, in its full quasi-compact quasi-separated
generality.

```lean
theorem hasResolutionProperty_of_isIdealAffineCovering {X : Scheme.{u}} {m : ℕ}
    {U : Fin m → X.Opens} {I : Fin m → X.IdealSheafData} (h : IsIdealAffineCovering X U I)
    (E : Fin m → X.Modules)
    (hE : ∀ j, SheafOfModules.IsFiniteLocallyFree (R := X.ringCatSheaf) (E j))
    (q : ∀ j, E j ⟶ idealPow (I j) 1) (hq : ∀ j, Epi (q j)) :
    HasResolutionProperty X
```

It is in
`StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyIdealCoveringSubstantial.lean`; the
Noetherian form is
`AlgebraicGeometry.hasResolutionProperty_of_isNoetherian_of_coe_support_idealSheafDataOfHom`.
Assembled, these give [Stacks, Tag 0F8B] as
`AlgebraicGeometry.hasResolutionProperty_iff_exists_of_isLimit` in
`StacksFrontier/AlgebraicGeometry/Perfect/ResolutionPropertyLimitStageQcqs.lean`.

## References

* [Stacks Project, Tag 0F8B](https://stacks.math.columbia.edu/tag/0F8B)
* [Stacks Project, Tag 0F89](https://stacks.math.columbia.edu/tag/0F89)
* [Stacks Project, Tag 0B8W](https://stacks.math.columbia.edu/tag/0B8W)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ModuleLimits
open Stacks.AlgebraicGeometry.IdealPowerColimit

universe v u

namespace AlgebraicGeometry

/-- The coherence `AlgebraicGeometry.Scheme.Modules.pullbackUnitIso_comp_eq` solved for the inner
leg: pulling the identification of the structure sheaf of `Z` with the pullback of the structure
sheaf of `Y` back along `f` and then identifying again is the identification along a composite
`h = f ≫ g`, read through the comparison isomorphisms of the pullback functors. -/
theorem Scheme.Modules.pullbackUnitIso_map_hom {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (h : X ⟶ Z) (w : f ≫ g = h) :
    (Scheme.Modules.pullback f).map (Scheme.Modules.pullbackUnitIso g).hom ≫
        (Scheme.Modules.pullbackUnitIso f).hom =
      (Scheme.Modules.pullbackComp f g).hom.app Z.unitModule ≫
        (Scheme.Modules.pullbackCongr w).hom.app Z.unitModule ≫
          (Scheme.Modules.pullbackUnitIso h).hom := by
  rw [← Scheme.Modules.pullbackUnitIso_comp_eq f g h w]
  simp

section

variable {I : Type u} [Category.{v} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (g : i ⟶ j), IsAffineHom (D.map g)] (c : Cone D)
  [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

include c in
/-- **The descent step, for a finite locally free module on the limit.**  Let `c` be a limit
cone over a cofiltered diagram `D` of quasi-compact, quasi-separated schemes with affine
transition morphisms.  Let `E₀` be a finite locally free module on the limit `c.pt` and
`α : E₀ ⟶ 𝒪_{c.pt}` a morphism to the structure sheaf.

Then there are a stage `l` over a prescribed stage `i`, a finite locally free
`𝒪_{D.obj l}`-module `E` and a morphism `θ : E ⟶ 𝒪_{D.obj l}` together with an isomorphism `κ`
identifying the pullback of `E` to the limit with `E₀` and carrying the pullback of `θ` to `α`.

[Stacks, Tag 0B8W] (1) descends `E₀` to a stage and [Stacks, Tag 01ZR] (3) descends `α` read
through that identification.  This is the form in which the substantial direction of
[Stacks, Tag 0F89] uses the descent: there the resolutions are given on the limit, not produced
from the resolution property of the limit. -/
theorem exists_stage_isFiniteLocallyFree_hom_pt_of_isLimit (hc : IsLimit c) (i : I)
    (E₀ : c.pt.Modules)
    (hE₀ : SheafOfModules.IsFiniteLocallyFree (R := c.pt.ringCatSheaf) E₀)
    (α : E₀ ⟶ c.pt.unitModule) :
    ∃ (l : I) (_ : l ⟶ i) (E : (D.obj l).Modules),
      SheafOfModules.IsFiniteLocallyFree (R := (D.obj l).ringCatSheaf) E ∧
      ∃ (θ : E ⟶ (D.obj l).unitModule)
        (κ : (Scheme.Modules.pullback (c.π.app l)).obj E ≅ E₀),
          (Scheme.Modules.pullback (c.π.app l)).map θ ≫
              (Scheme.Modules.pullbackUnitIso (c.π.app l)).hom = κ.hom ≫ α := by
  classical
  -- Tag 0B8W (1): the module comes from a stage.
  obtain ⟨i₁, E₁, hE₁, ⟨κ⟩⟩ := exists_isFiniteLocallyFree_pullback_iso D c hc E₀ hE₀
  -- Move to a stage below both `i₁` and `i`, so that the conclusion can be over `i`.
  let m := IsCofiltered.min i₁ i
  let a : m ⟶ i₁ := IsCofiltered.minToLeft i₁ i
  let b : m ⟶ i := IsCofiltered.minToRight i₁ i
  let E₁' := (Scheme.Modules.pullback (D.map a)).obj E₁
  have hE₁' : SheafOfModules.IsFiniteLocallyFree (R := (D.obj m).ringCatSheaf) E₁' :=
    SheafOfModules.IsFiniteLocallyFree.pullback_scheme (D.map a) E₁ hE₁
  let tr : (Scheme.Modules.pullback (c.π.app m)).obj E₁' ≅
      (Scheme.Modules.pullback (c.π.app i₁)).obj E₁ :=
    (Scheme.Modules.pullbackComp (c.π.app m) (D.map a)).app E₁ ≪≫
      (Scheme.Modules.pullbackCongr (c.w a)).app E₁
  -- The morphism to the structure sheaf, read between pullbacks of modules on the stage `m`.
  let φ : (Scheme.Modules.pullback (c.π.app m)).obj E₁' ⟶
      (Scheme.Modules.pullback (c.π.app m)).obj (D.obj m).unitModule :=
    tr.hom ≫ κ.inv ≫ α ≫ (Scheme.Modules.pullbackUnitIso (c.π.app m)).inv
  have hE₁'fp : E₁'.IsFinitePresentation :=
    SheafOfModules.IsFiniteLocallyFree.isFinitePresentation E₁' hE₁'
  have hunitfp : ((D.obj m).unitModule).IsFinitePresentation := isFinitePresentation_unit (D.obj m)
  -- Tag 01ZR (3): that morphism comes from a stage over `m`.
  obtain ⟨l, e, φl, hφl⟩ :=
    exists_map_of_pullback_of_isLimit D c hc m E₁' (D.obj m).unitModule φ
  refine ⟨l, e ≫ b, (Scheme.Modules.pullback (D.map e)).obj E₁',
    SheafOfModules.IsFiniteLocallyFree.pullback_scheme (D.map e) E₁' hE₁',
    φl ≫ (Scheme.Modules.pullbackUnitIso (D.map e)).hom,
    (Scheme.Modules.pullbackComp (c.π.app l) (D.map e)).app E₁' ≪≫
      (Scheme.Modules.pullbackCongr (c.w e)).app E₁' ≪≫ tr ≪≫ κ.symm, ?_⟩
  rw [Functor.map_comp, Category.assoc,
    Scheme.Modules.pullbackUnitIso_map_hom (c.π.app l) (D.map e) (c.π.app m) (c.w e),
    reassoc_of% hφl]
  simp only [φ, Iso.trans_hom, Iso.symm_hom, Iso.app_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

include c in
/-- **The descent step of the substantial direction of [Stacks, Tag 0F8B].**  Let `c` be a limit
cone over a cofiltered diagram `D` of quasi-compact, quasi-separated schemes with affine
transition morphisms, and suppose the limit `c.pt` has the resolution property.  Let `A` be a
finite type quasi-coherent module on a stage `D.obj i` and `α : A ⟶ 𝒪_{D.obj i}`.

Then there are a stage `l` over `i`, a finite locally free `𝒪_{D.obj l}`-module `E` and a
morphism `θ : E ⟶ 𝒪_{D.obj l}` whose pullback to `c.pt` is an epimorphism onto the pullback of
`A` followed by the pullback of `α`.

The resolution property of `c.pt` resolves the pullback of `A`, which is again of finite type and
quasi-coherent, and `exists_stage_isFiniteLocallyFree_hom_pt_of_isLimit` descends the resolving
module together with its composite to the structure sheaf. -/
theorem exists_stage_isFiniteLocallyFree_hom_of_isLimit (hc : IsLimit c)
    [HasResolutionProperty c.pt] (i : I) (A : (D.obj i).Modules)
    [A.IsQuasicoherent] [A.IsFiniteType] (α : A ⟶ (D.obj i).unitModule) :
    ∃ (l : I) (_ : l ⟶ i) (E : (D.obj l).Modules),
      SheafOfModules.IsFiniteLocallyFree (R := (D.obj l).ringCatSheaf) E ∧
      ∃ (θ : E ⟶ (D.obj l).unitModule)
        (ε : (Scheme.Modules.pullback (c.π.app l)).obj E ⟶
            (Scheme.Modules.pullback (c.π.app i)).obj A),
        Epi ε ∧
          (Scheme.Modules.pullback (c.π.app l)).map θ ≫
              (Scheme.Modules.pullbackUnitIso (c.π.app l)).hom =
            ε ≫ (Scheme.Modules.pullback (c.π.app i)).map α ≫
              (Scheme.Modules.pullbackUnitIso (c.π.app i)).hom := by
  classical
  have hqc : ((Scheme.Modules.pullback (c.π.app i)).obj A).IsQuasicoherent :=
    @SheafOfModules.modulePullback_isQuasicoherent _ _ (c.π.app i).toLRSHom.toShHom A
      (show A.IsQuasicoherent from inferInstance)
  have hft : ((Scheme.Modules.pullback (c.π.app i)).obj A).IsFiniteType :=
    SheafOfModules.pullback_isFiniteType (c.π.app i).toLRSHom.toShHom A
  -- A finite locally free resolution of the pullback of `A` on the limit.
  obtain ⟨E₀, hE₀, q, hq⟩ := HasResolutionProperty.exists_finiteLocallyFree_quotient
    (X := c.pt) ((Scheme.Modules.pullback (c.π.app i)).obj A)
  obtain ⟨l, e, E, hE, θ, κ, hκ⟩ :=
    exists_stage_isFiniteLocallyFree_hom_pt_of_isLimit D c hc i E₀ hE₀
      (q ≫ (Scheme.Modules.pullback (c.π.app i)).map α ≫
        (Scheme.Modules.pullbackUnitIso (c.π.app i)).hom)
  have _ : Epi q := hq
  exact ⟨l, e, E, hE, θ, κ.hom ≫ q, inferInstance, by rw [hκ, Category.assoc]⟩

include c in
/-- **The descent step of the substantial direction of [Stacks, Tag 0F8B], for a sheaf of
ideals.**  `AlgebraicGeometry.exists_stage_isFiniteLocallyFree_hom_of_isLimit` applied to a finite
type quasi-coherent sheaf of ideals `J` on a stage, read as the module
`Stacks.AlgebraicGeometry.IdealPowerColimit.idealPow J 1` with its inclusion into the structure
sheaf.  This is the shape in which the proof of [Stacks, Tag 0F8B] produces its data: the ideals
there come from [Stacks, Tag 01PH], through
`AlgebraicGeometry.exists_isFiniteType_idealSheafData_support_eq_compl`. -/
theorem exists_stage_isFiniteLocallyFree_hom_idealSheafData_of_isLimit (hc : IsLimit c)
    [HasResolutionProperty c.pt] (i : I) (J : (D.obj i).IdealSheafData)
    (hJ : (idealPow J 1).IsFiniteType) :
    ∃ (l : I) (_ : l ⟶ i) (E : (D.obj l).Modules),
      SheafOfModules.IsFiniteLocallyFree (R := (D.obj l).ringCatSheaf) E ∧
      ∃ (θ : E ⟶ (D.obj l).unitModule)
        (ε : (Scheme.Modules.pullback (c.π.app l)).obj E ⟶
            (Scheme.Modules.pullback (c.π.app i)).obj (idealPow J 1)),
        Epi ε ∧
          (Scheme.Modules.pullback (c.π.app l)).map θ ≫
              (Scheme.Modules.pullbackUnitIso (c.π.app l)).hom =
            ε ≫ (Scheme.Modules.pullback (c.π.app i)).map
                  (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple J 1
                    (structureModule (D.obj i))).ι ≫
              (Scheme.Modules.pullbackUnitIso (c.π.app i)).hom :=
  have := hJ
  exists_stage_isFiniteLocallyFree_hom_of_isLimit D c hc i (idealPow J 1)
    (Stacks.AlgebraicGeometry.IdealPower.idealPowerMultiple J 1
      (structureModule (D.obj i))).ι

end

end AlgebraicGeometry

end
