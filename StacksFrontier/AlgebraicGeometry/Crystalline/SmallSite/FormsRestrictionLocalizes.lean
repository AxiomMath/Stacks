module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorRestrictionAffineChart

/-!
# The restriction of `Ω^i_{X/S}` to an affine ambient scheme localizes on the basic opens

Fix a global crystalline situation `(p, (S, I, γ), X)` and an object `A = (U, T, δ)` of
`Cris(X/S)` with `T` affine, lying over an affine open `V` of the divided power base.  Over
`T.basicOpen g` the sections of the restriction of `Ω^i_{X/S}` are the localization away from `g`
of its sections over `T`:

> `RestrictedLocalizes A (restrictedModule A (crysDifferentialForms S i))`.

This gives the first equality of the proof of [Stacks, Tag 07LF] for affine `T`.

In degree one, `Crystalline.isLocalizedModule_presheafRestrictₗ` localizes the presheaf of divided
power differentials of `T` over the base, and `...comparisonIso` ([Stacks, Tag 07IZ]) identifies
that presheaf with the restriction of `Ω_{X/S}`.  From degree one to degree `i`,
`IsLocalization.isLocalizedModule_of_exteriorPower` says that the `i`-th exterior power of a
localization is a localization of the `i`-th exterior power, and the sections of `Ω^i_{X/S}` are
the exterior power of those of `Ω_{X/S}` on the nose, by `PresheafOfModules.extPowSections`.

## Main results

* `Stacks.AlgebraicGeometry.AffineChartLocalization.isLocalizedModule_presheafRestrictₗ_of_iso` —
  whether a restriction map of a presheaf of modules on a scheme is a localization is invariant
  under an isomorphism of presheaves of modules.
* `IsLocalizedModule.congr_module` — `IsLocalizedModule` transports along an **equality** of the
  module structures on its target.
* `IsLocalization.isLocalizedModule_of_exteriorPower_compHom` —
  `IsLocalization.isLocalizedModule_of_exteriorPower` with the target's base-ring module
  structure presented as a restriction of scalars along `algebraMap`.
* `PresheafOfModules.isLocalizedModule_restrictAlongₗ_extPow` — for a presheaf of modules over any
  presheaf of commutative rings: if the sections of `O` and of `F` along a restriction map both
  localize at a multiplicative set, so do the sections of the sectionwise exterior power
  `PresheafOfModules.extPow n F`.
* `Crystalline.GlobalCrystallineSituation.SmallSite.restrictedLocalizes_crysDifferentials` —
  the degree-one case.
* `Crystalline.GlobalCrystallineSituation.SmallSite.restrictedLocalizes_crysDifferentialForms` —
  the restriction of `Ω^i_{X/S}` to the ambient scheme localizes on the basic opens.
* `Crystalline.GlobalCrystallineSituation.SmallSite.tensorRestrictionLocalizes` — the hypothesis
  of the affine-chart lemma at the coefficient presheaf of [Stacks, Tag 07LF], under hypothesis
  (1) of [Stacks, Tag 07JN] and the two affinenesses.
* `...SmallSite.bijective_toSheafify_app_tensorDifferentialFormsPresheaf_of_isAffine`
  — the first equality of [Stacks, Tag 07LF]: for `T` affine over an affine open of the divided
  power base and `F` locally quasi-coherent, the sections over `A` of the crystalline
  sheafification of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` are the tensor product
  `F(A) ⊗_{Γ(T,𝒪_T)} Ω^i_{X/S}(A)` of the sections of the two factors.

## Implementation notes

The ring of sections is spelled `O.obj X`, not `(O ⋙ forget₂ CommRingCat RingCat).obj X`: the two
are definitionally equal but different terms, and instance search keyed on the second does not see
a local instance stated at the first.  The `⋙ forget₂` spelling is confined to the inside of
`PresheafOfModules.isLocalizedModule_restrictAlongₗ_extPow`.

The `R`-module structure that `IsLocalization.isLocalizedModule_of_exteriorPower` puts on
`⋀ⁿ_{Rₛ}(M')` is the submodule structure for the `R`-algebra `ExteriorAlgebra Rₛ M'`, while a
presheaf of modules supplies a restriction of scalars along `algebraMap R Rₛ`.  The two are equal
by `Module.ext'` but not definitionally, hence `IsLocalizedModule.congr_module`.

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 00DL](https://stacks.math.columbia.edu/tag/00DL)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u uR uM

/-! ### Transport along an isomorphism of presheaves of modules -/

namespace Stacks.AlgebraicGeometry.AffineChartLocalization

attribute [local instance] sectionsModule

variable {X : Scheme.{u}}

/-- **Whether a restriction map of a presheaf of modules on a scheme is a localization is
invariant under an isomorphism of presheaves of modules.**

An isomorphism of presheaves of modules is bijective on the sections over each open, and
compatible with the restriction maps, so the two restriction maps differ by composition with
bijections on both sides. -/
theorem isLocalizedModule_presheafRestrictₗ_of_iso
    {P Q : PresheafOfModules.{u} X.ringCatSheaf.obj} (e : P ≅ Q)
    {U W : X.Opens} (h : U ≤ W) (g : Γ(X, W))
    (hP : letI := presheafModuleOfLE P h
      IsLocalizedModule (Submonoid.powers g) (presheafRestrictₗ P h)) :
    letI := presheafModuleOfLE Q h
    IsLocalizedModule (Submonoid.powers g) (presheafRestrictₗ Q h) := by
  let := presheafModuleOfLE P h
  let := presheafModuleOfLE Q h
  have hbij : ∀ Y : X.Opensᵒᵖ, Function.Bijective
      (ConcreteCategory.hom (PresheafOfModules.Hom.app e.hom Y)) := fun Y ↦
    have : IsIso (PresheafOfModules.Hom.app e.hom Y) :=
      inferInstanceAs (IsIso ((PresheafOfModules.evaluation X.ringCatSheaf.obj Y).map e.hom))
    ConcreteCategory.bijective_of_isIso _
  let eW : ↥(P.obj (op W)) →ₗ[Γ(X, W)] ↥(Q.obj (op W)) :=
    (PresheafOfModules.Hom.app e.hom (op W)).hom
  let eU : ↥(P.obj (op U)) →ₗ[Γ(X, W)] ↥(Q.obj (op U)) :=
    { toFun := ConcreteCategory.hom (PresheafOfModules.Hom.app e.hom (op U))
      map_add' := map_add _
      map_smul' := fun r x ↦
        (PresheafOfModules.Hom.app e.hom (op U)).hom.map_smul
          ((X.presheaf.map (homOfLE h).op).hom r) x }
  have hcomm : eU ∘ₗ presheafRestrictₗ P h = presheafRestrictₗ Q h ∘ₗ eW :=
    LinearMap.ext fun x ↦ PresheafOfModules.naturality_apply e.hom (homOfLE h).op x
  have h1 : IsLocalizedModule (Submonoid.powers g) (eU ∘ₗ presheafRestrictₗ P h) :=
    (IsLocalizedModule.comp_iff_of_bijective_left (Submonoid.powers g) eU
      (hbij (op U))).2 hP
  rw [hcomm] at h1
  exact (IsLocalizedModule.comp_iff_of_bijective_right (Submonoid.powers g) eW
    (hbij (op W))).1 h1

end Stacks.AlgebraicGeometry.AffineChartLocalization

/-! ### Exterior powers of a localization, over a restriction of scalars -/

/-- **`IsLocalizedModule` transports along an equality of the module structures on its target**,
between two maps with the same underlying function.  Two module structures with the same scalar
action are equal by `Module.ext'`, but they need not be definitionally equal, and then neither
statement is accepted for the other. -/
theorem IsLocalizedModule.congr_module {R : Type uR} [CommRing R] {M N : Type uM}
    [AddCommGroup M] [Module R M] [AddCommGroup N] (T : Submonoid R)
    (i₁ i₂ : Module R N) (hi : i₁ = i₂)
    (f₁ : @LinearMap R R _ _ (RingHom.id R) M N _ _ _ i₁)
    (f₂ : @LinearMap R R _ _ (RingHom.id R) M N _ _ _ i₂)
    (hf : ∀ x, f₁ x = f₂ x)
    (h : @IsLocalizedModule R _ M N _ _ _ i₁ T f₁) :
    @IsLocalizedModule R _ M N _ _ _ i₂ T f₂ := by
  subst hi
  exact (LinearMap.ext hf : f₁ = f₂) ▸ h

section ExteriorPowerCompHom

variable {R : Type uR} [CommRing R] (Rₛ : Type uR) [CommRing Rₛ] [Algebra R Rₛ]
  {M M' : Type uM} [AddCommGroup M] [Module R M] [AddCommGroup M'] [Module R M']
  [Module Rₛ M'] [IsScalarTower R Rₛ M'] (f : M →ₗ[R] M') (n : ℕ)

/-- **`IsLocalization.isLocalizedModule_of_exteriorPower` with the target read over `R` by
restriction of scalars along `algebraMap R Rₛ`.**

This is the shape in which a presheaf of modules presents the scalars on the sections over a
smaller object: `Module.compHom` of the sections' own module structure along a restriction map of
the structure presheaf.  The `R`-module structure the exterior power carries by default is
instead the submodule structure of `ExteriorAlgebra Rₛ M'` as an `R`-algebra; the two have the
same scalar action by `algebraMap_smul`, so `IsLocalizedModule.congr_module` crosses between
them. -/
theorem IsLocalization.isLocalizedModule_of_exteriorPower_compHom (T : Submonoid R)
    [IsLocalization T Rₛ] [IsLocalizedModule T f]
    (Φ : @LinearMap R R _ _ (RingHom.id R) ↥(⋀[R]^n M) ↥(⋀[Rₛ]^n M') _ _ _
      (Module.compHom ↥(⋀[Rₛ]^n M') (algebraMap R Rₛ)))
    (hΦ : ∀ v : Fin n → M, Φ (exteriorPower.ιMulti R n v) =
      exteriorPower.ιMulti Rₛ n fun j ↦ f (v j)) :
    @IsLocalizedModule R _ _ _ _ _ _
      (Module.compHom ↥(⋀[Rₛ]^n M') (algebraMap R Rₛ)) T Φ := by
  have hsmul : ∀ (r : R) (x : ↥(⋀[Rₛ]^n M')), r • x = (algebraMap R Rₛ r) • x := fun r x ↦
    Subtype.ext (algebraMap_smul Rₛ r (x : ExteriorAlgebra Rₛ M')).symm
  let Ψ : ↥(⋀[R]^n M) →ₗ[R] ↥(⋀[Rₛ]^n M') :=
    { toFun := Φ
      map_add' := map_add Φ
      map_smul' := fun r x ↦ (Φ.map_smul r x).trans (hsmul r (Φ x)).symm }
  exact IsLocalizedModule.congr_module T inferInstance _
    (Module.ext' _ _ fun r x ↦ hsmul r x) Ψ Φ (fun _ ↦ rfl)
    (IsLocalization.isLocalizedModule_of_exteriorPower Rₛ f n T Ψ hΦ)

end ExteriorPowerCompHom

/-! ### The sectionwise exterior power of a presheaf of modules that localizes -/

namespace PresheafOfModules

universe w a v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  (F : PresheafOfModules.{max w a} (O ⋙ forget₂ CommRingCat RingCat)) {X Y : Cᵒᵖ} (f : X ⟶ Y)

/-- **The sections of a presheaf of modules over an object, as a module over the sections of the
structure presheaf on another**, by restriction of scalars along a restriction map of `O`. -/
@[instance_reducible]
noncomputable def sectionsModuleAlong : Module ((O.obj X : Type w)) ↥(F.obj Y) :=
  letI : Module ((O.obj Y : Type w)) ↥(F.obj Y) := (F.obj Y).isModule
  Module.compHom _ (O.map f).hom

/-- **The algebra structure on the sections of `O` carried by one of its restriction maps.** -/
@[instance_reducible]
noncomputable def algebraAlong : Algebra ((O.obj X : Type w)) ((O.obj Y : Type w)) :=
  (O.map f).hom.toAlgebra

/-- **A restriction map of a presheaf of modules, as a linear map over the sections of `O` on the
source object.** -/
noncomputable def restrictAlongₗ :
    letI : Module ((O.obj X : Type w)) ↥(F.obj X) := (F.obj X).isModule
    letI := sectionsModuleAlong F f
    ↥(F.obj X) →ₗ[(O.obj X : Type w)] ↥(F.obj Y) :=
  letI : Module ((O.obj X : Type w)) ↥(F.obj X) := (F.obj X).isModule
  letI := sectionsModuleAlong F f
  { toFun := F.map f
    map_add' := map_add _
    map_smul' := fun r x ↦ F.map_smul f r x }

variable {F f} in
/-- **The sectionwise exterior power of a presheaf of modules whose sections localize along a
restriction map localizes there too**, as soon as the sections of the structure presheaf do.

This is `IsLocalization.isLocalizedModule_of_exteriorPower_compHom` at the restriction map of
`PresheafOfModules.extPow n F`, whose hypothesis on wedges holds because the restriction maps of
the sectionwise exterior power are the semilinear exterior powers of those of `F`
(`PresheafOfModules.extPowSections_map`), and those carry a wedge of sections to the wedge of
their restrictions (`ExteriorAlgebra.mapₛₗ_ιMulti`). -/
theorem isLocalizedModule_restrictAlongₗ_extPow (n : ℕ)
    (T : Submonoid ((O.obj X : Type w)))
    (hT : letI := algebraAlong (O := O) f
      IsLocalization T ((O.obj Y : Type w)))
    (hF : letI : Module ((O.obj X : Type w)) ↥(F.obj X) := (F.obj X).isModule
      letI := sectionsModuleAlong F f
      IsLocalizedModule T (restrictAlongₗ F f)) :
    letI : Module ((O.obj X : Type w)) ↥((extPow n F).obj X) := ((extPow n F).obj X).isModule
    letI := sectionsModuleAlong (extPow n F) f
    IsLocalizedModule T (restrictAlongₗ (extPow n F) f) := by
  let := algebraAlong (O := O) f
  let : Module ((O.obj X : Type w)) ↥(F.obj X) := (F.obj X).isModule
  let : Module ((O.obj Y : Type w)) ↥(F.obj Y) := (F.obj Y).isModule
  let := sectionsModuleAlong F f
  let : Module ((O.obj X : Type w)) ↥((extPow n F).obj X) := ((extPow n F).obj X).isModule
  let := sectionsModuleAlong (extPow n F) f
  have := hT
  have := hF
  let : IsScalarTower ((O.obj X : Type w)) ((O.obj Y : Type w)) ↥(F.obj Y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  exact IsLocalization.isLocalizedModule_of_exteriorPower_compHom ((O.obj Y : Type w))
    (restrictAlongₗ F f) n T (restrictAlongₗ (extPow n F) f) fun v ↦ Subtype.ext
      ((extPowSections_map n F f _).trans (ExteriorAlgebra.mapₛₗ_ιMulti _ _ n v))

end PresheafOfModules

/-! ### The restriction of `Ω^i_{X/S}` to the ambient scheme of an object -/

namespace Crystalline.GlobalCrystallineSituation.SmallSite

open Stacks.AlgebraicGeometry.AffineChartLocalization

variable {S : GlobalCrystallineSituation.{u}} (A : CrystallineThickening S)
  (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)

attribute [local instance] restrictedAlgebra

/-- **The restriction of `Ω^i_{X/S}` to the opens of the ambient scheme is the `i`-th sectionwise
exterior power of the restriction of `Ω_{X/S}`.**  Restricting along the functor of restrictions
of the object changes neither the sections nor the transition maps, so it commutes with the
sectionwise exterior power on the nose. -/
theorem restrictedModule_crysDifferentialForms_eq_extPow :
    restrictedModule A (crysDifferentialForms S i) =
      PresheafOfModules.extPow i (restrictedModule A (crysDifferentials S)) := rfl

variable {A} in
/-- **The restriction of `Ω_{X/S}` to an affine ambient scheme localizes on the basic opens**, for
an object lying over an affine open of the divided power base.

`Crystalline.isLocalizedModule_presheafRestrictₗ` is the statement for the presheaf of divided
power differentials of `T` over the base,
`Crystalline.GlobalCrystallineSituation.comparisonIso` ([Stacks, Tag 07IZ]) identifies that
presheaf with the restriction of `Ω_{X/S}`, and
`...AffineChartLocalization.isLocalizedModule_presheafRestrictₗ_of_iso` transports along the
identification.  `isLocalizedModule_ambientRestrictₗ_iff` then reads the conclusion over the
restriction of `𝒪_{X/S}` instead of over `𝒪_T`. -/
theorem restrictedLocalizes_crysDifferentials
    [IsAffine A.obj.thickening.target.scheme] {V : S.S.scheme.Opens}
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
    (hV : IsAffineOpen V) :
    RestrictedLocalizes A (restrictedModule A (crysDifferentials S)) := by
  intro g U hU hUV
  refine (isLocalizedModule_ambientRestrictₗ_iff
    (restrictedModule A (crysDifferentials S)) hUV g).2 ?_
  subst hU
  exact isLocalizedModule_presheafRestrictₗ_of_iso
    (_root_.Crystalline.GlobalCrystallineSituation.comparisonIso A.obj) hUV g
    (_root_.Crystalline.isLocalizedModule_presheafRestrictₗ A.obj.thickening.target
      S.S.scheme A.obj.toBase.hom (isAffineOpen_top A.obj.thickening.target.scheme) h hV g)

variable {A i} in
/-- **The `i`-th sectionwise exterior power of the restriction of `Ω_{X/S}` localizes on the basic
opens of an affine ambient scheme.**  This is
`PresheafOfModules.isLocalizedModule_restrictAlongₗ_extPow` fed with
`isLocalization_restrictedCommRing` and `restrictedLocalizes_crysDifferentials`. -/
theorem restrictedLocalizes_extPow_crysDifferentials
    [IsAffine A.obj.thickening.target.scheme] {V : S.S.scheme.Opens}
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
    (hV : IsAffineOpen V) :
    RestrictedLocalizes A
      (PresheafOfModules.extPow i (restrictedModule A (crysDifferentials S))) := by
  intro g U hU hUV
  exact PresheafOfModules.isLocalizedModule_restrictAlongₗ_extPow
    (F := restrictedModule A (crysDifferentials S)) (f := (homOfLE hUV).op) i
    (Submonoid.powers (openTopResEquiv A (⊤ : A.obj.thickening.target.scheme.Opens) g))
    (isLocalization_restrictedCommRing g hU hUV)
    (restrictedLocalizes_crysDifferentials h hV g hU hUV)

variable {A i} in
/-- **The restriction of `Ω^i_{X/S}` to an affine ambient scheme localizes on the basic opens**:
over `T.basicOpen g` its sections are the localization away from `g` of its sections over `T`. -/
theorem restrictedLocalizes_crysDifferentialForms
    [IsAffine A.obj.thickening.target.scheme] {V : S.S.scheme.Opens}
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
    (hV : IsAffineOpen V) :
    RestrictedLocalizes A (restrictedModule A (crysDifferentialForms S i)) :=
  restrictedLocalizes_extPow_crysDifferentials h hV

variable {A F i} in
/-- **The restriction of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to an affine ambient scheme localizes on the
basic opens**, for a locally quasi-coherent `F` and an object lying over an affine open of the
divided power base.

This discharges the hypothesis of `tensorRestrictionLocalizes_of_forms`: the `F` factor localizes
by hypothesis (1) of [Stacks, Tag 07JN] and the `Ω^i_{X/S}` factor by
`restrictedLocalizes_crysDifferentialForms`. -/
theorem tensorRestrictionLocalizes [IsAffine A.obj.thickening.target.scheme]
    {V : S.S.scheme.Opens}
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
    (hV : IsAffineOpen V) (hF : IsLocallyQuasiCoherent F) :
    TensorRestrictionLocalizes A F i :=
  tensorRestrictionLocalizes_of_forms hF (restrictedLocalizes_crysDifferentialForms h hV)

variable {A F i} in
/-- **The first equality of the proof of [Stacks, Tag 07LF].** For an object `A = (U, T, δ)` of
`Cris(X/S)` with `T` affine and lying over an affine open of the divided power base, and a locally
quasi-coherent sheaf of `𝒪_{X/S}`-modules `F`, the sections over `A` of the crystalline
sheafification of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` are the tensor product of the sections of the two
factors there. -/
theorem bijective_toSheafify_app_tensorDifferentialFormsPresheaf_of_isAffine
    [IsAffine A.obj.thickening.target.scheme] {V : S.S.scheme.Opens}
    (h : (⊤ : A.obj.thickening.target.scheme.Opens) ≤ A.obj.toBase.hom ⁻¹ᵁ V)
    (hV : IsAffineOpen V) (hF : IsLocallyQuasiCoherent F) :
    Function.Bijective (ConcreteCategory.hom
      ((CategoryTheory.toSheafify (smallTopology S)
        (tensorDifferentialFormsPresheaf F i)).app (op A))) :=
  bijective_toSheafify_app_tensorDifferentialFormsPresheaf_of_localizes
    (tensorRestrictionLocalizes h hV hF)

end Crystalline.GlobalCrystallineSituation.SmallSite

end
