module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PrincipalPartsUniversal
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSite
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials

/-!
# The module of differentials and the universe of the module sections

Let `φ : O₁ ⟶ O₂` be a morphism of sheaves of commutative rings on a site `(C, J)`, with rings of
sections in a universe `u`.  The module of differentials `Ω_{O₂/O₁}` of Stacks 04BN corepresents
the functor of relative derivations, and that functor depends on the universe of the modules it
is evaluated on: `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSite` lives at module
universe `max u u₁ v₁ v`, where `u₁` and `v₁` are the universes of the site.  When sheafification
of abelian presheaves exists at the universe `u` of the rings — on an essentially small site, for
instance — the sheaf associated to the presheaf of sectionwise Kähler differentials gives a
module of differentials `Ω` already at universe `u`.

This file proves that the universe lift of `Ω` is the module of differentials at the larger
universe: `moduleOfDifferentialsOfSite ≅ uliftForPresentation Ω`.  The lifted universal
derivation is universal because the universe lift of the sheafification map is still locally
bijective, so that morphisms out of the lift of `Ω` into a sheaf of modules are morphisms out of
the lifted presheaf of Kähler differentials, which corepresents derivations at every universe
(`AlgebraicGeometry.SheafOfModules.liftedDiffUniversal`).

## Main definitions

* `AlgebraicGeometry.SheafOfModules.uliftDifferentialsUnit`: the universe lift of the
  sheafification map of the presheaf of Kähler differentials.
* `AlgebraicGeometry.SheafOfModules.uliftDifferentialsDerivation`: the lifted universal
  derivation.
* `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsOfSiteIsoUlift`: the identification
  of the module of differentials with the universe lift of `Ω`.

## References

* [Stacks Project, Tag 04BN](https://stacks.math.columbia.edu/tag/04BN)
* [Stacks Project, Tag 08TP](https://stacks.math.columbia.edu/tag/08TP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v₁ u u₁

namespace AlgebraicGeometry.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {O₁ O₂ : Sheaf J CommRingCat.{u}} (φ : O₁ ⟶ O₂)

/-- The sheaf associated to the presheaf of sectionwise Kähler differentials of `φ`, with its
sections at the universe of the rings. -/
abbrev sheafifiedDifferentials :
    _root_.SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) :=
  (PresheafOfModules.sheafification (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).obj
    (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)

/-- The universe lift of `sheafifiedDifferentials φ` to the universe `max u u₁ v₁ v` of the
module of differentials. -/
abbrev uliftDifferentials :
    _root_.SheafOfModules.{max u u₁ v₁ v} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) :=
  _root_.SheafOfModules.uliftForPresentation.{u₁, v₁, u, u, max u₁ v₁ v}
    (sheafifiedDifferentials φ)

/-- The sheafification map of the presheaf of Kähler differentials. -/
abbrev differentialsSheafificationUnit :=
  (PresheafOfModules.sheafificationAdjunction
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj)).unit.app
      (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)

/-- **The universe lift of the sheafification map** of the presheaf of Kähler differentials. -/
def uliftDifferentialsUnit :
    liftPresheaf.{v, v₁, u, u₁}
        (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom) ⟶
      (uliftDifferentials.{v} φ).val where
  app X := ModuleCat.ofHom
    { toFun := fun x => ULift.up ((differentialsSheafificationUnit φ).app X x.down)
      map_add' := fun x y => congrArg ULift.up
        (((differentialsSheafificationUnit φ).app X).hom.map_add x.down y.down)
      map_smul' := fun r x => congrArg ULift.up
        (((differentialsSheafificationUnit φ).app X).hom.map_smul r x.down) }
  naturality {X Y} f := by
    ext x
    exact congrArg ULift.up
      (PresheafOfModules.naturality_apply (differentialsSheafificationUnit φ) f x.down)

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- On sections over `X`, `uliftDifferentialsUnit φ` sends `x` to the lift of the image of
`x.down` under the sheafification map. -/
theorem uliftDifferentialsUnit_app_apply (X : Cᵒᵖ)
    (x : (liftPresheaf.{v, v₁, u, u₁}
      (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ.hom)).obj X) :
    (uliftDifferentialsUnit.{v} φ).app X x =
      ULift.up ((differentialsSheafificationUnit φ).app X x.down) :=
  rfl

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The sheafification map of the presheaf of Kähler differentials is locally injective. -/
theorem differentialsSheafificationUnit_isLocallyInjective :
    Presheaf.IsLocallyInjective J
      ((PresheafOfModules.toPresheaf _).map (differentialsSheafificationUnit φ)) :=
  ((GrothendieckTopology.WEqualsLocallyBijective.iff _).1 (J.W_toSheafify _)).1

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- The sheafification map of the presheaf of Kähler differentials is locally surjective. -/
theorem differentialsSheafificationUnit_isLocallySurjective :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf _).map (differentialsSheafificationUnit φ)) :=
  ((GrothendieckTopology.WEqualsLocallyBijective.iff _).1 (J.W_toSheafify _)).2

/-- The universe lift of the sheafification map is locally injective. -/
instance uliftDifferentialsUnit_isLocallyInjective :
    PresheafOfModules.IsLocallyInjective J (uliftDifferentialsUnit.{v} φ) where
  equalizerSieve_mem {X} x y h := by
    have h' : (differentialsSheafificationUnit φ).app X x.down =
        (differentialsSheafificationUnit φ).app X y.down := congrArg ULift.down h
    refine J.superset_covering ?_
      ((differentialsSheafificationUnit_isLocallyInjective φ).equalizerSieve_mem
        (X := X) x.down y.down h')
    intro Z g hg
    exact congrArg ULift.up hg

/-- The universe lift of the sheafification map is locally surjective. -/
instance uliftDifferentialsUnit_isLocallySurjective :
    PresheafOfModules.IsLocallySurjective J (uliftDifferentialsUnit.{v} φ) where
  imageSieve_mem {X} s := by
    refine J.superset_covering ?_
      ((differentialsSheafificationUnit_isLocallySurjective φ).imageSieve_mem
        (U := X) (ULift.down s))
    rintro Z g ⟨x, hx⟩
    exact ⟨ULift.up x, congrArg ULift.up hx⟩

/-- **The lifted universal derivation**, with values in the universe lift of `Ω`. -/
def uliftDifferentialsDerivation : (uliftDifferentials.{v} φ).val.Derivation' φ.hom :=
  (liftedDiffDerivation.{v₁, u, u₁, v} φ.hom).postcomp (uliftDifferentialsUnit.{v} φ)

variable [J.WEqualsLocallyBijective AddCommGrpCat.{max u u₁ v₁ v}]

omit [J.HasSheafCompose (forget₂ CommRingCat RingCat)] in
/-- **The lifted derivation is universal** among derivations with values in sheaves of modules
at the larger universe. -/
theorem existsUnique_uliftDifferentialsDerivation
    (F : _root_.SheafOfModules.{max u u₁ v₁ v} (Stacks.SheafOfModules.Tensor.ringSheaf O₂))
    (D : F.val.Derivation' φ.hom) :
    ∃! g : uliftDifferentials.{v} φ ⟶ F,
      (uliftDifferentialsDerivation.{v} φ).postcomp g.val = D := by
  let U := liftedDiffUniversal.{v, v₁, u, u₁} φ.hom
  let e := PresheafOfModules.homEquivOfIsLocallyBijective (uliftDifferentialsUnit.{v} φ) F.isSheaf
  refine ⟨⟨e.symm (U.desc D)⟩, ?_, fun g hg => ?_⟩
  · show (liftedDiffDerivation.{v₁, u, u₁, v} φ.hom).postcomp
      (uliftDifferentialsUnit.{v} φ ≫ e.symm (U.desc D)) = D
    rw [show uliftDifferentialsUnit.{v} φ ≫ e.symm (U.desc D) = U.desc D from
      e.apply_symm_apply (U.desc D)]
    exact U.fac D
  · apply _root_.SheafOfModules.hom_ext
    show g.val = e.symm (U.desc D)
    apply e.injective
    rw [e.apply_symm_apply]
    apply U.postcomp_injective
    exact hg.trans (U.fac D).symm

/-- The universe lift of `Ω` corepresents relative derivations at the larger universe. -/
def uliftDifferentialsCorepresentableBy :
    (derivationsFunctor.{v} O₁ O₂ φ).CorepresentableBy (uliftDifferentials.{v} φ) :=
  universalDerivationCorepresentableBy.{v, v₁, u, u₁} O₁ O₂ φ
    (uliftDifferentialsDerivation.{v} φ) (existsUnique_uliftDifferentialsDerivation.{v} φ)

/-- **The module of differentials is the universe lift of `Ω`.** -/
def moduleOfDifferentialsOfSiteIsoUlift :
    moduleOfDifferentialsOfSite.{v₁, u₁, u, v} O₁ O₂ φ ≅ uliftDifferentials.{v} φ :=
  (derivationsFunctor.{v} O₁ O₂ φ).corepresentableBy.uniqueUpToIso
    (uliftDifferentialsCorepresentableBy.{v} φ)

end AlgebraicGeometry.SheafOfModules
