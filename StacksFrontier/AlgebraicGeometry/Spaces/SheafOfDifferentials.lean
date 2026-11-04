module

public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.RingedSite
public import StacksFrontier.AlgebraicGeometry.Spaces.StructureMapSharp
public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of differentials of a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`.  Stacks 03G8 attaches to
`f` a morphism of the small étale ringed topoi, `AlgebraicGeometry.Space.smallEtaleRingedToposHom`,
whose structure map in inverse-image form is a homomorphism `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` of sheaves of
commutative rings on the small étale site of `X`.  The *sheaf of differentials* `Ω_{X/Y}` of
Stacks 04CT is the module of differentials of that homomorphism in the sense of Stacks 04BN,
together with its universal `Y`-derivation `d_{X/Y} : 𝒪_X ⟶ Ω_{X/Y}`; a `Y`-derivation is by
definition an `f♯`-derivation.

The module of differentials is constructed, not chosen: it is the associated sheaf of modules of
the presheaf whose sections on an étale chart `U` are the Kähler differentials of `𝒪_X(U)` over
`(f⁻¹𝒪_Y)(U)`, and `universalDerivation_isUniversal` proves that it corepresents the functor of
`Y`-derivations, which is the property Stacks 04BN names it by.

## Main definitions

* `AlgebraicGeometry.Space.inverseImageStructureSheaf` is `f⁻¹𝒪_Y`, the inverse image of the
  structure sheaf of the target, as a sheaf of commutative rings on the small étale site of `X`.
* `AlgebraicGeometry.Space.structureSharpInverseImage` is the inverse-image form
  `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map of `f`.
* `AlgebraicGeometry.Space.sheafOfDifferentials` is the sheaf of differentials `Ω_{X/Y}`, and
  `AlgebraicGeometry.Space.universalDerivation` is its universal `Y`-derivation `d_{X/Y}`.
* `AlgebraicGeometry.Space.universalDerivationHom` is `d_{X/Y}` as a morphism of the underlying
  sheaves of sets, and `AlgebraicGeometry.Space.pushforwardUniversalDerivationHom` is the
  composite `𝒪_X ⟶ f_*𝒪_{X'} ⟶ f_*Ω_{X'/Y'}` of Stacks 04CX for a commutative square.
* `AlgebraicGeometry.Space.IsSheafOfDifferentialsMap` is the property of Stacks 04CX
  characterizing the comparison map `c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of a commutative square.

## Main results

* `AlgebraicGeometry.Space.universalDerivation_isUniversal`: every `Y`-derivation with values in
  an `𝒪_X`-module factors through `d_{X/Y}` by a unique morphism of `𝒪_X`-modules.  So
  `Ω_{X/Y}` corepresents the functor of `Y`-derivations.
* `AlgebraicGeometry.Space.eq_of_isSheafOfDifferentialsMap`: at most one morphism of
  `𝒪_{X'}`-modules `f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` has the characterizing property of Stacks 04CX.

## Implementation notes

The small étale site of an algebraic space has its objects one universe above its morphisms and
its structure rings, `RingedSite.{u + 1, u, u}`.  The module of differentials of a homomorphism
of sheaves of commutative rings on a *small* site is
`Stacks.Sheaves.Differentials.moduleOfDifferentials`, and it does not apply here: that site is
`C : Type u` with `Category.{u} C`.  The construction below is the same formula — sheafify the
presheaf of sectionwise Kähler differentials — assembled from Mathlib's
`PresheafOfModules.DifferentialsConstruction.relativeDifferentials'` and
`PresheafOfModules.sheafification`, both of which are universe-polymorphic.  For the same reason
the universal property is proved from Mathlib's
`PresheafOfModules.DifferentialsConstruction.isUniversal'` through the sheafification bijection
rather than read off the small-site statement.

The instance `smallEtaleRingedSite_hasWeakSheafify` restates one of the two sheafification
hypotheses of the small étale site for the projections of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does not unfold; this is
the pattern their `∀`-quantified slice versions in
`StacksFrontier/AlgebraicGeometry/Spaces/RingedSite.lean` already follow. The other hypothesis,
`AlgebraicGeometry.Space.smallEtaleRingedSite_wEqualsLocallyBijective`, is restated the same way
in `StacksFrontier/AlgebraicGeometry/Spaces/ModulesAbelian.lean`, which this module re-exports.

## References

* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT)
* [Stacks Project, Tag 04BQ](https://stacks.math.columbia.edu/tag/04BQ), the sheaf of
  differentials of a morphism of ringed topoi.
* [Stacks Project, Tag 04BN](https://stacks.math.columbia.edu/tag/04BN) and
  [Tag 04BL](https://stacks.math.columbia.edu/tag/04BL), the module of differentials of a
  homomorphism of sheaves of rings and its universal property.
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the morphism of small
  étale ringed topoi of a morphism of algebraic spaces.
-/

@[expose] public section

open CategoryTheory

universe u v₁ u₁ w

namespace AlgebraicGeometry.Space

section Presheaf

variable {C : Type u₁} [Category.{v₁} C]

/-- Morphisms out of the presheaf of sectionwise Kähler differentials of
`φ' : S ⟶ R` are the relative derivations of a presheaf of `R`-modules: the universal property of
`PresheafOfModules.DifferentialsConstruction.derivation'`, packaged as a bijection. -/
private noncomputable def presheafDifferentialsEquiv
    {S R : Cᵒᵖ ⥤ CommRingCat.{w}} (φ' : S ⟶ R)
    (M : PresheafOfModules.{w} (R ⋙ forget₂ CommRingCat RingCat)) :
    (PresheafOfModules.DifferentialsConstruction.relativeDifferentials' φ' ⟶ M) ≃
      M.Derivation' φ' where
  toFun g := (PresheafOfModules.DifferentialsConstruction.derivation' φ').postcomp g
  invFun := (PresheafOfModules.DifferentialsConstruction.isUniversal' φ').desc
  left_inv _ :=
    (PresheafOfModules.DifferentialsConstruction.isUniversal' φ').postcomp_injective _ _
      ((PresheafOfModules.DifferentialsConstruction.isUniversal' φ').fac _)
  right_inv := (PresheafOfModules.DifferentialsConstruction.isUniversal' φ').fac

end Presheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Presheaves of abelian groups on the small étale site of an algebraic space admit
sheafification, stated for the topology of
`AlgebraicGeometry.Space.smallEtaleRingedSite`, which instance search does not unfold. -/
instance smallEtaleRingedSite_hasWeakSheafify (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hF : IsAlgebraicSpace B S hS F) :
    HasWeakSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{u} := by
  change HasWeakSheafify (SmallEtale.topology B S hS F) AddCommGrpCat.{u}
  infer_instance

variable {X Y : AlgebraicSpaces B S hS}

/-- The inverse image `f⁻¹𝒪_Y` of the structure sheaf of the target, as a sheaf of commutative
rings on the small étale site of `X`. -/
noncomputable def inverseImageStructureSheaf (f : X ⟶ Y) :
    Sheaf (SmallEtale.topology B S hS X.1) CommRingCat.{u} :=
  (Stacks.Sheaves.ToposPushforward.inverseImageCommRingFunctor
    (smallEtaleRingedToposHom B S hS f).toToposHom).obj (smallEtaleRingedTopos B S hS Y).O

/-- The inverse-image form `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map of the morphism of small
étale ringed topoi of `f`.  A `Y`-derivation of an `𝒪_X`-module is an `f♯`-derivation. -/
noncomputable def structureSharpInverseImage (f : X ⟶ Y) :
    inverseImageStructureSheaf B S hS f ⟶ (smallEtaleRingedTopos B S hS X).O :=
  (smallEtaleRingedToposHom B S hS f).fSharpInverseImage

/-- **Stacks 04CT.** The sheaf of differentials `Ω_{X/Y}` of a morphism `f : X ⟶ Y` of algebraic
spaces: the module of differentials of `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X`, realized as the associated sheaf of
modules of the presheaf of sectionwise Kähler differentials of `f♯`. -/
@[stacks 04CT "the sheaf of differentials of a morphism of algebraic spaces"]
noncomputable def sheafOfDifferentials (f : X ⟶ Y) : Modules.{u, u} B S hS X.1 X.2 :=
  (PresheafOfModules.sheafification (𝟙 _)).obj
    (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
      (structureSharpInverseImage B S hS f).hom)

/-- **Stacks 04CT.** The universal `Y`-derivation `d_{X/Y} : 𝒪_X ⟶ Ω_{X/Y}`: the sectionwise
Kähler differential followed by the unit of sheafification. -/
@[stacks 04CT "the universal `Y`-derivation `d_{X/Y}`"]
noncomputable def universalDerivation (f : X ⟶ Y) :
    (sheafOfDifferentials B S hS f).val.Derivation'
      (structureSharpInverseImage B S hS f).hom :=
  (PresheafOfModules.DifferentialsConstruction.derivation'
      (structureSharpInverseImage B S hS f).hom).postcomp
    ((PresheafOfModules.sheafificationAdjunction
        (J := (smallEtaleRingedSite B S hS X.1 X.2).J)
        (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS X.1 X.2).O)).obj)).unit.app
      (PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
        (structureSharpInverseImage B S hS f).hom))

/-- The sheaf of differentials corepresents the functor of `Y`-derivations: every `Y`-derivation
with values in an `𝒪_X`-module factors through `d_{X/Y}` by a unique morphism of
`𝒪_X`-modules. -/
theorem universalDerivation_isUniversal (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (D : F.val.Derivation' (structureSharpInverseImage B S hS f).hom) :
    ∃! g : sheafOfDifferentials B S hS f ⟶ F,
      (universalDerivation B S hS f).postcomp g.val = D := by
  set e := (PresheafOfModules.sheafificationHomEquiv
      (𝟙 ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS X.1 X.2).O)).obj) (P :=
      PresheafOfModules.DifferentialsConstruction.relativeDifferentials'
        (structureSharpInverseImage B S hS f).hom) (F := F)).trans
    (presheafDifferentialsEquiv (structureSharpInverseImage B S hS f).hom _)
  have key (g : sheafOfDifferentials B S hS f ⟶ F) :
      e g = (universalDerivation B S hS f).postcomp g.val := by
    ext U x
    rfl
  exact ⟨e.symm D, (key _).symm.trans (e.apply_symm_apply D),
    fun g hg ↦ (Equiv.eq_symm_apply e).mpr ((key g).trans hg)⟩

/-! ### The comparison map of a commutative square -/

/-- The universal `Y`-derivation `d_{X/Y}` as a morphism of the underlying sheaves of sets, the
form in which the direct image along a morphism of algebraic spaces applies to it. -/
noncomputable def universalDerivationHom (f : X ⟶ Y) :
    CategoryTheory.Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) ⟶
      CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
        (sheafOfDifferentials B S hS f) :=
  CategoryTheory.Sheaf.unaryOpHom (fun _ a ↦ (universalDerivation B S hS f).d a)
    (fun g a ↦ ((universalDerivation B S hS f).d_map g a).symm)

variable {X' Y' : AlgebraicSpaces B S hS}

/-- **Stacks 04CX.** For a commutative square with top edge `f : X' ⟶ X` and left edge
`p' : X' ⟶ Y'`, the structure map `f♯ : 𝒪_X ⟶ f_*𝒪_{X'}` followed by the direct image of the
universal `Y'`-derivation `d_{X'/Y'}`, on underlying sheaves of sets. -/
@[stacks 04CX "the composite `f_*d_{X'/Y'} ∘ f♯`"]
noncomputable def pushforwardUniversalDerivationHom (f : X' ⟶ X) (p' : X' ⟶ Y') :
    CategoryTheory.Sheaf.ringSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) ⟶
      CategoryTheory.Sheaf.moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X)
        ((modulePushforward B S hS f).obj (sheafOfDifferentials B S hS p')) :=
  (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
      (structureSharp B S hS f) ≫
    (smallEtaleDirectImage B S hS f).map (universalDerivationHom B S hS p')

/-- **Stacks 04CX**, the characterizing property of the comparison map
`c_f : f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of a commutative square: its adjoint transpose carries the
universal differential `d_{X/Y}(t)` of a local section `t` of `𝒪_X` to `d_{X'/Y'}(f♯ t)`. -/
@[stacks 04CX "the characterizing property of `c_f` on universal local sections"]
def IsSheafOfDifferentialsMap (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    (c : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p') : Prop :=
  ∀ (U : (SmallEtale B S hS X.1)ᵒᵖ) (t : (structureRingSheaf B S hS X).obj.obj U),
    ((((modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
        (sheafOfDifferentials B S hS p') c).val.app U).hom)
        ((universalDerivation B S hS p).d t) =
      (pushforwardUniversalDerivationHom B S hS f p').hom.app U t

/-- **Stacks 04CX**, uniqueness: at most one morphism `f^*Ω_{X/Y} ⟶ Ω_{X'/Y'}` of
`𝒪_{X'}`-modules carries the pulled-back universal differentials to the universal differentials
of the pulled-back local sections. -/
@[stacks 04CX "uniqueness of the comparison map `c_f`"]
theorem eq_of_isSheafOfDifferentialsMap (f : X' ⟶ X) (p : X ⟶ Y) (p' : X' ⟶ Y')
    {c₁ c₂ : (modulePullback B S hS f).obj (sheafOfDifferentials B S hS p) ⟶
      sheafOfDifferentials B S hS p'}
    (h₁ : IsSheafOfDifferentialsMap B S hS f p p' c₁)
    (h₂ : IsSheafOfDifferentialsMap B S hS f p p' c₂) : c₁ = c₂ := by
  set e := (modulePullbackAdjunction B S hS f).homEquiv (sheafOfDifferentials B S hS p)
    (sheafOfDifferentials B S hS p')
  have hD : (universalDerivation B S hS p).postcomp (e c₁).val =
      (universalDerivation B S hS p).postcomp (e c₂).val := by
    apply PresheafOfModules.Derivation.ext
    ext U t
    exact (h₁ U t).trans (h₂ U t).symm
  obtain ⟨g, hg, hu⟩ := universalDerivation_isUniversal B S hS p
    ((modulePushforward B S hS f).obj (sheafOfDifferentials B S hS p'))
    ((universalDerivation B S hS p).postcomp (e c₁).val)
  exact e.injective ((hu _ rfl).trans (hu _ hD.symm).symm)

end AlgebraicGeometry.Space

end
