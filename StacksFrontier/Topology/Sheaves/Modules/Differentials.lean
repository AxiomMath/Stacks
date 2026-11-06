module

public import Mathlib.Algebra.Category.ModuleCat.Differentials.Presheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Topology.Sheaves.Sheaf
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf of relative differentials on a topological space

For a morphism `O₁ ⟶ O₂` of sheaves of commutative rings on a topological space, the
derivations of `O₂` relative to `O₁` with values in a sheaf of `O₂`-modules are represented
by a sheaf of modules, the sheaf of relative differentials.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.SheafDerivation`: relative derivations with values in a
  sheaf of modules.
* `AlgebraicGeometry.SheafOfModules.IsUniversal`: the universal property of a relative
  derivation.
* `AlgebraicGeometry.SheafOfModules.moduleOfDifferentials`: the representing sheaf.
* `AlgebraicGeometry.SheafOfModules.universalDerivation`: its universal relative derivation.
* `AlgebraicGeometry.SheafOfModules.sectionwiseDifferentialsSheaf`: the sheafification of the
  sectionwise Kähler differentials.
* `AlgebraicGeometry.SheafOfModules.sectionwiseDerivation`: the derivation sending a local
  section to its differential in that sheaf.

## Main results

* `AlgebraicGeometry.SheafOfModules.universalDerivation_isUniversal`: the unique
  factorization through the universal derivation.
* `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsIsoSectionwise` identifies the
  representing sheaf with the sectionwise sheafification.
* `AlgebraicGeometry.SheafOfModules.moduleOfDifferentialsIsoSectionwise_compatible` identifies
  the universal derivation with the sheafified sectionwise derivation.

## Implementation notes

Representability is stated by its universal element: postcomposition with the universal
derivation is a bijection from morphisms out of `moduleOfDifferentials` to relative
derivations. These bijections commute with postcomposition, so this unique-factorization
statement is exactly a corepresentation of the derivations functor, the covariant convention
for representability.

The representing object comes from the corepresentability of the derivations functor on a
general site. The sectionwise presentation then follows from the universal property of
presheaf differentials together with the sheafification adjunction, with the compatibility
needed to transport its generators. The sectionwise construction lies in the same universe as
the rings, as in Mathlib's `relativeDifferentials'`, while the abstract representing object
still allows a larger coefficient universe.

`underlyingRingSheaf` is the open-cover-site case of the site-level
`Stacks.SheafOfModules.Tensor.ringSheaf`. The two are kept apart because `TopCat.Sheaf` is a
`def` rather than an abbreviation, so the elaborator will not unify the two spellings of the
sheaf type on its own.

## References

* [Stacks Project, Tag 08RM](https://stacks.math.columbia.edu/tag/08RM)
-/

@[expose] public section

open CategoryTheory PresheafOfModules TopologicalSpace

universe u v w u_1

namespace AlgebraicGeometry.SheafOfModules

attribute [local instance 1100] CategoryTheory.CategoryStruct.toQuiver

/-- The sheaf of rings underlying a sheaf of commutative rings on a topological space. -/
noncomputable abbrev underlyingRingSheaf {X : TopCat.{u}}
    (O : TopCat.Sheaf CommRingCat.{max u v} X) :
    TopCat.Sheaf RingCat.{max u v} X :=
  (sheafCompose (Opens.grothendieckTopology X)
    (forget₂ CommRingCat.{max u v} RingCat.{max u v})).obj O

/-- Relative derivations of sheaves, expressed on their underlying presheaves. -/
@[ega "IV 16.5.1" "more general"]
abbrev SheafDerivation {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} (φ : O₁ ⟶ O₂)
    (M : _root_.SheafOfModules.{max u v w} (underlyingRingSheaf O₂)) :=
  PresheafOfModulesOfCommRing.Derivation' M.val φ.hom

/-- A relative derivation into a sheaf of modules is universal if every relative
derivation factors through it by a unique morphism of sheaves of modules. -/
def IsUniversal {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} {φ : O₁ ⟶ O₂}
    {Ω : _root_.SheafOfModules.{max u v w} (underlyingRingSheaf O₂)}
    (d : SheafDerivation φ Ω) : Prop :=
  ∀ (F : _root_.SheafOfModules.{max u v w} (underlyingRingSheaf O₂))
    (D : SheafDerivation φ F),
    ∃! f : Ω ⟶ F, (d.postcomp f.val : SheafDerivation φ F) = D

/-- The derivations functor on the open-cover site is corepresentable. Instance search does
not unfold the definition `TopCat.Sheaf`, so it cannot see the general site-level instance
through that spelling of the sheaf type; this records it at the shape the search does see. -/
instance derivationsFunctor_isCorepresentable_topCat {X : TopCat.{u}}
    (O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X) (φ : O₁ ⟶ O₂) :
    (derivationsFunctor.{w} O₁ O₂ φ).IsCorepresentable :=
  derivationsFunctor_isCorepresentable.{w} O₁ O₂ φ

/-- The sheaf of relative differentials representing derivations along `φ`. -/
@[stacks 08RP "the module of differentials"]
noncomputable def moduleOfDifferentials {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} (φ : O₁ ⟶ O₂) :
    _root_.SheafOfModules.{max u v w} (underlyingRingSheaf O₂) :=
  (derivationsFunctor.{w} O₁ O₂ φ).coreprX

/-- The universal relative derivation into `moduleOfDifferentials φ`. -/
@[stacks 08RP "the module of differentials", ega "IV 16.3.6" "dt", ega "IV 16.5.3" "(i)"]
noncomputable def universalDerivation {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} (φ : O₁ ⟶ O₂) :
    SheafDerivation.{u, v, u_1} φ (moduleOfDifferentials.{u, v, u_1} φ) :=
  (derivationsFunctor.{u_1} O₁ O₂ φ).coreprx

/-- **Stacks Project, Tag 08RM.** Postcomposition with the universal
derivation gives the unique morphism from the module of relative
differentials to any coefficient sheaf. -/
@[stacks 08RM,
  stacks 01UR "postcomposition with the universal derivation is bijective onto the derivations",
  stacks 04BV "the factorization D = d o theta of a derivation through the universal derivation",
  ega "IV 16.5.3" "(ii)"]
theorem universalDerivation_isUniversal {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} (φ : O₁ ⟶ O₂) :
    IsUniversal.{u, v, u_1} (universalDerivation.{u, v, u_1} φ) := by
  intro F D
  let e := (derivationsFunctor.{u_1} O₁ O₂ φ).corepresentableBy
  have heq (f : moduleOfDifferentials.{u, v, u_1} φ ⟶ F) :
      e.homEquiv f =
        (universalDerivation.{u, v, u_1} φ).postcomp f.val :=
    (e.homEquiv_eq f).trans rfl
  refine ⟨e.homEquiv.symm D, ?_, ?_⟩
  · exact (heq _).symm.trans (e.homEquiv.apply_symm_apply D)
  · intro f hf
    exact e.homEquiv.injective ((heq f).trans (hf.trans (e.homEquiv.apply_symm_apply D).symm))

/-- The sheaf associated to the presheaf whose sections on `U` are the
Kähler differentials of `O₂(U)` over `O₁(U)`. -/
noncomputable abbrev sectionwiseDifferentialsSheaf {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} (φ : O₁ ⟶ O₂) :
    _root_.SheafOfModules.{max u v} (underlyingRingSheaf O₂) := by
  letI : HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max u v} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u v} _ _
  letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u v} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{
      _, _, _, _, max u v} _
  exact (PresheafOfModules.sheafification.{max u v}
    (𝟙 (underlyingRingSheaf O₂).obj)).obj
    (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom)

/-- The sectionwise differential followed by the unit of sheafification. -/
noncomputable def sectionwiseDerivation {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} (φ : O₁ ⟶ O₂) :
    SheafDerivation φ (sectionwiseDifferentialsSheaf φ) := by
  letI : HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max u v} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u v} _ _
  letI : (Opens.grothendieckTopology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u v} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{
      _, _, _, _, max u v} _
  exact (PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' φ.hom).postcomp
    ((PresheafOfModules.sheafificationAdjunction (J := Opens.grothendieckTopology X)
      (𝟙 (underlyingRingSheaf O₂).obj)).unit.app
        (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom))

/-- Sheafifying the universal sectionwise derivation represents derivations
with values in sheaves. -/
theorem sectionwiseDerivation_isUniversal {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} (φ : O₁ ⟶ O₂) :
    IsUniversal (sectionwiseDerivation φ) := by
  let : HasSheafify (Opens.grothendieckTopology X)
      AddCommGrpCat.{max u v} :=
    hasSheafifyEssentiallySmallSite.{_, _, _, _, max u v} _ _
  let : (Opens.grothendieckTopology X).WEqualsLocallyBijective
      AddCommGrpCat.{max u v} :=
    GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{
      _, _, _, _, max u v} _
  let R := underlyingRingSheaf O₂
  let P := PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials' φ.hom
  let S : _root_.SheafOfModules.{max u v} R := sectionwiseDifferentialsSheaf φ
  let dP := PresheafOfModulesOfCommRing.DifferentialsConstruction.derivation' φ.hom
  let η : P ⟶ (_root_.SheafOfModules.forget R).obj S :=
    (PresheafOfModules.sheafificationAdjunction (J := Opens.grothendieckTopology X)
      (𝟙 R.obj)).unit.app P
  let dS : SheafDerivation φ S := dP.postcomp η
  change IsUniversal dS
  intro F D
  let e := PresheafOfModulesOfCommRing.DifferentialsConstruction.isUniversal' φ.hom
  let g : P ⟶ (_root_.SheafOfModules.forget R).obj F := e.desc D
  let f : S ⟶ F :=
    (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm g
  have hf : (dS.postcomp f.val : SheafDerivation φ F) = D := by
    change dP.postcomp (η ≫ f.val) = D
    have hmap : η ≫ f.val = g := by
      change PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj) f = g
      exact Equiv.apply_symm_apply _ g
    rw [hmap]
    exact e.fac D
  refine ⟨f, hf, fun f' hf' ↦
    (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).injective (e.postcomp_injective _ _ ?_)⟩
  ext U x
  exact (PresheafOfModulesOfCommRing.Derivation.congr_d hf' x).trans
    (PresheafOfModulesOfCommRing.Derivation.congr_d hf x).symm

/-- The representing module is canonically the sheafification of sectionwise
Kähler differentials, with its specified universal derivation. -/
noncomputable def moduleOfDifferentialsIsoSectionwise {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} (φ : O₁ ⟶ O₂) :
    moduleOfDifferentials.{u, v, max u v} φ ≅
      sectionwiseDifferentialsSheaf φ := by
  let dS := sectionwiseDerivation φ
  have hS := sectionwiseDerivation_isUniversal φ
  let f := Classical.choose (universalDerivation_isUniversal φ _ dS)
  have hf := (Classical.choose_spec
    (universalDerivation_isUniversal φ _ dS)).1
  let g := Classical.choose (hS _ (universalDerivation φ))
  have hg := (Classical.choose_spec
    (hS _ (universalDerivation φ))).1
  refine ⟨f, g, ?_, ?_⟩
  · refine (universalDerivation_isUniversal φ _ (universalDerivation φ)).unique ?_ rfl
    ext U x
    exact congrArg (fun y ↦ (g.val.app U).hom y)
      (PresheafOfModulesOfCommRing.Derivation.congr_d hf x) |>.trans
        (PresheafOfModulesOfCommRing.Derivation.congr_d hg x)
  · refine (hS _ dS).unique ?_ rfl
    ext U x
    exact congrArg (fun y ↦ (f.val.app U).hom y)
      (PresheafOfModulesOfCommRing.Derivation.congr_d hg x) |>.trans
        (PresheafOfModulesOfCommRing.Derivation.congr_d hf x)

/-- The comparison carries the universal derivation to the image of the
sectionwise derivation under the unit of sheafification. -/
@[simp]
theorem moduleOfDifferentialsIsoSectionwise_compatible {X : TopCat.{u}}
    {O₁ O₂ : TopCat.Sheaf CommRingCat.{max u v} X} (φ : O₁ ⟶ O₂) :
    (universalDerivation φ).postcomp
        (moduleOfDifferentialsIsoSectionwise φ).hom.val =
      sectionwiseDerivation φ :=
  (Classical.choose_spec
    (universalDerivation_isUniversal φ _ (sectionwiseDerivation φ))).1

end AlgebraicGeometry.SheafOfModules
