module

public import StacksFrontier.AlgebraicGeometry.Spaces.ThickeningCoherentSystem
public import StacksFrontier.AlgebraicGeometry.Spaces.BoundedAffineAlgebraAntiEquivalenceProof
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraPullbackQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.AffinePushforwardQuasicoherentAlgebra
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteDirectImageCoherence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeClosedInFiniteFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystemOfSymmetricAlgebra

/-!
# The direct images along a cartesian tower of affine morphisms

Let `Z 0 → Z 1 → ⋯` be a tower of algebraic spaces with transitions `t n : Z n ⟶ Z (n + 1)`, and
let `W n` be algebraic spaces affine over `Z n` forming a cartesian tower over it:
`W n = Z n ×_{Z (n + 1)} W (n + 1)`. The direct images `𝒜_n = (W n ⟶ Z n)_* 𝒪_{W n}` are then
quasi-coherent algebras with algebra isomorphisms `t n ^* 𝒜_{n + 1} ≅ 𝒜_n` (base change for affine
morphisms, Stacks 081V), and their underlying modules — when coherent — form a coherent system
`(𝒜_n, φ_n)` on the tower, an object of the category of Stacks 08BF.

## Main definitions

* `AlgebraicGeometry.Space.affineOverIsoBaseChangeOfIsPullback`: an algebraic space affine over
  `Y` which is the base change of one affine over `X` along `g : Y ⟶ X`, by a cartesian square, is
  isomorphic to the chosen base change.
* `AlgebraicGeometry.Space.affineTowerAlgebraTransition`: `t n ^* 𝒜_{n + 1} ≅ 𝒜_n`.
* `AlgebraicGeometry.Space.affineTowerModuleTransition`: the same on the underlying modules.
* `AlgebraicGeometry.Space.affineTowerSystem`: the coherent system on the tower.

## Main results

* `AlgebraicGeometry.Space.isCoherent_underlyingModule_pushforwardAlgebra_of_isFinite`: along a
  finite morphism onto a locally Noetherian algebraic space the direct image of the structure
  sheaf is coherent.

## References

* [Stacks Project, Tag 0A01](https://stacks.math.columbia.edu/tag/0A01)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 08BF](https://stacks.math.columbia.edu/tag/08BF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **An algebraic space affine over `Y` which is a base change, by a cartesian square, of one
affine over `X` is isomorphic over `Y` to the chosen base change.** -/
def affineOverIsoBaseChangeOfIsPullback {X Y : AlgebraicSpaces B S hS} (g : Y ⟶ X)
    (W : AffineOver B S hS Y) (W' : AffineOver B S hS X) (s : W.obj.left ⟶ W'.obj.left)
    (h : IsPullback s W.obj.hom W'.obj.hom g) :
    W ≅ affineOverBaseChange B S hS g W' :=
  (ObjectProperty.fullyFaithfulι _).preimageIso
    (Over.isoMk (h.isoIsPullback _ _ (affineOverBaseChange_isPullback B S hS g W'))
      (h.isoIsPullback_hom_snd _ _ _))

/-- The direct image of the structure sheaf carries an isomorphism of algebraic spaces affine over
`X` to an isomorphism of `𝒪_X`-algebras, in the opposite direction. -/
def pushforwardAlgebraIsoOfIso {X : AlgebraicSpaces B S hS} {W W' : AffineOver B S hS X}
    (e : W ≅ W') : pushforwardAlgebra B S hS W'.obj ≅ pushforwardAlgebra B S hS W.obj :=
  (affinePushforwardAlgebraFunctor B S hS X).mapIso e.op

variable {Z : ℕ → AlgebraicSpaces B S hS} (t : ∀ n, Z n ⟶ Z (n + 1))
  (W : ∀ n, AffineOver B S hS (Z n)) (s : ∀ n, (W n).obj.left ⟶ (W (n + 1)).obj.left)
  (hcart : ∀ n, IsPullback (s n) (W n).obj.hom (W (n + 1)).obj.hom (t n))

/-- **The transition isomorphisms of the direct-image algebras of a cartesian affine tower**,
`t n ^* 𝒜_{n + 1} ≅ 𝒜_n`: the base-change comparison of Stacks 081V followed by the direct image of
the identification of `W n` with the base change of `W (n + 1)`. -/
def affineTowerAlgebraTransition (n : ℕ) :
    (algebraPullback B S hS (t n)).obj (pushforwardAlgebra B S hS (W (n + 1)).obj) ≅
      pushforwardAlgebra B S hS (W n).obj :=
  haveI := isIso_affineOverBaseChangeAlgebraHom B S hS (t n) (W (n + 1))
  asIso (affineOverBaseChangeAlgebraHom B S hS (t n) (W (n + 1))) ≪≫
    pushforwardAlgebraIsoOfIso B S hS
      (affineOverIsoBaseChangeOfIsPullback B S hS (t n) (W n) (W (n + 1)) (s n) (hcart n))

/-- The transition isomorphisms of a cartesian affine tower, on the underlying modules:
`t n ^* 𝒜_{n + 1} ≅ 𝒜_n` as `𝒪_{Z n}`-modules. -/
def affineTowerModuleTransition (n : ℕ) :
    (modulePullback B S hS (t n)).obj
        (pushforwardAlgebra B S hS (W (n + 1)).obj).underlyingModule ≅
      (pushforwardAlgebra B S hS (W n).obj).underlyingModule :=
  underlyingModuleAlgebraPullbackModulePullbackIso B S hS (t n) _ ≪≫
    (AlgebraSheaf.underlyingModuleFunctor (F := (Z n).1) (hF := (Z n).2)).mapIso
      (affineTowerAlgebraTransition B S hS t W s hcart n)

/-- **The coherent system of a cartesian affine tower** on the tower `Z`, when the direct images
of the structure sheaves are coherent: the object `(𝒜_n, φ_n)` of the category of Stacks 08BF. -/
def affineTowerSystem
    (hcoh : ∀ n, IsCoherent B S hS (Z n).1 (Z n).2
      (pushforwardAlgebra B S hS (W n).obj).underlyingModule) :
    ThickeningCoherentSystem B S hS Z t where
  term n := ⟨_, hcoh n⟩
  transitionIso n := affineTowerModuleTransition B S hS t W s hcart n

/-- The terms of the coherent system of a cartesian affine tower are the direct images of the
structure sheaves. -/
@[simp]
theorem affineTowerSystem_term_obj
    (hcoh : ∀ n, IsCoherent B S hS (Z n).1 (Z n).2
      (pushforwardAlgebra B S hS (W n).obj).underlyingModule) (n : ℕ) :
    ((affineTowerSystem B S hS t W s hcart hcoh).term n).obj =
      (pushforwardAlgebra B S hS (W n).obj).underlyingModule :=
  rfl

/-- **Along a finite morphism onto a locally Noetherian algebraic space the direct image of the
structure sheaf is coherent.** -/
theorem isCoherent_underlyingModule_pushforwardAlgebra_of_isFinite {X Y : AlgebraicSpaces B S hS}
    (f : Y ⟶ X) (hf : IsFinite B S hS f.hom)
    [Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V))] :
    IsCoherent B S hS X.1 X.2 (pushforwardAlgebra B S hS (Over.mk f)).underlyingModule := by
  have hqc := isQuasicoherent_pushforwardAlgebra_of_isAffineHom' B S hS (Over.mk f)
    (IsFinite.isAffineHom hf)
  have := isFiniteTypeOnSite_underlyingModule_of_isFinite B S hS _ hqc
    (isFinite_pushforwardAlgebra_of_isFinite B S hS f hf)
  exact (isCoherent_iff_isQuasicoherentOnSite_and_isFiniteType B S hS X.1 X.2 _).2
    ⟨hqc, Stacks.SheafOfModules.presheafIsFiniteType_of_isFiniteTypeOnSite _ inferInstance⟩

end AlgebraicGeometry.Space

end
