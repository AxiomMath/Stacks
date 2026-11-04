module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.Composition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.LeftTensorNotation
public import StacksFrontier.AlgebraicGeometry.RelativeProjSeparated.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ClosedEmbeddingProjectionFormulaDerived
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionAssociativity

/-!
# The Fourier-Mukai functor of a kernel pushed forward from a closed subscheme

Let `f : X ⟶ S` and `g : Y ⟶ S` be morphisms of schemes and let

`s : Z ⟶ X ×_S Y`

be a closed immersion.  The Fourier-Mukai functor of [Stacks, Tag 0FYQ] attached to the kernel
`Rs_*𝒪_Z` is the composite of the derived pullback along `s ≫ pr₁` with the derived direct image
along `s ≫ pr₂`:

`Φ_{Rs_*𝒪_Z} ≅ L(s ∘ pr_1)^* ⋙ R(s ∘ pr_2)_*`.

When `Z = Y` and `s` is a *section* of the second projection this reads
`Φ_{Rs_*𝒪_Y} ≅ L(pr_1 ∘ s)^*`.

## Main definitions

* `AlgebraicGeometry.fourierMukaiDerivedPushforwardUnitIso`: the displayed isomorphism, for an
  arbitrary closed immersion `s` into `X ×_S Y`.
* `AlgebraicGeometry.fourierMukaiIsoDerivedPullback_of_isSection`: its form at a section of the
  second projection, `Φ_{Rs_*𝒪_Y} ≅ L(pr_1 ∘ s)^*`.
* `AlgebraicGeometry.fourierMukaiIsoDerivedPullback_of_comp_snd_eq_id`: the same for a section
  of the second projection when `f` is separated.

## References

* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 0FYV](https://stacks.math.columbia.edu/tag/0FYV)
* [Stacks Project, Tag 0G0E](https://stacks.math.columbia.edu/tag/0G0E)
* [Stacks Project, Tag 0B53](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 0B55](https://stacks.math.columbia.edu/tag/0B55)
* [Stacks Project, Tag 0D5S](https://stacks.math.columbia.edu/tag/0D5S)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.DerivedMonoidal

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

/-! ### The structure sheaf in degree zero as the monoidal unit -/

/-- Tensoring with `𝒪_W` in degree zero is the identity: `𝒪_W ⊗^𝐋 - ≅ 𝟭`. -/
def dtenLeftUnitIso (W : Scheme.{u}) :
    dtenLeft W (derivedUnitObject W) ≅ 𝟭 (DerivedCategory W.Modules) :=
  letI : MonoidalCategory (DerivedCategory W.Modules) :=
    canonicalDerivedMonoidal W.toRingedSpace.sheaf
  eqToIso (congrArg (dtenLeft W)
      (tensorUnit_canonicalDerivedMonoidal W.toRingedSpace.sheaf).symm) ≪≫
    MonoidalCategory.leftUnitorNatIso (DerivedCategory W.Modules)

/-! ### Derived functors along identities and composites -/

/-- `R(𝟙_W)_*` is the derived direct image along the identity of the underlying ringed space. -/
theorem dpush_id_eq (W : Scheme.{u}) :
    dpush (𝟙 W) = derivedPushforward (𝟙 W.toRingedSpace) :=
  rfl

/-- `L(𝟙_W)^*` is the derived pullback along the identity of the underlying ringed space. -/
theorem dpull_id_eq (W : Scheme.{u}) :
    dpull (𝟙 W) = derivedPullback (𝟙 W.toRingedSpace) :=
  rfl

/-- The derived pullback along a composite of morphisms of schemes, read on the underlying
morphisms of ringed spaces. -/
theorem dpull_comp_eq {U V W : Scheme.{u}} (p : U ⟶ V) (q : V ⟶ W) :
    derivedPullback (p.toLRSHom.toShHom ≫ q.toLRSHom.toShHom) = dpull (p ≫ q) :=
  congrArg (fun m => derivedPullback m) (shHom_comp p q).symm

/-- The derived direct image along a composite of morphisms of schemes, read on the underlying
morphisms of ringed spaces. -/
theorem dpush_comp_eq {U V W : Scheme.{u}} (p : U ⟶ V) (q : V ⟶ W) :
    derivedPushforward (p.toLRSHom.toShHom ≫ q.toLRSHom.toShHom) = dpush (p ≫ q) :=
  congrArg (fun m => derivedPushforward m) (shHom_comp p q).symm

/-- The isomorphism `R(𝟙_W)_* ≅ 𝟭`. -/
def dpushIdIso (W : Scheme.{u}) : dpush (𝟙 W) ≅ 𝟭 (DerivedCategory W.Modules) :=
  eqToIso (dpush_id_eq W) ≪≫
    Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPushforwardIdIso W.toRingedSpace

/-- The isomorphism `L(𝟙_W)^* ≅ 𝟭`. -/
def dpullIdIso (W : Scheme.{u}) : dpull (𝟙 W) ≅ 𝟭 (DerivedCategory W.Modules) :=
  eqToIso (dpull_id_eq W) ≪≫
    Stacks.Cohomology.DerivedPushforwardAssociativity.derivedPullbackIdIso W.toRingedSpace

/-! ### The two composites through a morphism into the product -/

section Product

variable {S X Y Z : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (s : Z ⟶ Limits.pullback f g)

/-- The isomorphism `L pr_1^* ⋙ Ls^* ≅ L(s ∘ pr_1)^*`. -/
def dpullCompFstIso :
    dpull (Limits.pullback.fst f g) ⋙ dpull s ≅ dpull (s ≫ Limits.pullback.fst f g) :=
  Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      s.toLRSHom.toShHom (Limits.pullback.fst f g).toLRSHom.toShHom ≪≫
    eqToIso (dpull_comp_eq s (Limits.pullback.fst f g))

/-- The isomorphism `Rs_* ⋙ R pr_{2,*} ≅ R(s ∘ pr_2)_*`. -/
def dpushCompSndIso :
    dpush s ⋙ dpush (Limits.pullback.snd f g) ≅ dpush (s ≫ Limits.pullback.snd f g) :=
  derivedPushforwardCompIso s.toLRSHom.toShHom (Limits.pullback.snd f g).toLRSHom.toShHom ≪≫
    eqToIso (dpush_comp_eq s (Limits.pullback.snd f g))

/-! ### The projection formula at a closed immersion into the product -/

/-- For a closed immersion `s : Z ⟶ X ×_S Y`, the projection-formula map

`Rs_*𝒪_Z ⊗^𝐋_{𝒪_{X ×_S Y}} A ⟶ Rs_*(𝒪_Z ⊗^𝐋_{𝒪_Z} Ls^*A)`

is an isomorphism for every `A` in `D(𝒪_{X ×_S Y})`. -/
theorem isIso_projectionFormulaMap_of_isClosedImmersion [IsClosedImmersion s]
    (A : DerivedCategory (Limits.pullback f g).Modules) :
    IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
      s.toLRSHom.toShHom (derivedUnitObject Z) A) :=
  Stacks.Cohomology.DerivedProjectionFormula.isIso_projectionFormulaMap_of_isClosedEmbedding
    s.toLRSHom.toShHom (IsClosedImmersion.isClosedEmbedding s) (derivedUnitObject Z) A

/-- The projection formula at a closed immersion `s`, as an isomorphism of functors
`Rs_*𝒪_Z ⊗^𝐋 - ≅ Ls^* ⋙ (𝒪_Z ⊗^𝐋 -) ⋙ Rs_*`. -/
def dprojectionClosedImmersionIso [IsClosedImmersion s] :
    dtenLeft (Limits.pullback f g) ((dpush s).obj (derivedUnitObject Z)) ≅
      dpull s ⋙ dtenLeft Z (derivedUnitObject Z) ⋙ dpush s :=
  haveI : ∀ A, IsIso ((dprojectionFormulaRight s (derivedUnitObject Z)).app A) :=
    isIso_projectionFormulaMap_of_isClosedImmersion f g s
  letI inst : IsIso (dprojectionFormulaRight s (derivedUnitObject Z)) := NatIso.isIso_of_isIso_app _
  @asIso _ _ _ _ (dprojectionFormulaRight s (derivedUnitObject Z)) inst

/-- The isomorphism `- ⊗^𝐋 Rs_*𝒪_Z ≅ Ls^* ⋙ Rs_*` for a closed immersion `s`. -/
def dtenDerivedPushforwardUnitIso [IsClosedImmersion s] :
    dtenR (Limits.pullback f g) ((dpush s).obj (derivedUnitObject Z)) ≅ dpull s ⋙ dpush s :=
  dtenRSwapIso (Limits.pullback f g) ((dpush s).obj (derivedUnitObject Z)) ≪≫
    dprojectionClosedImmersionIso f g s ≪≫
    Functor.isoWhiskerLeft (dpull s)
      (Functor.isoWhiskerRight (dtenLeftUnitIso Z) (dpush s) ≪≫ (dpush s).leftUnitor)

/-! ### The Fourier-Mukai functor of the kernel `Rs_*𝒪_Z` -/

/-- The Fourier-Mukai functor of a kernel pushed forward from a closed subscheme of the
product. For a closed immersion `s : Z ⟶ X ×_S Y`,

`Φ_{Rs_*𝒪_Z} = R pr_{2,*}(L pr_1^*(-) ⊗^𝐋_{𝒪_{X ×_S Y}} Rs_*𝒪_Z) ≅ L(s ∘ pr_1)^* ⋙ R(s ∘ pr_2)_*`.
-/
def fourierMukaiDerivedPushforwardUnitIso [IsClosedImmersion s] :
    fourierMukai f g ((dpush s).obj (derivedUnitObject Z)) ≅
      dpull (s ≫ Limits.pullback.fst f g) ⋙ dpush (s ≫ Limits.pullback.snd f g) :=
  Functor.isoWhiskerLeft (dpull (Limits.pullback.fst f g))
      (Functor.isoWhiskerRight (dtenDerivedPushforwardUnitIso f g s)
        (dpush (Limits.pullback.snd f g))) ≪≫
    Functor.isoWhiskerRight (dpullCompFstIso f g s)
      (dpush s ⋙ dpush (Limits.pullback.snd f g)) ≪≫
    Functor.isoWhiskerLeft (dpull (s ≫ Limits.pullback.fst f g)) (dpushCompSndIso f g s)

end Product

/-! ### A kernel pushed forward from a section of the second projection -/

section SectionOfSecondProjection

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S) (s : Y ⟶ Limits.pullback f g)

/-- The Fourier-Mukai functor of the kernel `Rs_*𝒪_Y` at a section `s` of the second
projection which is a closed immersion is the derived pullback along `pr_1 ∘ s`:

`Φ_{Rs_*𝒪_Y} ≅ L(pr_1 ∘ s)^*`. -/
def fourierMukaiIsoDerivedPullback_of_isSection [IsClosedImmersion s]
    (hsnd : s ≫ Limits.pullback.snd f g = 𝟙 Y) :
    fourierMukai f g ((dpush s).obj (derivedUnitObject Y)) ≅
      dpull (s ≫ Limits.pullback.fst f g) :=
  fourierMukaiDerivedPushforwardUnitIso f g s ≪≫
    Functor.isoWhiskerLeft (dpull (s ≫ Limits.pullback.fst f g))
      (eqToIso (congrArg dpush hsnd) ≪≫ dpushIdIso Y) ≪≫
    (dpull (s ≫ Limits.pullback.fst f g)).rightUnitor

/-- For `f` separated, the Fourier-Mukai functor of the kernel `Rs_*𝒪_Y` at a section `s` of the
second projection is the derived pullback along `pr_1 ∘ s`: `Φ_{Rs_*𝒪_Y} ≅ L(pr_1 ∘ s)^*`. -/
def fourierMukaiIsoDerivedPullback_of_comp_snd_eq_id [IsSeparated f]
    (hsnd : s ≫ Limits.pullback.snd f g = 𝟙 Y) :
    fourierMukai f g ((dpush s).obj (derivedUnitObject Y)) ≅
      dpull (s ≫ Limits.pullback.fst f g) :=
  letI : IsClosedImmersion s :=
    Stacks.AlgebraicGeometry.RelativeProjSeparated.isClosedImmersion_of_section
      (Limits.pullback.snd f g) s hsnd
  fourierMukaiIsoDerivedPullback_of_isSection f g s hsnd

end SectionOfSecondProjection

end AlgebraicGeometry

end
