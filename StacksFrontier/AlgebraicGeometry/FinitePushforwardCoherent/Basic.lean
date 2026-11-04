module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.AffinePushforward.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentFinite.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Finite type of the direct image along a finite morphism

Let `f : Y ⟶ X` be a finite morphism of schemes. The sections of the direct image `f_*F` over
an affine open `V ⊆ X` are the sections of `F` over the affine open `f⁻¹V`, and they form a
finite `Γ(X, V)`-module as soon as `F` is quasi-coherent of finite type: they are finite over
`Γ(Y, f⁻¹V)`, which is in turn a finite `Γ(X, V)`-algebra because `f` is finite. Finite type is
local on the base, so `f_*F` is of finite type; and the converse holds as well, which is
[Stacks, Tag 05B3].

## Main results

* `Stacks.AlgebraicGeometry.FinitePushforwardCoherent.finite_sections_pushforward`: the sections
  of `f_*F` over an affine open form a finite module over the structure ring of that open.
* `Stacks.AlgebraicGeometry.FinitePushforwardCoherent.isFiniteType_pushforward`: the direct
  image of a quasi-coherent module of finite type along a finite morphism is of finite type.
* `Stacks.AlgebraicGeometry.FinitePushforwardCoherent.isFiniteType_pushforward_iff`: the
  converse also holds, so a quasi-coherent module is of finite type exactly when its direct
  image along a finite morphism is. This is [Stacks, Tag 05B3].

The coherence assertion of [Stacks, Tag 01Y6], which these finiteness results feed, is
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite`.

## Implementation notes

The whole argument is affine-local, and the two identifications it rests on are definitional at
this pin: `Γ(f_*F, V)` is `Γ(F, f⁻¹V)` by `AlgebraicGeometry.Scheme.Modules.pushforward_obj_obj`,
and the `Γ(X, V)`-action on it is the `Γ(Y, f⁻¹V)`-action read through `f.app V`. So the scalar
tower `Γ(X, V) → Γ(Y, f⁻¹V) → Γ(f_*F, V)` is `IsScalarTower.of_algebraMap_smul` applied to
`rfl`, and no transport of a module structure is needed anywhere.

Finiteness of the sections of `F` itself over the affine open `f⁻¹V` is
`Stacks.AlgebraicGeometry.CoherentFinite.finite_sections`, the form in which this repository
carries [Stacks, Tag 01PB]; finiteness of `Γ(Y, f⁻¹V)` over `Γ(X, V)` is
`AlgebraicGeometry.Scheme.Hom.finite_app`. Locality of finite type is
`Stacks.AlgebraicGeometry.CoherentTFAE.isFiniteType_of_cover_isFiniteTildeOn`, whose hypothesis
`Stacks.AlgebraicGeometry.CoherentTFAE.IsFiniteTildeOn` is reached from finiteness of the
sections through `Stacks.AlgebraicGeometry.CoherentFinite.specSectionsEquiv`.

Neither assertion of [Stacks, Tag 01Y6] is proved here. Coherence of `f_*F` is
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite`, and
vanishing of the higher direct images is
`Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isZero_higherDirectImage_of_isFinite`.

## References

* [Stacks Project, Tag 01Y6](https://stacks.math.columbia.edu/tag/01Y6)
* [Stacks Project, Tag 05B3](https://stacks.math.columbia.edu/tag/05B3)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.CoherentFinite
open Stacks.AlgebraicGeometry.CoherentTFAE

universe u

namespace Stacks.AlgebraicGeometry.FinitePushforwardCoherent

variable {X Y : Scheme.{u}} (f : Y ⟶ X) (F : Y.Modules)

/-! ### The sections over an affine open -/

/-- The algebra structure of `Γ(Y, f⁻¹V)` over `Γ(X, V)` given by `f.app V`. -/
private noncomputable instance (V : X.Opens) : Algebra Γ(X, V) Γ(Y, f ⁻¹ᵁ V) :=
  (f.app V).hom.toAlgebra

/-- The `Γ(Y, f⁻¹V)`-module structure on the sections of `f_*F` over `V`. -/
private noncomputable instance (V : X.Opens) :
    Module Γ(Y, f ⁻¹ᵁ V) Γ((Scheme.Modules.pushforward f).obj F, V) :=
  inferInstanceAs (Module Γ(Y, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V))

/-- The scalar tower `Γ(X, V) → Γ(Y, f⁻¹V) → Γ(f_*F, V)`. -/
private instance (V : X.Opens) :
    IsScalarTower Γ(X, V) Γ(Y, f ⁻¹ᵁ V) Γ((Scheme.Modules.pushforward f).obj F, V) :=
  IsScalarTower.of_algebraMap_smul fun _ _ => rfl

/-- **The sections of `f_*F` over an affine open `V` form a finite `Γ(X, V)`-module**, for `f`
finite and `F` quasi-coherent of finite type.

They are the sections of `F` over the affine open `f⁻¹V`, finite over `Γ(Y, f⁻¹V)` by
[Stacks, Tag 01PB], and `Γ(Y, f⁻¹V)` is a finite `Γ(X, V)`-algebra because `f` is finite. -/
theorem finite_sections_pushforward [IsFinite f] [F.IsQuasicoherent] [F.IsFiniteType]
    {V : X.Opens} (hV : IsAffineOpen V) :
    Module.Finite Γ(X, V) Γ((Scheme.Modules.pushforward f).obj F, V) := by
  have : Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V) := f.finite_app V hV
  have : Module.Finite Γ(Y, f ⁻¹ᵁ V) Γ((Scheme.Modules.pushforward f).obj F, V) :=
    finite_sections F (hV.preimage f)
  exact Module.Finite.trans Γ(Y, f ⁻¹ᵁ V) _

/-- **The sections of `F` over `f⁻¹V` form a finite `Γ(Y, f⁻¹V)`-module** when those of `f_*F`
over the affine open `V` form a finite `Γ(X, V)`-module. This is the converse half of
[Stacks, Tag 05B3] at one affine open: finiteness descends along the finite algebra map
`Γ(X, V) → Γ(Y, f⁻¹V)` because a module finite over the base is finite over the extension. -/
theorem finite_sections_of_finite_sections_pushforward {V : X.Opens}
    (hP : Module.Finite Γ(X, V) Γ((Scheme.Modules.pushforward f).obj F, V)) :
    Module.Finite Γ(Y, f ⁻¹ᵁ V) Γ(F, f ⁻¹ᵁ V) :=
  Module.Finite.of_restrictScalars_finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V)
    Γ((Scheme.Modules.pushforward f).obj F, V)

/-! ### Condition (4) of Stacks 01XZ for the direct image -/

/-- Finite sections over an affine open make a module a finite `tilde` there. -/
private theorem isFiniteTildeOn_of_finite_sections (G : X.Modules) (V : X.Opens)
    (hV : IsAffineOpen V) [G.IsQuasicoherent] (h : Module.Finite Γ(X, V) Γ(G, V)) :
    IsFiniteTildeOn G V hV :=
  isFiniteTildeOn_of_finite_specModule G V hV (Module.Finite.equiv (specSectionsEquiv G hV).symm)

/-- **`f_*F` is a finite `tilde` on every affine open of `X`**, for `f` finite and `F`
quasi-coherent of finite type. -/
theorem isFiniteTildeOn_pushforward [IsFinite f] [F.IsQuasicoherent] [F.IsFiniteType]
    (V : X.Opens) (hV : IsAffineOpen V) :
    IsFiniteTildeOn ((Scheme.Modules.pushforward f).obj F) V hV :=
  isFiniteTildeOn_of_finite_sections _ V hV (finite_sections_pushforward f F hV)

/-! ### Finite type -/

/-- **The direct image of a quasi-coherent module of finite type along a finite morphism is of
finite type.** This is the forward half of [Stacks, Tag 05B3], and the only input the coherence
statement of [Stacks, Tag 01Y6] needs beyond quasi-coherence. -/
theorem isFiniteType_pushforward [IsFinite f] [F.IsQuasicoherent] [F.IsFiniteType] :
    ((Scheme.Modules.pushforward f).obj F).IsFiniteType :=
  isFiniteType_of_cover_isFiniteTildeOn _ (fun V : X.affineOpens => (V : X.Opens))
    (IsOpenCover.mk (iSup_affineOpens_eq_top X)) (fun V => V.2)
    (fun V => isFiniteTildeOn_pushforward f F _ V.2)

/-- **The preimages of the affine opens of `X` cover `Y`**, for any morphism `f : Y ⟶ X`. -/
theorem isOpenCover_preimage_affineOpens :
    IsOpenCover (fun V : X.affineOpens => f ⁻¹ᵁ (V : X.Opens)) :=
  IsOpenCover.mk <| by
    rw [← Scheme.Hom.preimage_iSup, iSup_affineOpens_eq_top, Scheme.Hom.preimage_top]

/-- **[Stacks, Tag 05B3].** A quasi-coherent module on the source of a finite morphism is of
finite type if and only if its direct image is of finite type. -/
@[stacks 05B3]
theorem isFiniteType_pushforward_iff [IsFinite f] [F.IsQuasicoherent] :
    F.IsFiniteType ↔ ((Scheme.Modules.pushforward f).obj F).IsFiniteType := by
  refine ⟨fun h => isFiniteType_pushforward f F, fun h => ?_⟩
  refine isFiniteType_of_cover_isFiniteTildeOn F
    (fun V : X.affineOpens => f ⁻¹ᵁ (V : X.Opens))
    (f.iSup_preimage_eq_top (iSup_affineOpens_eq_top X))
    (fun V => V.2.preimage f) (fun V => ?_)
  have hP : Module.Finite Γ(X, (V : X.Opens))
      Γ((Scheme.Modules.pushforward f).obj F, (V : X.Opens)) :=
    finite_sections _ V.2
  have hF : Module.Finite Γ(Y, f ⁻¹ᵁ (V : X.Opens)) Γ(F, f ⁻¹ᵁ (V : X.Opens)) :=
    finite_sections_of_finite_sections_pushforward f F hP
  exact isFiniteTildeOn_of_finite_sections F _ (V.2.preimage f) hF

end Stacks.AlgebraicGeometry.FinitePushforwardCoherent

end
