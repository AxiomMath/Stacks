module

public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ReflexivePowerTransitionMulSection

/-!
# The system of [Stacks, Tag 0EBN] as a diagram indexed by `ℕ`

Let `X` be a scheme, `ℱ` an `𝒪_X`-module and `s ∈ Γ(X, ℱ)`.  The reflexive powers of `ℱ` and
the multiplications by `s` between them,

`𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯`,

are the system whose colimit is `j_*𝒪_U` in the colimit clause of [Stacks, Tag 0EBN].  They are
constructed in `ReflexivePowers.lean` as a family of objects together with a family of morphisms
between consecutive ones, which is not a diagram: nothing in this material produced a functor
`ℕ ⥤ X.Modules`, so the system had no colimit to speak of.  This file assembles the two families
into such a functor, by `CategoryTheory.Functor.ofSequence`, and does the same for the ordinary
tensor-power system `𝒪_X →ˢ ℱ →ˢ ℱ^{⊗ 2} → ⋯`.

It then upgrades the objectwise comparison `ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}` of
`ReflexivePowerTransitionRestrict.lean`, together with the commuting square at each `n` proved in
`ReflexivePowerTransitionMulSection.lean`, into an isomorphism **of diagrams**: over an open `V`
on which `ℱ` is invertible, the system of [Stacks, Tag 0EBN] *is* the tensor-power system of the
invertible module `ℱ|_V` and the restricted section, which is the system [Stacks, Tag 01PW] is
about.  Being an isomorphism of diagrams rather than a family of isomorphisms, it transports
colimits, which a family of isomorphisms does not.

## Main definitions

* `Stacks.AlgebraicGeometry.ReflexivePowers.reflexivePowerSystem`: the system of
  [Stacks, Tag 0EBN] as a functor `ℕ ⥤ X.Modules`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.tensorPowerSystem`: the ordinary tensor-power system
  as a functor `ℕ ⥤ X.Modules`.
* `Stacks.AlgebraicGeometry.ReflexivePowers.restrictPowerSystemIso`: the isomorphism of diagrams
  `(system of Tag 0EBN)|_V ≅ (tensor-power system of ℱ|_V and s|_V)`.

## Implementation notes

`CategoryTheory.Functor.ofSequence` takes the morphisms out of `n` into `n + 1` and defines the
action on a general `n ⟶ m` by composing; its only computation rule is
`CategoryTheory.Functor.ofSequence_map_homOfLE_succ`, at the successor steps, which is why the
two `..._map_succ` lemmas below are the interface and the general action is never unfolded.
Dually `CategoryTheory.NatTrans.ofSequence` asks for naturality only at the successor steps, and
that is exactly the square `restrict_reflexivePowerTransition_comp_restrictPowerIso_hom'` of
`ReflexivePowerTransitionMulSection.lean` proves.

The `n = 0` term is the one that is not on the nose: `reflexivePower F 0` is
`SheafOfModules.unit X.ringCatSheaf` and `tensorPower (ℱ|_V) 0` is the unit of `V`, and the
comparison between them is `AlgebraicGeometry.Scheme.Modules.restrictUnitIso V.ι`, the
identification `𝒪_X|_V ≅ 𝒪_V`, not an equality; and the transition out of degree `0` is not
multiplication by anything but the morphism `𝒪 ⟶ ℱ` determined by the section.  Both are already
handled inside `restrictPowerIso` and the square above, so they cost nothing here.

## References

* [Stacks Project, Tag 0EBN](https://stacks.math.columbia.edu/tag/0EBN)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public section

noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexivePowers

variable {X : Scheme.{u}}

/-! ### The two systems as diagrams -/

/-- **The system `𝒪_X →ˢ ℱ →ˢ ℱ^{[2]} →ˢ ⋯` of [Stacks, Tag 0EBN] as a functor `ℕ ⥤ X.Modules`.**
Its value at `n` is the `n`-th reflexive power and its successor maps are the transitions
`reflexivePowerTransition F s n`, multiplication by `s` into the reflexive hull. -/
def reflexivePowerSystem (F : X.Modules) (s : F.sections) : CategoryTheory.Functor ℕ X.Modules :=
  Functor.ofSequence (reflexivePowerTransition F s)

/-- The value of the system at `n` is the `n`-th reflexive power. -/
@[simp]
theorem reflexivePowerSystem_obj (F : X.Modules) (s : F.sections) (n : ℕ) :
    (reflexivePowerSystem F s).obj n = reflexivePower F n := rfl

/-- The successor step of the system is the transition map. -/
@[simp]
theorem reflexivePowerSystem_map_succ (F : X.Modules) (s : F.sections) (n : ℕ) :
    (reflexivePowerSystem F s).map (homOfLE (Nat.le_add_right n 1)) =
      reflexivePowerTransition F s n :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-- **The ordinary tensor-power system `𝒪_X →ˢ ℱ →ˢ ℱ^{⊗ 2} → ⋯` as a functor `ℕ ⥤ X.Modules`.**
This is the system [Stacks, Tag 01PW] is about, for an invertible `ℱ`. -/
def tensorPowerSystem (F : X.Modules) (s : F.sections) : CategoryTheory.Functor ℕ X.Modules :=
  Functor.ofSequence (tensorPowerTransition F s)

/-- The value of the tensor-power system at `n` is the `n`-th tensor power. -/
@[simp]
theorem tensorPowerSystem_obj (F : X.Modules) (s : F.sections) (n : ℕ) :
    (tensorPowerSystem F s).obj n = tensorPower F n := rfl

/-- The successor step of the tensor-power system is multiplication by `s`. -/
@[simp]
theorem tensorPowerSystem_map_succ (F : X.Modules) (s : F.sections) (n : ℕ) :
    (tensorPowerSystem F s).map (homOfLE (Nat.le_add_right n 1)) = tensorPowerTransition F s n :=
  Functor.ofSequence_map_homOfLE_succ _ n

/-! ### The two systems agree over an open where `ℱ` is invertible -/

section Restrict

variable [IsIntegral X] [IsLocallyNoetherian X] (F : X.Modules) (V : X.Opens)
    (hF : _root_.SheafOfModules.IsCoherent F) [Nonempty V.toScheme]
    (hV : Stacks.SheafOfModules.IsInvertible V.toScheme.sheaf.obj
      V.toScheme.ringCatSheaf.property ((Scheme.Modules.restrictFunctor V.ι).obj F))
    (s : F.sections)

/-- The comparison `ℱ^{[n]}|_V ≅ (ℱ|_V)^{⊗ n}` of `restrictPowerIso`, assembled into a morphism
of diagrams.  Naturality at the successor steps is
`restrict_reflexivePowerTransition_comp_restrictPowerIso_hom'`, and
`CategoryTheory.NatTrans.ofSequence` asks for nothing else. -/
def restrictPowerSystemHom :
    reflexivePowerSystem F s ⋙ Scheme.Modules.restrictFunctor V.ι ⟶
      tensorPowerSystem ((Scheme.Modules.restrictFunctor V.ι).obj F) (restrictSection V F s) :=
  NatTrans.ofSequence (fun n => (restrictPowerIso F V hF hV n).hom) fun n => by
    rw [Functor.comp_map, reflexivePowerSystem_map_succ, tensorPowerSystem_map_succ]
    exact restrict_reflexivePowerTransition_comp_restrictPowerIso_hom' F V hF hV s n

/-- Each component of `restrictPowerSystemHom` is the comparison at that stage. -/
@[simp]
theorem restrictPowerSystemHom_app (n : ℕ) :
    (restrictPowerSystemHom F V hF hV s).app n = (restrictPowerIso F V hF hV n).hom := rfl

/-- **Over an open `V` on which `ℱ` is invertible the system of [Stacks, Tag 0EBN] is isomorphic,
as a diagram, to the tensor-power system of `ℱ|_V` and `s|_V`.**  Each component is an
isomorphism, so the morphism of diagrams is one. -/
def restrictPowerSystemIso :
    reflexivePowerSystem F s ⋙ Scheme.Modules.restrictFunctor V.ι ≅
      tensorPowerSystem ((Scheme.Modules.restrictFunctor V.ι).obj F) (restrictSection V F s) :=
  haveI : ∀ n : ℕ, IsIso ((restrictPowerSystemHom F V hF hV s).app n) := fun n =>
    inferInstanceAs (IsIso (restrictPowerIso F V hF hV n).hom)
  haveI : IsIso (restrictPowerSystemHom F V hF hV s) :=
    NatIso.isIso_of_isIso_app _
  asIso (restrictPowerSystemHom F V hF hV s)

/-- The isomorphism of diagrams is the comparison at each stage. -/
@[simp]
theorem restrictPowerSystemIso_hom_app (n : ℕ) :
    (restrictPowerSystemIso F V hF hV s).hom.app n = (restrictPowerIso F V hF hV n).hom := rfl

end Restrict

end Stacks.AlgebraicGeometry.ReflexivePowers

end

end
