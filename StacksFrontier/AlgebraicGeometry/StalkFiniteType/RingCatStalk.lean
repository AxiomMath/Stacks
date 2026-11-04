module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkFreeCover
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk

/-!
# The `RingCat`-valued and `CommRingCat`-valued stalks of the structure sheaf, and Tag 0B8J

A sheaf of modules on a scheme `X` is a sheaf of modules over `X.ringCatSheaf`, a sheaf valued
in `RingCat`, so the base ring over which a stalk of such a sheaf is naturally a module is the
`RingCat`-valued stalk `TopCat.Presheaf.stalk X.ringCatSheaf.obj x`. But the local ring of the
scheme is the `CommRingCat`-valued stalk `X.presheaf.stalk x`, and that is the base ring used by
Stacks Tag 01C9 and by `StacksFrontier/AlgebraicGeometry/StalkFreeBridge/`. These are two
filtered colimits taken in two different categories; a module, a basis or a linear equivalence
over one of them is not one over the other.

The consequence that motivates this file: Stacks Tag 0B8J,
`Stacks.SheafOfModules.nonempty_over_iso_free_of_stalk_basis`, states its hypothesis as a
`Module.Basis` over the `RingCat`-valued stalk, so a basis produced in the local-ring vocabulary
cannot be fed to it directly.

## Main results

* `Stacks.StalkFiniteType.comm_smul_eq`: the two stalk actions on the stalk of a presheaf of
  modules agree through `SemilinearStalk.commStalkRingEquiv`. This restates
  `SemilinearStalk.comm_smul_eq`, whose statement is pinned to `TopCat.{0}` and therefore cannot
  be applied on a `Scheme.{u}`; the proof here is that one, with the universe left free.
* `Stacks.StalkFiniteType.ringCatStalkRingEquiv`: the comparison ring equivalence at a scheme,
  from the `RingCat`-valued stalk of `X.ringCatSheaf` to the local ring `𝒪_{X,x}`.
* `Stacks.StalkFiniteType.basisRingCatStalk`: transport of a `Module.Basis` of a stalk from the
  local-ring base to the `RingCat`-valued base, along that comparison.
* `Stacks.StalkFiniteType.exists_over_iso_free_of_stalk_basis`: **Tag 0B8J driven from a basis
  over the local ring.** A finitely presented sheaf of modules on a scheme whose stalk at `x` is
  free on a finite basis *over `𝒪_{X,x}`* is isomorphic to a free sheaf of modules on a
  neighbourhood of `x`.

## Implementation notes

`SemilinearStalk.commStalkIso` and `SemilinearStalk.commStalkRingEquiv` are already universe
polymorphic and are the named form of the comparison
`preservesColimitIso (forget₂ CommRingCat RingCat)`; nothing new is needed there. What was
missing at `Scheme.{u}` is the compatibility of the two *module* actions: that statement mentions
a `PresheafOfModules`, and in `SemilinearStalk.comm_smul_eq` all four of its universe parameters
elaborated to `0`, so the lemma speaks only about spaces in `Type`. `comm_smul_eq` below is the
same proof with `X : TopCat.{u}` written out.

The direction of the transport is `Module.Basis.mapCoeffs (ringCatStalkRingEquiv x).symm`: the
basis one has is over the local ring and the basis Tag 0B8J wants is over the `RingCat`-valued
stalk.

## References

* [Stacks Project, Tag 0B8J](https://stacks.math.columbia.edu/tag/0B8J)
* [Stacks Project, Tag 01C9](https://stacks.math.columbia.edu/tag/01C9)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace Stacks.StalkFiniteType

section Space

variable {T : TopCat.{u}} (R : TopCat.Presheaf CommRingCat.{u} T) (x : T)

/-- On germs the `CommRingCat`-valued and `RingCat`-valued stalk actions agree. This is
`SemilinearStalk.comm_smul_germ` with the universe left free. -/
theorem comm_smul_germ (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (U : Opens T) (hx : x ∈ U) (r : R.obj (op U)) (m : M.obj (op U)) :
    R.germ U x hx r • TopCat.Presheaf.germ M.presheaf U x hx m
      = TopCat.Presheaf.germ (C := RingCat) (R ⋙ forget₂ CommRingCat RingCat) U x hx r •
        TopCat.Presheaf.germ M.presheaf U x hx m := by
  rw [← PresheafOfModules.germ_smul M x U hx r m]
  exact PresheafOfModules.germ_ringCat_smul M x U hx r m

/-- **The `CommRingCat` and `RingCat` stalk actions agree** through
`SemilinearStalk.commStalkRingEquiv`.

This is `SemilinearStalk.comm_smul_eq`, whose statement elaborated all of its universe
parameters to `0` — it mentions a `PresheafOfModules`, unlike `commStalkRingEquiv` itself, which
is polymorphic — and so cannot be applied on a scheme in `Scheme.{u}`. The proof is the same
germ reduction. -/
theorem comm_smul_eq (M : PresheafOfModules.{u} (R ⋙ forget₂ CommRingCat RingCat))
    (s : ToType (TopCat.Presheaf.stalk (C := RingCat)
      (R ⋙ forget₂ CommRingCat RingCat) x))
    (m : ToType (TopCat.Presheaf.stalk M.presheaf x)) :
    SemilinearStalk.commStalkRingEquiv R x s • m = s • m := by
  obtain ⟨U₁, hU₁, r₀, hr⟩ :=
    TopCat.Presheaf.exists_germ_eq (R ⋙ forget₂ CommRingCat RingCat) s
  obtain ⟨U₂, hU₂, m₀, hm⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf m
  have hmem : x ∈ U₁ ⊓ U₂ := ⟨hU₁, hU₂⟩
  rw [← hr, ← hm, ← TopCat.Presheaf.germ_res_apply (R ⋙ forget₂ CommRingCat RingCat)
      (homOfLE (inf_le_left : U₁ ⊓ U₂ ≤ U₁)) x hmem r₀,
    ← TopCat.Presheaf.germ_res_apply M.presheaf
      (homOfLE (inf_le_right : U₁ ⊓ U₂ ≤ U₂)) x hmem m₀,
    SemilinearStalk.commStalkRingEquiv_germ]
  exact comm_smul_germ R x M (U₁ ⊓ U₂) hmem _ _

end Space

section OnAScheme

variable {X : Scheme.{u}}

/-- The comparison ring equivalence between the `RingCat`-valued stalk of `X.ringCatSheaf`, over
which the stalks of sheaves of modules on `X` are modules, and the local ring `𝒪_{X,x}`, which is
the `CommRingCat`-valued stalk. It is `SemilinearStalk.commStalkRingEquiv`, i.e.
`preservesColimitIso (forget₂ CommRingCat RingCat)`, read at a scheme. -/
def ringCatStalkRingEquiv (x : X) :
    ToType (TopCat.Presheaf.stalk X.ringCatSheaf.obj x) ≃+* ToType (X.presheaf.stalk x) :=
  SemilinearStalk.commStalkRingEquiv X.presheaf x

/-- The local ring acts on a stalk through `ringCatStalkRingEquiv` as the `RingCat`-valued stalk
does. This is the hypothesis `Module.Basis.mapCoeffs` asks for. -/
theorem ringCatStalk_smul_eq (M : X.Modules) (x : X)
    (c : ToType (X.presheaf.stalk x))
    (m : ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :
    (ringCatStalkRingEquiv x).symm c • m = c • m :=
  (comm_smul_eq X.presheaf x M.val ((ringCatStalkRingEquiv x).symm c) m).symm.trans
    (congrArg (fun y : ToType (X.presheaf.stalk x) => y • m)
      ((ringCatStalkRingEquiv x).apply_symm_apply c))

/-- A basis of a stalk over the local ring `𝒪_{X,x}` is a basis over the `RingCat`-valued stalk
of `X.ringCatSheaf`. This is the transport that lets the output of
`StacksFrontier/AlgebraicGeometry/StalkFreeBridge/` and of Stacks Tag 01C9 be fed to
Stacks Tag 0B8J. -/
def basisRingCatStalk {ρ : Type u} (M : X.Modules) (x : X)
    (b : Module.Basis ρ (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :
    Module.Basis ρ (ToType (TopCat.Presheaf.stalk X.ringCatSheaf.obj x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x)) :=
  b.mapCoeffs (ringCatStalkRingEquiv x).symm (ringCatStalk_smul_eq M x)

/-- **Stacks Tag 0B8J on a scheme, with the hypothesis stated over the local ring.** A finitely
presented sheaf of modules on a scheme whose stalk at `x` is free on a finite basis over
`𝒪_{X,x}` is isomorphic to a free sheaf of modules on an open neighbourhood of `x`.

Tag 0B8J itself (`Stacks.SheafOfModules.nonempty_over_iso_free_of_stalk_basis`) asks for the
basis over the `RingCat`-valued stalk of `X.ringCatSheaf`; `basisRingCatStalk` supplies it. -/
theorem exists_over_iso_free_of_stalk_basis {ρ : Type u} [Finite ρ] (M : X.Modules)
    [M.IsFinitePresentation] (x : X)
    (b : Module.Basis ρ (ToType (X.presheaf.stalk x))
      (ToType (TopCat.Presheaf.stalk M.val.presheaf x))) :
    ∃ U : X.Opens, x ∈ U ∧
      Nonempty (M.over U ≅ SheafOfModules.free (R := X.ringCatSheaf.over U) ρ) :=
  Stacks.SheafOfModules.nonempty_over_iso_free_of_stalk_basis M x (basisRingCatStalk M x b)

end OnAScheme

end Stacks.StalkFiniteType

end
