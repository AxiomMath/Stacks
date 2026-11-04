module

public import Mathlib.Algebra.Module.GradedModule
public import StacksFrontier.AlgebraicGeometry.GradedLocalization.ModuleMaps
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Basic

/-!
# The graded module of sections of a sheaf-level graded module

Over a scheme `S` with a sheaf-level graded `𝒪_S`-algebra `A`
(`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra`), a sheaf of graded
`A`-modules is an integer-indexed family of quasi-coherent `𝒪_S`-modules with an `𝒪_S`-bilinear
action of the homogeneous pieces of `A` raising degrees additively. This file introduces that
datum and builds, for every open `U` of `S`, the graded module of its sections over `U`: the
external direct sum `⨁ n : ℤ, Γ(M.piece n, U)`, its internal grading by additive subgroups, the
action of the graded ring of sections of `A`, and the restriction maps.

This is the module-side counterpart of
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionRing`, and it is built in
the same shape: the carrier is the external direct sum, the internal grading is the family of
ranges of the summand inclusions `DirectSum.of`, and the action comes from
`DirectSum.Gmodule`.

## Main definitions

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule`: a sheaf of graded modules
  over a sheaf-level graded `𝒪_S`-algebra, with every homogeneous piece quasi-coherent.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule.sectionModulePieces`: the
  homogeneous sections of degree `n` over an open.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule.sectionModule`: their direct
  sum, `⨁ n : ℤ, Γ(M.piece n, U)`.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule.sectionModuleGrading`: the
  internal grading, by the ranges of the inclusions of the homogeneous summands.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule.resPiece`, `res` and `resₛₗ`:
  restriction of homogeneous sections along an inclusion of opens, of the graded modules of
  sections as an additive map, and the same as a semilinear map over the restriction of the
  graded rings of sections.

## Main results

* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule.instGmodule` and `instModule`:
  the homogeneous sections form a graded module over the homogeneous sections of `A`, hence
  their direct sum is a module over the graded ring of sections `A.sectionRing U`.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule.of_smul_of`: the action on the
  homogeneous summands is the action of the sheaf-level datum. This equation is what makes the
  module structure usable.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule.sectionModuleDecomposition`:
  the module of sections is the direct sum of its homogeneous parts.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule.instGradedSMul`: the action of
  `A.sectionRing U` respects the two internal gradings. Together with the decomposition this is
  what `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf` consumes alongside the
  graded ring `A.grading U`.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule.res_smul`: restriction is
  semilinear over `A.resRingHom`, which is the restriction underlying the graded ring
  homomorphism `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.res`.
* `Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedModule.res_id` and `res_comp`:
  restriction is functorial.

## Implementation notes

**Two index types.** The graded ring of sections of `A` is indexed by `ℕ`, as
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionPieces` is, while the
module of sections is indexed by `ℤ`, as in the source: a graded module over a nonnegatively
graded algebra has components in every degree. `DirectSum.Gmodule`
supports exactly this through a `VAdd ιA ιM`, and the action used here is the repository's
`Stacks.GradedLocalization.instVAddNatInt`, which is `n +ᵥ i = (n : ℤ) + i`. Mathlib supplies no
`VAdd ℕ ℤ`.

The spellings `((i + j : ℕ) : ℤ)` and `(i : ℤ) + (j : ℤ)` are definitionally equal, since
`Nat.cast` into `ℤ` is `Int.ofNat` and `Int.add` reduces on constructors, so the degree
bookkeeping of the action is confined to the two `GradedMonoid` laws, where the index equality
has to be named for `Sigma.ext`; nowhere else is a transport needed, and no `eqToHom` appears.

**Where the action comes from.** The homogeneous action is one `SheafBilinearMap` per pair of
degrees, so biadditivity in both variables is already the additivity of the two `AddMonoidHom`
layers of `SheafBilinearMap.app`: the four distributivity fields of `DirectSum.Gmodule` are
`map_add` and `map_zero`. Only the unit and associativity laws are data of the structure, and
they are heterogeneous equalities for the same reason as in `SheafGradedAlgebra`: their two
sides live in pieces of degrees that agree only propositionally.

**Quasi-coherence is a field, not a side condition.** `SheafGradedAlgebra` bundles
quasi-coherence of its homogeneous pieces, and the module datum here does the same. The
predicate `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.IsQuasicoherentGradedModule` says the
same thing one level up, for the site-level `SheafOfModules.GradedModule`, which has no
presentation by section rings; it does not apply to this datum, and bundling costs nothing here.
Nothing in this file uses quasi-coherence — it is carried because the degreewise localization
property of the sections, which is what the comparison on the affine charts of relative `Proj`
rests on, needs it, exactly as `SheafGradedAlgebra.isLocalization_strHom` needs it on the algebra
side.

**Transparency.** `sectionModulePieces`, `sectionModule` and `sectionModuleGrading` are
`abbrev`s, for the reasons recorded for
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.sectionPieces` and `grading`:
`sectionModulePieces` must be reducible for the `AddCommGroup` and `Module` instances on
`Γ(M.piece n, U)` to be found at the graded-module fields, and `sectionModuleGrading` must be
reducible for `simp` to see the summand inclusions inside
`DirectSum.Decomposition.ofAddHom`.

**A hazard for the consumers.** `AlgebraicGeometry.ProjectiveSpectrum.Proj.associatedModuleSheaf`
takes `[SetLike.GradedSMul 𝒜 𝒨]` with its own *file-local* `VAdd ℕ ℤ` baked into that binder, so
the instance is not the one carried by `instGradedSMul`. The two are definitionally equal and a
term application goes through; a consumer that meets a `synthInstanceFailed` there should pass the
`GradedSMul` explicitly rather than reach for a transparency option.

**Universes.** Monomorphic in the scheme universe `u`, as the algebra side is: the homogeneous
pieces are `S.Modules`, whose sections live in `Type u`.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 0FQZ](https://stacks.math.columbia.edu/tag/0FQZ)
* [Stacks Project, Tag 01O7](https://stacks.math.columbia.edu/tag/01O7)

## Not done here

No Stacks tag is carried. This file is the input vocabulary for the sheaf attached to a graded
module on relative `Proj`; the assertions of Tag 01O7 are about that sheaf, and none of them is
stated here.

Nothing is proved about the degreewise localization property of the module of sections, the
analogue of `SheafGradedAlgebra.isLocalization_strHom`, and nothing compares the module of
sections over an open with the module of sections over a basic open inside it. Morphisms of
sheaf-level graded modules, which Tag 0FQZ also defines, are not introduced.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite DirectSum
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

universe u

variable {S : Scheme.{u}}

/-- A sheaf of graded modules over a sheaf-level graded `𝒪_S`-algebra `A`, given as a family of
sheaves of modules indexed by `ℤ` with an `𝒪_S`-bilinear action of the homogeneous pieces of
`A` that adds degrees, and with every piece quasi-coherent.

This is the sheaf-level module datum of Tag 0FQZ, in the form that Tag 01O7 quantifies over. -/
public structure SheafGradedModule (A : SheafGradedAlgebra S) where
  /-- The homogeneous piece in each degree. -/
  piece : ℤ → S.Modules
  /-- The action of a homogeneous local section of `A` on a homogeneous local section. -/
  smul (i j : ℤ) : SheafBilinearMap (A.piece i) (piece j) (piece (i + j))
  /-- The unit of `A` acts as the identity. -/
  one_smul (j : ℤ) (U : S.Opens) (x : Γ(piece j, U)) :
    HEq ((smul 0 j).app U (A.one U) x) x
  /-- The action is associative against the multiplication of `A`. -/
  mul_smul (i j k : ℤ) (U : S.Opens) (a : Γ(A.piece i, U)) (b : Γ(A.piece j, U))
      (x : Γ(piece k, U)) :
    HEq ((smul (i + j) k).app U ((A.mul i j).app U a b) x)
      ((smul i (j + k)).app U a ((smul j k).app U b x))
  /-- Every homogeneous piece is quasi-coherent. -/
  isQuasicoherent (n : ℤ) : (piece n).IsQuasicoherent

namespace SheafGradedModule

attribute [instance] isQuasicoherent

section Sections

variable {A : SheafGradedAlgebra S} (M : SheafGradedModule A) (U : S.Opens)

/-- The degree-`n` homogeneous sections of `M` over an open. -/
public abbrev sectionModulePieces (n : ℤ) : Type u := Γ(M.piece n, U)

/-- The graded module of sections of `M` over an open: the direct sum of the homogeneous
pieces, over all integer degrees. -/
public abbrev sectionModule : Type u := ⨁ n : ℤ, M.sectionModulePieces U n

/-! ### The action of the graded ring of sections -/

/-- The homogeneous sections of `A` act on the homogeneous sections of `M`: a degree-`i` section
of `A` and a degree-`j` section of `M` over the same open give the degree-`i + j` section obtained
from the sheaf-level homogeneous action `M.smul i j`. -/
public noncomputable instance instGSMul :
    GradedMonoid.GSMul (A.sectionPieces U) (M.sectionModulePieces U) :=
  ⟨fun {i j} a x => (M.smul (i : ℤ) j).app U a x⟩

/-- The graded action of a degree-`i` section `a` of `A` on a degree-`j` section `x` of `M` over
`U` is the sheaf-level homogeneous action `(M.smul (i : ℤ) j).app U a x`. -/
public theorem gSMul_def {i : ℕ} {j : ℤ} (a : A.sectionPieces U i)
    (x : M.sectionModulePieces U j) :
    (GradedMonoid.GSMul.smul a x : M.sectionModulePieces U (i +ᵥ j)) =
      (M.smul (i : ℤ) j).app U a x := rfl

/-- **The homogeneous sections of `M` form a graded module over the homogeneous sections of
`A`.** The unit and associativity laws are the structure's own; biadditivity is the additivity
of the two layers of the homogeneous action. -/
public noncomputable instance instGmodule :
    DirectSum.Gmodule (A.sectionPieces U) (M.sectionModulePieces U) :=
  { M.instGSMul U with
    one_smul := fun x => Sigma.ext (Int.zero_add x.1) (M.one_smul _ U x.2)
    mul_smul := fun a a' x =>
      Sigma.ext (show ((a.1 + a'.1 : ℕ) : ℤ) + x.1 = (a.1 : ℤ) + ((a'.1 : ℤ) + x.1) by
        push_cast; ring) (M.mul_smul (a.1 : ℤ) (a'.1 : ℤ) x.1 U a.2 a'.2 x.2)
    smul_add := fun _ _ _ => map_add _ _ _
    smul_zero := fun _ => map_zero _
    add_smul := fun _ _ _ => by rw [gSMul_def, map_add]; rfl
    zero_smul := fun _ => by rw [gSMul_def, map_zero]; rfl }

/-- **The graded module of sections of `M` over an open is a module over the graded ring of
sections of `A` over that open.** -/
public noncomputable instance instModule : Module (A.sectionRing U) (M.sectionModule U) :=
  inferInstance

/-- **The action on the homogeneous summands is the homogeneous action of the sheaf-level
datum.** This is the equation that characterizes the module structure. -/
public theorem of_smul_of {i : ℕ} {j : ℤ} (a : A.sectionPieces U i)
    (x : M.sectionModulePieces U j) :
    DirectSum.of (A.sectionPieces U) i a • DirectSum.of (M.sectionModulePieces U) j x =
      DirectSum.of (M.sectionModulePieces U) ((i : ℤ) + j) ((M.smul (i : ℤ) j).app U a x) :=
  DirectSum.Gmodule.of_smul_of _ _ a x

/-! ### The internal grading -/

/-- The degree-`n` part of the module of sections, as an additive subgroup: the range of the
inclusion of the degree-`n` summand. -/
public noncomputable abbrev sectionModuleGrading (n : ℤ) : AddSubgroup (M.sectionModule U) :=
  (DirectSum.of (M.sectionModulePieces U) n).range

/-- The additive subgroups of the module of sections form an `AddSubgroupClass`.

Named for the reason recorded for
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.instAddSubgroupClass`: this
instance is an argument of the associated sheaf on a chart of relative `Proj`, where it appears
at very many positions inside one term, and an anonymous instance is lifted into a
per-declaration auxiliary, so two spellings of one term differ at every one of them. -/
public noncomputable instance instAddSubgroupClass :
    AddSubgroupClass (AddSubgroup (M.sectionModule U)) (M.sectionModule U) := inferInstance

/-- The image of a degree-`n` homogeneous section under the inclusion of the degree-`n` summand
lies in the degree-`n` part of the module of sections. -/
public theorem of_mem_sectionModuleGrading {n : ℤ} (x : M.sectionModulePieces U n) :
    DirectSum.of (M.sectionModulePieces U) n x ∈ M.sectionModuleGrading U n := ⟨x, rfl⟩

/-- An element of the module of sections lies in its degree-`n` part if and only if it is the
image of some degree-`n` homogeneous section under the inclusion of the degree-`n` summand. -/
public theorem mem_sectionModuleGrading_iff {n : ℤ} (z : M.sectionModule U) :
    z ∈ M.sectionModuleGrading U n ↔
      ∃ x, DirectSum.of (M.sectionModulePieces U) n x = z := Iff.rfl

/-- The module of sections is the direct sum of its homogeneous parts. -/
@[instance_reducible]
public noncomputable def sectionModuleDecomposition :
    DirectSum.Decomposition (M.sectionModuleGrading U) := by
  let d : M.sectionModule U →+ ⨁ n : ℤ, M.sectionModuleGrading U n :=
    DirectSum.toAddMonoid fun n =>
      (DirectSum.of (fun n => M.sectionModuleGrading U n) n).comp
        (DirectSum.of (M.sectionModulePieces U) n).rangeRestrict
  refine DirectSum.Decomposition.ofAddHom _ d ?_ ?_
  · apply DirectSum.addHom_ext
    intro n x
    simp [d]
  · apply DirectSum.addHom_ext
    intro n y
    obtain ⟨x, hx⟩ := y
    obtain ⟨a, rfl⟩ := hx
    simp [d]
    rfl

/-- **The action of the graded ring of sections respects the two internal gradings**: a
degree-`i` section of `A` carries the degree-`j` part of the module of sections into its
degree-`i + j` part. -/
public instance instGradedSMul :
    SetLike.GradedSMul (A.grading U) (M.sectionModuleGrading U) where
  smul_mem := by
    rintro i j a x ⟨a, rfl⟩ ⟨x, rfl⟩
    exact ⟨_, (DirectSum.Gmodule.of_smul_of _ _ a x).symm⟩

end Sections

/-! ### Restriction -/

section Restriction

variable {A : SheafGradedAlgebra S} (M : SheafGradedModule A) {U V : S.Opens}

/-- Restriction of homogeneous sections of degree `n` along an inclusion of opens. -/
public noncomputable def resPiece (h : U ≤ V) (n : ℤ) :
    M.sectionModulePieces V n →+ M.sectionModulePieces U n where
  toFun := (M.piece n).presheaf.map (homOfLE h).op
  map_zero' := map_zero _
  map_add' := map_add _

/-- Restriction of a degree-`n` homogeneous section along `U ≤ V` is the restriction map of the
presheaf of the degree-`n` piece along the inclusion `U ⟶ V`. -/
public theorem resPiece_apply (h : U ≤ V) (n : ℤ) (x : M.sectionModulePieces V n) :
    M.resPiece h n x = (M.piece n).presheaf.map (homOfLE h).op x := rfl

/-- Restriction of the graded modules of sections along an inclusion of opens, as an additive
map. -/
public noncomputable def res (h : U ≤ V) : M.sectionModule V →+ M.sectionModule U :=
  DirectSum.toAddMonoid fun n =>
    (DirectSum.of (M.sectionModulePieces U) n).comp (M.resPiece h n)

/-- Restriction of the graded modules of sections sends the image of a degree-`n` homogeneous
section `x` over `V` under the summand inclusion to the image of its restriction
`M.resPiece h n x` under the degree-`n` summand inclusion over `U`. -/
public theorem res_of (h : U ≤ V) {n : ℤ} (x : M.sectionModulePieces V n) :
    M.res h (DirectSum.of (M.sectionModulePieces V) n x) =
      DirectSum.of (M.sectionModulePieces U) n (M.resPiece h n x) :=
  DirectSum.toAddMonoid_of _ n x

/-- Restriction preserves the internal grading. -/
public theorem res_mem_sectionModuleGrading (h : U ≤ V) {n : ℤ} {z : M.sectionModule V}
    (hz : z ∈ M.sectionModuleGrading V n) : M.res h z ∈ M.sectionModuleGrading U n := by
  obtain ⟨x, rfl⟩ := hz
  exact ⟨_, (M.res_of h x).symm⟩

/-- **Restriction of the graded modules of sections is semilinear over restriction of the graded
rings of sections.** On the homogeneous summands this is the naturality of the homogeneous
action. -/
public theorem res_smul (h : U ≤ V) (w : A.sectionRing V) (z : M.sectionModule V) :
    M.res h (w • z) = A.resRingHom h w • M.res h z := by
  induction w using DirectSum.induction_on with
  | zero => rw [zero_smul, map_zero, map_zero, zero_smul]
  | of i a =>
    induction z using DirectSum.induction_on with
    | zero => rw [smul_zero, map_zero, smul_zero]
    | of j x =>
      rw [DirectSum.Gmodule.of_smul_of, M.res_of, A.resRingHom_of, M.res_of,
        DirectSum.Gmodule.of_smul_of]
      exact congrArg (DirectSum.of (M.sectionModulePieces U) (i +ᵥ j))
        ((M.smul (i : ℤ) j).naturality h a x)
    | add z z' hz hz' => rw [smul_add, map_add, hz, hz', map_add, smul_add]
  | add w w' hw hw' => rw [add_smul, map_add, hw, hw', map_add, add_smul]

/-- Restriction of the graded modules of sections, as a semilinear map over the restriction
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.res` of the graded rings of
sections. -/
public noncomputable def resₛₗ (h : U ≤ V) :
    M.sectionModule V →ₛₗ[A.resRingHom h] M.sectionModule U where
  toFun := M.res h
  map_add' := map_add _
  map_smul' := M.res_smul h

/-- The semilinear restriction map agrees, as a function, with the additive restriction map
`res`. -/
public theorem resₛₗ_apply (h : U ≤ V) (z : M.sectionModule V) :
    M.resₛₗ h z = M.res h z := rfl

end Restriction

variable {A : SheafGradedAlgebra S} (M : SheafGradedModule A)

/-- Restriction along the identity is the identity. -/
public theorem res_id (U : S.Opens) : M.res (le_refl U) = AddMonoidHom.id (M.sectionModule U) := by
  refine DirectSum.addHom_ext fun n x => ?_
  rw [M.res_of, AddMonoidHom.id_apply, M.resPiece_apply,
    show (homOfLE (le_refl U)).op = 𝟙 (op U) from rfl]
  simp

/-- Restriction is functorial. -/
public theorem res_comp {U V W : S.Opens} (hUV : U ≤ V) (hVW : V ≤ W) :
    M.res (hUV.trans hVW) = (M.res hUV).comp (M.res hVW) := by
  refine DirectSum.addHom_ext fun n x => ?_
  rw [M.res_of, AddMonoidHom.coe_comp, Function.comp_apply, M.res_of, M.res_of]
  congr 1
  rw [M.resPiece_apply, M.resPiece_apply, M.resPiece_apply, ← Functor.map_comp_apply]
  rfl

end SheafGradedModule

end Stacks.AlgebraicGeometry.RelativeProjBridge

end
