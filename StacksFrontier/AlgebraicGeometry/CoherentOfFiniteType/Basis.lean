module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherenceClosure
public import StacksFrontier.AlgebraicGeometry.ProperMapping.CoherenceClosure

/-!
# Coherence can be checked on a basis of opens

Coherence of a sheaf of modules `M` on a ringed space quantifies over *every* open `U` and every
finite family of sections of `M` over `U`: it asks that the module of relations among them be of
finite type. Every proof that a specific sheaf is coherent instead produces such a statement only
over the members of some *basis* of the topology — over the affine opens of a scheme, say. This
file bridges the two.

The content is that the conclusion, being of finite type, is local on the base, so the
quantification over all opens may be refined to a basis. Two lemmas carry it. The first is that
being of finite type over an object of a site passes to objects below it, which is what makes the
set of objects `Z` of the slice site at `U` with `(Ker φ)|_Z` of finite type a *sieve* — the
remaining content is then that this sieve covers, which is exactly the basis hypothesis. The
second transports a finite family of sections over `U`, restricted to such a `Z`, to a family of
sections over the open `Z.left`, where the hypothesis applies; that is the slice-of-a-slice
transport, and it goes through `Stacks.SheafOfModules.overOverEquivalence`.

## Main results

* `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isFiniteType_over_of_isFiniteType_over`: on any
  site, being of finite type over an object passes to objects below it. Pinned Mathlib has
  restriction to one object (`Stacks.SheafOfModules.isFiniteType_over_of_isFiniteType`) but not
  this relative form.
* `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isFiniteType_kernel_over_of_kernel_free`: the
  relation module of a finite family of sections over `U`, restricted to an object `Z` of the
  slice site at `U`, is of finite type as soon as the relation modules of finite families of
  sections over the open `Z.left` are.
* `Stacks.AlgebraicGeometry.CoherentOfFiniteType.isFiniteType_kernel_free_of_basis` and
  `isCoherent_of_basis`: **coherence can be checked on a basis of opens.**
* `Stacks.AlgebraicGeometry.CoherentOfFiniteType.freeIsoUnit`, `isFiniteType_unit` and
  `isQuasicoherent_unit`: the structure sheaf is free on one generator, hence of finite type and
  quasi-coherent, on an arbitrary ringed space.

## Implementation notes

The coherence predicate produced is `_root_.SheafOfModules.IsCoherent`, the one of
Stacks Tag 01BW, which is the one the scheme-level statements of
[Stacks, Tag 02O5] use. Coherence is declared twice on this branch as two distinct constants with
the same two fields, and inside the `Stacks.` namespace both the unqualified name
`SheafOfModules.IsCoherent` and the dot notation resolve to the *other* one,
`Stacks.SheafOfModules.IsCoherent`; writing it unqualified here would silently state a different
theorem. The bridge between the two is
`Stacks.AlgebraicGeometry.ProperMapping.{stacksIsCoherent, isCoherent_of_stacks,
isCoherent_iff}`.

Everything is equi-universe, `X : Type u` with `RingCat.{u}`-valued structure sheaf and
`SheafOfModules.{u}`, because both coherence predicates and the whole finite-type substrate are
declared that way.

The basis hypothesis is phrased as a predicate `P : Opens X → Prop` together with the
neighbourhood-basis property, rather than as `TopologicalSpace.Opens.IsBasis`, so that the
consumer may use any convenient family — for a scheme, `IsAffineOpen` — without first packaging
it as a set of opens.

## References

* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/
@[expose] public section

open CategoryTheory Limits TopologicalSpace SheafOfModules

universe u

namespace Stacks.AlgebraicGeometry.CoherentOfFiniteType

/-! ### Finite type over an object of a site is hereditary -/

section Site

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasFiniteWidePullbacks C] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

omit [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **Being of finite type over an object of the site passes to objects below it.** -/
theorem isFiniteType_over_of_isFiniteType_over {M : SheafOfModules.{u} R} {U V : C}
    (hU : (M.over U).IsFiniteType) (f : V ⟶ U) : (M.over V).IsFiniteType := by
  have := hU
  have h1 : ((M.over U).over (Over.mk f)).IsFiniteType :=
    Stacks.SheafOfModules.isFiniteType_over_of_isFiniteType (J := J.over U) (Over.mk f)
  have h2 := Stacks.SheafOfModules.isFiniteType_overOverEquivalence_inverse_obj
    (R := R) U (Over.mk f) h1
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (Stacks.SheafOfModules.overOverIso M U (Over.mk f))

end Site

/-! ### Checking coherence on a basis of opens -/

section RingedSpace

variable {X : Type u} [TopologicalSpace X]
  {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}

/-- The relation module of finitely many sections of `M` over `U`, restricted to an object `Z`
of the slice site at `U`, is of finite type as soon as the relation modules of finite families of
sections over the open `Z.left` are. -/
theorem isFiniteType_kernel_over_of_kernel_free {M : SheafOfModules.{u} R} (U : Opens X)
    {A : Type u} [Finite A] (φ : (free A : SheafOfModules.{u} (R.over U)) ⟶ M.over U)
    (Z : Over U)
    (hZ : ∀ (B : Type u) (_ : Finite B)
      (ψ : (free B : SheafOfModules.{u} (R.over Z.left)) ⟶ M.over Z.left),
      (kernel ψ).IsFiniteType) :
    ((kernel φ).over Z).IsFiniteType := by
  have key : (kernel (φ.over Z)).IsFiniteType := by
    let e := Stacks.SheafOfModules.overOverEquivalence (R := R) U Z
    let τ : (((free A : SheafOfModules.{u} (R.over U)).over Z)).GeneratingSections :=
      (free.generatingSections (R := R.over U) A).map (overFunctor (R.over U) Z) (by rfl)
    let σ := τ.map e.inverse (Iso.refl (unit (R.over Z.left)))
    have hfin : Finite σ.I := inferInstanceAs (Finite A)
    have h1 := hZ σ.I hfin (σ.π ≫ (e.inverse.map (φ.over Z) ≫
      (Stacks.SheafOfModules.overOverIso M U Z).hom))
    have h2 : (kernel (e.inverse.map (φ.over Z) ≫
        (Stacks.SheafOfModules.overOverIso M U Z).hom)).IsFiniteType :=
      Stacks.SheafOfModules.isFiniteType_kernel_of_epi_comp σ.π _ h1
    have h3 : (kernel (e.inverse.map (φ.over Z))).IsFiniteType :=
      Stacks.SheafOfModules.isFiniteType_of_iso.{u}
        (M := kernel (e.inverse.map (φ.over Z) ≫
          (Stacks.SheafOfModules.overOverIso M U Z).hom))
        (N := kernel (e.inverse.map (φ.over Z)))
        (kernel.mapIso _ (e.inverse.map (φ.over Z)) (Iso.refl _)
          (Stacks.SheafOfModules.overOverIso M U Z).symm (by simp))
    have h4 : (e.inverse.obj (kernel (φ.over Z))).IsFiniteType :=
      Stacks.SheafOfModules.isFiniteType_of_iso.{u}
        (PreservesKernel.iso e.inverse (φ.over Z)).symm
    exact Stacks.SheafOfModules.isFiniteType_of_overOverEquivalence_inverse U Z h4
  exact Stacks.SheafOfModules.isFiniteType_of_iso.{u}
    (Stacks.SheafOfModules.overKernelIso φ Z).symm

/-- **Coherence can be checked on a basis of opens.** If `M` is of finite type and, for every
member `V` of a family of opens that is a neighbourhood basis of every point, the relations among
every finite family of sections of `M` over `V` are locally finitely generated, then `M` is
coherent. -/
theorem isFiniteType_kernel_free_of_basis {M : SheafOfModules.{u} R} (P : Opens X → Prop)
    (hbasis : ∀ (W : Opens X) (x : X), x ∈ W → ∃ V, P V ∧ x ∈ V ∧ V ≤ W)
    (hP : ∀ (V : Opens X), P V → ∀ (B : Type u) (_ : Finite B)
      (ψ : (free B : SheafOfModules.{u} (R.over V)) ⟶ M.over V), (kernel ψ).IsFiniteType)
    (U : Opens X) {A : Type u} [Finite A]
    (φ : (free A : SheafOfModules.{u} (R.over U)) ⟶ M.over U) : (kernel φ).IsFiniteType := by
  have hcover : ((Opens.grothendieckTopology X).over U).CoversTop
      (Subtype.val : { Z : Over U // ((kernel φ).over Z).IsFiniteType } → Over U) := by
    intro Y
    have hYU : Y.left ≤ U := leOfHom Y.hom
    have hS : Sieve.ofObjects (fun v : { V : Opens X // P V ∧ V ≤ U } => v.1) Y.left ∈
        Opens.grothendieckTopology X Y.left := by
      intro x hx
      obtain ⟨V, hV, hxV, hVY⟩ := hbasis Y.left x hx
      exact ⟨V, homOfLE hVY, (Sieve.mem_ofObjects_iff _ _).2
        ⟨⟨V, hV, hVY.trans hYU⟩, ⟨𝟙 V⟩⟩, hxV⟩
    refine ((Opens.grothendieckTopology X).over U).superset_covering ?_
      ((Over.forget U).cover_lift ((Opens.grothendieckTopology X).over U)
        (Opens.grothendieckTopology X) hS)
    intro Z g hg
    obtain ⟨i, ⟨h⟩⟩ := (Sieve.mem_ofObjects_iff _ ((Over.forget U).map g)).1 hg
    refine (Sieve.mem_ofObjects_iff _ g).2 ⟨⟨Z, ?_⟩, ⟨𝟙 Z⟩⟩
    refine isFiniteType_over_of_isFiniteType_over
      (isFiniteType_kernel_over_of_kernel_free U φ (Over.mk (homOfLE i.2.2))
        fun B hB ψ => hP i.1 i.2.1 B hB ψ) (Over.homMk h ?_)
    apply Subsingleton.elim
  exact Stacks.SheafOfModules.LocalKernel.isFiniteType_of_coversTop (kernel φ)
    Subtype.val hcover fun i => i.2

/-- **Coherence can be checked on a basis of opens.** If `M` is of finite type and, for every
member `V` of a family of opens that is a neighbourhood basis of every point, the relations among
every finite family of sections of `M` over `V` are locally finitely generated, then `M` is
coherent. -/
theorem isCoherent_of_basis (M : SheafOfModules.{u} R) [M.IsFiniteType] (P : Opens X → Prop)
    (hbasis : ∀ (W : Opens X) (x : X), x ∈ W → ∃ V, P V ∧ x ∈ V ∧ V ≤ W)
    (hP : ∀ (V : Opens X), P V → ∀ (B : Type u) (_ : Finite B)
      (ψ : (free B : SheafOfModules.{u} (R.over V)) ⟶ M.over V), (kernel ψ).IsFiniteType) :
    _root_.SheafOfModules.IsCoherent M where
  isFiniteType := inferInstance
  kernel_isFiniteType U _A hA φ :=
    have := hA
    isFiniteType_kernel_free_of_basis P hbasis hP U φ

/-! ### The structure sheaf is free on one generator -/

/-- **The structure sheaf is the free module on a one-element index type.** This is
`AlgebraicGeometry.structureSheafFreeIso`, which has the same body, over an arbitrary ringed
space rather than over a scheme. -/
noncomputable abbrev freeIsoUnit : free (R := R) PUnit.{u + 1} ≅ unit.{u} R :=
  coproductUniqueIso fun _ : PUnit.{u + 1} => unit.{u} R

/-- **The structure sheaf is of finite type**: it is generated by the section `1`. This is
`AlgebraicGeometry.structureSheaf_isFiniteType` over an arbitrary ringed space. -/
instance isFiniteType_unit : (unit.{u} R).IsFiniteType :=
  Stacks.SheafOfModules.isFiniteType_of_iso.{u} freeIsoUnit

/-- **The structure sheaf is quasi-coherent.** This is
`Stacks.AlgebraicGeometry.AffinePushforward.isQuasicoherent_unit` over an arbitrary ringed
space. -/
theorem isQuasicoherent_unit : (unit.{u} R).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent R).prop_of_iso freeIsoUnit inferInstance

end RingedSpace

end Stacks.AlgebraicGeometry.CoherentOfFiniteType

end
