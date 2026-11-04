module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestriction

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeTensorFree
public import StacksCore.Tactic.StacksAttribute

/-!
# The powers of a locally free sheaf of modules are locally free

Let `(C, J)` be a site, `O♯` a sheaf of commutative rings on it and `F` a locally free sheaf of
modules over the underlying sheaf of rings. This file proves clause (6) of Stacks Tag 01CK: each
`Tⁿ F`, each `⋀ⁿ F` and each `Symⁿ F` is again locally free.

Local freeness of `F` is a covering `{U i}` of the terminal object together with isomorphisms
`free (γ i) ≅ F|_{U i}`, and over each member of that covering the powers are computed by two
isomorphisms, one localising the power and one computing it on a free module:

* for the two quotients, `Stacks.SheafOfModules.symmetricPowerOverIso` and
  `exteriorPowerOverIso` identify `(Symⁿ F)|_U` and `(⋀ⁿ F)|_U` with the powers computed on the
  slice site `(Over U, J.over U)`, and `symmetricPowerFreeIsoOfIsoAnyIndex` and
  `exteriorPowerFreeIsoOfIsoAnyIndex` compute those on a sheaf of modules isomorphic to a free
  one, on an **arbitrary** index type;
* for the tensor powers neither input exists, because `Tⁿ` is not a sheafified sectionwise
  construction, and both are built here by induction on the degree from
  `Stacks.TensorCoherence.tensorSheafOverIso` and `Stacks.SheafOfModules.tensorIsoFree`
  respectively — `T⁰ F` is the structure sheaf, `T¹ F` is `F`, and `Tⁿ⁺² F` is `F ⊗ Tⁿ⁺¹ F` by
  definition.

Composing them exhibits every power as free over each member of the covering, which is the
clause. **The same covering works in every degree**, and that is recorded here as
`Stacks.SheafOfModules.symmetricPowerOverFreeIsoOfIsoFree`,
`exteriorPowerOverFreeIsoOfIsoFree` and `exists_nonempty_iso_free_tensorPowerOver`, which take
`U`, the index type `γ` and the trivialisation of `F|_U` and produce a trivialisation of the
degree-`n` power for every `n` with no further shrinking. That uniformity is what Tag 01CL needs
over and above this file.

## Main definitions

* `Stacks.SheafOfModules.symmetricPowerOverFreeIsoOfIsoFree`: the degree-`n` symmetric power of
  a sheaf of modules, restricted to an object over which the module becomes free on `γ`, is free
  on the degree-`n` multidegrees in `γ`. This is the symmetric analogue of
  `Stacks.SheafOfModules.exteriorPowerOverFreeIsoOfIsoFree`.
* `Stacks.SheafOfModules.tensorPowerOverIso`: **restriction to a slice site commutes with the
  tensor powers**, the tensor analogue of `symmetricPowerOverIso` and `exteriorPowerOverIso`.

## Main results

* `Stacks.SheafOfModules.isLocallyFree_of_forall_iso_free`: a sheaf of modules that is free over
  each member of a covering of the terminal object is locally free.
* `Stacks.SheafOfModules.exists_nonempty_iso_free_tensorPower`: **every tensor power of a sheaf
  of modules isomorphic to a free one is free**, the tensor analogue of
  `exists_nonempty_iso_free_symmetricPower` and `exists_nonempty_iso_free_exteriorPower`.
* `Stacks.SheafOfModules.isLocallyFree_symmetricPower`, `isLocallyFree_exteriorPower` and
  `isLocallyFree_tensorPower`: **clause (6) of Tag 01CK**, for the symmetric, the exterior and
  the tensor powers.

## Implementation notes

**No finiteness, and no claim about ranks.** Tag 01CK clause (6) is about local freeness with
arbitrary local index sets; the fixed-finite-rank statement for the exterior power is
`Stacks.SheafOfModules.isFiniteLocallyFreeOfRank_exteriorPower` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerRank` and the finite-locally-free
statement is `AlgebraicGeometry.ProperSmoothDeRham.isFiniteLocallyFree_exteriorPower` of
`StacksFrontier.AlgebraicGeometry.DeRham.ProperSmoothFormsPerfectBaseChange`. Neither implies the
clause, because both assume the local index types finite; the clause is what is proved here, and
the input that makes it possible with no finiteness is
`Stacks.SheafOfModules.exteriorPowerFreeIsoOfIsoAnyIndex`.

**The index type of a tensor power is existentially quantified.** The recursion
`T⁰ = Π₀`, `T¹ = M`, `Tⁿ⁺² = M ⊗ Tⁿ⁺¹` produces `PUnit`, `γ`, `γ × γ`, `γ × (γ × γ)`, …, a
different nesting of products at each degree. Naming it would mean either defining that nesting
by recursion or transporting `free` along `Equiv.piFinSucc` at every step, and clause (6) asserts
nothing about which type it is, so the index is left under an `∃`. The uniformity Tag 01CL needs
survives this: the index produced depends on `U` and the trivialisation only through `γ`, so the
`∃` is instantiated once per covering member and then used in every degree.

**The decidable equality and the linear order are supplied classically.** The monomial basis of
a symmetric power needs the former on the index type and Mathlib's exterior basis needs the
latter; neither appears in the statement of the clause, so each local index type is given a
decidable equality by `classical` and a linear order by well-ordering it.

## References

* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u₁ u

namespace Stacks.SheafOfModules

section Assemble

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]

/-- **A sheaf of modules which is free over every member of a covering of the terminal object is
locally free.** The generating sections over `X i` are the images of the standard generators of
`free (K i)` under the given isomorphism, and the associated morphism out of a free sheaf of
modules is an isomorphism because it is that isomorphism composed with the identity. -/
theorem isLocallyFree_of_forall_iso_free {M : _root_.SheafOfModules.{u} R}
    {I : Type u₁} (X : I → C) (hX : J.CoversTop X) (K : I → Type u)
    (E : ∀ i, M.over (X i) ≅ _root_.SheafOfModules.free (R := R.over (X i)) (K i)) :
    M.IsLocallyFree := by
  refine ⟨⟨{ I := I
             X := X
             coversTop := hX
             generators := fun i =>
               (_root_.SheafOfModules.free.generatingSections (K i)).ofEpi (E i).inv },
    ⟨fun i => ?_⟩⟩⟩
  have h₀ : IsIso (_root_.SheafOfModules.free.generatingSections
      (R := R.over (X i)) (K i)).π := by
    rw [_root_.SheafOfModules.free.generatingSections_π]
    exact IsIso.id _
  show IsIso ((_root_.SheafOfModules.free.generatingSections (K i)).ofEpi (E i).inv).π
  rw [_root_.SheafOfModules.GeneratingSections.ofEpi_π]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₀ inferInstance

/-- A sheaf of modules `M` is locally free if, over every object where the locally free `F`
becomes free on some index type, `M` is free on some index type. -/
private theorem isLocallyFree_of_forall_iso_free_of_isLocallyFree
    {F M : _root_.SheafOfModules.{u} R} [hF : F.IsLocallyFree]
    (H : ∀ (U : C) (γ : Type u), (F.over U ≅ _root_.SheafOfModules.free (R := R.over U) γ) →
      ∃ K : Type u, Nonempty (M.over U ≅ _root_.SheafOfModules.free (R := R.over U) K)) :
    M.IsLocallyFree := by
  obtain ⟨q, hq⟩ := hF.exists_isLocallyFreeData
  choose K hK using fun i : q.I => by
    have : IsIso (q.generators i).π := hq.isIso i
    exact H (q.X i) (q.generators i).I (asIso (q.generators i).π).symm
  exact isLocallyFree_of_forall_iso_free q.X q.coversTop K fun i => (hK i).some

end Assemble

variable {C : Type u₁} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {Osharp : Sheaf J CommRingCat.{u}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}] [HasWeakSheafify J AddCommGrpCat.{u}]
  [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}]
  {F : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)}

/-- The degree-`n` symmetric power of a sheaf of modules, restricted to an object `U` over which
the module becomes free on an index type `γ`, is free on the degree-`n` multidegrees in `γ`.

This is the composite of `Stacks.SheafOfModules.symmetricPowerOverIso`, which passes from the
symmetric power computed on `(C, J)` to the one computed on the slice site over `U`, and
`Stacks.SheafOfModules.symmetricPowerFreeIsoOfIsoAnyIndex`, which computes the symmetric power
of a free module. The symmetric algebra on the slice site is taken to be the chosen one,
`SheafOfModules.algebras`, so no second package has to be supplied by the caller. -/
noncomputable def symmetricPowerOverFreeIsoOfIsoFree
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (U : C) (n : ℕ)
    (γ : Type u) [DecidableEq γ]
    (e : F.over U ≅ _root_.SheafOfModules.free (R := (Sheaf.toRingCat J Osharp).over U) γ) :
    (A.symmetricPower n).over U ≅
      _root_.SheafOfModules.free (R := (Sheaf.toRingCat J Osharp).over U)
        {d : γ →₀ ℕ | d.degree = n} :=
  let B := _root_.SheafOfModules.algebras (Osharp := Osharp.over U) (J.over U)
    (show _root_.SheafOfModules.{u} (Sheaf.toRingCat (J.over U) (Osharp.over U)) from F.over U)
  (symmetricPowerOverIso F U n A.symmetric A.symmetricGenerator A.symmetric_isSymmetricAlgebra
      B.symmetric B.symmetricGenerator B.symmetric_isSymmetricAlgebra).trans
    (symmetricPowerFreeIsoOfIsoAnyIndex (J.over U) γ n B e)

/-- **Each symmetric power of a locally free sheaf of modules is locally free.** This is clause
(6) of [Stacks, Tag 01CK] for the symmetric powers: a covering trivialising `F` with index types
`γ i` trivialises `Symⁿ F` with index types the degree-`n` multidegrees in `γ i`. -/
@[stacks 01CK "symmetric powers of a locally free module"]
theorem isLocallyFree_symmetricPower
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (n : ℕ)
    [hF : F.IsLocallyFree] : (A.symmetricPower n).IsLocallyFree := by
  classical
  refine isLocallyFree_of_forall_iso_free_of_isLocallyFree (F := F) fun U γ e => ?_
  exact ⟨_, ⟨symmetricPowerOverFreeIsoOfIsoFree A U n γ e⟩⟩

/-- **Each exterior power of a locally free sheaf of modules is locally free.** This is clause
(6) of [Stacks, Tag 01CK] for the exterior powers: a covering trivialising `F` with index types
`γ i` trivialises `⋀ⁿ F` with index types the `n`-element subsets of `γ i`. -/
@[stacks 01CK "exterior powers of a locally free module", sga "6 X 6.1" "special case"]
theorem isLocallyFree_exteriorPower
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (n : ℕ)
    [hF : F.IsLocallyFree] : (A.exteriorPower n).IsLocallyFree := by
  classical
  refine isLocallyFree_of_forall_iso_free_of_isLocallyFree (F := F) fun U γ e => ?_
  let : LinearOrder γ := IsWellOrder.linearOrder WellOrderingRel
  exact ⟨_, ⟨exteriorPowerOverFreeIsoOfIsoFree A U n γ e⟩⟩

/-! ### The tensor powers -/

omit [∀ U : C, (J.over U).HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{u}] in
/-- **Every tensor power of a sheaf of modules isomorphic to a free one is free.** The index type
is the `n`-fold product of the given one; it is left existentially quantified because the
recursion that produces it, `T⁰ = 𝒪`, `T¹ = M`, `Tⁿ⁺² = M ⊗ Tⁿ⁺¹`, produces a different nesting
of products at each step. The inductive step is
`Stacks.SheafOfModules.tensorIsoFree`, i.e. Tag 00DN for a tensor product of two free sheaves of
modules, so no presentation of a tensor power is needed. -/
theorem exists_nonempty_iso_free_tensorPower
    {M : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)} (γ : Type u)
    (e : M ≅ _root_.SheafOfModules.free (R := Sheaf.toRingCat J Osharp) γ) (n : ℕ) :
    ∃ K : Type u, Nonempty (_root_.SheafOfModules.tensorPower J M n ≅
      _root_.SheafOfModules.free (R := Sheaf.toRingCat J Osharp) K) := by
  induction n with
  | zero =>
    refine ⟨PUnit.{u + 1}, ⟨?_⟩⟩
    exact (Limits.coproductUniqueIso
      (fun _ : PUnit.{u + 1} => _root_.SheafOfModules.unit (Sheaf.toRingCat J Osharp))).symm
  | succ m ih =>
    match m, ih with
    | 0, _ => exact ⟨γ, ⟨e⟩⟩
    | (m + 1), ih =>
      obtain ⟨K, ⟨eK⟩⟩ := ih
      exact ⟨γ × K, ⟨tensorIsoFree J e eK⟩⟩

/-- **Restriction to a slice site commutes with the tensor powers.** This is the tensor analogue
of `Stacks.SheafOfModules.symmetricPowerOverIso` and `exteriorPowerOverIso`, and unlike those two
it is an induction rather than a comparison of sheafifications: the degree-zero and degree-one
pieces restrict on the nose, and the step is
`PresheafOfModules.tensorSheafBifunctorOverIso`, the statement that a tensor product of sheaves of
modules commutes with restriction. -/
noncomputable def tensorPowerOverIso
    (F : _root_.SheafOfModules.{u} (Sheaf.toRingCat J Osharp)) (U : C) : ∀ n : ℕ,
    _root_.SheafOfModules.tensorPower (J.over U)
        (show _root_.SheafOfModules.{u} (Sheaf.toRingCat (J.over U) (Osharp.over U)) from
          F.over U) n ≅
      (_root_.SheafOfModules.tensorPower J F n).over U
  | 0 => Iso.refl _
  | 1 => Iso.refl _
  | (n + 2) =>
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{max u₁ v, v, u, u, u} (Osharp.over U)).obj
        (F.over U)).mapIso (tensorPowerOverIso F U (n + 1)) ≪≫
        (PresheafOfModules.tensorSheafBifunctorOverIso.{v, u₁, u, u, u}
          (Osharp := Osharp) U F (_root_.SheafOfModules.tensorPower J F (n + 1))).symm

/-- The degree-`n` tensor power of a sheaf of modules, restricted to an object `U` over which the
module becomes free, is free. This is the tensor analogue of
`Stacks.SheafOfModules.exteriorPowerOverFreeIsoOfIsoFree`; the index type is existentially
quantified for the reason recorded at
`Stacks.SheafOfModules.exists_nonempty_iso_free_tensorPower`, but it depends only on `U` and the
given trivialisation, so **one object of the site trivialises every degree**. -/
theorem exists_nonempty_iso_free_tensorPowerOver
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (U : C) (n : ℕ) (γ : Type u)
    (e : (show _root_.SheafOfModules.{u} (Sheaf.toRingCat (J.over U) (Osharp.over U)) from
          F.over U) ≅
      _root_.SheafOfModules.free (R := Sheaf.toRingCat (J.over U) (Osharp.over U)) γ) :
    ∃ K : Type u, Nonempty ((A.tensor.piece (n : ℤ)).over U ≅
      _root_.SheafOfModules.free (R := (Sheaf.toRingCat J Osharp).over U) K) := by
  obtain ⟨K, ⟨eK⟩⟩ := exists_nonempty_iso_free_tensorPower (J := J.over U)
    (Osharp := Osharp.over U) γ e n
  exact ⟨K, ⟨(_root_.SheafOfModules.overFunctor (Sheaf.toRingCat J Osharp) U).mapIso
    (A.tensorPieceIso n) ≪≫ (tensorPowerOverIso F U n).symm ≪≫ eK⟩⟩

/-- **Each tensor power of a locally free sheaf of modules is locally free.** This is clause (6)
of [Stacks, Tag 01CK] for the tensor powers: a covering trivialising `F` with index types `γ i`
trivialises `Tⁿ F` with index types the `n`-fold products of the `γ i`. -/
@[stacks 01CK "tensor powers of a locally free module"]
theorem isLocallyFree_tensorPower
    (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras J F) (n : ℕ)
    [hF : F.IsLocallyFree] : (A.tensor.piece (n : ℤ)).IsLocallyFree := by
  exact isLocallyFree_of_forall_iso_free_of_isLocallyFree (F := F) fun U γ e =>
    exists_nonempty_iso_free_tensorPowerOver A U n γ e

end Stacks.SheafOfModules

end
