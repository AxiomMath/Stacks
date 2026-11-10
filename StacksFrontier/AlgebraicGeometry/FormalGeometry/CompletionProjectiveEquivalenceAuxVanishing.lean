module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import
  StacksFrontier.AlgebraicGeometry.FormalGeometry.CoherentAdicSystem.TransitionKernelTwistVanishing
public import StacksFrontier.AlgebraicGeometry.ProperAmpleCohomology.Basic
public import StacksFrontier.AlgebraicGeometry.RelativeSerreVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeFiniteType.Basic

/-!
# The homogeneous pieces of a graded module over a sheaf of graded algebras

This file is the cohomological groundwork for
`Stacks.Coherent.HasAssociatedGradedTwistVanishing`, the hypothesis of [Stacks, Tag 0884] —
that is, for part (2) of [Stacks, Tag 0897] at the associated graded algebra
`𝓑 = ⨁ₘ ℐᵐ/ℐᵐ⁺¹` of `ℐ = I · 𝒪_X`.

## What is proved here

Let `X` be a locally Noetherian scheme, let `𝓟` be a sheaf of graded algebras on it and let `M`
be a graded `𝓟`-module with quasi-coherent pieces which is of finite type on affine opens
(`Stacks.Coherent.IsFiniteTypeOnAffine`, the conclusion of [Stacks, Tag 087Z]).

* `Stacks.Coherent.moduleFinite_piece` — over every affine open the sections of `Mₙ` form a
  **finite** `Γ(X, U)`-module, in every degree `n : ℤ`, as soon as the homogeneous pieces of `𝓟`
  themselves have finite modules of sections there. The generators of `M` over `U` have finitely
  many degrees, and the only part of the algebra that can carry a generator of degree `j` into
  degree `n` is the single piece `𝓟_{n-j}`.
* `Stacks.Coherent.isCoherent_piece` — hence **every homogeneous piece `Mₙ` is coherent**.
* `Stacks.Coherent.moduleFinite_algebraPiece` — the finiteness hypothesis of the two previous
  items, discharged for the associated graded algebra `𝓑 = ⨁ₘ ℐᵐ/ℐᵐ⁺¹` of a quasi-coherent
  sheaf of ideals `ℐ` presented by `Stacks.Coherent.AssociatedGradedAlgebraData`. This is where
  the Noetherian hypothesis is spent: `D` identifies `𝓑ₘ` over an affine open with the finite
  `Γ(X, U)`-module `Jᵐ/Jᵐ⁺¹`.
* `Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_of_lt` — the **uniform
  cohomological-dimension bound**: for `f : X ⟶ Spec A` proper there is one `e` with
  `Hᵖ(X, Mₙ ⊗ L ^⊗ d) = 0` for every `p > e`, every degree `n` and every `d`. This is
  [Stacks, Tag 01XJ] read on `X`
  (`Stacks.AlgebraicGeometry.RelativeSerreVanishing.exists_isZero_hgroup_tensorPowTwist_of_lt`),
  and it is the base of the descending induction on the cohomological degree.
* `Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_on_finset` — Serre vanishing for
  **finitely many** degrees at once: for a `Finset` of degrees there is one `d₁` above which all
  the higher cohomology of the twists of those pieces vanishes. This is clause (4) of
  [Stacks, Tag 0B5T]
  (`Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist`) applied
  to each of the finitely many pieces, which `Stacks.Coherent.isCoherent_piece` makes coherent.
  The sheaf of graded algebras is arbitrary, its finiteness entering as the hypothesis `hP`: the
  dévissage of part (2) of [Stacks, Tag 0897] applies this to graded modules over the polynomial
  algebra, not over the associated graded algebra.

## What is *not* proved here

`HasAssociatedGradedTwistVanishing` asks for one `d₀` serving **all** degrees `n` at once. The
last two items above are the two ends of the descending induction on the cohomological degree `p`
that produces it. The induction itself is
`StacksFrontier/AlgebraicGeometry/FormalGeometry/CompletionProjectiveEquivalenceAuxDevissage.lean`,
and its dévissage step — which cannot be taken over the associated graded algebra itself, the
pieces of `𝓑` not being free — is run over an auxiliary graded algebra with free pieces in
the module
`StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxPresentation`.
That is why the finiteness of the pieces of the algebra enters
`Stacks.Coherent.moduleFinite_piece` and `Stacks.Coherent.isCoherent_piece` as a hypothesis
rather than through `D`: the induction is applied to graded modules over the auxiliary algebra,
obtained by `SheafOfModules.GradedModule.restrictScalars`.

## References

* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
* [Stacks Project, Tag 0884](https://stacks.math.columbia.edu/tag/0884)
* [Stacks Project, Tag 087Z](https://stacks.math.columbia.edu/tag/087Z)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 0B5T](https://stacks.math.columbia.edu/tag/0B5T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.Ample Stacks.RelativeVeryAmple

universe u

namespace Stacks.Coherent

/-! ### Sections of a zero module -/

private theorem sections_eq_zero' {X : Scheme.{u}} (N : X.Modules) (hN : IsZero N)
    (U : X.Opensᵒᵖ) (x : N.val.obj U) : x = 0 := by
  have happ := congrArg (fun g : N ⟶ N => g.val.app U x) (hN.eq_of_src (𝟙 N) 0)
  rw [show ((𝟙 N : N ⟶ N).val.app U) = 𝟙 _ from rfl,
    show ((0 : N ⟶ N).val.app U) = 0 from rfl] at happ
  simpa using happ

private theorem moduleFinite_of_isZero {X : Scheme.{u}} (N : X.Modules) (hN : IsZero N)
    (U : X.Opens) : Module.Finite Γ(X, U) Γ(N, U) := by
  refine ⟨⟨∅, eq_top_iff.2 fun x _ => ?_⟩⟩
  rw [sections_eq_zero' N hN (op U) x]
  exact Submodule.zero_mem _

/-! ### The homogeneous pieces, read as `𝒪_X`-modules -/

variable {X : Scheme.{u}}

/-- A homogeneous piece of a sheaf of graded algebras, read as an `𝒪_X`-module. The type
ascription is what puts the sections in the shape the `Γ(-, U)` notation and its module structure
expect. -/
public abbrev algPiece (P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf) (m : ℤ) :
    X.Modules :=
  P.piece m

/-- A homogeneous piece of a graded module over a sheaf of graded algebras, read as an
`𝒪_X`-module. -/
public abbrev modPiece {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    (M : SheafOfModules.GradedModule P) (n : ℤ) : X.Modules :=
  M.piece n

/-! ### Finiteness and coherence of the homogeneous pieces of a graded module -/

section Pieces

variable {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}

/-- Acting on a fixed homogeneous section `s` of degree `d` by the degree-`m` part of the
algebra, read in degree `n = d + m`. It is `Γ(X, U)`-linear in the algebra variable by
`SheafOfModules.GradedModule.smul_smul_right`. -/
private def actLinear (M : SheafOfModules.GradedModule P) (U : X.affineOpens)
    {d m n : ℤ} (h : d + m = n) (s : Γ(modPiece M d, U.1)) :
    Γ(algPiece P m, U.1) →ₗ[Γ(X, U.1)] Γ(modPiece M n, U.1) := by
  subst h
  exact
    { toFun := fun a => M.smul d m (op U.1) s a
      map_add' := fun a b => map_add (M.smul d m (op U.1) s) a b
      map_smul' := fun r a => M.smul_smul_right d m (op U.1) r s a }

private theorem eqRec_smul_eq_actLinear (M : SheafOfModules.GradedModule P)
    (U : X.affineOpens) {d m n : ℤ} (h : d + m = n)
    (s : (M.piece d).val.obj (op U.1)) (a : (P.piece m).val.obj (op U.1)) :
    (h ▸ M.smul d m (op U.1) s a : (M.piece n).val.obj (op U.1)) = actLinear M U h s a := by
  subst h
  rfl

/-- **The sections of a homogeneous piece of a graded module of finite type, over an affine
open, form a finite module** — over any sheaf of graded algebras whose own homogeneous pieces
have finite modules of sections over affine opens.

The generators supplied by `Stacks.Coherent.IsFiniteTypeOnAffine` have finitely many degrees, and
the only part of the algebra that can carry a generator of degree `j` into degree `n` is the
single piece `𝓟_{n-j}`. So the finitely many products of a generator with a generator of that
finite module already span.

For the associated graded algebra of an ideal sheaf the hypothesis `hP` is
`Stacks.Coherent.moduleFinite_algebraPiece`, and that is where the Noetherian hypothesis is
spent. -/
public theorem moduleFinite_piece
    (hP : ∀ (U : X.affineOpens) (m : ℤ), Module.Finite Γ(X, U.1) Γ(algPiece P m, U.1))
    (M : SheafOfModules.GradedModule P) (hft : IsFiniteTypeOnAffine M) (U : X.affineOpens)
    (n : ℤ) :
    Module.Finite Γ(X, U.1) Γ(modPiece M n, U.1) := by
  classical
  obtain ⟨G, hG⟩ := hft U
  have : ∀ s : {x // x ∈ G}, Module.Finite Γ(X, U.1) Γ(algPiece P (n - s.1.1), U.1) :=
    fun s => hP U _
  let S : Submodule Γ(X, U.1) Γ(modPiece M n, U.1) :=
    ⨆ s : {x // x ∈ G}, LinearMap.range
      (actLinear M U (show s.1.1 + (n - s.1.1) = n by omega) s.1.2)
  have hSfg : S.FG :=
    Submodule.fg_iSup _ fun s => Submodule.fg_range _
  have htop : S = ⊤ := by
    refine top_unique fun t _ => ?_
    refine (AddSubgroup.closure_le S.toAddSubgroup).mpr ?_ ((hG n).ge (AddSubgroup.mem_top t))
    rintro t' ⟨s, hsG, m, a, h, rfl⟩
    obtain rfl : m = n - s.1 := by omega
    change _ ∈ S
    rw [eqRec_smul_eq_actLinear M U h s.2 a]
    exact Submodule.mem_iSup_of_mem ⟨s, hsG⟩ ⟨a, rfl⟩
  exact Module.finite_def.mpr (htop ▸ hSfg)

/-- **Every homogeneous piece of a quasi-coherent graded module of finite type is coherent** —
over any sheaf of graded algebras whose own pieces have finite modules of sections over affine
opens. This is (4) ⇒ (1) of [Stacks, Tag 01XZ]: the sections over every affine open form a finite
module by `Stacks.Coherent.moduleFinite_piece`. -/
public theorem isCoherent_piece [IsLocallyNoetherian X]
    (hP : ∀ (U : X.affineOpens) (m : ℤ), Module.Finite Γ(X, U.1) Γ(algPiece P m, U.1))
    (M : SheafOfModules.GradedModule P)
    (hqc : ∀ n : ℤ, (M.piece n).IsQuasicoherent) (hft : IsFiniteTypeOnAffine M) (n : ℤ) :
    (modPiece M n).IsCoherent := by
  have : (modPiece M n).IsQuasicoherent := hqc n
  have : (modPiece M n).IsFiniteType :=
    Stacks.AlgebraicGeometry.TopDegreeFiniteType.isFiniteType_of_forall_moduleFinite_sections
      (modPiece M n) fun U => moduleFinite_piece hP M hft U n
  exact Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isQuasicoherent_of_isFiniteType _

end Pieces

/-! ### Finiteness of the homogeneous pieces of the associated graded algebra -/

/-- `Jⁿ/Jⁿ⁺¹` is a finite module over a Noetherian ring: it is a quotient of the finitely
generated ideal `Jⁿ`. -/
private theorem moduleFinite_associatedGraded_piece (R : Type u) [CommRing R]
    [IsNoetherianRing R] (J : Ideal R) (n : ℕ) :
    Module.Finite R (AssociatedGraded.piece (M := R) J n) := by
  have : Module.Finite R ↥(AssociatedGraded.power (M := R) J n) :=
    Module.Finite.iff_fg.mpr (IsNoetherian.noetherian _)
  infer_instance

variable {I : X.IdealSheafData} [IsLocallyNoetherian X]

/-- The degree-`m` piece of the associated graded algebra, over an affine open, as a
`Γ(X, U)`-linear equivalence with `Jᵐ/Jᵐ⁺¹`. The additive identification is
`Stacks.Coherent.AssociatedGradedAlgebraData.algebraPiece` and its linearity over the structure
sheaf is `…algebraPiece_smul`. -/
private def algebraPieceLinearEquiv (D : AssociatedGradedAlgebraData I) (U : X.affineOpens)
    (m : ℕ) :
    Γ(algPiece D.algebra (m : ℤ), U.1) ≃ₗ[Γ(X, U.1)]
      AssociatedGraded.piece (M := Γ(X, U.1)) (I.ideal U) m where
  toFun := D.algebraPiece m U
  map_add' := (D.algebraPiece m U).map_add
  map_smul' r a := D.algebraPiece_smul m U r a
  invFun := (D.algebraPiece m U).symm
  left_inv := (D.algebraPiece m U).left_inv
  right_inv := (D.algebraPiece m U).right_inv

/-- **The sections of a homogeneous piece of the associated graded algebra over an affine open
form a finite module.** In nonnegative degrees this is finiteness of `Jᵐ/Jᵐ⁺¹` over the
Noetherian ring `Γ(X, U)`, transported along `D.algebraPiece`; in negative degrees the piece is
zero. -/
public theorem moduleFinite_algebraPiece (D : AssociatedGradedAlgebraData I)
    (U : X.affineOpens) (m : ℤ) :
    Module.Finite Γ(X, U.1) Γ(algPiece D.algebra m, U.1) := by
  rcases lt_or_ge m 0 with hm | hm
  · exact moduleFinite_of_isZero _ (D.algebraNegative m hm) U.1
  · lift m to ℕ using hm
    have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
    have := moduleFinite_associatedGraded_piece Γ(X, U.1) (I.ideal U) m
    exact Module.Finite.equiv (algebraPieceLinearEquiv D U m).symm

end Stacks.Coherent

namespace Stacks.Coherent

variable {X : Scheme.{u}} {I : X.IdealSheafData} {D : AssociatedGradedAlgebraData I}

/-! ### The two ends of the descending induction -/

/-- **One cohomological degree above which every twist of every homogeneous piece is acyclic.**

[Stacks, Tag 01XJ], read on `X` through the Leray degeneration over the affine base
(`Stacks.AlgebraicGeometry.RelativeSerreVanishing.exists_isZero_hgroup_tensorPowTwist_of_lt`),
bounds the cohomological degree uniformly in the coherent module and in the twist; the pieces of
`M` are coherent by `Stacks.Coherent.isCoherent_piece`. This is the base case of the descending
induction on the cohomological degree that part (2) of [Stacks, Tag 0897] is proved by. -/
public theorem exists_isZero_Hgroup_piece_tensorPowModule_of_lt
    (A : Type u) [CommRing A] [IsNoetherianRing A] (f : X ⟶ Spec (.of A)) [IsProper f]
    (M : SheafOfModules.GradedModule D.algebra)
    (hqc : ∀ n : ℤ, (M.piece n).IsQuasicoherent) (hft : IsFiniteTypeOnAffine M)
    (L : X.Modules) [IsInvertibleModule X L] :
    ∃ e : ℕ, ∀ p : ℕ, e < p → ∀ n d : ℤ,
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (tensorModules X (modPiece M n) (tensorPowModule X L d))) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨e, he⟩ :=
    Stacks.AlgebraicGeometry.RelativeSerreVanishing.exists_isZero_hgroup_tensorPowTwist_of_lt f L
  exact ⟨e, fun p hp n d =>
    he p hp (modPiece M n) (isCoherent_piece (moduleFinite_algebraPiece D) M hqc hft n) d⟩

/-- **Serre vanishing for finitely many homogeneous degrees at once.**

Clause (4) of [Stacks, Tag 0B5T]
(`Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist`) gives, for
each coherent module separately, a twist above which the higher cohomology vanishes; the pieces
of `M` are coherent by `Stacks.Coherent.isCoherent_piece`, and a `Finset` of degrees admits the
maximum of the finitely many bounds. This is the half of the descending induction's step that
*is* available: the middle term of the dévissage is a finite direct sum of copies of finitely
many of the pieces.

The sheaf of graded algebras is arbitrary: the only thing the proof asks of it is the hypothesis
`hP` of `Stacks.Coherent.isCoherent_piece`, that the sections of its homogeneous pieces over an
affine open form finite modules. For the associated graded algebra of an ideal sheaf that is
`Stacks.Coherent.moduleFinite_algebraPiece`, and for the polynomial algebra
`Stacks.Coherent.polyAlgebra` it is
`Stacks.SymmetricFree.forall_moduleFinite_symmetricAlgebraPiece`; the second is the one the
dévissage of part (2) of [Stacks, Tag 0897] uses, its auxiliary algebra being the polynomial
algebra and not the associated graded algebra. -/
public theorem exists_isZero_Hgroup_piece_tensorPowModule_on_finset
    (A : Type u) [CommRing A] [IsNoetherianRing A] (f : X ⟶ Spec (.of A)) [IsProper f]
    {P : SheafOfModules.GradedAlgebra.{u, u} X.ringCatSheaf}
    (hP : ∀ (U : X.affineOpens) (m : ℤ), Module.Finite Γ(X, U.1) Γ(algPiece P m, U.1))
    (M : SheafOfModules.GradedModule P)
    (hqc : ∀ n : ℤ, (M.piece n).IsQuasicoherent) (hft : IsFiniteTypeOnAffine M)
    (L : X.Modules) [IsInvertibleModule X L] (hL : IsAmple X L) (s : Finset ℤ) :
    ∃ d₁ : ℕ, ∀ d : ℕ, d₁ ≤ d → ∀ p : ℕ, 0 < p → ∀ n ∈ s,
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (tensorModules X (modPiece M n) (tensorPowModule X L (d : ℤ)))) := by
  classical
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have key : ∀ n : {x // x ∈ s}, ∃ d₁ : ℕ, ∀ d p : ℕ, d₁ ≤ d → 0 < p →
      IsZero (Hgroup X.ringCatSheaf ⊤ p
        (tensorModules X (modPiece M n.1) (tensorPowModule X L (d : ℤ)))) := by
    intro n
    have := isCoherent_piece hP M hqc hft n.1
    exact Stacks.AlgebraicGeometry.ProperAmpleCohomology.exists_isZero_Hgroup_tensorPowTwist
      f (modPiece M n.1) L hL
  choose k hk using key
  exact ⟨Finset.univ.sup k, fun d hd p hp n hn =>
    hk ⟨n, hn⟩ d p ((Finset.le_sup (f := k) (Finset.mem_univ _)).trans hd) hp⟩

end Stacks.Coherent

end
