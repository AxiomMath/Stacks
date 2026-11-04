module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeSectionsTuples
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProjectiveEquivalenceAuxVanishing
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.Presentation
public import StacksFrontier.AlgebraicGeometry.SymmetricFree.Sheaf

/-!
# The homogeneous pieces of a polynomial algebra over a scheme are finite over affine opens

Let `X` be a scheme and let `I` be a finite index type. The sheaf of graded algebras

`𝓟 = Sym(𝒪_X^{(I)}) = 𝒪_X[x_i : i ∈ I]`,

that is `SheafOfModules.sheafifiedSymmetricAlgebra` of `SheafOfModules.free I`, has for its
degree-`n` homogeneous piece the free sheaf of modules on the degree-`n` monomials in the
variables `x_i` — the sheaf-level Tag 00DN,
`Stacks.SymmetricFree.sheafifiedSymmetricPieceFreeIso`. There are finitely many such monomials
when `I` is finite, so the sections of the piece over any open form a finite module over the
functions there.

That finiteness is exactly the hypothesis `hP` of `Stacks.Coherent.moduleFinite_piece` and
`Stacks.Coherent.isCoherent_piece`, and the hypothesis `hPfin` of
`Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_of_epi_over`: those statements run the
dévissage of [Stacks, Tag 0897] over an auxiliary graded algebra with free pieces instead of the
associated graded algebra itself, and `𝓟` is that auxiliary algebra. The final statement here is
given in their `∀ (U : X.affineOpens) (m : ℤ), …` shape so that it can be passed to them with no
massaging.

## Main results

* `Stacks.SymmetricFree.finite_setOf_degree_eq` — the degree-`n` monomials in finitely many
  variables form a finite type. An exponent never exceeds the degree, so `d ↦ (d i : Fin (n+1))`
  injects them into `I → Fin (n + 1)`.
* `Stacks.SymmetricFree.schemeSymmetricPieceFreeIso` — Tag 00DN at the sheaf level, spelled at
  the site of opens of a scheme: the degree-`n` piece of `𝓟` is free on the degree-`n`
  monomials.
* `Stacks.SymmetricFree.moduleFinite_sections_free` — the sections of a free sheaf of modules on
  a finite index type, over any open, form a finite module over the functions on that open.
* `Stacks.SymmetricFree.moduleFinite_sections_symmetricFreePiece` and
  `Stacks.SymmetricFree.moduleFinite_symmetricAlgebraPiece` — the finiteness of the sections of
  the degree-`m` piece of `𝓟`, over an arbitrary open and over an affine one.
* `Stacks.SymmetricFree.forall_moduleFinite_symmetricAlgebraPiece` — the same, in the shape the
  three consumers named above expect.
* `Stacks.SymmetricFree.isQuasicoherent_symmetricAlgebraPiece` — every homogeneous piece of `𝓟`
  is quasi-coherent, for an arbitrary set of variables. This is clause (5) of [Stacks, Tag 01CK]
  for symmetric powers at the free sheaf of modules on `I`.

## Implementation notes

**Two spellings of the sections.** The sections of a module `M` on a scheme carry a
`Γ(X, U)`-module structure through `AlgebraicGeometry.Scheme.Modules`, which is a `def`: the
instance is found only for a term whose type is syntactically `X.Modules`, which is what the
abbreviation `Stacks.Coherent.algPiece` provides and what the `Γ(M, U)` notation needs.
`SheafOfModules.free I` is not of that shape, so the two intermediate statements are given over
`X.ringCatSheaf.obj.obj (op U)` with the sections written as `M.val.obj (op U)`. The two
descriptions of ring and module are definitionally equal, so
`moduleFinite_symmetricAlgebraPiece` is the arbitrary-open statement with no proof.

**Negative degrees.** `SheafOfModules.symmetricPiece_eq_zero_of_neg_sheafifiedSymmetricAlgebra`
gives the vanishing sectionwise, which is all that is needed: a module all of whose elements are
zero is finite, the empty family spanning it. The piece is also a zero object
(`SheafOfModules.isZero_sheafifiedSymmetricAlgebra_piece_of_neg`), but reading that back on
sections is a detour.

**No Stacks attribute is attached.** Tag 00DN is about modules over a ring and about the
exterior power as well as the symmetric one; the sheaf-level symmetric half it is used through
here is an ingredient of clause (6) of Tag 01CK rather than either tag, as recorded at
`Stacks.SymmetricFree.sheafifiedSymmetricPieceFreeIso`.

## References

* [Stacks Project, Tag 00DN](https://stacks.math.columbia.edu/tag/00DN)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Tag 0FQW](https://stacks.math.columbia.edu/tag/0FQW)
* [Stacks Project, Tag 0897](https://stacks.math.columbia.edu/tag/0897)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u v

namespace Stacks.SymmetricFree

/-- **The degree-`n` monomials in finitely many variables form a finite type.** Each exponent of
a monomial of degree `n` is at most `n`, so `d ↦ fun i => (d i : Fin (n + 1))` injects the
degree-`n` monomials into `I → Fin (n + 1)`. -/
instance finite_setOf_degree_eq {I : Type v} [Finite I] {n : ℕ} :
    Finite {d : I →₀ ℕ | Finsupp.degree d = n} := by
  refine Finite.of_injective
    (f := fun d : {d : I →₀ ℕ | Finsupp.degree d = n} => fun i : I =>
      (⟨(d : I →₀ ℕ) i, by
        have hd : Finsupp.degree (d : I →₀ ℕ) = n := d.2
        have hle : (d : I →₀ ℕ) i ≤ Finsupp.degree (d : I →₀ ℕ) := Finsupp.le_degree i _
        omega⟩ : Fin (n + 1))) ?_
  intro a b hab
  refine Subtype.ext (Finsupp.ext fun i => ?_)
  simpa using congrArg Fin.val (congrFun hab i)

variable (X : Scheme.{u}) (I : Type u)

/-- **Tag 00DN at the sheaf level, over a scheme:** the degree-`n` homogeneous piece of the
polynomial algebra `𝒪_X[x_i : i ∈ I]` is the free sheaf of modules on the degree-`n` monomials
in the variables `x_i`. This is `Stacks.SymmetricFree.sheafifiedSymmetricPieceFreeIso` at the
site of opens of `X`, where the ring sheaf of the scheme is the one the symmetric algebra is
built over. -/
noncomputable def schemeSymmetricPieceFreeIso (n : ℕ) :
    (SheafOfModules.sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X)
        (SheafOfModules.free (R := X.ringCatSheaf) I)).piece (n : ℤ) ≅
      SheafOfModules.free (R := X.ringCatSheaf) {d : I →₀ ℕ | Finsupp.degree d = n} :=
  sheafifiedSymmetricPieceFreeIso (Opens.grothendieckTopology ↥X) I n

/-- **The sections of a finite free sheaf of modules form a finite module.** Over an open `U`
they are the `κ`-tuples of functions on `U`, by `Stacks.SheafOfModules.freeSectionsIso`. -/
theorem moduleFinite_sections_free (κ : Type u) [Finite κ] (U : X.Opens) :
    Module.Finite (X.ringCatSheaf.obj.obj (op U))
      ((SheafOfModules.free (R := X.ringCatSheaf) κ).val.obj (op U)) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  exact Module.Finite.equiv
    (Stacks.SheafOfModules.freeSectionsIso (R := X.ringCatSheaf) κ (op U)).toLinearEquiv

/-- **The sections of a homogeneous piece of `𝒪_X[x_i : i ∈ I]` over an open form a finite
module**, for a finite set of variables `I`. In a negative degree the piece has no nonzero
section; in degree `n ≥ 0` it is free on the finitely many degree-`n` monomials, by
`Stacks.SymmetricFree.schemeSymmetricPieceFreeIso`. -/
theorem moduleFinite_sections_symmetricFreePiece [Finite I] (U : X.Opens) (m : ℤ) :
    Module.Finite Γ(X, U)
      Γ(Stacks.Coherent.algPiece (SheafOfModules.sheafifiedSymmetricAlgebra
        (Opens.grothendieckTopology ↥X) (SheafOfModules.free (R := X.ringCatSheaf) I)) m, U) := by
  rcases lt_or_ge m 0 with hm | hm
  · refine ⟨⟨∅, eq_top_iff.2 fun x _ => ?_⟩⟩
    rw [show x = 0 from SheafOfModules.symmetricPiece_eq_zero_of_neg_sheafifiedSymmetricAlgebra
      (Opens.grothendieckTopology ↥X) _ m hm (op U) x]
    exact Submodule.zero_mem _
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hm
    have : Module.Finite (X.ringCatSheaf.obj.obj (op U))
        ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).obj
          (SheafOfModules.free (R := X.ringCatSheaf)
            {d : I →₀ ℕ | Finsupp.degree d = n})) :=
      moduleFinite_sections_free X {d : I →₀ ℕ | Finsupp.degree d = n} U
    have hpiece : Module.Finite (X.ringCatSheaf.obj.obj (op U))
        ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).obj
          ((SheafOfModules.sheafifiedSymmetricAlgebra (Opens.grothendieckTopology ↥X)
            (SheafOfModules.free (R := X.ringCatSheaf) I)).piece (n : ℤ))) :=
      Module.Finite.equiv
        ((_root_.SheafOfModules.evaluation X.ringCatSheaf (op U)).mapIso
          (schemeSymmetricPieceFreeIso X I n).symm).toLinearEquiv
    exact hpiece

/-- **The sections of a homogeneous piece of `𝒪_X[x_i : i ∈ I]` over an affine open form a
finite module.** This is `Stacks.SymmetricFree.moduleFinite_sections_symmetricFreePiece` with the
sections written through `Stacks.Coherent.algPiece`, which is the shape
`Stacks.Coherent.moduleFinite_piece` and its two companions ask for. -/
theorem moduleFinite_symmetricAlgebraPiece [Finite I] (U : X.affineOpens) (m : ℤ) :
    Module.Finite Γ(X, U.1)
      Γ(Stacks.Coherent.algPiece (SheafOfModules.sheafifiedSymmetricAlgebra
        (Opens.grothendieckTopology ↥X) (SheafOfModules.free (R := X.ringCatSheaf) I)) m, U.1) :=
  moduleFinite_sections_symmetricFreePiece X I U.1 m

/-- **The finiteness hypothesis on `𝒪_X[x_i : i ∈ I]`, in the shape its consumers take it.**
This is the hypothesis `hP` of `Stacks.Coherent.moduleFinite_piece` and
`Stacks.Coherent.isCoherent_piece`, and the hypothesis `hPfin` of
`Stacks.Coherent.exists_isZero_Hgroup_piece_tensorPowModule_of_epi_over`, discharged for the
polynomial algebra on a finite set of variables. -/
theorem forall_moduleFinite_symmetricAlgebraPiece [Finite I] :
    ∀ (U : X.affineOpens) (m : ℤ), Module.Finite Γ(X, U.1)
      Γ(Stacks.Coherent.algPiece (SheafOfModules.sheafifiedSymmetricAlgebra
        (Opens.grothendieckTopology ↥X) (SheafOfModules.free (R := X.ringCatSheaf) I)) m, U.1) :=
  fun U m => moduleFinite_symmetricAlgebraPiece X I U m

/-- **Every homogeneous piece of `𝒪_X[x_i : i ∈ I]` is quasi-coherent**, in every integer
degree and for an arbitrary set of variables. The negative pieces are zero objects, and in a
nonnegative degree this is clause (5) of [Stacks, Tag 01CK] for symmetric powers,
`Stacks.SliceAlgebra.isQuasicoherent_sheafifiedSymmetricPiece`, applied to the free sheaf of
modules on `I`, which is quasi-coherent because it is a coproduct of copies of the structure
sheaf. -/
theorem isQuasicoherent_symmetricAlgebraPiece (m : ℤ) :
    (Stacks.Coherent.algPiece (SheafOfModules.sheafifiedSymmetricAlgebra
      (Opens.grothendieckTopology ↥X)
      (SheafOfModules.free (R := X.ringCatSheaf) I)) m).IsQuasicoherent := by
  have : (SheafOfModules.free (R := X.ringCatSheaf) I).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free I
  exact SheafOfModules.isQuasicoherent_sheafifiedSymmetricAlgebra_piece
    (Opens.grothendieckTopology ↥X) (SheafOfModules.free (R := X.ringCatSheaf) I)
    (fun n => Stacks.SliceAlgebra.isQuasicoherent_sheafifiedSymmetricPiece X
      (SheafOfModules.free (R := X.ringCatSheaf) I) n) m

end Stacks.SymmetricFree

end
