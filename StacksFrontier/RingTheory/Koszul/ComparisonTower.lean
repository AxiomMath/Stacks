module

public import StacksFrontier.Algebra.DifferentialGraded.HomotopyRetractTensor
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleRepresents
public import StacksFrontier.RingTheory.Koszul.AppendTensorIsomorphism
public import StacksFrontier.RingTheory.Koszul.ComparisonAlgebraRetract

/-!
# The comparison algebra of a sequence resolves its Koszul algebra

Let `f₁, …, f_r` be elements of a commutative ring `R` and let `N ≥ t`. The algebra
$$B_{N,t} = R\langle x_1, z_1, u_1\rangle \otimes_R \cdots \otimes_R
  R\langle x_r, z_r, u_r\rangle$$
maps to the Koszul algebra `K_t = R⟨x_1, …, x_r⟩` by the tensor product of the one-variable
comparison homomorphisms, followed by the identification of `K_t` with the tensor product of the
one-variable Koszul algebras. That homomorphism carries a homotopy retraction, hence is a
quasi-isomorphism of the underlying complexes of `R`-modules; this is the step of the proof of Tag
0GZ7 which the source records as *"a tensor product of quasi-isomorphisms between bounded above
complexes of free `R`-modules"*.

The construction is by induction on the length of the sequence, a sequence of length `s + 1` being
the concatenation of its first `s` terms with its last. The induction needs no transport along the
resulting identity of sequences other than in the conclusion, which is a statement about the
Koszul algebra of the sequence alone.

## Main definitions

* `Koszul.KoszulRetractData`: a differential graded algebra mapping onto `K_t` with a homotopy
  retraction of that map.
* `Koszul.powAppendRetract`: the isomorphism `K_t(g) ⊗_R K_t(h) → K_t(g, h)` read as a homotopy
  retraction.

## Main results

* `Koszul.nonempty_koszulRetractData`: for every sequence and every `N ≥ t` such data exists,
  with the tensor product of the one-variable comparison algebras as the resolving algebra.

## References

* [Stacks Project, Tag 0GZ7](https://stacks.math.columbia.edu/tag/0GZ7)
* [Stacks Project, Tag 065W](https://stacks.math.columbia.edu/tag/065W)
-/

@[expose] public noncomputable section

namespace Koszul

universe u

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {r s : ℕ}

/-- A resolution of the Koszul algebra `K_t` of a sequence: a differential graded algebra together
with a homomorphism onto `K_t` admitting a homotopy retraction. -/
structure KoszulRetractData (f : Fin r → R) (t : ℕ) where
  /-- The resolving differential graded algebra. -/
  carrier : DifferentialGradedAlgebra.{u, u} R
  /-- The homomorphism onto `K_t`. -/
  hom : carrier.Hom (powAlgebra f t)
  /-- A homotopy retraction of that homomorphism. -/
  retract : HomotopyRetract hom

/-- The isomorphism `K_t(g) ⊗_R K_t(h) → K_t(g, h)` read as a homotopy retraction. -/
def powAppendRetract (g : Fin r → R) (h : Fin s → R) (t : ℕ) :
    HomotopyRetract (powAppendFromTensor g h t) :=
  HomotopyRetract.ofInverse (powAppendFromTensor g h t) (powAppendToTensor g h t)
    (fun b => AlgHom.ext_iff.mp (powAppendFromTensor_powAppendToTensor g h t) b)
    (fun a => AlgHom.ext_iff.mp (powAppendToTensor_powAppendFromTensor g h t) a)

/-- **The comparison algebra of a sequence resolves its Koszul algebra.** For every sequence
`f₁, …, f_r` in `R` and every `N ≥ t` the iterated tensor product of the one-variable comparison
algebras maps onto `K_t` by a homomorphism with a homotopy retraction. -/
theorem nonempty_koszulRetractData {N t : ℕ} (hNt : t ≤ N) :
    ∀ (q : ℕ) (f : Fin q → R), Nonempty (KoszulRetractData f t) := by
  intro q
  induction q with
  | zero =>
      intro f
      exact ⟨{ carrier := powAlgebra f t
               hom := idHom (powAlgebra f t)
               retract := HomotopyRetract.ofInverse (idHom (powAlgebra f t))
                 (idHom (powAlgebra f t)) (fun _ => rfl) (fun _ => rfl) }⟩
  | succ p ih =>
      intro f
      have heq : Fin.append (Fin.init f) (fun _ : Fin 1 => f (Fin.last p)) = f := by
        rw [Fin.append_right_eq_snoc, Fin.snoc_init_self]
      obtain ⟨D⟩ := ih (Fin.init f)
      rw [← heq]
      exact ⟨{ carrier := tensorProduct D.carrier (comparisonAlgebra (f (Fin.last p)) hNt)
               hom := (powAppendFromTensor (Fin.init f)
                   (fun _ : Fin 1 => f (Fin.last p)) t).comp
                 ((tensorHomLeft D.hom
                     (powAlgebra (fun _ : Fin 1 => f (Fin.last p)) t)).comp
                   (tensorHomRight D.carrier
                     (comparisonToKoszul (f (Fin.last p)) hNt)))
               retract := (powAppendRetract (Fin.init f)
                   (fun _ : Fin 1 => f (Fin.last p)) t).comp
                 ((D.retract.tensorLeft
                     (powAlgebra (fun _ : Fin 1 => f (Fin.last p)) t)).comp
                   ((comparisonHomotopyRetract (f (Fin.last p)) hNt).tensorRight
                     D.carrier)) }⟩

end Koszul
