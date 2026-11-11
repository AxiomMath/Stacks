module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.FlatSheafDerivedLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.GrothendieckExistence.PerfectSectionsOfLimitCarrier

/-!
# [Stacks, Tag 0CX6]: `RΓ(X, K ⊗^𝐋 E)` and `RHom_X(E, K)` are perfect and commute with base change

In Situation [Stacks, Tag 0CX4] let `K = R lim_{D_QCoh(𝒪_X)} Fₙ = DQ_X(R lim_{D(𝒪_X)} Fₙ)` be the
object of [Stacks, Tag 0CX5]. The coherator `DQ_X` and the derived limit `R lim_{D(𝒪_X)} Fₙ` exist
by `AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit_bounded`; this file chooses
them and states [Stacks, Tag 0CX6] for the resulting `K`, from
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.perfectSections_of_derivedLimit`, which proves
the statement for every coherator and every derived limit triangle.

## Main definitions

* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.coherator`: the coherator `DQ_X`.
* `AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit`: `R lim_{D(𝒪_X)} Fₙ`.

## Main results

* `FlatSheafExistenceSituation.ringIsPerfect_limitSections_and_isIso_baseChangeMap`:
  **[Stacks, Tag 0CX6]**.

## References

* [Stacks Project, Tag 0CX6](https://stacks.math.columbia.edu/tag/0CX6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite

universe u

namespace AlgebraicGeometry.Space

namespace FlatSheafExistenceSituation

variable (D : FlatSheafExistenceSituation.{u})

/-! ### The object `K` of [Stacks, Tag 0CX5] -/

/-- The coherator `DQ_X : D(𝒪_X) ⥤ D_QCoh(𝒪_X)`, the right adjoint of the inclusion, which exists by
[Stacks, Tag 0CX5] (`AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit_bounded`). -/
def coherator : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left ⥤
    (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).FullSubcategory :=
  haveI := D.derivedLimit_bounded.1
  (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι.rightAdjoint

/-- The adjunction `ι ⊣ DQ_X` of `AlgebraicGeometry.Space.FlatSheafExistenceSituation.coherator`. -/
def coheratorAdjunction :
    (spaceQuasicoherentProp D.B D.S D.containsLimitBase D.X.left).ι ⊣ D.coherator :=
  haveI := D.derivedLimit_bounded.1
  Adjunction.ofIsLeftAdjoint _

/-- A derived limit `R lim_{D(𝒪_X)} Fₙ` of the system `(iₙ,* Fₙ)`, which exists by
[Stacks, Tag 0CX5] (`AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit_bounded`). -/
def derivedLimit : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left :=
  D.derivedLimit_bounded.2.1.choose

/-- The map `R lim Fₙ ⟶ ∏ iₙ,* Fₙ` of the derived limit triangle of
`AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit`. -/
def derivedLimitToProduct :
    D.derivedLimit ⟶ ∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩ :=
  D.derivedLimit_bounded.2.1.choose_spec.choose

/-- `derivedLimitToProduct` is the first map of a distinguished triangle
`R lim Fₙ ⟶ ∏ Fₙ ⟶ ∏ Fₙ ⟶ (R lim Fₙ)[1]` whose middle map is `1 - transition`. -/
theorem exists_derivedLimitToProduct_triangle_distinguished :
    ∃ δ : (∏ᶜ fun n : ℕ => D.derivedSystem.obj ⟨n⟩) ⟶ D.derivedLimit⟦(1 : ℤ)⟧,
      Triangle.mk D.derivedLimitToProduct (Pi.lift fun n : ℕ =>
        Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ => D.derivedSystem.obj ⟨n⟩) (n + 1) ≫
            D.derivedSystem.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left) :=
  D.derivedLimit_bounded.2.1.choose_spec.choose_spec

/-- **[Stacks, Tag 0CX6].** In Situation [Stacks, Tag 0CX4] let
`K = R lim_{D_QCoh(𝒪_X)} Fₙ = DQ_X(R lim_{D(𝒪_X)} Fₙ)` be the object of [Stacks, Tag 0CX5]
(`DQ_X` is `AlgebraicGeometry.Space.FlatSheafExistenceSituation.coherator` and
`R lim_{D(𝒪_X)} Fₙ` is `AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit`, both of
which exist by `AlgebraicGeometry.Space.FlatSheafExistenceSituation.derivedLimit_bounded`). Then for
every perfect object `E` of `D(𝒪_X)` and every `n`:

1. `M = RΓ(X, K ⊗^𝐋 E)` (written `RΓ(X, E ⊗^𝐋 K)`) is a perfect object of `D(A)` and the
   canonical map `M ⊗^𝐋_A Aₙ ⟶ RΓ(Xₙ, E|_{Xₙ} ⊗^𝐋 Fₙ)` is an isomorphism in `D(Aₙ)`;
2. `N = RHom_X(E, K)` is a perfect object of `D(A)` and the canonical map
   `N ⊗^𝐋_A Aₙ ⟶ RHom_{Xₙ}(E|_{Xₙ}, Fₙ)` is an isomorphism in `D(Aₙ)`.

Here `E|_{Xₙ}` is the derived pullback of `E` along `iₙ : Xₙ ⟶ X`. The same holds for every other
choice of coherator and of derived limit triangle
(`AlgebraicGeometry.Space.FlatSheafExistenceSituation.perfectSections_of_derivedLimit`). -/
@[stacks 0CX6 "both parts in full, for every perfect E on X and every n, with \
K = DQ_X(R lim_{D(O_X)} F_n) the object of 0CX5, whose coherator and derived limit exist by \
derivedLimit_bounded: (1) RΓ(X, K ⊗^L E) is perfect in D(A) and the canonical map \
RΓ(X, K ⊗^L E) ⊗^L_A A_n → RΓ(X_n, F_n ⊗^L E|_{X_n}) is an isomorphism; (2) RHom_X(E, K) is \
perfect in D(A) and the canonical map RHom_X(E, K) ⊗^L_A A_n → RHom_{X_n}(E|_{X_n}, F_n) is an \
isomorphism"]
theorem ringIsPerfect_limitSections_and_isIso_baseChangeMap
    (E : spaceDerivedCategory D.B D.S D.containsLimitBase D.X.left)
    (hE : spaceIsPerfect D.B D.S D.containsLimitBase D.X.left E) (n : ℕ) :
    (StacksDraft.ringIsPerfect (D.limitTensorSections D.coherator D.derivedLimit E) ∧
      IsIso (D.limitTensorSectionsBaseChangeMap D.coheratorAdjunction D.derivedLimit E
        D.derivedLimitToProduct n)) ∧
    (StacksDraft.ringIsPerfect (D.limitSheafHomSections D.coherator D.derivedLimit E) ∧
      IsIso (D.limitSheafHomSectionsBaseChangeMap D.coheratorAdjunction D.derivedLimit E hE
        D.derivedLimitToProduct n)) :=
  D.perfectSections_of_derivedLimit D.coheratorAdjunction D.derivedLimit D.derivedLimitToProduct
    D.exists_derivedLimitToProduct_triangle_distinguished E hE n

end FlatSheafExistenceSituation

end AlgebraicGeometry.Space
