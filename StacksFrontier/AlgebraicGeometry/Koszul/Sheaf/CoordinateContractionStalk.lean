module

public import StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.CoordinateContractionChainData

/-!
# The coordinate contraction at a stalk is contraction by a coordinate functional

Let `O♯` be a sheaf of commutative rings on a space `X`, let `F = (O♯)ʳ` be the finite free sheaf
of `O♯`-modules on `r` generators and let `A` be a bundle of tensor, exterior and symmetric
algebras of `F`. The contraction `δⱼ` by the `j`-th coordinate functional is a morphism

`δⱼ : ⋀^{n+1}(F) ⟶ ⋀ⁿ(F)`

of sheaves of modules. At a point `x` the stalk of `⋀ⁿ(F)` is the exterior power
`⋀ⁿ_{O_x}((O_x)ʳ)` of a free module of rank `r`, by Stacks Tag 01CH, and this file identifies the
map `δⱼ` induces on stalks under that identification: it is **contraction by the `j`-th coordinate
functional of `(O_x)ʳ`**, that is, by `LinearMap.proj j`.

Nothing new is proved. `StacksFrontier.AlgebraicGeometry.Koszul.Sheaf.CoordinateContractionChainData`
exhibits `δⱼ` as the differential of the Koszul chain complex of the `j`-th coordinate projection
`F ⟶ O♯`, and the stalk identification of the differential of a Koszul chain complex is
`Stacks.RegularSequence.exteriorKoszulStalkEquiv_stalkLin`: it is the ring-level Koszul
differential of the sequence of germs of the global sections defining the morphism. For the `j`-th
coordinate projection that sequence is the `j`-th standard basis vector, whose associated linear
form is the `j`-th coordinate projection of `(O_x)ʳ`.

## Main results

* `Koszul.seqDual_single_eq_proj`: the linear form of the `j`-th standard basis vector is the
  `j`-th coordinate projection.
* `PresheafOfModules.ExteriorFunctional.ext_dual`: two functionals on a presheaf of modules with
  the same linear forms are equal.
* `Stacks.SheafOfModules.unitExteriorFunctional_freeProj`: **the functional attached to the `j`-th
  coordinate projection is the `j`-th coordinate functional.**
* `SheafOfModules.TensorExteriorSymmetricAlgebras.coordKoszulDNat`: the coordinate contraction
  between the exterior powers of adjacent nonnegative degrees.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.coordKoszulChainData_dNat`: in adjacent
  nonnegative degrees the differential of the coordinate chain data is the coordinate contraction.
* `SheafOfModules.TensorExteriorSymmetricAlgebras.exteriorKoszulStalkEquiv_stalkLin_coordKoszulD`:
  **the coordinate contraction at a stalk is contraction by the `j`-th coordinate projection of
  `(O_x)ʳ`.**

## Implementation notes

**Two indexings of the same morphism.** The chain data indexes its differential by its source
alone, as `⋀ⁿ F ⟶ ⋀^{n-1} F`, while the contraction is indexed by both degrees. In nonnegative
degrees the two differ by the transport along `((n + 1 : ℕ) : ℤ) - 1 = ((n : ℕ) : ℤ)`, which is not
an identity of integers that holds definitionally for a variable `n`. The bridge is
`Stacks.RegularSequence.KoszulChainData.dOf_eq_koszulD`, which states exactly that the chain data's
differential at independently named degrees is the transported Koszul differential of the
functional attached to the morphism; `Stacks.RegularSequence.KoszulChainData.dNat` is that
differential at the degrees `((n + 1 : ℕ) : ℤ)` and `((n : ℕ) : ℤ)`.

**The two functionals are equal, not merely equal on sections.** A functional on a presheaf of
modules bundles a family of linear forms together with a naturality property, and the property is a
proposition, so two functionals with the same forms are equal. That equality is what lets the
Koszul differential of the functional attached to the coordinate projection be rewritten as the
coordinate contraction; a pointwise agreement of the forms would not, the differential depending on
the functional as a whole.

## References

* [Stacks Project, Tag 01CH](https://stacks.math.columbia.edu/tag/01CH)
* [Stacks Project, Tag 062K](https://stacks.math.columbia.edu/tag/062K)
* [Stacks Project, Tag 0BQY](https://stacks.math.columbia.edu/tag/0BQY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Sheaf Opposite TopologicalSpace

namespace Koszul

universe t

/-- **The linear form of the `j`-th standard basis vector is the `j`-th coordinate projection.**
The form of a sequence `f` sends `v` to `∑ i, vᵢ fᵢ`, and for `f` the `j`-th standard basis vector
only the `j`-th summand survives. -/
theorem seqDual_single_eq_proj {R : Type t} [CommRing R] {r : ℕ} (j : Fin r) :
    Koszul.seqDual (Pi.single j (1 : R)) = LinearMap.proj j := by
  classical
  refine LinearMap.ext fun v => ?_
  rw [Koszul.seqDual_apply,
    Finset.sum_eq_single j (fun b _ hb => by rw [Pi.single_eq_of_ne hb, mul_zero])
      (fun hj => absurd (Finset.mem_univ j) hj),
    Pi.single_eq_same, mul_one]
  rfl

end Koszul

namespace PresheafOfModules.ExteriorFunctional

universe v u w a

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}
  {F : PresheafOfModules.{max w a} (O ⋙ forget₂ _ RingCat)}

/-- **Two functionals on a presheaf of modules with the same linear forms are equal.** The
remaining field is the naturality of those forms, which is a proposition. -/
theorem ext_dual {φ ψ : ExteriorFunctional.{v, u, w, a} F} (h : φ.dual = ψ.dual) : φ = ψ := by
  obtain ⟨d₁, n₁⟩ := φ
  obtain ⟨d₂, n₂⟩ := ψ
  cases h
  rfl

end PresheafOfModules.ExteriorFunctional

namespace Stacks.SheafOfModules

universe v u w

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]

/-- **The functional attached to the `j`-th coordinate projection is the `j`-th coordinate
functional.** The two have the same linear forms by
`Stacks.SheafOfModules.coordExteriorFunctional_dual_eq_freeProj`, and a functional is determined by
its forms. -/
theorem unitExteriorFunctional_freeProj (j : ι) :
    unitExteriorFunctional (freeProj (S := toRingCat J Osharp) j) =
      coordExteriorFunctional (Osharp := Osharp) j :=
  PresheafOfModules.ExteriorFunctional.ext_dual
    (funext fun U => LinearMap.ext fun e =>
      (coordExteriorFunctional_dual_eq_freeProj (Osharp := Osharp) j U e).symm)

end Stacks.SheafOfModules

namespace SheafOfModules.TensorExteriorSymmetricAlgebras

universe v u w

section ChainData

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify J AddCommGrpCat.{w}]
  {ι : Type w} [DecidableEq ι] [Finite ι]
  (A : TensorExteriorSymmetricAlgebras J (SheafOfModules.free (R := toRingCat J Osharp) ι))

/-- **The coordinate contraction between the exterior powers of adjacent nonnegative degrees**,
`δⱼ : ⋀^{n+1}(F) ⟶ ⋀ⁿ(F)`. The integer degrees are the casts of `n + 1` and `n`. -/
def coordKoszulDNat (j : ι) (n : ℕ) : A.exteriorPower (n + 1) ⟶ A.exteriorPower n :=
  A.coordKoszulD j (show ((n : ℕ) : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring)

/-- **The coordinate chain data's differential at independently named degrees is the coordinate
contraction.** -/
theorem coordKoszulChainData_dOf (j : ι) {p q : ℤ} (h : q + 1 = p) :
    (A.coordKoszulChainData j).dOf h = A.coordKoszulD j h := by
  rw [Stacks.RegularSequence.KoszulChainData.dOf_eq_koszulD,
    Stacks.SheafOfModules.unitExteriorFunctional_freeProj, coordKoszulD_eq_koszulD]

/-- **In adjacent nonnegative degrees the coordinate chain data's differential is the coordinate
contraction.** The transport along `((n + 1 : ℕ) : ℤ) - 1 = ((n : ℕ) : ℤ)` that separates the two
indexings is absorbed. -/
theorem coordKoszulChainData_dNat (j : ι) (n : ℕ) :
    (A.coordKoszulChainData j).dNat n =
      A.coordKoszulD j (show ((n : ℕ) : ℤ) + 1 = ((n + 1 : ℕ) : ℤ) by push_cast; ring) :=
  A.coordKoszulChainData_dOf j _

end ChainData

section Stalk

universe u'

variable {X : TopCat.{u'}} {Osharp : Sheaf (Opens.grothendieckTopology ↥X) CommRingCat.{u'}}
  [HasSheafify (Opens.grothendieckTopology ↥X) AddCommGrpCat.{u'}]
  [(Opens.grothendieckTopology ↥X).WEqualsLocallyBijective AddCommGrpCat.{u'}]
  {r : ℕ}
  (A : TensorExteriorSymmetricAlgebras (Opens.grothendieckTopology ↥X)
    (Stacks.RegularSequence.koszulFreeSheaf Osharp r))

/-- The global sections defining the `j`-th coordinate projection are the `j`-th standard basis
vector. -/
theorem freeHomEquiv_freeProj_val (j k : Fin r) :
    ((SheafOfModules.unit
          (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).freeHomEquiv
        (Stacks.SheafOfModules.freeProj
          (S := toRingCat (Opens.grothendieckTopology ↥X) Osharp) (ULift.up j))
        (ULift.up k)).val (op (⊤ : Opens ↥X)) =
      (Pi.single j (1 : ToType (Osharp.obj.obj (op (⊤ : Opens ↥X))))
        : Fin r → ToType (Osharp.obj.obj (op (⊤ : Opens ↥X)))) k := by
  classical
  have h : (SheafOfModules.unit
        (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).freeHomEquiv
      (Stacks.SheafOfModules.freeProj
        (S := toRingCat (Opens.grothendieckTopology ↥X) Osharp) (ULift.up j)) (ULift.up k) =
    (SheafOfModules.unit (toRingCat (Opens.grothendieckTopology ↥X) Osharp)).unitHomEquiv
      (if (ULift.up k : ULift.{u'} (Fin r)) = ULift.up j then 𝟙 _ else 0) := by
    rw [Stacks.SheafOfModules.freeProj, Equiv.apply_symm_apply]
  rw [h, Pi.single_apply]
  by_cases hk : k = j
  · subst hk
    rw [ite_eq_left (rfl : (ULift.up k : ULift.{u'} (Fin r)) = ULift.up k),
      ite_eq_left (rfl : k = k)]
    rfl
  · rw [ite_eq_right (fun hh => hk (congrArg ULift.down hh)), ite_eq_right hk]
    rfl

/-- **The coordinate contraction at a stalk is contraction by a coordinate functional.** Under the
identification of the stalk of `⋀ⁿ((O♯)ʳ)` with the exterior power `⋀ⁿ_{O_x}((O_x)ʳ)`, the map
that `δⱼ` induces on stalks is the ring-level Koszul differential of the `j`-th coordinate
projection of `(O_x)ʳ`, that is, contraction by `LinearMap.proj j`.

The contraction is the differential of the Koszul chain complex of the `j`-th coordinate
projection, whose defining sequence of global sections is the `j`-th standard basis vector; the
stalk identification of the differential of a Koszul chain complex is the ring-level Koszul
differential of the germs of that sequence, and the linear form of the `j`-th standard basis
vector is `LinearMap.proj j`. -/
theorem exteriorKoszulStalkEquiv_stalkLin_coordKoszulD (j : Fin r) (n : ℕ) (x : ↥X)
    (m : ↑(TopCat.Presheaf.stalk (A.exteriorPower (n + 1)).val.presheaf x)) :
    Stacks.SheafOfModules.exteriorKoszulStalkEquiv A n x
        (Stacks.RegularSequence.stalkLin (A.coordKoszulDNat (ULift.up j) n).val x m) =
      Koszul.d (LinearMap.proj j) n
        (Stacks.SheafOfModules.exteriorKoszulStalkEquiv A (n + 1) x m) := by
  classical
  have hseq : (Koszul.seqDual fun k : Fin r =>
        TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x (Opens.mem_top x)
          ((Pi.single j (1 : ToType (Osharp.obj.obj (op (⊤ : Opens ↥X))))
            : Fin r → ToType (Osharp.obj.obj (op (⊤ : Opens ↥X)))) k)) =
      LinearMap.proj j := by
    refine Eq.trans (congrArg Koszul.seqDual (funext fun k => ?_))
      (Koszul.seqDual_single_eq_proj j)
    exact (Pi.apply_single (fun _ => TopCat.Presheaf.germ Osharp.obj (⊤ : Opens ↥X) x
      (Opens.mem_top x)) (fun _ => map_zero _) j 1 k).trans (by rw [map_one])
  have hd : A.coordKoszulDNat (ULift.up j) n = (A.coordKoszulChainData (ULift.up j)).dNat n :=
    (A.coordKoszulChainData_dNat (ULift.up j) n).symm
  rw [hd, ← hseq]
  exact Stacks.RegularSequence.exteriorKoszulStalkEquiv_stalkLin
    (A.coordKoszulChainData (ULift.up j))
    (fun k => (Pi.single j (1 : ToType (Osharp.obj.obj (op (⊤ : Opens ↥X))))
      : Fin r → ToType (Osharp.obj.obj (op (⊤ : Opens ↥X)))) k)
    (fun k => freeHomEquiv_freeProj_val (Osharp := Osharp) j k) n x m

end Stalk

end SheafOfModules.TensorExteriorSymmetricAlgebras

end
