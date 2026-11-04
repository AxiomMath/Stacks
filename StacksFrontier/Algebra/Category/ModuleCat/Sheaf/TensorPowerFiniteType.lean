module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFiniteType
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPresentation
import StacksCore.Tactic.StacksAttribute

/-!
# Finiteness of the tensor powers of a sheaf of modules

Let `(X, 𝒪_X)` be a ringed space and `F` a sheaf of `𝒪_X`-modules of finite presentation. Then
every tensor power `Tⁿ F` is again of finite presentation. This is clause (3) of Stacks Tag 01CK
for the tensor powers, the remaining third of that clause; the symmetric and the exterior thirds
are `Stacks.SheafOfModules.isFinitePresentation_symmetricPower` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SymmetricPowerFiniteType` and
`isFinitePresentation_exteriorPower` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType`.

The mathematics is not Tag 01CJ, which presents the two *quotients* of the tensor algebra by a
three-term sequence and does not apply to a tensor power, but the induction already used for
quasi-coherence in
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerPresentation`: `Tⁿ⁺²(F)` is
`F ⊗ Tⁿ⁺¹(F)` by definition, `Stacks.SheafOfModules.presentationTensorSheaf` presents a tensor
product of two presented sheaves of modules, and `T⁰(F)` and `T¹(F)` are the structure sheaf and
`F`. What this file adds to that induction is the bookkeeping of finiteness along it: the
presentation of a tensor product has generators `σ₁ × σ₂` and relations
`(ι₁ × σ₂) ⊕ (σ₁ × ι₂)`, so it is finite as soon as the two given presentations are, and every
other step of the induction either keeps the index types or is one of the two base cases.

## Main results

* `Stacks.SheafOfModules.presentationTensorSheaf_isFinite`: the presentation of a tensor product
  built by `Stacks.SheafOfModules.presentationTensorSheaf` is finite when the two given
  presentations are.
* `Stacks.SheafOfModules.exists_isFinite_presentation_tensorSheaf`: **a tensor product of two
  finitely presented sheaves of modules is finitely presented**, over an arbitrary site.
* `Stacks.SheafOfModules.exists_isFinite_presentation_tensorPower` and
  `exists_isFinite_presentation_tensorPower_over`: a finite presentation of `F` presents every
  tensor power of `F` finitely, globally and over an object of the site.
* `Stacks.SheafOfModules.isFinitePresentation_tensorPower`: **clause (3) of Tag 01CK for the
  tensor powers** — each tensor power of a sheaf of modules of finite presentation on a ringed
  space is of finite presentation.

## Implementation notes

**The finiteness transfers are the ones the exterior half already needed.** `presentationOfIso`
and `presentationUnit` are the only two other constructions appearing in the induction, and
`Stacks.SheafOfModules.presentationOfIso_isFinite` and `presentationUnit_isFinite` of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExteriorPowerFiniteType` are not
exterior-specific, so nothing has to be reproved; as there, the finiteness hypothesis of
`presentationOfIso_isFinite` is supplied by name rather than left to instance search, because
the comparison isomorphisms involved are not seen through at reducible transparency.

**Why the index types of `presentationTensorSheaf` can be read off.**
`Stacks.SheafOfModules.presentationTensorSheaf` ends in
`SheafOfModules.presentationOfIsCokernelFree` applied to a morphism
`free ((ι₁ × σ₂) ⊕ (σ₁ × ι₂)) ⟶ free (σ₁ × σ₂)`, so its generator and relation index types are
those two types definitionally, and the instance below is proved by giving the two `Finite`
instances directly.

**Uniformity in the degree.** As in the quasi-coherent case, the open over which `F` is
presented presents every tensor power of `F`, with no further shrinking:
`Stacks.SheafOfModules.exists_isFinite_presentation_tensorPower_over` is stated for a fixed
object of the site and every `n`.

## References

* [Stacks Project, Tag 01CE](https://stacks.math.columbia.edu/tag/01CE)
* [Stacks Project, Tag 01CJ](https://stacks.math.columbia.edu/tag/01CJ)
* [Stacks Project, Tag 01CK](https://stacks.math.columbia.edu/tag/01CK)
* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf AlgebraicGeometry
  TopologicalSpace

universe v u w

namespace Stacks.SheafOfModules

section Site

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {Osharp : Sheaf J CommRingCat.{w}}
  [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

open _root_.SheafOfModules in
/-- **The presentation of a tensor product built from two presentations by free sheaves of
modules on finite index types is finite.** Its generators are `σ₁ × σ₂` and its relations
`(ι₁ × σ₂) ⊕ (σ₁ × ι₂)`, which is what `Stacks.SheafOfModules.presentationTensorSheaf` hands to
`SheafOfModules.presentationOfIsCokernelFree`. -/
instance presentationTensorSheaf_isFinite {ι₁ σ₁ ι₂ σ₂ : Type w}
    [Finite ι₁] [Finite σ₁] [Finite ι₂] [Finite σ₂]
    {M N : _root_.SheafOfModules.{w} (toRingCat J Osharp)}
    {f₁ : free (R := toRingCat J Osharp) ι₁ ⟶ free σ₁} {g₁ : free σ₁ ⟶ M}
    {z₁ : f₁ ≫ g₁ = 0} (h₁ : IsColimit (CokernelCofork.ofπ g₁ z₁))
    {f₂ : free (R := toRingCat J Osharp) ι₂ ⟶ free σ₂} {g₂ : free σ₂ ⟶ N}
    {z₂ : f₂ ≫ g₂ = 0} (h₂ : IsColimit (CokernelCofork.ofπ g₂ z₂)) :
    (presentationTensorSheaf J h₁ h₂).IsFinite where
  isFiniteType_generators := ⟨inferInstanceAs (Finite (σ₁ × σ₂))⟩
  isFiniteType_relations := ⟨inferInstanceAs (Finite ((ι₁ × σ₂) ⊕ (σ₁ × ι₂)))⟩

/-- **A tensor product of two finitely presented sheaves of modules is finitely presented.** This
is the finite refinement of `Stacks.SheafOfModules.nonempty_presentation_tensorSheaf`, i.e. of
the key step of Stacks 01CE. -/
theorem exists_isFinite_presentation_tensorSheaf
    {M N : _root_.SheafOfModules.{w} (toRingCat J Osharp)}
    (p : M.Presentation) [hp : p.IsFinite] (q : N.Presentation) [hq : q.IsFinite] :
    ∃ r : ((tensorSheafRight J N).obj M).Presentation, r.IsFinite :=
  ⟨presentationTensorSheaf J p.isColimitRelationsHom q.isColimitRelationsHom,
    presentationTensorSheaf_isFinite J _ _⟩

/-- **A finite presentation of `F` presents every tensor power of `F` finitely.** This is the
finite refinement of `Stacks.SheafOfModules.nonempty_presentation_tensorPower`: the induction is
the same, the degree-`n+2` power being `F ⊗ Tⁿ⁺¹(F)` by definition, and the two index types
produced at each step are products and sums of the given ones. -/
theorem exists_isFinite_presentation_tensorPower
    {F : _root_.SheafOfModules.{w} (toRingCat J Osharp)} (p : F.Presentation) [hp : p.IsFinite]
    (n : ℕ) :
    ∃ r : (_root_.SheafOfModules.tensorPower J F n).Presentation, r.IsFinite := by
  induction n with
  | zero => exact ⟨presentationUnit, presentationUnit_isFinite⟩
  | succ m ih =>
    match m, ih with
    | 0, _ => exact ⟨p, hp⟩
    | (m + 1), ih =>
      obtain ⟨q, hq⟩ := ih
      exact exists_isFinite_presentation_tensorSheaf J p q (hq := hq)

section Over

variable [∀ X : C, (J.over X).HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [∀ X : C, HasSheafify (J.over X) AddCommGrpCat.{w}]
  [∀ X : C, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **A finite presentation of `F` over an object `U` of the site presents every tensor power of
`F` finitely over that same `U`.** The uniformity in the degree is the same as in
`Stacks.SheafOfModules.nonempty_presentation_tensorPower_over`: the object is the one over which
`F` is presented, and no degree needs a smaller one. -/
theorem exists_isFinite_presentation_tensorPower_over (U : C)
    {F : _root_.SheafOfModules.{w} (toRingCat J Osharp)} (p : (F.over U).Presentation)
    [hp : p.IsFinite] (n : ℕ) :
    ∃ r : ((_root_.SheafOfModules.tensorPower J F n).over U).Presentation, r.IsFinite := by
  induction n with
  | zero => exact ⟨presentationUnit, presentationUnit_isFinite⟩
  | succ m ih =>
    match m, ih with
    | 0, _ => exact ⟨p, hp⟩
    | (m + 1), ih =>
      obtain ⟨q, hq⟩ := ih
      obtain ⟨r, hr⟩ :=
        exists_isFinite_presentation_tensorSheaf (J.over U) (Osharp := Osharp.over U) p q
          (hp := hp) (hq := hq)
      exact ⟨presentationOfIso
        (Stacks.TensorCoherence.tensorSheafOverIso F
          (_root_.SheafOfModules.tensorPower J F (m + 1)) U) r,
        presentationOfIso_isFinite _ _ (hP := hr)⟩

end Over

end Site

/-! ### Clause (3) of Tag 01CK for the tensor powers -/

section Conclusion

universe t

variable {X : AlgebraicGeometry.RingedSpace.{t, t}}
  (F : _root_.SheafOfModules.{t} (structureSheafRing X))
  (A : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) F)

/-- **A finite presentation of `F` over an open presents the degree-`n` piece of the tensor
algebra of `F` finitely over that same open.** This is
`Stacks.SheafOfModules.exists_isFinite_presentation_tensorPower_over` read at the site of opens
of a ringed space and transported along the identification
`SheafOfModules.TensorExteriorSymmetricAlgebras.tensorPieceIso` of that piece with the degree-`n`
tensor power. -/
theorem exists_isFinite_presentation_tensorPiece_over (U : Opens X.carrier)
    (p : (F.over U).Presentation) [hp : p.IsFinite] (n : ℕ) :
    ∃ r : ((A.tensor.piece (n : ℤ)).over U).Presentation, r.IsFinite := by
  obtain ⟨r, hr⟩ := exists_isFinite_presentation_tensorPower_over
    (Opens.grothendieckTopology X.carrier) (Osharp := X.sheaf) U p n (hp := hp)
  exact ⟨presentationOfIso
    ((_root_.SheafOfModules.overFunctor
      (structureSheafRing X) U).mapIso (A.tensorPieceIso n)).symm r,
    presentationOfIso_isFinite _ _ (hP := hr)⟩

/-- **Each tensor power of a sheaf of modules of finite presentation on a ringed space is of
finite presentation.** This is clause (3) of [Stacks, Tag 01CK] for the tensor powers. The
covering family is the one that presents `F` finitely; no degree needs a smaller open, because
`Stacks.SheafOfModules.exists_isFinite_presentation_tensorPiece_over` presents every degree
finitely over that same open. -/
@[stacks 01CK "tensor powers of a module of finite presentation"]
theorem isFinitePresentation_tensorPower [F.IsFinitePresentation] (n : ℕ) :
    (A.tensor.piece (n : ℤ)).IsFinitePresentation := by
  obtain ⟨c, hc⟩ :=
    _root_.SheafOfModules.IsFinitePresentation.exists_quasicoherentData.{t, t, t} F
  have hp : ∀ i, ∃ r : ((A.tensor.piece (n : ℤ)).over (c.X i)).Presentation, r.IsFinite := fun i =>
    exists_isFinite_presentation_tensorPiece_over F A (c.X i) (c.presentation i) n
      (hp := hc.isFinite_presentation i)
  let q : _root_.SheafOfModules.QuasicoherentData.{t, t, t, t} (A.tensor.piece (n : ℤ)) :=
    { I := c.I
      X := c.X
      coversTop := c.coversTop
      presentation := fun i => (hp i).choose }
  have hq : _root_.SheafOfModules.QuasicoherentData.IsFinitePresentation.{t, t, t, t} q := by
    constructor
    intro i
    exact (hp i).choose_spec
  constructor
  exact ⟨q, hq⟩

end Conclusion

end Stacks.SheafOfModules

end
