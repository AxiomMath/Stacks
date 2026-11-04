module

public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Basic
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPresentations
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank
public import StacksFrontier.AlgebraicGeometry.InvertibleLocallyFree.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Defs
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksCore.Tactic.StacksAttribute

/-!
# Symmetry of the Euler characteristic of a tensor product, and the formula of Tag 0AYV at
`ℰ = 𝒪_X`

Tag 0AYV computes `χ(X, ℰ ⊗ ℱ)` on a proper curve over a field, for `ℰ` finite locally free of
rank `n` and `ℱ` coherent, as `r · deg(ℰ) + n · χ(X, ℱ)` where `r` is the rank of `ℱ` at the
generic point. Its proof runs the dévissage of Tag 01YH over the property "the formula holds for
`ℱ`", and that dévissage has two base cases: `ℱ = 𝒪_X` and a sheaf supported at a closed point.
`StacksFrontier/AlgebraicGeometry/CurveTensorEuler/Basic.lean` proves the first of those.

This file proves the *other* boundary instance of the same formula — the one in the locally free
argument rather than in the coherent one, `ℰ = 𝒪_X` — together with the unconditional ingredients
the dévissage needs and that the library did not have: coherence of `ℰ` and of `ℰ ⊗ ℱ` on a curve,
the symmetry `χ(X, ℱ ⊗ 𝒢) = χ(X, 𝒢 ⊗ ℱ)`, and `deg(𝒪_X) = 0`. The left unitor of the Tag 01CA
tensor product, `AlgebraicGeometry.SheafOfModules.tensorSheafUnitLeftIso`, is imported from
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections`.

## Main results

* `AlgebraicGeometry.SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve`: a
  finite locally free module of constant rank on a curve over a field is coherent.
* `AlgebraicGeometry.isCoherent_tensorSheaf_of_isCurve`: on a curve over a field, the tensor
  product of a finite locally free module of constant rank with a coherent module is coherent.
* `AlgebraicGeometry.eulerCharacteristic_tensorSheaf_comm`: `χ(X, ℱ ⊗ 𝒢) = χ(X, 𝒢 ⊗ ℱ)`.
* `AlgebraicGeometry.curveDegree_unit_eq_zero`: `deg(𝒪_X) = 0`.
* `AlgebraicGeometry.eulerCharacteristic_unit_tensor_eq_curveDegree_add`: **the formula of Tag
  0AYV at `ℰ = 𝒪_X`**, namely `χ(X, 𝒪_X ⊗ ℱ) = r · deg(𝒪_X) + 1 · χ(X, ℱ)`, for *every* integer
  `r`.

## Implementation notes

**Why the generic-rank slot is an arbitrary integer.** At `ℰ = 𝒪_X` the degree is zero, so the
formula of Tag 0AYV holds whatever is put in the place of the rank of `ℱ` at the generic point.
Quantifying over that slot is therefore a generalisation of the tag's instance at `ℰ = 𝒪_X`, not
a weakening of it, and it has the advantage of not mentioning the generic rank at all — which
the library does not yet have under any name, and which belongs to Tag 05P2.

**Coherence is derived rather than assumed.** On a curve the structure morphism is locally of
finite type, so `AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian` makes `X` locally
Noetherian, and Tag 01XZ then makes a finite locally free module coherent and the structure sheaf
coherent. Both are theorems in the structure morphism rather than instances, which is why
`CurveTensorEuler/Basic.lean` carries them as instance hypotheses; the statements here take
`AlgebraicGeometry.IsCurve` and discharge them. The coherence witnesses are passed explicitly
with `@`, because `ℰ.IsCoherent` is stated at the `AlgebraicGeometry.Scheme.ringCatSheaf`
spelling of the sheaf of rings while `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`
  reads its arguments at the
`structureSheafRing` spelling, and instance search —
  being syntactic — does not
cross between the two.

**Which fixed-rank class.** The repository has two classes named `IsFiniteLocallyFreeOfRank` with
the same body. Everything here is stated over the library one,
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`
(`StacksFrontier/Topology/Sheaves/Modules/LocallyFree.lean`, carrying `@[stacks 01C6 "(3)"]`), which
is the class `AlgebraicGeometry.curveDegree` consumes.
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit` supplies the structure sheaf at
rank one for that class, and is registered as an instance here; no bridge between the two classes
is introduced.

**What Tag 0AYV still owes**, beyond the two boundary instances proved here: the dévissage of Tag
01YH, which the library does not have; unconditional additivity of `χ` along a short exact
sequence (Tag 08AA), available in
`StacksFrontier/AlgebraicGeometry/EulerCharAdditivity/TwoOutOfThree.lean` only with the finite
dimensionality of Tag 02O6 and the vanishing of Tag 01XJ as hypotheses; the second base case,
Tag 0AYT (5); and the generic rank of a coherent module with its additivity, Tag 05P2. No
`@[stacks 0AYV]` attribute is attached in this file.

## References

* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.SheafOfModules

/-! The structure sheaf of a scheme is finite locally free of rank one for the library class
`AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank`; that is
`AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_unit`, imported from
`StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Rank`.  It is registered as an instance here,
which is the form the coherence statements below resolve it in. -/
attribute [instance] isFiniteLocallyFreeOfRank_unit

/-- **A finite locally free module of constant rank on a curve over a field is coherent.** The
structure morphism of a curve is locally of finite type, hence `X` is locally Noetherian, and
Tag 01XZ applies. -/
theorem isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [AlgebraicGeometry.IsCurve k f] (E : X.Modules)
    (n : ℕ) [IsFiniteLocallyFreeOfRank.{u, u, u} E n] : _root_.SheafOfModules.IsCoherent E :=
  @Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isFiniteLocallyFree X
    (AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f) E
    (IsFiniteLocallyFreeOfRank.isFiniteLocallyFree.{u, u, u} E n)

end AlgebraicGeometry.SheafOfModules

namespace AlgebraicGeometry

variable (k : Type u) [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- **On a curve over a field, the tensor product of a finite locally free module of constant
rank with a coherent module is coherent.** This is the coherence witness that the conclusion of
Tag 0AYV carries as an existential. -/
theorem isCoherent_tensorSheaf_of_isCurve [IsCurve k f] (E : X.Modules) (n : ℕ)
    [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] (F : X.Modules)
    [hF : SheafOfModules.IsCoherent F] :
    ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (E)).obj
        (F))).IsCoherent :=
  @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace E F
    (SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f E n) hF

/-- **The Euler characteristic of a tensor product is symmetric in its two arguments.** This is
the bridge between the two argument orders in which the tag chain states the tensor product:
Tag 0AYV writes `ℰ ⊗ ℱ` with the locally free factor first, Tag 0AYT (5) writes it with the
coherent factor first. -/
theorem eulerCharacteristic_tensorSheaf_comm [IsProper f] (F G : X.Modules)
    [hF : SheafOfModules.IsCoherent F] [hG : SheafOfModules.IsCoherent G] :
    @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (G)))
        (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace F G hF hG) =
      @eulerCharacteristic k _ X f _ ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (G)).obj (F)))
        (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace G F hG hF) :=
  @eulerCharacteristic_eq_of_iso k _ X f _ _ _
    (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace F G hF hG)
    (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace G F hG hF)
    (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X.toRingedSpace F G)

/-- **The degree of the structure sheaf is zero.** Immediate from the definition of the degree as
`χ(X, ℰ) - rank · χ(X, 𝒪_X)`. -/
theorem curveDegree_unit_eq_zero [IsProper f] (hdim : topologicalKrullDim X ≤ 1)
    [hO : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf)] :
    @curveDegree k _ X f _ hdim (SheafOfModules.unit X.ringCatSheaf) 1
        (SheafOfModules.isFiniteLocallyFreeOfRank_unit X) = 0 := by
  rw [@curveDegree_eq_eulerCharacteristic_sub k _ X f _ hdim _ 1
    (SheafOfModules.isFiniteLocallyFreeOfRank_unit X) hO hO]
  ring

/-- **The formula of Tag 0AYV at `ℰ = 𝒪_X`**: `χ(X, 𝒪_X ⊗ ℱ) = r · deg(𝒪_X) + 1 · χ(X, ℱ)`.
Since `deg(𝒪_X) = 0` this holds for *every* integer `r`, in particular for the rank of `ℱ` at the
generic point, which is what the tag puts there. Together with
`AlgebraicGeometry.eulerCharacteristic_tensor_unit_eq_curveDegree_add` this gives both boundary
instances of the tag's formula. -/
theorem eulerCharacteristic_unit_tensor_eq_curveDegree_add [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (F : X.Modules) [hF : SheafOfModules.IsCoherent F]
    (r : ℤ) :
    @eulerCharacteristic k _ X f _
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
            ((SheafOfModules.unit X.ringCatSheaf))).obj (F)))
        (isCoherent_tensorSheaf_of_isCurve k f (SheafOfModules.unit X.ringCatSheaf) 1 F) =
      r * @curveDegree k _ X f _ hdim (SheafOfModules.unit X.ringCatSheaf) 1
            (SheafOfModules.isFiniteLocallyFreeOfRank_unit X) +
        (1 : ℤ) * eulerCharacteristic k f F := by
  have hunit : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    SheafOfModules.isCoherent_of_isFiniteLocallyFreeOfRank_of_isCurve k f _ 1
  have hiso : @eulerCharacteristic k _ X f _
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          ((SheafOfModules.unit X.ringCatSheaf))).obj (F)))
      (isCoherent_tensorSheaf_of_isCurve k f (SheafOfModules.unit X.ringCatSheaf) 1 F) =
        eulerCharacteristic k f F :=
    @eulerCharacteristic_eq_of_iso k _ X f _ _ _
      (isCoherent_tensorSheaf_of_isCurve k f (SheafOfModules.unit X.ringCatSheaf) 1 F) hF
      (SheafOfModules.tensorSheafUnitLeftIso X.toRingedSpace F)
  rw [hiso, @curveDegree_unit_eq_zero k _ X f _ hdim hunit]
  ring

/-- The formula of Tag 0AYV at `ℰ = 𝒪_X`, in the existential shape of that tag, which also
supplies coherence of the tensor product. -/
theorem exists_eulerCharacteristic_unit_tensor_eq_curveDegree_add [IsCurve k f] [IsProper f]
    (hdim : topologicalKrullDim X ≤ 1) (F : X.Modules) [SheafOfModules.IsCoherent F] (r : ℤ) :
    ∃ h : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
        ((SheafOfModules.unit X.ringCatSheaf))).obj (F))).IsCoherent,
      @eulerCharacteristic k _ X f _
          ((((Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
              ((SheafOfModules.unit X.ringCatSheaf))).obj (F))) h =
        r * @curveDegree k _ X f _ hdim (SheafOfModules.unit X.ringCatSheaf) 1
              (SheafOfModules.isFiniteLocallyFreeOfRank_unit X) +
          (1 : ℤ) * eulerCharacteristic k f F :=
  ⟨_, eulerCharacteristic_unit_tensor_eq_curveDegree_add k f hdim F r⟩

end AlgebraicGeometry

end
