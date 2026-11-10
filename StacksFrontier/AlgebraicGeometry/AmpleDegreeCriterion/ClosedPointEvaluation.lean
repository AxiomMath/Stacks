module

public import StacksFrontier.AlgebraicGeometry.CohomologyZeroLinear.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ClosedPointDegree
public import StacksFrontier.AlgebraicGeometry.Modules.InvertibleStalkFree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.NonpositiveDegreeSection
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Evaluating a global section of an invertible module at a closed point

Let `k` be a field, let `f : X ⟶ Spec k` be a scheme over `k` and let `𝓛` be an invertible
`𝒪_X`-module. This file makes "the value of a global section of `𝓛` at a point `x`" into a
`k`-linear map out of `Γ(𝓛, ⊤)`, and records the two properties of it that a counting argument
needs: its target is finite-dimensional when `x` is a closed point, and a section whose value
at `x` is zero vanishes at `x` in the sense of [Stacks, Tag 01CY].

The value is taken in the residue field `κ(x)`, read as a `k`-module along the structure
morphism. There is no canonical map `Γ(𝓛, ⊤) → κ(x)`, because `𝓛` is not the structure sheaf;
what there is, for an invertible `𝓛`, is a trivialization `𝓛_x ≃ 𝒪_{X,x}` of the stalk
(`Stacks.InvertibleStalk.nonempty_linearEquiv_stalk`), unique only up to a unit. Composing the
germ map with a choice of trivialization and then with the residue map gives a map whose
*vanishing* does not depend on the choice: the chosen isomorphism carries `𝔪_x 𝓛_x` onto
`𝔪_x 𝒪_{X,x}`, and the latter is the kernel of the residue map. That is why the two theorems
below are an evaluation map stated with no uniqueness claim, together with a one-directional
vanishing criterion, rather than an isomorphism.

Finite-dimensionality of the target is the Hilbert Nullstellensatz: the structural map
`k → κ(x)` is of finite type when `X` is locally of finite type over `k`
(`Stacks.EtaleCohomology.finiteType_fieldToResidue`), and a field of finite type over `k` is
finite over `k`.

## Main definitions

The elided prefix is `AlgebraicGeometry`.

* `residueFieldOverBase`: the residue field `κ(x)` as a `k`-module, along the structure
  morphism.
* `sectionEvaluation`: **the `k`-linear evaluation at `x` of a global section of an invertible
  module**, `Γ(𝓛, ⊤) →ₗ[k] κ(x)`.

## Main results

* `finite_residueFieldOverBase`: **`κ(x)` is finite over `k`** at a closed point of a scheme
  locally of finite type over `k`.
* `notMem_nonvanishingLocus_of_sectionEvaluation_eq_zero`: **a section whose evaluation at `x`
  is zero vanishes at `x`**, that is, `x` is outside its nonvanishing locus.

## Implementation notes

The `k`-module structure on `Γ(𝓛, ⊤)` is the one
`AlgebraicGeometry.restrictScalarsOverBase` puts on it — the same one that
`AlgebraicGeometry.cohomologyOverFieldZeroLinearIso` identifies `H⁰(X, 𝓛)` with — so that a
dimension count performed in cohomology may be read off this evaluation map. That functor
restricts along `f.appLE ⊤ ⊤`, while the module structure on `κ(x)` restricts along
`f.appTop ≫ X.Γevaluation x`; `AlgebraicGeometry.Scheme.Hom.appLE_eq_app` is what reconciles
the two inside the proof that the evaluation map is `k`-linear.

The stalk `𝓛_x` carries two module structures over `𝒪_{X,x}` in this repository, Mathlib's
(named `AlgebraicGeometry.Scheme.Modules.moduleStalkPresheaf` and
`Stacks.ModuleStalk.stalkModule`) and the hand-built one of Tag 01CB
(`Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`). The trivialization of the stalk
and the submodule `𝔪_x 𝓛_x` live at the first, the set
`Stacks.SheafOfModules.nonvanishingLocus` at the second, and
`AlgebraicGeometry.nonvanishingLocus_sectionsOfTop_eq` is what passes between them; nothing
below crosses the two by hand.

## References

* [Stacks Project, Tag 0B5X](https://stacks.math.columbia.edu/tag/0B5X)
* [Stacks Project, Tag 01CY](https://stacks.math.columbia.edu/tag/01CY)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 00FV](https://stacks.math.columbia.edu/tag/00FV)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

/-- **The residue field at a point of a scheme over `k`, as a `k`-module.** The structure
morphism `f : X ⟶ Spec k` composed with evaluation at `x` is a ring map `k → κ(x)`, and this is
`κ(x)` with the `k`-action it gives. -/
public noncomputable abbrev residueFieldOverBase (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) : ModuleCat.{u} k :=
  (ModuleCat.restrictScalars
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom).obj
      (ModuleCat.of (X.residueField x) (X.residueField x))

/-- **The residue field at a closed point of a scheme locally of finite type over `k` is
finite-dimensional over `k`.** The structural map `k → κ(x)` is of finite type, and a field of
finite type over `k` is finite over `k` by the Hilbert Nullstellensatz. -/
@[ega "I 6.4.2" "necessity", sga "3 X 1.4" "partial"]
public theorem finite_residueFieldOverBase (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    Module.Finite k (residueFieldOverBase k f x) := by
  have hbridge : fieldToResidue f x
      = (Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x := by
    simp only [fieldToResidue, fieldToStalk, Scheme.Γevaluation, Scheme.evaluation,
      Category.assoc]
  have hft := Stacks.EtaleCohomology.finiteType_fieldToResidue f x hx
  rw [hbridge] at hft
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  have : Algebra.FiniteType k (X.residueField x) := hft
  exact finite_of_finite_type_of_isJacobsonRing k (X.residueField x)

/-- **The `k`-linear evaluation of a global section of an invertible module at a point.** The
germ at `x` of a global section of `𝓛` is read through a trivialization `𝓛_x ≃ 𝒪_{X,x}` of the
stalk and then mapped to the residue field. The trivialization is only unique up to a unit, so
the individual values of this map carry no meaning; what is well defined is whether a value is
zero, which is `AlgebraicGeometry.notMem_nonvanishingLocus_of_sectionEvaluation_eq_zero`. -/
public noncomputable def sectionEvaluation (k : Type u) [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (P : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P] (x : X) :
    (restrictScalarsOverBase k f).obj
        ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).obj P) →ₗ[k]
      residueFieldOverBase k f x :=
  let e := (Stacks.InvertibleStalk.nonempty_linearEquiv_stalk P x).some
  { toFun := fun s => X.residue x (e ((P.presheaf.Γgerm x).hom s))
    map_add' := fun s t =>
      (congrArg (fun z => X.residue x (e z))
          (map_add (P.presheaf.Γgerm x).hom s t)).trans
        ((congrArg (fun y => X.residue x y) (e.map_add _ _)).trans
          (map_add (X.residue x).hom _ _))
    map_smul' := fun a s => by
      refine (congrArg (fun z => X.residue x (e z)) (Stacks.ModuleStalk.Γgerm_smul P x
        (((Scheme.ΓSpecIso (.of k)).inv ≫ f.appLE ⊤ ⊤ (by simp)).hom a) s)).trans ?_
      refine (congrArg (fun y => X.residue x y) (e.map_smul _ _)).trans ?_
      refine (map_mul (X.residue x).hom _ _).trans ?_
      refine congrArg (fun v : Γ(X, ⊤) =>
        X.residue x ((X.presheaf.Γgerm x).hom v) *
          X.residue x (e ((P.presheaf.Γgerm x).hom s))) ?_
      exact congrArg (fun q : Γ(Spec (.of k), ⊤) ⟶ Γ(X, ⊤) =>
        q.hom ((Scheme.ΓSpecIso (.of k)).inv.hom a)) f.appLE_eq_app }

/-- **A global section of an invertible module whose evaluation at `x` vanishes vanishes at
`x`.** The chosen trivialization of the stalk carries `𝔪_x 𝓛_x` onto the maximal ideal of
`𝒪_{X,x}`, which is the kernel of the residue map, so a zero value forces the germ into
`𝔪_x 𝓛_x` — that is, `x` lies outside the nonvanishing locus of [Stacks, Tag 01CY]. -/
public theorem notMem_nonvanishingLocus_of_sectionEvaluation_eq_zero (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (P : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 P] (x : X)
    (s : (restrictScalarsOverBase k f).obj
      ((SheafOfModules.evaluation X.ringCatSheaf (Opposite.op (⊤ : X.Opens))).obj P))
    (hs : sectionEvaluation k f P x s = 0) :
    x ∉ Stacks.SheafOfModules.nonvanishingLocus (X := X.toRingedSpace) P
      (Stacks.SheafOfModules.sectionsOfTop (X := X.toRingedSpace) P s) := by
  rw [nonvanishingLocus_sectionsOfTop_eq P s]
  intro hmem
  refine hmem ?_
  set e := (Stacks.InvertibleStalk.nonempty_linearEquiv_stalk P x).some
  set z := (P.presheaf.Γgerm x).hom s
  have hker : e z ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk x) :=
    (IsLocalRing.residue_eq_zero_iff _).mp (by
      change X.residue x (e z) = 0
      exact hs)
  have hgen : z = e z • e.symm 1 := by
    apply e.injective
    simp
  rw [hgen]
  exact Stacks.ModuleStalk.smul_mem_maximalSmul_of_mem_maximalIdeal hker _

end AlgebraicGeometry

end
