module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupStalk
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.RootsOfUnityGaloisModule
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Sections of `μ_n` over a field, and germ evaluation on them

Let `K` be a field and `sbar` a geometric point of `Spec K`, with `Kˢᵉᵖ` the separable closure of
the residue field at its image.  This file puts `μ_n` on the small étale site of [Stacks, Tag
021B] of `Spec K`, reads a section of it as an `n`-th root of unity in the global functions of the
étale neighbourhood, and evaluates that root of unity at a lift of the geometric point, giving the
germ-evaluation map into `μ_n(Kˢᵉᵖ)`.

This is the analogue, for the `n`-torsion of the multiplicative group, of the opening of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.GaloisCohomology.MultiplicativeGroupStalk` and of
`…GaloisCohomology.AdditiveGroupStalk`, and it is the input from which clause (4) of
[Stacks, Tag 03QV] — the correspondence between `μ_n` and the Galois module `μ_n(Kˢᵉᵖ)` — is
assembled, in the way clauses (1), (2) and (3) already are.

## Main definitions

* `AlgebraicGeometry.rootsOfUnitySheafRestriction`: `μ_n` on the small étale site of Tag 021B.
* `AlgebraicGeometry.sepClosureRootsOfUnity`: `μ_n(Kˢᵉᵖ)`, raised to the coefficient universe of
  étale cohomology.
* `AlgebraicGeometry.rootsOfUnitySectionUnit` and
  `AlgebraicGeometry.rootsOfUnitySectionRoot`: the invertible global function underlying a section
  of `μ_n`, and the same read as an element of `μ_n(Γ(U, 𝒪_U))`.
* `AlgebraicGeometry.rootsOfUnitySectionEval`: **germ evaluation on sections of `μ_n`**, as a
  morphism of abelian groups.

## Main results

* `AlgebraicGeometry.rootsOfUnitySectionUnit_pow`: the invertible global function underlying a
  section of `μ_n` is an `n`-th root of unity.
* `AlgebraicGeometry.rootsOfUnitySectionUnit_add` and
  `AlgebraicGeometry.rootsOfUnitySectionUnit_zero`: it is multiplicative in the section, the group
  of sections being written additively — which is what makes germ evaluation a homomorphism.
* `AlgebraicGeometry.coe_restrictRootsOfUnity_sectionRoot`: germ evaluation on `μ_n` is germ
  evaluation on `𝐆_m` of the underlying invertible global function.

## Implementation notes

`μ_n` is `Stacks.Kummer.rootsOfUnitySheaf`, the kernel of the `n`-th power map on `𝐆_m`, so its
sections are not given by a formula; they are read through `Stacks.Kummer.rootsOfUnityι`, the
inclusion `μ_n ⟶ 𝐆_m`, whose value on sections is an invertible global function with `n`-th power
one by `Stacks.Kummer.pow_eq_one_of_rootsOfUnitySheaf`.  Sections of the *restricted* sheaf over
an object `U` of the site of Tag 021B are the sections of `μ_n` over the image of `U` in Mathlib's
small étale site, which is a definitional identity, so the inclusion of the unrestricted sheaf is
applied directly.

Everything ring-theoretic is reused verbatim from the multiplicative file: evaluation of an
invertible global function at a lift of the geometric point is
`AlgebraicGeometry.geometricPointFiberEvalUnits`, and `restrictRootsOfUnity` carries it to the
`n`-th roots of unity.

## References

* [Stacks Project, Tag 03QV](https://stacks.math.columbia.edu/tag/03QV): the example whose
  clause (4) this file is the input for.
* [Stacks Project, Tag 04JQ](https://stacks.math.columbia.edu/tag/04JQ): the stalk equivalence.
* [Stacks Project, Tag 03PL](https://stacks.math.columbia.edu/tag/03PL): the Kummer sequence,
  which presents `μ_n` as the kernel of the `n`-th power map.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

attribute [local instance] GeometricPoint.residueFieldAlgebra

variable (B : BigEtaleSite.{u}) (K : Type u) [Field K] (hK : B.Contains (Spec (.of K)))
  (sbar : GeometricPoint (Spec (.of K))) (n : ℕ)

/-- `μ_n` on the small étale site of Tag 021B of `Spec K`. -/
@[sga "4½ Arcata 2.2.4" "special case"]
abbrev rootsOfUnitySheafRestriction :
    Sheaf (SmallEtale.topology B (Spec (.of K)) hK) AddCommGrpCat.{u + 1} :=
  (smallEtaleSheafRestriction B K hK).obj
    (Stacks.Kummer.rootsOfUnitySheaf.{u, u + 1} (Spec (.of K)) n)

/-- The `n`-th roots of unity of the separable closure, as the abelian group in which the stalk of
`μ_n` is computed. -/
abbrev sepClosureRootsOfUnity : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of (ULift.{u + 1}
    (Additive ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))))

/-- The inclusion `μ_n ⟶ 𝐆_m` on the small étale site of Tag 021B. -/
abbrev rootsOfUnityιRestriction :
    rootsOfUnitySheafRestriction B K hK n ⟶ multiplicativeSheafRestriction B K hK :=
  (smallEtaleSheafRestriction B K hK).map (Stacks.Kummer.rootsOfUnityι.{u, u + 1} _ n)

/-- The invertible global function underlying a section of `μ_n`. -/
def rootsOfUnitySectionUnit (U : SmallEtale B (Spec (.of K)) hK)
    (s : ToType ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U))) :
    (Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))ˣ :=
  Additive.toMul
    (ConcreteCategory.hom
      ((Stacks.Kummer.rootsOfUnityι.{u, u + 1} (Spec (.of K)) n).hom.app
        (op ((SmallEtale.toEtaleSite B (Spec (.of K)) hK).obj U))) s).down

/-- The invertible global function underlying a section of `μ_n` is an `n`-th root of unity. -/
theorem rootsOfUnitySectionUnit_pow (U : SmallEtale B (Spec (.of K)) hK)
    (s : ToType ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U))) :
    rootsOfUnitySectionUnit B K hK n U s ^ n = 1 :=
  Stacks.Kummer.pow_eq_one_of_rootsOfUnitySheaf.{u, u + 1} (Spec (.of K)) n
    ((SmallEtale.toEtaleSite B (Spec (.of K)) hK).obj U) s _ rfl

/-- The component at `U` of the inclusion `μ_n ⟶ 𝐆_m`, as a morphism of abelian groups. -/
private abbrev rootsOfUnityιApp (U : SmallEtale B (Spec (.of K)) hK) :=
  ConcreteCategory.hom
    ((Stacks.Kummer.rootsOfUnityι.{u, u + 1} (Spec (.of K)) n).hom.app
      (op ((SmallEtale.toEtaleSite B (Spec (.of K)) hK).obj U)))

/-- The invertible global function underlying a section of `μ_n` is multiplicative in the
section, the group of sections being written additively. -/
theorem rootsOfUnitySectionUnit_add (U : SmallEtale B (Spec (.of K)) hK)
    (s s' : ToType ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U))) :
    rootsOfUnitySectionUnit B K hK n U (s + s') =
      rootsOfUnitySectionUnit B K hK n U s * rootsOfUnitySectionUnit B K hK n U s' :=
  congrArg (fun z => Additive.toMul (ULift.down z)) (map_add (rootsOfUnityιApp B K hK n U) s s')

/-- The invertible global function underlying the zero section of `μ_n` is `1`. -/
theorem rootsOfUnitySectionUnit_zero (U : SmallEtale B (Spec (.of K)) hK) :
    rootsOfUnitySectionUnit B K hK n U 0 = 1 :=
  congrArg (fun z => Additive.toMul (ULift.down z)) (map_zero (rootsOfUnityιApp B K hK n U))

/-- The `n`-th root of unity in `Γ(U, 𝒪)` underlying a section of `μ_n`. -/
def rootsOfUnitySectionRoot (U : SmallEtale B (Spec (.of K)) hK)
    (s : ToType ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U))) :
    ↥(rootsOfUnity n Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤)) :=
  ⟨rootsOfUnitySectionUnit B K hK n U s,
    (mem_rootsOfUnity _ _).mpr (rootsOfUnitySectionUnit_pow B K hK n U s)⟩

/-- **The germ-evaluation map on sections of `μ_n`**: an `n`-th root of unity in the global
functions on a pointed étale neighbourhood is evaluated at the lift, giving an `n`-th root of
unity in the separable closure. -/
def rootsOfUnitySectionEvalHom (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    ToType ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U)) →+
      ULift.{u + 1}
        (Additive ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))) where
  toFun s := ULift.up (Additive.ofMul
    (restrictRootsOfUnity ((geometricPointFiberEval B K hK sbar U p).hom) n
      (rootsOfUnitySectionRoot B K hK n U s)))
  map_zero' := by
    refine congrArg ULift.up (congrArg Additive.ofMul (Subtype.ext (Units.ext ?_)))
    change (geometricPointFiberEval B K hK sbar U p).hom
        ((rootsOfUnitySectionUnit B K hK n U 0 :
          Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))) = 1
    rw [rootsOfUnitySectionUnit_zero]
    exact map_one _
  map_add' s s' := by
    refine congrArg ULift.up (congrArg Additive.ofMul (Subtype.ext (Units.ext ?_)))
    change (geometricPointFiberEval B K hK sbar U p).hom
        ((rootsOfUnitySectionUnit B K hK n U (s + s') :
          Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))) =
      (geometricPointFiberEval B K hK sbar U p).hom
          ((rootsOfUnitySectionUnit B K hK n U s :
            Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤))) *
        (geometricPointFiberEval B K hK sbar U p).hom
          ((rootsOfUnitySectionUnit B K hK n U s' :
            Γ((SmallEtale.toScheme B (Spec (.of K)) hK).obj U, ⊤)))
    rw [rootsOfUnitySectionUnit_add]
    exact map_mul _ _ _

/-- The germ-evaluation map on sections of `μ_n`, as a morphism of abelian groups. -/
def rootsOfUnitySectionEval (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U) :
    (rootsOfUnitySheafRestriction B K hK n).obj.obj (op U) ⟶
      sepClosureRootsOfUnity K sbar n :=
  AddCommGrpCat.ofHom (rootsOfUnitySectionEvalHom B K hK sbar n U p)

/-- Germ evaluation on sections of `μ_n`, computed on a section. -/
theorem rootsOfUnitySectionEval_apply (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (s : ToType ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U))) :
    ConcreteCategory.hom (rootsOfUnitySectionEval B K hK sbar n U p) s =
      ULift.up (Additive.ofMul
        (restrictRootsOfUnity ((geometricPointFiberEval B K hK sbar U p).hom) n
          (rootsOfUnitySectionRoot B K hK n U s))) := rfl

/-- The `n`-th root of unity in the separable closure produced by germ evaluation is the value at
the lift of the invertible global function underlying the section. -/
theorem coe_restrictRootsOfUnity_sectionRoot (U : SmallEtale B (Spec (.of K)) hK)
    (p : (geometricPointFiber B (Spec (.of K)) hK sbar).obj U)
    (s : ToType ((rootsOfUnitySheafRestriction B K hK n).obj.obj (op U))) :
    ((restrictRootsOfUnity ((geometricPointFiberEval B K hK sbar U p).hom) n
          (rootsOfUnitySectionRoot B K hK n U s) :
        ↥(rootsOfUnity n ↥(GeometricPoint.separableClosure sbar))) :
          (↥(GeometricPoint.separableClosure sbar))ˣ) =
      geometricPointFiberEvalUnits B K hK sbar U p
        (rootsOfUnitySectionUnit B K hK n U s) := by
  refine Units.ext ?_
  rfl

end AlgebraicGeometry

end
