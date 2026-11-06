module

public import StacksFrontier.Deformation.ToposThickening.SolutionIsomorphism

/-!
# The automorphisms of a solution of a deformation problem of ringed topoi

Fix a square-zero extension problem `S : RingedToposExtensionProblem X B` of ringed topoi — the
problem (91.13.0.1) of [Stacks Project, Tag 08V4], consisting of a first order thickening
`t : (Sh(B), O_B) ⟶ (Sh(B'), O_{B'})` of a base ringed topos, a morphism of ringed topoi
`f : (Sh(C), O) ⟶ (Sh(B), O_B)`, an `O`-module `G` and a map `c : f⁻¹J ⟶ G` — and let `P` be a
*solution*, a
`Deformation.ToposThickening.RingedToposExtensionProblem.CompatibleFirstOrderThickening S`.

This file computes the group of automorphisms of `P` fitting into that diagram. The computation
is the source's: an endomorphism of `P` over `O`, under `f⁻¹O_{B'}` and inducing the identity on
`G` is `x ↦ x + δ(x)` for a unique derivation `δ` of the thickened structure sheaf with values
in `G`, and conversely. Since the morphisms of solutions are automatically invertible
([Stacks Project, Tag 08UK], `CompatibleFirstOrderThickening.Hom.isIso`), those endomorphisms
are already the automorphisms, so the automorphism group of a solution is the group of such
derivations.

## Main definitions

* `...CompatibleFirstOrderThickening.Derivation`: a derivation of a solution — a section-wise
  additive map from the thickened structure sheaf to the prescribed module `G`, natural in the
  object of the site, satisfying the Leibniz rule with scalars acting through the reduction, and
  vanishing both on `G` and on the image of `f⁻¹O_{B'}`. It is an additive commutative group
  under pointwise addition.
* `...CompatibleFirstOrderThickening.translate`: the action `p ↦ p + δ` of a derivation of `P`
  on the morphisms of solutions out of `P`.

## Main results

* `...CompatibleFirstOrderThickening.translate_existsUnique`: for two solutions `P`, `Q` the
  morphisms of solutions `P ⟶ Q` are a principal homogeneous space under the derivations of
  `P`: any one of them is carried to any other by exactly one derivation.
* `...CompatibleFirstOrderThickening.autEquivDerivation` and `autEquivDerivation_mul`:
  **Stacks 08V5, clause (3)** — the automorphisms of a solution fitting into the diagram of
  [Stacks Project, Tag 08V4] are canonically isomorphic, as a group, to the derivations of that
  solution.

## What is proved and what is not

The source states clause (3) as an isomorphism with `Ext⁰_O(L_f, G)`, and reaches it from
[Stacks Project, Tag 08UK] through the two identifications `NL_f = τ_{≥ -1}L_f`
([Stacks Project, Tag 08V2]) and `H⁰(L_f) = Ω_f` ([Stacks Project, Tag 08V0]). What is proved
here is the automorphism group itself, for the concrete group of section-wise derivations of the
solution; **its identification with `Ext⁰_O(L_f, G)` is not proved**, and the attribute below
says so.

Three steps separate the two readings, and none of them is in this library. First, a derivation
of the *thickened* structure sheaf vanishing on `G` descends to a derivation of `O`: the
reduction is only locally surjective, so this is a descent along a locally bijective map of
sheaves of abelian groups and not a section-wise construction. Second, derivations of `O` over
`f⁻¹O_B` with values in `G` are `Hom_O(Ω_f, G)` by the corepresentability
`AlgebraicGeometry.SheafOfModules.existsUnique_descDerivation` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PrincipalPartsUniversal.lean` — available, but
only after the first step. Third, `Hom_O(Ω_f, G) = Ext⁰_O(L_f, G)` needs `H⁰(L_f) = Ω_f`
(`AlgebraicGeometry.RingedToposHom.cotangentComplex_homologyZeroIso`, Tag 08V0) together with
the fact that `L_f` is concentrated in non-positive degrees, in the form
`Hom_{D(O)}(K, G[0]) = Hom_O(H⁰(K), G)`; the second factor is a t-structure computation that is
not carried out anywhere in this library.

The two neighbouring statements are formulated in the same way: the acting group of
[Stacks Project, Tag 08UG] clause (2) is the concrete
`Deformation.ToposThickening.LiftDiagram.Derivation` with the identification with
`Hom(Ω_{O₁/O_{B₁}}, g_*G₂)` explicitly not claimed, and the library's form of
[Stacks Project, Tag 08UK] claims the separation half only.

## Implementation notes

The automorphism group of a solution is `Aut P` in the groupoid of solutions and their
compatible isomorphisms, which is how
`...CompatibleFirstOrderThickening.AutomorphismGroup` is defined. It is reached from the
morphisms of solutions in two steps: `CategoryTheory.Groupoid.isoEquivHom` identifies `Aut P`
with the endomorphisms of `P` in that groupoid, which are the *isomorphisms* of solutions, and
`CompatibleFirstOrderThickening.Hom.isIso` of [Stacks Project, Tag 08UK] identifies those with
the morphisms of solutions. The second step is why the instance arguments of that tag — that the
topology admits the forgetful sheaf composition for commutative rings, and that the forgetful
functor reflects isomorphisms — appear here too.

The derivation attached to a morphism of solutions is defined by choice, from the section-wise
surjectivity of the kernel identification of the target, exactly as
`Deformation.ToposThickening.LiftDiagram.diff` is: the difference of two morphisms of solutions
is killed by the reduction of the target, hence is the inclusion of a unique section of `G`.

## References

* [Stacks Project, Tag 08V5](https://stacks.math.columbia.edu/tag/08V5)
* [Stacks Project, Tag 08V4](https://stacks.math.columbia.edu/tag/08V4)
* [Stacks Project, Tag 08UK](https://stacks.math.columbia.edu/tag/08UK)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
* [Stacks Project, Tag 08V0](https://stacks.math.columbia.edu/tag/08V0)
* [Stacks Project, Tag 08V2](https://stacks.math.columbia.edu/tag/08V2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u' w'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{v, u, w}}
  {B : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})]
  [B.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  {S : RingedToposExtensionProblem X B}

namespace CompatibleFirstOrderThickening

/-- The product of two sections of the ideal of a solution vanishes: the ideal has square
zero. -/
public theorem incl_mul_incl (P : S.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ}
    (g h : S.G.val.obj U) : P.incl g * P.incl h = 0 := by
  have hmem : P.incl g * P.incl h ∈
      RingHom.ker (P.reduction.hom.app U).hom * RingHom.ker (P.reduction.hom.app U).hom :=
    Ideal.mul_mem_mul (RingHom.mem_ker.2 (P.reduction_incl g))
      (RingHom.mem_ker.2 (P.reduction_incl h))
  rw [← pow_two, P.squareZero U] at hmem
  simpa using hmem

/-- A morphism of solutions is determined by the underlying homomorphism of sheaves of rings. -/
public theorem Hom.ext' {P Q : S.CompatibleFirstOrderThickening} {p q : Hom P Q}
    (h : p.hom = q.hom) : p = q := by
  cases p; cases q; cases h; rfl

/-! ### Derivations of a solution -/

/-- The derivation situation of a solution `P` of the square-zero extension problem of
[Stacks Project, Tag 08V4]: its thickened structure sheaf with the reduction, the inverse image
of the thickened base mapping into it, and the prescribed module `G` identified with its ideal,
the values being taken over the same reduced structure sheaf. -/
public noncomputable abbrev toSituation (P : S.CompatibleFirstOrderThickening) :
    DerivationSituation X.J where
  O := X.O
  O' := P.extension
  OB' := (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension
  reduction := P.reduction
  f' := P.baseMap
  I := S.G
  inclusion := P.kernelInclusion
  Otarget := X.O
  g := 𝟙 X.O
  G := S.G

/-- The ideal inclusion of the situation of a solution is the solution's own. -/
@[simp]
public theorem toSituation_incl (P : S.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ}
    (g : S.G.val.obj U) : P.toSituation.incl g = P.incl g := rfl

/-- The base structure map of the situation of a solution is the solution's own. -/
@[simp]
public theorem toSituation_f' (P : S.CompatibleFirstOrderThickening) :
    P.toSituation.f' = P.baseMap := rfl

/-- The reduction of the situation of a solution is the solution's own. -/
@[simp]
public theorem toSituation_reduction (P : S.CompatibleFirstOrderThickening) :
    P.toSituation.reduction = P.reduction := rfl

/-- The comparison of the situation of a solution is the identity, so it acts trivially on
sections. -/
@[simp]
public theorem toSituation_g_apply (P : S.CompatibleFirstOrderThickening) {U : X.Cᵒᵖ}
    (x : X.O.obj.obj U) : P.toSituation.g.hom.app U x = x := rfl

/-- A *derivation* of a solution `P`: a derivation of its situation, that is a section-wise
additive map from the thickened structure sheaf of `P` to the prescribed module `G`, natural in
the object of the site, satisfying the Leibniz rule with scalars acting through the reduction
`O' ⟶ O`, and vanishing both on `G` and on the image of the inverse image `f⁻¹O_{B'}` of the
thickened base. This is the group acting on the morphisms of solutions out of `P`, and its
additive group is the one of `Deformation.ToposThickening.Derivation`. -/
public abbrev Derivation (P : S.CompatibleFirstOrderThickening) :=
  _root_.Deformation.ToposThickening.Derivation P.toSituation

namespace Derivation

variable {P : S.CompatibleFirstOrderThickening}

/-- The Leibniz rule of a derivation of a solution, with the scalars read through the
solution's own reduction. -/
public theorem leibniz' (δ : Derivation P) (U : X.Cᵒᵖ) (x y : P.extension.obj.obj U) :
    δ.toFun U (x * y) =
      toRingSection X.J (P.reduction.hom.app U x) • δ.toFun U y +
        toRingSection X.J (P.reduction.hom.app U y) • δ.toFun U x :=
  δ.leibniz U x y

/-- A derivation of a solution vanishes on the prescribed module, read through the solution's
own inclusion. -/
public theorem map_kernel' (δ : Derivation P) (U : X.Cᵒᵖ) (g : S.G.val.obj U) :
    δ.toFun U (P.incl g) = 0 :=
  δ.map_kernel U g

/-- A derivation of a solution vanishes on the image of the thickened base, read through the
solution's own structure map. -/
public theorem map_base' (δ : Derivation P) (U : X.Cᵒᵖ)
    (a : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    δ.toFun U (P.baseMap.hom.app U a) = 0 :=
  δ.map_base U a

end Derivation

/-! ### The morphisms of solutions as a principal homogeneous space -/

variable {P Q : S.CompatibleFirstOrderThickening}

/-- Translating a morphism of solutions by a derivation of its source: the homomorphism
`x ↦ p(x) + δ(x)`. -/
public noncomputable def translate (p : Hom P Q) (δ : Derivation P) : Hom P Q where
  hom := ObjectProperty.homMk
    { app := fun U => CommRingCat.ofHom
        { toFun := fun x => p.hom.hom.app U x + Q.incl (δ.toFun U x)
          map_one' := by
            rw [δ.map_one U, Q.incl_zero, add_zero]
            simp
          map_mul' := fun x y => by
            have hx : p.hom.hom.app U x * Q.incl (δ.toFun U y) =
                Q.incl (toRingSection X.J (P.reduction.hom.app U x) • δ.toFun U y) :=
              (Q.mul_incl (p.hom.hom.app U x) (δ.toFun U y)).trans
                (congrArg (fun scalar : X.O.obj.obj U => Q.incl
                  ((show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
                    X.O).obj.obj U from scalar) •
                    (show S.G.val.obj U from δ.toFun U y))) (p.reduction_apply x))
            have hy : p.hom.hom.app U y * Q.incl (δ.toFun U x) =
                Q.incl (toRingSection X.J (P.reduction.hom.app U y) • δ.toFun U x) :=
              (Q.mul_incl (p.hom.hom.app U y) (δ.toFun U x)).trans
                (congrArg (fun scalar : X.O.obj.obj U => Q.incl
                  ((show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
                    X.O).obj.obj U from scalar) •
                    (show S.G.val.obj U from δ.toFun U x))) (p.reduction_apply y))
            have hp : p.hom.hom.app U (x * y) =
                p.hom.hom.app U x * p.hom.hom.app U y := by simp
            rw [hp, Derivation.leibniz' δ U x y, Q.incl_add, ← hx, ← hy]
            linear_combination -Q.incl_mul_incl (δ.toFun U x) (δ.toFun U y)
          map_zero' := by
            rw [δ.map_zero U, Q.incl_zero, add_zero]
            simp
          map_add' := fun x y => by
            have hp : p.hom.hom.app U (x + y) =
                p.hom.hom.app U x + p.hom.hom.app U y := by simp
            rw [hp, δ.map_add' U x y, Q.incl_add]
            abel }
      naturality := fun {U V} h => by
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        change p.hom.hom.app V (P.extension.obj.map h x) +
            Q.incl (δ.toFun V (P.extension.obj.map h x)) =
          Q.extension.obj.map h (p.hom.hom.app U x + Q.incl (δ.toFun U x))
        have sectionNaturality :=
          (congrArg (fun value : S.G.val.obj V => Q.incl value)
            (δ.naturality h x)).trans (Q.incl_naturality h (δ.toFun U x))
        exact (congrArg₂ (fun first second : Q.extension.obj.obj V => first + second)
          (sheafHom_naturality_apply X.J p.hom h x) sectionNaturality).trans
            (map_add (Q.extension.obj.map h).hom _ _).symm }
  reduction_comm := by
    refine sheafHom_ext X.J fun U x => ?_
    change Q.reduction.hom.app U (p.hom.hom.app U x + Q.incl (δ.toFun U x)) =
      P.reduction.hom.app U x
    rw [map_add, Q.reduction_incl, add_zero, p.reduction_apply]
  baseMap_comm := by
    refine sheafHom_ext X.J fun U a => ?_
    change p.hom.hom.app U (P.baseMap.hom.app U a) +
        Q.incl (δ.toFun U (P.baseMap.hom.app U a)) = Q.baseMap.hom.app U a
    rw [Derivation.map_base' δ U a, Q.incl_zero, add_zero]
    exact congrArg
      (fun k : (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ⟶ Q.extension =>
        k.hom.app U a) p.baseMap_comm
  kernel_comm := fun U g => by
    change p.hom.hom.app U (P.incl g) + Q.incl (δ.toFun U (P.incl g)) = Q.incl g
    rw [Derivation.map_kernel' δ U g, Q.incl_zero, add_zero, p.kernel_comm]

/-- The formula determining a translate. -/
@[simp]
public theorem translate_apply (p : Hom P Q) (δ : Derivation P) (U : X.Cᵒᵖ)
    (x : P.extension.obj.obj U) :
    (translate p δ).hom.hom.app U x = p.hom.hom.app U x + Q.incl (δ.toFun U x) := rfl

/-- The zero derivation acts trivially. -/
public theorem translate_zero (p : Hom P Q) : translate p 0 = p := by
  refine Hom.ext' (sheafHom_ext X.J fun U x => ?_)
  rw [translate_apply, Derivation.zero_toFun, Q.incl_zero, add_zero]

/-- The action of derivations on the morphisms of solutions is additive. -/
public theorem translate_add (p : Hom P Q) (δ ε : Derivation P) :
    translate (translate p δ) ε = translate p (δ + ε) := by
  refine Hom.ext' (sheafHom_ext X.J fun U x => ?_)
  rw [translate_apply, translate_apply, translate_apply, Derivation.add_toFun, Q.incl_add]
  abel

/-- The difference of two morphisms of solutions lies in the prescribed module. -/
public theorem exists_diff (p q : Hom P Q) (U : X.Cᵒᵖ) (x : P.extension.obj.obj U) :
    ∃ g : S.G.val.obj U, Q.incl g = q.hom.hom.app U x - p.hom.hom.app U x := by
  refine Q.exists_incl _ ?_
  rw [map_sub, q.reduction_apply, p.reduction_apply, sub_self]

/-- The section of the prescribed module by which two morphisms of solutions differ. -/
public noncomputable def diff (p q : Hom P Q) (U : X.Cᵒᵖ) (x : P.extension.obj.obj U) :
    S.G.val.obj U :=
  (exists_diff p q U x).choose

/-- The defining property of the difference of two morphisms of solutions. -/
public theorem incl_diff (p q : Hom P Q) (U : X.Cᵒᵖ) (x : P.extension.obj.obj U) :
    Q.incl (diff p q U x) = q.hom.hom.app U x - p.hom.hom.app U x :=
  (exists_diff p q U x).choose_spec

/-- The difference of two morphisms of solutions is a derivation of their common source. -/
public noncomputable def derivationOfHoms (p q : Hom P Q) : Derivation P where
  toFun := diff p q
  map_add' U x y := by
    refine Q.incl_injective ?_
    rw [incl_diff, Q.incl_add, incl_diff, incl_diff, map_add, map_add]
    abel
  naturality {U V} h x := by
    refine Q.incl_injective ?_
    have imageDifference := (incl_diff p q V (P.extension.obj.map h x)).trans
      ((congrArg₂ (fun first second : Q.extension.obj.obj V => first - second)
        (sheafHom_naturality_apply X.J q.hom h x)
        (sheafHom_naturality_apply X.J p.hom h x)).trans
          (map_sub (Q.extension.obj.map h).hom _ _).symm)
    exact imageDifference.trans
      ((congrArg (fun value : Q.extension.obj.obj U => Q.extension.obj.map h value)
        (incl_diff p q U x)).symm.trans (Q.incl_naturality h (diff p q U x)).symm)
  leibniz U x y := by
    refine Q.incl_injective ?_
    change Q.incl (diff p q U (x * y)) = Q.incl
      ((show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O).obj.obj U
          from P.reduction.hom.app U x) • diff p q U y +
        (show ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj X.O).obj.obj U
          from P.reduction.hom.app U y) • diff p q U x)
    have hqx := q.reduction_apply (U := U) x
    have hpy := p.reduction_apply (U := U) y
    rw [Q.incl_add, ← hqx, ← hpy,
      ← Q.mul_incl, ← Q.mul_incl, incl_diff, incl_diff, incl_diff, map_mul, map_mul]
    ring
  map_kernel U g := by
    refine Q.incl_injective ?_
    simp only [toSituation_incl]
    rw [incl_diff, q.kernel_comm, p.kernel_comm, sub_self, Q.incl_zero]
  map_base U a := by
    refine Q.incl_injective ?_
    simp only
    have hp := congrArg
      (fun k : (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ⟶ Q.extension =>
        k.hom.app U a) p.baseMap_comm
    have hq := congrArg
      (fun k : (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ⟶ Q.extension =>
        k.hom.app U a) q.baseMap_comm
    rw [incl_diff, Q.incl_zero]
    change q.hom.hom.app U (P.baseMap.hom.app U a) - p.hom.hom.app U (P.baseMap.hom.app U a) = 0
    rw [show q.hom.hom.app U (P.baseMap.hom.app U a) = Q.baseMap.hom.app U a from hq,
      show p.hom.hom.app U (P.baseMap.hom.app U a) = Q.baseMap.hom.app U a from hp, sub_self]

/-- The difference derivation of two morphisms of solutions, on sections. -/
@[simp]
public theorem derivationOfHoms_toFun (p q : Hom P Q) (U : X.Cᵒᵖ)
    (x : P.extension.obj.obj U) : (derivationOfHoms p q).toFun U x = diff p q U x := rfl

/-- Translating a morphism of solutions by the difference derivation produces the other. -/
public theorem translate_derivationOfHoms (p q : Hom P Q) :
    translate p (derivationOfHoms p q) = q := by
  refine Hom.ext' (sheafHom_ext X.J fun U x => ?_)
  show p.hom.hom.app U x + Q.incl (diff p q U x) = q.hom.hom.app U x
  rw [incl_diff]
  abel

/-- **The morphisms of solutions are a principal homogeneous space** under the derivations of
their common source: any one of them is carried to any other by exactly one derivation. -/
public theorem translate_existsUnique (p q : Hom P Q) :
    ∃! δ : Derivation P, translate p δ = q := by
  refine ⟨derivationOfHoms p q, translate_derivationOfHoms p q, fun ε hε => ?_⟩
  refine Derivation.ext_apply fun U x => ?_
  refine Q.incl_injective ?_
  have h : p.hom.hom.app U x + Q.incl (ε.toFun U x) = q.hom.hom.app U x :=
    congrArg (fun r : Hom P Q => r.hom.hom.app U x) hε
  rw [derivationOfHoms_toFun, incl_diff, ← h]
  abel

/-- The morphisms of solutions out of `P`, based at one of them, are the derivations of `P`. -/
public noncomputable def homEquivDerivation (p : Hom P Q) : Derivation P ≃ Hom P Q where
  toFun := translate p
  invFun := derivationOfHoms p
  left_inv δ := ((translate_existsUnique p (translate p δ)).unique
    (translate_derivationOfHoms p (translate p δ)) rfl)
  right_inv := translate_derivationOfHoms p

/-! ### Stacks 08V5, clause (3) -/

variable [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [(forget CommRingCat.{w}).ReflectsIsomorphisms]

/-- The isomorphisms of solutions are the morphisms of solutions: every morphism of solutions is
invertible by [Stacks Project, Tag 08UK]
(`CompatibleFirstOrderThickening.Hom.isIso`), and the two passages are mutually inverse. -/
public noncomputable def isoEquivHom (P Q : S.CompatibleFirstOrderThickening) :
    Iso P Q ≃ Hom P Q where
  toFun := Iso.toHom
  invFun := Hom.toIso
  left_inv _ := Iso.ext (CategoryTheory.Iso.ext rfl)
  right_inv _ := Hom.ext' rfl

/-- **Stacks Project, Tag 08V5, clause (3).** The automorphisms of a solution of the square-zero
extension problem of [Stacks Project, Tag 08V4] fitting into that diagram are canonically
bijective to the derivations of that solution — section-wise maps from its thickened structure
sheaf to the prescribed module `G` satisfying the Leibniz rule and vanishing on `G` and on the
image of `f⁻¹O_{B'}`. With `autEquivDerivation_mul` this is an isomorphism of groups.

The source writes the group as `Ext⁰_O(L_f, G)`; that identification is **not** proved here, and
the three steps separating the two readings are recorded in the implementation notes of this
file. -/
@[stacks 08V5 "clause (3), the automorphism group of a solution, computed for the concrete \
group of section-wise derivations of the solution rather than Ext⁰_O(L_f, G); that \
identification is not proved, as in the library's Stacks 08UG and Stacks 08UK"]
public noncomputable def autEquivDerivation (P : S.CompatibleFirstOrderThickening) :
    P.AutomorphismGroup ≃ Derivation P :=
  Aut.isoEquiv.trans <| (Groupoid.isoEquivHom P P).trans
    ((isoEquivHom P P).trans (homEquivDerivation (Hom.id P)).symm)

/-- The value of the bijection of `autEquivDerivation` on sections. -/
public theorem incl_autEquivDerivation_toFun (P : S.CompatibleFirstOrderThickening)
    (a : P.AutomorphismGroup) (U : X.Cᵒᵖ) (x : P.extension.obj.obj U) :
    P.incl ((autEquivDerivation P a).toFun U x) = a.asIso.hom.hom.hom.hom.app U x - x :=
  incl_diff (Hom.id P) (Iso.toHom a.asIso.hom) U x

omit [X.J.HasSheafCompose (forget CommRingCat.{w})]
  [(forget CommRingCat.{w}).ReflectsIsomorphisms] in
/-- The product of two automorphisms of a solution acts on sections as the composite of their
actions. -/
public theorem autMul_apply (P : S.CompatibleFirstOrderThickening)
    (a b : P.AutomorphismGroup) (U : X.Cᵒᵖ) (x : P.extension.obj.obj U) :
    (a * b).asIso.hom.hom.hom.hom.app U x =
      a.asIso.hom.hom.hom.hom.app U (b.asIso.hom.hom.hom.hom.app U x) := rfl

/-- **Stacks Project, Tag 08V5, clause (3).** The canonical bijection between the automorphisms
of a solution and the derivations of that solution is an isomorphism of groups: composition of
automorphisms is addition of derivations. -/
@[stacks 08V5 "clause (3), that the canonical bijection of `autEquivDerivation` between the \
automorphisms of a solution and its section-wise derivations is a group isomorphism; the group \
is not identified with Ext⁰_O(L_f, G), as in the library's Stacks 08UG and Stacks 08UK"]
public theorem autEquivDerivation_mul (P : S.CompatibleFirstOrderThickening)
    (a b : P.AutomorphismGroup) :
    autEquivDerivation P (a * b) = autEquivDerivation P a + autEquivDerivation P b := by
  refine Derivation.ext_apply fun U x => ?_
  refine P.incl_injective ?_
  rw [Derivation.add_toFun, P.incl_add, incl_autEquivDerivation_toFun P a U x,
    incl_autEquivDerivation_toFun P b U x, incl_autEquivDerivation_toFun P (a * b) U x,
    autMul_apply P a b U x]
  have hb : b.asIso.hom.hom.hom.hom.app U x =
      x + P.incl ((autEquivDerivation P b).toFun U x) := by
    rw [incl_autEquivDerivation_toFun]
    abel
  rw [hb, map_add]
  have hker := a.asIso.hom.kernel_comm U ((autEquivDerivation P b).toFun U x)
  change a.asIso.hom.hom.hom.hom.app U (P.incl ((autEquivDerivation P b).toFun U x)) =
    P.incl ((autEquivDerivation P b).toFun U x) at hker
  rw [hker, incl_autEquivDerivation_toFun P b U x]
  abel

end CompatibleFirstOrderThickening

end Deformation.ToposThickening.RingedToposExtensionProblem

end
