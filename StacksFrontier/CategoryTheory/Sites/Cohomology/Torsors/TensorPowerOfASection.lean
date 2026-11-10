module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalInduced
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.PicardGroupOfARingedSiteGeneral

/-!
# Tensor powers of a section of an invertible module

Let `(C, O)` be a ringed site and `L` an invertible `O`-module. A section `s` of `L` over an
object `U` has an `n`-th tensor power `s^{⊗ n}`, a section of `L^{⊗ n}` over `U`: it is formed
from the tensor product of sections of Tag 01CA and the successor comparison of the tensor
powers of Tag 01CU. Scaling `s` by a section of the structure sheaf scales `s^{⊗ n}` by its
`n`-th power, the construction commutes with restriction, and the `n`-th power of a local
generator is a local generator — the last because the tensor product of two local generators is
one.

## Main definitions

* `Stacks.Cohomology.Torsors.Generators.tpow` is the `n`-th tensor power of an invertible module,
  at the natural-number exponent and over the ring sheaf of the site.
* `Stacks.Cohomology.Torsors.Generators.tpowSuccIso` is the successor comparison at that
  exponent.
* `Stacks.Cohomology.Torsors.Generators.powerSection` is the `n`-th tensor power of a section.
* `Stacks.Cohomology.Torsors.Generators.generatorPowerSection` is its refinement to local
  generators.
* `Stacks.Cohomology.Torsors.Generators.powerMap` is the `n`-th tensor power of an isomorphism of
  invertible modules.

## Main results

* `Stacks.Cohomology.Torsors.Generators.powerSection_smul`: `(r • s)^{⊗ n} = r^n • s^{⊗ n}`.
* `Stacks.Cohomology.Torsors.Generators.powerSection_restrict`: tensor powers of sections commute
  with restriction.
* `Stacks.Cohomology.Torsors.Generators.generatorPowerSection_val`: the local generator produced
  from a local generator is its tensor power.
* `Stacks.Cohomology.Torsors.Generators.tensorProductIso_tensorSection`: the tensor product of
  two isomorphisms sends the tensor product of two sections to the tensor product of their
  images.
* `Stacks.Cohomology.Torsors.Generators.powerSection_map`: the `n`-th tensor power of an
  isomorphism sends `s^{⊗ n}` to the `n`-th tensor power of the image of `s`.

## Implementation notes

The tensor powers of Tag 01CU are indexed by the integers and are defined over
`Stacks.SheafOfModules.TensorSheafification.structureSheaf O hO`, while the local generators of
Tag 040E are indexed over the ring sheaf `Stacks.SheafOfModules.Tensor.ringSheaf` of a ringed
site. The two sheaves of rings are the same, so `tpow` is a type ascription of `tensorPower` at
the second spelling; writing the powers this way is what makes the scalar multiplications of the
two developments the same instance, without which neither `powerSection_smul` nor
`Stacks.Cohomology.Torsors.Generators.tensorSection_smul'` can even be stated at a tensor power.

`powerMap` composes its three constituents to the *left*, `(A ≪≫ B) ≪≫ C`, so that the value of
the composite on a section is the nested application by `rfl`. Associated to the right, the
inner `Iso.trans` has a middle object whose sheaf condition is a projection of the ringed site,
which is not type-correct at `implicit` transparency and so blocks `rw` and `simp` on
`CategoryTheory.Iso.trans_hom`.

`tensorProductIso_tensorSection` is naturality of the sheafification unit, which is why
`Stacks.SheafOfModules.toSheafifyVal_naturality` is the only import beyond the Picard
development.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Tag 040E](https://stacks.math.columbia.edu/tag/040E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.SheafOfModules.Invertible (tensorPower tensorPowerSuccIso tensorProductIso)
open Stacks.SheafOfModules (IsInvertible)

universe u v w

namespace Stacks.Cohomology.Torsors.Generators

variable (X : RingedSite.{u, v, w})
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify X.J AddCommGrpCat.{w}]

/-- The `k`-th tensor power, as a sheaf of modules over the ring sheaf of the site. -/
noncomputable abbrev tpow (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (k : ℕ) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  tensorPower X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L (k : ℤ)

/-- The successor comparison for natural tensor powers. -/
noncomputable def tpowSuccIso (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (k : ℕ) :
    tensorSheafOfModules X (tpow X L k) L ≅ tpow X L (k + 1) :=
  tensorPowerSuccIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L (k : ℤ)

/-- The `k`-th tensor power of a section. -/
noncomputable def powerSection (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (U : X.C)
    (s : L.val.obj (op U)) :
    (k : ℕ) → (tpow X L k).val.obj (op U)
  | 0 => (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
  | k + 1 => (tpowSuccIso X L k).hom.val.app (op U)
      (tensorSection X (tpow X L k) L U (powerSection L U s k) s)

/-- The tensor power of a section at a successor exponent. -/
theorem powerSection_succ (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (U : X.C)
    (s : L.val.obj (op U)) (k : ℕ) :
    powerSection X L U s (k + 1) =
      (tpowSuccIso X L k).hom.val.app (op U)
        (tensorSection X (tpow X L k) L U (powerSection X L U s k) s) := rfl

/-- Scaling a section scales its `k`-th tensor power by the `k`-th power of the scalar. -/
theorem powerSection_smul (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (U : X.C)
    (r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
    (s : L.val.obj (op U)) :
    (k : ℕ) → powerSection X L U (r • s) k = r ^ k • powerSection X L U s k
  | 0 => by
      change (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) =
        r ^ 0 • (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))
      rw [pow_zero, one_smul]
  | k + 1 => by
      rw [powerSection_succ, powerSection_succ, powerSection_smul L U r s k,
        tensorSection_smul', pow_succ]
      exact ((tpowSuccIso X L k).hom.val.app (op U)).hom.map_smul _ _

/-- Tensor powers of sections commute with restriction. -/
theorem powerSection_restrict (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] {U V : X.C}
    (f : V ⟶ U) (s : L.val.obj (op U)) :
    (k : ℕ) →
      (tpow X L k).val.restrictₛₗ f.op (powerSection X L U s k) =
        powerSection X L V (L.val.restrictₛₗ f.op s) k
  | 0 => by
      change ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op)
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) =
        (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V))
      exact map_one _
  | k + 1 =>
      (PresheafOfModules.naturality_apply (tpowSuccIso X L k).hom.val f.op
          (tensorSection X (tpow X L k) L U (powerSection X L U s k) s)).symm.trans
        (congrArg ((tpowSuccIso X L k).hom.val.app (op V))
          ((tensorSection_restrict X (tpow X L k) L f (powerSection X L U s k) s).trans
            (congrArg (fun z => tensorSection X (tpow X L k) L V z
                (L.val.restrictₛₗ f.op s)) (powerSection_restrict L f s k))))


/-- The `k`-th tensor power of a local generator is a local generator. -/
noncomputable def generatorPowerSection
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (U : X.C)
    (s : GeneratorSections' X L U) :
    (k : ℕ) → GeneratorSections' X (tpow X L k) U
  | 0 => ⟨(1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)), by
      intro V f
      have h : (fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) =>
          r • (tpow X L 0).val.restrictₛₗ f.op
            (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U))) =
          fun r : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V) => r := by
        funext r
        change r • ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.map f.op)
          (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) = r
        rw [map_one]
        exact mul_one r
      rw [h]
      exact Function.bijective_id⟩
  | k + 1 => generatorSections_mapIso' X (tpowSuccIso X L k) U
      (tensorGeneratorSections' X (tpow X L k) L U (generatorPowerSection L U s k) s)

/-- The underlying section of the tensor power of a local generator is the tensor power of its
underlying section. -/
theorem generatorPowerSection_val
    (L : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L] (U : X.C)
    (s : GeneratorSections' X L U) :
    (k : ℕ) → (generatorPowerSection X L U s k).val = powerSection X L U s.val k
  | 0 => rfl
  | k + 1 => congrArg (fun z => (((tpowSuccIso X L k).hom.val.app (op U)).hom)
      (tensorSection X (tpow X L k) L U z s.val)) (generatorPowerSection_val L U s k)


/-- Naturality of the sheafification unit, read on a section. -/
theorem sheafifyMap_toSheafify_apply
    {P Q : PresheafOfModules.{w}
      (Stacks.SheafOfModules.TensorSheafification.structureSheaf X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2).obj}
    (phi : P ⟶ Q) (V : X.Cᵒᵖ) (x : P.obj V) :
    (((Stacks.SheafOfModules.TensorSheafification.sheafify X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2).map phi).val.app V).hom
        (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 P).app V).hom x) =
      (((Stacks.SheafOfModules.TensorSheafification.toSheafify X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 Q).app V).hom) ((phi.app V).hom x) :=
  congrArg (fun α => ((PresheafOfModules.Hom.app α V).hom) x)
    (Stacks.SheafOfModules.toSheafifyVal_naturality X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 phi)

/-- The tensor product of two isomorphisms carries the tensor product of two sections to the
tensor product of their images. -/
theorem tensorProductIso_tensorSection
    {L L' N N' : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (e : L ≅ L') (f : N ≅ N') (U : X.C) (s : L.val.obj (op U)) (t : N.val.obj (op U)) :
    ((tensorProductIso X.O.obj
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 e f).hom.val.app (op U)).hom
        (tensorSection X L N U s t) =
      tensorSection X L' N' U ((e.hom.val.app (op U)).hom s) ((f.hom.val.app (op U)).hom t) := by
  refine (sheafifyMap_toSheafify_apply X
    (P := PresheafOfModules.tensorObj L.val N.val) _
    (op U) (s ⊗ₜ[X.O.obj.obj (op U)] t)).trans ?_
  rfl


omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- The inverse of an isomorphism of sheaves of modules undoes it on sections. -/
theorem sheafIso_inv_app_hom_app
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (i : A ≅ B)
    (V : X.Cᵒᵖ) (x : A.val.obj V) :
    ((i.inv.val.app V).hom) (((i.hom.val.app V).hom) x) = x :=
  ((SheafOfModules.evaluation (Stacks.SheafOfModules.Tensor.ringSheaf X.O) V).mapIso
    i).hom_inv_id_apply x

/-- The `k`-th tensor power of an isomorphism of invertible modules. -/
noncomputable def powerMap {L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (e : L ≅ M) :
    (k : ℕ) → tpow X L k ≅ tpow X M k
  | 0 => Iso.refl _
  | k + 1 => ((tpowSuccIso X L k).symm ≪≫
      tensorProductIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (powerMap e k) e) ≪≫
      tpowSuccIso X M k

/-- The tensor power of an isomorphism at a successor exponent. -/
theorem powerMap_succ {L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (e : L ≅ M)
    (k : ℕ) :
    powerMap X e (k + 1) = ((tpowSuccIso X L k).symm ≪≫
      tensorProductIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 (powerMap X e k) e) ≪≫
      tpowSuccIso X M k := rfl

omit [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasWeakSheafify X.J AddCommGrpCat.{w}] in
/-- The value of a composite of morphisms of sheaves of modules on a section is the nested
application. -/
theorem comp_val_app_apply
    {A B D : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)} (g : A ⟶ B)
    (g' : B ⟶ D) (V : X.Cᵒᵖ) (x : A.val.obj V) :
    ((g'.val.app V).hom) (((g.val.app V).hom) x) = (((g ≫ g').val.app V).hom) x := rfl

/-- The `k`-th tensor power of an isomorphism carries the `k`-th tensor power of a section to
the `k`-th tensor power of its image. -/
theorem powerSection_map {L M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 L]
    [IsInvertible X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2 M] (e : L ≅ M)
    (U : X.C) (s : L.val.obj (op U)) :
    (k : ℕ) → ((powerMap X e k).hom.val.app (op U)).hom (powerSection X L U s k) =
        powerSection X M U ((e.hom.val.app (op U)).hom s) k
  | 0 => rfl
  | k + 1 => by
      have h0 : ((powerMap X e (k + 1)).hom.val.app (op U)).hom
            (powerSection X L U s (k + 1)) =
          ((tpowSuccIso X M k).hom.val.app (op U)).hom
            (((tensorProductIso X.O.obj (Stacks.SheafOfModules.Tensor.ringSheaf X.O).2
                (powerMap X e k) e).hom.val.app
                (op U)).hom
              (((tpowSuccIso X L k).inv.val.app (op U)).hom
                (powerSection X L U s (k + 1)))) := rfl
      rw [h0, powerSection_succ, sheafIso_inv_app_hom_app, tensorProductIso_tensorSection,
        powerSection_map e U s k, powerSection_succ]


end Stacks.Cohomology.Torsors.Generators

end
