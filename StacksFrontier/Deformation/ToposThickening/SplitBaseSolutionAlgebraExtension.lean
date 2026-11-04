module

public import StacksFrontier.Deformation.AlgebraExtension.Basic
public import StacksFrontier.Deformation.ToposThickening.ExtensionProblem

/-!
# Solutions over a split base thickening are extensions of algebras over the reduced base

Let `S` be a square-zero extension problem of ringed topoi (Stacks 08UF) over `f : X ⟶ B`, with
base thickening `𝒪_{B'} ⟶ 𝒪_B`, ideal `𝒥`, prescribed module `𝒢` and prescribed map
`c : f⁻¹𝒥 ⟶ 𝒢`. Suppose the base thickening is split by a ring map `s : 𝒪_B ⟶ 𝒪_{B'}`. This
is the situation of the trivial square-zero extensions `A ⟶ A[M]` of the tangent functor
(Stacks 07Y9), split by the constants. Then a solution `𝒪'` is the same as an extension
`0 → 𝒢 → 𝒪' → 𝒪_X → 0` of `f⁻¹𝒪_B`-algebras: restrict the `f⁻¹𝒪_{B'}`-algebra structure along
`f⁻¹s`, and conversely extend an `f⁻¹𝒪_B`-algebra structure to `f⁻¹𝒪_{B'} = f⁻¹s(f⁻¹𝒪_B) ⊕ f⁻¹𝒥`
by `c` on the ideal. This file proves that the two constructions identify the isomorphism classes.
Composed with Stacks 0GQ5 (`Deformation.AlgebraExtension.extClassEquiv`), it gives the class
in `Ext¹(NL_{X/B}, 𝒢)` of a deformation over the split thickening, which is the tangent class of
Remark 0D1P.

## Main definitions

* `...RingedToposExtensionProblem.toSplitAlgebraExtension`: a solution, as an extension of
  `f⁻¹𝒪_B`-algebras.
* `...RingedToposExtensionProblem.splitBaseMap`: the map `f⁻¹𝒪_{B'} ⟶ 𝒪'`,
  `b ↦ r(b) + c(b - f⁻¹s(r(b)))`, attached to an extension of `f⁻¹𝒪_B`-algebras.
* `...RingedToposExtensionProblem.ofSplitAlgebraExtension`: the solution it defines.
* `...RingedToposExtensionProblem.solutionClassesEquivSplitAlgebraExtensionClasses`: the
  bijection of isomorphism classes.

## Main results

* `...RingedToposExtensionProblem.baseMap_comp_eq_of_split`: the map from `f⁻¹𝒪_{B'}` of a
  solution is determined by its `f⁻¹𝒪_B`-algebra structure and its kernel.
* `...RingedToposExtensionProblem.isomorphic_iff_toSplitAlgebraExtension`.

## Implementation notes

The ideal part `b - f⁻¹s(r(b))` of a section of `f⁻¹𝒪_{B'}` is read as a section of `f⁻¹𝒥`
through the uniqueness clause `idealUniversal` of the problem
(`...RingedToposExtensionProblem.idealPart`). Its additivity, multiplicativity and naturality all
follow from that uniqueness. Multiplicativity uses that the ideal has square zero, which comes
from the linearity of its inclusion over `f⁻¹𝒪_{B'}`.

## References

* [Stacks Project, Tag 08UF](https://stacks.math.columbia.edu/tag/08UF)
* [Stacks Project, Tag 0GQ5](https://stacks.math.columbia.edu/tag/0GQ5)
* [Stacks Project, Remark 0D1P](https://stacks.math.columbia.edu/tag/0D1P)
-/

@[expose] public noncomputable section

open CategoryTheory
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (inverseImageCommRingFunctor)

universe v u w v' u'

namespace Deformation.ToposThickening.RingedToposExtensionProblem

variable {X : RingedTopos.{v, u, w}} {B : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [B.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [B.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  (S : RingedToposExtensionProblem X B)
  (s : B.O ⟶ S.baseExtension) (hs : s ≫ S.baseReduction = 𝟙 B.O)

include hs in
/-- The section of the base thickening, pulled back, splits the pulled-back reduction. -/
theorem inverseImage_section_reduction :
    (inverseImageCommRingFunctor S.f.toToposHom).map s ≫
      (inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction = 𝟙 _ := by
  rw [← Functor.map_comp, hs, CategoryTheory.Functor.map_id]

include hs in
/-- Sectionwise form of `inverseImage_section_reduction`: `r(f⁻¹s(a)) = a`. -/
theorem inverseImage_section_reduction_apply (U : X.Cᵒᵖ)
    (a : ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O).obj.obj U) :
    ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U
      (((inverseImageCommRingFunctor S.f.toToposHom).map s).hom.app U a) = a :=
  congrArg (fun k => k.hom.app U a) (inverseImage_section_reduction S s hs)

/-- **A solution over a split base thickening, as an extension of algebras over the reduced
base.** A section `s` of the base thickening `𝒪_{B'} ⟶ 𝒪_B` makes a solution `𝒪'` of the
problem an extension of `f⁻¹𝒪_B`-algebras of `𝒪_X` by `𝒢`, through `f⁻¹s` followed by the map
`f⁻¹𝒪_{B'} ⟶ 𝒪'`. -/
def toSplitAlgebraExtension (P : S.CompatibleFirstOrderThickening) :
    Deformation.AlgebraExtension (J := X.J) S.f.fSharpInverseImage S.G where
  extension := P.extension
  reduction := P.reduction
  locallySurjective := P.locallySurjective
  squareZero := P.squareZero
  algebraMap := (inverseImageCommRingFunctor S.f.toToposHom).map s ≫ P.baseMap
  algebraMap_reduction := by
    rw [Category.assoc, P.baseMap_reduction, ← Category.assoc,
      inverseImage_section_reduction S s hs, Category.id_comp]
  kernelInclusion := P.kernelInclusion
  kernelZero := P.kernelZero
  kernelUniversal := P.kernelUniversal

/-- An isomorphism of solutions is an isomorphism of the attached extensions of algebras. -/
def toSplitAlgebraExtensionHom {P Q : S.CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso P Q) :
    toSplitAlgebraExtension S s hs P ⟶ toSplitAlgebraExtension S s hs Q where
  hom := e.hom.hom
  reduction_comm := e.reduction_comm
  algebraMap_comm := by
    change ((inverseImageCommRingFunctor S.f.toToposHom).map s ≫ P.baseMap) ≫ e.hom.hom = _
    rw [Category.assoc, e.baseMap_comm]
    rfl
  kernel_comm := e.kernel_comm

/-- An isomorphism of solutions is an isomorphism of the attached extensions of algebras. -/
def toSplitAlgebraExtensionIso {P Q : S.CompatibleFirstOrderThickening}
    (e : CompatibleFirstOrderThickening.Iso P Q) :
    toSplitAlgebraExtension S s hs P ≅ toSplitAlgebraExtension S s hs Q where
  hom := toSplitAlgebraExtensionHom S s hs e
  inv := toSplitAlgebraExtensionHom S s hs e.symm
  hom_inv_id := Deformation.AlgebraExtension.MapAlong.ext e.hom.hom_inv_id
  inv_hom_id := Deformation.AlgebraExtension.MapAlong.ext e.hom.inv_hom_id

/-! ### The base map is determined by the splitting and the ideal -/

include hs in
/-- Every section of `f⁻¹𝒪_{B'}` is `f⁻¹s` of its reduction plus a section of the ideal. -/
theorem exists_eq_section_add_ideal (U : X.Cᵒᵖ)
    (b : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    ∃ x : S.I.val.obj U,
      b = ((inverseImageCommRingFunctor S.f.toToposHom).map s).hom.app U
          (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U b) +
        (show ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U from
          S.idealInclusion.val.app U x) := by
  set r := ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U
  set σ := ((inverseImageCommRingFunctor S.f.toToposHom).map s).hom.app U
  have hd : r (b - σ (r b)) = 0 := by
    rw [map_sub, inverseImage_section_reduction_apply S s hs, sub_self]
  obtain ⟨x, hx, -⟩ := S.idealUniversal U (b - σ (r b)) hd
  exact ⟨x, by rw [hx]; abel⟩

include hs in
/-- **A morphism of solutions is determined on the base by the splitting.** A homomorphism
between the thickened structure sheaves of two solutions that respects the `f⁻¹𝒪_B`-algebra
structures given by `s` and is the identity on the identified kernels commutes with the maps
from `f⁻¹𝒪_{B'}`. -/
theorem baseMap_comp_eq_of_split {P Q : S.CompatibleFirstOrderThickening}
    (g : P.extension ⟶ Q.extension)
    (hg : ((inverseImageCommRingFunctor S.f.toToposHom).map s ≫ P.baseMap) ≫ g =
      (inverseImageCommRingFunctor S.f.toToposHom).map s ≫ Q.baseMap)
    (hk : ∀ (U : X.Cᵒᵖ) (m : S.G.val.obj U),
      g.hom.app U (show P.extension.obj.obj U from P.kernelInclusion.val.app U m) =
        (show Q.extension.obj.obj U from Q.kernelInclusion.val.app U m)) :
    P.baseMap ≫ g = Q.baseMap := by
  apply Sheaf.hom_ext
  ext U b
  obtain ⟨x, hx⟩ := exists_eq_section_add_ideal S s hs U b
  set r := ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U
  set σ := ((inverseImageCommRingFunctor S.f.toToposHom).map s).hom.app U
  have hσ : g.hom.app U (P.baseMap.hom.app U (σ (r b))) = Q.baseMap.hom.app U (σ (r b)) :=
    congrArg (fun k => k.hom.app U (r b)) hg
  have hP := (congrArg (fun t => P.baseMap.hom.app U t) hx).trans (map_add _ _ _)
  have hQ := (congrArg (fun t => Q.baseMap.hom.app U t) hx).trans (map_add _ _ _)
  change g.hom.app U (P.baseMap.hom.app U b) = Q.baseMap.hom.app U b
  refine ((congrArg (fun t => g.hom.app U t) hP).trans (map_add _ _ _)).trans ?_
  refine Eq.trans ?_ hQ.symm
  refine congrArg₂ (· + ·) hσ ?_
  refine (congrArg (fun t => g.hom.app U t) (P.baseMap_ideal U x)).trans ?_
  exact (hk U _).trans (Q.baseMap_ideal U x).symm

/-- An isomorphism of the attached extensions of algebras is an isomorphism of solutions. -/
def isoOfSplitAlgebraExtensionIso {P Q : S.CompatibleFirstOrderThickening}
    (e : toSplitAlgebraExtension S s hs P ≅ toSplitAlgebraExtension S s hs Q) :
    CompatibleFirstOrderThickening.Iso P Q where
  hom :=
    { hom := e.hom.hom
      inv := e.inv.hom
      hom_inv_id := congrArg (fun φ => φ.hom) e.hom_inv_id
      inv_hom_id := congrArg (fun φ => φ.hom) e.inv_hom_id }
  reduction_comm := e.hom.reduction_comm
  baseMap_comm := baseMap_comp_eq_of_split S s hs e.hom.hom e.hom.algebraMap_comm
    (fun U m => e.hom.kernel_comm U m)
  kernel_comm := fun U m => e.hom.kernel_comm U m

/-- Two solutions are isomorphic exactly when the attached extensions of algebras are. -/
theorem isomorphic_iff_toSplitAlgebraExtension {P Q : S.CompatibleFirstOrderThickening} :
    (CompatibleFirstOrderThickening.isomorphicSetoid S).r P Q ↔
      Nonempty (toSplitAlgebraExtension S s hs P ≅ toSplitAlgebraExtension S s hs Q) :=
  ⟨fun ⟨e⟩ => ⟨toSplitAlgebraExtensionIso S s hs e⟩,
    fun ⟨e⟩ => ⟨isoOfSplitAlgebraExtensionIso S s hs e⟩⟩

/-! ### Every extension of algebras over the reduced base comes from a solution -/

/-- The reduction `f⁻¹𝒪_{B'} ⟶ f⁻¹𝒪_B` on sections. -/
abbrev baseRed (U : X.Cᵒᵖ) :=
  ((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.app U

/-- The section `f⁻¹𝒪_B ⟶ f⁻¹𝒪_{B'}` on sections. -/
abbrev baseSec (U : X.Cᵒᵖ) :=
  ((inverseImageCommRingFunctor S.f.toToposHom).map s).hom.app U

/-- The inclusion of the inverse-image base ideal into `f⁻¹𝒪_{B'}`, on sections. -/
def idealIncl (U : X.Cᵒᵖ) (x : S.I.val.obj U) :
    ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U :=
  S.idealInclusion.val.app U x

/-- A section of `f⁻¹𝒪_B`, read as a scalar of `f⁻¹𝒥`. -/
abbrev baseScalar {U : X.Cᵒᵖ}
    (t : ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O).obj.obj U) :
    ((sheafCompose X.J (forget₂ CommRingCat.{w} RingCat.{w})).obj
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O)).obj.obj U := t

/-- `idealIncl` is additive. -/
theorem idealIncl_add (U : X.Cᵒᵖ) (x y : S.I.val.obj U) :
    S.idealIncl U (x + y) = S.idealIncl U x + S.idealIncl U y :=
  map_add (S.idealInclusion.val.app U).hom x y

/-- `idealIncl` sends zero to zero. -/
theorem idealIncl_zero (U : X.Cᵒᵖ) : S.idealIncl U 0 = 0 :=
  map_zero (S.idealInclusion.val.app U).hom

/-- `idealIncl` is `f⁻¹𝒪_{B'}`-linear: a section of `f⁻¹𝒪_{B'}` acts on the ideal through its
reduction. -/
theorem mul_idealIncl (U : X.Cᵒᵖ)
    (t : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U)
    (x : S.I.val.obj U) :
    t * S.idealIncl U x = S.idealIncl U (S.baseScalar (S.baseRed U t) • x) :=
  ((S.idealInclusion.val.app U).hom.map_smul' t x).symm

/-- A section of the ideal reduces to zero in `f⁻¹𝒪_B`. -/
theorem baseRed_idealIncl (U : X.Cᵒᵖ) (x : S.I.val.obj U) :
    S.baseRed U (S.idealIncl U x) = 0 :=
  S.idealZero U x

include hs in
/-- The ideal part `b - f⁻¹s(r(b))` of a section `b` of `f⁻¹𝒪_{B'}` reduces to zero. -/
theorem baseRed_sub_baseSec (U : X.Cᵒᵖ)
    (b : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    S.baseRed U (b - S.baseSec s U (S.baseRed U b)) = 0 := by
  rw [map_sub, inverseImage_section_reduction_apply S s hs, sub_self]

/-- The ideal part `b - f⁻¹s(r(b))` of a section `b` of `f⁻¹𝒪_{B'}`, as a section of `f⁻¹𝒥`. -/
def idealPart (U : X.Cᵒᵖ)
    (b : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    S.I.val.obj U :=
  (S.idealUniversal U _ (baseRed_sub_baseSec S s hs U b)).choose

/-- The inclusion of the ideal part of `b` is `b - f⁻¹s(r(b))`. -/
theorem idealIncl_idealPart (U : X.Cᵒᵖ)
    (b : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    S.idealIncl U (S.idealPart s hs U b) = b - S.baseSec s U (S.baseRed U b) :=
  (S.idealUniversal U _ (baseRed_sub_baseSec S s hs U b)).choose_spec.1

/-- The ideal part of `b` is the unique section of the ideal whose inclusion is
`b - f⁻¹s(r(b))`. -/
theorem idealPart_eq_of_idealIncl (U : X.Cᵒᵖ)
    (b : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U)
    (x : S.I.val.obj U) (hx : S.idealIncl U x = b - S.baseSec s U (S.baseRed U b)) :
    S.idealPart s hs U b = x :=
  ((S.idealUniversal U _ (baseRed_sub_baseSec S s hs U b)).choose_spec.2 x hx).symm

/-- `idealPart` is additive. -/
theorem idealPart_add (U : X.Cᵒᵖ)
    (b b' : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    S.idealPart s hs U (b + b') = S.idealPart s hs U b + S.idealPart s hs U b' := by
  refine S.idealPart_eq_of_idealIncl s hs U _ _ ?_
  rw [S.idealIncl_add, S.idealIncl_idealPart, S.idealIncl_idealPart, map_add, map_add]
  abel

/-- The ideal part of a product: `(b b')ᵢ = r(b) • b'ᵢ + r(b') • bᵢ`, since the ideal has square
zero. -/
theorem idealPart_mul (U : X.Cᵒᵖ)
    (b b' : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    S.idealPart s hs U (b * b') =
      S.baseScalar (S.baseRed U b) • S.idealPart s hs U b' +
        S.baseScalar (S.baseRed U b') • S.idealPart s hs U b := by
  refine S.idealPart_eq_of_idealIncl s hs U _ _ ?_
  rw [S.idealIncl_add, ← S.mul_idealIncl, ← S.mul_idealIncl, S.idealIncl_idealPart,
    S.idealIncl_idealPart, map_mul, map_mul]
  have hsq : (b - S.baseSec s U (S.baseRed U b)) * (b' - S.baseSec s U (S.baseRed U b')) = 0 := by
    rw [← S.idealIncl_idealPart s hs U b', S.mul_idealIncl, baseRed_sub_baseSec S s hs U b]
    exact (congrArg (S.idealIncl U) (zero_smul _ _)).trans (S.idealIncl_zero U)
  linear_combination hsq

/-- The ideal part of a section of the ideal is itself. -/
theorem idealPart_idealIncl (U : X.Cᵒᵖ) (x : S.I.val.obj U) :
    S.idealPart s hs U (S.idealIncl U x) = x := by
  refine S.idealPart_eq_of_idealIncl s hs U _ _ ?_
  rw [S.baseRed_idealIncl, map_zero, sub_zero]

/-- The ideal part of `f⁻¹s(a)` is zero. -/
theorem idealPart_baseSec (U : X.Cᵒᵖ)
    (a : ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O).obj.obj U) :
    S.idealPart s hs U (S.baseSec s U a) = 0 := by
  refine S.idealPart_eq_of_idealIncl s hs U _ _ ?_
  rw [S.idealIncl_zero, inverseImage_section_reduction_apply S s hs, sub_self]

/-- The ideal part of zero is zero. -/
theorem idealPart_zero (U : X.Cᵒᵖ) : S.idealPart s hs U 0 = 0 := by
  simpa only [map_zero] using S.idealPart_baseSec s hs U 0

/-- The ideal part of one is zero. -/
theorem idealPart_one (U : X.Cᵒᵖ) : S.idealPart s hs U 1 = 0 := by
  simpa only [map_one] using S.idealPart_baseSec s hs U 1

/-- `idealIncl` commutes with restriction. -/
theorem idealIncl_naturality {U V : X.Cᵒᵖ} (h : U ⟶ V) (x : S.I.val.obj U) :
    S.idealIncl V (S.I.val.map h x) =
      ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.map h
        (S.idealIncl U x) :=
  PresheafOfModules.naturality_apply S.idealInclusion.val h x

/-- `baseRed` commutes with restriction. -/
theorem baseRed_naturality {U V : X.Cᵒᵖ} (h : U ⟶ V)
    (b : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    S.baseRed V (((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.map h b) =
      ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O).obj.map h (S.baseRed U b) :=
  ConcreteCategory.congr_hom
    (((inverseImageCommRingFunctor S.f.toToposHom).map S.baseReduction).hom.naturality h) b

/-- `baseSec` commutes with restriction. -/
theorem baseSec_naturality {U V : X.Cᵒᵖ} (h : U ⟶ V)
    (a : ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O).obj.obj U) :
    S.baseSec s V (((inverseImageCommRingFunctor S.f.toToposHom).obj B.O).obj.map h a) =
      ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.map h
        (S.baseSec s U a) :=
  ConcreteCategory.congr_hom
    (((inverseImageCommRingFunctor S.f.toToposHom).map s).hom.naturality h) a

/-- `idealPart` commutes with restriction. -/
theorem idealPart_naturality {U V : X.Cᵒᵖ} (h : U ⟶ V)
    (b : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    S.idealPart s hs V
        (((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.map h b) =
      S.I.val.map h (S.idealPart s hs U b) := by
  refine S.idealPart_eq_of_idealIncl s hs V _ _ ?_
  rw [S.idealIncl_naturality, S.idealIncl_idealPart, map_sub, S.baseRed_naturality,
    S.baseSec_naturality]

/-- The prescribed map `c : f⁻¹𝒥 ⟶ 𝒢`, on sections. -/
def cMap (U : X.Cᵒᵖ) (x : S.I.val.obj U) : S.G.val.obj U := S.c.val.app U x

/-- `cMap` is additive. -/
theorem cMap_add (U : X.Cᵒᵖ) (x y : S.I.val.obj U) :
    S.cMap U (x + y) = S.cMap U x + S.cMap U y :=
  map_add (S.c.val.app U).hom x y

/-- `cMap` sends zero to zero. -/
theorem cMap_zero (U : X.Cᵒᵖ) : S.cMap U 0 = 0 :=
  map_zero (S.c.val.app U).hom

/-- `cMap` is linear over `f⁻¹𝒪_B`, acting on `𝒢` through `f♯`. -/
theorem cMap_smul (U : X.Cᵒᵖ)
    (t : ((inverseImageCommRingFunctor S.f.toToposHom).obj B.O).obj.obj U) (x : S.I.val.obj U) :
    S.cMap U (S.baseScalar t • x) =
      Deformation.AlgebraExtension.scalar (S.f.fSharpInverseImage.hom.app U t) • S.cMap U x :=
  (S.c.val.app U).hom.map_smul' t x

/-- `cMap` commutes with restriction. -/
theorem cMap_naturality {U V : X.Cᵒᵖ} (h : U ⟶ V) (x : S.I.val.obj U) :
    S.cMap V (S.I.val.map h x) = S.G.val.map h (S.cMap U x) :=
  PresheafOfModules.naturality_apply S.c.val h x

variable (E : Deformation.AlgebraExtension (J := X.J) S.f.fSharpInverseImage S.G)

/-- The map `f⁻¹𝒪_{B'} ⟶ 𝒪'` of an extension of `f⁻¹𝒪_B`-algebras over the split base, on
sections: `b ↦ r(b) + c(b - f⁻¹s(r(b)))`. -/
def splitBaseMapApp (U : X.Cᵒᵖ) :
    ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U →+*
      E.extension.obj.obj U where
  toFun b := E.algebraMap.hom.app U (S.baseRed U b) + E.incl (S.cMap U (S.idealPart s hs U b))
  map_one' := by
    rw [map_one, map_one, S.idealPart_one, S.cMap_zero, E.incl_zero, add_zero]
  map_mul' b b' := by
    simp only
    rw [map_mul, map_mul, S.idealPart_mul, S.cMap_add, S.cMap_smul, S.cMap_smul, E.incl_add,
      add_mul, mul_add, mul_add, E.incl_mul_incl, E.mul_incl, mul_comm (E.incl _), E.mul_incl,
      E.reduction_algebraMap, E.reduction_algebraMap]
    abel
  map_zero' := by
    rw [map_zero, map_zero, S.idealPart_zero, S.cMap_zero, E.incl_zero, add_zero]
  map_add' b b' := by
    simp only
    rw [map_add, map_add, S.idealPart_add, S.cMap_add, E.incl_add]
    abel

/-- **The map `f⁻¹𝒪_{B'} ⟶ 𝒪'` of an extension of algebras over the split base.** -/
def splitBaseMap :
    (inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension ⟶ E.extension where
  hom :=
    { app U := CommRingCat.ofHom
        (R := ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U)
        (S := E.extension.obj.obj U) (S.splitBaseMapApp s hs E U)
      naturality U V h := by
        ext b
        change S.splitBaseMapApp s hs E V
            (((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.map h b) =
          E.extension.obj.map h (S.splitBaseMapApp s hs E U b)
        simp only [splitBaseMapApp, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk]
        rw [map_add, S.baseRed_naturality, S.idealPart_naturality, S.cMap_naturality,
          E.incl_naturality]
        congr 1
        exact ConcreteCategory.congr_hom (E.algebraMap.hom.naturality h) _ }

/-- `splitBaseMap` on sections is `b ↦ r(b) + c(b - f⁻¹s(r(b)))`. -/
theorem splitBaseMap_app (U : X.Cᵒᵖ)
    (b : ((inverseImageCommRingFunctor S.f.toToposHom).obj S.baseExtension).obj.obj U) :
    (S.splitBaseMap s hs E).hom.app U b =
      E.algebraMap.hom.app U (S.baseRed U b) + E.incl (S.cMap U (S.idealPart s hs U b)) :=
  rfl

/-- **The solution attached to an extension of algebras over the split base.** An extension
`0 → 𝒢 → 𝒪' → 𝒪_X → 0` of `f⁻¹𝒪_B`-algebras becomes a solution of the problem through the map
`f⁻¹𝒪_{B'} ⟶ 𝒪'`, `b ↦ r(b) + c(b - f⁻¹s(r(b)))`. -/
def ofSplitAlgebraExtension : S.CompatibleFirstOrderThickening where
  extension := E.extension
  reduction := E.reduction
  locallySurjective := E.locallySurjective
  squareZero := E.squareZero
  baseMap := S.splitBaseMap s hs E
  baseMap_reduction := by
    apply Sheaf.hom_ext
    ext U b
    change E.reduction.hom.app U ((S.splitBaseMap s hs E).hom.app U b) =
      S.f.fSharpInverseImage.hom.app U (S.baseRed U b)
    rw [S.splitBaseMap_app, map_add, E.reduction_algebraMap, E.reduction_incl, add_zero]
  kernelInclusion := E.kernelInclusion
  kernelZero := E.kernelZero
  kernelUniversal := E.kernelUniversal
  baseMap_ideal U a := by
    change (S.splitBaseMap s hs E).hom.app U (S.idealIncl U a) = E.incl (S.cMap U a)
    rw [S.splitBaseMap_app, S.baseRed_idealIncl, map_zero, zero_add, S.idealPart_idealIncl]

/-- The `f⁻¹𝒪_B`-algebra structure of the solution attached to `E` is that of `E`. -/
theorem toSplitAlgebraExtension_ofSplitAlgebraExtension_algebraMap :
    (toSplitAlgebraExtension S s hs (S.ofSplitAlgebraExtension s hs E)).algebraMap =
      E.algebraMap := by
  apply Sheaf.hom_ext
  ext U a
  change (S.splitBaseMap s hs E).hom.app U (S.baseSec s U a) = E.algebraMap.hom.app U a
  rw [S.splitBaseMap_app, inverseImage_section_reduction_apply S s hs, S.idealPart_baseSec,
    S.cMap_zero, E.incl_zero, add_zero]

/-- The extension of algebras of the solution attached to `E` is `E`. -/
def toSplitAlgebraExtensionOfSplitAlgebraExtensionHom :
    toSplitAlgebraExtension S s hs (S.ofSplitAlgebraExtension s hs E) ⟶ E where
  hom := 𝟙 _
  reduction_comm := Category.id_comp _
  algebraMap_comm := (Category.comp_id _).trans
    (S.toSplitAlgebraExtension_ofSplitAlgebraExtension_algebraMap s hs E)
  kernel_comm _ _ := rfl

/-- The extension of algebras of the solution attached to `E` is `E`. -/
def toSplitAlgebraExtensionOfSplitAlgebraExtensionIso :
    toSplitAlgebraExtension S s hs (S.ofSplitAlgebraExtension s hs E) ≅ E where
  hom := S.toSplitAlgebraExtensionOfSplitAlgebraExtensionHom s hs E
  inv :=
    { hom := 𝟙 _
      reduction_comm := Category.id_comp _
      algebraMap_comm := (Category.comp_id _).trans
        (S.toSplitAlgebraExtension_ofSplitAlgebraExtension_algebraMap s hs E).symm
      kernel_comm _ _ := rfl }
  hom_inv_id := Deformation.AlgebraExtension.MapAlong.ext (Category.id_comp _)
  inv_hom_id := Deformation.AlgebraExtension.MapAlong.ext (Category.id_comp _)

/-- **Solutions over a split base thickening are extensions of algebras over the reduced
base.** A section `s` of the base thickening `𝒪_{B'} ⟶ 𝒪_B` identifies the isomorphism classes
of solutions of the problem with the isomorphism classes of extensions
`0 → 𝒢 → 𝒪' → 𝒪_X → 0` of `f⁻¹𝒪_B`-algebras. -/
def solutionClassesEquivSplitAlgebraExtensionClasses :
    CompatibleFirstOrderThickening.IsomorphismClasses S ≃
      Quotient (isIsomorphicSetoid
        (Deformation.AlgebraExtension (J := X.J) S.f.fSharpInverseImage S.G)) :=
  Equiv.ofBijective
    (Quotient.map (toSplitAlgebraExtension S s hs)
      (fun _ _ h => (isomorphic_iff_toSplitAlgebraExtension S s hs).1 h))
    ⟨fun a b h => by
      induction a using Quotient.inductionOn
      induction b using Quotient.inductionOn
      exact Quotient.sound ((isomorphic_iff_toSplitAlgebraExtension S s hs).2 (Quotient.exact h)),
    fun e => by
      induction e using Quotient.inductionOn with
      | _ E => exact ⟨Quotient.mk _ (S.ofSplitAlgebraExtension s hs E),
        Quotient.sound ⟨S.toSplitAlgebraExtensionOfSplitAlgebraExtensionIso s hs E⟩⟩⟩

/-- The bijection `solutionClassesEquivSplitAlgebraExtensionClasses` on the class of a solution. -/
@[simp]
theorem solutionClassesEquivSplitAlgebraExtensionClasses_mk (P : S.CompatibleFirstOrderThickening) :
    solutionClassesEquivSplitAlgebraExtensionClasses S s hs (Quotient.mk _ P) =
      Quotient.mk _ (toSplitAlgebraExtension S s hs P) :=
  rfl

end Deformation.ToposThickening.RingedToposExtensionProblem

end
