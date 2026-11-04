module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatResolution.ComplexLifting
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor
public import StacksCore.Tactic.StacksAttribute

/-!
# The curvature class of a square-zero extension of sheaves of rings

Let `f : O ⟶ O₀` be a surjection of sheaves of commutative rings on a site whose kernel is an
ideal sheaf `I` of square zero, and let `K₀` be a bounded above complex of `O₀`-modules. Tag
0DIT lifts `K₀` to a bounded above graded family `F` of flat `O`-modules carrying maps `d` in
consecutive degrees whose extension of scalars is a complex `F₀` quasi-isomorphic to `K₀`. The
composite `d ∘ d` vanishes after reduction, so it lands in the kernel of the reduction, which
for a flat term is `F₀ ⊗_{O₀} I`; the universal property of extension of scalars then descends
it to a map `F₀ ⟶ (F₀ ⊗_{O₀} I)[2]` of complexes, the *curvature* of the lifted differential.
Passing to the derived category gives the canonical map

`ω(K₀) : K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]`

of Tag 0DIU, natural in `K₀`.

## Main definitions

* `Deformation.ComplexLift.SquareZeroIdeal`: a square-zero ideal sheaf presenting `f`.
* `Deformation.ComplexLift.FlatLift`: a bounded above flat lift of a complex, as produced by
  Tag 0DIT.
* `Deformation.ComplexLift.IdealKernel`: the identification of the kernel of the reduction with
  `F₀ ⊗_{O₀} I`, normalized on local pure tensors by multiplication.
* `Deformation.ComplexLift.curvature`: the square of the lifted differential, read in
  `F₀ ⊗_{O₀} I`.
* `Deformation.ComplexLift.curvatureMap`: the curvature as a map of complexes
  `F₀ ⟶ (F₀ ⊗_{O₀} I)[2]`.
* `Deformation.ComplexLift.FlatLiftHom`: a morphism of flat lifts over a map of the lifted
  complexes.
* `Deformation.ComplexLift.DerivedIdealTensor`: the derived tensor product with `I`, recorded
  by its comparison with the ordinary tensor product.
* `Deformation.ComplexLift.obstructionMap`: **Tag 0DIU**, the map `ω(K₀)`.

## Main results

* `Deformation.ComplexLift.unit_comp_curvature`: **Tag 0DIU**, the map is the curvature
  `d ∘ d` of the lifted differential; `Deformation.ComplexLift.eq_curvature_of_unit_comp`: it
  is the unique such map.
* `Deformation.ComplexLift.FlatLift.ofLiftedComplex`: the output of Tag 0DIT
  (`Stacks.SheafOfModules.ComplexLifting.exists_liftedComplex`) is a flat lift.
* `Deformation.ComplexLift.curvature_natural`, `.curvatureMap_natural`,
  `.derivedCurvature_natural`: a morphism of flat lifts carries curvature to curvature.
* `Deformation.ComplexLift.obstructionMap_natural`: **Tag 0DIU**, naturality of `ω`.
* `Deformation.ComplexLift.obstructionMap_eq_of_hom`: **Tag 0DIU**, `ω(K₀)` does not depend on
  the lift: two lifts joined by a morphism over the identity give the same map.

## Implementation notes

The curvature is *constructed*, not chosen: `ddLift` is the factorization of `d ∘ d` through the
kernel of the reduction, which exists because the reduction is a complex, and `curvature` is its
descent along the universal morphism `F ⟶ F₀|_O`. Both steps are universal properties, so
`eq_curvature_of_unit_comp` characterizes the result, and the naturality statements are theorems
about that construction.

What is taken as data is the ambient geometry, in the style of Tags 0DIX, 0DIY and 0DIZ: the
ideal sheaf with its inclusion into the structure sheaf, the flat lift, the identification of
the kernel of the reduction with `F₀ ⊗_{O₀} I`, and the derived tensor product with `I` together
with its comparison with the ordinary tensor product. The kernel identification is normalized by
the pure-tensor formula `x̄ ⊗ a ↦ a · x`, which is what makes `ω` canonical rather than one of
its multiples; its compatibility with a morphism of lifts is the hypothesis `hemb` of the
naturality results, and is the same formula read on both inclusions.

The ordinary tensor product with `I` is the flipped tensor bifunctor
`Stacks.SheafOfModules.Tensor.sheafTensor`, the functor whose exactness defines flatness in
`AlgebraicGeometry.SheafOfModules.IsFlat`, so the flatness hypothesis of a lift is literally
about the functor appearing in the target of `ω`. Its additivity, which forms the complex
`F₀ ⊗_{O₀} I`, is an instance hypothesis, as in the derived tensor product interface. The
module and ring universes agree, which is where the tensor product of sheaves of modules is
available; the site universes and the universe of the derived category are independent.

## References

* [Stacks Project, Tag 0DIU](https://stacks.math.columbia.edu/tag/0DIU)
* [Stacks Project, Tag 0DIT](https://stacks.math.columbia.edu/tag/0DIT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open Stacks.Sheaves.ChangeOfRings (ringSheafMap)
open Stacks.SheafOfModules.ComplexLifting (GradedDifferential BaseChangeTo
  IsExtensionOfScalars)

universe v u w d

namespace Deformation.ComplexLift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify J AddCommGrpCat.{w}]

/-- Sheaves of modules over a sheaf of commutative rings on a site. -/
abbrev SheafMod (O : Sheaf J CommRingCat.{w}) :=
  SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O)

/-- Restriction of scalars along a morphism of sheaves of commutative rings. -/
abbrev restrict {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀) :
    SheafMod O₀ ⥤ SheafMod O :=
  SheafOfModules.restrictScalars (ringSheafMap f)

/-- Tensoring a complex of `O₀`-modules degreewise with a fixed sheaf of modules. -/
abbrev idealTensorFunctor (O₀ : Sheaf J CommRingCat.{w}) (I : SheafMod O₀)
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₀).flip.obj I).Additive] :
    CochainComplex (SheafMod O₀) ℤ ⥤ CochainComplex (SheafMod O₀) ℤ :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₀).flip.obj I).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- A square-zero ideal sheaf presenting a surjection `f : O ⟶ O₀` of sheaves of commutative
rings: the sections of `I` include into those of `O` as exactly the kernel of `f`, compatibly
with the module structure, and all their products vanish. -/
structure SquareZeroIdeal {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀) (I : SheafMod O₀) where
  /-- The inclusion of the ideal into the structure sheaf, on local sections. -/
  incl (U : Cᵒᵖ) : I.val.obj U →+ O.obj.obj U
  /-- The inclusion is compatible with restriction of sections. -/
  incl_map {U V : Cᵒᵖ} (g : U ⟶ V) (a : I.val.obj U) :
    incl V (I.val.map g a) = O.obj.map g (incl U a)
  /-- The ideal is killed by the surjection. -/
  f_incl (U : Cᵒᵖ) (a : I.val.obj U) : f.hom.app U (incl U a) = 0
  /-- Every local section killed by the surjection comes from a unique section of the ideal. -/
  existsUnique_incl (U : Cᵒᵖ) (b : O.obj.obj U) (hb : f.hom.app U b = 0) :
    ∃! a : I.val.obj U, incl U a = b
  /-- The module structure on the ideal is multiplication by any lift of the scalar. -/
  incl_smul (U : Cᵒᵖ) (b : O.obj.obj U) (a : I.val.obj U) :
    incl U ((show (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj.obj U from f.hom.app U b) • a) =
      b * incl U a
  /-- The ideal has square zero. -/
  incl_mul_incl (U : Cᵒᵖ) (a b : I.val.obj U) : incl U a * incl U b = 0

/-- A bounded above flat lift of a complex of `O₀`-modules across `f : O ⟶ O₀`, as produced by
Stacks 0DIT: a graded family of flat `O`-modules with maps in consecutive degrees whose
extension of scalars is a complex quasi-isomorphic to the given one. -/
structure FlatLift {O O₀ : Sheaf J CommRingCat.{w}} (f : O ⟶ O₀)
    (K₀ : CochainComplex (SheafMod O₀) ℤ) where
  /-- The graded family of flat `O`-modules with its maps in consecutive degrees. -/
  F : GradedDifferential (SheafMod O)
  /-- Every term is flat. -/
  flat (n : ℤ) : AlgebraicGeometry.SheafOfModules.IsFlat (F.X n)
  /-- The family vanishes in sufficiently high degrees. -/
  boundedAbove : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (F.X n)
  /-- The maps to the target in every degree. -/
  toTarget (n : ℤ) : F.X n ⟶ (restrict f).obj (K₀.X n)
  /-- After extension of scalars the family is a complex mapping to the target. -/
  baseChange : BaseChangeTo f F K₀ toTarget
  /-- The induced map of complexes is a quasi-isomorphism. -/
  quasiIso : QuasiIso baseChange.map

/-- A solution to the lifting problem of Stacks 0DIT, for whatever family was prescribed, is a
flat lift of the target complex. -/
def FlatLift.ofLiftedComplex [HasSheafify J AddCommGrpCat.{w}]
    {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀}
    {G : GradedDifferential (SheafMod O)} {K₀ : CochainComplex (SheafMod O₀) ℤ}
    {g : ∀ n, G.X n ⟶ (restrict f).obj (K₀.X n)}
    (T : Stacks.SheafOfModules.ComplexLifting.LiftedComplex f G K₀ g) : FlatLift f K₀ where
  F := T.F
  flat := T.flat
  boundedAbove := T.boundedAbove
  toTarget := T.toTarget
  baseChange := T.baseChange
  quasiIso := T.quasiIso

/-- The complex `F₀ ⊗_{O₀} I` attached to a flat lift. -/
abbrev FlatLift.idealTensor {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} {I : SheafMod O₀}
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₀).flip.obj I).Additive]
    {K₀ : CochainComplex (SheafMod O₀) ℤ}
    (L : FlatLift f K₀) : CochainComplex (SheafMod O₀) ℤ :=
  (idealTensorFunctor O₀ I).obj L.baseChange.complex

/-- The identification of the kernel of the reduction of a flat lift with the tensor product of
the reduction with the ideal sheaf. On local sections it sends `x̄ ⊗ a` to `a · x`, which
determines it. -/
structure IdealKernel {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} {I : SheafMod O₀}
    [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₀).flip.obj I).Additive]
    (S : SquareZeroIdeal f I)
    {K₀ : CochainComplex (SheafMod O₀) ℤ} (L : FlatLift f K₀) where
  /-- The inclusion of the ideal part of a lifted term. -/
  emb (n : ℤ) : (restrict f).obj ((L.idealTensor (I := I)).X n) ⟶ L.F.X n
  /-- The ideal part is killed by the reduction. -/
  emb_comp_unit (n : ℤ) : emb n ≫ L.baseChange.unit n = 0
  /-- The ideal part is exactly the kernel of the reduction. -/
  isKernel (n : ℤ) : IsLimit (KernelFork.ofι (emb n) (emb_comp_unit n))
  /-- The inclusion is compatible with the two differentials. -/
  emb_d (n : ℤ) :
    emb n ≫ L.F.d n =
      (restrict f).map ((L.idealTensor (I := I)).d n (n + 1)) ≫ emb (n + 1)
  /-- The inclusion sends a local pure tensor `x̄ ⊗ a` to `a · x`. This normalization is what
  makes the identification canonical rather than one of its multiples. -/
  emb_tmul (n : ℤ) (U : Cᵒᵖ) (x : (L.F.X n).val.obj U) (a : I.val.obj U) :
    (emb n).val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf O₀)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O₀).obj)).unit.app
          (PresheafOfModules.tensorObj ((L.baseChange.complex.X n)).val I.val)).app U
          ((L.baseChange.unit n).val.app U x ⊗ₜ[O₀.obj.obj U] a)) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U from S.incl U a) • x

section Curvature

variable {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} {I : SheafMod O₀}
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₀).flip.obj I).Additive]
  {S : SquareZeroIdeal f I}
  {K₀ : CochainComplex (SheafMod O₀) ℤ} {L : FlatLift f K₀}

/-- The square of the lifted differential vanishes after reduction: the reduction is a
complex. -/
lemma dd_comp_unit (n : ℤ) :
    (L.F.d n ≫ L.F.d (n + 1)) ≫ L.baseChange.unit (n + 1 + 1) = 0 :=
  calc (L.F.d n ≫ L.F.d (n + 1)) ≫ L.baseChange.unit (n + 1 + 1)
      = (L.F.d n ≫ L.baseChange.unit (n + 1)) ≫
          (restrict f).map (L.baseChange.complex.d (n + 1) (n + 1 + 1)) := by
        rw [Category.assoc, L.baseChange.differential (n + 1), Category.assoc]
    _ = L.baseChange.unit n ≫ (restrict f).map (L.baseChange.complex.d n (n + 1) ≫
          L.baseChange.complex.d (n + 1) (n + 1 + 1)) := by
        rw [L.baseChange.differential n, Functor.map_comp, Category.assoc]
    _ = 0 := by rw [HomologicalComplex.d_comp_d, Functor.map_zero, comp_zero]

/-- The reduction of a lifted term is an extension of scalars: two maps out of it that agree
after the reduction agree. -/
lemma unit_hom_ext (n : ℤ) {N : SheafMod O₀}
    {α β : L.baseChange.complex.X n ⟶ N}
    (h : L.baseChange.unit n ≫ (restrict f).map α =
      L.baseChange.unit n ≫ (restrict f).map β) : α = β :=
  (L.baseChange.isExtension n N).injective h

/-- Reassociated form of the compatibility of the reduction with the differentials. -/
lemma unit_comp_map_d (n : ℤ) {Z : SheafMod O}
    (h : (restrict f).obj (L.baseChange.complex.X (n + 1)) ⟶ Z) :
    L.baseChange.unit n ≫ (restrict f).map (L.baseChange.complex.d n (n + 1)) ≫ h =
      L.F.d n ≫ L.baseChange.unit (n + 1) ≫ h := by
  rw [← Category.assoc, ← L.baseChange.differential n, Category.assoc]

variable (T : IdealKernel S L)

/-- The ideal part of a lifted term is a subobject. -/
lemma mono_emb (n : ℤ) : Mono (T.emb n) := mono_of_isLimit_fork (T.isKernel n)

/-- Two maps from the reduction of a lifted term to the ideal part of a lift agree if they agree
after the reduction map and the ideal inclusion. -/
private theorem hom_ext_of_unit_comp_emb {K₁ : CochainComplex (SheafMod O₀) ℤ}
    {L₁ : FlatLift f K₁} (T₁ : IdealKernel S L₁) (n m : ℤ)
    {α β : L.baseChange.complex.X n ⟶ (L₁.idealTensor (I := I)).X m}
    (h : L.baseChange.unit n ≫ (restrict f).map α ≫ T₁.emb m =
      L.baseChange.unit n ≫ (restrict f).map β ≫ T₁.emb m) : α = β := by
  have := mono_emb T₁ m
  refine unit_hom_ext n ?_
  rwa [← cancel_mono (T₁.emb m), Category.assoc, Category.assoc]

/-- The square of the lifted differential, factored through the ideal part of its target
term. -/
def ddLift (n : ℤ) :
    L.F.X n ⟶ (restrict f).obj ((L.idealTensor (I := I)).X (n + 1 + 1)) :=
  (T.isKernel (n + 1 + 1)).lift
    (KernelFork.ofι (L.F.d n ≫ L.F.d (n + 1)) (dd_comp_unit n))

/-- Followed by the ideal inclusion, `ddLift T n` is the square of the lifted differential. -/
@[simp]
lemma ddLift_comp_emb (n : ℤ) :
    ddLift T n ≫ T.emb (n + 1 + 1) = L.F.d n ≫ L.F.d (n + 1) :=
  Fork.IsLimit.lift_ι (T.isKernel (n + 1 + 1))

/-- **The curvature of a lifted differential.** The square of the lifted differential vanishes
after reduction, hence lands in the ideal part `F₀ ⊗_{O₀} I` of the target term; the universal
property of extension of scalars then descends it to a map out of the reduction. -/
def curvature (n : ℤ) :
    L.baseChange.complex.X n ⟶ (L.idealTensor (I := I)).X (n + 1 + 1) :=
  IsExtensionOfScalars.desc f (L.baseChange.isExtension n) (ddLift T n)

/-- The curvature is the descent of `ddLift T n` along the extension of scalars. -/
lemma curvature_eq (n : ℤ) :
    curvature T n = IsExtensionOfScalars.desc f (L.baseChange.isExtension n) (ddLift T n) :=
  rfl

/-- The curvature computes the square of the lifted differential: pulled back to the lift and
followed by the ideal inclusion it is `d ∘ d`. This is the identification of `ω` with the
curvature class, read on the complex representing it. -/
@[reassoc, stacks 0DIU "variant: the curvature d ∘ d of the lifted differential, the complex-level
map; the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem unit_comp_curvature (n : ℤ) :
    L.baseChange.unit n ≫ (restrict f).map (curvature T n) ≫ T.emb (n + 1 + 1) =
      L.F.d n ≫ L.F.d (n + 1) := by
  rw [curvature_eq, ← Category.assoc, IsExtensionOfScalars.desc_spec, ddLift_comp_emb]

/-- The curvature is the unique map satisfying `unit_comp_curvature`. -/
theorem eq_curvature_of_unit_comp (n : ℤ)
    (c : L.baseChange.complex.X n ⟶ (L.idealTensor (I := I)).X (n + 1 + 1))
    (hc : L.baseChange.unit n ≫ (restrict f).map c ≫ T.emb (n + 1 + 1) =
      L.F.d n ≫ L.F.d (n + 1)) : c = curvature T n := by
  refine hom_ext_of_unit_comp_emb T n _ ?_
  rw [hc, unit_comp_curvature]

/-- The curvature commutes with the differentials: both sides of the square compose with the
ideal inclusion to `d ∘ d ∘ d`. -/
theorem curvature_comm (n : ℤ) :
    curvature T n ≫ (L.idealTensor (I := I)).d (n + 1 + 1) (n + 1 + 1 + 1) =
      L.baseChange.complex.d n (n + 1) ≫ curvature T (n + 1) := by
  refine hom_ext_of_unit_comp_emb T n _ ?_
  simp only [Functor.map_comp, Category.assoc]
  rw [← T.emb_d (n + 1 + 1), unit_comp_curvature_assoc, unit_comp_map_d,
    unit_comp_curvature T (n + 1)]

/-- **The curvature class of a flat lift**, as a map of complexes `F₀ ⟶ (F₀ ⊗_{O₀} I)[2]`. In
degree `n` it is the curvature of the lifted differential, that is the square of that
differential read in the ideal part. -/
def curvatureMap :
    L.baseChange.complex ⟶
      (CategoryTheory.shiftFunctor (CochainComplex (SheafMod O₀) ℤ) (2 : ℤ)).obj
        (L.idealTensor (I := I)) where
  f n := curvature T n ≫
    ((L.idealTensor (I := I)).XIsoOfEq (show n + 1 + 1 = n + 2 by omega)).hom
  comm' i j hij := by
    obtain rfl : j = i + 1 := by simpa using hij.symm
    have h2 : ((2 : ℤ)).negOnePow = 1 := by decide
    simp only [CochainComplex.shiftFunctor_obj_d', h2, one_smul]
    rw [Category.assoc, HomologicalComplex.XIsoOfEq_hom_comp_d, ← Category.assoc,
      ← curvature_comm, Category.assoc, HomologicalComplex.d_comp_XIsoOfEq_hom]

/-- In degree `n`, the curvature class is the curvature followed by the identification of
the degree `n + 1 + 1` term with the degree `n + 2` term. -/
@[simp]
lemma curvatureMap_f (n : ℤ) :
    (curvatureMap T).f n =
      curvature T n ≫
        ((L.idealTensor (I := I)).XIsoOfEq (show n + 1 + 1 = n + 2 by omega)).hom := rfl

end Curvature

section Naturality

variable {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} {I : SheafMod O₀}
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₀).flip.obj I).Additive]
  {S : SquareZeroIdeal f I}
  {K₀ L₀ : CochainComplex (SheafMod O₀) ℤ}

/-- A morphism of flat lifts over a map `φ : K₀ ⟶ L₀` of the lifted complexes: a map of the
graded families compatible with the maps in consecutive degrees, together with the induced map
of reductions. -/
structure FlatLiftHom (L : FlatLift f K₀) (M : FlatLift f L₀) (φ : K₀ ⟶ L₀) where
  /-- The map of graded families. -/
  hom (n : ℤ) : L.F.X n ⟶ M.F.X n
  /-- It commutes with the maps in consecutive degrees. -/
  hom_d (n : ℤ) : L.F.d n ≫ hom (n + 1) = hom n ≫ M.F.d n
  /-- The induced map of reductions. -/
  red : L.baseChange.complex ⟶ M.baseChange.complex
  /-- The two maps correspond under the universal morphisms. -/
  unit_red (n : ℤ) :
    hom n ≫ M.baseChange.unit n = L.baseChange.unit n ≫ (restrict f).map (red.f n)
  /-- The map of reductions lies over `φ`. -/
  red_map : red ≫ M.baseChange.map = L.baseChange.map ≫ φ

variable {L : FlatLift f K₀} {M : FlatLift f L₀} {φ : K₀ ⟶ L₀} (h : FlatLiftHom L M φ)

/-- Reassociated form of the compatibility of a morphism of lifts with the reductions. -/
lemma unit_red_assoc (n : ℤ) {Z : SheafMod O}
    (k : (restrict f).obj (M.baseChange.complex.X n) ⟶ Z) :
    L.baseChange.unit n ≫ (restrict f).map (h.red.f n) ≫ k =
      h.hom n ≫ M.baseChange.unit n ≫ k := by
  rw [← Category.assoc, ← h.unit_red n, Category.assoc]

variable (TL : IdealKernel S L) (TM : IdealKernel S M)
  (hemb : ∀ n : ℤ, (restrict f).map (((idealTensorFunctor O₀ I).map h.red).f n) ≫ TM.emb n =
    TL.emb n ≫ h.hom n)

include h hemb

/-- **Naturality of the curvature.** A morphism of flat lifts carries the curvature of the
source to the curvature of the target, degreewise. -/
theorem curvature_natural (n : ℤ) :
    curvature TL n ≫ ((idealTensorFunctor O₀ I).map h.red).f (n + 1 + 1) =
      h.red.f n ≫ curvature TM n := by
  refine hom_ext_of_unit_comp_emb TM n _ ?_
  simp only [Functor.map_comp, Category.assoc]
  rw [hemb (n + 1 + 1), unit_comp_curvature_assoc, unit_red_assoc,
    unit_comp_curvature TM n, h.hom_d (n + 1), ← Category.assoc, h.hom_d n, Category.assoc]

/-- **Naturality of the curvature class.** -/
theorem curvatureMap_natural :
    curvatureMap TL ≫ (CategoryTheory.shiftFunctor (CochainComplex (SheafMod O₀) ℤ)
        (2 : ℤ)).map ((idealTensorFunctor O₀ I).map h.red) =
      h.red ≫ curvatureMap TM := by
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  simp only [HomologicalComplex.comp_f, curvatureMap_f, CochainComplex.shiftFunctor_map_f',
    Category.assoc]
  rw [← HomologicalComplex.XIsoOfEq_hom_naturality, ← Category.assoc,
    curvature_natural h TL TM hemb n, Category.assoc]

end Naturality

section Derived

variable {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} (I : SheafMod O₀)
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₀).flip.obj I).Additive]
  [HasDerivedCategory.{d} (SheafMod O₀)]

/-- The derived tensor product with the ideal sheaf, recorded by its canonical comparison with
the ordinary tensor product. The comparison is required to be invertible on the bounded above
complexes with flat terms, which are the ones computing the derived tensor product; that is
what identifies the functor as `- ⊗^L_{O₀} I`. -/
structure DerivedIdealTensor where
  /-- The derived tensor product with the ideal. -/
  functor : DerivedCategory (SheafMod O₀) ⥤ DerivedCategory (SheafMod O₀)
  /-- The comparison with the ordinary tensor product. -/
  comparison : idealTensorFunctor O₀ I ⋙ DerivedCategory.Q ⟶ DerivedCategory.Q ⋙ functor
  /-- The comparison is invertible on bounded above complexes with flat terms. -/
  isIso_comparison (P : CochainComplex (SheafMod O₀) ℤ)
    (hflat : ∀ n, AlgebraicGeometry.SheafOfModules.IsFlat (P.X n))
    (hbdd : ∃ N : ℤ, ∀ n : ℤ, N ≤ n → IsZero (P.X n)) : IsIso (comparison.app P)

variable {I} {S : SquareZeroIdeal f I} (D : DerivedIdealTensor I)
  {K₀ L₀ : CochainComplex (SheafMod O₀) ℤ}

/-- The curvature class of a flat lift, read in the derived category of the reduction. -/
def derivedCurvature {L : FlatLift f K₀} (T : IdealKernel S L) :
    DerivedCategory.Q.obj L.baseChange.complex ⟶
      (D.functor.obj (DerivedCategory.Q.obj L.baseChange.complex))⟦(2 : ℤ)⟧ :=
  DerivedCategory.Q.map (curvatureMap T) ≫
    (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.app (L.idealTensor (I := I)) ≫
    (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
      (D.comparison.app L.baseChange.complex)

/-- The reduction of a flat lift is a quasi-isomorphism, hence invertible in the derived
category. -/
instance isIso_Q_map_baseChange_map {L : FlatLift f K₀} :
    IsIso (DerivedCategory.Q.map L.baseChange.map) := by
  have := L.quasiIso
  infer_instance

/-- **Stacks 0DIU.** The canonical map `ω(K₀) : K₀ ⟶ (K₀ ⊗^L_{O₀} I)[2]` attached to a
square-zero extension of sheaves of rings with ideal sheaf `I`. It is the curvature of the
lifted differential of a bounded above flat lift of `K₀`, transported along the
quasi-isomorphism identifying the reduction of that lift with `K₀`. -/
@[stacks 0DIU "variant: at a supplied derived ideal tensor datum D; the tag is Deformation.ComplexLift.tensorOmegaMinus, the map K₀ ⟶ (K₀ ⊗^L I)[2]"]
def obstructionMap {L : FlatLift f K₀} (T : IdealKernel S L) :
    DerivedCategory.Q.obj K₀ ⟶ (D.functor.obj (DerivedCategory.Q.obj K₀))⟦(2 : ℤ)⟧ :=
  inv (DerivedCategory.Q.map L.baseChange.map) ≫ derivedCurvature D T ≫
    (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
      (D.functor.map (DerivedCategory.Q.map L.baseChange.map))

variable {L : FlatLift f K₀} {M : FlatLift f L₀} {φ : K₀ ⟶ L₀} (h : FlatLiftHom L M φ)
  (TL : IdealKernel S L) (TM : IdealKernel S M)
  (hemb : ∀ n : ℤ, (restrict f).map (((idealTensorFunctor O₀ I).map h.red).f n) ≫ TM.emb n =
    TL.emb n ≫ h.hom n)

include h hemb

/-- Naturality of the derived curvature class along a morphism of flat lifts. -/
theorem derivedCurvature_natural :
    derivedCurvature D TL ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
          (D.functor.map (DerivedCategory.Q.map h.red)) =
      DerivedCategory.Q.map h.red ≫ derivedCurvature D TM := by
  have hcomp := D.comparison.naturality h.red
  have hshift := (DerivedCategory.Q.commShiftIso (2 : ℤ)).hom.naturality
    ((idealTensorFunctor O₀ I).map h.red)
  simp only [Functor.comp_map] at hcomp hshift
  simp only [derivedCurvature, Category.assoc, ← Functor.map_comp]
  rw [← hcomp, Functor.map_comp]
  slice_lhs 2 3 => rw [← hshift]
  slice_lhs 1 2 =>
    rw [← Functor.map_comp, curvatureMap_natural h TL TM hemb, Functor.map_comp]
  simp only [Category.assoc]

/-- **Stacks 0DIU.** Naturality of `ω`: for a map `φ : K₀ ⟶ L₀` of bounded above complexes
covered by a morphism of flat lifts, the square formed by `ω(K₀)`, `ω(L₀)` and the maps induced
by `φ` commutes. -/
@[stacks 0DIU "variant: naturality of ω along a morphism of flat lifts at a supplied derived ideal
tensor datum D; the tag is Deformation.ComplexLift.tensorOmegaMinus_natural"]
theorem obstructionMap_natural :
    DerivedCategory.Q.map φ ≫ obstructionMap D TM =
      obstructionMap D TL ≫
        (CategoryTheory.shiftFunctor (DerivedCategory (SheafMod O₀)) (2 : ℤ)).map
          (D.functor.map (DerivedCategory.Q.map φ)) := by
  have hred : DerivedCategory.Q.map L.baseChange.map ≫ DerivedCategory.Q.map φ =
      DerivedCategory.Q.map h.red ≫ DerivedCategory.Q.map M.baseChange.map := by
    rw [← Functor.map_comp, ← Functor.map_comp, h.red_map]
  have hinv : DerivedCategory.Q.map φ ≫ inv (DerivedCategory.Q.map M.baseChange.map) =
      inv (DerivedCategory.Q.map L.baseChange.map) ≫ DerivedCategory.Q.map h.red := by
    rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
    exact hred
  simp only [obstructionMap, Category.assoc]
  slice_lhs 1 2 => rw [hinv]
  simp only [Category.assoc, ← Functor.map_comp]
  slice_lhs 2 3 => rw [← derivedCurvature_natural D h TL TM hemb]
  simp only [Category.assoc, ← Functor.map_comp, h.red_map]

end Derived

section Canonical

variable {O O₀ : Sheaf J CommRingCat.{w}} {f : O ⟶ O₀} {I : SheafMod O₀}
  [((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, w, w} O₀).flip.obj I).Additive]
  [HasDerivedCategory.{d} (SheafMod O₀)]
  {S : SquareZeroIdeal f I} (D : DerivedIdealTensor I)
  {K₀ : CochainComplex (SheafMod O₀) ℤ}

/-- **Stacks 0DIU.** Two flat lifts of the same complex joined by a morphism of lifts over the
identity give the same map `ω(K₀)`. Together with the existence of a lift receiving maps from
any two, this is the independence of `ω` of the lift, hence its canonicality. -/
@[stacks 0DIU "variant: independence of the flat lift at a supplied derived ideal tensor datum D;
the tag is Deformation.ComplexLift.tensorOmegaMinus"]
theorem obstructionMap_eq_of_hom {L M : FlatLift f K₀} (h : FlatLiftHom L M (𝟙 K₀))
    (TL : IdealKernel S L) (TM : IdealKernel S M)
    (hemb : ∀ n : ℤ, (restrict f).map (((idealTensorFunctor O₀ I).map h.red).f n) ≫
      TM.emb n = TL.emb n ≫ h.hom n) :
    obstructionMap D TL = obstructionMap D TM := by
  have hn := obstructionMap_natural D h TL TM hemb
  simpa using hn.symm

end Canonical

end Deformation.ComplexLift

end
