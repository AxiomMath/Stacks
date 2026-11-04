module

public import StacksFrontier.Deformation.ToposThickening.LiftingDerivationGroup
public import StacksFrontier.CategoryTheory.Sites.Modules.FreeAlgebraConormalDescent
import StacksCore.Tactic.StacksAttribute

/-!
# Step 1 of the proof of Stacks 08UG/08U8: the presentation attached to a lift diagram

This file carries out Step 1 of the proof of [Stacks Project, Tag 08U8] (and of its
ringed-topos twin [Stacks Project, Tag 08UG]) for a
`Deformation.ToposThickening.FirstOrderLiftDiagram`, which is the source's diagram with the
underlying topoi identified as in its own reduction.

The source sets `ℰ = 𝒪_{X'₁} ×_{𝒪_{X₂}} 𝒪_{X'₂}`, a sheaf of *sets* with a surjection
`α : ℰ → 𝒪_{X₁}`, and uses the presentation `NL(α)` in place of `NL_{𝒪_{X₁}/𝒪_{S₁}}`. The two
projections of the fibre product extend to two homomorphisms of `𝒪_{S'₁}`-algebras
`a : 𝒪_{S'₁}[ℰ] ⟶ 𝒪_{X'₁}` and `b : 𝒪_{S'₁}[ℰ] ⟶ 𝒪_{X'₂}`, whose restrictions to
`ℐ' = Ker(𝒪_{S'₁}[ℰ] → 𝒪_{X₁})` land in the two square-zero ideals `𝒢₁` and `𝒢₂`. The
difference `ν ∘ a|_{ℐ'} - b|_{ℐ'}` kills `𝒥₁·𝒪_{S'₁}[ℰ]` and so descends along
`ℐ'/(ℐ')² ↠ ℐ/ℐ²` to the source's homomorphism `ξ : ℐ/ℐ² ⟶ 𝒢₂`.

## Main definitions

* `Deformation.ToposThickening.FirstOrderLiftDiagram.pairPresheaf`: the sheaf of sets `ℰ`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.pairAlpha`: the surjection `α : ℰ → 𝒪_{X₁}`.
* `Deformation.ToposThickening.FirstOrderLiftDiagram.frontAlgebra` and `backAlgebra`: the two
  algebra maps `a` and `b`.

## References

* [Stacks Project, Tag 08U8](https://stacks.math.columbia.edu/tag/08U8)
* [Stacks Project, Tag 08UG](https://stacks.math.columbia.edu/tag/08UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sites.FreeAlgebra
open Stacks.Sites.Conormal

universe v u w

namespace Deformation.ToposThickening.FirstOrderLiftDiagram

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasWeakSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget AddCommGrpCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  (D : FirstOrderLiftDiagram.{v, u, max u v w} J)

/-! ### The local surjectivity built into the diagram -/

/-- The reduction of the front layer is locally surjective: a field of `LiftSquare`, exposed as
an instance so the presentation machinery can find it. -/
instance isLocallySurjective_frontReduction :
    Presheaf.IsLocallySurjective J D.front.reduction.hom := D.front.locallySurjective

/-- The reduction of the back layer is locally surjective. -/
instance isLocallySurjective_backReduction :
    Presheaf.IsLocallySurjective J D.back.reduction.hom := D.back.locallySurjective

/-- The reduction of the front base is locally surjective; this is the hypothesis `u` of the
descent machinery, for `u = 𝒪_{S'₁} ⟶ 𝒪_{S₁}`. -/
instance isLocallySurjective_frontBaseReduction :
    Presheaf.IsLocallySurjective J D.front.baseReduction.hom := D.front.baseLocallySurjective

/-! ### The sheaf of sets `ℰ = 𝒪_{X'₁} ×_{𝒪_{X₂}} 𝒪_{X'₂}` -/

/-- A section of the sheaf of sets `ℰ = 𝒪_{X'₁} ×_{𝒪_{X₂}} 𝒪_{X'₂}` of Step 1 of the proof of
[Stacks Project, Tag 08U8]: a pair of sections of the two thickened structure sheaves whose
reductions agree in the reduced structure sheaf of the back layer, the one taken along the
reduction of the front layer followed by the comparison `g` and the other along the reduction
of the back layer. -/
abbrev PairSection (U : Cᵒᵖ) : Type (max u v w) :=
  {p : D.front.O'.obj.obj U × D.back.O'.obj.obj U //
    D.g.hom.app U (D.front.reduction.hom.app U p.1) = D.back.reduction.hom.app U p.2}

/-- The restriction of a section of `ℰ` along a morphism of the site. -/
def pairSectionMap {U V : Cᵒᵖ} (h : U ⟶ V) (p : D.PairSection U) : D.PairSection V :=
  ⟨(D.front.O'.obj.map h p.1.1, D.back.O'.obj.map h p.1.2), by
    change D.g.hom.app V (D.front.reduction.hom.app V (D.front.O'.obj.map h p.1.1)) =
      D.back.reduction.hom.app V (D.back.O'.obj.map h p.1.2)
    rw [sheafHom_naturality_apply, sheafHom_naturality_apply, p.2,
      sheafHom_naturality_apply]⟩

omit [HasWeakSheafify J CommRingCat] [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] [J.WEqualsLocallyBijective CommRingCat]
  [J.HasSheafCompose (forget AddCommGrpCat)] [HasSheafify J AddCommGrpCat] in
/-- Restriction of sections of `ℰ` is the identity on the identity of the site. -/
theorem pairSectionMap_id (U : Cᵒᵖ) (p : D.PairSection U) : D.pairSectionMap (𝟙 U) p = p := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show D.front.O'.obj.map (𝟙 U) p.1.1 = p.1.1
    simp
  · show D.back.O'.obj.map (𝟙 U) p.1.2 = p.1.2
    simp

omit [HasWeakSheafify J CommRingCat] [HasWeakSheafify J AddCommGrpCat]
  [J.WEqualsLocallyBijective AddCommGrpCat] [J.WEqualsLocallyBijective CommRingCat]
  [J.HasSheafCompose (forget AddCommGrpCat)] [HasSheafify J AddCommGrpCat] in
/-- Restriction of sections of `ℰ` is compatible with composition in the site. -/
theorem pairSectionMap_comp {U V W : Cᵒᵖ} (h : U ⟶ V) (k : V ⟶ W) (p : D.PairSection U) :
    D.pairSectionMap (h ≫ k) p = D.pairSectionMap k (D.pairSectionMap h p) := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · show D.front.O'.obj.map (h ≫ k) p.1.1 =
      D.front.O'.obj.map k (D.front.O'.obj.map h p.1.1)
    simp
  · show D.back.O'.obj.map (h ≫ k) p.1.2 =
      D.back.O'.obj.map k (D.back.O'.obj.map h p.1.2)
    simp

/-- The sheaf of sets `ℰ = 𝒪_{X'₁} ×_{𝒪_{X₂}} 𝒪_{X'₂}` of Step 1 of the proof of
[Stacks Project, Tag 08U8]. Only the underlying sets are used, so this is recorded as a
presheaf of types; it is a sheaf, being a fibre product of sheaves, but the presentation
machinery below needs only the presheaf. -/
def pairPresheaf : Functor Cᵒᵖ (Type (max u v w)) where
  obj U := D.PairSection U
  map h := TypeCat.ofHom (D.pairSectionMap h)
  map_id U := by
    refine TypeCat.homEquiv.injective (funext fun p => ?_)
    exact D.pairSectionMap_id U p
  map_comp h k := by
    refine TypeCat.homEquiv.injective (funext fun p => ?_)
    exact D.pairSectionMap_comp h k p

/-- The first projection `ℰ ⟶ 𝒪_{X'₁}`, as a morphism of presheaves of sets. -/
def pairFst : pairPresheaf D ⟶ underlyingPresheaf J D.front.O' where
  app U := TypeCat.ofHom fun p : D.PairSection U => p.1.1
  naturality _ _ _ := rfl

/-- The second projection `ℰ ⟶ 𝒪_{X'₂}`, as a morphism of presheaves of sets. -/
def pairSnd : pairPresheaf D ⟶ underlyingPresheaf J D.back.O' where
  app U := TypeCat.ofHom fun p : D.PairSection U => p.1.2
  naturality _ _ _ := rfl

/-- The surjection `α : ℰ ⟶ 𝒪_{X₁}` of Step 1 of the proof of
[Stacks Project, Tag 08U8]: the first projection followed by the reduction of the front
layer. -/
def pairAlpha : pairPresheaf D ⟶ underlyingPresheaf J D.front.O :=
  pairFst D ≫ Functor.whiskerRight
    ((sheafToPresheaf J CommRingCat.{max u v w}).map D.front.reduction)
    (forget CommRingCat.{max u v w})

/-- On sections, `α` sends a pair `(x, y)` to the reduction of `x` in `𝒪_{X₁}`. -/
@[simp]
theorem pairAlpha_app (U : Cᵒᵖ) (p : D.PairSection U) :
    (pairAlpha D).app U p = D.front.reduction.hom.app U p.1.1 := by
  simp only [pairAlpha, pairFst, NatTrans.comp_app, Functor.whiskerRight_app]
  rfl

/-- **`α : ℰ ⟶ 𝒪_{X₁}` is locally surjective**, which is the source's "this comes with a
surjective map `α : ℰ → 𝒪_{X₁}`" and the standing hypothesis under which `NL(α)` may replace
`NL_{𝒪_{X₁}/𝒪_{S₁}}` ([Stacks Project, Tag 08TL]). A local section of `𝒪_{X₁}` lifts, locally,
to a section `x` of `𝒪_{X'₁}` because the reduction of the front layer is locally surjective;
refining further, the section `g(x̄)` of `𝒪_{X₂}` lifts to a section `y` of `𝒪_{X'₂}` because the
reduction of the back layer is locally surjective; and `(x, y)` is then a section of the fibre
product over the twice-refined object. -/
instance isLocallySurjective_pairAlpha : Presheaf.IsLocallySurjective J (pairAlpha D) where
  imageSieve_mem {U} s := by
    refine J.transitive (Presheaf.imageSieve_mem J D.front.reduction.hom s) _ ?_
    rintro V f ⟨x, hx⟩
    refine J.superset_covering ?_ (Presheaf.imageSieve_mem J D.back.reduction.hom
      (D.g.hom.app (op V) (D.front.O.obj.map f.op s)))
    rintro W j ⟨y, hy⟩
    have hred : D.front.reduction.hom.app (op W) (D.front.O'.obj.map j.op x) =
        D.front.O.obj.map j.op (D.front.O.obj.map f.op s) := by
      rw [sheafHom_naturality_apply, hx]
    refine ⟨⟨(D.front.O'.obj.map j.op x, y), ?_⟩, ?_⟩
    · change D.g.hom.app (op W) (D.front.reduction.hom.app (op W) (D.front.O'.obj.map j.op x)) =
        D.back.reduction.hom.app (op W) y
      rw [hred, sheafHom_naturality_apply, hy]
    · rw [pairAlpha_app, hred, ← ConcreteCategory.comp_apply, ← D.front.O.obj.map_comp,
        ← op_comp]
      rfl

/-- The second projection followed by the reduction of the back layer is `α` followed by the
comparison `g`: this is exactly the defining condition of the fibre product `ℰ`. -/
theorem pairSnd_comp_reduction :
    pairSnd D ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{max u v w}).map D.back.reduction)
        (forget CommRingCat.{max u v w}) =
      pairAlpha D ≫ Functor.whiskerRight
        ((sheafToPresheaf J CommRingCat.{max u v w}).map D.g)
        (forget CommRingCat.{max u v w}) := by
  ext U p
  simp only [pairAlpha, pairSnd, pairFst, NatTrans.comp_app, Functor.whiskerRight_app]
  exact p.2.symm

/-! ### The two algebra maps `a` and `b` -/

/-- The homomorphism of `𝒪_{S'₁}`-algebras `a : 𝒪_{S'₁}[ℰ] ⟶ 𝒪_{X'₁}` of Step 1 of the proof of
[Stacks Project, Tag 08U8]: the structure map of the front layer on coefficients, the first
projection on the generators. -/
def frontAlgebra : freeAlgebraSheaf J D.front.OB' (pairPresheaf D) ⟶ D.front.O' :=
  freeAlgebraSheafDesc J D.front.OB' D.front.O' (pairPresheaf D) D.front.f' (pairFst D)

/-- The homomorphism of `𝒪_{S'₁}`-algebras `b : 𝒪_{S'₁}[ℰ] ⟶ 𝒪_{X'₂}` of Step 1 of the proof of
[Stacks Project, Tag 08U8]: the comparison of thickened bases followed by the structure map of
the back layer on coefficients, the second projection on the generators. -/
def backAlgebra : freeAlgebraSheaf J D.front.OB' (pairPresheaf D) ⟶ D.back.O' :=
  freeAlgebraSheafDesc J D.front.OB' D.back.O' (pairPresheaf D) (D.gB' ≫ D.back.f') (pairSnd D)

/-- The presentation `α : 𝒪_{S'₁}[ℰ] ⟶ 𝒪_{X₁}` with the *thickened* coefficients, which is the
`restrictedPresentation` of the descent machinery for the base reduction
`𝒪_{S'₁} ⟶ 𝒪_{S₁}`. -/
abbrev thickenedPresentation : freeAlgebraSheaf J D.front.OB' (pairPresheaf D) ⟶ D.front.O :=
  restrictedPresentation J D.front.baseReduction (pairPresheaf D) D.front.f (pairAlpha D)

/-- The presentation `α : 𝒪_{S₁}[ℰ] ⟶ 𝒪_{X₁}` with the reduced coefficients, which is the
`basePresentation` of the descent machinery and the presentation the source's `NL(α)` is taken
of. -/
abbrev reducedPresentation : freeAlgebraSheaf J D.front.OB (pairPresheaf D) ⟶ D.front.O :=
  basePresentation J (pairPresheaf D) D.front.f (pairAlpha D)

/-- **The presentation with thickened coefficients is locally surjective**, because its family
of generators `α` is: [Stacks Project, Tag 08TL]. -/
instance isLocallySurjective_thickenedPresentation :
    Presheaf.IsLocallySurjective J (thickenedPresentation D).hom :=
  isLocallySurjective_freeAlgebraSheafDesc J D.front.OB' D.front.O (pairPresheaf D)
    (D.front.baseReduction ≫ D.front.f) (pairAlpha D)

/-- **The presentation with reduced coefficients is locally surjective**, for the same reason.
This is the presentation the source's `NL(α)` is taken of. -/
instance isLocallySurjective_reducedPresentation :
    Presheaf.IsLocallySurjective J (reducedPresentation D).hom :=
  isLocallySurjective_freeAlgebraSheafDesc J D.front.OB D.front.O (pairPresheaf D)
    D.front.f (pairAlpha D)

/-- **`a` is over the presentation `α`.** The algebra map `a : 𝒪_{S'₁}[ℰ] ⟶ 𝒪_{X'₁}` followed by
the reduction of the front layer is the presentation with thickened coefficients. On
coefficients this is the commutativity of the front square, and on the generators it is the
definition of `α` as the first projection followed by that reduction. -/
theorem frontAlgebra_comp_reduction :
    frontAlgebra D ≫ D.front.reduction = thickenedPresentation D := by
  refine freeAlgebraSheaf_hom_ext J D.front.OB' D.front.O (pairPresheaf D) ?_ ?_
  · rw [← Category.assoc, frontAlgebra,
      freeAlgebraSheafCoefficientMap_comp_desc J D.front.OB' D.front.O' (pairPresheaf D)
        D.front.f' (pairFst D),
      thickenedPresentation, restrictedPresentation,
      freeAlgebraSheafCoefficientMap_comp_desc J D.front.OB' D.front.O (pairPresheaf D)
        (D.front.baseReduction ≫ D.front.f) (pairAlpha D)]
    exact D.front.comm
  · rw [frontAlgebra, thickenedPresentation, restrictedPresentation,
      freeAlgebraSheafVariable_comp_desc J D.front.OB' D.front.O (pairPresheaf D)
        (D.front.baseReduction ≫ D.front.f) (pairAlpha D),
      Functor.map_comp, Functor.whiskerRight_comp, ← Category.assoc,
      freeAlgebraSheafVariable_comp_desc J D.front.OB' D.front.O' (pairPresheaf D)
        D.front.f' (pairFst D)]
    rfl

/-- **`b` is over the presentation `α` followed by the comparison `g`.** The algebra map
`b : 𝒪_{S'₁}[ℰ] ⟶ 𝒪_{X'₂}` followed by the reduction of the back layer is the presentation with
thickened coefficients followed by `g`. On coefficients this combines the commutativity of the
two squares of bases with that of the back square, and on the generators it is the defining
condition of the fibre product `ℰ`. -/
theorem backAlgebra_comp_reduction :
    backAlgebra D ≫ D.back.reduction = thickenedPresentation D ≫ D.g := by
  refine freeAlgebraSheaf_hom_ext J D.front.OB' D.back.O (pairPresheaf D) ?_ ?_
  · rw [← Category.assoc, backAlgebra,
      freeAlgebraSheafCoefficientMap_comp_desc J D.front.OB' D.back.O' (pairPresheaf D)
        (D.gB' ≫ D.back.f') (pairSnd D),
      ← Category.assoc, thickenedPresentation, restrictedPresentation,
      freeAlgebraSheafCoefficientMap_comp_desc J D.front.OB' D.front.O (pairPresheaf D)
        (D.front.baseReduction ≫ D.front.f) (pairAlpha D),
      Category.assoc, D.back.comm, ← Category.assoc, D.gB_comm, Category.assoc, D.g_comm]
    exact (Category.assoc _ _ _).symm
  · rw [backAlgebra, thickenedPresentation, restrictedPresentation, Functor.map_comp,
      Functor.map_comp, Functor.whiskerRight_comp, Functor.whiskerRight_comp,
      ← Category.assoc, ← Category.assoc,
      freeAlgebraSheafVariable_comp_desc J D.front.OB' D.back.O' (pairPresheaf D)
        (D.gB' ≫ D.back.f') (pairSnd D),
      freeAlgebraSheafVariable_comp_desc J D.front.OB' D.front.O (pairPresheaf D)
        (D.front.baseReduction ≫ D.front.f) (pairAlpha D)]
    exact pairSnd_comp_reduction D


/-! ### The two restriction data `ν ∘ a|_{ℐ'}` and `b|_{ℐ'}` -/

/-- The ideal `ℐ' = Ker(𝒪_{S'₁}[ℰ] → 𝒪_{X₁})` of Step 1, objectwise. -/
abbrev thickIdeal (X : Cᵒᵖ) : Ideal ((freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :=
  kernelIdeal (thickenedPresentation D).hom X

/-- The presentation with thickened coefficients, evaluated through `a` and then reduced, is the
presentation itself: the section form of `frontAlgebra_comp_reduction`. -/
theorem reduction_frontAlgebra_apply (X : Cᵒᵖ)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    D.front.reduction.hom.app X ((frontAlgebra D).hom.app X x) =
      (thickenedPresentation D).hom.app X x :=
  congrArg (fun k : freeAlgebraSheaf J D.front.OB' (pairPresheaf D) ⟶ D.front.O =>
    k.hom.app X x) (frontAlgebra_comp_reduction D)

/-- The presentation with thickened coefficients, evaluated through `b` and then reduced, is the
presentation followed by the comparison `g`: the section form of
`backAlgebra_comp_reduction`. -/
theorem reduction_backAlgebra_apply (X : Cᵒᵖ)
    (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) :
    D.back.reduction.hom.app X ((backAlgebra D).hom.app X x) =
      D.g.hom.app X ((thickenedPresentation D).hom.app X x) :=
  congrArg (fun k : freeAlgebraSheaf J D.front.OB' (pairPresheaf D) ⟶ D.back.O =>
    k.hom.app X x) (backAlgebra_comp_reduction D)

/-- The section of the ideal `𝒢₁` of the front layer attached to a local section of `ℐ'` by the
algebra map `a`: the source's `a|_{ℐ'}`. It exists because `a` is over the presentation, so `a`
carries `ℐ'` into the kernel of the reduction of the front layer, which `𝒢₁` is identified
with. -/
def frontIdealSection (X : Cᵒᵖ) (x : D.thickIdeal X) : D.front.G.val.obj X :=
  (D.front.exists_incl ((frontAlgebra D).hom.app X x.1)
    ((reduction_frontAlgebra_apply D X x.1).trans (RingHom.mem_ker.mp x.2))).choose

/-- The inclusion of `𝒢₁` into `𝒪_{X'₁}` sends `frontIdealSection D X x` to `a(x)`. -/
theorem incl_frontIdealSection (X : Cᵒᵖ) (x : D.thickIdeal X) :
    D.front.incl (frontIdealSection D X x) = (frontAlgebra D).hom.app X x.1 :=
  (D.front.exists_incl ((frontAlgebra D).hom.app X x.1)
    ((reduction_frontAlgebra_apply D X x.1).trans (RingHom.mem_ker.mp x.2))).choose_spec

/-- The section of the ideal `𝒢₂` of the back layer attached to a local section of `ℐ'` by the
algebra map `b`: the source's `b|_{ℐ'}`. -/
def backIdealSection (X : Cᵒᵖ) (x : D.thickIdeal X) : D.back.G.val.obj X :=
  (D.back.exists_incl ((backAlgebra D).hom.app X x.1) (by
    rw [reduction_backAlgebra_apply, RingHom.mem_ker.mp x.2, map_zero])).choose

/-- The inclusion of `𝒢₂` into `𝒪_{X'₂}` sends `backIdealSection D X x` to `b(x)`. -/
theorem incl_backIdealSection (X : Cᵒᵖ) (x : D.thickIdeal X) :
    D.back.incl (backIdealSection D X x) = (backAlgebra D).hom.app X x.1 :=
  (D.back.exists_incl ((backAlgebra D).hom.app X x.1) (by
    rw [reduction_backAlgebra_apply, RingHom.mem_ker.mp x.2, map_zero])).choose_spec

/-- `frontIdealSection` sends `0` to `0`. -/
theorem frontIdealSection_zero (X : Cᵒᵖ) :
    frontIdealSection D X 0 = 0 := by
  refine D.front.incl_injective ?_
  rw [incl_frontIdealSection, D.front.incl_zero]
  exact map_zero ((frontAlgebra D).hom.app X).hom

/-- `frontIdealSection` is additive. -/
theorem frontIdealSection_add (X : Cᵒᵖ) (x y : D.thickIdeal X) :
    frontIdealSection D X (x + y) = frontIdealSection D X x + frontIdealSection D X y := by
  refine D.front.incl_injective ?_
  rw [incl_frontIdealSection, D.front.incl_add, incl_frontIdealSection, incl_frontIdealSection]
  exact map_add ((frontAlgebra D).hom.app X).hom x.1 y.1

/-- `frontIdealSection` sends `r • x` to the image of `r` in `𝒪_{X₁}` acting on the section
attached to `x`. -/
theorem frontIdealSection_smul (X : Cᵒᵖ)
    (r : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) (x : D.thickIdeal X) :
    frontIdealSection D X (r • x) =
      toRingSection J ((thickenedPresentation D).hom.app X r) • frontIdealSection D X x := by
  refine D.front.incl_injective ?_
  rw [incl_frontIdealSection, ← reduction_frontAlgebra_apply, ← D.front.mul_incl,
    incl_frontIdealSection]
  exact map_mul ((frontAlgebra D).hom.app X).hom r x.1

/-- `frontIdealSection` commutes with restriction along a morphism `f : X ⟶ Y`. -/
theorem frontIdealSection_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : D.thickIdeal X) :
    frontIdealSection D Y
        ⟨(freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.map f x.1,
          map_kernel (thickenedPresentation D).hom f x.2⟩ =
      D.front.G.val.map f (frontIdealSection D X x) := by
  refine D.front.incl_injective ?_
  rw [incl_frontIdealSection, D.front.incl_naturality, incl_frontIdealSection]
  exact sheafHom_naturality_apply J (frontAlgebra D) f x.1

/-- `backIdealSection` sends `0` to `0`. -/
theorem backIdealSection_zero (X : Cᵒᵖ) :
    backIdealSection D X 0 = 0 := by
  refine D.back.incl_injective ?_
  rw [incl_backIdealSection, D.back.incl_zero]
  exact map_zero ((backAlgebra D).hom.app X).hom

/-- `backIdealSection` is additive. -/
theorem backIdealSection_add (X : Cᵒᵖ) (x y : D.thickIdeal X) :
    backIdealSection D X (x + y) = backIdealSection D X x + backIdealSection D X y := by
  refine D.back.incl_injective ?_
  rw [incl_backIdealSection, D.back.incl_add, incl_backIdealSection, incl_backIdealSection]
  exact map_add ((backAlgebra D).hom.app X).hom x.1 y.1

/-- `backIdealSection` sends `r • x` to the image of `r` in `𝒪_{X₂}` under the presentation
followed by `g`, acting on the section attached to `x`. -/
theorem backIdealSection_smul (X : Cᵒᵖ)
    (r : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) (x : D.thickIdeal X) :
    backIdealSection D X (r • x) =
      toRingSection J (D.g.hom.app X ((thickenedPresentation D).hom.app X r)) •
        backIdealSection D X x := by
  refine D.back.incl_injective ?_
  rw [incl_backIdealSection, ← reduction_backAlgebra_apply, ← D.back.mul_incl,
    incl_backIdealSection]
  exact map_mul ((backAlgebra D).hom.app X).hom r x.1

/-- `backIdealSection` commutes with restriction along a morphism `f : X ⟶ Y`. -/
theorem backIdealSection_map {X Y : Cᵒᵖ} (f : X ⟶ Y) (x : D.thickIdeal X) :
    backIdealSection D Y
        ⟨(freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.map f x.1,
          map_kernel (thickenedPresentation D).hom f x.2⟩ =
      D.back.G.val.map f (backIdealSection D X x) := by
  refine D.back.incl_injective ?_
  rw [incl_backIdealSection, D.back.incl_naturality, incl_backIdealSection]
  exact sheafHom_naturality_apply J (backAlgebra D) f x.1

/-- **The restriction datum `ν ∘ a|_{ℐ'}` of Step 1.** The algebra map `a` carries a local
section of `ℐ'` into the ideal `𝒢₁`, and `ν` carries that into `𝒢₂`, read as a module over
`𝒪_{X₁}` through the comparison `g` — the source's `g_*𝒢₂`. Linearity over `𝒪_{S'₁}[ℰ]` acting
through the presentation combines the fact that a section of the thickened sheaf acts on the
square-zero ideal through its reduction with the linearity of `ν`. -/
def frontRestriction : IdealRestriction (thickenedPresentation D) (pushedIdeal D) where
  app X :=
    { toFun := fun x => D.nuSection (frontIdealSection D X x)
      map_zero' := by
        rw [frontIdealSection_zero]
        exact map_zero (D.nu.val.app X).hom
      map_add' := fun x y => by
        rw [frontIdealSection_add]
        exact D.nuSection_add _ _ }
  app_smul X r g := by
    change D.nuSection (frontIdealSection D X (r • g)) = _
    rw [frontIdealSection_smul]
    exact map_smul (D.nu.val.app X).hom _ _
  app_map {X Y} f g := by
    change D.nuSection (frontIdealSection D Y _) = _
    rw [frontIdealSection_map]
    exact PresheafOfModules.naturality_apply D.nu.val f (frontIdealSection D X g)

/-- **The restriction datum `b|_{ℐ'}` of Step 1.** The algebra map `b` carries a local section
of `ℐ'` into the ideal `𝒢₂`; the scalars act through `g` because `b` is over the presentation
followed by `g`, which is exactly the module structure of the source's `g_*𝒢₂`. -/
def backRestriction : IdealRestriction (thickenedPresentation D) (pushedIdeal D) where
  app X :=
    { toFun := fun x => backIdealSection D X x
      map_zero' := backIdealSection_zero D X
      map_add' := backIdealSection_add D X }
  app_smul X r g := backIdealSection_smul D X r g
  app_map {_X _Y} f g := backIdealSection_map D f g

/-! ### The two restriction data agree on `𝒥₁·𝒪_{S'₁}[ℰ]` -/

/-- **The front algebra map on a coefficient.** `a` sends the generator attached to a section
`j` of `𝒪_{B'₁}` to `f'₁(j)`, by the defining property of the presentation. -/
theorem frontAlgebra_app_coefficientMap (X : Cᵒᵖ) (j : D.front.OB'.obj.obj X) :
    (frontAlgebra D).hom.app X
      ((freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D)).hom.app X j) =
      D.front.f'.hom.app X j :=
  congrArg (fun k : D.front.OB' ⟶ D.front.O' => k.hom.app X j)
    (freeAlgebraSheafCoefficientMap_comp_desc J D.front.OB' D.front.O' (pairPresheaf D)
      D.front.f' (pairFst D))

/-- **The back algebra map on a coefficient.** `b` sends the same generator to
`f'₂(gB'(j))`, the comparison `gB'` of thickened bases intervening. -/
theorem backAlgebra_app_coefficientMap (X : Cᵒᵖ) (j : D.front.OB'.obj.obj X) :
    (backAlgebra D).hom.app X
      ((freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D)).hom.app X j) =
      D.back.f'.hom.app X (D.gB'.hom.app X j) :=
  congrArg (fun k : D.front.OB' ⟶ D.back.O' => k.hom.app X j)
    (freeAlgebraSheafCoefficientMap_comp_desc J D.front.OB' D.back.O' (pairPresheaf D)
      (D.gB' ≫ D.back.f') (pairSnd D))

/-- **The two restriction data agree on a coefficient of `𝒥₁`.** This is the source's assertion
that `a` and `b` agree on `𝒥₁·𝒪_{S'₁}[ℰ]` as maps into `𝒢₂`, at a generator: the section
`a(j) = f'₁(j)` lies in `𝒢₁` exactly because `j` is killed by the base reduction — the
hypothesis `hj`, available at the only call site because the generators of `𝒥₁·𝒪_{S'₁}[ℰ]` are
by definition the coefficients belonging to `Ker(𝒪_{B'₁} ⟶ 𝒪_{B₁})` — and the compatibility
`nu_base` of the diagram then says that `b(j) = f'₂(gB'(j))` is the image under `ν` of the
corresponding section of `𝒢₁`. This is where the commutativity of the left hand square of the
source's diagram of ideal rows enters. -/
theorem frontRestriction_app_coefficientMap (X : Cᵒᵖ) (j : D.front.OB'.obj.obj X)
    (hj : D.front.baseReduction.hom.app X j = 0)
    (h : (freeAlgebraSheafCoefficientMap J D.front.OB' (pairPresheaf D)).hom.app X j ∈
      D.thickIdeal X) :
    (frontRestriction D).app X ⟨_, h⟩ = (backRestriction D).app X ⟨_, h⟩ := by
  have ha := frontAlgebra_app_coefficientMap D X j
  have hb := backAlgebra_app_coefficientMap D X j
  have hfront : D.front.f'.hom.app X j = D.front.incl (frontIdealSection D X ⟨_, h⟩) := by
    rw [incl_frontIdealSection, ha]
  refine D.back.incl_injective ?_
  show D.back.incl (D.nuSection (frontIdealSection D X ⟨_, h⟩)) =
    D.back.incl (backIdealSection D X ⟨_, h⟩)
  rw [incl_backIdealSection, hb, D.nu_base X j (frontIdealSection D X ⟨_, h⟩) hj hfront]
  rfl

/-- **The two restriction data of Step 1 agree on the whole of `𝒥₁·𝒪_{S'₁}[ℰ]`.** The
generators are `frontRestriction_app_coefficientMap`, and a restriction datum is additive and
linear over `𝒪_{S'₁}[ℰ]` acting through the presentation, so the agreement spreads over the
span. This is the hypothesis of the descent
`Stacks.Sites.Conormal.existsUnique_descend_conormalDifference`. -/
theorem frontRestriction_eq_backRestriction (X : Cᵒᵖ) (x : D.thickIdeal X)
    (hx : (x : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X) ∈
      coefficientKernelIdeal J D.front.baseReduction (pairPresheaf D) X) :
    (frontRestriction D).app X x = (backRestriction D).app X x := by
  have hle := coefficientKernelIdeal_le_restrictedPresentationIdeal.{v, u, max u v w, max u v w}
    J D.front.baseReduction (pairPresheaf D) D.front.f (pairAlpha D) X
  suffices hsuf : ∀ (y : (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)).obj.obj X),
      y ∈ coefficientKernelIdeal J D.front.baseReduction (pairPresheaf D) X →
      ∀ (h : y ∈ D.thickIdeal X),
        (frontRestriction D).app X ⟨y, h⟩ = (backRestriction D).app X ⟨y, h⟩ by
    have := hsuf x.1 hx x.2
    exact (congrArg (fun y => (frontRestriction D).app X y) (Subtype.ext rfl)).trans
      (this.trans (congrArg (fun y => (backRestriction D).app X y) (Subtype.ext rfl)))
  intro y hy
  induction hy using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨j, hj, rfl⟩ := hz
    intro h
    exact frontRestriction_app_coefficientMap D X j (RingHom.mem_ker.mp hj) h
  | zero =>
    intro h
    rw [show (⟨0, h⟩ : D.thickIdeal X) = 0 from Subtype.ext rfl,
      map_zero, map_zero]
  | add z z' hz hz' ihz ihz' =>
    intro h
    have hz2 : z ∈ D.thickIdeal X := hle hz
    have hz2' : z' ∈ D.thickIdeal X := hle hz'
    rw [show (⟨z + z', h⟩ : D.thickIdeal X) = ⟨z, hz2⟩ + ⟨z', hz2'⟩ from Subtype.ext rfl,
      map_add, map_add, ihz hz2, ihz' hz2']
  | smul r z hz ihz =>
    intro h
    have hz2 : z ∈ D.thickIdeal X := hle hz
    rw [show (⟨r • z, h⟩ : D.thickIdeal X) = r • (⟨z, hz2⟩ : D.thickIdeal X) from Subtype.ext rfl,
      (frontRestriction D).app_smul, (backRestriction D).app_smul, ihz hz2]

/-! ### The homomorphism `ξ : ℐ/ℐ² ⟶ g_*𝒢₂` of Step 1 -/

/-- The conormal module `ℐ/ℐ²` of the presentation with reduced coefficients: the degree `-1`
term of the source's `NL(α)`, and the module the obstruction homomorphism `ξ` comes out of. -/
abbrev reducedConormal :
    SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf D.front.O) :=
  conormalSheaf.{v, u, max u v w, max u v w} J
    (freeAlgebraSheaf J D.front.OB (pairPresheaf D)) D.front.O (reducedPresentation D)

/-- The surjection `ℐ'/(ℐ')² ↠ ℐ/ℐ²` of Step 1, along which the difference cocycle
descends. -/
abbrev conormalDescentMap :
    conormalSheaf.{v, u, max u v w, max u v w} J
        (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)) D.front.O (thickenedPresentation D) ⟶
      reducedConormal D :=
  presentationConormalMap.{v, u, max u v w, max u v w} J D.front.baseReduction
    (pairPresheaf D) D.front.f (pairAlpha D)

/-- The difference cocycle `ν ∘ a|_{ℐ'} - b|_{ℐ'} : ℐ'/(ℐ')² ⟶ g_*𝒢₂` of Step 1. -/
abbrev conormalDifferenceCocycle :
    conormalSheaf.{v, u, max u v w, max u v w} J
        (freeAlgebraSheaf J D.front.OB' (pairPresheaf D)) D.front.O (thickenedPresentation D) ⟶
      pushedIdeal D :=
  conormalDifference.{v, u, max u v w, max u v w} (thickenedPresentation D) (pushedIdeal D)
    (frontRestriction D) (backRestriction D)

/-- **Step 1 of the proof of [Stacks Project, Tag 08U8] descends the difference.** The
difference cocycle `ν ∘ a|_{ℐ'} - b|_{ℐ'} : ℐ'/(ℐ')² ⟶ g_*𝒢₂` of the two restriction data
factors through the surjection `ℐ'/(ℐ')² ↠ ℐ/ℐ²`, in exactly one way, because the two data
agree on `𝒥₁·𝒪_{S'₁}[ℰ]`, which is the kernel of `ℐ' ↠ ℐ`. -/
theorem existsUnique_obstructionConormalHom :
    ∃! ψ : reducedConormal D ⟶ pushedIdeal D,
      conormalDescentMap D ≫ ψ = conormalDifferenceCocycle D :=
  existsUnique_descend_conormalDifference.{v, u, max u v w, max u v w} J
    D.front.baseReduction (pairPresheaf D) D.front.f (pairAlpha D) (pushedIdeal D)
    (frontRestriction D) (backRestriction D) (frontRestriction_eq_backRestriction D)

/-- **The homomorphism `ξ : ℐ/ℐ² ⟶ g_*𝒢₂` of Step 1 of the proof of
[Stacks Project, Tag 08U8].** It sends the class of a local section `f` of `ℐ` to
`ν(a(f')) - b(f')`, where `f'` is any lift of `f` to a local section of `ℐ'`; that this is well
defined is the content of Step 1, and is `existsUnique_obstructionConormalHom`. The obstruction
class of clause (1) is the class of this homomorphism in `Ext¹(NL(α), 𝒢₂)`. -/
def obstructionConormalHom : reducedConormal D ⟶ pushedIdeal D :=
  (existsUnique_obstructionConormalHom D).choose

/-- The defining property of `ξ`: pulled back along `ℐ'/(ℐ')² ↠ ℐ/ℐ²` it is the difference
cocycle of the two restriction data of Step 1. -/
theorem conormalDescentMap_comp_obstructionConormalHom :
    conormalDescentMap D ≫ obstructionConormalHom D = conormalDifferenceCocycle D :=
  (existsUnique_obstructionConormalHom D).choose_spec.1

end Deformation.ToposThickening.FirstOrderLiftDiagram

end
