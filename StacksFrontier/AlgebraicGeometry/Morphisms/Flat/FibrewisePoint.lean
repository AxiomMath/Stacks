module

public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Flatness.EssentialFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.Module
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.StalkFinitePresentation
public import StacksFrontier.RingTheory.Flat.FibrewiseCriterionEssFPBase
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# The fibrewise criterion for flatness at a point, on local rings

Let `X ⟶ Y ⟶ S` be morphisms of schemes, let `x` be a point of `X` with images `y` in `Y` and
`s` in `S`, and let `M` be a module over the local ring `𝒪_{X,x}`. The fibrewise criterion for
flatness (Stacks Tag 039C) compares

1. `M` is flat over `𝒪_{S,s}`, and the fibre `M/𝔪_s M` is flat over the fibre ring
   `𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}`;
2. `𝒪_{Y,y}` is flat over `𝒪_{S,s}`, and `M` is flat over `𝒪_{Y,y}`,

under the finiteness assumptions of Tag 039C: `X ⟶ S` locally of finite presentation, `M` of
finite presentation over `𝒪_{X,x}`, `Y ⟶ S` locally of finite type, and `M` nonzero.

This file proves that comparison. The two directions are the two halves of the Stacks proof: the
implication (1) ⇒ (2) is the critère de platitude par fibres in its essentially-finitely-presented
form, Stacks Tag 05UV, already available as
`Module.essentiallyOfFinitePresentation_and_flat_and_flat_of_flat_quotient_maximalIdeal`; the
implication (2) ⇒ (1) is transitivity of flatness (Tag 00HC, Mathlib's `Module.Flat.trans`)
together with the fact that a base change of a flat module is flat (Tag 00HI), applied to the
quotient map `𝒪_{Y,y} → 𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}`.

## Main results

* `Stacks.Flatness.flat_quotient_smul_top_of_flat`: the fibre `M/I M` of a flat module is flat
  over the quotient ring `A/I`. This is Stacks Tag 00HI for the ring map `A → A/I`.
* `Stacks.Flatness.flat_and_flat_quotient_smul_top_iff`: the criterion for a chain of local rings
  `R → A → B` and a `B`-module `M`.
* `Stacks.Flatness.flat_and_flat_fibre_stalk_iff`: the same criterion for the chain of stalks of
  `X ⟶ Y ⟶ S` at a point, with the two finiteness inputs discharged from the finiteness of the
  morphisms.
* `Stacks.Flatness.isFlatOverAt_comp`: for morphisms of schemes, condition (2) implies the first
  half of condition (1).
* `Stacks.Flatness.flat_and_flat_fibre_stalk_sheaf_iff`: the criterion for the stalk of a finite
  type quasi-coherent module, where the finite-presentation hypothesis is no longer assumed but
  derived from Stacks Tag 05I7.

## Implementation notes

The fibre of `M` is spelled as in Tag 05UV: the ideal is `(maximalIdeal R).map (algebraMap R A)`,
the fibre ring is the quotient of `A` by it, and the fibre module is `M ⧸ (that ideal) • ⊤` taken
in `Submodule A M`, which carries a module structure over the fibre ring by
`Module.isTorsionBySet_quotient_ideal_smul`. Mathlib has no `IsScalarTower A (A ⧸ I) (M ⧸ I • ⊤)`
instance, and that tower is what lets flatness be transported between `(A ⧸ I) ⊗[A] M` and
`M ⧸ I • ⊤`; it is supplied privately here, where it is pointwise `rfl` on the generators of the
quotient.

`flat_and_flat_fibre_stalk_iff` is stated for an arbitrary module over the stalk `𝒪_{X,x}` rather
than for the stalk of a sheaf of modules, because the three flatness conditions it does not
quotient are then literally `AlgebraicGeometry.IsFlatOverAt` and `AlgebraicGeometry.IsFlatAt` once
the module is instantiated at a stalk: those predicates install exactly the module structures
`Module.compHom _ (f.stalkMap x).hom` used here. The scalar tower between the three stalks is
`AlgebraicGeometry.Scheme.Hom.stalkMap_comp`; `Algebra.EssFiniteType` for `𝒪_{S,s} → 𝒪_{Y,y}` is
`AlgebraicGeometry.LocallyOfFiniteType.stalkMap` and essential finite presentation for
`𝒪_{S,s} → 𝒪_{X,x}` is
`AlgebraicGeometry.LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap`.

What Tag 039C states in addition, and what is **not** proved here, is that the fibre ring and the
fibre module are the stalk of the fibre scheme `Y_s` at `y` and the stalk of the pullback of a
finitely presented quasi-coherent module to `X_s` at `x`. Those two identifications are missing
infrastructure. For the second one, `PullbackStalkTensor.stalkPullbackTensorIso` (Stacks 0098) is
now stated for ringed spaces in an arbitrary universe, but it computes the stalk of the *tensor
formula* `𝒪_X ⊗_{f⁻¹𝒪_Y} f⁻¹G` of Stacks 0095 (2), not of the left adjoint
`RingedSpaceModuleAdjunction.modulePullback`; identifying the two is still open and needs a left
adjoint to `PresheafOfModules.restrictScalars`, which Mathlib does not have.

The finite presentation of the stalk is no longer an assumption of the sheaf-level statement.
`Stacks.Flatness.flat_and_flat_fibre_stalk_sheaf_iff` instantiates
`flat_and_flat_fibre_stalk_iff` at the stalk of a finite type quasi-coherent module and derives
finite presentation of that stalk from Stacks Tag 05I7
(`Stacks.Flatness.finitePresentation_stalk_of_isFlatOverAt`) on both sides of the equivalence; it
therefore carries Stacks Tag 05I5 as a hypothesis, which is the one proposition Tag 05I7 still
rests on in this repository. No declaration here carries the `039C` tag.

## References

* [Stacks Project, Tag 039C](https://stacks.math.columbia.edu/tag/039C)
* [Stacks Project, Tag 05UV](https://stacks.math.columbia.edu/tag/05UV)
* [Stacks Project, Tag 00HC](https://stacks.math.columbia.edu/tag/00HC)
* [Stacks Project, Tag 00HI](https://stacks.math.columbia.edu/tag/00HI)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry IsLocalRing TensorProduct

universe u

namespace Stacks.Flatness

/-- Transport of flatness along a linear equivalence that is only linear over a subring whose
image is all of the base: if `A → B` is surjective and `e : P ≃ₗ[A] Q` is an equivalence of
`B`-modules which is `A`-linear, then `e` is automatically `B`-linear, so flatness of `P` over
`B` gives flatness of `Q` over `B`. -/
private theorem flat_of_linearEquiv_of_surjective {A B P Q : Type*} [CommRing A] [CommRing B]
    [Algebra A B] (hsurj : Function.Surjective (algebraMap A B))
    [AddCommGroup P] [Module A P] [Module B P] [IsScalarTower A B P]
    [AddCommGroup Q] [Module A Q] [Module B Q] [IsScalarTower A B Q]
    (e : P ≃ₗ[A] Q) [Module.Flat B P] : Module.Flat B Q :=
  Module.Flat.of_linearEquiv
    (AddEquiv.toLinearEquiv (R := B) e.toAddEquiv fun b p => by
      obtain ⟨a, rfl⟩ := hsurj b
      rw [algebraMap_smul, algebraMap_smul]
      exact e.map_smul a p).symm

/-- The quotient `M ⧸ I • ⊤` of an `A`-module by an ideal is a module over `A ⧸ I` whose scalar
action is compatible with the one of `A`. Mathlib provides the module structure but not this
tower. -/
private theorem isScalarTower_quotient_smul_top {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A) :
    IsScalarTower A (A ⧸ I) (M ⧸ (I • (⊤ : Submodule A M))) :=
  IsScalarTower.of_algebraMap_smul fun a q => by
    induction q using Submodule.Quotient.induction_on with
    | H m => exact Module.Quotient.mk_smul_mk M I a m

/-- **Stacks Tag 00HI for the quotient map `A → A ⧸ I`.** The fibre `M ⧸ I M` of a flat
`A`-module `M` is flat over the quotient ring `A ⧸ I`, being the base change of `M` along
`A → A ⧸ I`. -/
public theorem flat_quotient_smul_top_of_flat {A M : Type*} [CommRing A] [AddCommGroup M]
    [Module A M] (I : Ideal A) [Module.Flat A M] :
    Module.Flat (A ⧸ I) (M ⧸ (I • (⊤ : Submodule A M))) :=
  have := isScalarTower_quotient_smul_top (A := A) (M := M) I
  flat_of_linearEquiv_of_surjective (A := A) (B := A ⧸ I) Ideal.Quotient.mk_surjective
    (TensorProduct.quotTensorEquivQuotSMul M I)

/-- **The fibrewise criterion for flatness at a point, on local rings** (the local content of
Stacks Tag 039C). Let `R → A → B` be local homomorphisms of local rings, let `𝔪` be the maximal
ideal of `R`, and let `M` be a nonzero `B`-module of finite presentation. Assume `R → B` is
essentially of finite presentation and `R → A` is essentially of finite type. Then `M` is flat
over `R` with flat fibre `M/𝔪M` over `A/𝔪A` if and only if `A` is flat over `R` and `M` is flat
over `A`.

The forward implication is Stacks Tag 05UV; the reverse one needs none of the finiteness
hypotheses and is transitivity of flatness (Tag 00HC) together with
`Stacks.Flatness.flat_quotient_smul_top_of_flat` (Tag 00HI). -/
public theorem flat_and_flat_quotient_smul_top_iff {R A B M : Type*} [CommRing R] [CommRing A]
    [CommRing B] [IsLocalRing R] [IsLocalRing A] [IsLocalRing B]
    [Algebra R A] [Algebra A B] [Algebra R B] [IsScalarTower R A B]
    [IsLocalHom (algebraMap R A)] [IsLocalHom (algebraMap A B)]
    [AddCommGroup M] [Module R M] [Module A M] [Module B M]
    [IsScalarTower R A M] [IsScalarTower A B M]
    [Algebra.EssFiniteType R A] [Module.FinitePresentation B M] [Nontrivial M]
    (hRB : (algebraMap R B).EssentiallyOfFinitePresentation) :
    (Module.Flat R M ∧
        Module.Flat (A ⧸ (maximalIdeal R).map (algebraMap R A))
          (M ⧸ ((maximalIdeal R).map (algebraMap R A) • (⊤ : Submodule A M))))
      ↔ (Module.Flat R A ∧ Module.Flat A M) := by
  constructor
  · rintro ⟨_, _⟩
    exact (Module.essentiallyOfFinitePresentation_and_flat_and_flat_of_flat_quotient_maximalIdeal
      (R := R) (S := A) (S' := B) (M := M) hRB).2
  · rintro ⟨_, _⟩
    exact ⟨Module.Flat.trans R A M, flat_quotient_smul_top_of_flat _⟩

/-- **The fibrewise criterion for flatness at a point of a chain of schemes** (the local content
of Stacks Tag 039C). For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ S` with `X ⟶ S` locally of
finite presentation and `g` locally of finite type, a point `x` of `X`, and a nonzero module `M`
of finite presentation over the stalk `𝒪_{X,x}`: `M` is flat over `𝒪_{S,s}` with flat fibre
`M/𝔪_s M` over `𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}` if and only if `𝒪_{Y,y}` is flat over `𝒪_{S,s}` and `M` is
flat over `𝒪_{Y,y}`, where `y = f x` and `s = g y`.

The algebra structure on the stalks and the two coarser module structures on `M` are taken as
parameters pinned by `hRA`, `hAM` and `hRM`, so that the statement mentions only the stalk maps.
With `M` instantiated at the stalk of a sheaf of modules on `X` and the three equations supplied
by `rfl`, the left-hand first conjunct is `AlgebraicGeometry.IsFlatOverAt` for `f ≫ g` and the
right-hand conjuncts are `AlgebraicGeometry.IsFlatAt` for `g` and
`AlgebraicGeometry.IsFlatOverAt` for `f`. The fibre conjunct is written with quotients of stalks,
not with the stalks of the fibre schemes; see the module docstring. -/
public theorem flat_and_flat_fibre_stalk_iff {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] (x : X)
    (M : Type u) [AddCommGroup M]
    [Algebra (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))]
    [Module (X.presheaf.stalk x) M] [Module (Y.presheaf.stalk (f x)) M]
    [Module (S.presheaf.stalk (g (f x))) M]
    [Module.FinitePresentation (X.presheaf.stalk x) M] [Nontrivial M]
    (hRA : algebraMap (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))
      = (g.stalkMap (f x)).hom)
    (hAM : ∀ (a : Y.presheaf.stalk (f x)) (m : M), a • m = (f.stalkMap x).hom a • m)
    (hRM : ∀ (r : S.presheaf.stalk (g (f x))) (m : M),
      r • m = ((f ≫ g).stalkMap x).hom r • m) :
    (Module.Flat (S.presheaf.stalk (g (f x))) M ∧
        Module.Flat (Y.presheaf.stalk (f x) ⧸
            (maximalIdeal (S.presheaf.stalk (g (f x)))).map
              (algebraMap (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))))
          (M ⧸ ((maximalIdeal (S.presheaf.stalk (g (f x)))).map
              (algebraMap (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))) •
            (⊤ : Submodule (Y.presheaf.stalk (f x)) M))))
      ↔ (Module.Flat (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) ∧
          Module.Flat (Y.presheaf.stalk (f x)) M) := by
  let _ : Algebra (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) := (f.stalkMap x).hom.toAlgebra
  let _ : Algebra (S.presheaf.stalk (g (f x))) (X.presheaf.stalk x) :=
    ((f ≫ g).stalkMap x).hom.toAlgebra
  have hAB : algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) = (f.stalkMap x).hom := rfl
  have hRB : algebraMap (S.presheaf.stalk (g (f x))) (X.presheaf.stalk x)
      = ((f ≫ g).stalkMap x).hom := rfl
  have hcomp : ∀ r : S.presheaf.stalk (g (f x)),
      ((f ≫ g).stalkMap x).hom r = (f.stalkMap x).hom ((g.stalkMap (f x)).hom r) :=
    RingHom.congr_fun (congrArg (·.hom) (Scheme.Hom.stalkMap_comp f g x))
  have : IsScalarTower (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))
      (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [hRB, hAB, hRA]
      exact hcomp r
  have : IsScalarTower (Y.presheaf.stalk (f x)) (X.presheaf.stalk x) M :=
    IsScalarTower.of_algebraMap_smul fun a m => by rw [hAB, hAM]
  have : IsScalarTower (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) M :=
    IsScalarTower.of_algebraMap_smul fun r m => by
      rw [hRA, hAM, hRM]
      exact congrArg (· • m) (hcomp r).symm
  have : IsLocalHom (algebraMap (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x))) := by
    rw [hRA]
    infer_instance
  have : IsLocalHom (algebraMap (Y.presheaf.stalk (f x)) (X.presheaf.stalk x)) := by
    rw [hAB]
    infer_instance
  have : Algebra.EssFiniteType (S.presheaf.stalk (g (f x))) (Y.presheaf.stalk (f x)) := by
    rw [← RingHom.essFiniteType_algebraMap, hRA]
    exact LocallyOfFiniteType.stalkMap g (f x)
  refine flat_and_flat_quotient_smul_top_iff (B := X.presheaf.stalk x) ?_
  rw [hRB]
  exact LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap (f ≫ g) x

/-- For morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ S`, an `𝒪_X`-module flat over `Y` at `x`
is flat over `S` at `x` as soon as `g` is flat at `f x`. This is
`AlgebraicGeometry.IsFlatOverAt.comp` read through the underlying morphisms of ringed spaces, and
it is the half of condition (1) of Stacks Tag 039C that follows from condition (2) with no
finiteness hypothesis. -/
public lemma isFlatOverAt_comp {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    (F : SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) (x : X)
    (hF : AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x)
    (hg : AlgebraicGeometry.IsFlatAt g.toLRSHom.toShHom (f x)) :
    AlgebraicGeometry.IsFlatOverAt (f ≫ g).toLRSHom.toShHom F x :=
  AlgebraicGeometry.IsFlatOverAt.comp f.toLRSHom.toShHom g.toLRSHom.toShHom F x hF hg

/-- **The fibrewise criterion for flatness at a point, for the stalk of a sheaf of modules** (the
local content of Stacks Tag 039C, with its finite-presentation hypothesis discharged). For
morphisms of schemes `f : X ⟶ Y` and `g : Y ⟶ S` with `X ⟶ S` locally of finite presentation and
`g` locally of finite type, and a finite type quasi-coherent `𝒪_X`-module `F` with nonzero stalk
at `x`: `F` is flat over `S` at `x` with flat fibre `F_x/𝔪_s F_x` over
`𝒪_{Y,y}/𝔪_s 𝒪_{Y,y}` if and only if `g` is flat at `y` and `F` is flat over `Y` at `x`.

This is `Stacks.Flatness.flat_and_flat_fibre_stalk_iff` instantiated at `M = F_x`, where the
hypothesis `Module.FinitePresentation 𝒪_{X,x} M` is no longer needed: in the forward direction it
comes from the first conjunct by Stacks 05I7, and in the backward direction from the first
conjunct of the right-hand side together with
`Stacks.Flatness.isFlatOverAt_comp` and the same tag. Stacks 05I7 is
`Stacks.Flatness.finitePresentation_stalk_of_isFlatOverAt`, which is now a theorem. With `M`
instantiated at the stalk the three module structures are the canonical ones, so the two flatness
conjuncts that are not quotients are literally `AlgebraicGeometry.IsFlatOverAt` and
`AlgebraicGeometry.IsFlatAt`. -/
public theorem flat_and_flat_fibre_stalk_sheaf_iff
    {X Y S : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ S)
    [LocallyOfFinitePresentation (f ≫ g)] [LocallyOfFiniteType g] (x : X)
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    [Nontrivial (ToType (TopCat.Presheaf.stalk F.val.presheaf x))] :
    letI : Algebra (ToType (S.presheaf.stalk (g (f x)))) (ToType (Y.presheaf.stalk (f x))) :=
      (g.stalkMap (f x)).hom.toAlgebra
    letI : Module (ToType (Y.presheaf.stalk (f x)))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
      Module.compHom _ (f.stalkMap x).hom
    letI : Module (ToType (S.presheaf.stalk (g (f x))))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
      Module.compHom _ ((f ≫ g).stalkMap x).hom
    (AlgebraicGeometry.IsFlatOverAt (f ≫ g).toLRSHom.toShHom F x ∧
        Module.Flat (ToType (Y.presheaf.stalk (f x)) ⧸
            (maximalIdeal (ToType (S.presheaf.stalk (g (f x))))).map
              (algebraMap (ToType (S.presheaf.stalk (g (f x))))
                (ToType (Y.presheaf.stalk (f x)))))
          (ToType (TopCat.Presheaf.stalk F.val.presheaf x) ⧸
            ((maximalIdeal (ToType (S.presheaf.stalk (g (f x))))).map
              (algebraMap (ToType (S.presheaf.stalk (g (f x))))
                (ToType (Y.presheaf.stalk (f x)))) •
              (⊤ : Submodule (ToType (Y.presheaf.stalk (f x)))
                (ToType (TopCat.Presheaf.stalk F.val.presheaf x))))))
      ↔ (AlgebraicGeometry.IsFlatAt g.toLRSHom.toShHom (f x) ∧
          AlgebraicGeometry.IsFlatOverAt f.toLRSHom.toShHom F x) := by
  let _ : Algebra (ToType (S.presheaf.stalk (g (f x)))) (ToType (Y.presheaf.stalk (f x))) :=
    (g.stalkMap (f x)).hom.toAlgebra
  let _ : Module (ToType (Y.presheaf.stalk (f x)))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.compHom _ (f.stalkMap x).hom
  let _ : Module (ToType (S.presheaf.stalk (g (f x))))
      (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) :=
    Module.compHom _ ((f ≫ g).stalkMap x).hom
  have key : Module.FinitePresentation (ToType (X.presheaf.stalk x))
        (ToType (TopCat.Presheaf.stalk F.val.presheaf x)) → _ := fun _ =>
    flat_and_flat_fibre_stalk_iff f g x (ToType (TopCat.Presheaf.stalk F.val.presheaf x))
      rfl (fun _ _ => rfl) (fun _ _ => rfl)
  exact ⟨fun hL => (key (finitePresentation_stalk_of_isFlatOverAt (f ≫ g) F x hL.1)).mp hL,
    fun hR => (key (finitePresentation_stalk_of_isFlatOverAt (f ≫ g) F x
      (isFlatOverAt_comp f g F x hR.2 hR.1))).mpr hR⟩

end Stacks.Flatness

end
