module

public import StacksFrontier.AlgebraicGeometry.Assembly.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleOpenFactor
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.Divisors.ReflexiveEquivalence.StalkDescent
public import StacksFrontier.AlgebraicGeometry.FiberRank.ConstantStalkRank
public import StacksFrontier.AlgebraicGeometry.FiberRank.LocallyFree
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.DualFiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Smooth.DifferentialsRank
public import StacksCore.Tactic.StacksAttribute

/-!
# The normal bundle of the diagonal of a smooth morphism

Let `f : Y ⟶ Z` be a smooth morphism of schemes. The diagonal `Δ : Y ⟶ Y ×_Z Y` is an immersion,
and it is closed exactly when `f` is separated, which is not assumed. It factors as the closed
immersion `Δ' : Y ⟶ U` into the open neighbourhood `U = Y ×_Z Y ∖ ∂Δ(Y)` of its image followed by
the inclusion of `U`; in Mathlib these are `AlgebraicGeometry.Scheme.Hom.liftCoborder` and
`AlgebraicGeometry.Scheme.Hom.coborderRange`, with commuting equation
`AlgebraicGeometry.Scheme.Hom.liftCoborder_ι` and `Δ'` a closed immersion by instance.

The conormal sheaf of `Δ` is the sheaf of relative differentials `Ω_{Y/Z}` (Stacks 08S2), which
is finite locally free because `f` is smooth (Stacks 02G1), and of rank `d` when `f` has relative
dimension `d`: the rank of `Ω_{Y/Z}` at a point is the local dimension there of the fibre through
it. The conormal sheaf of `Δ'` is that of `Δ`, so `𝒩 = 𝒞_{Y/U}^∨` is a finite locally free
`𝒪_Y`-module of rank `d`, and since a finite locally free module is reflexive, the canonical map
`𝒞_{Y/U} ⟶ 𝒩^∨` is an isomorphism, whose inverse is a surjection `𝒩^∨ ⟶ 𝒞_{Y/U}`. That is a
virtual normal bundle for `Δ'` in the sense of Stacks 0FBQ, of rank `d`: the normal bundle of the
diagonal, and the input from which the Gysin class `Δ^!` of Stacks 0FBR is built.

## Main definitions

* `Stacks.Chow.VirtualNormalBundle.ofIsFiniteLocallyFree`: the normal bundle `𝒞^∨` of an
  immersion whose conormal sheaf `𝒞` is finite locally free, as a virtual normal bundle.
* `Stacks.Chow.diagonalVirtualNormalBundle`: the normal bundle of the diagonal of a smooth
  morphism, as a virtual normal bundle for the closed factor `Δ'` of the diagonal.

## Main results

* `Stacks.AlgebraicGeometry.ReflexiveModules.toDoubleDual_isIso_of_isFiniteLocallyFree`: a finite
  locally free module on an arbitrary scheme is reflexive.
* `AlgebraicGeometry.SmoothOfRelativeDimension.relativeDimension`: a morphism smooth of relative
  dimension `d` has relative dimension `d` in the sense of Stacks 02NJ.
* `Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials_of_relativeDimension`:
  `Ω_{Y/Z}` is finite locally free of rank `d` for `f` smooth of relative dimension `d`.
* `Stacks.Chow.isFiniteLocallyFreeOfRank_immersionConormalSheaf_diagonal` and
  `Stacks.Chow.isFiniteLocallyFreeOfRank_immersionConormalSheaf_liftCoborder_diagonal`: the
  conormal sheaves of `Δ` and of `Δ'` are finite locally free of rank `d`.
* `Stacks.Chow.isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle`: the normal bundle of the
  diagonal has rank `d`.

## Implementation notes

Relative dimension is read in the sense of Stacks 02NJ, `AlgebraicGeometry.RelativeDimension`,
which is the hypothesis the flat pullbacks of the chapter carry; the variant for Mathlib's
`AlgebraicGeometry.SmoothOfRelativeDimension` follows from
`AlgebraicGeometry.SmoothOfRelativeDimension.relativeDimension`. Neither local Noetherianity nor
separatedness is needed: the rank is computed from the stalks of `Ω_{Y/Z}`, and reflexivity of a
finite locally free module is checked on stalks, which are finite free.

The virtual normal bundle is attached to the closed factor `Δ'` rather than to `Δ`, because the
construction of the class of Stacks 0FBK takes a closed immersion; a virtual normal bundle of `Δ'`
is the same as one of `Δ` by `Stacks.Chow.VirtualNormalBundle.openFactorEquiv`. It is defined for
an arbitrary smooth `f`, the relative dimension entering only through the rank.

## References

* [Stacks Project, Section 42.60 (Tag 0FBR)](https://stacks.math.columbia.edu/tag/0FBR)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 08S2](https://stacks.math.columbia.edu/tag/08S2)
* [Stacks Project, Tag 02G1](https://stacks.math.columbia.edu/tag/02G1)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules Stacks.Thickenings

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

/-- **A finite locally free module on a scheme is reflexive.** Its module and its dual are of
finite presentation, so reflexivity may be checked on stalks (Stacks 0AY3), and each stalk is the
stalk of a finite free module over a trivialising open, hence finite free and reflexive. No
Noetherian or coherence hypothesis is needed. -/
theorem toDoubleDual_isIso_of_isFiniteLocallyFree {X : Scheme.{u}} (F : X.Modules)
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} F) :
    IsIso (toDoubleDual F) := by
  have : F.IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree F hF
  have : (dualSheaf F).IsFinitePresentation :=
    AlgebraicGeometry.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree _
      (isFiniteLocallyFree_dualSheaf F hF)
  refine Stacks.AlgebraicGeometry.ReflexiveEquivalence.isReflexive_of_forall_isReflexive_stalk F
    fun x => ?_
  obtain ⟨U, hxU, I, hIfin, ⟨e⟩⟩ := (Scheme.Modules.isFiniteLocallyFree_iff F).2 hF x
  exact ReflexiveEquivalence.isReflexive_stalk_of_isReflexive_stalk_restrict
    U.ι F ⟨x, hxU⟩
    (Stacks.FundamentalGroup.ExtendedEtale.isReflexive_stalk_of_iso_free (Y := U.toScheme)
      ⟨x, hxU⟩ (F.restrict U.ι) I e)

end Stacks.AlgebraicGeometry.ReflexiveModules

namespace AlgebraicGeometry

variable {X S : Scheme.{u}}

/-- **A morphism smooth of relative dimension `d` has relative dimension `d`** in the sense of
Stacks 02NJ: each fibre is smooth of relative dimension `d` over its residue field, so it has
local dimension `d` at every point, hence is equidimensional, and of dimension `d` when it is
nonempty. -/
theorem SmoothOfRelativeDimension.relativeDimension (d : ℕ) (f : X ⟶ S) [LocallyOfFiniteType f]
    [SmoothOfRelativeDimension d f] : RelativeDimension f d := by
  intro s hs
  have hsm : SmoothOfRelativeDimension d (f.fiberToSpecResidueField s) := by
    let := smoothOfRelativeDimension_isStableUnderBaseChange d
    show SmoothOfRelativeDimension d (pullback.snd f (S.fromSpecResidueField s))
    exact MorphismProperty.of_isPullback
      (IsPullback.of_hasPullback f (S.fromSpecResidueField s)) inferInstance
  exact ⟨equidimensional_of_topologicalKrullDimAt_eq (S.residueField s) (f.fiber s)
      (f.fiberToSpecResidueField s)
      (@topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field ↥(S.residueField s) _
        (f.fiber s) d (f.fiberToSpecResidueField s) hsm),
    @topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field ↥(S.residueField s) _
      (f.fiber s) hs d (f.fiberToSpecResidueField s) hsm⟩

/-- **The sheaf of relative differentials of a smooth morphism of relative dimension `d` is
finite locally free of rank `d`.** It is finite locally free by Stacks 02G1, its rank at a point
is the local dimension of the fibre through that point, and a fibre of relative dimension `d` is
equidimensional of dimension `d`, so has local dimension `d` everywhere. -/
@[ega "IV 17.10.2" "special case"]
theorem Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials_of_relativeDimension
    (f : X ⟶ S) [Smooth f] {d : ℕ} (hf : RelativeDimension f d) :
    SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Scheme.Hom.relativeDifferentials f) d := by
  have hflf : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
      (Scheme.Hom.relativeDifferentials f) :=
    Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f
  obtain ⟨hft, hfree, -⟩ :=
    ((Scheme.Modules.flat_finitePresentation_locallyFree_fiberRank_tfae
      (Scheme.Hom.relativeDifferentials f)).out 4 5 rfl rfl).mp hflf
  have _ := hft
  refine Scheme.Modules.isFiniteLocallyFreeOfRank_of_forall_fiberRank_eq _ d fun x => ?_
  rw [Scheme.Modules.fiberRank_eq_finrank_stalk (Scheme.Hom.relativeDifferentials f) x (hfree x)]
  have hdim := finrank_stalk_relativeDifferentials_eq_fiberDimensionAt f x
  obtain ⟨heq, hd⟩ := hf (f x) ⟨f.asFiber x⟩
  rw [topologicalKrullDimAt_eq_of_equidimensional (S.residueField (f x)) (f.fiber (f x))
    (f.fiberToSpecResidueField (f x)) heq hd (f.asFiber x)] at hdim
  exact_mod_cast hdim

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### The normal bundle of an immersion with finite locally free conormal sheaf -/

section OfIsFiniteLocallyFree

variable {W X : Scheme.{u}} (i : W ⟶ X) [IsImmersion i]
  (h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} (immersionConormalSheaf i))

/-- **The normal bundle of an immersion with finite locally free conormal sheaf.** If the
conormal sheaf `𝒞` of `i` is finite locally free, then `𝒩 = 𝒞^∨` is finite locally free and the
inverse of the canonical isomorphism `𝒞 ⟶ 𝒞^∨∨` is a surjection `𝒩^∨ ⟶ 𝒞`, so `𝒩` is a virtual
normal bundle for `i` in the sense of Stacks 0FBQ. -/
noncomputable def VirtualNormalBundle.ofIsFiniteLocallyFree : VirtualNormalBundle i where
  bundle := dualSheaf (immersionConormalSheaf i)
  isFiniteLocallyFree := isFiniteLocallyFree_dualSheaf _ h
  surjection := @inv _ _ _ _ (toDoubleDual (immersionConormalSheaf i))
    (toDoubleDual_isIso_of_isFiniteLocallyFree _ h)
  epi := @IsIso.epi_of_iso _ _ _ _ _ (@IsIso.inv_isIso _ _ _ _ _
    (toDoubleDual_isIso_of_isFiniteLocallyFree _ h))

/-- The underlying module of `Stacks.Chow.VirtualNormalBundle.ofIsFiniteLocallyFree` is the dual
`𝒩 = 𝒞^∨` of the conormal sheaf. -/
@[simp]
theorem VirtualNormalBundle.ofIsFiniteLocallyFree_bundle :
    (VirtualNormalBundle.ofIsFiniteLocallyFree i h).bundle =
      dualSheaf (immersionConormalSheaf i) :=
  rfl

/-- The structural surjection of `Stacks.Chow.VirtualNormalBundle.ofIsFiniteLocallyFree` is
inverse to the canonical map into the double dual. -/
@[simp]
theorem VirtualNormalBundle.toDoubleDual_comp_ofIsFiniteLocallyFree_surjection :
    toDoubleDual (immersionConormalSheaf i) ≫
        (VirtualNormalBundle.ofIsFiniteLocallyFree i h).surjection = 𝟙 _ :=
  @IsIso.hom_inv_id _ _ _ _ _ (toDoubleDual_isIso_of_isFiniteLocallyFree _ h)

/-- The structural surjection of `Stacks.Chow.VirtualNormalBundle.ofIsFiniteLocallyFree` is
inverse to the canonical map into the double dual. -/
@[simp]
theorem VirtualNormalBundle.ofIsFiniteLocallyFree_surjection_comp_toDoubleDual :
    (VirtualNormalBundle.ofIsFiniteLocallyFree i h).surjection ≫
        toDoubleDual (immersionConormalSheaf i) = 𝟙 _ :=
  @IsIso.inv_hom_id _ _ _ _ _ (toDoubleDual_isIso_of_isFiniteLocallyFree _ h)

/-- The structural surjection of `Stacks.Chow.VirtualNormalBundle.ofIsFiniteLocallyFree` is an
isomorphism. -/
instance VirtualNormalBundle.isIso_ofIsFiniteLocallyFree_surjection :
    IsIso (VirtualNormalBundle.ofIsFiniteLocallyFree i h).surjection :=
  @IsIso.inv_isIso _ _ _ _ _ (toDoubleDual_isIso_of_isFiniteLocallyFree _ h)

/-- If the conormal sheaf has constant rank `r`, so has the normal bundle. -/
instance VirtualNormalBundle.isFiniteLocallyFreeOfRank_ofIsFiniteLocallyFree_bundle (r : ℕ)
    [hr : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (immersionConormalSheaf i) r] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (VirtualNormalBundle.ofIsFiniteLocallyFree i h).bundle r :=
  isFiniteLocallyFreeOfRank_dualSheaf (immersionConormalSheaf i) r (hE := hr)

end OfIsFiniteLocallyFree

/-! ### The conormal sheaf of the diagonal -/

variable {Y Z : Scheme.{u}} (f : Y ⟶ Z)

/-- **The conormal sheaf of the closed factor of the diagonal of a smooth morphism is finite
locally free.** It is the conormal sheaf of the diagonal, which is `Ω_{Y/Z}` by Stacks 08S2, and
`Ω_{Y/Z}` is finite locally free by Stacks 02G1. -/
theorem isFiniteLocallyFree_immersionConormalSheaf_liftCoborder_diagonal [Smooth f] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (immersionConormalSheaf (pullback.diagonal f).liftCoborder) :=
  (Scheme.Modules.isFiniteLocallyFree_iff _).mp
    (Scheme.Modules.IsFiniteLocallyFree.of_iso
      (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f ≪≫
        Stacks.Immersion.conormalSheafSelfIso (pullback.diagonal f).liftCoborder)
      ((Scheme.Modules.isFiniteLocallyFree_iff _).mpr
        (Scheme.Hom.isFiniteLocallyFree_relativeDifferentials f)))

/-- **The conormal sheaf of the diagonal of a smooth morphism of relative dimension `d` is finite
locally free of rank `d`.** It is `Ω_{Y/Z}` by Stacks 08S2. -/
theorem isFiniteLocallyFreeOfRank_immersionConormalSheaf_diagonal [Smooth f] {d : ℕ}
    (hd : RelativeDimension f d) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (immersionConormalSheaf (pullback.diagonal f)) d :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (Stacks.Tag08S2Assembly.relativeDifferentialsIsoDiagonalConormal f)
    (Scheme.Hom.isFiniteLocallyFreeOfRank_relativeDifferentials_of_relativeDimension f hd)

/-- **The conormal sheaf of the closed factor of the diagonal of a smooth morphism of relative
dimension `d` is finite locally free of rank `d`.** It is the conormal sheaf of the diagonal. -/
theorem isFiniteLocallyFreeOfRank_immersionConormalSheaf_liftCoborder_diagonal [Smooth f]
    {d : ℕ} (hd : RelativeDimension f d) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (immersionConormalSheaf (pullback.diagonal f).liftCoborder) d :=
  AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
    (Stacks.Immersion.conormalSheafSelfIso (pullback.diagonal f).liftCoborder)
    (isFiniteLocallyFreeOfRank_immersionConormalSheaf_diagonal f hd)

/-! ### The normal bundle of the diagonal -/

/-- **The normal bundle of the diagonal of a smooth morphism**, as a virtual normal bundle for the
closed immersion `Δ' : Y ⟶ U` through which the diagonal factors into the open neighbourhood
`U = (pullback.diagonal f).coborderRange` of its image: the dual of the conormal sheaf of `Δ'`,
with the inverse of the reflexivity isomorphism as structural surjection. -/
noncomputable def diagonalVirtualNormalBundle [Smooth f] :
    VirtualNormalBundle (pullback.diagonal f).liftCoborder :=
  VirtualNormalBundle.ofIsFiniteLocallyFree _
    (isFiniteLocallyFree_immersionConormalSheaf_liftCoborder_diagonal f)

/-- The underlying module of the normal bundle of the diagonal is the dual of the conormal sheaf
of the closed factor `Δ'` of the diagonal. -/
@[simp]
theorem diagonalVirtualNormalBundle_bundle [Smooth f] :
    (diagonalVirtualNormalBundle f).bundle =
      dualSheaf (immersionConormalSheaf (pullback.diagonal f).liftCoborder) :=
  rfl

/-- The structural surjection of the normal bundle of the diagonal is an isomorphism. -/
instance isIso_diagonalVirtualNormalBundle_surjection [Smooth f] :
    IsIso (diagonalVirtualNormalBundle f).surjection :=
  VirtualNormalBundle.isIso_ofIsFiniteLocallyFree_surjection _ _

/-- **Stacks Project, Section 42.60 (Tag 0FBR), the degree.** For `f` smooth of constant relative
dimension `d`, the normal bundle of the diagonal is finite locally free of rank `d`; this is why
the Gysin class `Δ^!` lies in `A^d(Y ⟶ Y ×_Z Y)`. -/
@[stacks 0FBR "constant relative dimension d: the normal bundle of the diagonal has rank d"]
theorem isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle [Smooth f] {d : ℕ}
    (hd : RelativeDimension f d) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (diagonalVirtualNormalBundle f).bundle d :=
  isFiniteLocallyFreeOfRank_dualSheaf _ d
    (hE := isFiniteLocallyFreeOfRank_immersionConormalSheaf_liftCoborder_diagonal f hd)

/-- The normal bundle of the diagonal of a morphism smooth of relative dimension `d`, in the sense
of `AlgebraicGeometry.SmoothOfRelativeDimension`, is finite locally free of rank `d`. -/
instance isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle_of_smoothOfRelativeDimension
    [Smooth f] (d : ℕ) [SmoothOfRelativeDimension d f] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (diagonalVirtualNormalBundle f).bundle d :=
  isFiniteLocallyFreeOfRank_diagonalVirtualNormalBundle f
    (SmoothOfRelativeDimension.relativeDimension d f)

end Stacks.Chow

end
