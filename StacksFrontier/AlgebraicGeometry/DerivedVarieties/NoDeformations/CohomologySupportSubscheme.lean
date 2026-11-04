module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.DerivedStalkHomology
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.SubschemeStalkFlat
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.SchemeTheoreticStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.ZeroDimensionalTestModules
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# The closed subscheme carried by the zeroth cohomology sheaf of a perfect complex

Let `W` be a locally Noetherian scheme and let `K` be a perfect object of `D(𝒪_W)`. Its zeroth
cohomology sheaf is coherent (`AlgebraicGeometry.isCoherent_homology_of_isPerfect'`), so it has
a scheme-theoretic support: a closed subscheme of `W` whose ideal sheaf is, on each affine open,
the annihilator of the sections there. This file collects what that subscheme is and does.

It is the subscheme `Z` that the proof of [Stacks, Tag 0G0R] builds. The source builds it by
gluing: at each closed point `z` of the fibre `Y_s ×_k Y_s` it produces an affine open `U(z)` and
a closed subscheme `Z(z) ⊆ U(z)` with `K|_{U(z)}` quasi-isomorphic to `𝒪_{Z(z)}`, and then
remarks that the pieces agree on overlaps. Taking the scheme-theoretic support of `H^0(K)`
instead makes the subscheme global from the start — an annihilator is canonical, so there is
nothing to glue — and the source's four local properties become statements about the stalks of
its ideal sheaf, which is what the rest of the argument consumes.

## Main definitions

* `AlgebraicGeometry.cohomologySupportIdeal`: the ideal sheaf of the scheme-theoretic support of
  `H^0(K)`, for `K` perfect.

## Main results

* `AlgebraicGeometry.stalk_cohomologySupportIdeal`: the ideal it induces in the local ring at `z`
  is the annihilator of the stalk of `H^0(K)` there.
* `AlgebraicGeometry.stalk_cohomologySupportIdeal_of_derivedStalk_iso_single`: when the derived
  stalk of `K` at `z` is `𝒪_{W,z} ⧸ I` in degree zero, that ideal is `I`. This is the form in
  which the Koszul description of [Stacks, Tag 0G0N] determines `Z` near a point of the diagonal.
* `AlgebraicGeometry.notMem_support_cohomologySupportIdeal_of_isZero_stalk`: a point at which
  the stalk of `H^0(K)` vanishes does not lie on the subscheme. This is what Case I of
  [Stacks, Tag 0G0R] delivers: `AlgebraicGeometry.exists_mem_forall_isZero_stalkHomology_caseI`
  produces a whole neighbourhood of such points off the diagonal, and they are therefore absent
  from `Z`.
* `AlgebraicGeometry.isFlatAt_subschemeι_comp_of_derivedStalk_iso_single`: with that ideal `I`
  known, `Z ⟶ S` is flat at the point of `Z` over `z` as soon as `𝒪_{W,z} ⧸ I` is flat over the
  local ring of the base. Both inputs are what [Stacks, Tag 0G0N] delivers.

## Implementation notes

*Which coherence is used.* `AlgebraicGeometry.Scheme.Modules.schemeTheoreticSupport` needs its
module quasi-coherent and of finite type. Both come from perfectness of `K`: finite type from
`AlgebraicGeometry.isCoherent_homology_of_isPerfect'`, quasi-coherence from
`AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent`. Neither is an instance, so they
are introduced inside the definition and re-introduced in each statement about it; the
definition therefore takes perfectness of `K` as an explicit argument, and two different proofs
of perfectness give the same ideal sheaf only propositionally — which is why the lemmas below
take the same proof term that the definition was formed with.

*The two spellings of the stalk.* `SheafOfModules.supp` is phrased with the
`AddCommGrpCat`-valued stalk of the underlying presheaf, while the vanishing that Case I
produces is `IsZero` of `SheafOfModules.stalkObj`, a `ModuleCat` over the `RingCat`-valued stalk
of the structure sheaf. The two have the same carrier, so `IsZero` on the second gives
`Subsingleton` of the first and the support criterion applies.

## References

* [Stacks Project, Tag 0G0R](https://stacks.math.columbia.edu/tag/0G0R)
* [Stacks Project, Tag 05JU](https://stacks.math.columbia.edu/tag/05JU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

section Support

variable {W : Scheme.{u}} [IsLocallyNoetherian W]

/-- The zeroth cohomology sheaf of a perfect object is of finite type. -/
theorem isFiniteType_zeroHomology_of_isPerfect (K : DerivedCategory W.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) K) :
    ((DerivedCategory.homologyFunctor W.Modules 0).obj K).IsFiniteType :=
  (isCoherent_homology_of_isPerfect' W K hK 0).isFiniteType

omit [IsLocallyNoetherian W] in
/-- The zeroth cohomology sheaf of a perfect object is quasi-coherent. -/
theorem isQuasicoherent_zeroHomology_of_isPerfect (K : DerivedCategory W.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) K) :
    ((DerivedCategory.homologyFunctor W.Modules 0).obj K).IsQuasicoherent :=
  have hK' : RingedSpace.IsPerfect (X := W.toRingedSpace) K := hK
  isQuasicoherentDerived_of_isPseudoCoherent W K hK'.isPseudoCoherent 0

/-- **The ideal sheaf of the scheme-theoretic support of `H^0(K)`**, for `K` a perfect object of
`D(𝒪_W)` on a locally Noetherian scheme. The closed subscheme it cuts out is the `Z` of
[Stacks, Tag 0G0R]. -/
def cohomologySupportIdeal (K : DerivedCategory W.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) K) :
    W.IdealSheafData :=
  haveI := isFiniteType_zeroHomology_of_isPerfect K hK
  haveI := isQuasicoherent_zeroHomology_of_isPerfect K hK
  Scheme.Modules.schemeTheoreticSupport ((DerivedCategory.homologyFunctor W.Modules 0).obj K)

/-- **The ideal cut out in a local ring by the subscheme of [Stacks, Tag 0G0R]** is the
annihilator of the stalk of `H^0(K)` there. -/
theorem stalk_cohomologySupportIdeal (K : DerivedCategory W.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) K) (z : W) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule
      ((DerivedCategory.homologyFunctor W.Modules 0).obj K) z
    IdealSheafData.stalk (cohomologySupportIdeal K hK) z =
      Module.annihilator (W.presheaf.stalk z)
        (((DerivedCategory.homologyFunctor W.Modules 0).obj K).presheaf.stalk z) :=
  have := isFiniteType_zeroHomology_of_isPerfect K hK
  have := isQuasicoherent_zeroHomology_of_isPerfect K hK
  Scheme.Modules.stalk_schemeTheoreticSupport
    ((DerivedCategory.homologyFunctor W.Modules 0).obj K) z

omit [IsLocallyNoetherian W] in
/-- A point at which the stalk of a quasi-coherent module of finite type vanishes does not lie
on the scheme-theoretic support of that module. -/
theorem notMem_support_schemeTheoreticSupport_of_isZero_stalkObj (F : W.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] (z : W)
    (h : IsZero (SheafOfModules.stalkObj W.ringCatSheaf z F)) :
    z ∉ (Scheme.Modules.schemeTheoreticSupport F).support := by
  have hsub : Subsingleton
      ((show TopCat.Presheaf AddCommGrpCat.{u} W.toTopCat from F.val.presheaf).stalk z) :=
    ModuleCat.isZero_iff_subsingleton.mp h
  intro hz
  obtain ⟨a, ha⟩ : z ∈ SheafOfModules.supp F := by
    rwa [Scheme.Modules.supp_eq_support_schemeTheoreticSupport F]
  exact ha (Subsingleton.elim a 0)

/-- **A point at which the stalk of `H^0(K)` vanishes is not on the subscheme `Z`.** This is the
conclusion of Case I of [Stacks, Tag 0G0R]: off the diagonal the kernel vanishes on a whole
neighbourhood, so none of those points lies on `Z`. -/
theorem notMem_support_cohomologySupportIdeal_of_isZero_stalk (K : DerivedCategory W.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) K) (z : W)
    (h : IsZero (SheafOfModules.stalkObj W.ringCatSheaf z
      ((DerivedCategory.homologyFunctor W.Modules 0).obj K))) :
    z ∉ (cohomologySupportIdeal K hK).support :=
  have := isFiniteType_zeroHomology_of_isPerfect K hK
  have := isQuasicoherent_zeroHomology_of_isPerfect K hK
  notMem_support_schemeTheoreticSupport_of_isZero_stalkObj
    ((DerivedCategory.homologyFunctor W.Modules 0).obj K) z h

/-- **The ideal `Z` cuts out in the local ring at `z`, when the derived stalk of `K` there is a
cyclic module.** If `K_z` is `𝒪_{W,z} ⧸ I` placed in degree zero — the shape the Koszul
description of [Stacks, Tag 0G0N] produces, with `I` the ideal generated by the lifted regular
sequence — then the stalk of the ideal sheaf of `Z` at `z` is `I`. -/
theorem stalk_cohomologySupportIdeal_of_derivedStalk_iso_single (K : DerivedCategory W.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) K) (z : W)
    (I : Ideal (W.presheaf.stalk z))
    (e : (derivedStalkFunctor z).obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u} (W.presheaf.stalk z)) 0).obj
        (ModuleCat.of (W.presheaf.stalk z) (W.presheaf.stalk z ⧸ I))) :
    IdealSheafData.stalk (cohomologySupportIdeal K hK) z = I := by
  rw [stalk_cohomologySupportIdeal K hK z]
  have h := annihilator_modulesStalk_zeroHomology_of_derivedStalk_iso_single z K
    (ModuleCat.of (W.presheaf.stalk z) (W.presheaf.stalk z ⧸ I)) e
  rwa [Ideal.annihilator_quotient] at h

end Support

section Flat

variable {W S : Scheme.{u}} [IsLocallyNoetherian W]

/-- **The subscheme `Z` of [Stacks, Tag 0G0R] is flat over the base at a point of the diagonal.**
If at a point `z` of `W` the derived stalk of `K` is `𝒪_{W,z} ⧸ I` in degree zero and that
quotient is flat over `𝒪_{S, p z}`, then `Z ⟶ S` is flat at the point of `Z` over `z`.

Both hypotheses are what [Stacks, Tag 0G0N] produces at a point of the diagonal, with
`I = (f_1, …, f_r)` the ideal of the lifted regular sequence. -/
theorem isFlatAt_subschemeι_comp_of_derivedStalk_iso_single (p : W ⟶ S)
    (K : DerivedCategory W.Modules)
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := W.toRingedSpace) K)
    (ζ : (cohomologySupportIdeal K hK).subscheme)
    (I : Ideal (W.presheaf.stalk ((cohomologySupportIdeal K hK).subschemeι ζ)))
    (e : (derivedStalkFunctor ((cohomologySupportIdeal K hK).subschemeι ζ)).obj K ≅
      (DerivedCategory.singleFunctor (ModuleCat.{u}
          (W.presheaf.stalk ((cohomologySupportIdeal K hK).subschemeι ζ))) 0).obj
        (ModuleCat.of (W.presheaf.stalk ((cohomologySupportIdeal K hK).subschemeι ζ))
          (W.presheaf.stalk ((cohomologySupportIdeal K hK).subschemeι ζ) ⧸ I)))
    (hflat : RingHom.Flat ((Ideal.Quotient.mk I).comp
      (p.stalkMap ((cohomologySupportIdeal K hK).subschemeι ζ)).hom)) :
    AlgebraicGeometry.IsFlatAt
      ((cohomologySupportIdeal K hK).subschemeι ≫ p).toLRSHom.toShHom ζ := by
  rwa [IdealSheafData.isFlatAt_subschemeι_comp_iff,
    stalk_cohomologySupportIdeal_of_derivedStalk_iso_single K hK _ I e]

end Flat

end AlgebraicGeometry

end
