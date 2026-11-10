/-
Copyright (c) 2026 Stacks Project Lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniGenericMember
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.BaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuotClosedSubschemeFlat
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapStructureSheaf

/-!
# The closed subscheme cut out by a member of `Quot_{OO/Pn/Z}(T)` is stable under base change

`AlgebraicGeometry.ProjectiveQuot.subschemeOfFamily` is the closed subscheme of `Pn_T` cut out by
a submodule `K` of `OO^{+1}` on `Pn_T` whose quotient is of finite presentation (Stacks 01QQ,
through `AlgebraicGeometry.ProjectiveQuot.idealOfFamily`). This file proves that it commutes with
base change: for `g : T' -> T` the closed subscheme cut out by
`AlgebraicGeometry.ProjectiveQuot.baseChange g K` sits in a cartesian square over `g` with the
one cut out by `K`.

This is the shape `AlgebraicGeometry.PolarizedFamily.Hom.cartesian` consumes, and it is the
base-change half of the mapping property of the universal family of `Hilb^P_{Pn_Z/Z}` -- the
hypothesis `huniv` of
`AlgebraicGeometry.noetherianSpace_of_isHilbertPolarizedPoint_of_universalFamily` (Stacks 0E96);
see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Quot/PolarizedHilbertUniversalFamily.lean`.

The two steps are the ones the source's dictionary suggests.

* **`AlgebraicGeometry.ProjectiveQuot.idealOfFamily` commutes with inverse image.** The sheaf of
  ideals of `baseChange g K` is the inverse image along `Pn_{T'} -> Pn_T` of the sheaf of ideals
  of `K`, i.e. `AlgebraicGeometry.Scheme.IdealSheafData.comap` of it. This is
  `AlgebraicGeometry.ProjectiveQuot.idealSheafDataOfFamily_baseChange`, and the route to it is
  *not* a comparison of the two quotient maps out of `OO_{Pn_{T'}}`: it is enough that the two
  quotient *modules* are isomorphic, because an ideal sheaf is recovered from its quotient as an
  annihilator (`Stacks.IdealSheaf.eq_of_pushforwardUnit_iso` below). The isomorphism is a chain
  of four identifications already in the library, listed in
  `AlgebraicGeometry.ProjectiveQuot.pushforwardUnitIdealSheafDataOfFamilyBaseChangeIso`.
* **the closed subscheme of a pulled-back sheaf of ideals is the pullback of the closed
  subscheme.** This is `Stacks.Bertini.isPullback_subschemeι_comap`, and pasting it onto
  `AlgebraicGeometry.isPullback_projectiveSpaceOverMap` gives the square over `g`.

## Main results

* `Stacks.IdealSheaf.ideal_le_of_pushforwardUnit_hom`: if the structure sheaf of the closed
  subscheme of `I`, pushed forward, maps onto the one of `J`, then `I.ideal <= J.ideal`.
* `Stacks.IdealSheaf.eq_of_pushforwardUnit_iso`: **two sheaves of ideals whose quotients of the
  structure sheaf are isomorphic as modules are equal.** No compatibility of the quotient maps is
  assumed.
* `AlgebraicGeometry.ProjectiveQuot.idealSheafDataOfFamily_baseChange`: **the sheaf of ideals of
  the base change is the inverse image of the sheaf of ideals.**
* `AlgebraicGeometry.ProjectiveQuot.isPullback_subschemeOfFamily_baseChange`: **the closed
  subscheme cut out by the base change of a member of `Quot_{OO/Pn/Z}(T)` is the fibre product
  over `g` of the one cut out by the member.**

## Implementation notes

**Why an annihilator, and not a comparison of quotient maps.** The sheaf of ideals of
`baseChange g K` is the kernel of `OO_{Pn_{T'}} -> g^*(OO^{+1}/K)`, and the sheaf of ideals
`AlgebraicGeometry.Scheme.IdealSheafData.comap` produces is the kernel of
`OO_{Pn_{T'}} -> j_* OO_W` for the pulled-back closed immersion `j`; equality of the two kernels
would ordinarily need the isomorphism of the two targets to carry the one map to the other, and
that compatibility -- the inverse image of `Stacks.ClosedSubscheme.structureSheafProjection`
against `Stacks.IdealSheaf.comapStructureSheafIso` -- is not in the library. It is not needed.
Over an affine open `U` the sections of `i_* OO_Z` are `Gamma(X, U)` modulo `I.ideal U` acted on
through `i.app U`, and the annihilator of that module is `I.ideal U`, because the module has the
unit section: so `I.ideal U` is read off the module structure alone and any module isomorphism of
the two quotients forces `I = J`. Only two computations are needed, both definitional: the
sections of `(pushforward i).obj (unitModule Z)` over `U` are the sections of `OO_Z` over
`i^{-1}U`, and the action of `x` on them is multiplication by `i.app U x`.

The annihilator that appears is the one `AlgebraicGeometry.Scheme.Modules.annihilatorIdeal`
takes over the affine opens, and the content of `Stacks.IdealSheaf.eq_of_pushforwardUnit_iso`
could equally be read as the pair of statements that the annihilator ideal sheaf of `𝒪_X / I` is
`I` and that it is invariant under isomorphism; neither of those is in the library, and the
direct form is what the consumer here needs.

`Stacks.CartierQuotientChart.ideal_eq_of_spec_quotient_iso` is the affine statement of the same
uniqueness, but it takes the isomorphism *over* `Spec R`; the lemma here takes no compatibility
at all, which is exactly what makes it applicable to a chain of isomorphisms assembled from
cokernel comparisons and a base-change isomorphism.

**The hypothesis of `AlgebraicGeometry.ProjectiveQuot.subschemeOfFamily` is finite presentation
of the quotient**, not membership in `AlgebraicGeometry.ProjectiveQuot.families`, so the
statements below take that hypothesis; the membership forms, which is what a consumer of
`Quot^P` has, are the corollaries with `_of_mem`.

## References

* [Stacks Project, Tag 01QQ](https://stacks.math.columbia.edu/tag/01QQ)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 09TR](https://stacks.math.columbia.edu/tag/09TR)
* [Stacks Project, Tag 0E96](https://stacks.math.columbia.edu/tag/0E96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace Stacks.IdealSheaf

variable {X : Scheme.{u}}

/-- **The action of `Gamma(X, U)` on the sections of `i_* 𝒪_Z` is multiplication through
`i.app U`.** Both the carrier of the sections of the direct image over `U` and the action are
those of `𝒪_Z` over `i ⁻¹ᵁ U` restricted along `i.app U`, so this is definitional; it is the one
computation the annihilator argument of
`Stacks.IdealSheaf.eq_of_pushforwardUnit_iso` needs. -/
theorem smul_pushforwardUnit (I : X.IdealSheafData) (U : X.Opens) (x : Γ(X, U))
    (s : Γ((Scheme.Modules.pushforward I.subschemeι).obj
      (Scheme.unitModule I.subscheme), U)) :
    x • s = (show Γ((Scheme.Modules.pushforward I.subschemeι).obj
        (Scheme.unitModule I.subscheme), U) from
      I.subschemeι.app U x * (show Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U) from s)) :=
  rfl

/-- **A morphism of direct images of structure sheaves which is surjective on the sections over
an affine open compares the two sheaves of ideals there.** A section of `I.ideal U` kills every
section of `i_* 𝒪_{Z}` over `U`, hence -- the morphism being `Gamma(X, U)`-linear and onto -- every
section of `j_* 𝒪_{W}`, and in particular the unit section, whose annihilator is `J.ideal U`. -/
theorem ideal_le_of_pushforwardUnit_hom {I J : X.IdealSheafData}
    (φ : (Scheme.Modules.pushforward I.subschemeι).obj (Scheme.unitModule I.subscheme) ⟶
      (Scheme.Modules.pushforward J.subschemeι).obj (Scheme.unitModule J.subscheme))
    (U : X.affineOpens) (hφ : Function.Surjective (φ.app U.1)) :
    I.ideal U ≤ J.ideal U := by
  intro x hx
  have hx0 : I.subschemeι.app U.1 x = 0 := by
    rw [← RingHom.mem_ker, Scheme.IdealSheafData.ker_subschemeι_app]
    exact hx
  have hkill : ∀ s, x • s = (0 : Γ((Scheme.Modules.pushforward I.subschemeι).obj
      (Scheme.unitModule I.subscheme), U.1)) := by
    intro s
    rw [smul_pushforwardUnit I U.1 x s, hx0]
    show (show Γ((Scheme.Modules.pushforward I.subschemeι).obj
        (Scheme.unitModule I.subscheme), U.1) from
      (0 : Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1)) *
        (show Γ(I.subscheme, I.subschemeι ⁻¹ᵁ U.1) from s)) = 0
    rw [zero_mul]
    rfl
  obtain ⟨s₀, hs₀⟩ := hφ (show Γ((Scheme.Modules.pushforward J.subschemeι).obj
    (Scheme.unitModule J.subscheme), U.1) from
      (1 : Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U.1)))
  have hlin : φ.app U.1 (x • s₀) = x • φ.app U.1 s₀ :=
    (φ.val.app (op U.1)).hom.map_smul x s₀
  have hone : x • (show Γ((Scheme.Modules.pushforward J.subschemeι).obj
      (Scheme.unitModule J.subscheme), U.1) from
        (1 : Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U.1))) = 0 := by
    rw [← hs₀, ← hlin, hkill s₀, map_zero]
  rw [smul_pushforwardUnit J U.1 x _] at hone
  rw [← Scheme.IdealSheafData.ker_subschemeι_app, RingHom.mem_ker]
  have hmul : J.subschemeι.app U.1 x * (1 : Γ(J.subscheme, J.subschemeι ⁻¹ᵁ U.1)) = 0 := hone
  rwa [mul_one] at hmul

/-- **Two sheaves of ideals whose quotients of the structure sheaf are isomorphic as modules are
equal.** The quotient of `𝒪_X` by a sheaf of ideals `I` is the direct image of the structure
sheaf of the closed subscheme `I` cuts out, and over an affine open `U` the annihilator of its
sections is `I.ideal U`; so an isomorphism of the two quotients, with no compatibility with the
quotient maps assumed, gives both inclusions through
`Stacks.IdealSheaf.ideal_le_of_pushforwardUnit_hom`. -/
theorem eq_of_pushforwardUnit_iso {I J : X.IdealSheafData}
    (e : (Scheme.Modules.pushforward I.subschemeι).obj (Scheme.unitModule I.subscheme) ≅
      (Scheme.Modules.pushforward J.subschemeι).obj (Scheme.unitModule J.subscheme)) :
    I = J := by
  have key : ∀ {I J : X.IdealSheafData}
      (e : (Scheme.Modules.pushforward I.subschemeι).obj (Scheme.unitModule I.subscheme) ≅
        (Scheme.Modules.pushforward J.subschemeι).obj (Scheme.unitModule J.subscheme))
      (U : X.affineOpens), I.ideal U ≤ J.ideal U := by
    intro I J e U
    refine ideal_le_of_pushforwardUnit_hom e.hom U fun t => ⟨e.inv.app U.1 t, ?_⟩
    exact congrArg (fun φ => AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app φ U.1) t) e.inv_hom_id
  exact Scheme.IdealSheafData.ext (funext fun U => le_antisymm (key e U) (key e.symm U))

end Stacks.IdealSheaf

namespace AlgebraicGeometry.ProjectiveQuot

variable {n : ℕ} {T T' : Scheme.{u}}

/-- **The quotient of `𝒪_{ℙⁿ_{T'}}` by the sheaf of ideals of `baseChange g K` is the quotient
by the inverse image of the sheaf of ideals of `K`.** Four identifications already in the
library: the quotient of the structure sheaf by the sheaf of ideals of a member is the direct
image of the structure sheaf of the subscheme it cuts out
(`AlgebraicGeometry.ProjectiveQuot.pushforwardUnitSubschemeOfFamilyIso`); the quotient of the
base change is the inverse image of the quotient
(`AlgebraicGeometry.ProjectiveQuot.quotientBaseChangeIso`); the inverse image of the first
identification; and affine base change for the direct image of the structure sheaf of a closed
subscheme (Stacks 02KG, `Stacks.IdealSheaf.comapStructureSheafIso`). -/
def pushforwardUnitIdealSheafDataOfFamilyBaseChangeIso (g : T' ⟶ T)
    {K : Subobject (freeModule n 1 T)} (hK : (quotient K).IsFinitePresentation)
    (hK' : (quotient (baseChange g K)).IsFinitePresentation) :
    (Scheme.Modules.pushforward (idealSheafDataOfFamily (baseChange g K) hK').subschemeι).obj
        (Scheme.unitModule (idealSheafDataOfFamily (baseChange g K) hK').subscheme) ≅
      (Scheme.Modules.pushforward
          (((idealSheafDataOfFamily K hK).comap (projectiveSpaceOverMap n g)).subschemeι)).obj
        (Scheme.unitModule
          ((idealSheafDataOfFamily K hK).comap (projectiveSpaceOverMap n g)).subscheme) :=
  pushforwardUnitSubschemeOfFamilyIso (baseChange g K) hK' ≪≫
    quotientBaseChangeIso g K ≪≫
      (Scheme.Modules.pullback (projectiveSpaceOverMap n g)).mapIso
          (pushforwardUnitSubschemeOfFamilyIso K hK).symm ≪≫
        Stacks.IdealSheaf.comapStructureSheafIso (projectiveSpaceOverMap n g)
          (idealSheafDataOfFamily K hK)

/-- **`AlgebraicGeometry.ProjectiveQuot.idealOfFamily` commutes with inverse image**: the sheaf
of ideals of `ℙⁿ_{T'}` cut out by `baseChange g K` is the inverse image along
`AlgebraicGeometry.projectiveSpaceOverMap` of the one cut out by `K`. The two quotients of the
structure sheaf are isomorphic
(`AlgebraicGeometry.ProjectiveQuot.pushforwardUnitIdealSheafDataOfFamilyBaseChangeIso`) and a
sheaf of ideals is determined by its quotient
(`Stacks.IdealSheaf.eq_of_pushforwardUnit_iso`). -/
theorem idealSheafDataOfFamily_baseChange (g : T' ⟶ T) {K : Subobject (freeModule n 1 T)}
    (hK : (quotient K).IsFinitePresentation)
    (hK' : (quotient (baseChange g K)).IsFinitePresentation) :
    idealSheafDataOfFamily (baseChange g K) hK' =
      (idealSheafDataOfFamily K hK).comap (projectiveSpaceOverMap n g) :=
  Stacks.IdealSheaf.eq_of_pushforwardUnit_iso
    (pushforwardUnitIdealSheafDataOfFamilyBaseChangeIso g hK hK')

/-- **The closed subscheme cut out by the base change of a submodule of `𝒪^{⊕ 1}` is the fibre
product of the one cut out by the submodule.** The sheaf of ideals of the base change is the
inverse image of the sheaf of ideals
(`AlgebraicGeometry.ProjectiveQuot.idealSheafDataOfFamily_baseChange`), the closed subscheme of
an inverse image of a sheaf of ideals is the fibre product of the closed subscheme
(`Stacks.Bertini.isPullback_subschemeι_comap`), and projective space is stable under base change
(`AlgebraicGeometry.isPullback_projectiveSpaceOverMap`); the two cartesian squares paste. -/
theorem isPullback_subschemeOfFamily_baseChange (g : T' ⟶ T)
    {K : Subobject (freeModule n 1 T)} (hK : (quotient K).IsFinitePresentation)
    (hK' : (quotient (baseChange g K)).IsFinitePresentation) :
    ∃ w : subschemeOfFamily (baseChange g K) hK' ⟶ subschemeOfFamily K hK,
      IsPullback w
        (subschemeOfFamilyι (baseChange g K) hK' ≫ (projectiveSpaceOver n T' ↘ T'))
        (subschemeOfFamilyι K hK ≫ (projectiveSpaceOver n T ↘ T)) g := by
  change ∃ w : (idealSheafDataOfFamily (baseChange g K) hK').subscheme ⟶
      (idealSheafDataOfFamily K hK).subscheme,
    IsPullback w
      ((idealSheafDataOfFamily (baseChange g K) hK').subschemeι ≫
        (projectiveSpaceOver n T' ↘ T'))
      ((idealSheafDataOfFamily K hK).subschemeι ≫ (projectiveSpaceOver n T ↘ T)) g
  rw [idealSheafDataOfFamily_baseChange g hK hK']
  exact ⟨_, (Stacks.Bertini.isPullback_subschemeι_comap (idealSheafDataOfFamily K hK)
    (projectiveSpaceOverMap n g)).flip.paste_vert (isPullback_projectiveSpaceOverMap n g)⟩

/-- **The closed subscheme cut out by the base change of a member of `Quot_{𝒪/ℙⁿ/ℤ}(T)` is the
fibre product over `g` of the one cut out by the member.** This is
`AlgebraicGeometry.ProjectiveQuot.isPullback_subschemeOfFamily_baseChange` at the finite
presentation clause of membership; it is the shape
`AlgebraicGeometry.PolarizedFamily.Hom.cartesian` consumes. -/
theorem isPullback_subschemeOfFamily_baseChange_of_mem (g : T' ⟶ T)
    {K : Subobject (freeModule n 1 T)} (hK : K ∈ families n 1 T)
    (hK' : baseChange g K ∈ families n 1 T') :
    ∃ w : subschemeOfFamily (baseChange g K) hK'.1 ⟶ subschemeOfFamily K hK.1,
      IsPullback w
        (subschemeOfFamilyι (baseChange g K) hK'.1 ≫ (projectiveSpaceOver n T' ↘ T'))
        (subschemeOfFamilyι K hK.1 ≫ (projectiveSpaceOver n T ↘ T)) g :=
  isPullback_subschemeOfFamily_baseChange g hK.1 hK'.1

end AlgebraicGeometry.ProjectiveQuot

end
