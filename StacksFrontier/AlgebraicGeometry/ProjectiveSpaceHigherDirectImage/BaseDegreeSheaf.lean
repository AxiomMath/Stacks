module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistTensorPow
public import StacksFrontier.AlgebraicGeometry.Descent.EffectiveEpi.QuasicoherentSections
public import StacksFrontier.AlgebraicGeometry.Descent.PullbackSectionsSheaf.UnitComparison
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.Twist
public import StacksFrontier.AlgebraicGeometry.RelativeProjTwists.DegreeSection

/-!
# The degree-`d` part of `𝒪_S[T₀, …, Tₙ]` and its map into `f_* 𝒪(d)`

Let `S` be a scheme, let `n` be a natural number, let `d` be an integer and let
`f : ℙⁿ_S ⟶ S` be the structure morphism of projective `n`-space over `S`. The degree-zero row
of the display of [Stacks, Tag 01XW] reads

`f_* 𝒪(d) = (𝒪_S[T₀, …, Tₙ])_d`,

and the degree-`n` row is the `𝒪_S`-dual of `(𝒪_S[T₀, …, Tₙ])_{-n-1-d}`. This file supplies the
two objects both rows are stated about: the sheaf `(𝒪_S[T₀, …, Tₙ])_d` on the base, and the
canonical morphism of `𝒪_S`-modules

`(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)`

that those rows assert is an isomorphism.

The degree-`d` part of a polynomial algebra is free on the monomials of total degree `d`, so the
sheaf is the free `𝒪_S`-module on the degree-`d` multidegrees — a set that is empty for `d < 0`
and finite of cardinality `(n + d choose n)` for `d ≥ 0`. The morphism is the one that sends the
basis vector of a degree-`d` monomial `T^e` to the global section of `𝒪(d)` that `T^e` defines:
`𝒪(d)` on `ℙⁿ_S` is by definition the pullback of the degree-`d` twist of the integral model
`ℙⁿ_ℤ = Proj ℤ[T₀, …, Tₙ]`, where a homogeneous element of degree `d` *is* a global section of
the degree-`d` twist.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `MonomialIndex`: the degree-`d` multidegrees in `n + 1` variables, indexing the monomials of
  total degree `d`.
* `baseDegreeSheaf`: **the sheaf `(𝒪_S[T₀, …, Tₙ])_d` on `S`**, the free `𝒪_S`-module on
  `MonomialIndex n d`.
* `monomialSectionAtUniverse`: `T^e` as a global section of `𝒪(d)` on `ℙⁿ_ℤ`.
* `twistOverSection`: `T^e` as a global section of `𝒪(d)` on `ℙⁿ_S`.
* `toPushforwardTwistOver`: **the canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)`.**

## Main results

* `isEmpty_monomialIndex` and `isZero_baseDegreeSheaf_of_neg`: there is no monomial of negative
  degree, so `baseDegreeSheaf n S d` is the zero sheaf for `d < 0`.
* `MonomialIndex.natEquiv` and `baseDegreeSheafNatIso`: at a nonnegative degree the index set is
  the one `Stacks.SheafOfModules.symmetricPowerFreeIsoAnyIndex` identifies with the degree-`d`
  symmetric power of a free sheaf, which is the reading
  `(𝒪_S[T₀, …, Tₙ])_d = Sym^d(𝒪_S^{n+1})` of the sheaf above.
* `freeHomEquiv_toPushforwardTwistOver`: **the morphism sends the basis vector of `T^e` to the
  global section `T^e` of `𝒪(d)`**, which is what pins it down as *the* canonical morphism
  rather than some morphism.

## Implementation notes

**The index type is `ULift`ed.** A free sheaf of modules over a sheaf of rings in `RingCat.{u}`
is free on a `Type u`, while the multidegrees of `n + 1` variables form a `Type 0`; the variables
are therefore taken to be `ULift.{u} (Fin (n + 1))` and relabelled to `Fin (n + 1)` by
`Equiv.ulift` where a polynomial is needed. Taking the variables rather than the whole index set
to be the `ULift` is what makes `MonomialIndex.natEquiv` available: the index set
`Stacks.SheafOfModules.symmetricPowerFreeIsoAnyIndex` produces is literally the degree-`d`
multidegrees of a `Type u` of variables.

**The degree is an integer but a monomial has a natural-number degree.** A member of
`MonomialIndex n d` carries the equation `(e.degree : ℤ) = d` with `e.degree : ℕ`, and
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection` produces a section of the twist in
the natural-number degree `e.degree`. The two are matched by transporting along that equation
with `CategoryTheory.eqToHom`, read on sections over `⊤`. No case distinction on the sign of `d`
is needed: for `d < 0` the index type is empty and nothing has to be produced.

**The morphism is defined globally, on all of `S`.** Both rows of the display are statements
that a morphism of sheaves on `S` is invertible, and invertibility is local: once the morphism
exists on `S` it suffices to invert it over the affine opens of a basis. A family of
isomorphisms over the affine opens with no global morphism underneath them cannot be assembled
that way, which is why
`StacksFrontier/AlgebraicGeometry/ProjectiveSpaceHigherDirectImage/DegreeZero.lean` can only do
the twist `d = 0`, where the morphism being inverted is `f^♯` and so already global.

**What is not proved here.** Nothing is claimed about `toPushforwardTwistOver` being an
isomorphism, and no `stacks` attribute is attached: the degree-zero row of [Stacks, Tag 01XW] is
the assertion that it is one, and that assertion needs the surjectivity of the degree-`d`
section map over a general ring together with the compatibility of [Stacks, Tag 01XV] with base
change at the level of sheaf cohomology. The vanishing row of the tag is carried by
`StacksFrontier/AlgebraicGeometry/ProjectiveSpaceHigherDirectImage/MiddleVanishing.lean` and the
degree-zero row at `d = 0` by `StacksFrontier/AlgebraicGeometry/ProjectiveSpaceHigherDirectImage/DegreeZero.lean`.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
* [Stacks Project, Tag 01MP](https://stacks.math.columbia.edu/tag/01MP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistSections
open Stacks.AlgebraicGeometry.ProjTwistTensorPow

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local implicit_reducible] AlgebraicGeometry.projectiveSpaceAtUniverse
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose

/-! ### The degree-`d` monomials in `n + 1` variables -/

/-- The multidegrees of total degree `d` in `n + 1` variables, indexing the monomials of total
degree `d` in the homogeneous coordinate ring of `ℙⁿ`. The variables are `ULift`ed so that the
index type lies in the universe of the base scheme; it is empty for `d < 0`. -/
abbrev MonomialIndex (n : ℕ) (d : ℤ) : Type u :=
  {e : ULift.{u} (Fin (n + 1)) →₀ ℕ // (e.degree : ℤ) = d}

/-- There is no monomial of negative total degree. -/
theorem isEmpty_monomialIndex (n : ℕ) {d : ℤ} (hd : d < 0) : IsEmpty (MonomialIndex.{u} n d) :=
  ⟨fun e => by have := e.2; omega⟩

/-- Relabelling the variables along `Equiv.ulift` does not change the total degree. -/
theorem degree_equivMapDomain_ulift {n : ℕ} (e : ULift.{u} (Fin (n + 1)) →₀ ℕ) :
    (Finsupp.equivMapDomain (Equiv.ulift : ULift.{u} (Fin (n + 1)) ≃ Fin (n + 1)) e).degree =
      e.degree := by
  rw [Finsupp.equivMapDomain_eq_mapDomain, Finsupp.degree_mapDomain]

/-- At a nonnegative degree, the degree-`d` multidegrees are the index set on which
`Stacks.SheafOfModules.symmetricPowerFreeIsoAnyIndex` exhibits the degree-`d` symmetric power of
a free sheaf of modules as free. -/
def MonomialIndex.natEquiv (n m : ℕ) :
    MonomialIndex.{u} n (m : ℤ) ≃ {e : ULift.{u} (Fin (n + 1)) →₀ ℕ | e.degree = m} :=
  Equiv.subtypeEquivRight fun _ => by exact_mod_cast Iff.rfl

/-- The degree-`d` monomial `T^e` of the homogeneous coordinate ring of `ℙⁿ_ℤ`. -/
def coordMonomial {n : ℕ} {d : ℤ} (e : MonomialIndex.{u} n d) :
    MvPolynomial (Fin (n + 1)) (ULift.{u} ℤ) :=
  MvPolynomial.monomial (Finsupp.equivMapDomain Equiv.ulift e.1) 1

/-- `T^e` is homogeneous of degree the total degree of `e`. -/
theorem coordMonomial_mem {n : ℕ} {d : ℤ} (e : MonomialIndex.{u} n d) :
    coordMonomial e ∈
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ) e.1.degree :=
  MvPolynomial.isHomogeneous_monomial 1 (degree_equivMapDomain_ulift e.1)

/-! ### The monomials as global sections of the twists -/

/-- `T^e` as a global section of `𝒪(d)` on the integral model `ℙⁿ_ℤ` of projective space: a
homogeneous element of degree `d` is a global section of the degree-`d` twist, by
`AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection`. -/
def monomialSectionAtUniverse {n : ℕ} {d : ℤ} (e : MonomialIndex.{u} n d) :
    Γ(projectiveSpaceAtUniverseTwistingSheaf.{u} n d, ⊤) :=
  (eqToHom (congrArg (projectiveSpaceAtUniverseTwistingSheaf.{u} n) e.2)).app ⊤
    (degreeSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) (ULift.{u} ℤ)) e.1.degree
      ⟨coordMonomial e, coordMonomial_mem e⟩)

/-- `T^e` as a global section of `𝒪(d)` on `ℙⁿ_S`: the twist on `ℙⁿ_S` is the pullback of the
twist on the integral model, and a global section pulls back to a global section. -/
def twistOverSection (n : ℕ) (S : Scheme.{u}) (d : ℤ) (e : MonomialIndex.{u} n d) :
    Γ(twistOver n S d, ⊤) :=
  pullbackGlobalSections (projectiveSpaceOver.toIntegralAtUniverse n S)
    (projectiveSpaceAtUniverseTwistingSheaf.{u} n d) (monomialSectionAtUniverse e)

/-! ### The degree-`d` sheaf on the base and the canonical map -/

/-- **The sheaf `(𝒪_S[T₀, …, Tₙ])_d` on `S`**: the degree-`d` part of the polynomial algebra
over `𝒪_S` in `n + 1` variables, which is free on the monomials of total degree `d`. -/
abbrev baseDegreeSheaf (n : ℕ) (S : Scheme.{u}) (d : ℤ) : S.Modules :=
  SheafOfModules.free (R := S.ringCatSheaf) (MonomialIndex.{u} n d)

/-- **At a nonnegative degree `(𝒪_S[T₀, …, Tₙ])_d` is the degree-`d` symmetric power of
`𝒪_S^{n+1}`**, in the sense that it is the free sheaf on the index set that
`Stacks.SheafOfModules.symmetricPowerFreeIsoAnyIndex` identifies with the degree-`d` symmetric
power of the free sheaf on `n + 1` generators. -/
def baseDegreeSheafNatIso (n : ℕ) (S : Scheme.{u}) (m : ℕ) :
    baseDegreeSheaf n S (m : ℤ) ≅ SheafOfModules.free (R := S.ringCatSheaf)
      {e : ULift.{u} (Fin (n + 1)) →₀ ℕ | e.degree = m} :=
  (SheafOfModules.freeFunctor (R := S.ringCatSheaf)).mapIso (MonomialIndex.natEquiv n m).toIso

/-- **`(𝒪_S[T₀, …, Tₙ])_d` is the zero sheaf in a negative degree**, a polynomial algebra having
no homogeneous part in a negative degree. -/
theorem isZero_baseDegreeSheaf_of_neg (n : ℕ) (S : Scheme.{u}) {d : ℤ} (hd : d < 0) :
    IsZero (baseDegreeSheaf n S d) := by
  have : IsEmpty (MonomialIndex.{u} n d) := isEmpty_monomialIndex n hd
  rw [IsZero.iff_id_eq_zero]
  exact Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan _) _ _ fun i => isEmptyElim i

/-- `T^e` as a section of the direct image `f_* 𝒪(d)` on `S`, in the form
`CategoryTheory.SheafOfModules.sections` that a morphism out of a free sheaf is described by. -/
def pushforwardTwistOverSection (n : ℕ) (S : Scheme.{u}) (d : ℤ) (e : MonomialIndex.{u} n d) :
    ((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).obj
      (twistOver n S d)).sections :=
  SheafOfModules.pushforwardSections (projectiveSpaceOver n S ↘ S).toRingCatSheafHom
    (Scheme.Modules.sectionsTopEquiv (twistOver n S d) (twistOverSection n S d e))

/-- The section of `f_* 𝒪(d)` named by `T^e` is, over an open `V` of the base, the restriction of
the global section `T^e` of `𝒪(d)` to the inverse image `f⁻¹V`. -/
theorem pushforwardTwistOverSection_val (n : ℕ) (S : Scheme.{u}) (d : ℤ)
    (e : MonomialIndex.{u} n d) (V : S.Opens) :
    (pushforwardTwistOverSection n S d e).val (op V) =
      (twistOver n S d).presheaf.map
        (homOfLE (le_top : (projectiveSpaceOver n S ↘ S) ⁻¹ᵁ V ≤ ⊤)).op
        (twistOverSection n S d e) := by
  rw [pushforwardTwistOverSection, Scheme.Modules.pushforwardSections_val]
  exact Scheme.Modules.sectionsTopEquiv_val _ _ _

/-- **The canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)`** of `𝒪_S`-modules, for the
structure morphism `f : ℙⁿ_S ⟶ S` over an arbitrary scheme `S`, an arbitrary `n` and an
arbitrary integer `d`: the basis vector of a degree-`d` monomial `T^e` goes to the global
section of `𝒪(d)` that `T^e` defines.

The degree-zero row of the display of [Stacks, Tag 01XW] is the assertion that this is an
isomorphism; it is not proved here. -/
def toPushforwardTwistOver (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    baseDegreeSheaf n S d ⟶
      (Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).obj (twistOver n S d) :=
  (SheafOfModules.freeHomEquiv _).symm (pushforwardTwistOverSection n S d)

/-- **The canonical morphism sends the basis vector of `T^e` to the global section `T^e`.** -/
@[simp] theorem freeHomEquiv_toPushforwardTwistOver (n : ℕ) (S : Scheme.{u}) (d : ℤ) :
    SheafOfModules.freeHomEquiv _ (toPushforwardTwistOver n S d) =
      pushforwardTwistOverSection n S d :=
  Equiv.apply_symm_apply _ _

/-- **The canonical morphism carries the tautological section of the basis vector of `T^e` to the
section of `f_* 𝒪(d)` named by `T^e`.** -/
theorem sectionsMap_toPushforwardTwistOver (n : ℕ) (S : Scheme.{u}) (d : ℤ)
    (e : MonomialIndex.{u} n d) :
    SheafOfModules.sectionsMap (toPushforwardTwistOver n S d) (SheafOfModules.freeSection e) =
      pushforwardTwistOverSection n S d e :=
  SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection _ e

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
