module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.DivisorFlatPullback.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.ZeroSchemeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.PullbackInvertible.Basic

/-!
# Pullback of the invertible sheaf of an effective Cartier divisor

Let `f : X ⟶ Y` be a morphism of schemes and `D ⊆ Y` an effective Cartier divisor whose
pullback is defined, that is, whose scheme-theoretic inverse image `f^{-1}D` is again an
effective Cartier divisor ([Stacks, Tag 01WV], `Stacks.Divisors.IsPullbackDefined`). Then the
invertible sheaf of `D` pulls back to the invertible sheaf of `f^{-1}D`,

`f^* 𝒪_Y(D) ≅ 𝒪_X(f^{-1}D)`,

and under that identification the pullback of the canonical section `1_D` is the canonical
section `1_{f^{-1}D}`.

## Main definitions

* `Stacks.Divisors.invertibleSheafPullbackIso`: the identification `f^* 𝒪_Y(D) ≅ 𝒪_X(f^{-1}D)`.

## Main results

* `Stacks.Divisors.invertibleSheafPullbackIso_canonicalSection`: the pullback of `1_D` is
  `1_{f^{-1}D}`.
* `Stacks.Divisors.zeroScheme_pullbackCanonicalSection`: the zero scheme of the pulled-back
  canonical section is `f^{-1}D`.
* `Stacks.Divisors.isRegularSection_pullbackCanonicalSection`: the pulled-back canonical
  section is a nonzerodivisor.

## Implementation notes

**The shape of the argument.** The zero scheme of the canonical section of `𝒪_Y(D)` is `D`
itself (`Stacks.Divisors.zeroScheme_canonicalSection`), zero schemes commute with pullback
([Stacks, Tag 0B6Y], `AlgebraicGeometry.zeroScheme_pullback`), and the pullback of an invertible
module is invertible ([Stacks, Tag 0B8L], `Stacks.Modules.isInvertible_pullback`). So the zero
scheme of the pulled-back canonical section is `f^{-1}D`, which is an effective Cartier divisor
by hypothesis, and therefore the pulled-back canonical section is a nonzerodivisor
([Stacks, Tag 02OR] (4),
`AlgebraicGeometry.isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection`). The whole
statement is then the identification of an invertible module carrying a nonzerodivisor section
with the invertible sheaf of the zero scheme of that section
(`AlgebraicGeometry.invertibleSheafIsoZeroSchemeOfIsRegularSection`), transported along the
equality of ideal sheaves.

**Why the isomorphism is produced by `Classical.choose`.** Transporting the identification along
an equality of ideal-sheaf data has to move the canonical section along the same equality, and
the only painless way to do that is to destructure the equality — which requires the statement
being transported to be a proposition. So the existence statement
`Stacks.Divisors.exists_invertibleSheafPullbackIso` carries both halves at once, and the
isomorphism is a choice of witness for it; the section identity is the corresponding
`Classical.choose_spec`. Nothing is weakened: the definition is an isomorphism, not an existence
claim, and it satisfies the section identity by construction.

**Global sections as sections.** `AlgebraicGeometry.IsRegularSection` is stated for an element of
`SheafOfModules.sections`, while `AlgebraicGeometry.pullbackGlobalSections` produces a section
over the whole space. `Stacks.Divisors.sectionsOfTop` bridges the two: on a scheme the two are
interchangeable because every open is contained in `⊤`.

## References

* [Stacks Project, Tag 0C4U](https://stacks.math.columbia.edu/tag/0C4U)
* [Stacks Project, Tag 01WV](https://stacks.math.columbia.edu/tag/01WV)
* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
* [Stacks Project, Tag 02OR](https://stacks.math.columbia.edu/tag/02OR)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.Divisors

variable {X : Scheme.{u}}

/-- **A global section of a module on a scheme, from its value over the whole space.** The
components over the other opens are the restrictions of that value. -/
def sectionsOfTop (M : X.Modules) (x : Γ(M, (⊤ : X.Opens))) : M.sections :=
  M.val.sectionsMk (fun U => M.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op x)
    fun {U V} g =>
      (M.val.map_comp_apply (homOfLE (le_top : U.unop ≤ ⊤)).op g x).symm.trans
        (congrArg (fun h : op (⊤ : X.Opens) ⟶ V => (M.val.map h) x) (Subsingleton.elim _ _))

/-- The component of `Stacks.Divisors.sectionsOfTop` over an open is the restriction. -/
theorem sectionsOfTop_eval (M : X.Modules) (x : Γ(M, (⊤ : X.Opens))) (U : X.Opens) :
    (sectionsOfTop M x).eval (op U) = M.presheaf.map (homOfLE le_top).op x := rfl

/-- `Stacks.Divisors.sectionsOfTop` recovers the section it was built from. -/
theorem sectionsOfTop_eval_top (M : X.Modules) (x : Γ(M, (⊤ : X.Opens))) :
    (sectionsOfTop M x).eval (op ⊤) = x := by
  rw [sectionsOfTop_eval,
    show (homOfLE (le_top : (⊤ : X.Opens) ≤ ⊤)).op = 𝟙 (op (⊤ : X.Opens)) from
      Subsingleton.elim _ _,
    M.presheaf.map_id]
  rfl

variable {Y : Scheme.{u}} (f : X ⟶ Y) (D : Y.IdealSheafData) [IsEffectiveCartierDivisor D]

/-- **The pullback of the canonical section `1_D`**, as a global section of `f^* 𝒪_Y(D)`. -/
def pullbackCanonicalSection :
    Γ((Scheme.Modules.pullback f).obj (invertibleSheaf' D), (⊤ : X.Opens)) :=
  pullbackGlobalSections f (invertibleSheaf' D) ((canonicalSection' D).eval (op ⊤))

/-- The pullback of `𝒪_Y(D)` is invertible: this is [Stacks, Tag 0B8L] at the invertible sheaf
of an effective Cartier divisor, re-spelled so that the zero-scheme API of [Stacks, Tag 02OQ]
resolves its hypothesis by instance search. -/
instance isInvertible_pullback_invertibleSheaf :
    AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      ((Scheme.Modules.pullback f).obj (invertibleSheaf' D)) :=
  haveI := isTensorInvertible_invertibleSheaf D
  (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).1
    (Stacks.Modules.isInvertible_pullback f (invertibleSheaf' D))

/-- **The zero scheme of the pulled-back canonical section is the inverse-image divisor.** The
zero scheme of `1_D` is `D` ([Stacks, Tag 02OQ],
`Stacks.Divisors.zeroScheme_canonicalSection`) and zero schemes commute with pullback
([Stacks, Tag 0B6Y], `AlgebraicGeometry.zeroScheme_pullback`). -/
theorem zeroScheme_pullbackCanonicalSection :
    zeroScheme X ((Scheme.Modules.pullback f).obj (invertibleSheaf' D))
        (pullbackCanonicalSection f D) = D.comap f :=
  (zeroScheme_pullback f (invertibleSheaf' D) ((canonicalSection' D).eval (op ⊤))).trans
    (congrArg (fun I : Y.IdealSheafData => I.comap f) (zeroScheme_canonicalSection D))

variable [IsPullbackDefined f D]

/-- An equality of closed subschemes transports the effective-Cartier-divisor property. -/
theorem isEffectiveCartierDivisor_of_eq {E E' : X.IdealSheafData} (h : E = E')
    [IsEffectiveCartierDivisor E'] : IsEffectiveCartierDivisor E := by
  cases h
  infer_instance

omit [IsPullbackDefined f D] in
/-- The zero scheme of the pulled-back canonical section, read through
`Stacks.Divisors.sectionsOfTop`, is the inverse-image divisor. -/
theorem zeroScheme_sectionsOfTop_pullbackCanonicalSection :
    zeroScheme X ((Scheme.Modules.pullback f).obj (invertibleSheaf' D))
        ((sectionsOfTop ((Scheme.Modules.pullback f).obj (invertibleSheaf' D))
          (pullbackCanonicalSection f D)).eval (op ⊤)) = D.comap f :=
  by rw [sectionsOfTop_eval_top]; exact zeroScheme_pullbackCanonicalSection f D

/-- **The pulled-back canonical section is a nonzerodivisor.** Its zero scheme is the
inverse-image divisor, which is an effective Cartier divisor exactly because the pullback of `D`
is defined, and a section of an invertible module whose zero scheme is an effective Cartier
divisor is a nonzerodivisor ([Stacks, Tag 02OR] (4)). -/
theorem isRegularSection_pullbackCanonicalSection :
    IsRegularSection X.sheaf.obj X.ringCatSheaf.property
      (sectionsOfTop ((Scheme.Modules.pullback f).obj (invertibleSheaf' D))
        (pullbackCanonicalSection f D)) :=
  (isEffectiveCartierDivisor_zeroScheme_iff_isRegularSection X
      ((Scheme.Modules.pullback f).obj (invertibleSheaf' D)) _).1
    (isEffectiveCartierDivisor_of_eq (zeroScheme_sectionsOfTop_pullbackCanonicalSection f D))

/-- Transporting the identification of an invertible module with the invertible sheaf of a
closed subscheme along an equality of closed subschemes. -/
private theorem exists_invertibleSheafIso_of_eq {M : X.Modules} {E E' : X.IdealSheafData}
    (h : E = E') (x : Γ(M, (⊤ : X.Opens)))
    (p : ∃ e : M ≅ invertibleSheaf' E,
      Scheme.Modules.Hom.app e.hom ⊤ x = (canonicalSection' E).val (op ⊤)) :
    ∃ e : M ≅ invertibleSheaf' E',
      Scheme.Modules.Hom.app e.hom ⊤ x = (canonicalSection' E').val (op ⊤) := by
  cases h
  exact p

/-- **There is an identification `f^* 𝒪_Y(D) ≅ 𝒪_X(f^{-1}D)` carrying the pullback of `1_D` to
`1_{f^{-1}D}`.** The pulled-back canonical section is a nonzerodivisor section of an invertible
module whose zero scheme is `f^{-1}D`, so the identification is the one of
`AlgebraicGeometry.invertibleSheafIsoZeroSchemeOfIsRegularSection` transported along that
equality. -/
theorem exists_invertibleSheafPullbackIso :
    ∃ e : (Scheme.Modules.pullback f).obj (invertibleSheaf' D) ≅ invertibleSheaf' (D.comap f),
      Scheme.Modules.Hom.app e.hom ⊤ (pullbackCanonicalSection f D) =
        (canonicalSection' (D.comap f)).val (op ⊤) := by
  have hreg := isRegularSection_pullbackCanonicalSection f D
  refine exists_invertibleSheafIso_of_eq
    (zeroScheme_sectionsOfTop_pullbackCanonicalSection f D)
    (pullbackCanonicalSection f D) ?_
  exact ⟨invertibleSheafIsoZeroSchemeOfIsRegularSection _ _ hreg, by
    simpa only [sectionsOfTop_eval_top] using
      invertibleSheafIsoZeroSchemeOfIsRegularSection_section _ _ hreg⟩

/-- **Stacks Project, Tag 0C4U.** The canonical identification `f^* 𝒪_Y(D) ≅ 𝒪_X(f^{-1}D)` of
the invertible sheaf of an effective Cartier divisor whose pullback is defined with the
invertible sheaf of its inverse image. -/
@[stacks 0C4U "associated sheaf"]
def invertibleSheafPullbackIso :
    (Scheme.Modules.pullback f).obj (invertibleSheaf' D) ≅ invertibleSheaf' (D.comap f) :=
  Classical.choose (exists_invertibleSheafPullbackIso f D)

/-- **Stacks Project, Tag 0C4U.** Under the identification
`Stacks.Divisors.invertibleSheafPullbackIso` the pullback of the canonical section `1_D` is the
canonical section `1_{f^{-1}D}`. -/
@[stacks 0C4U "canonical section"]
theorem invertibleSheafPullbackIso_canonicalSection :
    Scheme.Modules.Hom.app (invertibleSheafPullbackIso f D).hom ⊤
        (pullbackCanonicalSection f D) =
      (canonicalSection' (D.comap f)).val (op ⊤) :=
  Classical.choose_spec (exists_invertibleSheafPullbackIso f D)

end Stacks.Divisors

end
