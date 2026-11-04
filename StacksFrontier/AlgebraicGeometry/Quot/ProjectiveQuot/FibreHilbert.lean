module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.BaseChange
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.HilbertPolynomialTwistShift
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Basic

/-!
# Fibrewise Hilbert functions of finitely presented modules on `ℙⁿ_T`

For a module `ℱ` of finite presentation on `ℙⁿ_T` and a point `t ∈ T`, the fibre `ℱ_t` on
`ℙⁿ_{κ(t)}` is coherent, and `d ↦ χ(ℙⁿ_{κ(t)}, ℱ_t(d))` is its Hilbert function. It is invariant
under isomorphism, under base change `T' ⟶ T` (the fibre over `t'` is the extension of scalars of
the fibre over the image of `t'`, Stacks 08AB), and twisting shifts it.

## Main definitions

* `AlgebraicGeometry.ProjectiveQuot.fibreHilbert`: `d ↦ χ(ℙⁿ_{κ(t)}, ℱ_t(d))`.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.fibreHilbert_eq_of_iso`,
  `AlgebraicGeometry.ProjectiveQuot.fibreHilbert_pullback`,
  `AlgebraicGeometry.ProjectiveQuot.fibreHilbert_twist`.
* `AlgebraicGeometry.ProjectiveQuot.hasFibreHilbertPolynomial_iff`: membership in `Quot^P` read
  on `fibreHilbert`.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n : ℕ}

/-- The inverse image of a module of finite presentation is of finite presentation. -/
instance isFinitePresentation_pullback_obj {X Y : Scheme.{u}} (f : X ⟶ Y) (M : Y.Modules)
    [M.IsFinitePresentation] : ((Scheme.Modules.pullback f).obj M).IsFinitePresentation :=
  Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_pullback f M

/-- The twist of a module of finite presentation is of finite presentation. -/
instance isFinitePresentation_twist_obj {T : Scheme.{u}} (d : ℤ)
    (F : (projectiveSpaceOver n T).Modules) [F.IsFinitePresentation] :
    (twist d F).IsFinitePresentation :=
  isFinitePresentation_twist d F inferInstance

/-- The fibre of a module of finite presentation is coherent. -/
theorem isCoherent_fibre {T : Scheme.{u}} (t : T) (F : (projectiveSpaceOver n T).Modules)
    [F.IsFinitePresentation] : (fibre t F).IsCoherent :=
  isCoherent_of_isFinitePresentation_projectiveSpace _ _

/-- **The fibrewise Hilbert function** `d ↦ χ(ℙⁿ_{κ(t)}, ℱ_t(d))` of a module of finite
presentation on `ℙⁿ_T` at a point `t ∈ T`. -/
def fibreHilbert {T : Scheme.{u}} (F : (projectiveSpaceOver n T).Modules)
    [F.IsFinitePresentation] (t : T) : ℤ → ℤ :=
  @hilbertPolynomial (T.residueField t) _ n (fibre t F) (isCoherent_fibre t F)

/-- The fibrewise Hilbert function is computed on any coherent module isomorphic to the fibre. -/
private theorem fibreHilbert_eq_of_fibre_iso {T : Scheme.{u}}
    {F : (projectiveSpaceOver n T).Modules} [F.IsFinitePresentation] (t : T)
    {G : (projectiveSpaceOverRing n (.of (T.residueField t))).Modules} [G.IsCoherent]
    (e : fibre t F ≅ G) (d : ℤ) : fibreHilbert F t d = hilbertPolynomial _ n G d := by
  have := isCoherent_fibre t F
  exact hilbertPolynomial_eq_of_iso _ n e d

/-- Isomorphic modules of finite presentation on `ℙⁿ_T` have the same fibrewise Hilbert function
at every point `t ∈ T`. -/
theorem fibreHilbert_eq_of_iso {T : Scheme.{u}} {F G : (projectiveSpaceOver n T).Modules}
    [F.IsFinitePresentation] [G.IsFinitePresentation] (e : F ≅ G) (t : T) :
    fibreHilbert F t = fibreHilbert G t := by
  have := isCoherent_fibre t G
  exact funext <| fibreHilbert_eq_of_fibre_iso t
    ((Scheme.Modules.pullback (fibreMap n t)).mapIso e)

/-- **Base change of the fibrewise Hilbert function**: the fibre of `(ℙⁿ_g)^* ℱ` over `t'` is the
extension of scalars of the fibre of `ℱ` over `g t'`, which has the same Hilbert function. -/
theorem fibreHilbert_pullback {T' T : Scheme.{u}} (g : T' ⟶ T)
    (F : (projectiveSpaceOver n T).Modules) [F.IsFinitePresentation] (t' : T') :
    fibreHilbert ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj F) t' =
      fibreHilbert F (g t') := by
  let := (g.residueFieldMap t').hom.toAlgebra
  let E := projectiveSpaceFieldExtensionMap (T.residueField (g t')) (T'.residueField t') n
  let e : fibre t' ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj F) ≅
      (Scheme.Modules.pullback E).obj (fibre (g t') F) :=
    (Scheme.Modules.pullbackComp (fibreMap n t') (projectiveSpaceOverMap n g)).app F ≪≫
      (Scheme.Modules.pullbackCongr (fibreMap_comp_projectiveSpaceOverMap g t')).app F ≪≫
      ((Scheme.Modules.pullbackComp E (fibreMap n (g t'))).app F).symm
  have := isCoherent_fibre (g t') F
  have hFK : ((Scheme.Modules.pullback E).obj (fibre (g t') F)).IsCoherent :=
    isCoherent_of_isFinitePresentation_projectiveSpace _ _
  funext d
  exact (fibreHilbert_eq_of_fibre_iso t' e d).trans
    (hilbertPolynomial_pullback_fieldExtension _ _ n (fibre (g t') F) hFK d)

/-- **Twisting shifts the fibrewise Hilbert function**: `χ(ℱ(a)_t(d)) = χ(ℱ_t(d + a))`. -/
theorem fibreHilbert_twist {T : Scheme.{u}} (F : (projectiveSpaceOver n T).Modules)
    [F.IsFinitePresentation] (a : ℤ) (t : T) (d : ℤ) :
    fibreHilbert (twist a F) t d = fibreHilbert F t (d + a) := by
  have := isCoherent_fibre t F
  have : (projectiveTwist n (fibre t F) a).IsCoherent :=
    isCoherent_of_isFinitePresentation_projectiveSpace _ (twist a (fibre t F))
  have e : fibre t (twist a F) ≅ projectiveTwist n (fibre t F) a :=
    (twistPullbackIso (T.fromSpecResidueField t) a F).symm
  exact (fibreHilbert_eq_of_fibre_iso t e d).trans
    (hilbertPolynomial_projectiveTwist _ n (fibre t F) a d)

/-- **Membership in `Quot^P`, read on the fibrewise Hilbert function.** -/
theorem hasFibreHilbertPolynomial_iff {P : Polynomial ℚ} {T : Scheme.{u}}
    (F : (projectiveSpaceOver n T).Modules) [F.IsFinitePresentation] :
    HasFibreHilbertPolynomial P F ↔ ∀ t : T, ∀ d : ℤ, (fibreHilbert F t d : ℚ) = P.eval (d : ℚ) :=
  ⟨fun h t d => (h t).2 d, fun h t => ⟨isCoherent_fibre t F, h t⟩⟩

end AlgebraicGeometry.ProjectiveQuot

end
