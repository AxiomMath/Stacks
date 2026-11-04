module

public import StacksFrontier.AlgebraicGeometry.OneDimensionalLocal.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.AffinePairLocality
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.BoundedComplex

/-!
# A locally bounded above complex with relatively pseudo-coherent terms

Let `f : X ⟶ S` be a morphism of schemes locally of finite type and let `𝓕` be a complex of
`𝒪_X`-modules which is bounded above on a neighbourhood of every point. If the term `𝓕ⁱ` is
`(m - i)`-pseudo-coherent relative to `S` for every `i`, then `𝓕` is `m`-pseudo-coherent relative
to `S`. This is Stacks 09UP.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isZero_restrict_iff_forall_isZero_stalk`: vanishing of the
  restriction of a sheaf of modules to an open subscheme is vanishing of its stalks at the points
  of that open.
* `AlgebraicGeometry.exists_isZero_restrict_of_isCompact`: a family of sheaves of modules which
  vanishes in high degrees near every point of a *quasi-compact* open vanishes in high degrees on
  that open, with a single bound.
* `AlgebraicGeometry.Scheme.Hom.isPseudoCoherentFrom_Q_of_locally_boundedAbove`: **Stacks 09UP.**

## Implementation notes

The content of the tag is the passage from the sheaf-level statement Stacks 09V7, proved as
`AlgebraicGeometry.RingedSpace.isPseudoCoherentComplexFrom_of_locally_boundedAbove`, to the
relative one. As for Stacks 09UL, the reduction is not immediate from the definition of
Stacks 09UI, because each term of the complex comes with its own affine covers and closed
immersions while the conclusion has to be proved at a single one. Stacks 09UJ supplies both
halves of the fix: it turns relative `m`-pseudo-coherence into a condition at every compatible
pair of affine opens, and — through
`AlgebraicGeometry.Scheme.Hom.IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion`, which
is Stacks 09VC — into a condition at every closed immersion over such a pair. One closed
immersion `i : U ⟶ 𝔸ⁿ_V`, which exists by
`AlgebraicGeometry.exists_isClosedImmersion_affineSpace_resLE`, therefore serves for every term
at once.

At that closed immersion the local condition is sheaf-level `m`-pseudo-coherence of the derived
pushforward (`AlgebraicGeometry.Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff`), and
restriction along an open immersion and pushforward along a closed immersion are both exact, so
the composite carries `𝓕` to a complex `𝓕'` on `𝔸ⁿ_V` with `𝓕'ⁱ = i_*(𝓕ⁱ|_U)` and carries the
derived object `Q(𝓕)` to `Q(𝓕')`.

On `𝔸ⁿ_V` only the *globally* bounded above case of Stacks 09V7,
`AlgebraicGeometry.RingedSpace.isPseudoCoherentFrom_Q_of_boundedAbove`, is needed: `U` is affine,
hence quasi-compact, so the local bounds on `𝓕` can be replaced by one bound valid on all of `U`
by `AlgebraicGeometry.exists_isZero_restrict_of_isCompact`, and a zero module is carried to a zero
module by `i_*`. That replacement is where vanishing of a sheaf of modules is recognised as a
condition on stalks.

The derived categories are the ones provided by `CategoryTheory.HasDerivedCategory.standard`,
which is made a local instance; there is no global instance, so a user of these results makes the
same declaration.

## References

* [The Stacks Project, Lemma 36.61.9 (09UP)](https://stacks.math.columbia.edu/tag/09UP)
* [The Stacks Project, Definition 36.61.1 (09UI)](https://stacks.math.columbia.edu/tag/09UI)
* [The Stacks Project, Lemma 36.61.5 (09UJ)](https://stacks.math.columbia.edu/tag/09UJ)
* [The Stacks Project, Lemma 36.61.2 (09VC)](https://stacks.math.columbia.edu/tag/09VC)
* [The Stacks Project, Lemma 20.46.14 (09V7)](https://stacks.math.columbia.edu/tag/09V7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### Vanishing of a sheaf of modules on an open subscheme -/

namespace Scheme.Modules

/-- **Vanishing of the restriction of a sheaf of modules to an open subscheme is a condition on
stalks.** The restriction of `M` to `U` is a zero object exactly when the stalk of `M` at every
point of `U` vanishes, because restriction along an open immersion commutes with taking stalks
(`AlgebraicGeometry.Scheme.Modules.restrictStalkNatIso`) and a sheaf of modules with vanishing
stalks is a zero object (`AlgebraicGeometry.isZero_of_forall_isZero_stalk`). -/
public theorem isZero_restrict_iff_forall_isZero_stalk {X : Scheme.{u}} (U : X.Opens)
    (M : X.Modules) :
    IsZero ((restrictFunctor U.ι).obj M) ↔ ∀ x ∈ U, IsZero (M.presheaf.stalk x) := by
  refine ⟨fun h x hx => ?_, fun h => isZero_of_forall_isZero_stalk _ fun y =>
    (h (U.ι.base y) y.2).of_iso ((restrictStalkNatIso U.ι y).app M)⟩
  have h₁ := (Functor.map_isZero (TopCat.Presheaf.stalkFunctor Ab.{u} (⟨x, hx⟩ : U.toScheme))
    (Functor.map_isZero (toPresheaf U.toScheme) h)).of_iso
      ((restrictStalkNatIso U.ι (⟨x, hx⟩ : U.toScheme)).app M).symm
  exact h₁

end Scheme.Modules

/-- **A family of sheaves of modules which vanishes in high degrees near every point of a
quasi-compact open vanishes in high degrees on that open.** The point is that the bound becomes
uniform: finitely many of the given opens cover `U`, and the largest of their bounds works on all
of `U`.

Vanishing on `U` is checked on stalks through
`AlgebraicGeometry.Scheme.Modules.isZero_restrict_iff_forall_isZero_stalk`, which is what makes
the two restrictions — to a member of the cover and to `U` — comparable without a base-change
isomorphism. -/
public theorem exists_isZero_restrict_of_isCompact {X : Scheme.{u}} (M : ℤ → X.Modules)
    (U : X.Opens) (hU : IsCompact (U : Set X))
    (hM : ∀ x ∈ U, ∃ O : X.Opens, x ∈ O ∧ ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((Scheme.Modules.restrictFunctor O.ι).obj (M i))) :
    ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj (M i)) := by
  classical
  have hM' : ∀ x : (U : Set X), ∃ O : X.Opens, (x : X) ∈ O ∧ ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((Scheme.Modules.restrictFunctor O.ι).obj (M i)) := fun x => hM x x.2
  choose O hO b hb using hM'
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : (U : Set X) => (O x : Set X))
    (fun x => (O x).isOpen) fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hO ⟨y, hy⟩⟩
  obtain ⟨B, hB⟩ := (t.image b).exists_le
  refine ⟨B, fun i hi =>
    (Scheme.Modules.isZero_restrict_iff_forall_isZero_stalk U (M i)).2 fun x hx => ?_⟩
  obtain ⟨z, hzt, hzx⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact (Scheme.Modules.isZero_restrict_iff_forall_isZero_stalk (O z) (M i)).1
    (hb z i ((hB _ (Finset.mem_image_of_mem b hzt)).trans_lt hi)) x hzx

/-! ### Stacks 09UP -/

attribute [local instance] HasDerivedCategory.standard

namespace Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **Stacks 09UP.** Let `f : X ⟶ S` be a morphism of schemes locally of finite type, let `m` be
an integer and let `𝓕` be a complex of `𝒪_X`-modules which is bounded above on a neighbourhood of
every point. If `𝓕ⁱ` is `(m - i)`-pseudo-coherent relative to `S` for every `i`, then `𝓕` is
`m`-pseudo-coherent relative to `S`.

By Stacks 09UJ it is enough to check the local condition of Stacks 09UI at a compatible pair of
affine opens `U ⊆ f ⁻¹ᵁ V`, and by Stacks 09VC it may be checked at any one closed immersion
`i : U ⟶ 𝔸ⁿ_V` over `V`. There it says that the complex `i_*(𝓕|_U)` on `𝔸ⁿ_V` represents an
`m`-pseudo-coherent object, which is the globally bounded above case of Stacks 09V7: the terms
are `m`-pseudo-coherent in their degrees because each `𝓕ⁱ` is relatively `(m - i)`-pseudo-coherent
at the same pair and the same closed immersion, and the complex is bounded above on all of the
quasi-compact `U`. -/
@[stacks 09UP]
public theorem isPseudoCoherentFrom_Q_of_locally_boundedAbove [LocallyOfFiniteType f] (m : ℤ)
    (F : CochainComplex X.Modules ℤ)
    (hbdd : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧ ∃ b : ℤ, ∀ i : ℤ, b < i →
      IsZero ((Scheme.Modules.restrictFunctor U.ι).obj (F.X i)))
    (hterms : ∀ i : ℤ, IsModulePseudoCoherentFrom f (F.X i) (m - i)) :
    IsPseudoCoherentFrom f (DerivedCategory.Q.obj F) m := by
  refine isPseudoCoherentFrom_of_forall_affinePair f _ m fun U V hUV => ?_
  obtain ⟨n, i, hi, hio⟩ := exists_isClosedImmersion_affineSpace_resLE f V U hUV
  refine ⟨n, i, hi, hio, (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).2 ?_⟩
  obtain ⟨B, hB⟩ := exists_isZero_restrict_of_isCompact F.X U.1 U.2.isCompact
    fun x _ => hbdd x
  set R := Scheme.Modules.restrictFunctor U.1.ι
  set P := Scheme.Modules.pushforward i
  set C := (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)
  have hterm : ∀ j : ℤ, RingedSpace.IsPseudoCoherentFrom
      (X := (AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).toRingedSpace)
      ((DerivedCategory.singleFunctor _ j).obj (C.X j)) m := by
    intro j
    refine RingedSpace.isPseudoCoherentFrom_singleFunctor_of_singleFunctor_zero.{u + 1, u}
      _ m j ?_
    have h0 := (Scheme.Modules.isPseudoCoherentFromAfterPushforward_iff i _ _).1
      (IsPseudoCoherentFromOnAffinePair.forall_isClosedImmersion f
        (isPseudoCoherentFromOnAffinePair_of_isPseudoCoherentFrom f (hterms j) U V hUV)
        n i hi hio)
    exact (h0.of_iso (P.mapDerivedCategory.mapIso
        ((Functor.mapDerivedCategorySingleFunctor R 0).app (F.X j)))).of_iso
      ((Functor.mapDerivedCategorySingleFunctor P 0).app (R.obj (F.X j)))
  have hmain : RingedSpace.IsPseudoCoherentFrom
      (X := (AffineSpace (ULift.{u} (Fin n)) (V.1 : Scheme.{u})).toRingedSpace)
      (DerivedCategory.Q.obj C) m :=
    RingedSpace.isPseudoCoherentFrom_Q_of_boundedAbove m C B
      (fun p hp => Functor.map_isZero P (hB p hp)) hterm
  exact (hmain.of_iso
      (P.mapDerivedCategoryFactors.app
        ((R.mapHomologicalComplex (ComplexShape.up ℤ)).obj F)).symm).of_iso
    (P.mapDerivedCategory.mapIso (R.mapDerivedCategoryFactors.app F)).symm

end Scheme.Hom

end AlgebraicGeometry

end
