module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.AffineVanishingUnbounded
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
public import StacksFrontier.RingTheory.LocalCohomology.Deps.QuasicoherentAffineVanishing

/-!
# Bounded below affine vanishing

Let `X` be an *affine* scheme over a commutative ring `A`, with structure morphism
`f : X ⟶ Spec A`, and let `K` be a cochain complex of `𝒪_X`-modules which is bounded below and
whose terms are quasi-coherent. Then the canonical comparison
`AlgebraicGeometry.globalSectionsComplexComparison`
$$ Q(\Gamma(X, K^\bullet)) \longrightarrow R\Gamma(X, Q(K^\bullet)) $$
in `D(A)` is an isomorphism: the complex of `A`-linear global sections of `K` already computes
the *unbounded* derived global sections of the object it represents. This is the bounded below
case of the affine vanishing of Stacks 08D4, and it is the bounded input on which the
`E = R\lim \tau_{\geq -n}E` argument of that tag rests.

The two ingredients were already available and are joined here.

**Serre vanishing.** `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen`
(Stacks 01XB) says that `Hᵖ(U, F) = 0` for `p > 0`, `U` an affine open and `F` quasi-coherent.
It is stated for the `ℕ`-indexed, `AddCommGrpCat`-valued cohomology `Hgroup` of
Stacks Tag 01E3, i.e. for the right derived functors of
`secF 𝒪_X U = SheafOfModules.toSheaf 𝒪_X ⋙ Γ(U, -)`.

**Leray's acyclicity lemma.** The library's
`AlgebraicGeometry.isIso_globalSectionsComplexComparison_of_plus_of_rightAcyclic`
says that the comparison is invertible at a bounded below complex whose terms are right acyclic
for `A`-linear global sections. Right acyclicity (Stacks 0157) is a statement about the
`ℤ`-indexed `Functor.rightDerivedPlus` of `AlgebraicGeometry.globalSectionsOver`, which takes
values in `ModuleCat A`.

Joining them is the content of this file, and it is three steps.

1. The two global sections functors agree: `secF 𝒪_X ⊤` is *literally* `Γ(X, -)` followed by the
   forgetful functor `ModuleCat A ⥤ AddCommGrpCat`, both being "the sections over `⊤`, with the
   module structure forgotten". This is `globalSectionsOver_comp_forget₂`, an equality of
   functors.
2. Forgetting the `A`-module structure is an exact functor, so it commutes with right derived
   functors (`Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology`); and an
   `A`-module whose underlying abelian group is zero is zero. So the vanishing of Serre's
   `AddCommGrpCat`-valued `Hᵖ` is the vanishing of `R ᵖΓ(X, -)` in `ModuleCat A`.
3. Right acyclicity of an object for a left exact functor is vanishing of all its higher
   `ℕ`-indexed right derived functors there, by
   `Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived` — which is Stacks 015C read through
   the comparison `Stacks.DerivedIndexing.isZero_rightDerived_obj_iff` of the `ℕ`- and
   `ℤ`-indexed right derived functors.

## Main results

* `AlgebraicGeometry.globalSectionsOver_comp_forget₂` — `A`-linear global sections, with the
  module structure forgotten, is the abelian-group-valued global sections functor of
  Stacks 20.7.
* `AlgebraicGeometry.isZero_rightDerived_globalSectionsOver_of_isQuasicoherent` — Serre vanishing
  for the `ModuleCat A`-valued higher right derived functors of `Γ(X, -)`.
* `AlgebraicGeometry.rightAcyclic_globalSectionsOver_of_isQuasicoherent` — a quasi-coherent
  module on an affine scheme is right acyclic for `A`-linear global sections.
* `AlgebraicGeometry.isIso_globalSectionsComplexComparison_of_plus_of_isQuasicoherent` —
  **bounded below affine vanishing**: the comparison `Q(Γ(X, K)) ⟶ RΓ(X, Q(K))` is invertible for
  a bounded below complex of quasi-coherent modules on an affine scheme.
* `AlgebraicGeometry.isIso_globalSectionsComplexComparison_tilde_of_plus` — the same for the
  complexes `M̃^•` on `Spec R`, which is the form in which unbounded affine vanishing feeds the
  derived Spec–Γ equivalence of Stacks 06Z0.

## Implementation notes

`X.Modules` and `SheafOfModules X.ringCatSheaf` are definitionally equal but carry separately
declared `Category` and `Preadditive` instances that instance search does not cross; see the
implementation notes of `StacksFrontier/AlgebraicGeometry/DerivedGlobalSections.lean`. Everything
below is phrased in the `X.Modules` view, the one `AlgebraicGeometry.globalSectionsOver` uses,
and the crossing to Serre vanishing — whose conclusion is spelled over
`SheafOfModules X.ringCatSheaf` — happens only by passing a term, which unification handles.

Step 1 needs no construction: `AlgebraicGeometry.globalSectionsOver` is an `abbrev` whose body is
`SheafOfModules.evaluation X.ringCatSheaf (op ⊤) ⋙ ModuleCat.restrictScalars …`, and composing
with `forget₂ (ModuleCat A) AddCommGrpCat` reaches `M.val.presheaf.obj (op ⊤)`, which is what
`secF X.ringCatSheaf ⊤` is. The equality is therefore `rfl`, and it is recorded as a theorem only
to name the identification; the proofs below use the two spellings interchangeably.

The hypotheses are `IsAffine X` and quasi-coherence of the terms, not `X = Spec R`: Serre
vanishing is available over every affine open, so there is no reason to specialize, and the
derived Spec–Γ comparison needs the statement for `𝟙 (Spec R)`, which is the special case.

## What is not done

`@[stacks 08D4]` is not placed here, and is not needed here: that tag's covering set is complete
in `StacksFrontier/AlgebraicGeometry/Duality/AffineVanishing/DerivedBounds.lean` and
`StacksFrontier/AlgebraicGeometry/Duality/DerivedAmplitude/UpperBounds.lean`. What is proved here is
the bounded below input to the affine case, which is not one of the tag's clauses. Nor is
`@[stacks 015E]` placed, for the
reason given in the implementation notes of
`StacksFrontier/AlgebraicGeometry/AffineVanishingUnbounded.lean`. The hypothesis of
`AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app` quantifies over *all*
complexes of `R`-modules, so the derived Spec–Γ unit does not yet follow from the bounded below
case alone.

## References

* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 08D4](https://stacks.math.columbia.edu/tag/08D4)
* [Stacks Project, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w₁ w₂ u

namespace AlgebraicGeometry

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))

/-! ### `A`-linear global sections and abelian-group-valued sheaf cohomology -/

/-- **`A`-linear global sections, with the module structure forgotten, is the global sections
functor of the sheaf-cohomology chapters.** Both sides send a sheaf of `𝒪_X`-modules to its
abelian group of sections over `⊤`: `AlgebraicGeometry.globalSectionsOver` evaluates the
underlying presheaf of modules at `⊤` and then restricts and forgets the scalars, while `secF`
forgets the module structure first and then evaluates. The two are equal, not merely isomorphic,
so Serre vanishing for `secF` is Serre vanishing for `Γ(X, -)`. -/
theorem globalSectionsOver_comp_forget₂ :
    globalSectionsOver f ⋙ forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u} =
      secF X.ringCatSheaf (⊤ : X.Opens) :=
  rfl

/-- **Serre vanishing for `A`-linear global sections.** On an affine scheme over `A` the higher
right derived functors of `Γ(X, -) : Mod(𝒪_X) ⥤ ModuleCat A` vanish on a quasi-coherent module.

This is `Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen` (Stacks 01XB) at
the affine open `⊤`, transported from `AddCommGrpCat` to `ModuleCat A`: forgetting the
`A`-module structure is exact, hence commutes with right derived functors
(`Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology`), and an `A`-module with zero
underlying abelian group is zero. -/
theorem isZero_rightDerived_globalSectionsOver_of_isQuasicoherent [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] (p : ℕ) (hp : 0 < p) :
    IsZero (((globalSectionsOver f).rightDerived p).obj F) := by
  have h : IsZero (((globalSectionsOver f ⋙
      forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).rightDerived p).obj F) :=
    Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F ⊤
      (isAffineOpen_top X) p hp
  obtain ⟨e⟩ := Stacks.Cohomology.rightDerived_comp_iso_of_preservesHomology
    (globalSectionsOver f) (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) p F
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (AddCommGrpCat.subsingleton_of_isZero
      (show IsZero (((globalSectionsOver f).rightDerived p ⋙
        forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj F) from h.of_iso e))

variable [HasDerivedCategory.{w₁} X.Modules] [HasDerivedCategory.{w₂} (ModuleCat.{u} A)]

/-- **A quasi-coherent module on an affine scheme is right acyclic for `A`-linear global
sections** (Stacks 0157 for `Γ(X, -)`). Right acyclicity of an object for a left exact functor is
vanishing of all its higher right derived functors there — Stacks 015C, read through the
comparison of the `ℕ`- and `ℤ`-indexed right derived functors — and that vanishing is Serre
vanishing. -/
theorem rightAcyclic_globalSectionsOver_of_isQuasicoherent [IsAffine X]
    (F : X.Modules) [F.IsQuasicoherent] :
    (globalSectionsOver f).rightAcyclic F :=
  (Stacks.Cohomology.rightAcyclic_iff_isZero_rightDerived (globalSectionsOver f) F).2
    fun p hp => isZero_rightDerived_globalSectionsOver_of_isQuasicoherent f F p hp

/-! ### Bounded below affine vanishing -/

/-- **Bounded below affine vanishing.** Let `X` be an affine scheme over a commutative ring `A`
and let `K` be a bounded below cochain complex of quasi-coherent `𝒪_X`-modules. Then the
comparison `Q(Γ(X, K)) ⟶ RΓ(X, Q(K))` in `D(A)` is an isomorphism: the complex of `A`-linear
global sections of `K` computes the unbounded derived global sections.

This is the bounded below case of the affine vanishing of Stacks 08D4, and the bounded input of
the `E = R\lim \tau_{\geq -n}E` argument for an unbounded complex. It is Leray's acyclicity
lemma, `AlgebraicGeometry.isIso_globalSectionsComplexComparison_of_plus_of_rightAcyclic`, applied
to the right acyclicity supplied by Serre vanishing. -/
theorem isIso_globalSectionsComplexComparison_of_plus_of_isQuasicoherent [IsAffine X]
    (K : CochainComplex X.Modules ℤ) (hK : CochainComplex.plus X.Modules K)
    (hqc : ∀ n : ℤ, (K.X n).IsQuasicoherent) :
    IsIso (globalSectionsComplexComparison f K) :=
  isIso_globalSectionsComplexComparison_of_plus_of_rightAcyclic f K hK
    fun n => have := hqc n
      rightAcyclic_globalSectionsOver_of_isQuasicoherent f (K.X n)

/-! ### The complexes `M̃^•` -/

variable (R : CommRingCat.{u})

/-- **Bounded below affine vanishing for the complexes `M̃^•`.** For a bounded below cochain
complex `M^•` of `R`-modules, the comparison
`Q(Γ(Spec R, M̃^•)) ⟶ RΓ(Spec R, Q(M̃^•))` is an isomorphism.

This is the bounded below half of the hypothesis of
`AlgebraicGeometry.isIso_derivedTildeGlobalSectionsAdjunction_unit_app`, which is the affine case
of Stacks 08D4 and the last input of the derived Spec–Γ equivalence of Stacks 06Z0. Each term
`M̃ⁿ` is quasi-coherent, and `~` is faithful and additive, so the degreewise sheafification of a
bounded below complex is bounded below. -/
theorem isIso_globalSectionsComplexComparison_tilde_of_plus
    (M : CochainComplex (ModuleCat.{u} R) ℤ) (hM : CochainComplex.plus _ M) :
    IsIso (globalSectionsComplexComparison (𝟙 (Spec R))
      (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) := by
  obtain ⟨n, hn⟩ := hM
  refine isIso_globalSectionsComplexComparison_of_plus_of_isQuasicoherent (𝟙 (Spec R)) _
    ⟨n, ?_⟩ fun i => inferInstanceAs ((tilde.functor R).obj (M.X i)).IsQuasicoherent
  exact (CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff M (tilde.functor R) n).2 hn

end AlgebraicGeometry

end
