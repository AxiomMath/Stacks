module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjDegreeOpen
public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.Restrict

/-!
# The degree-`d` open of the restriction of a graded algebra to an open subscheme

Let `S` be a scheme, `A` a quasi-coherent graded `𝒪_S`-algebra in the form of Situation 01NN and
`U` an open of `S`. A statement proved for an **affine** base — `Quadruple.fdEquiv` of
[Stacks, Tag 01NU], say — is applied over an affine open `U` of a general base by restricting `A`
to `U` (`...RelativeProjBridge.SheafGradedAlgebra.restrict`), and then it speaks of the graded
ring of *global* sections of `A|_U`, hence of the scheme
`AlgebraicGeometry.Proj.degreeOpen ((A.restrict U.ι).grading ⊤) d`. The chart of the relative
homogeneous spectrum over `U`, on the other hand, is a morphism out of `Proj (A.grading U)`. This
file identifies the two **as schemes**:

`(Proj.degreeOpen ((A.restrict U.ι).grading ⊤) d).toScheme`
`  = (Proj.degreeOpen (A.grading U) d).toScheme`

and gives the induced bijection on morphisms into them, naturally in the test scheme.

## Main results

* `AlgebraicGeometry.Proj.gradedRing_eq`: **two `GradedRing` structures on one grading are
  equal.** `DirectSum.Decomposition` is a subsingleton and `SetLike.GradedMonoid` is a
  proposition, so a `GradedRing` carries no choice.
* `AlgebraicGeometry.Proj.degreeOpen_toScheme_congr`: **the congruence for
  `AlgebraicGeometry.Proj.degreeOpen` in its grading, with every instance an argument** — the
  carrier, the ring, the `CommRing`, the `SetLike` and the grading are separate on the two sides
  and compared by hypotheses, and the `AddSubgroupClass` and the `GradedRing` need no hypothesis
  at all, the first being a proposition and the second a subsingleton.
* `...RelativeProjBridge.SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme`: **the
  identification**, for the inclusion of an open subscheme.
* `...SheafGradedAlgebra.restrictDegreeOpenHomEquiv` and
  `...SheafGradedAlgebra.restrictDegreeOpenHomEquiv_comp`: the bijection it induces on the
  morphisms out of a test scheme, and its naturality in that scheme.

## Why the single-term `congrArg` does not work, and what does

The identity wanted is `...SheafGradedAlgebra.restrict_grading`, which holds by `rfl`, together
with `AlgebraicGeometry.Scheme.Opens.ι_image_top`. Forming it as the single term
`congrArg (fun W : S.Opens => AlgebraicGeometry.Proj (A.grading W)) U.ι_image_top` — the shape
that avoids rewriting under a motive mentioning `A.sectionRing W` — reports

`(deterministic) timeout at whnf, maximum number of heartbeats (200000) has been reached`,

and so does the plain `rfl` for the restriction half alone. Declaration by
declaration, the cost sits in exactly one place. `AlgebraicGeometry.Proj` takes the `GradedRing`
instance as an argument; the two instances are
`(A.restrict U.ι).instGradedRing ⊤` and `A.instGradedRing (U.ι ''ᵁ ⊤)`, whose *arguments* differ
— the base scheme itself differs, `U.toScheme` against `S` — so the congruence of two
applications of one constant fails and the kernel unfolds `instGradedRing`, and with it
`...SheafGradedAlgebra.decomposition` and the `GradedRing`/`DirectSum` tower over
`A.sectionRing`, the cost `StacksFrontier.AlgebraicGeometry.RelativeProjBridge.SectionRing` records.
Everything *else* compares cheaply: the section rings, their `CommRing` and `SetLike` instances,
the carriers `AddSubgroup (A.sectionRing ·)` and the gradings themselves are each `rfl` in a
fraction of a second (`restrict_ι_sectionRing_image`, `restrict_ι_commRing_heq`,
`restrict_ι_setLike_heq`, `restrict_ι_addSubgroup_eq`, `restrict_ι_grading_heq` below).

`degreeOpen_toScheme_congr` is therefore stated so that the `GradedRing` instance is an
**explicit** argument on each side and is never compared: inside the proof the two gradings are
identified first, and only then are the two instances shown equal — by `gradedRing_eq`, not by
defeq. `congrArg` cannot be used for this, the instance depending on the grading it is applied
to.

Two further points of discipline make the application go through.

* The five hypotheses are supplied as **named lemmas**, not as `rfl` and `HEq.rfl` inline. Lean's
  heartbeat budget is per declaration, so five `rfl`s inline share one budget; and, worse,
  `rfl` for `hR : R₁ = R₂` *unifies the two metavariables* before the conclusion meets the goal,
  which collapses the two sides of the statement into one and reinstates the very defeq the
  lemma exists to avoid.
* The `GradedRing` arguments are **explicit**. Left instance-implicit they are synthesized rather
  than read off the goal, and the synthesized instance is then compared with the one the goal
  carries — the expensive comparison again.

## References

* [Stacks Project, Tag 01NN](https://stacks.math.columbia.edu/tag/01NN)
* [Stacks Project, Tag 01N5](https://stacks.math.columbia.edu/tag/01N5)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open AlgebraicGeometry

universe u v

namespace AlgebraicGeometry.Proj

/-- **A grading carries at most one `GradedRing` structure.** The `SetLike.GradedMonoid` half is
a proposition and the `DirectSum.Decomposition` half is a subsingleton — a decomposition is
determined by the recomposition it inverts — so the two structures agree field by field. -/
theorem gradedRing_eq {σ : Type v} {R : Type u} [CommRing R] [SetLike σ R]
    [AddSubgroupClass σ R] {𝒜 : ℕ → σ} (i j : GradedRing 𝒜) : i = j :=
  congrArg
    (fun dec : DirectSum.Decomposition 𝒜 =>
      ({ toGradedMonoid := i.toGradedMonoid, toDecomposition := dec } : GradedRing 𝒜))
    (Subsingleton.elim i.toDecomposition j.toDecomposition)

/-- **The congruence for `AlgebraicGeometry.Proj.degreeOpen` in its grading**, as schemes.

Every datum of the two sides is a separate argument: the carrier `σ`, the ring `R`, the
`CommRing` and `SetLike` instances, the grading, and — explicitly, which is the point — the
`GradedRing` instance. The hypotheses compare the first five; the `AddSubgroupClass` instances
need no hypothesis, being proofs of a proposition, and the `GradedRing` instances need none
either, by `AlgebraicGeometry.Proj.gradedRing_eq`.

Stating it this way is what lets the degree-`d` open of a restricted graded algebra be compared
with the degree-`d` open of the algebra over the image open: see
`Stacks.AlgebraicGeometry.RelativeProjBridge.SheafGradedAlgebra.restrict_ι_degreeOpen_toScheme`
and the implementation notes of this file. -/
theorem degreeOpen_toScheme_congr {σ₁ σ₂ : Type v} {R₁ R₂ : Type u}
    [cr₁ : CommRing R₁] [cr₂ : CommRing R₂] [sl₁ : SetLike σ₁ R₁] [sl₂ : SetLike σ₂ R₂]
    [asc₁ : AddSubgroupClass σ₁ R₁] [asc₂ : AddSubgroupClass σ₂ R₂]
    (𝒜 : ℕ → σ₁) (ℬ : ℕ → σ₂) (i : GradedRing 𝒜) (j : GradedRing ℬ)
    (hR : R₁ = R₂) (hσ : σ₁ = σ₂) (hcr : HEq cr₁ cr₂) (hsl : HEq sl₁ sl₂) (h𝒜 : HEq 𝒜 ℬ)
    (d : ℕ) :
    (@AlgebraicGeometry.Proj.degreeOpen σ₁ R₁ cr₁ sl₁ asc₁ 𝒜 i d).toScheme
      = (@AlgebraicGeometry.Proj.degreeOpen σ₂ R₂ cr₂ sl₂ asc₂ ℬ j d).toScheme := by
  subst hR
  subst hσ
  obtain rfl := eq_of_heq hcr
  obtain rfl := eq_of_heq hsl
  obtain rfl := eq_of_heq h𝒜
  obtain rfl := gradedRing_eq i j
  rfl

/-- **The congruence for `AlgebraicGeometry.Proj.degreeOpen` along an equality of indices**, for
a family of graded rings indexed by a type: the degree-`d` opens at two equal indices are the
same scheme.

This is the half of the identification that moves `A.grading (U.ι ''ᵁ ⊤)` to `A.grading U`, where
nothing has to be unfolded and `subst` does all the work. -/
theorem degreeOpen_toScheme_congr_index {ι : Type*} {σ : ι → Type v} {R : ι → Type u}
    [∀ a, CommRing (R a)] [∀ a, SetLike (σ a) (R a)] [∀ a, AddSubgroupClass (σ a) (R a)]
    (𝒜 : ∀ a, ℕ → σ a) [∀ a, GradedRing (𝒜 a)] {a b : ι} (h : a = b) (d : ℕ) :
    (AlgebraicGeometry.Proj.degreeOpen (𝒜 a) d).toScheme
      = (AlgebraicGeometry.Proj.degreeOpen (𝒜 b) d).toScheme := by
  subst h; rfl

end AlgebraicGeometry.Proj

namespace Stacks.AlgebraicGeometry.RelativeProjBridge

namespace SheafGradedAlgebra

variable {S : Scheme.{u}} (A : SheafGradedAlgebra S)

/-! ### The five cheap identifications the congruence consumes

Each is `rfl`, and each is a separate declaration so that it gets its own heartbeat budget; see
the implementation notes. -/

/-- The graded ring of global sections of `A|_U` is the graded ring of sections of `A` over the
image of `⊤`. -/
theorem restrict_ι_sectionRing_image (U : S.Opens) :
    (A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)
      = A.sectionRing (U.ι ''ᵁ (⊤ : U.toScheme.Opens)) := rfl

/-- The carriers of the two gradings are the same type of additive subgroups. -/
theorem restrict_ι_addSubgroup_eq (U : S.Opens) :
    (AddSubgroup ((A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)) : Type u)
      = AddSubgroup (A.sectionRing (U.ι ''ᵁ (⊤ : U.toScheme.Opens))) := rfl

/-- The two `CommRing` structures on the graded ring of sections agree. -/
theorem restrict_ι_commRing_heq (U : S.Opens) :
    HEq (inferInstance : CommRing ((A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)))
      (inferInstance : CommRing (A.sectionRing (U.ι ''ᵁ (⊤ : U.toScheme.Opens)))) := HEq.rfl

/-- The two `SetLike` structures on the additive subgroups of the graded ring of sections
agree. -/
theorem restrict_ι_setLike_heq (U : S.Opens) :
    HEq (inferInstance :
        SetLike (AddSubgroup ((A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)))
          ((A.restrict U.ι).sectionRing (⊤ : U.toScheme.Opens)))
      (inferInstance :
        SetLike (AddSubgroup (A.sectionRing (U.ι ''ᵁ (⊤ : U.toScheme.Opens))))
          (A.sectionRing (U.ι ''ᵁ (⊤ : U.toScheme.Opens)))) := HEq.rfl

/-- `SheafGradedAlgebra.restrict_grading` at the inclusion of an open subscheme and `⊤`, as a
heterogeneous equality. -/
theorem restrict_ι_grading_heq (U : S.Opens) :
    HEq ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens))
      (A.grading (U.ι ''ᵁ (⊤ : U.toScheme.Opens))) := HEq.rfl

/-! ### The identification -/

/-- **The degree-`d` open of the graded ring of global sections of `A|_U` is the degree-`d` open
of the graded ring of sections of `A` over the image of `⊤`**, as schemes. The restriction half
of the identification: the two gradings are equal by
`...SheafGradedAlgebra.restrict_grading`, and `AlgebraicGeometry.Proj.degreeOpen_toScheme_congr`
transports the degree-`d` open along that equality without ever comparing the two `GradedRing`
instances. -/
theorem restrict_ι_degreeOpen_toScheme_image (U : S.Opens) (d : ℕ) :
    (AlgebraicGeometry.Proj.degreeOpen
        ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) d).toScheme
      = (AlgebraicGeometry.Proj.degreeOpen
        (A.grading (U.ι ''ᵁ (⊤ : U.toScheme.Opens))) d).toScheme :=
  AlgebraicGeometry.Proj.degreeOpen_toScheme_congr _ _ _ _ (restrict_ι_sectionRing_image A U)
    (restrict_ι_addSubgroup_eq A U) (restrict_ι_commRing_heq A U) (restrict_ι_setLike_heq A U)
    (restrict_ι_grading_heq A U) d

/-- **The degree-`d` open of the graded ring of global sections of `A|_U` is the degree-`d` open
of the graded ring of sections of `A` over `U`**, as schemes.

This is the identification a chart-wise argument on a relative homogeneous spectrum needs: the
affine-base statements of [Stacks, Tag 01NU] speak of the left-hand side, the chart of the
relative Proj over `U` is a morphism out of `Proj (A.grading U)`, and the two degree-`d` opens
are the same scheme. The restriction half is
`restrict_ι_degreeOpen_toScheme_image` and the image half is
`AlgebraicGeometry.Proj.degreeOpen_toScheme_congr_index` at
`AlgebraicGeometry.Scheme.Opens.ι_image_top`. -/
theorem restrict_ι_degreeOpen_toScheme (U : S.Opens) (d : ℕ) :
    (AlgebraicGeometry.Proj.degreeOpen
        ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) d).toScheme
      = (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).toScheme :=
  (restrict_ι_degreeOpen_toScheme_image A U d).trans
    (AlgebraicGeometry.Proj.degreeOpen_toScheme_congr_index (fun W : S.Opens => A.grading W)
      U.ι_image_top d)

/-! ### The identification on morphisms -/

/-- The bijection on morphisms out of a test scheme induced by an equality of schemes:
postcomposition with `CategoryTheory.eqToHom`. -/
def homEquivOfSchemeEq {X Y : Scheme.{u}} (h : X = Y) (T : Scheme.{u}) : (T ⟶ X) ≃ (T ⟶ Y) where
  toFun φ := φ ≫ eqToHom h
  invFun φ := φ ≫ eqToHom h.symm
  left_inv φ := by subst h; simp
  right_inv φ := by subst h; simp

/-- The bijection `homEquivOfSchemeEq h T` sends `φ` to `φ ≫ eqToHom h`. -/
@[simp] theorem homEquivOfSchemeEq_apply {X Y : Scheme.{u}} (h : X = Y) (T : Scheme.{u})
    (φ : T ⟶ X) : homEquivOfSchemeEq h T φ = φ ≫ eqToHom h := rfl

/-- The bijection induced by an equality of schemes is natural in the test scheme. -/
theorem homEquivOfSchemeEq_comp {X Y : Scheme.{u}} (h : X = Y) {T T' : Scheme.{u}} (g : T' ⟶ T)
    (φ : T ⟶ X) :
    homEquivOfSchemeEq h T' (g ≫ φ) = g ≫ homEquivOfSchemeEq h T φ :=
  (Category.assoc g φ (eqToHom h)).symm

/-- **The morphisms into the degree-`d` open of `A|_U` are the morphisms into the degree-`d` open
of `A` over `U`**, naturally in the test scheme (`restrictDegreeOpenHomEquiv_comp`). -/
def restrictDegreeOpenHomEquiv (U : S.Opens) (d : ℕ) (T : Scheme.{u}) :
    (T ⟶ (AlgebraicGeometry.Proj.degreeOpen
        ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) d).toScheme)
      ≃ (T ⟶ (AlgebraicGeometry.Proj.degreeOpen (A.grading U) d).toScheme) :=
  homEquivOfSchemeEq (restrict_ι_degreeOpen_toScheme A U d) T

/-- The bijection of `restrictDegreeOpenHomEquiv` is natural in the test scheme. -/
theorem restrictDegreeOpenHomEquiv_comp (U : S.Opens) (d : ℕ) {T T' : Scheme.{u}} (g : T' ⟶ T)
    (φ : T ⟶ (AlgebraicGeometry.Proj.degreeOpen
      ((A.restrict U.ι).grading (⊤ : U.toScheme.Opens)) d).toScheme) :
    restrictDegreeOpenHomEquiv A U d T' (g ≫ φ) = g ≫ restrictDegreeOpenHomEquiv A U d T φ :=
  homEquivOfSchemeEq_comp _ g φ

end SheafGradedAlgebra

end Stacks.AlgebraicGeometry.RelativeProjBridge

end
