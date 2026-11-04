module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpace
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# `Proj` of a polynomial ring, and reindexing the variables

`AlgebraicGeometry.Proj` of a polynomial ring graded by total degree is projective space, but the
variables come indexed by whatever type was convenient upstream.  This file proves that a
bijection of index types induces an isomorphism of the two `Proj`s, and names the `Proj` itself so
that the comparison can be stated with no local instance in sight.

The use is the Segre embedding: the Segre presentation of
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/SegrePresentation.lean` has its variables indexed
by `X × Y`, while Stacks Tag 01WD asks for a morphism to
`AlgebraicGeometry.projectiveSpaceAtUniverse (n * m + n + m)`, whose variables are indexed by
`Fin (n * m + n + m + 1)`.  Reindexing along `finProdFinEquiv` together with the arithmetic
identity `(n + 1) * (m + 1) = n * m + n + m + 1` closes that gap.

## What is proved, and the route

* `Stacks.AlgebraicGeometry.ProjPoly.renameGradedHom R e` is `MvPolynomial.rename e` as a graded
  ring homomorphism, for an arbitrary map `e` of index types; it respects the grading by
  `MvPolynomial.IsHomogeneous.rename_isHomogeneous`, which needs no hypothesis on `e` at all.
  `renameGradedHom_comp` and `renameGradedHom_id` are its functoriality.

* `Stacks.AlgebraicGeometry.ProjPoly.irrelevant_le_map_renameGradedHom` is the hypothesis
  `AlgebraicGeometry.Proj.map` requires, proved for a bijection of index types: a homogeneous
  element of positive degree in the target is the image of the one obtained by renaming back.
  Applying it to a bijection and to its inverse covers both directions.

* `Stacks.AlgebraicGeometry.ProjPoly.projIsoOfEquiv R e` is the resulting isomorphism of `Proj`s,
  built from `AlgebraicGeometry.Proj.map` in both directions, the two composites being identities
  by `AlgebraicGeometry.Proj.map_comp` and `AlgebraicGeometry.Proj.map_id`.  This is the same
  construction as `AlgebraicGeometry.projectiveSpaceIntegralIso`, which does it for a change of
  coefficient ring rather than of index type.

* `Stacks.AlgebraicGeometry.ProjPoly.projIsoULiftIndex R n` is the same isomorphism for the one
  **universe-crossing** reindexing that is available: stripping a `ULift` from the index type,
  `Proj R[T_{ULift (Fin (n+1))}] ≅ Proj R[T_{Fin (n+1)}]` at `R : Type u`, where both polynomial
  rings are visibly `Type u`.  This is what compares the graded ring of homogeneous sections of
  `Sym(𝒪_X^{n+1})` over an open, whose variables are indexed in the module universe, with
  `Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading`.

* `Stacks.AlgebraicGeometry.ProjPoly.projPoly R ι` names that `Proj`, and
  `Stacks.AlgebraicGeometry.ProjPoly.projPoly_fin` records that at `ULift.{u} ℤ` with the
  variables indexed by `Fin (k + 1)` it is `AlgebraicGeometry.projectiveSpaceAtUniverse k`, by
  reflexivity.  `Stacks.AlgebraicGeometry.ProjPoly.segreTargetIso` is the reindexing the Segre
  embedding needs:
  `projPoly R (Fin (n + 1) × Fin (m + 1)) ≅ projectiveSpaceAtUniverse (n * m + n + m)`.

## Implementation notes

The grading of a polynomial ring is `MvPolynomial.gradedAlgebra`, an abbreviation rather than an
instance, so it has to be supplied at each use; and a local instance introduced in a *statement*
does not survive into the proof of that statement.  The file is therefore in two layers.  The
general results take the grading as an ordinary instance **binder**, so that every statement
carries it and every proof has it.  Only the final specialisations, whose types must mention
`AlgebraicGeometry.projectiveSpaceAtUniverse`, supply the canonical grading, and they supply it in
the *body* of a definition, where a local instance is just a term.  `projPoly` exists to give the
left-hand side of those specialisations a name, so that the comparison with
`projectiveSpaceAtUniverse` is an equation between two named objects rather than between two
`Proj`s carrying local instances.

**Where the universes have to agree, and where they do not.** `renameGradedHom` and
`irrelevant_le_map_renameGradedHom` are purely algebraic and take `ι` and `κ` in **independent**
universes.  `projIsoOfEquiv` cannot: an isomorphism of `Proj`s is a morphism of schemes in the
universe of the ring, so it would need its two sides in `Scheme.{max u v₁}` and
`Scheme.{max u v₂}`, and that constraint cannot be imposed.  It therefore keeps `ι` and `κ` in one
universe, which costs nothing in the Segre application, where both index types are in `Type`.

`projIsoULiftIndex` is the universe-crossing case that is nevertheless available, because it is
stated at index types for which the two universes visibly coincide rather than by generalising
`projIsoOfEquiv`.

## What is not done

Nothing here is about the Segre product; this file only moves between index types.  In particular
the isomorphism recorded as the handover in
`StacksFrontier/AlgebraicGeometry/SegreEmbedding/Reduction.lean` — `Proj` of the Segre product
compared with a product of projective spaces — is not approached.

`projIsoOfEquiv` is not shown to be functorial in `e`, and no compatibility of it with the
structure morphism to `Spec` of the degree-zero part is proved; neither is needed downstream.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory MvPolynomial

namespace Stacks.AlgebraicGeometry.ProjPoly

universe t w v u

/-! ### Renaming the variables -/

section General

variable (R : Type u) [CommRing R] {ι : Type v} {κ : Type w}

/-- `MvPolynomial.rename` as a homomorphism of graded rings.  No hypothesis on `e` is needed:
renaming variables does not change the total degree of a monomial. -/
public noncomputable def renameGradedHom (e : ι → κ) :
    MvPolynomial.homogeneousSubmodule ι R →+*ᵍ MvPolynomial.homogeneousSubmodule κ R where
  toRingHom := (MvPolynomial.rename e).toRingHom
  map_mem hx := MvPolynomial.IsHomogeneous.rename_isHomogeneous hx

/-- `renameGradedHom R e` acts as `MvPolynomial.rename e`. -/
@[simp] public theorem renameGradedHom_apply (e : ι → κ) (p : MvPolynomial ι R) :
    renameGradedHom R e p = MvPolynomial.rename e p :=
  rfl

/-- Renaming along `e` and then along `f` is renaming along `f ∘ e`. -/
public theorem renameGradedHom_comp {μ : Type t} (e : ι → κ) (f : κ → μ) :
    (renameGradedHom R f).comp (renameGradedHom R e) = renameGradedHom R (f ∘ e) :=
  GradedRingHom.ext fun p => by simp [MvPolynomial.rename_rename]

/-- Renaming along the identity is the identity graded ring homomorphism. -/
public theorem renameGradedHom_id :
    renameGradedHom R (id : ι → ι) = GradedRingHom.id _ :=
  GradedRingHom.ext fun p => by simp

variable [GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R)]
  [GradedAlgebra (MvPolynomial.homogeneousSubmodule κ R)]

/-- The hypothesis of `AlgebraicGeometry.Proj.map`, for a bijection of index types.  Applying it
to a bijection and to its inverse gives both directions. -/
public theorem irrelevant_le_map_renameGradedHom (e : ι ≃ κ) :
    HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule κ R) ≤
      (HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule ι R)).map
        (renameGradedHom R (e : ι → κ)) := by
  apply (HomogeneousIdeal.irrelevant_le _).2
  intro i hi x hx
  have hy : MvPolynomial.rename (e.symm : κ → ι) x ∈
      MvPolynomial.homogeneousSubmodule ι R i :=
    MvPolynomial.IsHomogeneous.rename_isHomogeneous hx
  have hxy : renameGradedHom R (e : ι → κ) (MvPolynomial.rename (e.symm : κ → ι) x) = x := by
    rw [renameGradedHom_apply, MvPolynomial.rename_rename]
    simp
  rw [← hxy]
  exact Ideal.mem_map_of_mem _ (HomogeneousIdeal.mem_irrelevant_of_mem _ hi hy)

end General

section OneUniverse

variable (R : Type u) [CommRing R] {ι κ : Type v}
  [GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R)]
  [GradedAlgebra (MvPolynomial.homogeneousSubmodule κ R)]

/-- A bijection of index types induces an isomorphism of the two `Proj`s. -/
public noncomputable def projIsoOfEquiv (e : ι ≃ κ) :
    AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule ι R) ≅
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule κ R) := by
  refine ⟨AlgebraicGeometry.Proj.map (renameGradedHom R (e.symm : κ → ι))
      (irrelevant_le_map_renameGradedHom R e.symm),
    AlgebraicGeometry.Proj.map (renameGradedHom R (e : ι → κ))
      (irrelevant_le_map_renameGradedHom R e), ?_, ?_⟩
  · have hcomp : ((e.symm : κ → ι) ∘ (e : ι → κ)) = id := funext e.symm_apply_apply
    have h : (renameGradedHom R (e.symm : κ → ι)).comp (renameGradedHom R (e : ι → κ)) =
        GradedRingHom.id (MvPolynomial.homogeneousSubmodule ι R) := by
      rw [renameGradedHom_comp, hcomp, renameGradedHom_id]
    exact (AlgebraicGeometry.Proj.map_comp (renameGradedHom R (e : ι → κ))
      (renameGradedHom R (e.symm : κ → ι)) _ _).symm.trans
      (by simp only [h, AlgebraicGeometry.Proj.map_id])
  · have hcomp : ((e : ι → κ) ∘ (e.symm : κ → ι)) = id := funext e.apply_symm_apply
    have h : (renameGradedHom R (e : ι → κ)).comp (renameGradedHom R (e.symm : κ → ι)) =
        GradedRingHom.id (MvPolynomial.homogeneousSubmodule κ R) := by
      rw [renameGradedHom_comp, hcomp, renameGradedHom_id]
    exact (AlgebraicGeometry.Proj.map_comp (renameGradedHom R (e.symm : κ → ι))
      (renameGradedHom R (e : ι → κ)) _ _).symm.trans
      (by simp only [h, AlgebraicGeometry.Proj.map_id])

end OneUniverse

/-! ### Reindexing across universes: stripping a `ULift` from the index type -/

section ULiftIndex

variable (R : Type u) [CommRing R] (n : ℕ)

attribute [local instance] MvPolynomial.gradedAlgebra

/-- **The variables may be reindexed across universes, in the one case that matters: stripping a
`ULift`.** `Stacks.AlgebraicGeometry.ProjPoly.projIsoOfEquiv` cannot do this — it needs both index
types in one universe, since otherwise the two `Proj`s are objects of `Scheme.{max u v₁}` and
`Scheme.{max u v₂}` and there is no way to ask Lean for an isomorphism between them. Stated at
`R : Type u` with the index types `ULift.{u} (Fin (n + 1))` and `Fin (n + 1)` there is no
difficulty at all: both polynomial rings are visibly `Type u`, because `max u u` and `max 0 u`
are both `u`.

This is the comparison that identifies the graded ring of homogeneous sections of
`Sym(𝒪_X^{n+1})` over an open — whose variables are indexed in the module universe, which is
where `SheafOfModules.free` needs them — with
`Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading`, whose variables are indexed by
`Fin (n + 1)`. -/
public noncomputable def projIsoULiftIndex :
    AlgebraicGeometry.Proj
        (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) R) ≅
      AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) := by
  refine ⟨AlgebraicGeometry.Proj.map
      (renameGradedHom R ((Equiv.ulift.{u, 0}).symm : Fin (n + 1) → ULift.{u} (Fin (n + 1))))
      (irrelevant_le_map_renameGradedHom R (Equiv.ulift.{u, 0}).symm),
    AlgebraicGeometry.Proj.map
      (renameGradedHom R (Equiv.ulift.{u, 0} : ULift.{u} (Fin (n + 1)) → Fin (n + 1)))
      (irrelevant_le_map_renameGradedHom R Equiv.ulift.{u, 0}), ?_, ?_⟩
  · have h : (renameGradedHom R
          ((Equiv.ulift.{u, 0}).symm : Fin (n + 1) → ULift.{u} (Fin (n + 1)))).comp
        (renameGradedHom R (Equiv.ulift.{u, 0} : ULift.{u} (Fin (n + 1)) → Fin (n + 1))) =
        GradedRingHom.id
          (MvPolynomial.homogeneousSubmodule (ULift.{u} (Fin (n + 1))) R) := by
      rw [renameGradedHom_comp,
        show (((Equiv.ulift.{u, 0}).symm : Fin (n + 1) → ULift.{u} (Fin (n + 1))) ∘
            (Equiv.ulift.{u, 0} : ULift.{u} (Fin (n + 1)) → Fin (n + 1))) = id from
          funext (Equiv.ulift.{u, 0}).symm_apply_apply,
        renameGradedHom_id]
    exact (AlgebraicGeometry.Proj.map_comp
      (renameGradedHom R (Equiv.ulift.{u, 0} : ULift.{u} (Fin (n + 1)) → Fin (n + 1)))
      (renameGradedHom R ((Equiv.ulift.{u, 0}).symm : Fin (n + 1) → ULift.{u} (Fin (n + 1))))
      _ _).symm.trans (by simp only [h, AlgebraicGeometry.Proj.map_id])
  · have h : (renameGradedHom R
          (Equiv.ulift.{u, 0} : ULift.{u} (Fin (n + 1)) → Fin (n + 1))).comp
        (renameGradedHom R
          ((Equiv.ulift.{u, 0}).symm : Fin (n + 1) → ULift.{u} (Fin (n + 1)))) =
        GradedRingHom.id (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) R) := by
      rw [renameGradedHom_comp,
        show ((Equiv.ulift.{u, 0} : ULift.{u} (Fin (n + 1)) → Fin (n + 1)) ∘
            ((Equiv.ulift.{u, 0}).symm : Fin (n + 1) → ULift.{u} (Fin (n + 1)))) = id from
          funext (Equiv.ulift.{u, 0}).apply_symm_apply,
        renameGradedHom_id]
    exact (AlgebraicGeometry.Proj.map_comp
      (renameGradedHom R ((Equiv.ulift.{u, 0}).symm : Fin (n + 1) → ULift.{u} (Fin (n + 1))))
      (renameGradedHom R (Equiv.ulift.{u, 0} : ULift.{u} (Fin (n + 1)) → Fin (n + 1)))
      _ _).symm.trans (by simp only [h, AlgebraicGeometry.Proj.map_id])

/-- The forward map of `projIsoULiftIndex` is induced by renaming along `Equiv.ulift.symm`. -/
@[simp] public theorem projIsoULiftIndex_hom :
    (projIsoULiftIndex R n).hom = AlgebraicGeometry.Proj.map
      (renameGradedHom R ((Equiv.ulift.{u, 0}).symm : Fin (n + 1) → ULift.{u} (Fin (n + 1))))
      (irrelevant_le_map_renameGradedHom R (Equiv.ulift.{u, 0}).symm) :=
  rfl

/-- The inverse map of `projIsoULiftIndex` is induced by renaming along `Equiv.ulift`. -/
@[simp] public theorem projIsoULiftIndex_inv :
    (projIsoULiftIndex R n).inv = AlgebraicGeometry.Proj.map
      (renameGradedHom R (Equiv.ulift.{u, 0} : ULift.{u} (Fin (n + 1)) → Fin (n + 1)))
      (irrelevant_le_map_renameGradedHom R Equiv.ulift.{u, 0}) :=
  rfl

end ULiftIndex

/-! ### The named `Proj`, and the reindexing the Segre embedding needs -/

variable (R : Type u) [CommRing R]

/-- `Proj` of the polynomial ring on the index type `ι`, graded by total degree.  The canonical
grading is supplied here, in the body, so that statements about this object carry no local
instance. -/
public noncomputable def projPoly (ι : Type v) : Scheme.{max v u} :=
  letI : GradedAlgebra (MvPolynomial.homogeneousSubmodule ι R) := MvPolynomial.gradedAlgebra
  AlgebraicGeometry.Proj (MvPolynomial.homogeneousSubmodule ι R)

/-- At the canonical universe copy of the integers, with the variables indexed by `Fin (k + 1)`,
this is the integral model of projective `k`-space. -/
public theorem projPoly_fin (k : ℕ) :
    projPoly (ULift.{u} ℤ) (Fin (k + 1)) = projectiveSpaceAtUniverse.{u} k :=
  rfl

/-- The variables `z_{ij}` of the Segre presentation, indexed by pairs, reindexed by
`Fin (n * m + n + m + 1)`: there are `(n + 1) * (m + 1) = n * m + n + m + 1` of them. -/
public noncomputable def finProdEquiv (n m : ℕ) :
    Fin (n + 1) × Fin (m + 1) ≃ Fin (n * m + n + m + 1) :=
  finProdFinEquiv.trans (finCongr (by ring))

/-- Reindexing the Segre presentation's variables. -/
public noncomputable def projPolyProdIso (n m : ℕ) :
    projPoly R (Fin (n + 1) × Fin (m + 1)) ≅ projPoly R (Fin (n * m + n + m + 1)) :=
  letI : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1) × Fin (m + 1)) R) :=
    MvPolynomial.gradedAlgebra
  letI : GradedAlgebra
      (MvPolynomial.homogeneousSubmodule (Fin (n * m + n + m + 1)) R) :=
    MvPolynomial.gradedAlgebra
  projIsoOfEquiv R (finProdEquiv n m)

/-- **The target of the Segre embedding.**  `Proj` of the polynomial ring on the pairs `(i, j)`,
which is where the Segre presentation lands, is the integral model of projective
`(n * m + n + m)`-space, which is what Tag 01WD asks for. -/
public noncomputable def segreTargetIso (n m : ℕ) :
    projPoly (ULift.{u} ℤ) (Fin (n + 1) × Fin (m + 1)) ≅
      projectiveSpaceAtUniverse.{u} (n * m + n + m) :=
  projPolyProdIso (ULift.{u} ℤ) n m ≪≫ eqToIso (projPoly_fin (n * m + n + m))

end Stacks.AlgebraicGeometry.ProjPoly

end
