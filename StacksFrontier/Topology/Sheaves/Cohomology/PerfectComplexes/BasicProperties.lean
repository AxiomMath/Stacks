module

public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.SheafLevel
import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas

/-!
# Perfect complexes on a ringed space

A complex of `𝒪_X`-modules on a ringed space `X` is *perfect* if `X` has an open covering on
each member of which the complex is quasi-isomorphic to a strictly perfect complex; an object
of the derived category of `𝒪_X`-modules is perfect if some perfect complex represents it.

## Main definitions

* `AlgebraicGeometry.RingedSpace.IsPerfectComplex`: a complex of `𝒪_X`-modules is perfect.
* `AlgebraicGeometry.RingedSpace.IsPerfect`: an object of the derived category of
  `𝒪_X`-modules is perfect.

## Main results

* `AlgebraicGeometry.RingedSpace.isPerfectComplex_iff` and
  `AlgebraicGeometry.RingedSpace.isPerfect_iff` unfold the two definitions.
* `AlgebraicGeometry.RingedSpace.isPerfectComplex_of_isStrictlyPerfect`: a strictly perfect
  complex is perfect.
* `AlgebraicGeometry.RingedSpace.isPerfectComplex_of_forall_isZero` and
  `AlgebraicGeometry.RingedSpace.isPerfect_of_isZero`: a complex with zero terms is perfect, and
  a zero object of the derived category is perfect.
* `AlgebraicGeometry.RingedSpace.IsPerfectComplex.of_iso` and
  `AlgebraicGeometry.RingedSpace.IsPerfect.of_iso`: both predicates transport along an
  isomorphism.
* `AlgebraicGeometry.RingedSpace.IsPerfectComplex.isPerfect`: a perfect complex represents a
  perfect object of the derived category.
* `AlgebraicGeometry.RingedSpace.IsPerfectComplex.isPseudoCoherentComplex` and
  `AlgebraicGeometry.RingedSpace.IsPerfect.isPseudoCoherent`: a perfect complex is
  pseudo-coherent, and so is the object it represents.

## References

* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- A complex of `𝒪_X`-modules is *perfect* if there is an open covering of `X` such that on
each member of the covering the restricted complex receives a quasi-isomorphism from a
strictly perfect complex. -/
public def IsPerfectComplex (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ) : Prop :=
  ∃ (I : Type u) (U : I → Opens X.carrier), iSup U = ⊤ ∧
    ∀ i : I, ∃ P : CochainComplex
        (StrictlyPerfect.OXMod.{u, u} (X.restrict (U i).isOpenEmbedding)) ℤ,
      StrictlyPerfect.IsStrictlyPerfect P ∧
        ∃ f : P ⟶ restrictComplex E (U i), QuasiIso f

/-- A complex of `𝒪_X`-modules is perfect exactly when some open covering of `X` has strictly
perfect complexes quasi-isomorphic to the restrictions of the complex. -/
public theorem isPerfectComplex_iff (E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ) :
    IsPerfectComplex E ↔
      ∃ (I : Type u) (U : I → Opens X.carrier), iSup U = ⊤ ∧
        ∀ i : I, ∃ P : CochainComplex
            (StrictlyPerfect.OXMod.{u, u} (X.restrict (U i).isOpenEmbedding)) ℤ,
          StrictlyPerfect.IsStrictlyPerfect P ∧
            ∃ f : P ⟶ restrictComplex E (U i), QuasiIso f :=
  Iff.rfl

/-- An object of the derived category of `𝒪_X`-modules is *perfect* if it is represented by a
perfect complex. -/
public def IsPerfect [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)) : Prop :=
  ∃ E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ,
    IsPerfectComplex E ∧ Nonempty (DerivedCategory.Q.obj E ≅ K)

/-- An object of the derived category of `𝒪_X`-modules is perfect exactly when some perfect
complex represents it. -/
public theorem isPerfect_iff [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    (K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)) :
    IsPerfect K ↔
      ∃ E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ,
        IsPerfectComplex E ∧ Nonempty (DerivedCategory.Q.obj E ≅ K) :=
  Iff.rfl

end AlgebraicGeometry.RingedSpace

end

/-! ### Basic properties of perfect complexes -/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- A strictly perfect complex of `𝒪_X`-modules is perfect. -/
public theorem isPerfectComplex_of_isStrictlyPerfect
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ}
    (h : StrictlyPerfect.IsStrictlyPerfect E) : IsPerfectComplex E :=
  ⟨PUnit.{u + 1}, fun _ => ⊤, iSup_const, fun _ =>
    ⟨restrictComplex E ⊤, isStrictlyPerfect_restrictComplex h ⊤, 𝟙 _, inferInstance⟩⟩

/-- A complex of `𝒪_X`-modules all of whose terms are zero is perfect. -/
public theorem isPerfectComplex_of_forall_isZero
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ}
    (h : ∀ i, Limits.IsZero (E.X i)) : IsPerfectComplex E :=
  isPerfectComplex_of_isStrictlyPerfect (StrictlyPerfect.isStrictlyPerfect_of_forall_isZero h)

/-- Perfectness of a complex of `𝒪_X`-modules transports along an isomorphism of complexes. -/
public theorem IsPerfectComplex.of_iso
    {E E' : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ}
    (h : IsPerfectComplex E) (e : E ≅ E') : IsPerfectComplex E' := by
  obtain ⟨I, U, hU, hcov⟩ := h
  refine ⟨I, U, hU, fun i => ?_⟩
  obtain ⟨P, hP, α, hα⟩ := hcov i
  have hiso : restrictComplex E (U i) ≅ restrictComplex E' (U i) :=
    ((restrictModules X (U i)).mapHomologicalComplex (ComplexShape.up ℤ)).mapIso e
  exact ⟨P, hP, α ≫ hiso.hom, inferInstance⟩

/-- A perfect complex of `𝒪_X`-modules represents a perfect object of the derived category. -/
public theorem IsPerfectComplex.isPerfect
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ} (h : IsPerfectComplex E) :
    IsPerfect (DerivedCategory.Q.obj E) :=
  ⟨E, h, ⟨Iso.refl _⟩⟩

/-- The object of the derived category of `𝒪_X`-modules represented by a strictly perfect complex
is perfect. -/
public theorem isPerfect_Q_obj_of_isStrictlyPerfect
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    {P : CochainComplex (StrictlyPerfect.OXMod.{u, u} X) ℤ}
    (h : StrictlyPerfect.IsStrictlyPerfect P) : IsPerfect (DerivedCategory.Q.obj P) :=
  (isPerfectComplex_of_isStrictlyPerfect h).isPerfect

/-- Perfectness of an object of the derived category of `𝒪_X`-modules transports along an
isomorphism. -/
public theorem IsPerfect.of_iso [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    {K K' : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)} (h : IsPerfect K) (e : K ≅ K') :
    IsPerfect K' := by
  obtain ⟨E, hE, ⟨f⟩⟩ := h
  exact ⟨E, hE, ⟨f.trans e⟩⟩

open scoped ZeroObject in
/-- A zero object of the derived category of `𝒪_X`-modules is perfect. -/
public theorem isPerfect_of_isZero [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u} X)]
    {K : DerivedCategory (StrictlyPerfect.OXMod.{u, u} X)} (h : Limits.IsZero K) :
    IsPerfect K :=
  (isPerfect_Q_obj_of_isStrictlyPerfect (X := X)
    (StrictlyPerfect.isStrictlyPerfect_of_forall_isZero fun i =>
      (HomologicalComplex.eval _ _ i).isZero_obj (Limits.isZero_zero _))).of_iso
    ((DerivedCategory.Q.isZero_obj (Limits.isZero_zero _)).iso h)

/-- A perfect complex of `𝒪_X`-modules is `m`-pseudo-coherent for every `m`. -/
public theorem IsPerfectComplex.isPseudoCoherentComplex
    {E : CochainComplex (StrictlyPerfect.OXMod.{u, u, u} X) ℤ} (h : IsPerfectComplex E) :
    IsPseudoCoherentComplex E := by
  obtain ⟨I, U, hU, hcov⟩ := h
  intro m x
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU ▸ trivial : x ∈ iSup U)
  obtain ⟨P, hP, α, hα⟩ := hcov i
  exact ⟨U i, hi, P, hP, α, fun _ _ => inferInstance, inferInstance⟩

/-- A perfect object of the derived category of `𝒪_X`-modules is pseudo-coherent. -/
public theorem IsPerfect.isPseudoCoherent
    [HasDerivedCategory.{d} (StrictlyPerfect.OXMod.{u, u, u} X)]
    {K : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u} X)} (h : IsPerfect K) :
    IsPseudoCoherent K := by
  obtain ⟨E, hE, hiso⟩ := h
  exact ⟨E, hE.isPseudoCoherentComplex, hiso⟩

end AlgebraicGeometry.RingedSpace

end
