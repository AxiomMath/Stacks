module

public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.OpenLift.BiprodShiftLift
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.NoDeformations.DiagonalFibreVanishing
public import StacksFrontier.AlgebraicGeometry.Perfect.SupportedBiprodShiftLift

/-!
# Lifting a map from a supported perfect object off a quasi-compact open of `Spec A`

Let `X = Spec A`, let `T ⊆ X` be closed with `X ∖ T` quasi-compact, let `U ⊆ X` be a
quasi-compact open and let `E` be an object of `D(𝒪_X)` with quasi-coherent cohomology. For every
perfect object `F` of `D(𝒪_U)` whose cohomology is supported on `T ∩ U` and every map
`α : F ⟶ E|_U`, there is a perfect object `R` of `D(𝒪_X)` whose cohomology is supported on `T`,
a map `β : R ⟶ E`, and an isomorphism `R|_U ≅ F ⊕ F[1]` carrying `β|_U` to the projection onto
`F` followed by `α`.

This is the affine case of [Stacks, Tag 09IM], in the *strengthened* form the iteration of
[Stacks, Tag 09IN] needs: the conclusion names an isomorphism `R|_U ≅ F ⊕ F[1]` and not merely a
retraction of `F` off `R|_U`, and the compatibility says that `β|_U` is, in the coordinates of
that splitting, the projection followed by `α` — so that the second summand maps to `E` by zero.
With only the retraction and the weak compatibility the split-lift tower of
`DerivedCategory.exists_approximatesFrom_of_splitLiftOracle` stalls after one stage.

The affine case is where the strengthened form costs nothing: it falls out of the two inputs.

## The two inputs

* [Stacks, Tag 08EK] at `Spec A`,
  `Stacks.Perfect.SupportedBiprodShift.exists_isPerfect_supported_biprod_shift_iso_restrict`,
  produces a perfect `P` on `X` supported on `T` with `F ⊕ F[1] ≅ P|_U`. It knows nothing about
  `E`.
* [Stacks, Tag 08EH] in the open-subspace model,
  `Stacks.DerivedQCoh.OpenLift.exists_roof_restrictModules`, extends the map
  `P|_U ≅ F ⊕ F[1] ⟶ F ⟶ E|_U` to a map defined on all of `X` after replacing `P` by
  `Iₑ ⊗^𝐋 P` for a perfect stage `Iₑ` of the derived Koszul system — a replacement that does not
  change the restriction to `U`, because the comparison `Iₑ ⊗^𝐋 P ⟶ P` restricts to an
  isomorphism there.

So `R = Iₑ ⊗^𝐋 P`, and the two clauses carried over from `P` are: perfectness, by
[Stacks, Tag 09J5], and the support, because tensoring with anything preserves it.

## Main results

* `Stacks.Perfect.SupportedLiftAffineSpec.cohomologySupportedOn_derivedTensorSite_of_right`:
  tensoring preserves cohomological support, for the tensor product [Stacks, Tag 08EH] produces.
* `Stacks.Perfect.SupportedLiftAffineSpec.exists_isPerfect_supported_hom_biprod_shift_iso_restrict`:
  the statement above.
* `Stacks.Perfect.SupportedLiftAffineSpec.exists_roof_of_isCompact`: [Stacks, Tag 08EH] at an
  arbitrary quasi-compact open of `Spec A`, with the middle object existentially quantified — so
  the statement names no tensor product and transports along an isomorphism.
* `Stacks.Perfect.SupportedLiftAffineSpec.exists_iso_of_split_and_roof`: the reshaping of a
  splitting and a roof into a splitting compatible with a map, over variable categories.

## Implementation notes

**Where the support of the tensor product comes from, and the two tensor bifunctors.**
[Stacks, Tag 08EH] produces its middle object with
`Stacks.SheafOfModules.derivedTensorProductFunctor (affineSite A)`, the derived tensor product
indexed by the ringed *site*, while
`Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_right` — the
statement that tensoring on the left by anything preserves the support of the right factor — is
about `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, the one indexed by the
structure sheaf alone. The two are distinct terms, each from its own construction made opaque with
`irreducible_def`, and `AlgebraicGeometry.RingedSite.derivedTensorFunctorIso` is the comparison.
The supported factor is the *right* one because [Stacks, Tag 08EH] puts the Koszul stage on the
left.

**`HasDerivedCategory.standard`** is a local instance at priority `10000`, as in the two modules
whose statements are consumed: without the priority a different derived-category model is
selected and those statements are then about a different category, with no error naming the
cause.

The registrations of [Stacks, Tag 08EK], [Stacks, Tag 08EH], [Stacks, Tag 09J5] and
[Stacks, Tag 09IM] are on other declarations, so no tag attribute is placed in this module.

## References

* [Stacks Project, Tag 09IM](https://stacks.math.columbia.edu/tag/09IM)
* [Stacks Project, Tag 09IN](https://stacks.math.columbia.edu/tag/09IN)
* [Stacks Project, Tag 08EK](https://stacks.math.columbia.edu/tag/08EK)
* [Stacks Project, Tag 08EH](https://stacks.math.columbia.edu/tag/08EH)
* [Stacks Project, Tag 09J5](https://stacks.math.columbia.edu/tag/09J5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Opposite
open Koszul.DerivedSystem (affineSite derivedCat unionOfBasicOpens koszulDerivedSystem
  HasQuasicoherentCohomology)

universe u

namespace Stacks.Perfect.SupportedLiftAffineSpec

attribute [local instance 10000] HasDerivedCategory.standard

variable {A : CommRingCat.{u}}

/-- **Tensoring preserves cohomological support, for the tensor product [Stacks, Tag 08EH]
produces.** If `P` is supported on `T` then so is `Iₑ ⊗^𝐋 P`, the middle object of the roof of
[Stacks, Tag 08EH].

`Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_right` is the
same statement for the tensor product indexed by the structure sheaf rather than by the ringed
site; `AlgebraicGeometry.RingedSite.derivedTensorFunctorIso` crosses between the two. -/
theorem cohomologySupportedOn_derivedTensorSite_of_right (T : Set ↥(Spec A))
    (I P : derivedCat A)
    (hP : AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Spec A).sheaf) T P) :
    AlgebraicGeometry.CohomologySupportedOn
      (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (Spec A).sheaf) T
      (((Stacks.SheafOfModules.derivedTensorProductFunctor (affineSite A)).obj I).obj P) :=
  Stacks.Cohomology.PushforwardRestriction.cohomologySupportedOn_of_iso _ T
    (((AlgebraicGeometry.RingedSite.derivedTensorFunctorIso (affineSite A)).app I).app P).symm
    (Stacks.SheafOfModules.DerivedTensorStalk.cohomologySupportedOn_derivedTensor_of_right
      (Spec A).sheaf T I P hP)

/-- `exists_roof_of_isCompact` at `U = D(f₁) ∪ ⋯ ∪ D(f_r)`. For the elaborator's budget the roof
is taken apart by `Exists.elim` rather than by `obtain` — `rcases` eliminates each component with
the goal as motive — and the two clauses about the middle object are proved as `have`s before
the conclusion is assembled; either step done the other way does not finish inside the default
heartbeat budget here. -/
private theorem exists_roof_of_union (T : Set ↥(Spec A)) {r : ℕ} (f : Fin r → A)
    (P E : derivedCat A)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) P)
    (hPT : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing (Spec A).toRingedSpace) T P)
    (hE : HasQuasicoherentCohomology A E)
    (α : (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
        (unionOfBasicOpens f)).obj P ⟶
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace
        (unionOfBasicOpens f)).obj E) :
    ∃ (R : derivedCat A) (β : R ⟶ P) (γ : R ⟶ E),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) R ∧
        AlgebraicGeometry.CohomologySupportedOn (structureSheafRing (Spec A).toRingedSpace) T R ∧
          IsIso ((AlgebraicGeometry.RingedSpace.derivedRestrictModules
              (Spec A).toRingedSpace (unionOfBasicOpens f)).map β) ∧
            (AlgebraicGeometry.RingedSpace.derivedRestrictModules
                (Spec A).toRingedSpace (unionOfBasicOpens f)).map γ =
              (AlgebraicGeometry.RingedSpace.derivedRestrictModules
                (Spec A).toRingedSpace (unionOfBasicOpens f)).map β ≫ α := by
  have hPr : AlgebraicGeometry.RingedSpace.IsPerfect (X := (Spec A).toRingedSpace) P := hP
  have roof := Stacks.DerivedQCoh.OpenLift.exists_roof_restrictModules f P E hPr hE α
  refine roof.elim fun n hn => hn.elim fun β hβ' => hβ'.elim fun γ h => ?_
  -- Tag 09J5: the middle object of the roof is perfect.
  have hI := AlgebraicGeometry.RingedSpace.isPerfect_derivedTensorProduct (Spec A).toRingedSpace
      (AlgebraicGeometry.RingedSite.derivedTensorProductDatumOfSite (affineSite A)
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct (affineSite A))) _ P h.1 hP
  have hS := cohomologySupportedOn_derivedTensorSite_of_right T
    ((koszulDerivedSystem f).obj (op n)) P hPT
  exact ⟨_, β, γ, hI, hS, h.2.1, h.2.2⟩

/-- **[Stacks, Tag 08EH] at an arbitrary quasi-compact open, with the middle object's perfectness
and support.** For `P` perfect on `Spec A` with cohomology supported on `T`, `E` with
quasi-coherent cohomology, and a map `α : P|_U ⟶ E|_U` over a quasi-compact open `U`, there is a
roof `P ←β— R —γ→ E` with `R` perfect and supported on `T`, `β|_U` invertible and
`γ|_U = β|_U ≫ α`.

`Stacks.DerivedQCoh.OpenLift.exists_roof_restrictModules` is the roof at
`U = D(f₁) ∪ ⋯ ∪ D(f_r)`, and
`Stacks.DerivedQCoh.OpenLift.exists_unionOfBasicOpens_eq_of_isCompact` presents a quasi-compact
open that way. The two clauses about the middle object are [Stacks, Tag 09J5] and
`Stacks.Perfect.SupportedLiftAffineSpec.cohomologySupportedOn_derivedTensorSite_of_right`.

The reduction to the union form is isolated here, away from the statement below, because it
substitutes for `U` and therefore rewrites every hypothesis whose type mentions the category of
`𝒪_U`-modules: performed in the presence of the splitting `F ⊕ F[1]` and the map out of it, that
substitution does not finish inside the default heartbeat budget. -/
theorem exists_roof_of_isCompact (T : Set ↥(Spec A)) (U : (Spec A).Opens)
    (hU : IsCompact ((U : (Spec A).Opens) : Set ↥(Spec A))) (P E : derivedCat A)
    (hP : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) P)
    (hPT : AlgebraicGeometry.CohomologySupportedOn (structureSheafRing (Spec A).toRingedSpace) T P)
    (hE : HasQuasicoherentCohomology A E)
    (α : (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace U).obj P ⟶
      (AlgebraicGeometry.RingedSpace.derivedRestrictModules (Spec A).toRingedSpace U).obj E) :
    ∃ (R : derivedCat A) (β : R ⟶ P) (γ : R ⟶ E),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) R ∧
        AlgebraicGeometry.CohomologySupportedOn (structureSheafRing (Spec A).toRingedSpace) T R ∧
          IsIso ((AlgebraicGeometry.RingedSpace.derivedRestrictModules
              (Spec A).toRingedSpace U).map β) ∧
            (AlgebraicGeometry.RingedSpace.derivedRestrictModules
                (Spec A).toRingedSpace U).map γ =
              (AlgebraicGeometry.RingedSpace.derivedRestrictModules
                (Spec A).toRingedSpace U).map β ≫ α := by
  obtain ⟨r, f, rfl⟩ :=
    Stacks.DerivedQCoh.OpenLift.exists_unionOfBasicOpens_eq_of_isCompact A U hU
  exact exists_roof_of_union T f P E hP hPT hE α

/-- **The reshaping of a splitting and a roof into a splitting compatible with a map, over
variable categories.** Let `res : C ⥤ D`, let `S` be an object of `D` with a map `pr : S ⟶ F`
and let `α : F ⟶ res E`. Suppose some `P` in the good classes `Pp` and `Sp` has `S ≅ res P`, and
suppose every such `P` admits, for every `a : res P ⟶ res E`, a roof `P ←β— R —γ→ R` with `R`
again good, `res β` invertible and `res γ = res β ≫ a`. Then some good `R` carries a map
`γ : R ⟶ E` and an isomorphism `res R ≅ S` through which `res γ` is `pr` followed by `α`.

Nothing here is a biproduct and nothing is geometry: `S` stands for `F ⊕ F[1]` and `pr` for its
projection. That is what makes the statement usable. Elaborated at the geometry, the step fails:
the biproduct `F ⊕ F[1]` in the conclusion below and the one in [Stacks, Tag 08EK]'s conclusion
are two `CategoryTheory.Limits.HasBinaryBiproduct` instances for one pair of objects — the
category of `𝒪_U`-modules has two spellings and instance search keys on neither — and reconciling
them inside the destructuring of [Stacks, Tag 08EK] exhausts the default heartbeat budget, with
no error naming the cause. With `S` a variable the two meet once, in the term-mode application
below, where the check is immediate. The same device is
`Stacks.Perfect.SupportedBiprodShift.biprodShiftIsoOfFunctorIso`. -/
theorem exists_iso_of_split_and_roof {C D : Type*} [Category C] [Category D]
    (res : C ⥤ D) {E : C} {F S : D} (α : F ⟶ res.obj E) (pr : S ⟶ F) (Pp Sp : C → Prop)
    (hsplit : ∃ P : C, Pp P ∧ Sp P ∧ Nonempty (S ≅ res.obj P))
    (hroof : ∀ P : C, Pp P → Sp P → ∀ a : res.obj P ⟶ res.obj E,
      ∃ (R : C) (β : R ⟶ P) (γ : R ⟶ E), Pp R ∧ Sp R ∧ IsIso (res.map β) ∧
        res.map γ = res.map β ≫ a) :
    ∃ (R : C) (γ : R ⟶ E), Pp R ∧ Sp R ∧
      ∃ e : res.obj R ≅ S, res.map γ = e.hom ≫ pr ≫ α := by
  obtain ⟨P, hP, hPS, ⟨eP⟩⟩ := hsplit
  obtain ⟨R, β, γ, hR, hRS, hβ, hγ⟩ := hroof P hP hPS (eP.inv ≫ pr ≫ α)
  let := hβ
  refine ⟨R, γ, hR, hRS, asIso (res.map β) ≪≫ eP.symm, ?_⟩
  rw [hγ]
  simp only [Iso.trans_hom, Iso.symm_hom, asIso_hom, Category.assoc]

/-- **The affine case of [Stacks, Tag 09IM], in the strengthened form.** Let `X = Spec A`, let
`T ⊆ X` be closed with quasi-compact complement, let `U ⊆ X` be a quasi-compact open and let `E`
be an object of `D(𝒪_X)` with quasi-coherent cohomology. For every perfect `F` on `U` supported
on `T ∩ U` and every `α : F ⟶ E|_U` there are a perfect `R` on `X` supported on `T`, a map
`β : R ⟶ E` and an isomorphism `e : R|_U ≅ F ⊕ F[1]` with `β|_U = e.hom ≫ biprod.fst ≫ α`.

[Stacks, Tag 08EK] supplies `P` with `F ⊕ F[1] ≅ P|_U`, and [Stacks, Tag 08EH] extends the
composite `P|_U ≅ F ⊕ F[1] ⟶ F ⟶ E|_U` to `R = Iₑ ⊗^𝐋 P ⟶ E`; the splitting is the one
[Stacks, Tag 08EK] produced, read through the restriction of the roof's left leg, which is
invertible over `U`.

The registrations of [Stacks, Tag 08EK], [Stacks, Tag 08EH] and [Stacks, Tag 09IM] are on other
declarations, so no tag attribute is placed here. -/
theorem exists_isPerfect_supported_hom_biprod_shift_iso_restrict (T : Set ↥(Spec A))
    (hT : IsClosed T) (hTc : IsCompact Tᶜ) (U : (Spec A).Opens)
    (hU : IsCompact ((U : (Spec A).Opens) : Set ↥(Spec A)))
    (E : derivedCat A) (hE : HasQuasicoherentCohomology A E)
    (F : DerivedCategory (StrictlyPerfect.OXMod.{u, u, u}
      ((Spec A).toRingedSpace.restrict U.isOpenEmbedding)))
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect
      (X := (Spec A).toRingedSpace.restrict U.isOpenEmbedding) F)
    (hFT : AlgebraicGeometry.CohomologySupportedOn
      (structureSheafRing ((Spec A).toRingedSpace.restrict U.isOpenEmbedding))
      (Subtype.val ⁻¹' T) F)
    (α : F ⟶ (AlgebraicGeometry.RingedSpace.derivedRestrictModules
      (Spec A).toRingedSpace U).obj E) :
    ∃ (R : derivedCat A) (β : R ⟶ E),
      Stacks.Cohomology.PerfectComplexes.IsPerfect (X := (Spec A).toRingedSpace) R ∧
        AlgebraicGeometry.CohomologySupportedOn (structureSheafRing (Spec A).toRingedSpace) T R ∧
          ∃ e : (AlgebraicGeometry.RingedSpace.derivedRestrictModules
              (Spec A).toRingedSpace U).obj R ≅ F ⊞ F⟦(1 : ℤ)⟧,
            (AlgebraicGeometry.RingedSpace.derivedRestrictModules
                (Spec A).toRingedSpace U).map β =
              e.hom ≫ biprod.fst ≫ α :=
  exists_iso_of_split_and_roof _ α biprod.fst _ _
    (Stacks.Perfect.SupportedBiprodShift.exists_isPerfect_supported_biprod_shift_iso_restrict
      T hT hTc U hU F hF hFT)
    (fun P hP hPT a => exists_roof_of_isCompact T U hU P E hP hPT hE a)

end Stacks.Perfect.SupportedLiftAffineSpec

end
