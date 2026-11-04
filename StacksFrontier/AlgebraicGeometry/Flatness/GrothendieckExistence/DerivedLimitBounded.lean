module

public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.Boundedness
public import StacksFrontier.CategoryTheory.Triangulated.HomotopyLimit
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.Injectives.DerivedCategory.DerivedLimit
public import StacksCore.Tactic.StacksAttribute

/-!
# The coherator of a derived limit is bounded above

Let `X` be a quasi-compact and quasi-separated scheme, let `DQ_X : D(𝒪_X) ⥤ D_QCoh(𝒪_X)` be a
coherator of `X` ([Stacks, Tag 0CR0]) and let `(Kₙ)` be an inverse system in `D(𝒪_X)` indexed by
`ℕᵒᵖ` whose hypercohomology over the affine opens of `X` is concentrated in one interval `[a, b]`,
the same for every `n`. Let `K = Rlim Kₙ` be a derived limit of the system in `D(𝒪_X)`. Then

* `DQ_X(K)` is a derived limit of the system `(DQ_X(Kₙ))` in `D_QCoh(𝒪_X)`, which is the
  displayed equality `Rlim_{D_QCoh(𝒪_X)}(Kₙ) = DQ_X(Rlim_{D(𝒪_X)} Kₙ)` of [Stacks, Tag 0DIC];
* the cohomology sheaves of `DQ_X(K)` vanish outside a bounded interval, so `DQ_X(K)` lies in
  `D⁻_QCoh(𝒪_X)`, which is the conclusion of [Stacks, Tag 0DIC].

## Main results

* `AlgebraicGeometry.GrothendieckExistence.isDerivedLimit_coherator_obj` — the first assertion:
  the coherator, being a right adjoint, carries a derived limit to a derived limit.
* `AlgebraicGeometry.GrothendieckExistence.isDerivedLimit_map_derivedSectionsLocallySmall` — the
  instance of [Stacks, Tag 0D60] used below: derived sections over an open, taken at the locally
  small model at which the coherator lives, carry a derived limit to a derived limit.
* `AlgebraicGeometry.GrothendieckExistence.affineAmplitudeIn_of_isDerivedLimit` — the Milnor
  squeeze: a derived limit of a system with affine amplitude in `[a, b]` has affine amplitude in
  `[a, b + 1]`. Together with [Stacks, Tag 0CSA]
  (`Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj`) this gives the second assertion,
  the boundedness of the coherator of the derived limit.

## The shape of the proof

This is the source's proof of [Stacks, Tag 0DIC], in three steps.

*The equality.* `DQ_X` is a right adjoint, so it preserves the countable product occurring in a
derived-limit triangle, and it is exact because the adjunction `ι ⊣ DQ_X` is triangulated; an
exact functor preserving that product carries a derived-limit triangle to a derived-limit
triangle. This is `Stacks.Injectives.isDerivedLimit_map_rightAdjoint`.

*The reduction to `D⁻(𝒪_X)`.* `DQ_X` has bounded cohomological dimension, [Stacks, Tag 0CSA]
(`Stacks.Duality.Coherator.exists_isGE_isLE_coherator_obj`): there is an integer `N` depending only
on `X` and `DQ_X` such that the cohomology sheaves of `DQ_X(L)` lie in `[a, b + N]` as soon as the
hypercohomology of `L` over every affine open of `X` lies in `[a, b]`. So it suffices to bound the
affine hypercohomology of `Rlim Kₙ`.

*The Milnor sequence.* For an affine open `U` and every `m` the source's exact sequence

`0 ⟶ R¹lim H^{m-1}(U, Kₙ) ⟶ H^m(U, Rlim Kₙ) ⟶ lim H^m(U, Kₙ) ⟶ 0`

of [Stacks, Tag 0D60] has both outer terms zero whenever `m` and `m - 1` both avoid `[a, b]`, that
is whenever `m < a` or `b + 1 < m`: the product computing `R¹lim` is a product of zero modules and
the limit is a limit of zero modules. Hence `Rlim Kₙ` has affine amplitude in `[a, b + 1]`, the
single degree `b + 1` being the cost of the `R¹lim` term. The instance of Tag 0D60 needed is at the
locally small model and with values in `Γ(X, U)`-modules, so it is derived here from
[Stacks, Tag 08U1] (`Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor`) and the Milnor
sequence of [Stacks, Tag 07KY] (`DerivedCategory.isDerivedLimit_homology_shortExact`) in the same
two lines as the instances already in the library.

## The carried hypotheses

*The coherator and the inputs of Tag 0CSA.* `DQ_X` with its triangulated adjunction is an
argument, as it is in [Stacks, Tag 0CSA] and [Stacks, Tag 0CR2]; Tag 0CR0 is available in this
repository only with compact generation of `D_QCoh(𝒪_X)` as a hypothesis. The three hypotheses
`hmv`, `hmvTop` and `haffine` of Tag 0CSA are the ones its statement records: Tag 0CSA is
*invoked* to pass from the Milnor squeeze to the second assertion, not assumed.

*The uniform bound, which is what Situation 0DIB contributes.* The hypothesis `hL` says that the
terms of the tower all have affine amplitude in one interval `[a, b]`. In
Situation [Stacks, Tag 0DIB] this is the second half of the source's proof: each `Kₙ` is
pseudo-coherent, hence in `D⁻(𝒪_{Xₙ})`, its top nonvanishing cohomology sheaf is of finite
presentation ([Stacks, Tag 08DN]) and is carried to the top cohomology sheaf of `Kₙ₋₁` by the
derived restriction, so Nakayama's lemma ([Stacks, Tag 00DV]) along the thickening `Xₙ₋₁ ⊆ Xₙ`
forces the top degree to be independent of `n`; the passage from a bound on the cohomology sheaves
to a bound on the hypercohomology over an affine open is [Stacks, Tag 08E5] with
[Stacks, Tag 06Z0]. None of that is formalized here, and it is isolated in `hL`.

The hypothesis is not the conclusion in disguise. It mentions no coherator and no derived limit:
it is a statement about the individual terms `Kₙ`, each a different object of `D(𝒪_X)`, whereas
the conclusion is a single bound on the cohomology sheaves of `DQ_X` of the derived limit. The
derived limit of a tower of objects with amplitude in `[a, b]` need not be bounded at all before
`DQ_X` is applied, which is precisely why the source needs Tag 0CSA.

*The tower.* The system is an arbitrary inverse system in `D(𝒪_X)`, not the system `Riₙ,* Kₙ`
attached to the data of `AlgebraicGeometry.GrothendieckExistence.DerivedExistenceSituation`
(`StacksFrontier/AlgebraicGeometry/Flatness/GrothendieckExistence/Basic.lean`). Three things stand
between the two, and none of them is addressed here.

First, the model. The objects `Kₙ` of a `DerivedExistenceSituation` are elaborated under the
file-level `attribute [local instance] HasDerivedCategory.standard` of that file, so they live in
the derived category at the standard model, whereas the coherator exists only at the locally small
model `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`: at the standard model the morphisms
live one universe up and the compact-generation hypothesis of [Stacks, Tag 0CR0] is false rather
than merely unavailable, see the implementation notes of
`StacksFrontier/AlgebraicGeometry/Duality/CompactGeneration/CoheratorRevisited.lean`.

Second, the spelling of the category. A `DerivedExistenceSituation` uses
`StrictlyPerfect.OXMod (Xₙ).toRingedSpace`, the sheaves of modules over the structure sheaf of the
underlying ringed space, where the coherator uses `X.Modules`.

Third, the tower itself. The unbounded derived direct image `Rf_*` of sheaves of modules along a
morphism of schemes, `Stacks.Duality.derivedPushforward`, *is* available at a free
`HasDerivedCategory` and so at the locally small model; what is missing is the assembly of
`n ↦ Riₙ,* Kₙ` into a functor `ℕᵒᵖ ⥤ D(𝒪_X)`, which needs the comparison of the derived direct
images along the two routes `Xₙ → Xₙ₊₁ → X` and `Xₙ → X`. A `DerivedExistenceSituation` records
the corresponding equation only for the underlying morphisms of schemes, as `transition_fst`.

The statements below therefore apply to Situation 0DIB as soon as that tower can be formed, and
say nothing about it until then.

## References

* [Stacks Project, Tag 0DIC](https://stacks.math.columbia.edu/tag/0DIC)
* [Stacks Project, Tag 0DIB](https://stacks.math.columbia.edu/tag/0DIB)
* [Stacks Project, Tag 0CR0](https://stacks.math.columbia.edu/tag/0CR0)
* [Stacks Project, Tag 0CSA](https://stacks.math.columbia.edu/tag/0CSA)
* [Stacks Project, Tag 0D60](https://stacks.math.columbia.edu/tag/0D60)
* [Stacks Project, Tag 08U1](https://stacks.math.columbia.edu/tag/08U1)
* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
* [Stacks Project, Tag 08DN](https://stacks.math.columbia.edu/tag/08DN)
* [Stacks Project, Tag 08E5](https://stacks.math.columbia.edu/tag/08E5)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.ObjectProperty
open CategoryTheory.Pretriangulated Opposite
open Stacks.Duality Stacks.Duality.Coherator

universe u

namespace AlgebraicGeometry.GrothendieckExistence

/-! ### The equality of the statement -/

section Equality

variable {X : Scheme.{u}} {DQ : DerivedCategory X.Modules ⥤ quasiCoherentDerivedCategory X}

/-- **The displayed equality of [Stacks, Tag 0DIC]**: `Rlim_{D_QCoh(𝒪_X)}(Kₙ)` and
`DQ_X(Rlim_{D(𝒪_X)} Kₙ)` agree. Precisely, if `K` is a derived limit of an inverse system `(Kₙ)`
in `D(𝒪_X)` then `DQ_X(K)` is a derived limit of the system `(DQ_X(Kₙ))` in `D_QCoh(𝒪_X)`; the
existence of the product of the images is part of the conclusion.

This is the source's reason for the equality: `DQ_X` is a right adjoint, so it commutes with
products, and it is exact because the adjunction `ι ⊣ DQ_X` is triangulated, so it carries the
derived-limit triangle of `(Kₙ)` to the derived-limit triangle of `(DQ_X(Kₙ))`. -/
@[stacks 0DIC "the displayed equality only; the coherator of Stacks 0CR0 is an argument, as in \
  Stacks 0CSA and 0CR2, and the tower is an arbitrary inverse system in D(O_X) rather than the \
  system Ri_n,* K_n of Situation 0DIB, which this library cannot yet form at the locally small \
  model the coherator lives at"]
theorem isDerivedLimit_coherator_obj (adj : quasiCoherentι X ⊣ DQ) [DQ.CommShift ℤ]
    [adj.IsTriangulated] (L : ℕᵒᵖ ⥤ DerivedCategory X.Modules)
    [HasProduct fun n : ℕ => L.obj ⟨n⟩] (K : DerivedCategory X.Modules)
    (hK : IsDerivedLimit L K) :
    ∃ h : HasProduct fun n : ℕ => DQ.obj (L.obj ⟨n⟩),
      @IsDerivedLimit (quasiCoherentDerivedCategory X) _ _ _ _ _ _ (L ⋙ DQ) h (DQ.obj K) :=
  have : DQ.IsRightAdjoint := adj.isRightAdjoint
  have : DQ.IsTriangulated := inferInstance
  Stacks.Injectives.isDerivedLimit_map_rightAdjoint DQ L K hK

end Equality

/-! ### Derived sections over an open commute with derived limits, at the locally small model -/

section Sections

variable (X : Scheme.{u})

/-- Sections over an open preserve countable products: sections of a limit of sheaves of modules
are the limit of the sections. This is the hypothesis of [Stacks, Tag 08U1] for
`Stacks.Cohomology.sectionsFunctor`, which instance search does not see through that definition. -/
instance preservesCountableProducts_sectionsFunctor (U : X.Opens) :
    PreservesLimitsOfShape (Discrete ℕ) (Stacks.Cohomology.sectionsFunctor X U) :=
  inferInstanceAs (PreservesLimitsOfShape (Discrete ℕ)
    (SheafOfModules.evaluation X.ringCatSheaf (op U)))

/-- **[Stacks, Tag 0D60], first assertion, for `RΓ(U, -)` at the locally small model.** If `K` is a
derived limit of an inverse system `(Kₙ)` in `D(𝒪_X)`, then `RΓ(U, K)` is a derived limit of the
system `(RΓ(U, Kₙ))` in `D(Γ(X, U))`; the existence of the product of the images is part of the
conclusion.

This is [Stacks, Tag 08U1]: `𝒪_X`-modules are Grothendieck abelian, `Γ(X, U)`-modules have exact
countable products, and sections over `U` preserve countable products, so the right derived
functor of sections carries a derived-limit triangle to a derived-limit triangle. The instances of
Tag 0D60 already in the library are stated either for `Ab`-valued derived sections over an open, or
for module-valued derived sections over the base ring at `HasDerivedCategory.standard`; this one is
`Γ(X, U)`-module valued at the locally small model, which is the model
`Stacks.Duality.Coherator.AffineAmplitudeIn` is set at. -/
@[stacks 0D60 "commutation with derived limits, for the Γ(X, U)-module valued derived sections \
  over an open at the locally small model"]
theorem isDerivedLimit_map_derivedSectionsLocallySmall (U : X.Opens)
    (L : ℕᵒᵖ ⥤ DerivedCategory X.Modules) [HasProduct fun n : ℕ => L.obj ⟨n⟩]
    (K : DerivedCategory X.Modules) (hK : IsDerivedLimit L K) :
    ∃ h : HasProduct fun n : ℕ => (derivedSectionsLocallySmall X U).obj (L.obj ⟨n⟩),
      @IsDerivedLimit (DerivedCategory (ModuleCat.{u} Γ(X, U))) _ _ _ _ _ _
        (L ⋙ derivedSectionsLocallySmall X U) h ((derivedSectionsLocallySmall X U).obj K) := by
  obtain ⟨p, δ, hT⟩ := hK
  obtain ⟨h, δ', hT'⟩ := Stacks.Injectives.isDerivedLimit_map_rightDerivedFunctor
    (Stacks.Cohomology.sectionsFunctor X U) (derivedSectionsLocallySmall X U)
    (derivedSectionsLocallySmallUnit X U) L K p ⟨δ, hT⟩
  exact ⟨h, _, δ', hT'⟩

end Sections

/-! ### The Milnor squeeze -/

/-- A product of zero objects is zero. -/
private lemma isZero_pi {J : Type*} {C : Type*} [Category C] [HasZeroObject C]
    [HasZeroMorphisms C] (f : J → C) [HasProduct f] (h : ∀ j, IsZero (f j)) : IsZero (∏ᶜ f) :=
  (limit.isLimit (Discrete.functor f)).isZero_pt
    ((Functor.isZero_iff _).mpr fun j => h j.as)

/-- The middle term of a short exact sequence whose outer terms vanish is zero. -/
private lemma isZero_X₂_of_shortExact {C : Type*} [Category C] [Abelian C] {S : ShortComplex C}
    (hS : S.ShortExact) (h₁ : IsZero S.X₁) (h₃ : IsZero S.X₃) : IsZero S.X₂ :=
  hS.exact.isZero_X₂ (h₁.eq_zero_of_src _) (h₃.eq_zero_of_tgt _)

/-- **The Milnor squeeze.** If every term of an inverse system `(Kₙ)` in `D(𝒪_X)` has its
hypercohomology over the affine opens of `X` concentrated in `[a, b]`, then a derived limit of the
system has its hypercohomology over the affine opens concentrated in `[a, b + 1]`.

Fix an affine open `U` and a degree `m` outside `[a, b + 1]`. Then `m` and `m - 1` both lie
outside `[a, b]`, so in the Milnor short exact sequence

`0 ⟶ R¹lim H^{m-1}(U, Kₙ) ⟶ H^m(U, Rlim Kₙ) ⟶ lim H^m(U, Kₙ) ⟶ 0`

of [Stacks, Tag 0D60] the right-hand term is a limit of zero modules, hence zero, and the
left-hand term is a quotient of a product of zero modules, hence zero; so the middle term is
zero. The one degree lost at the top is the `R¹lim` term, which can be nonzero in degree `b + 1`
even though every `H^{b+1}(U, Kₙ)` vanishes. -/
theorem affineAmplitudeIn_of_isDerivedLimit (X : Scheme.{u})
    (L : ℕᵒᵖ ⥤ DerivedCategory X.Modules) [HasProduct fun n : ℕ => L.obj ⟨n⟩]
    (K : DerivedCategory X.Modules) (hK : IsDerivedLimit L K) (a b : ℤ)
    (hL : ∀ n : ℕ, AffineAmplitudeIn X a b (L.obj ⟨n⟩)) :
    AffineAmplitudeIn X a (b + 1) K := by
  intro U m hm
  obtain ⟨hprod, hlim⟩ := isDerivedLimit_map_derivedSectionsLocallySmall X U.1 L K hK
  have := hprod
  obtain ⟨p, c, -, hseq⟩ := DerivedCategory.isDerivedLimit_homology_shortExact
    (L ⋙ derivedSectionsLocallySmall X U.1) ((derivedSectionsLocallySmall X U.1).obj K) hlim
  obtain ⟨-, i, q, w, -, -, -, hshort⟩ := hseq m
  have hcur : m < a ∨ b < m := by omega
  have hprev : m - 1 < a ∨ b < m - 1 := by omega
  have hzeroPrev : IsZero (∏ᶜ fun n : ℕ =>
      ((L ⋙ derivedSectionsLocallySmall X U.1) ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) (m - 1)).obj (op n)) :=
    isZero_pi _ fun n => hL n U (m - 1) hprev
  refine isZero_X₂_of_shortExact hshort ?_ ?_
  · exact hzeroPrev.of_epi (cokernel.π _)
  · exact (limit.isLimit _).isZero_pt ((Functor.isZero_iff _).mpr fun n => hL n.unop U m hcur)

end AlgebraicGeometry.GrothendieckExistence

end
