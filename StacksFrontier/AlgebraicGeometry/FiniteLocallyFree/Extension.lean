module

public import StacksFrontier.AlgebraicGeometry.Modules.LocallySplitShortExact
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.FiniteLocallyFreeBiprod

/-!
# Finite locally free sheaves of modules are closed under extensions

Let `0 ⟶ ℰ' ⟶ ℰ ⟶ ℰ'' ⟶ 0` be a short exact sequence of `𝒪_X`-modules on a scheme `X` whose
two ends are finite locally free.  Then the middle term is finite locally free.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_shortExact`: the statement for the
  pointwise predicate `AlgebraicGeometry.Scheme.Modules.IsFiniteLocallyFree`.
* `Stacks.FiniteLocallyFree.isFiniteLocallyFree_of_shortExact`: the same statement for the class
  of [Stacks, Tag 01C6] (2).

## Implementation notes

Finite local freeness of the quotient already makes the sequence split over a neighbourhood of
every point, by `AlgebraicGeometry.Scheme.Modules.exists_nonempty_splitting_restrict`; that is
where the mathematical content sits, since a short exact sequence of locally free sheaves need
not split globally.  What is left is bookkeeping: shrink the neighbourhood so that the two ends
are moreover free there, transport the splitting to the smaller open, and read the middle term
off as a biproduct of two free modules, which is free on the sum of the two index types.

Only the pointwise predicate is manipulated, because it is the one whose witness is an
isomorphism onto a free module over a single open; the class of Stacks 01C6(2) is reached through
the two existing comparisons
`AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_iff_localGenerators` and
`Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry`.

The splitting is transported rather than produced afresh over the smaller open: restriction along
the inclusion of the smaller open into the larger is additive, so `ShortComplex.Splitting.map`
carries the splitting across, and the resulting short complex is identified with the restriction
to the smaller open by `Mathlib.AlgebraicGeometry.Modules.Sheaf`'s restriction-composition
isomorphism.  No transport along an equality of objects is involved.

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- **Restriction of a short complex of `𝒪_X`-modules to a smaller open**, as a short complex
isomorphic to the one obtained by restricting twice.  The inclusion of the smaller open factors
through the larger one, and restriction along a composite is the composite of the restrictions. -/
def mapRestrictFunctorIsoOfLE (S : ShortComplex X.Modules) {U V : X.Opens} (hle : U ≤ V) :
    S.map (restrictFunctor U.ι) ≅
      (S.map (restrictFunctor V.ι)).map (restrictFunctor (X.homOfLE hle)) :=
  S.mapNatIso ((restrictFunctorCongr (X.homOfLE_ι hle)).symm ≪≫
    restrictFunctorComp (X.homOfLE hle) V.ι)

/-- **A splitting of a short complex of `𝒪_X`-modules restricted to an open restricts to a
smaller open.**  Restriction along the inclusion of the smaller open into the larger is a left
adjoint, hence additive, so it carries the splitting across. -/
def splittingRestrictOfLE {S : ShortComplex X.Modules} {U V : X.Opens} (hle : U ≤ V)
    (sp : (S.map (restrictFunctor V.ι)).Splitting) :
    (S.map (restrictFunctor U.ι)).Splitting :=
  (sp.map (restrictFunctor (X.homOfLE hle))).ofIso (mapRestrictFunctorIsoOfLE S hle).symm

/-- **A biproduct of two sheaves of modules on a scheme identified with free ones is free on the
sum of the two index types**, with the biproduct ascribed to
`AlgebraicGeometry.Scheme.Modules`.

`Stacks.Perfect.BoundedLocallyFreeComplexes.freeSumBiprodIso` is the same isomorphism with its
biproduct taken in `SheafOfModules Y.ringCatSheaf`. The two biproducts agree definitionally, but
instance search finds `HasBinaryBiproduct` only at the spelling `Y.Modules`, whose abelian
structure is an instance of Mathlib's rather than one deduced from conditions on the site. -/
def biprodFreeIsoFreeSum {Y : Scheme.{u}} (I K : Type u) :
    ((SheafOfModules.free (R := Y.ringCatSheaf) I : Y.Modules) ⊞
        (SheafOfModules.free (R := Y.ringCatSheaf) K : Y.Modules)) ≅
      (SheafOfModules.free (R := Y.ringCatSheaf) (I ⊕ K) : Y.Modules) :=
  (Stacks.Perfect.BoundedLocallyFreeComplexes.freeSumBiprodIso Y.ringCatSheaf I K).symm

/-- **Two isomorphisms and an identification of the biproduct of their targets identify the
biproduct of their sources.**  The objects of the target biproduct are variables here, so that
instance search sees the category as `AlgebraicGeometry.Scheme.Modules` rather than reading it
off the type of a free module. -/
def biprodIsoOfIsos {Y : Scheme.{u}} {A B A' B' T : Y.Modules}
    (eA : A ≅ A') (eB : B ≅ B') (e : (A' ⊞ B') ≅ T) : (A ⊞ B) ≅ T :=
  biprod.mapIso eA eB ≪≫ e

/-- **Finite locally free sheaves of modules on a scheme are closed under extensions.** If the
two ends of a short exact sequence of `𝒪_X`-modules are finite locally free, so is the middle
term.

Over a neighbourhood of a point the sequence splits, because the quotient is finite locally free;
shrinking that neighbourhood so that both ends are free there presents the middle term as a
biproduct of two free modules of finite rank, hence as free on the sum of the two index types. -/
theorem isFiniteLocallyFree_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : IsFiniteLocallyFree S.X₁) (h₃ : IsFiniteLocallyFree S.X₃) :
    IsFiniteLocallyFree S.X₂ := by
  intro x
  obtain ⟨U, hxU, ⟨sp⟩⟩ := exists_nonempty_splitting_restrict S hS h₃ x
  obtain ⟨V, hxV, I, hI, ⟨e₁⟩⟩ := h₁ x
  obtain ⟨W, hxW, K, hK, ⟨e₃⟩⟩ := h₃ x
  have := hI
  have := hK
  set Z : X.Opens := U ⊓ V ⊓ W with hZ
  have eI : S.X₁.restrict Z.ι ≅
      (SheafOfModules.free (R := (Z : Scheme.{u}).ringCatSheaf) I : (Z : Scheme.{u}).Modules) :=
    restrictFreeOfLE (inf_le_left.trans inf_le_right) S.X₁ I e₁
  have eK : S.X₃.restrict Z.ι ≅
      (SheafOfModules.free (R := (Z : Scheme.{u}).ringCatSheaf) K : (Z : Scheme.{u}).Modules) :=
    restrictFreeOfLE inf_le_right S.X₃ K e₃
  exact ⟨Z, ⟨⟨hxU, hxV⟩, hxW⟩, I ⊕ K, inferInstance,
    ⟨(splittingRestrictOfLE (S := S) (inf_le_left.trans inf_le_left) sp).isoBinaryBiproduct
      ≪≫ biprodIsoOfIsos eI eK (biprodFreeIsoFreeSum I K)⟩⟩

end AlgebraicGeometry.Scheme.Modules

namespace Stacks.FiniteLocallyFree

variable {X : Scheme.{u}}

/-- **Finite locally free sheaves of modules on a scheme are closed under extensions**, with
finite local freeness spelled as the class of [Stacks, Tag 01C6] (2). -/
theorem isFiniteLocallyFree_of_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact)
    (h₁ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₁)
    (h₃ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₃) :
    IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) S.X₂ := by
  have := h₁
  have := h₃
  exact (Stacks.Modules.isFiniteLocallyFree_iff_localGenerators S.X₂).1
    (AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_shortExact S hS
      (AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFree _)
      (AlgebraicGeometry.Scheme.Modules.isFiniteLocallyFree_of_isFiniteLocallyFree _))

end Stacks.FiniteLocallyFree

end
