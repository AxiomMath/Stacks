module

public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.CodimensionTwoOpen
public import StacksFrontier.AlgebraicGeometry.Divisors.WeilDivisorClass.FirstChernClassInjective
public import StacksFrontier.AlgebraicGeometry.Properties.NormalDepthTwo
public import StacksFrontier.AlgebraicGeometry.ReflexiveOpenEquivalence.Pushforward
import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FiniteOverSmooth.NormalFibre

/-!
# A coherent reflexive module on a normal scheme is determined by its divisor class

Let `X` be an integral locally Noetherian normal scheme and `U ⊆ X` an open subscheme whose
complement has codimension at least two at every point.  Two things happen on such an open.
First, restriction to `U` is an equivalence on coherent reflexive modules, by [Stacks, Tag 0EBJ]:
the codimension bound becomes a depth bound at every point of the complement, because on a normal
scheme a local ring of dimension at least two has depth at least two.  Second, `U` is itself
integral, locally Noetherian and normal, so the first Chern class `Pic(U) → Cl(U)` is injective by
[Stacks, Tag 0BE8].

Together these say that a coherent reflexive `𝒪_X`-module whose restriction to `U` is invertible
is determined, up to isomorphism, by the Weil divisor class of that restriction.

## Main results

* `AlgebraicGeometry.two_le_depth_stalk_of_notMem_of_two_le_codimension` — on a locally Noetherian
  normal scheme the codimension bound of [Stacks, Tag 0AY6] (3) is the depth bound of
  [Stacks, Tag 0EBJ].
* `AlgebraicGeometry.nonempty_iso_of_nonempty_restrict_iso` — two coherent reflexive modules whose
  restrictions to such an open are isomorphic are isomorphic.
* `AlgebraicGeometry.nonempty_iso_of_weilDivisorClassOfInvertibleSheaf_restrict_eq` — **the
  injectivity clause of [Stacks, Tag 0EBM]**: two coherent reflexive modules invertible on such an
  open and with the same Weil divisor class there are isomorphic.

## Implementation notes

**Which clauses of Tag 0EBM are here.**  Tag 0EBM asserts that the group of isomorphism classes of
rank one coherent reflexive `𝒪_X`-modules is isomorphic to `Cl(X)`.  That isomorphism is not
constructed here and no declaration in this file claims it; what is proved is the injectivity
clause of the source's proof, in the form that does not presuppose the map.  The source reads injectivity as: a class in
the kernel restricts to the trivial class on a common `U`, hence is trivial on `U` by Tag 0BE8, and
therefore trivial on `X` by Tag 0EBJ.  That is exactly
`nonempty_iso_of_weilDivisorClassOfInvertibleSheaf_restrict_eq` with the two modules compared
directly instead of through a quotient.

The map `ℱ ↦ c₁(ℱ|_U)` itself is
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RankOneWeilClass.lean`, and
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_injective` is the present clause
restated for it; the independence of the chosen open that defining it needs is
`AlgebraicGeometry.weilClassOfCodimTwoInvertible_restrict`, which rests on the transport of a
regular meromorphic section and of its orders of vanishing along an open immersion in
`StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/RestrictMeromorphic.lean`.  Its
multiplicativity for the monoid law of Tag 0EBL is
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_mul` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RankOneWeilClassMultiplicative.lean`.  Its
surjectivity is
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonToWeilClass_surjective` of
`StacksFrontier/AlgebraicGeometry/Divisors/Reflexive/RankOneWeilClassSurjective.lean`, which rests
on the construction of `𝒪_X(D)` for an arbitrary Weil divisor on a NORMAL scheme in
`StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/NormalWeilDivisorInvertible.lean`:
`AlgebraicGeometry.positiveWeilIdeal` of
`StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/FirstChernClassSurjective.lean` is an
effective Cartier divisor on all of `X` only when the local rings are factorial, which by
[Stacks, Tag 0BE9] is strictly stronger than normality, so over a normal scheme it is taken only
on the open subscheme where it is principal, whose complement has codimension at least two.  The
isomorphism of Tag 0EBM is then
`AlgebraicGeometry.CoherentReflexive.rankOneSkeletonMulEquivWeilDivisorClass`.  The clause
`Cl(U) = Cl(X)` is
`AlgebraicGeometry.weilDivisorClassRestrictEquiv` of
`StacksFrontier/AlgebraicGeometry/Divisors/WeilDivisorClass/CodimensionTwoOpen.lean`.

**Why normality enters twice.**  It converts the codimension bound into the depth bound that
[Stacks, Tag 0EBJ] asks for, by `AlgebraicGeometry.two_le_depth_stalk_of_two_le_coheight`, which is
Serre's `(S₂)`; and it is the hypothesis of [Stacks, Tag 0BE8] on `U`, where it is inherited from
`X` by `AlgebraicGeometry.isNormal_of_isOpenImmersion`.

**The transfer back to `X` is by the equivalence of [Stacks, Tag 0EBJ]**, not by descending a
global morphism: for a general pair of coherent reflexive modules there need be no morphism on `X`
to descend.  Restriction to `U` is an equivalence of the categories of coherent reflexive modules
(`Stacks.AlgebraicGeometry.ReflexiveModules.reflexiveCoherentEquivalence`), so an isomorphism of
the restrictions of two coherent reflexive modules on `X` is the image of an isomorphism on `X`.

**Which invertibility.**  The Weil divisor class of [Stacks, Tag 0BE6] is stated for
`AlgebraicGeometry.SheafOfModules.IsInvertible` and the Picard group for
`Stacks.SheafOfModules.IsInvertible`; the two are exchanged by
`Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry`, the existing bridge, and no new one is
introduced.

## References

* [Stacks Project, Tag 0EBM](https://stacks.math.columbia.edu/tag/0EBM)
* [Stacks Project, Tag 0EBJ](https://stacks.math.columbia.edu/tag/0EBJ)
* [Stacks Project, Tag 0BE8](https://stacks.math.columbia.edu/tag/0BE8)
* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
* [Stacks Project, Tag 0AY6](https://stacks.math.columbia.edu/tag/0AY6)
-/

@[expose] public section

open CategoryTheory Order TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules (IsReflexive ReflexiveCoherentModules
  reflexiveCoherentEquivalence)

universe u

namespace AlgebraicGeometry

attribute [local instance] schemePicardGroupAddCommGroup

/-! ### From a codimension bound to a depth bound -/

/-- **The codimension bound of [Stacks, Tag 0AY6] (3) is the depth hypothesis of
[Stacks, Tag 0EBJ]**, on a locally Noetherian normal scheme: the codimension of the closure of a
point is its coheight, which is the Krull dimension of its local ring, and a normal local ring of
dimension at least two has depth at least two. -/
theorem two_le_depth_stalk_of_notMem_of_two_le_codimension {X : Scheme.{u}}
    [IsLocallyNoetherian X] [IsNormal X] (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x)) :
    ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x) := fun x hx =>
  two_le_depth_stalk_of_two_le_coheight x
    (by rw [coheight_eq_codimension_closureSingleton]; exact hU x hx)

/-! ### Descending an isomorphism from the open subscheme -/

/-- **Two coherent reflexive modules isomorphic over an open whose complement has depth at least
two are isomorphic.**  Restriction to such an open is an equivalence of the categories of coherent
reflexive modules by [Stacks, Tag 0EBJ], and an equivalence reflects isomorphisms. -/
theorem nonempty_iso_of_nonempty_restrict_iso {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] (U : X.Opens)
    (hdepth : ∀ x : X, x ∉ (U : Set X) →
      (2 : ℕ∞) ≤ Module.depth (X.presheaf.stalk x)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x)) (X.presheaf.stalk x))
    (M N : X.Modules) (hM : _root_.SheafOfModules.IsCoherent M) (hMr : IsReflexive M)
    (hN : _root_.SheafOfModules.IsCoherent N) (hNr : IsReflexive N)
    (h : Nonempty (M.restrict U.ι ≅ N.restrict U.ι)) :
    Nonempty (M ≅ N) := by
  obtain ⟨e, n, -⟩ := reflexiveCoherentEquivalence X U hdepth
  obtain ⟨φ⟩ := h
  let a : ReflexiveCoherentModules X := ⟨M, ⟨hM, hMr⟩⟩
  let b : ReflexiveCoherentModules X := ⟨N, ⟨hN, hNr⟩⟩
  have pU : (Scheme.Modules.pullback U.ι).obj M ≅ (Scheme.Modules.pullback U.ι).obj N :=
    ((Scheme.Modules.restrictFunctorIsoPullback U.ι).app M).symm ≪≫ φ ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback U.ι).app N
  exact ⟨(ObjectProperty.ι _).mapIso (e.unitIso.app a ≪≫
    e.inverse.mapIso (ObjectProperty.isoMk _ (n.app a ≪≫ pU ≪≫ (n.app b).symm)) ≪≫
    (e.unitIso.app b).symm)⟩

/-! ### The divisor class of the restriction determines the module -/

/-- **Stacks Project, Tag 0EBM, the injectivity clause.**  Let `X` be an integral locally
Noetherian normal scheme and `U ⊆ X` an open subscheme whose complement has codimension at least
two at every point.  Two coherent reflexive `𝒪_X`-modules whose restrictions to `U` are invertible
with the same Weil divisor class in `Cl(U)` are isomorphic.

This is the injectivity clause of the source's proof of Tag 0EBM, stated without the map that
clause is about: the first Chern class of `U` is injective by [Stacks, Tag 0BE8], so the two
restrictions are isomorphic, and restriction to `U` is an equivalence on coherent reflexive modules
by [Stacks, Tag 0EBJ], so the two modules are isomorphic on `X`.  The isomorphism that Tag 0EBM
itself asserts — between `Cl(X)` and the group of isomorphism classes of rank one coherent
reflexive `𝒪_X`-modules — is **not** proved here and no declaration claims it; see the
implementation notes for what is missing. -/
@[stacks 0EBM "the injectivity clause, with the two modules compared directly"]
theorem nonempty_iso_of_weilDivisorClassOfInvertibleSheaf_restrict_eq {X : Scheme.{u}}
    [IsIntegral X] [IsLocallyNoetherian X] [IsNormal X] (U : X.Opens)
    (hU : ∀ x : X, x ∉ U → (2 : ℕ∞) ≤ codimension (IrreducibleCloseds.closureSingleton x))
    (M N : X.Modules) (hM : _root_.SheafOfModules.IsCoherent M) (hMr : IsReflexive M)
    (hN : _root_.SheafOfModules.IsCoherent N) (hNr : IsReflexive N)
    [hMU : SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property
      (M.restrict U.ι)]
    [hNU : SheafOfModules.IsInvertible U.toScheme.sheaf.obj U.toScheme.ringCatSheaf.property
      (N.restrict U.ι)]
    (hc : haveI : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
      haveI : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
      weilDivisorClassOfInvertibleSheaf U.toScheme (M.restrict U.ι) =
        weilDivisorClassOfInvertibleSheaf U.toScheme (N.restrict U.ι)) :
    Nonempty (M ≅ N) := by
  have : IsIntegral U.toScheme := isIntegral_of_two_le_codimension_compl U hU
  have : IsLocallyNoetherian U.toScheme := isLocallyNoetherian_of_isOpenImmersion U.ι
  have : IsNormal U.toScheme := isNormal_of_isOpenImmersion U.ι
  have hMU' : Stacks.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property (M.restrict U.ι) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hMU
  have hNU' : Stacks.SheafOfModules.IsInvertible U.toScheme.sheaf.obj
      U.toScheme.ringCatSheaf.property (N.restrict U.ι) :=
    (Stacks.SheafOfModules.isInvertible_iff_algebraicGeometry _ _ _).mpr hNU
  refine nonempty_iso_of_nonempty_restrict_iso U
    (two_le_depth_stalk_of_notMem_of_two_le_codimension U hU) M N hM hMr hN hNr ?_
  refine (Stacks.SheafOfModules.picardClass_eq_iff U.toScheme.sheaf.obj
    U.toScheme.ringCatSheaf.property _ _ hMU' hNU').mp
    (picardToWeilDivisorClassGroup_injective U.toScheme ?_)
  change weilDivisorClassOfPicardClass U.toScheme _ = weilDivisorClassOfPicardClass U.toScheme _
  exact (weilDivisorClassOfPicardClass_picardClass U.toScheme _).trans
    (hc.trans (weilDivisorClassOfPicardClass_picardClass U.toScheme _).symm)

end AlgebraicGeometry

end
