module

public import StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalComparison
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.DiagonalTransport

/-!
# The tensor--Hom diagonal along a ring map that has a section

Let `φ : S →+* T` be a homomorphism of commutative rings which admits a *section*, that is a
homomorphism `s : T →+* S` with `φ ∘ s = id_T`.  The multiplication map of a diagonal,
`Δ : A ⊗[R] A → A`, is the example: either coprojection is a section of it
(`Dualizing.lmul'_comp_includeLeftRingHom`).

For such a `φ` derived restriction of scalars `i_* : D(T) ⥤ D(S)` does more than reflect
isomorphisms: it **reflects isomorphy of objects**.  Two objects of `D(T)` whose restrictions to
`D(S)` are merely isomorphic -- by any isomorphism at all, with no linearity over `T` asserted --
are isomorphic in `D(T)`, because `Res_φ ⋙ Res_s = Res_{φ ∘ s} = Res_{id} ≅ 𝟭`, so the functor
`Res_s` carries the given isomorphism back to one of the original objects.  That is
`Dualizing.nonempty_iso_of_restrictScalars_iso_of_section`.

## What this buys

The consequence recorded here is the identification

`Ext_φ(Y) ≅ RHom_S(T, Y ⊗ᴸ_S X)`

in `D(T)`, for `Y` and `X` in `D(S)` such that `RHom_S(T, X)` is the unit of `D(T)` and the
single-ring tensor--Hom diagonal of [stacks 0ATK] at `(Y, X, i_*1_T)` is invertible.  Over `D(S)`
every factor of that identification is available with no coherence whatever: restricted derived
extension of scalars is tensoring with the algebra
(`Dualizing.ProjectionFormula.restrictExtendIso`), restricted derived coextension of scalars is
the internal Hom out of the algebra
(`Dualizing.ProjectionFormula.restrictCoextendInternalHomIso`), and [stacks 0ATK] is the
remaining step.  Only the descent of the resulting isomorphism from `D(S)` to `D(T)` is at issue,
and the section supplies it.

**This is what makes the linearity obligation disappear.**  Without a section the same chain of
isomorphisms over `D(S)` gives nothing in `D(T)`: one has to know that the composite is `T`-linear,
which is the hypothesis `hlin` of
`Dualizing.ProjectionFormula.isIso_restrict_derivedTensorHomDiagonalAlongRingHom` -- that the
projection formula is linear for the action of the algebra,
`Dualizing.ProjectionFormula.restrictedAction` -- and that hypothesis is a chain-level coherence
reduced in `StacksFrontier.RingTheory.Dualizing.UpperShriek.DiagonalComparisonBridge` to
`Dualizing.ProjectionFormula.ProjCounitCompat`, which is unproved.  At a `φ` with a section it is
not needed at all: the conclusion below carries nothing beyond its two displayed hypotheses.

## Main results

* `Dualizing.nonempty_iso_of_restrictScalars_iso_of_section` -- derived restriction of scalars
  along a ring map with a section reflects isomorphy of objects.
* `Dualizing.nonempty_extendScalars_iso_derivedHom_tensor_of_section` -- the identification
  `Ext_φ(Y) ≅ RHom_S(T, Y ⊗ᴸ_S X)` displayed above.
* `Dualizing.nonempty_extendScalars_iso_derivedHom_tensor_of_isIso_restrict` -- the same
  identification at a `φ` with no section, from invertibility of the restricted tensor--Hom
  diagonal along `φ` instead.

## What a section does not do

The section trick is available exactly where the surjection it splits is: at the multiplication
map of a diagonal.  It is *not* available at
`Dualizing.diagonalQuotient : B ⊗[R] B → B ⊗[A] B`, which is surjective but has no ring section,
nor at the structure map `A → B ⊗[A] B`.  So the isomorphism
`Dualizing.DiagonalQuotientDerivedHom` that [stacks 0E2H] still carries -- an isomorphism of
`D(B ⊗[A] B)` -- does **not** follow from the statements here: restriction along `A → B ⊗[A] B`
reflects invertibility of a morphism but not isomorphy of objects, and the comparison of
`StacksFrontier.RingTheory.Dualizing.RelativeCompositionCoextension` lands over `A`.  What the
results here discharge is the step of that residue which lives over the diagonal `A ⊗[R] A`,
where the linearity obligation was; the linearity of the projection formula over `B ⊗[A] B` is
untouched.

**The obstruction is not that no section has been found; it is that none can be.**  The retraction
above needs a ring homomorphism `s` with `φ ∘ s = id`, so its target is simultaneously a quotient
and a subring of its source.  Among the rings of [stacks 0E2H] the split surjections are the
multiplication maps `A ⊗[R] A → A`, `B ⊗[R] B → B` and `B ⊗[A] B → B`, whose targets are `A` and
`B`; no ring in play carries a split surjection onto `B ⊗[A] B`.  So isomorphy of objects of
`D(B ⊗[A] B)` is reflected from nowhere, and the descent of the identification to `D(B ⊗[A] B)`
*has* to be the invertibility of a `B ⊗[A] B`-linear morphism.  That route is
`Dualizing.nonempty_extendScalars_iso_derivedHom_tensor_of_isIso_restrict` below: it is the same
identification, with the section replaced by conservativity of derived restriction of scalars
applied to the tensor--Hom diagonal along `φ` itself.  What it costs is exactly the hypothesis of
`Dualizing.ProjectionFormula.isIso_restrict_derivedTensorHomDiagonalAlongRingHom` -- the linearity
of the projection formula -- together with [stacks 0ATK] over the *source* ring `B ⊗[R] B`, and the
module documentation of `StacksFrontier.RingTheory.Dualizing.RelativeComposition` records the
witness that defeats [stacks 0ATK] there.  So the two statements here and that lemma exhaust the
two ways of descending, and [stacks 0E2H] needs the second.

## Implementation notes

The retraction needs nothing new: `Dualizing.mapDerivedCategoryCompNatIso` descends the
isomorphism of functors `Res_φ ⋙ Res_s ≅ Res_{id_T}` of `ModuleCat.restrictScalarsComp'` to derived
categories, and `Dualizing.mapDerivedCategoryIdIso` is restriction along the identity read as the
identity functor.  So the composite is an isomorphism of *functors* on `D(T)`, not just a family of
isomorphisms of objects.

No `@[stacks]` attribute is placed here.  The retraction is elementary and the identification is a
step of [stacks 0E2H], whose tag sits on
`Dualizing.isRelativeDualizingComplex_derivedTensorProductOver`.

## References

* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0ATK](https://stacks.math.columbia.edu/tag/0ATK)
* [Stacks Project, Tag 0E2H](https://stacks.math.columbia.edu/tag/0E2H)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open StacksDraft.DerivedHom

universe u

namespace Dualizing

noncomputable section

attribute [local instance] HasDerivedCategory.standard

variable {S T : Type u} [CommRing S] [CommRing T]

/-- **Derived restriction of scalars along a ring map with a section is a retraction.**  If
`s : T →+* S` is a section of `φ : S →+* T`, then restricting along `φ` and then along `s` is the
identity functor of `D(T)`: the two restrictions compose to restriction along `φ ∘ s = id_T`. -/
def restrictScalarsDerivedSectionNatIso (φ : S →+* T) (s : T →+* S)
    (hs : φ.comp s = RingHom.id T) :
    (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory ⋙
        (ModuleCat.restrictScalars.{u} s).mapDerivedCategory ≅
      𝟭 (DerivedCategory (ModuleCat.{u} T)) :=
  mapDerivedCategoryCompNatIso (ModuleCat.restrictScalars.{u} φ)
      (ModuleCat.restrictScalars.{u} s) (ModuleCat.restrictScalars.{u} (RingHom.id T))
      (ModuleCat.restrictScalarsComp'.{u} s φ (RingHom.id T) hs.symm).symm ≪≫
    mapDerivedCategoryIdIso

/-- **Derived restriction of scalars along a ring map with a section reflects isomorphy.**  Let
`s : T →+* S` be a section of `φ : S →+* T` and let `U` and `V` be objects of `D(T)`.  Any
isomorphism between the restrictions of `U` and `V` along `φ` -- with no `T`-linearity asserted of
it -- yields an isomorphism `U ≅ V` in `D(T)`.

This is strictly more than conservativity of derived restriction of scalars, which reflects
invertibility of a *given* morphism of `D(T)`
(`CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategory`): the isomorphism here need not
come from `D(T)` at all.  Applying
`Dualizing.restrictScalarsDerivedSectionNatIso` to both sides is the whole proof. -/
theorem nonempty_iso_of_restrictScalars_iso_of_section (φ : S →+* T) (s : T →+* S)
    (hs : φ.comp s = RingHom.id T) {U V : DerivedCategory (ModuleCat.{u} T)}
    (e : (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.obj U ≅
      (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.obj V) : Nonempty (U ≅ V) :=
  ⟨((restrictScalarsDerivedSectionNatIso φ s hs).app U).symm ≪≫
    (ModuleCat.restrictScalars.{u} s).mapDerivedCategory.mapIso e ≪≫
      (restrictScalarsDerivedSectionNatIso φ s hs).app V⟩

/-- **The restricted identification `i_*Ext_φ(Y) ≅ i_*RHom_S(T, Y ⊗ᴸ_S X)`.**  For `Y` and `X` in
`D(S)`, an isomorphism `RHom_S(T, X) ≅ 1_T` and invertibility of the single-ring tensor--Hom
diagonal of [stacks 0ATK] at `(Y, X, i_*1_T)`, the four isomorphisms

`i_*Ext_φ(Y) ≅ Y ⊗ᴸ_S i_*1_T ≅ Y ⊗ᴸ_S RHom_S(i_*1_T, X) ≅ RHom_S(i_*1_T, Y ⊗ᴸ_S X)
  ≅ i_*RHom_S(T, Y ⊗ᴸ_S X)`

compose.  The first is `Dualizing.ProjectionFormula.restrictExtendIso`, the second is the given
isomorphism read through `Dualizing.ProjectionFormula.restrictCoextendInternalHomIso`, the third is
[stacks 0ATK] and the last is that comparison again.  Nothing is carried: no linearity of the
projection formula over `T` is used, because the statement is one of `D(S)`. -/
def restrictExtendScalarsIsoDerivedHomTensor (φ : S →+* T)
    (E : TotalDerivedExtensionScalars φ)
    (adj : (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory ⊣ Dualizing.derivedHom φ)
    (adjE : E.functor ⊣ (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory)
    (Y X : DerivedCategory (ModuleCat.{u} S))
    (e : (Dualizing.derivedHom φ).obj X ≅ derivedTensorUnit.{u} T)
    (hdiag : IsIso (Dualizing.derivedTensorHomDiagonalOverRing Y X
      (Dualizing.ProjectionFormula.restrictedAlgebra
        (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory))) :
    (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.obj (E.functor.obj Y) ≅
      (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.obj
        ((Dualizing.derivedHom φ).obj ((derivedHomAdjunctionOverRing S).tensor.obj (Y, X))) :=
  let iStar := (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory
  let alg := Dualizing.ProjectionFormula.restrictedAlgebra iStar
  let rci := Dualizing.ProjectionFormula.restrictCoextendInternalHomIso φ E iStar adj adjE
  (Dualizing.ProjectionFormula.restrictExtendIso φ E iStar adj).app Y ≪≫
    (derivedHomAdjunctionOverRing S).tensor.mapIso
      ((Iso.refl Y).prod ((iStar.mapIso e).symm ≪≫ rci.app X)) ≪≫
    asIso (Dualizing.derivedTensorHomDiagonalOverRing Y X alg) ≪≫ (rci.app _).symm

/-- **`Ext_φ(Y) ≅ RHom_S(T, Y ⊗ᴸ_S X)` for a ring map with a section.**  Let `φ : S →+* T` have a
section `s : T →+* S`, let `E` be any total left derived model of extension of scalars along `φ`,
and let `Y` and `X` be objects of `D(S)` such that derived coextension of scalars carries `X` to
the tensor unit of `D(T)` and the single-ring tensor--Hom diagonal of [stacks 0ATK] at
`(Y, X, i_*1_T)` is invertible.  Then derived extension of scalars of `Y` is derived coextension of
scalars of `Y ⊗ᴸ_S X`.

The content is `Dualizing.restrictExtendScalarsIsoDerivedHomTensor` over `D(S)` followed by
`Dualizing.nonempty_iso_of_restrictScalars_iso_of_section`, and the section is what removes the
linearity obligation; see the module documentation. -/
theorem nonempty_extendScalars_iso_derivedHom_tensor_of_section (φ : S →+* T) (s : T →+* S)
    (hs : φ.comp s = RingHom.id T) (E : TotalDerivedExtensionScalars φ)
    (adj : (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory ⊣ Dualizing.derivedHom φ)
    (adjE : E.functor ⊣ (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory)
    (Y X : DerivedCategory (ModuleCat.{u} S))
    (e : (Dualizing.derivedHom φ).obj X ≅ derivedTensorUnit.{u} T)
    (hdiag : IsIso (Dualizing.derivedTensorHomDiagonalOverRing Y X
      (Dualizing.ProjectionFormula.restrictedAlgebra
        (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory))) :
    Nonempty (E.functor.obj Y ≅
      (Dualizing.derivedHom φ).obj ((derivedHomAdjunctionOverRing S).tensor.obj (Y, X))) :=
  nonempty_iso_of_restrictScalars_iso_of_section φ s hs
    (restrictExtendScalarsIsoDerivedHomTensor φ E adj adjE Y X e hdiag)

/-- **`Ext_φ(Y) ≅ RHom_S(T, X ⊗ᴸ_S Y)` for a ring map with no section.**  Let `φ : S →+* T` be any
ring homomorphism, let `E` be a total left derived model of extension of scalars along `φ`, and let
`Y` and `X` be objects of `D(S)` with derived coextension of scalars carrying `X` to the tensor
unit of `D(T)`.  If derived restriction of scalars along `φ` carries the tensor--Hom diagonal along
`φ`, `Dualizing.ProjectionFormula.derivedTensorHomDiagonalAlongRingHom`, to an isomorphism at `X`,
then derived extension of scalars of `Y` is derived coextension of scalars of `X ⊗ᴸ_S Y`.

This is the companion of `Dualizing.nonempty_extendScalars_iso_derivedHom_tensor_of_section` at a
`φ` which has **no** section: the diagonal along `φ` is a morphism of `D(T)`, so derived
restriction of scalars reflects its invertibility
(`CategoryTheory.Functor.reflectsIsomorphisms_mapDerivedCategory`), and the displayed
identification is that morphism read through the left unitor and the given isomorphism.  Nothing
else is used; in particular no linearity of the projection formula over `T` enters *here* -- it
enters in producing the hypothesis, which is the conclusion of
`Dualizing.ProjectionFormula.isIso_restrict_derivedTensorHomDiagonalAlongRingHom`. -/
theorem nonempty_extendScalars_iso_derivedHom_tensor_of_isIso_restrict (φ : S →+* T)
    (E : TotalDerivedExtensionScalars φ)
    (adj : (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory ⊣ Dualizing.derivedHom φ)
    (Y X : DerivedCategory (ModuleCat.{u} S))
    (e : (Dualizing.derivedHom φ).obj X ≅ derivedTensorUnit.{u} T)
    (hdiag : IsIso ((ModuleCat.restrictScalars.{u} φ).mapDerivedCategory.map
      ((Dualizing.ProjectionFormula.derivedTensorHomDiagonalAlongRingHom φ E
        (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory adj Y).app X))) :
    Nonempty (E.functor.obj Y ≅
      (Dualizing.derivedHom φ).obj ((derivedHomAdjunctionOverRing S).tensor.obj (X, Y))) := by
  have hiso : IsIso ((Dualizing.ProjectionFormula.derivedTensorHomDiagonalAlongRingHom φ E
      (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory adj Y).app X) :=
    @Functor.ReflectsIsomorphisms.reflects _ _ _ _
      (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory _ _ _ _ hdiag
  exact ⟨(derivedTensorUnitLeft T (E.functor.obj Y)).symm ≪≫
    (derivedHomAdjunctionOverRing T).tensor.mapIso
      (e.symm.prod (Iso.refl (E.functor.obj Y))) ≪≫
    asIso ((Dualizing.ProjectionFormula.derivedTensorHomDiagonalAlongRingHom φ E
      (ModuleCat.restrictScalars.{u} φ).mapDerivedCategory adj Y).app X)⟩

end

end Dualizing

end
