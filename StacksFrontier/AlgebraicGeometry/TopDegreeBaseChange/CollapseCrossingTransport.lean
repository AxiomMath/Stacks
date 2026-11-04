module

public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.CollapseCrossingGeometric

/-!
# The collapse crossing of [Stacks, Tag 0EX3] (c) at the spellings the `ψ` side carries

`…TopDegreeBaseChange.collapse_crossing_restrictedMorphism` (`CollapseCrossingGeometric.lean`)
crosses the two readings of Grothendieck's comparison of [Stacks, Tag 01XK] that the two sides of
conclusion (c) of [Stacks, Tag 0EX3] arrive in. It is stated at the two spellings the three
abstract squares are stated at: the pushforward along
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism`, and the `ψ`-side collapse indexed by the
composite functor `E ⋙ (-|_{f⁻¹V})` at the object `Z`.

The `ψ` side of (c) carries neither: `…TopDegreeBaseChange.prefix_transport_eq`
`_openSubschemeSectionsComparison_comp` (`FactorOnePrefixTransport.lean`) is stated at Mathlib's
`f ∣_ V` and at the collapse indexed by `…TopDegreeBaseChange.openSubschemeRestriction f V` at the
object `E.obj Z`. This file performs those two passages, so that the crossing is available at the
spellings the join meets it at.

## Main results

* `…TopDegreeBaseChange.collapse_index_crossing_restrictedMorphism`: **the index passage.**
  Grothendieck's collapse at the index functor `E ⋙ (-|_{f⁻¹V})` read at `Z` is the collapse at
  the index functor `openSubschemeRestriction f V` read at `E.obj Z`. Both components are the
  conjugated `CategoryTheory.ShortComplex.mapHomologyIso` that
  `Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_hom_app` prints, and that formula names the
  index only through the object, so the two readings are the same morphism.
* `…TopDegreeBaseChange.collapse_index_crossing_restrictedMorphism`: the same passage at the other
  spelling of the restricted morphism, the one `collapse_crossing_restrictedMorphism` is stated at.

The **morphism passage** — the whole equation of `collapse_crossing_restrictedMorphism`
transported to Mathlib's `f ∣_ V` — is *not* here and is not proved anywhere. What is available is the
vocabulary in which that equation can be *stated*, in
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/CollapseCrossingMorphismRestrict.lean`; see its
implementation notes for why the transport itself is still open.

## Implementation notes

*Why the index passage is not a general lemma.* The two components whose equality it asserts have
types `G(Rᵖ F (E'.obj Z)) ⟶ Rᵖ(F ⋙ G)(E'.obj Z)` and the same at `(openSubschemeRestriction f V)`
`.obj (E.obj Z)`. At variables of abstract categories those two objects are two unrelated terms,
so the equation does not even typecheck without an `eqToHom` transport; stated at the geometric
data they are the same term by `rfl`, and the equation typechecks on the nose. So the
general content is exactly `…AffineBase.rightDerivedCompNatIso_hom_app`, which is proved, and the
index passage is that lemma applied twice and joined by `Eq.trans` — the second application
needing its pointwise instance re-seated at the second spelling of the object, instance search
being syntactic.

*Why a **pointwise hypothesis** transports by `simp only` and not by `rw` — and why the morphism
passage does not transport by either.*
`…SchemeHigherDirectImage.toShHom_morphismRestrict` equates the two morphisms of sheaved spaces,
but `rw` on it leaves a motive that is not type correct: `CategoryTheory.Functor`
`.mapHomologicalComplex` takes the additivity of its argument as an instance argument, and the
instance that fires at `restrictedMorphism` is the bespoke `…HigherDirectImage`
`.modulePushforwardRestrictedMorphism_additive`. `simp only` discharges exactly this, the
dependency being on a proof of a `Prop`-valued class; raising the priority of the generic
additivity instance does not help. This is the behaviour
`AlgebraicGeometry/ProjectiveCoherentImage/Basic.lean` records, and
`…TopDegreeBaseChange.hres_openSubschemeTopSections` already uses it on the pointwise hypothesis
alone. `CategoryTheory.ShortComplex.PreservesLeftHomologyOf` is `Prop`-valued too, so the
collapse's explicit pointwise argument transports by the same mechanism and no `eqToIso` has to be
built. That mechanism does **not** extend to the crossing's *equation*: there the morphism occurs
in the types of both ends, `simp only` leaves it untouched and `rw` has no type-correct motive
(see `CollapseCrossingMorphismRestrict.lean`). The pointwise case works precisely
because the only dependency is on a proof of a `Prop`-valued class.

*No `@[stacks …]` attribute is placed.* These are passages between spellings of one compatibility
of instantiations of Grothendieck's collapse, and conclusion (c) of [Stacks, Tag 0EX3] is proved
elsewhere, as `…TopDegreeBaseChange.isIso_topDirectImageBaseChangeMap`
(`BaseChangeTopDegreeConclusion.lean`), by a route that does not use this file.

## References

* [Stacks Project, Tag 0EX3](https://stacks.math.columbia.edu/tag/0EX3)
* [Stacks Project, Tag 01E1](https://stacks.math.columbia.edu/tag/01E1)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01XK](https://stacks.math.columbia.edu/tag/01XK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.HigherDirectImage
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.AffineBase
open Stacks.AlgebraicGeometry.SchemeHigherDirectImage (toShHom_morphismRestrict)

namespace Stacks.AlgebraicGeometry.TopDegreeBaseChange

universe u

attribute [local instance 10000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens) (p : ℕ)
  {Dc : Type*} [Category* Dc]
  (E : Dc ⥤ SheafOfModules.{u} (structureSheafRing X.toSheafedSpace))

/-! ### The index passage -/

/-- **Grothendieck's collapse at the two index spellings the join meets it at.** For a morphism of
schemes `f : X ⟶ Y`, an open `V ⊆ Y`, a functor `E : Dc ⥤ Mod(𝒪_X)`, a degree `p` and an object
`Z`, the component at `Z` of the collapse of [Stacks, Tag 01XK] at the pair
`((f ∣_ V)_*, Γ(V, ⊤, -))` indexed by `E ⋙ (-|_{f⁻¹V})` is its component at `E.obj Z` when it is
indexed by `…TopDegreeBaseChange.openSubschemeRestriction f V` instead — which is the index the
`ψ` side of conclusion (c) of [Stacks, Tag 0EX3] carries, in
`…TopDegreeBaseChange.prefix_transport_eq_openSubschemeSectionsComparison_comp`.

Both are the conjugated `CategoryTheory.ShortComplex.mapHomologyIso` that
`Stacks.Cohomology.AffineBase.rightDerivedCompNatIso_hom_app` prints, and that formula names the
index functor only through the object it is applied to; the two objects are the same term by
`rfl`. **Nothing is assumed** of `f`, of `V`, of `E`, of `Z` or of `p` beyond the collapse's own
pointwise hypothesis, asked here at both index functors. -/
theorem collapse_index_crossing_morphismRestrict
    (hG : ∀ Z : Dc, (sectionsOverOpen (V : Scheme).toRingedSpace ⊤).PreservesLeftHomologyOf
      ((((modulePushforward (f ∣_ V).toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ openSubschemeRestriction f V).obj Z)).cocomplex).sc p))
    (hpsi : ∀ M : SheafOfModules.{u} (structureSheafRing X.toSheafedSpace),
      (sectionsOverOpen (V : Scheme).toRingedSpace ⊤).PreservesLeftHomologyOf
      ((((modulePushforward (f ∣_ V).toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((openSubschemeRestriction f V).obj M)).cocomplex).sc p))
    (Z : Dc) :
    (rightDerivedCompNatIso (E ⋙ openSubschemeRestriction f V)
        (modulePushforward (f ∣_ V).toLRSHom.toShHom)
        (sectionsOverOpen (V : Scheme).toRingedSpace ⊤) p hG).hom.app Z =
      (rightDerivedCompNatIso (openSubschemeRestriction f V)
        (modulePushforward (f ∣_ V).toLRSHom.toShHom)
        (sectionsOverOpen (V : Scheme).toRingedSpace ⊤) p hpsi).hom.app (E.obj Z) := by
  have := hG Z
  have := hpsi (E.obj Z)
  exact (rightDerivedCompNatIso_hom_app _ _ _ p hG Z).trans
    (rightDerivedCompNatIso_hom_app _ _ _ p hpsi (E.obj Z)).symm

/-- **The index passage, inverted.** The `ψ` side of conclusion (c) of [Stacks, Tag 0EX3] carries
the collapse **inverted** — `…TopDegreeBaseChange.prefix_transport_eq`
`_openSubschemeSectionsComparison_comp` reads it as `(rightDerivedCompNatIso …).inv.app M` — so
this is the form in which the passage is consumed. Two inverses of equal isomorphisms, by
`CategoryTheory.Iso.inv_eq_inv`; the hypotheses are `collapse_index_crossing_morphismRestrict`'s
and nothing besides. -/
theorem collapse_index_crossing_morphismRestrict_inv
    (hG : ∀ Z : Dc, (sectionsOverOpen (V : Scheme).toRingedSpace ⊤).PreservesLeftHomologyOf
      ((((modulePushforward (f ∣_ V).toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ openSubschemeRestriction f V).obj Z)).cocomplex).sc p))
    (hpsi : ∀ M : SheafOfModules.{u} (structureSheafRing X.toSheafedSpace),
      (sectionsOverOpen (V : Scheme).toRingedSpace ⊤).PreservesLeftHomologyOf
      ((((modulePushforward (f ∣_ V).toLRSHom.toShHom).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((openSubschemeRestriction f V).obj M)).cocomplex).sc p))
    (Z : Dc) :
    (rightDerivedCompNatIso (E ⋙ openSubschemeRestriction f V)
        (modulePushforward (f ∣_ V).toLRSHom.toShHom)
        (sectionsOverOpen (V : Scheme).toRingedSpace ⊤) p hG).inv.app Z =
      (rightDerivedCompNatIso (openSubschemeRestriction f V)
        (modulePushforward (f ∣_ V).toLRSHom.toShHom)
        (sectionsOverOpen (V : Scheme).toRingedSpace ⊤) p hpsi).inv.app (E.obj Z) :=
  by
  rw [← IsIso.inv_eq_inv, NatIso.inv_inv_app, NatIso.inv_inv_app]
  exact collapse_index_crossing_morphismRestrict f V p E hG hpsi Z

/-! ### The index passage at the crossing's own spelling of the restricted morphism -/

/-- **The index passage at the spelling `collapse_crossing_restrictedMorphism` is stated at.** The
same statement as `collapse_index_crossing_morphismRestrict`, with the pushforward along
`Stacks.Cohomology.HigherDirectImage.restrictedMorphism` and the restriction spelled
`moduleRestriction X (preimageOpen f V)` throughout — the spelling the three abstract squares and
the crossing use, and the one at which the bespoke
`…HigherDirectImage.modulePushforwardRestrictedMorphism_additive` is found.

This is the form that composes with
`…TopDegreeBaseChange.collapse_crossing_restrictedMorphism`: it reads that crossing's `ψ`-side
collapse at the single module `E.obj Z` rather than at the composite index functor. The two
spellings of the restricted morphism cannot be mixed inside one statement — see the implementation notes of
`BaseChangeSectionsTail.lean` — so the passage is proved at each of them. **Nothing is assumed**
of `f`, of `V`, of `E`, of `Z` or of `p` beyond the collapse's own pointwise hypothesis, asked at
both index functors. -/
theorem collapse_index_crossing_restrictedMorphism
    (hG : ∀ Z : Dc, (sectionsOnOpenSubschemeTop V).PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj Z)).cocomplex).sc p))
    (hsingle : ∀ M : SheafOfModules.{u} (structureSheafRing X.toSheafedSpace),
      (sectionsOnOpenSubschemeTop V).PreservesLeftHomologyOf
      ((((modulePushforward (restrictedMorphism f.toLRSHom.toShHom V)).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj
        (injectiveResolution ((moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V)).obj M)).cocomplex).sc p))
    (Z : Dc) :
    (rightDerivedCompNatIso (E ⋙ moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V))
        (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V))
        (sectionsOnOpenSubschemeTop V) p hG).hom.app Z =
      (rightDerivedCompNatIso (moduleRestriction X.toSheafedSpace
          (preimageOpen f.toLRSHom.toShHom V))
        (modulePushforward (restrictedMorphism f.toLRSHom.toShHom V))
        (sectionsOnOpenSubschemeTop V) p hsingle).hom.app (E.obj Z) := by
  have := hG Z
  have := hsingle (E.obj Z)
  exact (rightDerivedCompNatIso_hom_app _ _ _ p hG Z).trans
    (rightDerivedCompNatIso_hom_app _ _ _ p hsingle (E.obj Z)).symm

end Stacks.AlgebraicGeometry.TopDegreeBaseChange

end
