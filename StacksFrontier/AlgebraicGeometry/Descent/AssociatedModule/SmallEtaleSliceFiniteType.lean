module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleDerivedConservativity
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleSliceConservativity
public import StacksFrontier.AlgebraicGeometry.PseudoCoherentSites.IteratedSliceFiniteType
import StacksCore.Tactic.StacksAttribute

/-!
# Finite type descends along `ε` on a Zariski slice

Let `S` be a scheme and let `ε : (S_étale, 𝒪) ⟶ (S_Zar, 𝒪_S)` be the morphism of ringed sites of
Stacks 08H7.  Stacks 08HD says that an `𝒪_S`-module `𝓕` is of finite type if and only if `ε^*𝓕`
is of finite type on the small étale site; the implication (2) ⇒ (1) is proved as
`AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_of_associatedModule`.  A descent of
pseudo-coherence along `ε` which proceeds by induction on a cohomological gap needs that
implication *localized*: from finite type of `(ε^*𝓕)|_{ε(V)}` for an open `V` of `S` it has to
conclude finite type of `𝓕|_V`.

This module proves that localization.  Unlike the zero-detection assertion of Stacks 08H8, whose
localization `AlgebraicGeometry.SmallEtale.isZero_over_of_isZero_over_associatedModule` is formal,
this one does **not** follow from the global statement: the unit of `ε^* ⊣ ε_*` is a
monomorphism, and a monomorphism does not carry finite type to its source.  So the geometric
argument of 08HD is re-run with the opens restricted to those below `V`.

## The argument

Every geometric input of 08HD is public and applies verbatim, the image open of an étale object
over `ε(V)` being automatically an open below `V`.  Three steps.

* **Unpack the hypothesis on the étale slice.**
  `Stacks.SheafOfModules.exists_covering_sieve_finite_generators_of_isFiniteType_over` turns
  finite type of `(ε^*𝓕)|_{ε(V)}` into a covering sieve of the object `ε(V)` of the small étale
  site over each of whose arrows `ε^*𝓕` has finitely many generating global sections.  This is
  where the iterated-slice dictionary of
  `StacksFrontier/AlgebraicGeometry/PseudoCoherentSites/IteratedSliceFiniteType.lean` is used: the
  covering family of `SheafOfModules.IsFiniteType` on a slice carries its generators on the
  *iterated* slices, and they have to be read on the small étale site itself.
* **Shrink around a point.**  A covering sieve of the small étale site is jointly surjective on
  points (`AlgebraicGeometry.SmallEtale.exists_mem_arrows_mem_range`), so a point `x` of `V` is in
  the image of some object `Z` of the sieve; over `Z` the generators are read sectionwise
  (`Stacks.SheafOfModules.exists_generates_of_hasFiniteGlobalGenerators_over`) and
  `AlgebraicGeometry.SmallEtale.exists_imageOpen_generates` — the heart of 08HD — replaces them,
  after shrinking `Z` to some `Z'` still containing `x`, by finitely many sections of `𝓕` over the
  image open of `Z'`, generating `𝓕`.
* **Assemble below `V`.**  That image open lies below `imageOpen Z ≤ imageOpen (ε V) = V`
  (`AlgebraicGeometry.SmallEtale.imageOpen_le_imageOpen` and `imageOpen_opensObj`), so the opens
  below `V` carrying finitely many generating sections of `𝓕` cover `V`, and
  `Stacks.SheafOfModules.isFiniteType_over_of_locally_finite_generators` concludes.

## Main results

* `SmallEtale.exists_opens_generates_of_isFiniteType_over_associatedModule`:
  around every point of `V` there is an open `W ≤ V` carrying finitely many sections generating
  `𝓕`.
* `SmallEtale.isFiniteType_over_of_isFiniteType_over_associatedModule`:
  **finite type descends along `ε` on a Zariski slice** — finite type of `(ε^*𝓕)|_{ε(V)}` forces
  finite type of `𝓕|_V`.
* `SmallEtale.isFiniteType_homology_over_of_isFiniteType_homology_over_associatedModule`:
  the same for a cohomology sheaf of an object of `D(𝒪_S)`, through the comparison
  `AlgebraicGeometry.SmallEtale.associatedModuleDerivedHomologyIso`.  This is the localization to
  a Zariski slice of
  `AlgebraicGeometry.SmallEtale.isFiniteType_homology_of_isFiniteType_homology_associatedModule`,
  and it is the form the induction of Stacks 09VA consumes.

## Implementation notes

**No `@[stacks]` attribute is attached to anything here.**  Stacks 08HD is carried, in both
implications, by
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleFiniteType.lean`; what is
below is the localization of its clause (2) ⇒ (1) to a slice, which is not a clause of 08HD or of
any other tag.  In particular it is an *input* to Stacks 08HE clause (2) ⇒ (1), which is proved in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtalePseudoCoherentDescent.lean`.

The finite-type condition is Mathlib's `SheafOfModules.IsFiniteType`, not the categorical
`SheafOfModules.IsFiniteTypeOnSite` which 08HD is stated with, because that is what the base case
of the induction,
`AlgebraicGeometry.RingedSite.isPseudoCoherentFrom_Q_of_isFiniteType_homology_general`, asks
for.  The two renderings are compared by `Stacks.SheafOfModules.isFiniteType_of_isFiniteTypeOnSite`
and its converse; neither is used here, the argument being run directly at Mathlib's condition.

The three sheafification instances on the doubly iterated slices of the small étale site are
established below rather than imported: the depth-one ones are established in
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleOpenCoverQuasicoherence.lean`
from essential smallness of the small étale site, and that argument simply has to be run once
more, essential smallness being inherited by a slice.  The Zariski ones are already instances, the
opens of `S` being small.

`ε^*` is spelled `SheafOfModules.pullback (structureMap B S hS)` — which is
`AlgebraicGeometry.SmallEtale.associatedModule` by definition — in the two statements about a
module, and `AlgebraicGeometry.SmallEtale.associatedModuleOfSheaf` in the statement about a
cohomology sheaf, because that is the spelling at which `mapDerivedCategory` is formed; this is
the convention of
`StacksFrontier/AlgebraicGeometry/Descent/AssociatedModule/SmallEtaleSliceConservativity.lean`.

## References

* [Stacks Project, Tag 08H7](https://stacks.math.columbia.edu/tag/08H7)
* [Stacks Project, Tag 08HD](https://stacks.math.columbia.edu/tag/08HD)
* [Stacks Project, Tag 08HE](https://stacks.math.columbia.edu/tag/08HE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03WT](https://stacks.math.columbia.edu/tag/03WT)
* [Stacks Project, Tag 09VA](https://stacks.math.columbia.edu/tag/09VA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u d d'

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Sheafification on the doubly iterated slices of the small étale site -/

/-- A slice of the small étale site of `S` at an object is essentially `u`-small, the site itself
being so (`AlgebraicGeometry.SmallEtale.essentiallySmall`).  `Over X` is the same type as
`CostructuredArrow (𝟭 _) X`, for which this is a Mathlib instance, but carries its own `Category`
instance, so the transport along `CategoryTheory.CostructuredArrow.toOver` is needed. -/
public instance essentiallySmall_smallEtaleOver (X : SmallEtale B S hS) :
    EssentiallySmall.{u} (Over X) :=
  (essentiallySmall_congr (CostructuredArrow.toOver (𝟭 (SmallEtale B S hS)) X).asEquivalence).mp
    inferInstance

/-- Abelian presheaves on a doubly iterated slice of the small étale site of `S` have a left exact
sheafification.  This is `AlgebraicGeometry.SmallEtale.hasSheafify_smallEtaleOver` one slice
further out; the hypothesis it needs is essential smallness of `Over X`. -/
public instance hasSheafify_smallEtaleOverOver (X : SmallEtale B S hS) (W : Over X) :
    HasSheafify (((topology B S hS).over X).over W) AddCommGrpCat.{u} :=
  hasSheafifyEssentiallySmallSite.{u} _ _

/-- Weak equivalences of abelian presheaves on a doubly iterated slice of the small étale site of
`S` are the locally bijective maps, again by essential smallness. -/
public instance wEqualsLocallyBijective_smallEtaleOverOver (X : SmallEtale B S hS) (W : Over X) :
    (((topology B S hS).over X).over W).WEqualsLocallyBijective AddCommGrpCat.{u} :=
  GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall _

/-! ### Finite type descends along `ε` on a Zariski slice -/

/-- **Around every point of an open `V` of `S` there is an open `W ≤ V` carrying finitely many
generating sections of `𝓕`**, provided `(ε^*𝓕)|_{ε(V)}` is of finite type.

See the module documentation for the three steps: unpack the hypothesis on the étale slice, shrink
an étale object around the point with
`AlgebraicGeometry.SmallEtale.exists_imageOpen_generates`, and bound the image open obtained by
`V`. -/
public theorem exists_opens_generates_of_isFiniteType_over_associatedModule (V : S.Opens)
    (𝓕 : SheafOfModules.{u} S.ringCatSheaf)
    (h : SheafOfModules.IsFiniteType
      (((SheafOfModules.pullback.{u} (structureMap B S hS)).obj 𝓕).over
        ((opensToSmallEtale B S hS).obj V)))
    (x : ↥S) (hx : x ∈ V) :
    ∃ W : S.Opens, W ≤ V ∧ x ∈ W ∧ ∃ (m : ℕ) (r : Fin m → 𝓕.val.obj (op W)),
      PresheafOfModules.Generates (Opens.grothendieckTopology ↥S) 𝓕.val r := by
  obtain ⟨T, hT, hTgen⟩ :=
    Stacks.SheafOfModules.exists_covering_sieve_finite_generators_of_isFiniteType_over
      (structureSheaf B S hS)
      ((SheafOfModules.pullback.{u} (structureMap B S hS)).obj 𝓕)
      ((opensToSmallEtale B S hS).obj V) h
  obtain ⟨Z, g, hg, w, hwx⟩ := exists_mem_arrows_mem_range B S hS hT
    (⟨x, hx⟩ : (toScheme B S hS).obj ((opensToSmallEtale B S hS).obj V))
  obtain ⟨σ, hσ⟩ := hTgen g hg
  obtain ⟨n, s, hs⟩ := Stacks.SheafOfModules.exists_generates_of_hasFiniteGlobalGenerators_over
    ((SheafOfModules.pullback.{u} (structureMap B S hS)).obj 𝓕) Z
    (Stacks.SheafOfModules.hasFiniteGlobalGenerators_of_generatingSections _ σ hσ)
  obtain ⟨Z', c, ⟨w', hw'⟩, m, r, hr⟩ := exists_imageOpen_generates B S hS 𝓕 Z s hs w
  have hZZ : Z'.obj.hom.hom.base w' = x := by
    have e1 : Z'.obj.hom.hom.base w'
        = Z.obj.hom.hom.base ((toScheme B S hS).map c w') := by
      rw [show Z'.obj.hom = c.hom.left ≫ Z.obj.hom from (Over.w c.hom).symm]; rfl
    rw [e1, hw', BigEtaleOver.hom_hom_eq B S hS g.hom]
    exact congrArg Subtype.val hwx
  refine ⟨imageOpen B S hS Z', ?_, ⟨w', hZZ⟩, m, r, hr⟩
  calc imageOpen B S hS Z' ≤ imageOpen B S hS Z := imageOpen_le_imageOpen B S hS c
    _ ≤ imageOpen B S hS ((opensToSmallEtale B S hS).obj V) := imageOpen_le_imageOpen B S hS g
    _ = V := imageOpen_opensObj B S hS V

/-- **Finite type descends along `ε` on a Zariski slice.**  Let `V` be an open of `S` and let `𝓕`
be an `𝒪_S`-module.  If the restriction of `ε^*𝓕` to the small étale site of `V` — that is, to the
slice of `S_étale` over `ε(V)` — is of finite type, then `𝓕|_V` is of finite type.

This is the localization to a slice of the implication (2) ⇒ (1) of Stacks 08HD,
`AlgebraicGeometry.SmallEtale.isFiniteTypeOnSite_of_associatedModule`.  It does not follow from
that implication formally, a monomorphism not carrying finite type to its source; the covering
witnessing the conclusion is the family of *all* opens below `V` carrying finitely many generating
sections, which
`AlgebraicGeometry.SmallEtale.exists_opens_generates_of_isFiniteType_over_associatedModule` shows
covers `V`, and `Stacks.SheafOfModules.isFiniteType_over_of_locally_finite_generators` assembles
it. -/
public theorem isFiniteType_over_of_isFiniteType_over_associatedModule (V : S.Opens)
    (𝓕 : SheafOfModules.{u} S.ringCatSheaf)
    (h : SheafOfModules.IsFiniteType
      (((SheafOfModules.pullback.{u} (structureMap B S hS)).obj 𝓕).over
        ((opensToSmallEtale B S hS).obj V))) :
    SheafOfModules.IsFiniteType (𝓕.over V) := by
  classical
  let I := {W : S.Opens // W ≤ V ∧ ∃ (m : ℕ) (r : Fin m → 𝓕.val.obj (op W)),
    PresheafOfModules.Generates (Opens.grothendieckTopology ↥S) 𝓕.val r}
  refine Stacks.SheafOfModules.isFiniteType_over_of_locally_finite_generators S.ringCatSheaf 𝓕 V
    (I := I) (fun i ↦ i.1) (fun i ↦ homOfLE i.2.1) ?_ ?_
  · rw [Opens.mem_grothendieckTopology]
    intro x hx
    obtain ⟨W, hWV, hxW, m, r, hr⟩ :=
      exists_opens_generates_of_isFiniteType_over_associatedModule B S hS V 𝓕 h x hx
    refine ⟨W, homOfLE hWV, ?_, hxW⟩
    exact Sieve.ofArrows_mk _ _ (⟨W, hWV, m, r, hr⟩ : I)
  · intro i
    obtain ⟨m, r, hr⟩ := i.2.2
    exact Stacks.SheafOfModules.exists_isFiniteType_generatingSections_of_generates 𝓕 r hr

section Derived

variable [HasDerivedCategory.{d} (SheafOfModules.{u} S.ringCatSheaf)]
  [HasDerivedCategory.{d'} (SheafOfModules.{u} (structureSheaf B S hS))]

/-- **Finite type of a cohomology sheaf descends along `ε^*_D` on a Zariski slice.**  If the
restriction of `Hⁿ(ε^*_D E)` to the small étale site of an open `V` of `S` is of finite type, then
so is `Hⁿ(E)|_V`, for an arbitrary `E : D(𝒪_S)` with no quasi-coherence hypothesis.

This is `AlgebraicGeometry.SmallEtale.isFiniteType_over_of_isFiniteType_over_associatedModule` fed
with the comparison
`AlgebraicGeometry.SmallEtale.associatedModuleDerivedHomologyIso`, which turns the hypothesis into
finite type of `(ε^*Hⁿ E)|_{ε(V)}`.  It is the localization to a slice of
`AlgebraicGeometry.SmallEtale.isFiniteType_homology_of_isFiniteType_homology_associatedModule`. -/
public theorem isFiniteType_homology_over_of_isFiniteType_homology_over_associatedModule
    (V : S.Opens) (E : DerivedCategory (SheafOfModules.{u} S.ringCatSheaf)) (n : ℤ)
    (h : SheafOfModules.IsFiniteType (((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (structureSheaf B S hS)) n).obj
      ((associatedModuleOfSheaf B S hS).mapDerivedCategory.obj E)).over
        ((opensToSmallEtale B S hS).obj V))) :
    SheafOfModules.IsFiniteType (((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} S.ringCatSheaf) n).obj E).over V) := by
  refine isFiniteType_over_of_isFiniteType_over_associatedModule B S hS V _ ?_
  exact Stacks.SheafOfModules.Site.isFiniteType_of_iso
    ((SheafOfModules.overFunctor.{u} (structureSheaf B S hS)
      ((opensToSmallEtale B S hS).obj V)).mapIso
        ((associatedModuleDerivedHomologyIso B S hS n).app E)) h

end Derived

end AlgebraicGeometry.SmallEtale

end
