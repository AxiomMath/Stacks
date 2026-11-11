module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFlatBaseChangeProved
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.Modules

/-!
# The criterion for quasi-coherence on a category fibred in groupoids (Stacks 06WK)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` be a presheaf of
modules over the structure sheaf of **Stacks 06TV**. **Stacks 06WK** says that `F` is a
quasi-coherent module on `𝒳` in the sense of **Stacks 06WG** if and only if

* (a) `F` is locally quasi-coherent (**Stacks 06WJ**), and
* (b) for *every* arrow `φ : x ⟶ y` of `𝒳`, lying over a morphism of schemes `a : U ⟶ V`, the
  comparison map `c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 06WC** is an
  isomorphism.

This file writes both sides of that biconditional in the vocabulary of the library — clause (b)
is `AlgebraicGeometry.Stack.HasSmallEtaleBaseChangeProperty`, the left-hand side is
`AlgebraicGeometry.Stack.IsQuasicoherentFppf` — and proves the implications between them that
are available. The biconditional itself is proved downstream, in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.QuasicoherentIffComparisonIso`, as
`Stack.isQuasicoherentFppf_iff_isLocallyQuasicoherent_and_isIso_sheafifiedRestrictComparison`,
which carries the tag; see "Where the biconditional is proved" below.

The notions used are the ones of this development's 06WJ/06WC chain and no other:
`AlgebraicGeometry.Stack.IsLocallyQuasicoherent` for local quasi-coherence, and the restriction
to the small étale site is `AlgebraicGeometry.Stack.restrictModuleToSmallEtale`, whose
underlying abelian presheaf is the restriction of **Stacks 06W1**. Quasi-coherence on a site is
`SheafOfModules.IsQuasicoherentOnSite`, the predicate of **Stacks 03DL**(6), so the left-hand
side is the object part of `AlgebraicGeometry.FibredSite.quasicoherentModules` of 06WG.

## Main definitions

* `AlgebraicGeometry.Stack.HasSmallEtaleBaseChangeProperty`: **clause (b) of Stacks 06WK**, the
  comparison map of Stacks 06WC being an isomorphism along every arrow of `𝒳`.
* `AlgebraicGeometry.Stack.IsQuasicoherentFppf`: **the left-hand side of Stacks 06WK**, that the
  presheaf of modules is a sheaf for the inherited fppf topology of Stacks 06TP and is
  quasi-coherent on that site.

## Main results

* `AlgebraicGeometry.Stack.associatedTopology_etale_le_fppf`: the inherited étale topology is
  coarser than the inherited fppf topology.
* `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_of_hasSmallEtaleBaseChangeProperty` and
  `AlgebraicGeometry.Stack.hasFlatLfpBaseChangeProperty_of_hasSmallEtaleBaseChangeProperty`:
  clause (b) implies the flat base change property of **Stacks 0762** and hypothesis (b) of
  **Stacks 076T**, which ask the same isomorphism of fewer arrows.
* `AlgebraicGeometry.Stack.hasSmallEtaleBaseChangeProperty_of_iso`: clause (b) depends only on
  the isomorphism class of the presheaf of modules.
* `AlgebraicGeometry.Stack.fibredSite_ringStructureSheafCore_fppf_eq` and
  `AlgebraicGeometry.Stack.isQuasicoherentFppf_iff_isQuasicoherentOnSite_fibredSite`: **the two
  spellings of the structure sheaf of `𝒳` agree**, so the left-hand side written here is
  membership in the category `AlgebraicGeometry.FibredSite.quasicoherentModules` of Stacks 06WG.
  This is the bridge between the `AlgebraicGeometry.FibredSite` vocabulary of 06WG and 06WI and
  the `AlgebraicGeometry.Stack` vocabulary of 06WJ and 06WC, which any route through 06WI has
  to cross.
* `AlgebraicGeometry.Stack.isSheaf_etale_of_isQuasicoherentFppf`: **the first clause of local
  quasi-coherence, from the left-hand side, unconditionally.** This is the step the source takes
  with "hence a sheaf for the étale topology".
* `AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherent_of_baseChange`: **the fppf
  sheaf condition from (a) and (b)**, which is the sheaf half of the converse implication of
  Stacks 06WK.

## Where the biconditional is proved

Stacks 06WK, both directions, is
`Stack.isQuasicoherentFppf_iff_isLocallyQuasicoherent_and_isIso_sheafifiedRestrictComparison`.
Its clause (2) is stated there with the comparison map
`AlgebraicGeometry.Stack.sheafifiedRestrictComparison` of sheaves of modules, the adjunct under
sheafification of the comparison of Stacks 06WC. Both sides are read on the affine subcategory
of Stacks 0H0A: quasi-coherence on `𝒳` is, for an étale sheaf, the condition that the
base-change maps of the restriction maps between objects lying over affine schemes be bijective
(Stacks 0H0C and 0H0E, with Stacks 0EM8 for the passage from the inherited étale site to the
inherited fppf one), and between affine objects that condition is the invertibility of `c_φ`.
No hypothesis is carried there beyond those of the source.

Clause (b) is used in full by what is proved here, and nothing below weakens it: the arrows it
quantifies over are all the arrows of `𝒳`, as in the source.

## References

* [Stacks Project, Tag 06WK](https://stacks.math.columbia.edu/tag/06WK)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WG](https://stacks.math.columbia.edu/tag/06WG)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 0EM8](https://stacks.math.columbia.edu/tag/0EM8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-! ### The inherited étale topology is coarser than the inherited fppf topology -/

/-- The topology `𝒳` inherits from the big étale site is coarser than the one it inherits from
the big fppf site: a family of strongly cartesian arrows whose images form a selected étale
covering is one whose images form a selected covering. -/
theorem associatedTopology_etale_le_fppf :
    associatedTopology B S hS p (etaleTopology B) ≤ associatedTopology B S hS p B.topology :=
  Precoverage.toGrothendieck_mono fun _ _ hR ↦
    ⟨hR.1, over_le_over B S hS (etaleTopology_le_topology B) _ hR.2⟩

/-! ### The two sides of Stacks 06WK -/

/-- **Clause (b) of Stacks 06WK.** The comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 06WC** is an isomorphism along *every*
arrow `φ : x ⟶ y` of `𝒳`.

This is the flat base change property of **Stacks 0762** with the flatness condition on the
morphism below the arrow dropped, which is what 06WK asks; the comparison map is the one of
`AlgebraicGeometry.Stack.restrictModulePullbackComparison`, so the sections of the module live
in the universe of the schemes, for the reason recorded in the implementation notes of
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SmallEtaleModuleComparison`. -/
noncomputable abbrev HasSmallEtaleBaseChangeProperty (τ : GrothendieckTopology B.Schemes)
    (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj) : Prop :=
  ∀ {x y : 𝒳} (φ : x ⟶ y),
    IsIso (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F)

/-- Clause (b) of Stacks 06WK implies the flat base change property of **Stacks 0762**, which
asks the same isomorphism only of the arrows lying over a flat morphism of schemes. -/
theorem hasFlatBaseChangeProperty_of_hasSmallEtaleBaseChangeProperty
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (hF : HasSmallEtaleBaseChangeProperty B E h S hS p hp τ hτ F) :
    HasFlatBaseChangeProperty B E h S hS p hp τ hτ F :=
  fun φ _ => hF φ

/-- Clause (b) of Stacks 06WK implies hypothesis (b) of **Stacks 076T**, which asks the same
isomorphism only of the arrows lying over a morphism of schemes that is flat and locally of
finite presentation. -/
theorem hasFlatLfpBaseChangeProperty_of_hasSmallEtaleBaseChangeProperty
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (hF : HasSmallEtaleBaseChangeProperty B E h S hS p hp τ hτ F) :
    HasFlatLfpBaseChangeProperty B E h S hS p hp τ hτ F :=
  fun φ _ _ => hF φ

/-- Clause (b) of Stacks 06WK transports along an isomorphism of presheaves of modules, the
comparison map below a fixed arrow depending only on the isomorphism class of the module. -/
theorem hasSmallEtaleBaseChangeProperty_of_iso (τ : GrothendieckTopology B.Schemes)
    (hτ : τ ≤ B.topology)
    {F F' : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj} (e : F ≅ F')
    (hF : HasSmallEtaleBaseChangeProperty B E h S hS p hp τ hτ F) :
    HasSmallEtaleBaseChangeProperty B E h S hS p hp τ hτ F' :=
  fun ψ => isIso_restrictModulePullbackComparison_of_iso B E h S hS p hp τ hτ e ψ (hF ψ)

/-- **The left-hand side of Stacks 06WK.** A presheaf of modules over the structure sheaf of
`𝒳` is a *quasi-coherent module on `𝒳`* when it is a sheaf for the inherited fppf topology of
**Stacks 06TP** and is quasi-coherent on that site in the sense of **Stacks 03DL**(6). Being an
object of `AlgebraicGeometry.FibredSite.quasicoherentModules` is this, which is what
**Stacks 06WG** calls a quasi-coherent module.

The sheaf condition is existentially quantified rather than taken as an argument because it is
part of what the left-hand side of 06WK asserts; the underlying presheaf of rings is the same
for the inherited étale and fppf topologies, by
`AlgebraicGeometry.Stack.ringStructureSheafCore_obj`, so the presheaf of modules is read for the
fppf topology without changing anything but the sheaf condition asserted of it. -/
noncomputable abbrev IsQuasicoherentFppf
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) : Prop :=
  ∃ hF : Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F.presheaf,
    (⟨F, hF⟩ : SheafOfModules.{u}
      (ringStructureSheafCore B S hS p hp B.topology le_rfl)).IsQuasicoherentOnSite

/-! ### The left-hand side is quasi-coherence in the sense of Stacks 06WG -/

/-- The coefficient sheaf of rings the 06WJ/06WC chain uses at the fppf topology *is* the one
**Stacks 06WG** takes quasi-coherent modules over: both are `p.op` followed by the structure
sheaf of the big fppf category over `S`, read for the inherited fppf topology of Stacks 06TP.

The two spellings differ only in how the topology is named — by an
`AlgebraicGeometry.SiteKind` on one side, by a topology on `B.Schemes` together with a proof
that it is coarser than the fppf one on the other — and the sheaf conditions are propositions,
so the two sheaves of rings are equal by reflexivity. -/
theorem fibredSite_ringStructureSheafCore_fppf_eq :
    FibredSite.ringStructureSheafCore B S hS p hp .fppf =
      ringStructureSheafCore B S hS p hp B.topology le_rfl :=
  rfl

/-- **The left-hand side of Stacks 06WK is quasi-coherence in the sense of Stacks 06WG.** It
asserts of the presheaf of modules exactly that it is an object of
`AlgebraicGeometry.FibredSite.quasicoherentModules`, the category 06WG defines, the two
spellings of the coefficient sheaf of rings agreeing by
`AlgebraicGeometry.Stack.fibredSite_ringStructureSheafCore_fppf_eq`. -/
theorem isQuasicoherentFppf_iff_isQuasicoherentOnSite_fibredSite
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj) :
    IsQuasicoherentFppf B S hS p hp F ↔
      ∃ hF : Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F.presheaf,
        (⟨F, hF⟩ : SheafOfModules.{u}
          (FibredSite.ringStructureSheafCore B S hS p hp .fppf)).IsQuasicoherentOnSite :=
  Iff.rfl

/-! ### Stacks 06WK, the implications that are available -/

/-- **The first clause of local quasi-coherence, from the left-hand side of Stacks 06WK.** A
quasi-coherent module on `𝒳` is a sheaf for the inherited étale topology, that topology being
coarser than the inherited fppf one.

This is the step the source's proof takes with "hence a sheaf for the étale topology". -/
theorem isSheaf_etale_of_isQuasicoherentFppf
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hF : IsQuasicoherentFppf B S hS p hp F) :
    Presheaf.IsSheaf (associatedTopology B S hS p (etaleTopology B)) F.presheaf :=
  hF.elim fun hs _ => hs.of_le (associatedTopology_etale_le_fppf B S hS p)

/-- **The sheaf half of the converse implication of Stacks 06WK.** A locally quasi-coherent
presheaf of modules whose comparison maps of **Stacks 06WC** are isomorphisms along every arrow
of `𝒳` is a sheaf for the inherited fppf topology of **Stacks 06TP**.

Clause (b) of 06WK gives hypothesis (b) of **Stacks 076T** by
`AlgebraicGeometry.Stack.hasFlatLfpBaseChangeProperty_of_hasSmallEtaleBaseChangeProperty`, and
the conclusion is then Stacks 076T itself,
`AlgebraicGeometry.Stack.isSheaf_fppf_of_isLocallyQuasicoherent_of_flatBaseChange`. -/
theorem isSheaf_fppf_of_isLocallyQuasicoherent_of_baseChange
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F)
    (hbc : HasSmallEtaleBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F) :
    Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F.presheaf :=
  isSheaf_fppf_of_isLocallyQuasicoherent_of_flatBaseChange B E h S hS p hp F hlqc
    (hasFlatLfpBaseChangeProperty_of_hasSmallEtaleBaseChangeProperty B E h S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) F hbc)

end AlgebraicGeometry.Stack

end
