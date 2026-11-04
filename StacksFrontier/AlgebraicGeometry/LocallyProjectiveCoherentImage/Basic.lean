module

public import StacksFrontier.AlgebraicGeometry.CoherentImageBaseIso.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentImageLocalBase.Basic
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.ProjectiveMorphism
public import StacksFrontier.AlgebraicGeometry.QuasiProjective.HProjective

/-!
# Higher direct images along a locally projective morphism are coherent

Let `S` be a locally Noetherian scheme, let `f : X ⟶ S` be locally H-projective and let `ℱ` be a
coherent `𝒪_X`-module. Then `R^i f_* ℱ` is coherent for every `i ≥ 0`. This is
[Stacks, Tag 02O4].

The proof is the source's, in three reductions, each of which is local on the base and uses the
`ℕ`-indexed locality of `AlgebraicGeometry.CoherentImageLocalBase`:

* local H-projectivity gives a cover of `S` by opens over which `f` is H-projective on the nose
  (the definition supplies this for `pullback.snd f (𝒰.f i)`, which is isomorphic as an arrow to
  `f ∣_ (𝒰.f i).opensRange`), so the question reduces to an H-projective morphism;
* an H-projective morphism restricts to an H-projective morphism over any open of the base, so
  covering the base by affine opens reduces the question to an affine base;
* over an affine base the morphism is H-projective into `ℙⁿ` over the spectrum of a Noetherian
  ring, which is `Stacks.ProjCoherentCohomologyFinite`
  `.isCoherent_rightDerived_of_isProjectiveMorphism`.

The passage from `Spec Γ(T, 𝒪)` back to an arbitrary affine `T` is
`Stacks.AlgebraicGeometry.CoherentImageBaseIso.isCoherent_rightDerived_comp_isIso_iff`, an affine
scheme being its own spectrum only up to `AlgebraicGeometry.Scheme.isoSpec`.

## Main results

* `AlgebraicGeometry.IsProjectiveMorphism.restrict`: **H-projectivity restricts to an open of the
  base.**
* `AlgebraicGeometry.LocallyProjectiveCoherentImage`
  `.isCoherent_rightDerived_of_isProjectiveMorphism`: the conclusion for an H-projective morphism
  over a locally Noetherian base.
* `AlgebraicGeometry.LocallyProjectiveCoherentImage`
  `.isCoherent_rightDerived_of_isLocallyProjective`: **[Stacks, Tag 02O4].**

## Implementation notes

**The indexing is `ℕ`, and that is both faithful and necessary.** The tag asserts coherence of
`R^i f_* ℱ` for `i ≥ 0`, which is exactly a statement about
`CategoryTheory.Functor.rightDerived` quantified over `i : ℕ`; no claim is made in negative
degrees, where the derived functor vanishes anyway. It is also the only indexing in which this
theorem can be stated at all in the present import closure: `Functor.rightDerivedPlus` requires a
`CategoryTheory.HasDerivedCategory` instance, the library has two incompatible ones for
`X.Modules`, and the global `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` wins here while
the existing `ℤ`-indexed locality lemmas were compiled against
`CategoryTheory.HasDerivedCategory.standard`. See
`StacksFrontier/AlgebraicGeometry/CoherentImageLocalBase/Basic.lean`, which exists for this reason.

**Properness is never assumed.** It is a consequence — `isProper_of_isProjectiveMorphism` — and
is used only where the finiteness result over `Spec R` needs it.

**The arrow-isomorphism transport is Mathlib's, twice.**
`AlgebraicGeometry.morphismRestrictOpensRange` turns the definition's `pullback.snd f (𝒰.f i)`
into `f ∣_ (𝒰.f i).opensRange`, and `AlgebraicGeometry.morphismRestrictEq` moves between two
spellings of the same open; both are fed
to `AlgebraicGeometry.IsProjectiveMorphism.of_iso`, which is what makes H-projectivity an
isomorphism-invariant of an arrow. The module documentation of
`AlgebraicGeometry.ProjectiveCoherentImage` records that no such transport existed for Tag 01W8's
other projectivity predicate; for `IsProjectiveMorphism` it does, and that is what this file uses.

**The namespace avoids a `Stacks.` prefix** so that `SheafOfModules.IsCoherent` resolves to the
root class of [Stacks, Tag 01BW] rather than to the distinct `Stacks.SheafOfModules.IsCoherent`.

## References

* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
* [Stacks Project, Tag 01W8](https://stacks.math.columbia.edu/tag/01W8)
* [Stacks Project, Tag 01WF](https://stacks.math.columbia.edu/tag/01WF)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry
open Stacks.ProjCoherentCohomologyFinite Stacks.AlgebraicGeometry.CoherentImageBaseIso
open AlgebraicGeometry.CoherentImageLocalBase

universe u

namespace AlgebraicGeometry

/-- H-projectivity transports along an isomorphism of arrows. -/
private theorem isProjectiveMorphism_of_arrow_iso {X Y X' Y' : Scheme.{u}} {g : X ⟶ Y}
    {g' : X' ⟶ Y'} (e : Arrow.mk g ≅ Arrow.mk g') (hg : IsProjectiveMorphism g) :
    IsProjectiveMorphism g' :=
  hg.of_iso (Arrow.leftFunc.mapIso e) (Arrow.rightFunc.mapIso e) (Arrow.w e.hom)

/-- **H-projectivity restricts to an open of the base.** If `g` is H-projective then so is
`g ∣_ V` for every open `V` of its target.

H-projectivity is stable under base change ([Stacks, Tag 01WF]), so `pullback.snd g V.ι` is
H-projective; `AlgebraicGeometry.morphismRestrictOpensRange` identifies that arrow with
`g ∣_ V.ι.opensRange` and `AlgebraicGeometry.morphismRestrictEq` rewrites the open as `V`. -/
theorem IsProjectiveMorphism.restrict {X Y : Scheme.{u}} {g : X ⟶ Y}
    (hg : IsProjectiveMorphism g) (V : Y.Opens) : IsProjectiveMorphism (g ∣_ V) := by
  have h1 := isProjectiveMorphism_of_arrow_iso (morphismRestrictOpensRange g V.ι).symm
    (hg.baseChange V.ι)
  exact isProjectiveMorphism_of_arrow_iso
    (morphismRestrictEq g (Scheme.Opens.opensRange_ι V)) h1

namespace LocallyProjectiveCoherentImage

/-- **Higher direct images along an H-projective morphism to an affine Noetherian base are
coherent**, for an arbitrary affine base rather than a spectrum. The base is its own spectrum up
to `AlgebraicGeometry.Scheme.isoSpec`; H-projectivity transports along that isomorphism by
`AlgebraicGeometry.IsProjectiveMorphism.of_iso`, the conclusion over the spectrum is
`Stacks.ProjCoherentCohomologyFinite.isCoherent_rightDerived_of_isProjectiveMorphism`, and it
comes back along the isomorphism by
`Stacks.AlgebraicGeometry.CoherentImageBaseIso.isCoherent_rightDerived_comp_isIso_iff`. -/
theorem isCoherent_rightDerived_of_isProjectiveMorphism_affineBase {T : Scheme.{u}} [IsAffine T]
    [IsLocallyNoetherian T] {Y : Scheme.{u}} (g : Y ⟶ T) (hg : IsProjectiveMorphism g)
    (G : Y.Modules) (hG : G.IsCoherent) (q : ℕ) :
    (((Scheme.Modules.pushforward g).rightDerived q).obj G).IsCoherent := by
  have hproper : IsProper g := isProper_of_isProjectiveMorphism g hg
  have := hG
  have hGqc : G.IsQuasicoherent := isQuasicoherent_of_isCoherent G
  have hNoeth : IsNoetherianRing ↥(Γ(T, ⊤)) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top T⟩
  have hLNS : IsLocallyNoetherian (Spec (Γ(T, ⊤))) := inferInstance
  have hg' : IsProjectiveMorphism (g ≫ T.isoSpec.hom) :=
    IsProjectiveMorphism.of_iso (Iso.refl Y) T.isoSpec (by simp) hg
  exact (isCoherent_rightDerived_comp_isIso_iff g T.isoSpec G q).1
    (isCoherent_rightDerived_of_isProjectiveMorphism ↥(Γ(T, ⊤)) (g ≫ T.isoSpec.hom) hg' G hG q)

/-- **Higher direct images along an H-projective morphism to a locally Noetherian base are
coherent.** The base is covered by affine opens, `g` restricts to an H-projective morphism over
each of them, and coherence of a higher direct image is local on the base. -/
theorem isCoherent_rightDerived_of_isProjectiveMorphism {Y T : Scheme.{u}} (g : Y ⟶ T)
    [IsLocallyNoetherian T] (hg : IsProjectiveMorphism g) (G : Y.Modules) (hG : G.IsCoherent)
    (q : ℕ) :
    (((Scheme.Modules.pushforward g).rightDerived q).obj G).IsCoherent := by
  have := hG
  refine isCoherent_rightDerived_of_cover g G q
    (fun j : T.affineCover.I₀ => (T.affineCover.f j).opensRange)
    T.affineCover.iSup_opensRange ?_
  intro j
  have hAff : IsAffine ((T.affineCover.f j).opensRange).toScheme := isAffineOpen_opensRange _
  exact isCoherent_rightDerived_of_isProjectiveMorphism_affineBase
    (g ∣_ (T.affineCover.f j).opensRange) (hg.restrict _) _
    (AlgebraicGeometry.Modules.isCoherent_restrict G _) q

/-- **[Stacks, Tag 02O4].** For `S` locally Noetherian, `f : X ⟶ S` locally H-projective and `ℱ`
a coherent `𝒪_X`-module, the higher direct image `R^i f_* ℱ` is coherent for every `i ≥ 0`.

Local H-projectivity supplies an open cover of `S` over whose members `f` is H-projective — the
definition states this for `pullback.snd f (𝒰.f i)`, which is isomorphic as an arrow to
`f ∣_ (𝒰.f i).opensRange` — and coherence of a higher direct image is local on the base. -/
@[stacks 02O4]
theorem isCoherent_rightDerived_of_isLocallyProjective {X S : Scheme.{u}} (f : X ⟶ S)
    [IsLocallyNoetherian S] (hf : IsLocallyProjectiveMorphism f) (F : X.Modules)
    (hF : F.IsCoherent) (i : ℕ) :
    (((Scheme.Modules.pushforward f).rightDerived i).obj F).IsCoherent := by
  obtain ⟨𝒰, hproj⟩ := hf
  have := hF
  refine isCoherent_rightDerived_of_cover f F i
    (fun k : 𝒰.I₀ => (𝒰.f k).opensRange) 𝒰.iSup_opensRange ?_
  intro k
  have hpr : IsProjectiveMorphism (f ∣_ (𝒰.f k).opensRange) :=
    isProjectiveMorphism_of_arrow_iso (morphismRestrictOpensRange f (𝒰.f k)).symm (hproj k)
  exact isCoherent_rightDerived_of_isProjectiveMorphism (f ∣_ (𝒰.f k).opensRange) hpr _
    (AlgebraicGeometry.Modules.isCoherent_restrict F _) i

end LocallyProjectiveCoherentImage

end AlgebraicGeometry

end
