module

public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ExteriorPowerComparisonSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.LevelRestrictionSurjectivity
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.SheafifySections
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.TensorRestrictionVanishing

/-!
# The transition maps of the coefficient sheaf of [Stacks, Tag 07LF]

Fix a global crystalline situation `(p, (S, I, γ), X)`, a sheaf of `𝒪_{X/S}`-modules `F` on the
small crystalline site `Cris(X/S)` and an `i : ℕ`.  Hypothesis (2) of [Stacks, Tag 07JN] for the
coefficient sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of [Stacks, Tag 07LF], in the abelian form
`...SmallSite.HasSurjectiveWholeSpaceTransitions` that the rest of the proof of
[Stacks, Tag 07JN] consumes, asks that the transition map

`Γ((X, T', δ'), F ⊗ Ω^i) ⟶ Γ((X, T, δ), F ⊗ Ω^i)`

be surjective along every morphism of `Cris(X/S)` between objects over the whole of `X` whose map
on ambient schemes is a closed immersion.  This module carries that question to the ambient scheme
of the target, where the argument of `SmallSite/FMapGlobalSurjectivity.lean` is to be run on it,
and supplies the epimorphism that argument takes as its input.

Three steps are taken.

1. **The question is a question about the `f`-map over the whole ambient scheme.**  For an
   arbitrary abelian presheaf on `Cris(X/S)` the transition map along `g : A ⟶ B` is surjective as
   soon as the component of the `f`-map of [Stacks, Tag 07IP] over `⊤` is, with no hypothesis on
   the presheaf and none on `g`.  This is
   `...SmallSite.CohomologyRestriction.surjective_presheaf_map_of_isIso_toX` of
   `SmallSite/LevelRestrictionSurjectivity.lean` with its module-theoretic input removed.
2. **That `f`-map is an epimorphism of abelian sheaves on the ambient scheme**, for the tensor
   sheaf, from hypothesis (2) on `F` alone.  The `f`-map of the tensor *presheaf* of modules is
   locally surjective by [Stacks, Tag 07JN] hypothesis (2) for the tensor presheaf, which is
   proved; the sheafification units are locally surjective on both sides; and the passage from the
   source's ambient scheme to the target's is the new tool below — the functor of preimages of
   opens along a closed immersion which is surjective on points is **cocontinuous**, so pushing a
   presheaf morphism forward along it preserves local surjectivity.
3. **That `f`-map is an epimorphism of sheaves of modules**, over the restriction of `𝒪_{X/S}` to
   the ambient scheme of the target, again from hypothesis (2) on `F` alone.  The module structure
   is not put on by hand: the `f`-map of the restricted presheaf tensor product is a morphism of
   presheaves of modules, the direct image of the associated sheaf over the source's ambient
   scheme is a sheaf of modules, and the sheafification adjunction for presheaves of modules
   descends the first into the second.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite` except the
two scheme-theoretic results, which live in `AlgebraicGeometry`.

* `AlgebraicGeometry.isCocontinuous_opensMap_of_isClosedImmersion` — **the functor of preimages of
  opens along a closed immersion of schemes which is surjective on points is cocontinuous** for
  the Zariski topologies.  Such a morphism is a homeomorphism on underlying spaces, which is what
  makes a cover of a preimage refinable by the preimage of a cover.
* `AlgebraicGeometry.isLocallySurjective_pushforward_of_isClosedImmersion` and
  `...isLocallyInjective_pushforward_of_isClosedImmersion` — hence the pushforward of a locally
  surjective (resp. locally injective) morphism of abelian presheaves along such a morphism is
  again locally surjective (resp. locally injective).
* `...SmallSite.surjective_map_of_surjective_restrictOpenMap_top` — **the transition map of an
  abelian presheaf on `Cris(X/S)` along a morphism is surjective as soon as the `f`-map of that
  morphism over the whole ambient scheme of the target is**, with no hypothesis whatever on the
  presheaf.
* `...SmallSite.hasSurjectiveWholeSpaceTransitions_of_surjective_fmap_top` — the abelian form of
  hypothesis (2) of [Stacks, Tag 07JN] for an abelian sheaf, reduced to the surjectivity of those
  `f`-maps on global sections.
* `...SmallSite.isLocallySurjective_restrictionFMap_sheafify` — **the `f`-map of a crystalline
  sheafification is locally surjective on the ambient scheme of the target whenever the `f`-map of
  the presheaf is**, for a morphism which is a closed immersion and surjective on points.
* `...SmallSite.isLocallySurjective_restrictionFMap_tensorDifferentialFormsSheaf` — **the `f`-map
  of `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` is locally surjective on the ambient scheme of the target**, for
  every morphism between objects over the whole of `X` whose map on ambient schemes is a closed
  immersion, with hypothesis (2) of [Stacks, Tag 07JN] on `F` the only hypothesis carried.
* `...SmallSite.hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf_of_surjective_app`
  — the abelian form of hypothesis (2) for the tensor sheaf, from one input: that those locally
  surjective `f`-maps are surjective on global sections of the ambient scheme.
* `...SmallSite.directImageTensorRestrictionSheaf` and
  `...SmallSite.tensorRestrictionFMapSheaf` — **the `f`-map of the restricted coefficient sheaf as
  a morphism of sheaves of modules** over the restriction of `𝒪_{X/S}` to the ambient scheme of
  the target, into the direct image of the restriction over the source.
* `...SmallSite.toSheafify_comp_tensorRestrictionFMapSheaf` — that morphism factors the `f`-map of
  the restricted presheaf tensor product through the sheafification unit, which is its defining
  property.
* `...SmallSite.epi_tensorRestrictionFMapSheaf` — **it is an epimorphism of sheaves of modules**,
  with hypothesis (2) of [Stacks, Tag 07JN] on `F` the only hypothesis carried.

## What is and is not proved

Hypothesis (2) of [Stacks, Tag 07JN] for `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` in its abelian form —
`HasSurjectiveWholeSpaceTransitions (tensorDifferentialFormsSheaf F i)`, which is blocker (2) of
[Stacks, Tag 07LF] — is **not** proved here.  What is proved, with no hypothesis beyond
hypothesis (2) of [Stacks, Tag 07JN] on `F`, is that the question reduces to exactly one statement
about one affine scheme:

> the `f`-map `(F ⊗ Ω^i)_{T'} ⟶ f_*(F ⊗ Ω^i)_T` of abelian Zariski sheaves on the ambient scheme
> `T'` of the target, which is locally surjective by
> `isLocallySurjective_restrictionFMap_tensorDifferentialFormsSheaf`, is surjective on global
> sections.

That is the hypothesis `happ` of
`hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf_of_surjective_app`, and it is the
only hypothesis that declaration carries beyond hypothesis (2) on `F`.
It is **not** a statement standing in for a missing lemma about sheaves of abelian groups: a
locally surjective morphism of abelian sheaves on an affine scheme is *not* surjective on global
sections in general.  What makes it true here is the argument of
`SmallSite/FMapGlobalSurjectivity.lean`: both sides carry quasi-coherent `𝒪_{T'}`-module
structures for which the `f`-map is linear, and then
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` (or, through the kernel,
[Stacks, Tag 01XB]) applies.  The two module structures are available:

* the source, `(F ⊗ Ω^i)_{T'}`, is the Zariski sheafification of the restricted presheaf tensor
  product by `...CrystallineThickening.w_restrictOpen_tensorDifferentialFormsSheaf` of
  `SmallSite/SheafifySections.lean`, and that sheafification is quasi-coherent by
  `...SmallSite.isQuasicoherentOnSite_tensorRestrictionSheaf` of
  `SmallSite/TensorRestrictionVanishing.lean`;
* the target is its pushforward along a closed immersion, hence quasi-coherent by
  [Stacks, Tag 02KG], that is by
  `Stacks.AlgebraicGeometry.AffinePushforward.pushforward_isQuasicoherent_of_isAffineHom`.

The *linearity* of that `f`-map is proved here, which is the second half of this file:
`tensorRestrictionFMapSheaf` is a morphism of sheaves of modules whose underlying morphism of
abelian sheaves is the `f`-map above, and `epi_tensorRestrictionFMapSheaf` says it is an
epimorphism, both from hypothesis (2) on `F` alone.  It is built by the sheafification adjunction
for presheaves of modules, which is why no linearity has to be checked by hand; its scalars are
the restriction of `𝒪_{X/S}` to the ambient scheme, `...Thickening.ringRestrictionSheaf`, which
is the spelling `...SmallSite.isQuasicoherentOnSite_tensorRestrictionSheaf` proves the source
quasi-coherent in.

**Two things stand between that epimorphism and `happ`, and neither is proved here.**  Both are
changes of spelling rather than mathematics, and each is named here with its input.

1. *The quasi-coherence of the direct image, over `𝒪_{T'}` rather than over the restriction of
   `𝒪_{X/S}`.*  `Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` asks for an epimorphism
   of `AlgebraicGeometry.Scheme.Modules` with both sides quasi-coherent, and [Stacks, Tag 02KG]
   gives the quasi-coherence of a direct image only for
   `AlgebraicGeometry.Scheme.Modules.pushforward`, the pushforward along the map on ambient
   schemes.  `directImageTensorRestrictionSheaf` is instead `SheafOfModules.pushforward` along
   the `f`-map `...CohomologyRestriction.restrictionFMap` of the structure presheaf — the same
   functor of preimages of opens, a different semilinearity datum.  Restriction of scalars along
   the comparison of the two sheaves of rings turns each into the other, because
   `PresheafOfModules.pushforward` *is* a restriction of scalars of
   `PresheafOfModules.pushforward₀`, so what has to be proved is the commuting square of
   presheaves of rings on `T'`

   `𝒪_{T'} ⟶ (𝒪_{X/S})|_{T'} ⟶ f_* (𝒪_{X/S})|_T`  against  `𝒪_{T'} ⟶ f_* 𝒪_T ⟶ f_* (𝒪_{X/S})|_T`.

   Its components are exactly
   `...CohomologyRestriction.sectionsIso_inv_restrictionFMap_apply` of
   `SmallSite/FMapGlobalSurjectivity.lean`.  **The comparison of sheaves of rings
   to use is the one whose components are `...CrystallineThickening.sectionsIso`, namely
   `...SmallSite.CrystallineThickening.ringRestrictionIso`, and not
   `...Thickening.ringRestrictionSheafStructureIso`**: the implementation notes of
   `SmallSite/FormsRestrictionQuasicoherent.lean` record that identifying the second with a
   `sectionsIso`-built comparison would mean identifying `Crystalline.openTopResInv` with
   `AlgebraicGeometry.Scheme.Opens.topIso`, which the library does not do.  Since
   `Stacks.SheafOfModules.isQuasicoherentOnSite_restrictScalars_of_isIso` accepts *any*
   isomorphism of sheaves of rings, nothing is lost by using the first.
2. *The sections of the crystalline sheafification over the object.*  `happ` is about
   `(...restrictionFMap (tensorDifferentialFormsSheaf F i).obj g).app (op ⊤)`, a map of sections
   of the *crystalline* sheafification, while `tensorRestrictionFMapSheaf` is a map of sections of
   a *Zariski* sheafification on `T'`.  The identification is
   `...CrystallineThickening.restrictOpenSheafifyIso` of `SmallSite/SheafifySections.lean` at the
   two objects, and that the square it has to fit into commutes follows from
   `...CrystallineThickening.restrictOpenSheafify_hom_ext` — both composites agree after
   precomposition with the crystalline sheafification unit, by
   `toSheafify_comp_tensorRestrictionFMapSheaf` above together with the naturality of
   `CategoryTheory.toSheafify`, every map in sight being the universe lift of a map at the module
   universe.  This is written out nowhere.

**No `@[stacks]` attribute is placed.**  [Stacks, Tag 07LF] is not provable even with blocker (2)
closed: the acyclicity of the complex `M(0) → M(1) → M(2) → ⋯` for the tensor sheaf — item 6 of
the gap list of `SmallSite/AffineCohomology.lean`, input (3) of
`...SmallSite.vanishing07LF_of_isZero_homology_sectionsComplex` — remains, and the library has no
term of type `Crystalline.CosimplicialEnvelope`.  Nothing here is a clause of
[Stacks, Tag 07IP] or of [Stacks, Tag 07JN] either: these are steps inside a proof.

### Notes elsewhere that this refines

The "What is and is not proved" note of `SmallSite/SheafifySections.lean` says of input (2) of
[Stacks, Tag 07LF] that it "still needs the `H¹` argument of
`SmallSite/FMapGlobalSurjectivity.lean`, whose hypothesis is an epimorphism of sheaves of
`𝒪_T`-modules with quasi-coherent kernel — the same quasi-coherence, not the sections
identification", and that "nothing about input (2) is proved here".  Both halves are refined
rather than contradicted: the sections identification of that file is what carries the question to
`T'` at all, and the epimorphism the `H¹` argument asks for is supplied here — both as a morphism
of abelian sheaves and, over the restriction of `𝒪_{X/S}` to `T'`, as a morphism of sheaves of
modules.

The same note of `SmallSite/TensorRestrictionVanishing.lean` lists, under "What still blocks
[Stacks, Tag 07LF]", "the `H¹` argument of `SmallSite/FMapGlobalSurjectivity.lean`, which needs an
epimorphism of sheaves of `𝒪_T`-modules with quasi-coherent kernel; this is input (2) of
[Stacks, Tag 07LF], and it is a different quasi-coherence statement from the one proved here".
The last clause is **false for the source** of that epimorphism: the quasi-coherence input (2)
needs there is exactly `...isQuasicoherentOnSite_tensorRestrictionSheaf`, the statement proved in
that file, and it is needed at the very spelling of the sheaf of rings that file states it at,
which is the one `tensorRestrictionFMapSheaf` below is linear over.  For the *target* of the
epimorphism a second quasi-coherence is needed, and it is [Stacks, Tag 02KG] for a direct image,
which is a different statement — but it is not a different *quasi-coherence of the tensor sheaf*,
which is what that clause suggests.  Also, no kernel is needed: with both sides quasi-coherent,
`Stacks.SectionEpiAffine.surjective_app_of_isAffineOpen` concludes the surjectivity on an affine
open directly.  No file is edited to record this; the correction is here.

## Implementation notes

The cocontinuity of the functor of preimages of opens is proved from the definition rather than
from `CategoryTheory.Adjunction.isCocontinuous_iff_coverPreserving` through the equivalence
`TopologicalSpace.Opens.mapMapIso` of a homeomorphism: the three lines of the direct proof are the
same three lines that appear inside
`...CohomologyRestriction.isLocallySurjective_moduleFMap_of_isLocallySurjective_moduleComparison`
of `SmallSite/FMapSurjectivity.lean`, whereas the route through `mapMapIso` would first have to
factor the closed immersion through the isomorphism of topological spaces it induces.  The
surjectivity on points, which is what turns the closed embedding into a homeomorphism, is
unavoidable: for a closed immersion that is not surjective the functor of preimages is not
cocontinuous, an open cover of the empty preimage of a nonempty open being refinable by nothing.

`isLocallySurjective_restrictionFMap_tensorDifferentialFormsSheaf` supplies the hypothesis of
`isLocallySurjective_restrictionFMap_sheafify` through a `show`, not a `rw`: the `f`-map of
`...SmallSite.tensorDifferentialFormsPresheaf` is the universe lift of the `f`-map of the tensor
presheaf of modules definitionally, both being
`CategoryTheory.Functor.whiskerRight` of the same natural transformation, but
`...CohomologyRestriction.restrictionFMap` is a plain `def` and rewriting under it fails silently.

**An elaboration subtlety.**  `CategoryTheory.Presheaf.IsLocallySurjective` carries the concrete
structure of its coefficient category as instance-implicit arguments which the morphism does not
determine — `{FA}`, `{CA}` and the `ConcreteCategory` instance.  A hypothesis of that class in the
local context is therefore *not* found by instance search for a goal in which those arguments are
still metavariables, even when the hypothesis is stated with syntactically the same topology and
the same morphism: both `Presheaf.isLocallySurjective_comp` and
`...isLocallySurjective_of_isLocallySurjective_fac` take their local-surjectivity inputs as
instance arguments, and in `epi_tensorRestrictionFMapSheaf` both had to be passed explicitly
through `@`.  The presentation is a bare "failed to synthesize instance" naming a goal that is
visibly a hypothesis in the context, which reads like a spelling mismatch and is not one; the
remedy is `@` with the hypothesis in the instance slot, never a wider instance or a `show`.
`...isLocallySurjective_whisker` and
`...isLocallySurjective_moduleFMap_of_isIso_toX` are applied with their arguments explicit for the
same reason.

## References

* [Stacks Project, Tag 07LF](https://stacks.math.columbia.edu/tag/07LF)
* [Stacks Project, Tag 07JN](https://stacks.math.columbia.edu/tag/07JN)
* [Stacks Project, Tag 07JK](https://stacks.math.columbia.edu/tag/07JK)
* [Stacks Project, Tag 07IP](https://stacks.math.columbia.edu/tag/07IP)
* [Stacks Project, Tag 01XB](https://stacks.math.columbia.edu/tag/01XB)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe t u

noncomputable section

namespace AlgebraicGeometry

/-- **The functor of preimages of opens along a closed immersion which is surjective on points is
cocontinuous** for the Zariski topologies of the two schemes.

Cocontinuity asks that a Zariski cover of the preimage `f^{-1}W` of an open `W` of the target be
refined by the preimages of a Zariski cover of `W`.  Both hypotheses are used: surjectivity on
points produces, for a point of `W`, a point of `f^{-1}W` over it and hence a member `Z` of the
given cover around that point, and the closed immersion being topologically inducing writes `Z` as
the preimage of an open `V₁` of the target, so that `W ⊓ V₁` is an open of `W` around the given
point whose preimage lies in `Z`.

This is the step that lets a statement about a presheaf on the ambient scheme of the source of a
morphism of `Cris(X/S)` be pushed forward to the ambient scheme of its target; see
`isLocallySurjective_pushforward_of_isClosedImmersion`. -/
theorem isCocontinuous_opensMap_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsClosedImmersion f) (hsurj : Function.Surjective f.base) :
    (Opens.map f.base).IsCocontinuous
      (Opens.grothendieckTopology Y) (Opens.grothendieckTopology X) := by
  constructor
  intro W Sv hS
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨y, rfl⟩ := hsurj x
  obtain ⟨Z, i, hZ, hyZ⟩ := hS y hx
  obtain ⟨V₁, hV₁open, hV₁⟩ := f.isClosedEmbedding.isInducing.isOpen_iff.mp Z.2
  have hpre : (Opens.map f.base).obj (W ⊓ ⟨V₁, hV₁open⟩) ≤ Z :=
    fun z hz ↦ hV₁.le (show f.base z ∈ V₁ from hz.2)
  exact ⟨W ⊓ ⟨V₁, hV₁open⟩, homOfLE inf_le_left,
    Sv.downward_closed hZ (homOfLE hpre), hx, hV₁.ge hyZ⟩

/-- **The pushforward of a locally surjective morphism of abelian presheaves along a closed
immersion which is surjective on points is locally surjective.**  This is
`CategoryTheory.Presheaf.isLocallySurjective_whisker` at the cocontinuous functor
`isCocontinuous_opensMap_of_isClosedImmersion`. -/
theorem isLocallySurjective_pushforward_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsClosedImmersion f) (hsurj : Function.Surjective f.base)
    {P Q : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{t}} (η : P ⟶ Q)
    [Presheaf.IsLocallySurjective (Opens.grothendieckTopology X) η] :
    Presheaf.IsLocallySurjective (Opens.grothendieckTopology Y)
      (Functor.whiskerLeft (Opens.map f.base).op η) :=
  have := isCocontinuous_opensMap_of_isClosedImmersion f hf hsurj
  Presheaf.isLocallySurjective_whisker (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X) (Opens.map f.base) η

/-- **The pushforward of a locally injective morphism of abelian presheaves along a closed
immersion which is surjective on points is locally injective.**  This is
`CategoryTheory.Presheaf.isLocallyInjective_whisker` at the cocontinuous functor
`isCocontinuous_opensMap_of_isClosedImmersion`; it is recorded beside its surjective sibling
because the two together say that such a pushforward carries a sheafification morphism to a
sheafification morphism. -/
theorem isLocallyInjective_pushforward_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hf : IsClosedImmersion f) (hsurj : Function.Surjective f.base)
    {P Q : (X.Opens)ᵒᵖ ⥤ AddCommGrpCat.{t}} (η : P ⟶ Q)
    [Presheaf.IsLocallyInjective (Opens.grothendieckTopology X) η] :
    Presheaf.IsLocallyInjective (Opens.grothendieckTopology Y)
      (Functor.whiskerLeft (Opens.map f.base).op η) :=
  have := isCocontinuous_opensMap_of_isClosedImmersion f hf hsurj
  Presheaf.isLocallyInjective_whisker (Opens.grothendieckTopology Y)
    (Opens.grothendieckTopology X) (Opens.map f.base) η

end AlgebraicGeometry

namespace Crystalline.GlobalCrystallineSituation.SmallSite

variable {S : GlobalCrystallineSituation.{u}}

/-! ### The transition maps, read on the whole ambient scheme -/

/-- **The transition map `Γ(B, P) ⟶ Γ(A, P)` of an abelian presheaf on `Cris(X/S)` along a
morphism `g : A ⟶ B` is surjective as soon as the component of its `f`-map over the whole ambient
scheme of `B` is.**

No hypothesis is carried: neither on the presheaf, nor on `g`, nor on the situation.  The square

`g|_⊤ ≫ (B|_⊤ ⟶ B) = (A|_{g^{-1}⊤} ⟶ A) ≫ g`

of `...SmallSite.CrystallineThickening.restrictOpenMap_restrictOpenHom` identifies the two maps up
to the structure morphisms of the two restrictions to the whole ambient scheme, which are
isomorphisms by `...SmallSite.CrystallineThickening.isIso_restrictOpenHom_top`, and a surjection
factoring through an injection forces the other factor to be onto.

This is `...SmallSite.CohomologyRestriction.surjective_presheaf_map_of_isIso_toX` of
`SmallSite/LevelRestrictionSurjectivity.lean` with its module-theoretic input removed and made a
hypothesis.  That declaration's statement is this one with the hypothesis discharged, for the
abelian presheaf of a sheaf of modules satisfying the two hypotheses of [Stacks, Tag 07JN]. -/
theorem surjective_map_of_surjective_restrictOpenMap_top
    (P : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {A B : CrystallineThickening S} (g : A ⟶ B)
    (h : Function.Surjective (ConcreteCategory.hom (P.map
      (CrystallineThickening.restrictOpenMap g
        (⊤ : B.obj.thickening.target.scheme.Opens)).op))) :
    Function.Surjective (ConcreteCategory.hom (P.map g.op)) := by
  have : IsIso (A.restrictOpenHom
      (g.hom.targetHom.hom ⁻¹ᵁ (⊤ : B.obj.thickening.target.scheme.Opens))) :=
    CrystallineThickening.isIso_restrictOpenHom_of_eq_top A rfl
  have := CrystallineThickening.isIso_restrictOpenHom_top B
  have key : (P.map (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)).op) ≫
        (P.map (CrystallineThickening.restrictOpenMap g
          (⊤ : B.obj.thickening.target.scheme.Opens)).op) =
      (P.map g.op) ≫ (P.map
        (A.restrictOpenHom
          (g.hom.targetHom.hom ⁻¹ᵁ (⊤ : B.obj.thickening.target.scheme.Opens))).op) := by
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
      CrystallineThickening.restrictOpenMap_restrictOpenHom g
        (⊤ : B.obj.thickening.target.scheme.Opens)]
  have hu : Function.Surjective (ConcreteCategory.hom (P.map
      (B.restrictOpenHom (⊤ : B.obj.thickening.target.scheme.Opens)).op)) :=
    (ConcreteCategory.bijective_of_isIso _).2
  have ht : Function.Injective (ConcreteCategory.hom (P.map
      (A.restrictOpenHom
        (g.hom.targetHom.hom ⁻¹ᵁ (⊤ : B.obj.thickening.target.scheme.Opens))).op)) :=
    (ConcreteCategory.bijective_of_isIso _).1
  intro y
  obtain ⟨x, hx⟩ := (h.comp hu) (ConcreteCategory.hom (P.map
      (A.restrictOpenHom
        (g.hom.targetHom.hom ⁻¹ᵁ (⊤ : B.obj.thickening.target.scheme.Opens))).op) y)
  refine ⟨x, ht ?_⟩
  rwa [← ConcreteCategory.comp_apply, ← key, ConcreteCategory.comp_apply]

/-- **The abelian form of hypothesis (2) of [Stacks, Tag 07JN] follows from the surjectivity of
the `f`-maps on global sections of the ambient schemes.**  For an abelian sheaf `G` on
`Cris(X/S)`, if for every morphism `g : A ⟶ B` between objects over the whole of `X` whose map on
ambient schemes is a closed immersion the component over `⊤` of the `f`-map
`G_{T'} ⟶ f_* G_T` of [Stacks, Tag 07IP] is surjective, then
`...SmallSite.HasSurjectiveWholeSpaceTransitions G`.

This is `surjective_map_of_surjective_restrictOpenMap_top` quantified; the component over `⊤` of
`...CohomologyRestriction.restrictionFMap` is the transition map of `G` along the restriction of
`g` over the whole of `T'`, by
`...CohomologyRestriction.restrictionFMap_app`. -/
theorem hasSurjectiveWholeSpaceTransitions_of_surjective_fmap_top
    (G : Sheaf (smallTopology S) AddCommGrpCat.{u + 1})
    (h : ∀ (A B : CrystallineThickening S) (g : A ⟶ B), IsClosedImmersion g.hom.targetHom.hom →
      IsIso A.obj.toX → IsIso B.obj.toX →
      Function.Surjective (ConcreteCategory.hom
        ((CohomologyRestriction.restrictionFMap G.obj g).app
          (op (⊤ : B.obj.thickening.target.scheme.Opens))))) :
    HasSurjectiveWholeSpaceTransitions G :=
  fun A B g hg hA hB ↦
    surjective_map_of_surjective_restrictOpenMap_top G.obj g (h A B g hg hA hB)

/-! ### The `f`-map of a crystalline sheafification -/

/-- **The `f`-map of a crystalline sheafification is locally surjective on the ambient scheme of
the target whenever the `f`-map of the presheaf is.**

Let `P` be an abelian presheaf on `Cris(X/S)` and `g : A ⟶ B` a morphism whose map on ambient
schemes is a closed immersion and is surjective on points.  If the `f`-map of `P` along `g` is
locally surjective on the ambient scheme `T'` of `B`, then so is the `f`-map of the sheafification
of `P`.

The square of the sheafification unit against the two `f`-maps commutes, by naturality of
`CategoryTheory.toSheafify`.  Its other composite is locally surjective: the `f`-map of `P` is, by
hypothesis, and the pushforward to `T'` of the restriction to `T` of the unit is, by
`...CrystallineThickening.isLocallySurjective_whiskerLeft_restrictOpenFunctor` of
`SmallSite/SheafifySections.lean` followed by
`AlgebraicGeometry.isLocallySurjective_pushforward_of_isClosedImmersion`.  A morphism through
which a locally surjective composite factors on the right is locally surjective. -/
theorem isLocallySurjective_restrictionFMap_sheafify
    (P : (CrystallineThickening S)ᵒᵖ ⥤ AddCommGrpCat.{u + 1})
    {A B : CrystallineThickening S} (g : A ⟶ B)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hsurj : Function.Surjective g.hom.targetHom.hom.base)
    (hP : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      (CohomologyRestriction.restrictionFMap P g)) :
    Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      (CohomologyRestriction.restrictionFMap (sheafify (smallTopology S) P) g) := by
  have := isLocallySurjective_toSheafify P
  have := CrystallineThickening.isLocallySurjective_whiskerLeft_restrictOpenFunctor A
    (toSheafify (smallTopology S) P)
  have := isLocallySurjective_pushforward_of_isClosedImmersion g.hom.targetHom.hom hg hsurj
    (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
      (toSheafify (smallTopology S) P))
  have fac : Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor B).op
        (toSheafify (smallTopology S) P) ≫
      CohomologyRestriction.restrictionFMap (sheafify (smallTopology S) P) g =
    CohomologyRestriction.restrictionFMap P g ≫
      Functor.whiskerLeft (Opens.map g.hom.targetHom.hom.base).op
        (Functor.whiskerLeft (CrystallineThickening.restrictOpenFunctor A).op
          (toSheafify (smallTopology S) P)) :=
    NatTrans.ext (funext fun _ ↦ ((toSheafify (smallTopology S) P).naturality _).symm)
  exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ fac

/-- The `f`-map of the tensor presheaf of modules is locally surjective on the ambient scheme of
the target, from hypothesis (2) of [Stacks, Tag 07JN] on `F`. -/
private theorem isLocallySurjective_moduleFMap_tensorDifferentialForms
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    {A B : CrystallineThickening S} (g : A ⟶ B)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hA : IsIso A.obj.toX) (hB : IsIso B.obj.toX) :
    Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (CohomologyRestriction.ringRestriction B)).map
        (CohomologyRestriction.moduleFMap
          (tensorDifferentialForms
            (F.val : PresheafOfModules.{u}
              (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) g)) :=
  CohomologyRestriction.isLocallySurjective_moduleFMap_of_isIso_toX
    (tensorDifferentialForms
      (F.val : PresheafOfModules.{u} (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i)
    g (isSurjectiveComparison_tensorDifferentialForms' _ i hM) hg hA hB

/-- **The `f`-map of the coefficient sheaf `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of [Stacks, Tag 07LF] is
locally surjective on the ambient scheme of the target**, for every morphism of `Cris(X/S)`
between objects over the whole of `X` whose map on ambient schemes is a closed immersion, and for
every `i`.

The only hypothesis carried is `hM`, hypothesis (2) of [Stacks, Tag 07JN] for `F`.  Hypothesis (2)
for the tensor presheaf of modules follows from it, by
`...SmallSite.CohomologyRestriction.isSurjectiveComparison_tensorDifferentialForms'`, and gives the
local surjectivity of the `f`-map of that presheaf through
`...CohomologyRestriction.isLocallySurjective_moduleFMap_of_isIso_toX`; raising the coefficient
universe preserves local surjectivity, and
`isLocallySurjective_restrictionFMap_sheafify` crosses the sheafification.

Together with `hasSurjectiveWholeSpaceTransitions_of_surjective_fmap_top` this reduces blocker (2)
of [Stacks, Tag 07LF] to the surjectivity of this locally surjective morphism of abelian sheaves
on global sections of an affine scheme; see the module documentation for what that still needs. -/
theorem isLocallySurjective_restrictionFMap_tensorDifferentialFormsSheaf
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    {A B : CrystallineThickening S} (g : A ⟶ B)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hA : IsIso A.obj.toX) (hB : IsIso B.obj.toX) :
    Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      (CohomologyRestriction.restrictionFMap (tensorDifferentialFormsSheaf F i).obj g) := by
  have := isLocallySurjective_moduleFMap_tensorDifferentialForms F i hM g hg hA hB
  have hP : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      (CohomologyRestriction.restrictionFMap (tensorDifferentialFormsPresheaf F i) g) := by
    change Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      (Functor.whiskerRight
        ((PresheafOfModules.toPresheaf (CohomologyRestriction.ringRestriction B)).map
          (CohomologyRestriction.moduleFMap
            (tensorDifferentialForms
              (F.val : PresheafOfModules.{u}
                (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) g))
        AddCommGrpCat.uliftFunctor.{u + 1, u})
    infer_instance
  exact isLocallySurjective_restrictionFMap_sheafify
    (tensorDifferentialFormsPresheaf F i) g hg
    (CohomologyRestriction.surjective_targetHom_base_of_isIso_toX g hA hB) hP

/-- **The abelian form of hypothesis (2) of [Stacks, Tag 07JN] for the coefficient sheaf
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` of [Stacks, Tag 07LF], from one input.**

The hypotheses are hypothesis (2) of [Stacks, Tag 07JN] on `F` and
`happ`: that for a morphism between objects over the whole of `X` whose map on ambient schemes is
a closed immersion, the `f`-map of the tensor sheaf is surjective on global sections of the
ambient scheme of the target.  `happ` is the **only** carried hypothesis standing for something
the library does not have, and what it asks for is exactly the conclusion of the argument of
`SmallSite/FMapGlobalSurjectivity.lean` applied to the tensor sheaf: that `f`-map is locally
surjective by `isLocallySurjective_restrictionFMap_tensorDifferentialFormsSheaf`, both of its sides
are quasi-coherent modules on the affine ambient scheme, and so it is surjective on global
sections.  The module documentation says precisely what of that argument is in the library and
what is not.

No affineness of `X` is assumed: it is a standing hypothesis of [Stacks, Tag 07JN] and of
[Stacks, Tag 07LF], and it is what makes the ambient schemes of the objects over the whole of `X`
affine, so it is what `happ` is to be proved *from*; but it is not needed to pass from `happ` to
the conclusion, and assuming it here would only weaken this statement. -/
theorem hasSurjectiveWholeSpaceTransitions_tensorDifferentialFormsSheaf_of_surjective_app
    (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    (happ : ∀ (A B : CrystallineThickening S) (g : A ⟶ B), IsClosedImmersion g.hom.targetHom.hom →
      IsIso A.obj.toX → IsIso B.obj.toX →
      Presheaf.IsLocallySurjective
          (Opens.grothendieckTopology B.obj.thickening.target.scheme)
          (CohomologyRestriction.restrictionFMap (tensorDifferentialFormsSheaf F i).obj g) →
        Function.Surjective (ConcreteCategory.hom
          ((CohomologyRestriction.restrictionFMap (tensorDifferentialFormsSheaf F i).obj g).app
            (op (⊤ : B.obj.thickening.target.scheme.Opens))))) :
    HasSurjectiveWholeSpaceTransitions (tensorDifferentialFormsSheaf F i) :=
  hasSurjectiveWholeSpaceTransitions_of_surjective_fmap_top _ fun A B g hg hA hB ↦
    happ A B g hg hA hB
      (isLocallySurjective_restrictionFMap_tensorDifferentialFormsSheaf F i hM g hg hA hB)

/-! ### The `f`-map of the restricted tensor sheaf as a morphism of sheaves of modules -/

section Module

variable (F : SheafOfModules.{u} (structureSheaf S)) (i : ℕ)
  {A B : CrystallineThickening S} (g : A ⟶ B)

/-- **The `f`-map of the structure sheaf of `Cris(X/S)`, as a morphism of sheaves of rings over
the functor of preimages of opens.**  This is
`...CohomologyRestriction.restrictionFMap` at the structure presheaf, packaged as a morphism of
sheaves so that it can be the semilinearity datum of a pushforward of sheaves of modules.  It is
`Crystalline.GlobalCrystallineSituation.Thickening.ringRestrictionSheafFMap` at the underlying
morphism of `CRIS(X/S)`, written with the small-site `f`-map because that is the spelling
`...CohomologyRestriction.moduleFMap` is semilinear over. -/
def smallRingRestrictionSheafFMap :
    Thickening.ringRestrictionSheaf B.obj ⟶
      ((Opens.map g.hom.targetHom.hom.base).sheafPushforwardContinuous RingCat.{u}
          (Opens.grothendieckTopology B.obj.thickening.target.scheme)
          (Opens.grothendieckTopology A.obj.thickening.target.scheme)).obj
        (Thickening.ringRestrictionSheaf A.obj) :=
  ⟨CohomologyRestriction.restrictionFMap (crisRing S) g⟩

/-- **The direct image of the restricted coefficient sheaf of [Stacks, Tag 07LF].**  For a
morphism `g : A ⟶ B` of `Cris(X/S)` this is the pushforward along the map on ambient schemes of
`...SmallSite.tensorRestrictionSheaf A F i`, the associated sheaf of the restriction of
`F ⊗_{𝒪_{X/S}} Ω^i_{X/S}` to the ambient scheme of `A`, read as a sheaf of modules over the
restriction of `𝒪_{X/S}` to the ambient scheme of `B`.  Its sections over an open `W` are the
sections of `tensorRestrictionSheaf A F i` over `g^{-1}W`. -/
def directImageTensorRestrictionSheaf :
    SheafOfModules.{u} (Thickening.ringRestrictionSheaf B.obj) :=
  (SheafOfModules.pushforward.{u} (smallRingRestrictionSheafFMap g)).obj
    (tensorRestrictionSheaf A F i)

/-- **The `f`-map of the restriction of the presheaf tensor product `F ⊗_{𝒪_{X/S}} Ω^i_{X/S}`
into the direct image of its associated sheaf.**  It is the `f`-map
`...CohomologyRestriction.moduleFMap` of that presheaf of modules followed by the direct image of
the sheafification unit on the ambient scheme of the source; both are morphisms of presheaves of
modules, so no linearity has to be checked by hand. -/
def tensorRestrictionFMapPresheaf :
    tensorRestriction B F i ⟶ (directImageTensorRestrictionSheaf F i g).val :=
  CohomologyRestriction.moduleFMap
      (tensorDifferentialForms
        (F.val : PresheafOfModules.{u}
          (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) g ≫
    (PresheafOfModules.pushforward (smallRingRestrictionSheafFMap g).hom).map
      (PresheafOfModules.moduleSheafificationUnit
        (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        (𝟙 (restrictedCommRingSheaf A).obj) (tensorRestriction A F i))

/-- **The `f`-map of the restricted coefficient sheaf of [Stacks, Tag 07LF], as a morphism of
sheaves of modules over the restriction of `𝒪_{X/S}` to the ambient scheme of the target.**

This is `tensorRestrictionFMapPresheaf` descended over the sheafification of presheaves of
modules: the direct image of a sheaf is a sheaf, so the sheafification adjunction
`PresheafOfModules.sheafificationHomEquiv` extends the presheaf `f`-map uniquely over the
associated sheaf of its source.  Descending through that adjunction rather than constructing the
morphism component by component is what makes the linearity automatic. -/
def tensorRestrictionFMapSheaf :
    tensorRestrictionSheaf B F i ⟶ directImageTensorRestrictionSheaf F i g :=
  (PresheafOfModules.sheafificationHomEquiv
    (CategoryTheory.Sheaf.toRingCatMap
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      (𝟙 (restrictedCommRingSheaf B).obj))).symm (tensorRestrictionFMapPresheaf F i g)

/-- **The sheafified `f`-map factors the presheaf `f`-map through the sheafification unit.**  This
is the defining property of `tensorRestrictionFMapSheaf`, read on underlying abelian presheaves;
it is what identifies that morphism with the `f`-map of the crystalline sheafification. -/
theorem toSheafify_comp_tensorRestrictionFMapSheaf :
    toSheafify (Opens.grothendieckTopology B.obj.thickening.target.scheme)
          (tensorRestriction B F i).presheaf ≫
        (PresheafOfModules.toPresheaf (Thickening.ringRestrictionSheaf B.obj).obj).map
          (tensorRestrictionFMapSheaf F i g).val =
      (PresheafOfModules.toPresheaf (CohomologyRestriction.ringRestriction B)).map
        (tensorRestrictionFMapPresheaf F i g) := by
  have h := PresheafOfModules.toPresheaf_map_sheafificationHomEquiv_def
    (CategoryTheory.Sheaf.toRingCatMap
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      (𝟙 (restrictedCommRingSheaf B).obj))
    (P := tensorRestriction B F i) (F := directImageTensorRestrictionSheaf F i g)
    (tensorRestrictionFMapSheaf F i g)
  rw [show PresheafOfModules.sheafificationHomEquiv
        (CategoryTheory.Sheaf.toRingCatMap
          (Opens.grothendieckTopology B.obj.thickening.target.scheme)
          (𝟙 (restrictedCommRingSheaf B).obj))
        (tensorRestrictionFMapSheaf F i g) = tensorRestrictionFMapPresheaf F i g from
      Equiv.apply_symm_apply _ _] at h
  exact h.symm

/-- **The `f`-map of the restricted coefficient sheaf of [Stacks, Tag 07LF] is an epimorphism of
sheaves of modules**, for every morphism of `Cris(X/S)` between objects over the whole of `X`
whose map on ambient schemes is a closed immersion, and every `i`.

The only hypothesis carried is `hM`, hypothesis (2) of [Stacks, Tag 07JN] for `F`.  The presheaf
`f`-map is locally surjective by
`...CohomologyRestriction.isLocallySurjective_moduleFMap_of_isIso_toX` at the tensor presheaf,
whose hypothesis (2) is
`...SmallSite.CohomologyRestriction.isSurjectiveComparison_tensorDifferentialForms'`; the direct
image of the sheafification unit on the ambient scheme of the source is locally surjective by
`AlgebraicGeometry.isLocallySurjective_pushforward_of_isClosedImmersion`; and the sheafified
`f`-map factors their composite through a locally surjective unit, so it is locally surjective
and hence an epimorphism. -/
theorem epi_tensorRestrictionFMapSheaf
    (hM : CohomologyRestriction.IsSurjectiveComparison F.val)
    (hg : IsClosedImmersion g.hom.targetHom.hom)
    (hA : IsIso A.obj.toX) (hB : IsIso B.obj.toX) :
    Epi (tensorRestrictionFMapSheaf F i g) := by
  have := isLocallySurjective_moduleFMap_tensorDifferentialForms F i hM g hg hA hB
  have := GrothendieckTopology.W.isLocallySurjective
    ((Opens.grothendieckTopology A.obj.thickening.target.scheme).W_toSheafify
      (tensorRestriction A F i).presheaf)
  have hpf : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      (Functor.whiskerLeft (Opens.map g.hom.targetHom.hom.base).op
        (toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          (tensorRestriction A F i).presheaf)) :=
    isLocallySurjective_pushforward_of_isClosedImmersion g.hom.targetHom.hom hg
      (CohomologyRestriction.surjective_targetHom_base_of_isIso_toX g hA hB)
      (toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
        (tensorRestriction A F i).presheaf)
  have hcomp : Presheaf.IsLocallySurjective
      (Opens.grothendieckTopology B.obj.thickening.target.scheme)
      ((PresheafOfModules.toPresheaf (CohomologyRestriction.ringRestriction B)).map
        (tensorRestrictionFMapPresheaf F i g)) :=
    @Presheaf.isLocallySurjective_comp _ _ _ _ _ _ _ _ _ _ _ _
      ((PresheafOfModules.toPresheaf (CohomologyRestriction.ringRestriction B)).map
        (CohomologyRestriction.moduleFMap
          (tensorDifferentialForms
            (F.val : PresheafOfModules.{u}
              (structurePresheaf S ⋙ forget₂ CommRingCat RingCat)) i) g))
      (Functor.whiskerLeft (Opens.map g.hom.targetHom.hom.base).op
        (toSheafify (Opens.grothendieckTopology A.obj.thickening.target.scheme)
          (tensorRestriction A F i).presheaf))
      inferInstance hpf
  exact Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _
    (@Presheaf.isLocallySurjective_of_isLocallySurjective_fac _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (toSheafify_comp_tensorRestrictionFMapSheaf F i g) hcomp)

end Module

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
