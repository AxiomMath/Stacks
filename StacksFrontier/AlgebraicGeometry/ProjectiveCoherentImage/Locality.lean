module

public import StacksFrontier.AlgebraicGeometry.CoherentAbelian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveCoherentImage.Basic

/-!
# Coherence of a higher direct image is local on the base

[Stacks, Tag 02O4] — higher direct images of a coherent module under a locally projective
morphism to a locally Noetherian base are coherent — is proved in the source in four steps. The
second of them is "the assertion is local on `S`, so we may assume `S` affine Noetherian and `X`
a closed subscheme of `P ⁿ_R`", justified by [Stacks, Tag 01E5]. This file performs that step,
unconditionally in the cohomological input: given an open cover of the base on each member of
which the higher direct image of the restricted morphism is coherent, the higher direct image is
coherent on each member of the cover.

What this does **not** do is glue that conclusion into global coherence. Gluing needs coherence to
be local on a scheme in the `AlgebraicGeometry.Scheme.Modules.restrict` spelling, and the library
does not have it; see the implementation notes for the two declarations that are missing and where
they belong. They are hypotheses here, in the weakest form this argument uses, in the style of
the conditional reduction of [Stacks, Tag 0EBD].

[Stacks, Tag 02O4] itself is **not** proved, and no `stacks` attribute is attached: the remaining
input is its own statement for a projective morphism, which is the substance of the source's
argument and is listed below.

## Main results

* `AlgebraicGeometry.ProjectiveCoherentImage.isCoherent_restrict_higherDirectImage`: the
  unconditional half. The restriction to `V` of `R ᵖ f_* F` is coherent as soon as
  `R ᵖ (f ∣_ V)_* (F|_{f⁻¹ V})` is, for a single open `V` of the base. This is [Stacks, Tag 01E5]
  for schemes together with the closure of coherence under isomorphism.
* `AlgebraicGeometry.ProjectiveCoherentImage.isCoherent_higherDirectImage_of_cover`: the locality
  step of [Stacks, Tag 02O4], from a covering family of opens of the base and the gluing
  hypothesis.
* `AlgebraicGeometry.ProjectiveCoherentImage.isCoherent_higherDirectImage_of_openCover`: the same
  from a `AlgebraicGeometry.Scheme.OpenCover` of the base, which is the datum
  Tag 01W8's `IsLocallyProjective` supplies.
* `AlgebraicGeometry.ProjectiveCoherentImage.isCoherent_higherDirectImage_of_locallyProjective`:
  the whole reduction, parametric in the projectivity predicate. [Stacks, Tag 02O4] is its
  instance at projectivity of `f ∣_ V`, once the two coherence-locality declarations and the
  projective case exist.

## Implementation notes

**The two missing declarations, stated exactly.** Both belong in a new file
`StacksFrontier/AlgebraicGeometry/Modules/CoherentLocal.lean`, the sibling of the existing
`StacksFrontier/AlgebraicGeometry/Modules/QuasicoherentLocal.lean`, which proves the same two
statements for quasi-coherence (`Stacks.Modules.isQuasicoherent_of_restrict`) and whose
`Stacks.Modules.presentationOver` is the transport the coherent case needs an analogue of:

```
theorem isCoherent_restrict {X : Scheme.{u}} (M : X.Modules) [M.IsCoherent] (U : X.Opens) :
    ((Scheme.Modules.restrictFunctor U.ι).obj M).IsCoherent

theorem isCoherent_of_restrict {X : Scheme.{u}} (M : X.Modules) {I : Type u} (U : I → X.Opens)
    (hU : iSup U = ⊤)
    (h : ∀ i, ((Scheme.Modules.restrictFunctor (U i).ι).obj M).IsCoherent) : M.IsCoherent
```

Neither is a repackaging of an existing result. `Stacks.SheafOfModules.isCoherent_of_coversTop` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/CoherenceClosure.lean` glues
`Stacks.SheafOfModules.IsCoherentOn M W` — a predicate about the opens *of the ambient space*
below `W` and the slice site `Over W` — not coherence of the module on the open *subscheme*. That
file says so itself: making `IsCoherentOn W` literally the coherence of `M.over W` "is the
structurally better fix and is not done here". The comparison it does provide,
`isFiniteType_kernel_over_of_isCoherentOn`, runs in the direction that consumes `IsCoherentOn`,
so it cannot produce it. The transport in the other direction has to carry the kernel condition of
Tag 01BV across `AlgebraicGeometry.Scheme.Modules.overEquiv` and across the identification of an
open of `↥U` with an open of `X` below `U`; `StacksFrontier/AlgebraicGeometry/Modules/QuasicoherentLocal.lean` carries a *presentation*
across exactly those two and that is its only content, so the coherent analogue is of that size,
not a corollary.

**Projectivity is a parameter, because Tag 01W8's `IsProjective` cannot be mentioned
axiom-cleanly.** Tag 01W8's `IsLocallyProjective` is an existential over its `IsProjective`,
which asserts a closed immersion into the projective bundle `ℙ(ℰ)` of Tag 01OB.
That bundle is the relative `Proj` of Tag 01NQ applied to Tag 01OB's projective-bundle
situation, whose three fields are the three fields of Tag 01OB's `symmetricAlgebra_projAxioms`
— and that theorem is unproved. An unproved result reached only through the *vocabulary of a
type* is still reported by `#print axioms`, and the mechanism is worth stating because it is easy
to assume the opposite. Take an unproved existential; define a term as its `Classical.choose`;
define a proposition mentioning that term; then state a theorem taking that proposition as a
hypothesis and prove it by `trivial`. The proof discharges its goal without touching the
existential, yet `#print axioms` on it reports `sorryAx` together with `Classical.choice` —
because the *hypothesis* is phrased in a vocabulary whose construction went through the unproved
result, and the axiom audit follows the type as well as the proof term.

So any theorem whose hypothesis is Tag 01W8's `IsLocallyProjective f` fails the axiom check no
matter how it is proved, and the statement of Tag 02O4 is in that position as written. The same
observation underlies
`StacksFrontier/AlgebraicGeometry/HProjective/Basic.lean`, which generalises the bundle away and
supplies the axiom-clean `Stacks.HProjective.IsHProjective` — a closed immersion into
`AlgebraicGeometry.projectiveSpaceOver n S` over `S`. The final theorem below therefore takes the
projectivity predicate as a parameter: it is instantiable at
Tag 01W8's `IsProjective`, at `Stacks.HProjective.IsHProjective`, or at whatever the library
finally carries, and the reduction is the same in each case.

**The cohomological hypothesis is indexed by opens of the base, not by the cover's schemes.**
Tag 01W8's `IsLocallyProjective` asserts projectivity of `pullback.snd f (𝒰.f i)` for an open
immersion `𝒰.f i : 𝒰.obj i ⟶ S`, while the restriction isomorphism of [Stacks, Tag 01E5] is
about `f ∣_ V` for `V : S.Opens`. Passing between them changes the *base* of the morphism, from
`𝒰.obj i` to `(𝒰.f i).opensRange`, and nothing in the library transports a projectivity
predicate along an isomorphism of the base — for Tag 01W8's `IsProjective` that would need base
change of Tag 01OB's projective bundle along an isomorphism. So the hypotheses below are stated
for the opens of `S` that the cover ranges over, which is where the cohomological input is needed
and where no such transport arises.

## References

* [Stacks Project, Tag 02O4](https://stacks.math.columbia.edu/tag/02O4)
* [Stacks Project, Tag 01E5](https://stacks.math.columbia.edu/tag/01E5)
* [Stacks Project, Tag 01BV](https://stacks.math.columbia.edu/tag/01BV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.ProjectiveCoherentImage

attribute [local instance] HasDerivedCategory.standard

variable {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (p : ℕ)

/-- **Coherence of a higher direct image over an open of the base.** If the `p`-th higher direct
image along `f ∣_ V` of the restriction of `F` to `f⁻¹(V)` is coherent, then so is the restriction
to `V` of the `p`-th higher direct image of `F` along `f`.

This is `higherDirectImageRestrictObjIso` — [Stacks, Tag 01E5] for schemes — together with the
closure of coherence under isomorphism, which is
`AlgebraicGeometry.CoherentAbelian.coherentModules_isClosedUnderIsomorphisms`. No hypothesis on
`f`, on `F` or on the base is used. -/
theorem isCoherent_restrict_higherDirectImage (V : S.Opens)
    (h : (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).obj F)).IsCoherent) :
    ((Scheme.Modules.restrictFunctor V.ι).obj
      (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F)).IsCoherent :=
  ObjectProperty.prop_of_iso
    (P := fun M : SheafOfModules.{u} V.toScheme.ringCatSheaf => M.IsCoherent)
    (higherDirectImageRestrictObjIso f V F p) h

/-- **The locality step in the proof of [Stacks, Tag 02O4].** Let `V` be a family of opens
covering the base. If for every member the `p`-th higher direct image along `f ∣_ V i` of the
restriction of `F` is coherent, then the `p`-th higher direct image of `F` along `f` is coherent.

`hglue` is the missing declaration `isCoherent_of_restrict` of the module documentation: coherence
of a sheaf of modules on a scheme is local on the scheme. Everything else is proved. -/
theorem isCoherent_higherDirectImage_of_cover {I : Type u} (V : I → S.Opens)
    (hV : iSup V = ⊤)
    (hglue : ∀ (T : Scheme.{u}) (M : T.Modules) (J : Type u) (W : J → T.Opens), iSup W = ⊤ →
      (∀ j, ((Scheme.Modules.restrictFunctor (W j).ι).obj M).IsCoherent) → M.IsCoherent)
    (h : ∀ i, (((Scheme.Modules.pushforward (f ∣_ V i)).rightDerivedPlus (p : ℤ)).obj
      ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V i).ι).obj F)).IsCoherent) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F).IsCoherent :=
  hglue S _ I V hV fun i => isCoherent_restrict_higherDirectImage f F p (V i) (h i)

/-- **The locality step, from an open cover of the base.** This is the shape in which
Tag 01W8's `IsLocallyProjective` supplies its datum: an `AlgebraicGeometry.Scheme.OpenCover` of the
base. The opens are the ranges of the covering immersions, and
`AlgebraicGeometry.Scheme.OpenCover.iSup_opensRange` is the covering hypothesis.

Together with `hglue`, the only input still owed by [Stacks, Tag 02O4] is `h`: its own conclusion
for each base restriction `f ∣_ (𝒰.f j).opensRange`. When `𝒰` is a cover witnessing local
projectivity, that morphism is isomorphic *as an arrow* to the projective `pullback.snd f (𝒰.f j)`
— but see the module documentation: no predicate transport along such an isomorphism exists, so
`h` is owed at `f ∣_ (𝒰.f j).opensRange` itself. -/
theorem isCoherent_higherDirectImage_of_openCover (𝒰 : Scheme.OpenCover.{u} S)
    (hglue : ∀ (T : Scheme.{u}) (M : T.Modules) (J : Type u) (W : J → T.Opens), iSup W = ⊤ →
      (∀ j, ((Scheme.Modules.restrictFunctor (W j).ι).obj M).IsCoherent) → M.IsCoherent)
    (h : ∀ j : 𝒰.I₀,
      (((Scheme.Modules.pushforward (f ∣_ (𝒰.f j).opensRange)).rightDerivedPlus (p : ℤ)).obj
        ((Scheme.Modules.restrictFunctor (f ⁻¹ᵁ (𝒰.f j).opensRange).ι).obj F)).IsCoherent) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F).IsCoherent :=
  isCoherent_higherDirectImage_of_cover f F p (fun j => (𝒰.f j).opensRange)
    𝒰.iSup_opensRange hglue h

/-- **[Stacks, Tag 02O4] reduced to its projective case, parametric in projectivity.** Let `Proj`
be any property of morphisms of schemes. If `f` is `Proj` after restricting the base to each
member of some open cover — which is the shape of Tag 01W8's `IsLocallyProjective`, of
`Stacks.HProjective.IsHProjective` localised, and of the source's hypothesis — then the `p`-th
higher direct image of a coherent module along `f` is coherent, given:

* `hglue` and `hres`, the two halves of "coherence of a sheaf of modules on a scheme is local on
  the scheme", which are the missing declarations `isCoherent_of_restrict` and
  `isCoherent_restrict` of the module documentation;
* `hproj`, the conclusion of [Stacks, Tag 02O4] for a morphism whose base restriction is `Proj` —
  the projective case, which is the substance of the source's argument and is proved nowhere in
  this repository.

What is proved here is the reduction: the locality of the source's step 2, which is
[Stacks, Tag 01E5] for schemes (`higherDirectImageRestrictObjIso`) plus the closure of coherence
under isomorphism. Nothing about the local projectivity of `f` is used beyond producing the
cover, and no hypothesis on the base is needed: local Noetherianness of `S` is consumed entirely
inside `hproj`. -/
theorem isCoherent_higherDirectImage_of_locallyProjective [F.IsCoherent]
    (Proj : ∀ {A B : Scheme.{u}}, (A ⟶ B) → Prop)
    (hf : ∃ 𝒰 : Scheme.OpenCover.{u} S, ∀ j : 𝒰.I₀, Proj (f ∣_ (𝒰.f j).opensRange))
    (hglue : ∀ (T : Scheme.{u}) (M : T.Modules) (J : Type u) (W : J → T.Opens), iSup W = ⊤ →
      (∀ j, ((Scheme.Modules.restrictFunctor (W j).ι).obj M).IsCoherent) → M.IsCoherent)
    (hres : ∀ (T : Scheme.{u}) (M : T.Modules), M.IsCoherent → ∀ U : T.Opens,
      ((Scheme.Modules.restrictFunctor U.ι).obj M).IsCoherent)
    (hproj : ∀ V : S.Opens, Proj (f ∣_ V) → ∀ G : (f ⁻¹ᵁ V).toScheme.Modules, G.IsCoherent →
      (((Scheme.Modules.pushforward (f ∣_ V)).rightDerivedPlus (p : ℤ)).obj G).IsCoherent) :
    (((Scheme.Modules.pushforward f).rightDerivedPlus (p : ℤ)).obj F).IsCoherent := by
  obtain ⟨𝒰, h𝒰⟩ := hf
  refine isCoherent_higherDirectImage_of_openCover f F p 𝒰 hglue fun j => ?_
  exact hproj _ (h𝒰 j) _ (hres X F ‹F.IsCoherent› _)

end AlgebraicGeometry.ProjectiveCoherentImage

end
