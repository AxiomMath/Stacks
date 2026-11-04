module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuous
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuleSheafFunctoriality
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImage
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.PresheafBaseChange

/-!
# Base change for direct images along a 1-morphism of categories fibred in groupoids

Let `S` be a scheme, let `τ` be a topology on the underlying category of schemes of a big fppf
site `B`, and let

```
𝒴' ×_𝒴 𝒳 --- g' ---> 𝒳
   |                 |
   f'                f
   |                 |
   v                 v
  𝒴' ------ g -----> 𝒴
```

be the canonical 2-cartesian square of categories fibred in groupoids over `(Sch/S)_fppf`,
with `g'` and `f'` the two projections of the 2-fibre product. Stacks 075H asserts that the
base-change map `g⁻¹Rf_*ℱ ⟶ Rf'_*(g')⁻¹ℱ` is an isomorphism, functorially in `ℱ`.

This file proves the base-change comparison in the two forms that the library's inputs support:

* in degree zero, exactly the isomorphism `g⁻¹f_*ℱ ≅ f'_*(g')⁻¹ℱ` of abelian sheaves which the
  source quotes from Stacks 075B;
* in every degree, with the right-hand side read as the right derived functor of the *composite*
  `f'_* ∘ (g')⁻¹`, i.e. `g⁻¹ ∘ Rⁱf_* ≅ Rⁱ(f'_* ∘ (g')⁻¹)`.

See the implementation notes for what separates the second form from the source's
`Rⁱf'_* ∘ (g')⁻¹` and why that gap is not closed here.

The source states the same conclusion for `ℱ` in `Mod(𝒳_τ, 𝒪_𝒳)`. At module coefficients the
comparison of the two composites is proved outright on underlying abelian presheaves, which is
`AlgebraicGeometry.Stack.modulePresheafBaseChangeIso`; the two statements about sheaves of
modules themselves are deduced from it, each carrying as a hypothesis the one input that is not
available in the library — that this presheaf-level isomorphism is `𝒪`-linear, i.e. that it is
the image of a morphism of the two composites of sheaves of modules. The implementation notes
say precisely what that hypothesis is and why it is irreducible here.

## Main definitions

* `AlgebraicGeometry.Stack.baseChangeTwoSquare`: the canonical 2-cartesian square, as a
  `CategoryTheory.TwoSquare`.

## Main results

* `AlgebraicGeometry.Stack.abelianPresheafBaseChangeIso`: **Stacks 075B** at abelian
  coefficients, the presheaf-level base-change isomorphism
  `g⁻¹ ∘ ran_f ≅ ran_{f'} ∘ (g')⁻¹`.
* `AlgebraicGeometry.Stack.abelianDirectImageBaseChangeIso`: **Stacks 075H in degree zero**,
  `f_* ⋙ g⁻¹ ≅ (g')⁻¹ ⋙ f'_*` on abelian sheaves.
* `AlgebraicGeometry.Stack.abelianHigherDirectImageBaseChangeIso`: **Stacks 075H in every
  degree**, `(Rⁱf_*) ⋙ g⁻¹ ≅ Rⁱ((g')⁻¹ ⋙ f'_*)`.
* `AlgebraicGeometry.Stack.modulePresheafBaseChangeIso`: **Stacks 075B at module
  coefficients**, the comparison of the two composites of inverse- and direct-image functors of
  sheaves of modules around the square, read on underlying abelian presheaves.
* `AlgebraicGeometry.Stack.nonempty_moduleDirectImageBaseChangeIso`:
  `f_* ⋙ g⁻¹ ≅ (g')⁻¹ ⋙ f'_*` on sheaves of modules, for a square whose presheaf-level
  comparison is `𝒪`-linear. Untagged: that hypothesis is what Stacks 075H asserts at module
  coefficients.
* `AlgebraicGeometry.Stack.nonempty_moduleHigherDirectImageBaseChangeIso`:
  `(Rⁱf_*) ⋙ g⁻¹ ≅ Rⁱ((g')⁻¹ ⋙ f'_*)` on sheaves of modules, under the same hypothesis, and
  untagged for the same reason.

Four facts about one 1-morphism, needed to write those statements down, are recorded on the
way: `AlgebraicGeometry.Stack.isContinuous_of_isFiberedInGroupoids` and
`AlgebraicGeometry.Stack.isCocontinuous_of_isFiberedInGroupoids` (the two conjuncts of Stacks
06NW, for a 1-morphism presented by the strict commutation over the base rather than as a
`Functor.IsFibredOneMorphism`), `AlgebraicGeometry.Stack.additive_sheafPushforwardContinuous`
and `AlgebraicGeometry.Stack.preservesHomology_sheafPushforwardContinuous` (additivity and
exactness of the inverse image of abelian sheaves), together with
`AlgebraicGeometry.Stack.isFibered_twoFibreProductStructureFunctor` for the apex of the
square.

## Implementation notes

*What the proof is.* Inverse image of abelian sheaves on these sites is restriction along the
1-morphism with no sheafification (Stacks 06NW), and direct image is right Kan extension along
its opposite, again with no sheafification once one lands back in presheaves (Stacks 06NW). So
on underlying presheaves both composites around the square are the two composites of a right
Kan extension with a restriction, and the comparison between them is Mathlib's
`CategoryTheory.TwoSquare.ranBaseChange` of the opposite square. That transformation is
invertible exactly because the square is Guitart exact, which for the canonical 2-fibre product
of categories fibred in groupoids is Stacks 075B,
`CategoryTheory.TwoFibreProductOver.guitartExact_twoFibreProductSquare`. The library states
075B's conclusion only at coefficients in `Type t`; the Guitart exactness it is deduced from is
coefficient-free, so the abelian form below is a second instance of one and the same lemma, and
it is what the source means by "it holds for arbitrary presheaves". Since `sheafToPresheaf` is
fully faithful, the presheaf-level isomorphism descends to the sheaf-level one, which is the
degree-zero statement.

Passing to all degrees uses only that `g⁻¹` is exact (Stacks 06NW), hence preserves homology,
so that it may be pulled out of a right derived functor:
`CategoryTheory.Functor.rightDerivedCompIso` gives
`(f_* ⋙ g⁻¹).rightDerived n ≅ (f_*).rightDerived n ⋙ g⁻¹`, and transporting the degree-zero
isomorphism through `CategoryTheory.Functor.rightDerivedIsoOfNatIso` identifies the left-hand
side with `((g')⁻¹ ⋙ f'_*).rightDerived n`. No injective resolution is compared by hand and no
sheafification formula is used.

*What is missing for the source's own right-hand side.* The source writes
`Rⁱf'_*((g')⁻¹ℱ)`, that is `(g')⁻¹` followed by the right derived functor of `f'_*`, whereas
the statement proved here is the right derived functor of the composite. The two agree as soon
as `(g')⁻¹` carries injective abelian sheaves on `𝒳` to `f'_*`-acyclic sheaves on `𝒴' ×_𝒴 𝒳`.
That is where the source's proof uses the *value* half of Stacks 075G — `Rⁱf_*ℱ` is the sheaf
associated with `y ↦ Hⁱ((Sch/V)_fppf ×_{y,𝒴} 𝒳, pr⁻¹ℱ)` — to reduce to a 2-fibre product over
a scheme-slice, where the projection to `𝒳` *is* faithful, so that Stacks 06X1
(`AlgebraicGeometry.Stack.injective_sheafPushforwardContinuous_obj`) applies and `(g')⁻¹` even
preserves injectives. That route is unavailable for a general `g`: a morphism of `𝒴' ×_𝒴 𝒳` is
a pair whose `𝒴'`-component is pinned by its `𝒳`-component only up to the fibres of `g`, so
`g'` is faithful when `g` is — or when `𝒴'` is faithful over the base, which is what a
scheme-slice supplies — but not in general. Stacks 06X1 is available, as
`AlgebraicGeometry.Stack.exact_sheafPullback_of_faithful` and
`AlgebraicGeometry.Stack.injective_sheafPushforwardContinuous_obj` in
`StacksFrontier/AlgebraicGeometry/Stacks/Sheaves/Injectives.lean`; what is missing is the value
half of Stacks 075G, which is what reduces a general `g` to the scheme-slice case in which
06X1 applies.

*Module coefficients.* Inverse image of sheaves of modules is objectwise restriction
(Stacks 06WE), so on underlying abelian presheaves it is again precomposition with the opposite
1-morphism, on the nose; direct image of sheaves of modules restricts the direct image of
presheaves of modules of Stacks 06WD, whose underlying abelian presheaf is the right Kan
extension by `AlgebraicGeometry.Stack.ModuleFunctoriality.pushforward_iso`. So the two composites
of module functors around the square become, on underlying abelian presheaves, exactly the two
composites that `AlgebraicGeometry.Stack.abelianPresheafBaseChangeIso` identifies, and
`AlgebraicGeometry.Stack.modulePresheafBaseChangeIso` is that identification; it needs no
hypothesis beyond the ones already carried, because the Guitart exactness it rests on is
coefficient-free.

What that does *not* give is an isomorphism of sheaves of modules, and the missing input is one
sentence: that the presheaf-level isomorphism is linear over the structure sheaf. Reflection of
isomorphisms does not supply it, and it is worth being exact about why, because the reflection
is real and looks as though it should. `PresheafOfModules.toPresheaf` is faithful out of an
abelian category and therefore reflects isomorphisms, and `SheafOfModules.toSheaf` reflects them
outright. But reflection runs the other way: it converts a *lift* of the presheaf-level
isomorphism to the module level into a module-level isomorphism; it does not produce the lift.
The two statements below therefore carry that lift as the hypothesis `hlinear` and conclude
`Nonempty` of the isomorphism. The linearity itself is *not* proved here, which is why neither
statement carries a Stacks tag.

Linearity is provable, and the tool for it is
`Stacks.SheafOfModules.ranBaseChange_π` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardCocontinuousSquare.lean`: base change
of right Kan extensions, read on the legs of the limit cones. No mate of adjunctions and no
criterion for invertibility of a mate is needed. Applied to the sheaves of rings that leg
formula identifies the two ring maps through which a section acts on a leg
(`Stacks.SheafOfModules.scalarπ_square_apply`), and applied to the sheaves of modules it turns
that identification into linearity (`Stacks.SheafOfModules.ranSMul_squareComparison`); that is
how the corresponding hypothesis was removed from Stacks 0FN3.

Two things keep it from applying to the statements below as they stand. The leg formula itself
is general in the `CategoryTheory.TwoSquare`, but everything built on it there is stated for a
*strictly* commutative square `u' ⋙ v = v' ⋙ u`, with the `2`-cell `eqToHom` of that equality;
the square here is not strict — an object of `CategoryTheory.TwoFibreProductOver` carries an
isomorphism `f(x) ≅ g(y)` and not an equality, so `fst ⋙ f` and `snd ⋙ g` already differ on
objects and the `2`-cell is `CategoryTheory.TwoFibreProductOver.psiIso`. And the conclusion
reached there is about `Stacks.SheafOfModules.pushforwardCocontinuous`, whose module structure
sits on the right Kan extension itself, so that it is characterised on the legs by
`Stacks.SheafOfModules.ranSMul_π`; the direct image used below is
`AlgebraicGeometry.Stack.moduleSheafPushforward`, whose underlying presheaf is the compatible
sections of Stacks 06WD and whose module structure is transported to the Kan extension along
`AlgebraicGeometry.Stack.ModuleFunctoriality.pushforward_iso`, so no leg description of it is
available.

The module universe of those statements is `max (u+1) v₁ w₁ v₂ w₂ v₃ w₃ a`. It is forced: the
direct image of sheaves of modules is a limit indexed by the two sites, and an object of the
apex `𝒴' ×_𝒴 𝒳` carries an object of the base category `BigFppfOver B S hS`, which lives in
`Type (u+1)`. The coefficient universe `a` is free on top of that, exactly as for the abelian
statements.

*Generality.* The source fixes algebraic stacks and `τ` among the Zariski, étale, smooth,
syntomic and fppf topologies. Nothing below uses either: the statements are for categories
fibred in groupoids over the big fppf category of `S` — the generality of Stacks 075B, and the
one the footnote of Stacks 075G asks for — and for an arbitrary topology on `B.Schemes`, as
`AlgebraicGeometry.Stack.associatedTopology` and the rest of this directory do. The source's
five statements for algebraic stacks are instances. The apex of the square is the canonical
2-fibre product `𝒴' ×_𝒴 𝒳`, which is the apex the source displays.

The coefficient universe `a` is independent of the universe of the base scheme, and the
hypotheses asking for pointwise right Kan extensions, for sheafification and for injective
resolutions are size conditions on the sites, not mathematical content; they appear on
`CategoryTheory.Functor.sheafPushforwardCocontinuous` and on
`AlgebraicGeometry.Stack.derivedPresheafDirectImage` for the same reason.

## References

* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 075B](https://stacks.math.columbia.edu/tag/075B)
* [Stacks Project, Tag 075G](https://stacks.math.columbia.edu/tag/075G)
* [Stacks Project, Tag 06NW](https://stacks.math.columbia.edu/tag/06NW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u u₀ w₀ v₁ v₂ v₃ w₁ w₂ w₃ a
universe va wa vb wb mo

/-! ### The canonical square and its presheaf-level base change -/

section Square

variable {𝒞 : Type u₀} [Category.{w₀} 𝒞]
  {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴' : Type v₂} [Category.{w₂} 𝒴']
  {𝒴 : Type v₃} [Category.{w₃} 𝒴]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴' : 𝒴' ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)

/-- The canonical 2-cartesian square
```
𝒴' ×_𝒴 𝒳 --- g' ---> 𝒳
   |                 |
   f'                f
   |                 |
   v                 v
  𝒴' ------ g -----> 𝒴
```
of categories over `𝒞`, read as a `CategoryTheory.TwoSquare`: its two upper edges are the
projections `g' = TwoFibreProductOver.fst` and `f' = TwoFibreProductOver.snd` of the 2-fibre
product and its 2-cell is the comparison isomorphism `ψ` of Stacks 0040. -/
abbrev baseChangeTwoSquare :
    TwoSquare (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g)
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) f g :=
  TwoSquare.mk _ _ _ _ (TwoFibreProductOver.psiIso p𝒳 p𝒴' p𝒴 f g).hom

/-- The structure functor of the apex of the canonical square is a fibred category over `𝒞`:
the apex is fibred in groupoids by Stacks 0041. -/
theorem isFibered_twoFibreProductStructureFunctor
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴') :
    (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g).IsFibered :=
  (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc).isFibered

/-- **Stacks 075B at abelian coefficients.** For the canonical 2-cartesian square of categories
fibred in groupoids over `𝒞`, the base-change transformation `g⁻¹f_* ⟶ f'_*(g')⁻¹` of
presheaves of abelian groups is an isomorphism, naturally in the presheaf.

Direct image of presheaves is right Kan extension along the opposite functor and inverse image
is restriction, so the transformation is `CategoryTheory.TwoSquare.ranBaseChange` of the
opposite square, which is invertible because the square is Guitart exact. The library's
`CategoryTheory.TwoFibreProductOver.isIso_presheafRanBaseChange` is the same statement at
coefficients in `Type t`; both are instances of the one coefficient-free input
`CategoryTheory.TwoFibreProductOver.guitartExact_twoFibreProductSquare`. -/
@[stacks 075B "abelian coefficients"]
noncomputable def abelianPresheafBaseChangeIso
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{a}, f.op.HasPointwiseRightKanExtension G]
    [∀ G : (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)ᵒᵖ ⥤ AddCommGrpCat.{a},
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).op.HasPointwiseRightKanExtension G] :
    f.op.ran ⋙ (Functor.whiskeringLeft _ _ AddCommGrpCat.{a}).obj g.op ≅
      (Functor.whiskeringLeft _ _ AddCommGrpCat.{a}).obj
          (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).op ⋙
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).op.ran :=
  have : (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).GuitartExact :=
    TwoFibreProductOver.guitartExact_twoFibreProductSquare p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  have : (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).op.GuitartExact := inferInstance
  asIso ((baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).op.ranBaseChange (D := AddCommGrpCat.{a}))

end Square

/-! ### Base change on the associated sites -/

section Sites

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴' : Type v₂} [Category.{w₂} 𝒴']
  {𝒴 : Type v₃} [Category.{w₃} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes)

/-- A 1-morphism of categories fibred in groupoids over the big fppf category of `S` is
continuous for the associated topologies: the first conjunct of Stacks 06NW. -/
theorem isContinuous_of_isFiberedInGroupoids [p𝒳.IsFibered] [p𝒴.IsFibered]
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) :
    f.IsContinuous (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ) :=
  ((h𝒴.isFibredOneMorphism hfc).isContinuous_and_isCocontinuous_inheritedTopology _).1

/-- A 1-morphism of categories fibred in groupoids over the big fppf category of `S` is
cocontinuous for the associated topologies: the second conjunct of Stacks 06NW. -/
theorem isCocontinuous_of_isFiberedInGroupoids [p𝒳.IsFibered] [p𝒴.IsFibered]
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) :
    f.IsCocontinuous (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ) :=
  ((h𝒴.isFibredOneMorphism hfc).isContinuous_and_isCocontinuous_inheritedTopology _).2

/-- Inverse image of abelian sheaves along a 1-morphism of fibred categories is additive: it is
restriction along the 1-morphism, which is additive on underlying presheaves, and the inclusion
of sheaves into presheaves is faithful. -/
theorem additive_sheafPushforwardContinuous [p𝒳.IsFibered] [p𝒴.IsFibered]
    (hf : p𝒳.IsFibredOneMorphism p𝒴 f)
    [HasSheafify (associatedTopology B S hS p𝒳 τ) AddCommGrpCat.{a}]
    [HasSheafify (associatedTopology B S hS p𝒴 τ) AddCommGrpCat.{a}] :
    letI := (hf.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
    (f.sheafPushforwardContinuous AddCommGrpCat.{a}
      (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ)).Additive := by
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  let := Functor.additive_of_iso
    (hf.inverseImageCompSheafToPresheafIso (τ.over (B.obj hS)) AddCommGrpCat.{a}).symm
  exact Functor.additive_of_comp_faithful _
    (sheafToPresheaf (associatedTopology B S hS p𝒳 τ) AddCommGrpCat.{a})

/-- Inverse image of abelian sheaves along a 1-morphism of fibred categories is exact: it is
left exact by Stacks 06NW and right exact as a left adjoint. -/
theorem preservesHomology_sheafPushforwardContinuous [p𝒳.IsFibered] [p𝒴.IsFibered]
    (hf : p𝒳.IsFibredOneMorphism p𝒴 f)
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{a}, f.op.HasPointwiseRightKanExtension G]
    [HasSheafify (associatedTopology B S hS p𝒳 τ) AddCommGrpCat.{a}]
    [HasSheafify (associatedTopology B S hS p𝒴 τ) AddCommGrpCat.{a}] :
    letI := (hf.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
    letI := additive_sheafPushforwardContinuous.{u, v₁, v₃, w₁, w₃, a} B S hS p𝒳 p𝒴 f τ hf
    (f.sheafPushforwardContinuous AddCommGrpCat.{a}
      (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ)).PreservesHomology := by
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  let := additive_sheafPushforwardContinuous.{u, v₁, v₃, w₁, w₃, a} B S hS p𝒳 p𝒴 f τ hf
  let := hf.preservesFiniteLimits_inverseImage (J := τ.over (B.obj hS))
    (A := AddCommGrpCat.{a})
  let := (hf.sheafAdjunctionInheritedTopology (τ.over (B.obj hS))
    AddCommGrpCat.{a}).leftAdjoint_preservesColimits
  infer_instance

end Sites

/-! ### The base change isomorphisms -/

section BaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴' : Type v₂} [Category.{w₂} 𝒴']
  {𝒴 : Type v₃} [Category.{w₃} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes)

/-- **Stacks 075H in degree zero.** For the canonical 2-cartesian square of categories fibred in
groupoids over the big fppf category of `S` and any topology `τ` on `B.Schemes`, the
base-change map `g⁻¹f_*ℱ ⟶ f'_*(g')⁻¹ℱ` of abelian sheaves on the associated sites is an
isomorphism, naturally in `ℱ`.

This is the identification the source quotes from Stacks 075B at the start of the proof of
Stacks 075H. Both composites become, on underlying presheaves, the two ways round the square of
a right Kan extension and a restriction (Stacks 06NW), where they are identified by
`AlgebraicGeometry.Stack.abelianPresheafBaseChangeIso`; the descent to sheaves is full
faithfulness of `sheafToPresheaf`. -/
@[stacks 075H "degree zero, abelian sheaves: g⁻¹f_*ℱ ≅ f'_*(g')⁻¹ℱ"]
noncomputable def abelianDirectImageBaseChangeIso
    [p𝒳.IsFibered] [p𝒴'.IsFibered] [p𝒴.IsFibered]
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{a}, f.op.HasPointwiseRightKanExtension G]
    [∀ G : (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)ᵒᵖ ⥤ AddCommGrpCat.{a},
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).op.HasPointwiseRightKanExtension G] :
    letI : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g).IsFibered :=
      isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS p𝒳 p𝒴 f τ h𝒴 hfc
    letI := isContinuous_of_isFiberedInGroupoids B S hS p𝒴' p𝒴 g τ h𝒴 hgc
    letI := isContinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ h𝒳 TwoFibreProductOver.fst_comp_eq
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ h𝒴' TwoFibreProductOver.snd_comp_eq
    f.sheafPushforwardCocontinuous AddCommGrpCat.{a}
          (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ) ⋙
        g.sheafPushforwardContinuous AddCommGrpCat.{a}
          (associatedTopology B S hS p𝒴' τ) (associatedTopology B S hS p𝒴 τ) ≅
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).sheafPushforwardContinuous AddCommGrpCat.{a}
          (associatedTopology B S hS
            (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
          (associatedTopology B S hS p𝒳 τ) ⋙
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
          AddCommGrpCat.{a}
          (associatedTopology B S hS
            (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
          (associatedTopology B S hS p𝒴' τ) := by
  let := isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  let hf := h𝒴.isFibredOneMorphism hfc
  let hg := h𝒴.isFibredOneMorphism hgc
  let hprX := h𝒳.isFibredOneMorphism
    (TwoFibreProductOver.fst_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴') (p𝒮 := p𝒴) (F := f) (G := g))
  let hprY := h𝒴'.isFibredOneMorphism
    (TwoFibreProductOver.snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴') (p𝒮 := p𝒴) (F := f) (G := g))
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  let := (hg.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  let := (hprX.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  let := (hprY.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  refine Functor.fullyFaithfulCancelRight
    (sheafToPresheaf (associatedTopology B S hS p𝒴' τ) AddCommGrpCat.{a}) ?_
  exact Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (hg.inverseImageCompSheafToPresheafIso (τ.over (B.obj hS)) AddCommGrpCat.{a}) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (hf.directImageCompSheafToPresheafIso (τ.over (B.obj hS)) AddCommGrpCat.{a}) _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (abelianPresheafBaseChangeIso p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (hprX.inverseImageCompSheafToPresheafIso (τ.over (B.obj hS))
        AddCommGrpCat.{a}).symm _ ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _
      (hprY.directImageCompSheafToPresheafIso (τ.over (B.obj hS))
        AddCommGrpCat.{a}).symm ≪≫
    (Functor.associator _ _ _).symm

/-- **Stacks 075H in every degree.** For the canonical 2-cartesian square of categories fibred
in groupoids over the big fppf category of `S` and any topology `τ` on `B.Schemes`, the
base-change map is an isomorphism
`g⁻¹Rⁱf_*ℱ ≅ Rⁱ(f'_*(g')⁻¹)ℱ`
of abelian sheaves on the associated site of `𝒴'`, naturally in `ℱ`.

The right-hand side is the `i`-th right derived functor of the composite `f'_* ∘ (g')⁻¹`. The
source writes instead `Rⁱf'_*((g')⁻¹ℱ)`, the `i`-th right derived functor of `f'_*` evaluated
at `(g')⁻¹ℱ`; the two differ by whether `(g')⁻¹` sends injective abelian sheaves to
`f'_*`-acyclic ones, which is not available here. See the implementation notes of this file.

The proof uses nothing beyond the degree-zero isomorphism
`AlgebraicGeometry.Stack.abelianDirectImageBaseChangeIso` and exactness of `g⁻¹` (Stacks 06NW):
an exact functor may be pulled out of a right derived functor, so
`(f_* ⋙ g⁻¹).rightDerived i ≅ (f_*).rightDerived i ⋙ g⁻¹`, and the degree-zero isomorphism
rewrites the left-hand side. -/
@[stacks 075H "all degrees, abelian sheaves; Rⁱf'_*(g')⁻¹ as the right derived functor of the \
composite f'_* ∘ (g')⁻¹"]
noncomputable def abelianHigherDirectImageBaseChangeIso
    [p𝒳.IsFibered] [p𝒴'.IsFibered] [p𝒴.IsFibered]
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴') (n : ℕ)
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{a}, f.op.HasPointwiseRightKanExtension G]
    [∀ G : 𝒴'ᵒᵖ ⥤ AddCommGrpCat.{a}, g.op.HasPointwiseRightKanExtension G]
    [∀ G : (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)ᵒᵖ ⥤ AddCommGrpCat.{a},
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).op.HasPointwiseRightKanExtension G]
    [HasSheafify (associatedTopology B S hS p𝒳 τ) AddCommGrpCat.{a}]
    [HasSheafify (associatedTopology B S hS p𝒴' τ) AddCommGrpCat.{a}]
    [HasSheafify (associatedTopology B S hS p𝒴 τ) AddCommGrpCat.{a}]
    [HasSheafify (associatedTopology B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ) AddCommGrpCat.{a}]
    [HasInjectiveResolutions
      (Sheaf (associatedTopology B S hS p𝒳 τ) AddCommGrpCat.{a})] :
    letI : (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g).IsFibered :=
      isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS p𝒳 p𝒴 f τ h𝒴 hfc
    letI := isContinuous_of_isFiberedInGroupoids B S hS p𝒴' p𝒴 g τ h𝒴 hgc
    letI := isContinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ h𝒳 TwoFibreProductOver.fst_comp_eq
    letI := isCocontinuous_of_isFiberedInGroupoids B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ h𝒴' TwoFibreProductOver.snd_comp_eq
    letI : (f.sheafPushforwardCocontinuous AddCommGrpCat.{a}
        (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ)).Additive :=
      additive_sheafPushforwardCocontinuous B S hS p𝒳 p𝒴 f τ (h𝒴.isFibredOneMorphism hfc)
    letI : ((TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).sheafPushforwardContinuous
        AddCommGrpCat.{a}
        (associatedTopology B S hS
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
        (associatedTopology B S hS p𝒳 τ)).Additive :=
      additive_sheafPushforwardContinuous B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
        (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ
        (h𝒳.isFibredOneMorphism TwoFibreProductOver.fst_comp_eq)
    letI : ((TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
        AddCommGrpCat.{a}
        (associatedTopology B S hS
          (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
        (associatedTopology B S hS p𝒴' τ)).Additive :=
      additive_sheafPushforwardCocontinuous B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
        (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ
        (h𝒴'.isFibredOneMorphism TwoFibreProductOver.snd_comp_eq)
    (f.sheafPushforwardCocontinuous AddCommGrpCat.{a}
            (associatedTopology B S hS p𝒳 τ)
            (associatedTopology B S hS p𝒴 τ)).rightDerived n ⋙
        g.sheafPushforwardContinuous AddCommGrpCat.{a}
          (associatedTopology B S hS p𝒴' τ) (associatedTopology B S hS p𝒴 τ) ≅
      ((TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).sheafPushforwardContinuous AddCommGrpCat.{a}
            (associatedTopology B S hS
              (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
            (associatedTopology B S hS p𝒳 τ) ⋙
          (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
            AddCommGrpCat.{a}
            (associatedTopology B S hS
              (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
            (associatedTopology B S hS p𝒴' τ)).rightDerived n := by
  let := isFibered_twoFibreProductStructureFunctor p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  let hf := h𝒴.isFibredOneMorphism hfc
  let hg := h𝒴.isFibredOneMorphism hgc
  let hprX := h𝒳.isFibredOneMorphism
    (TwoFibreProductOver.fst_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴') (p𝒮 := p𝒴) (F := f) (G := g))
  let hprY := h𝒴'.isFibredOneMorphism
    (TwoFibreProductOver.snd_comp_eq (p𝒳 := p𝒳) (p𝒴 := p𝒴') (p𝒮 := p𝒴) (F := f) (G := g))
  let := (hf.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  let := (hg.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  let := (hprX.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).1
  let := (hprY.isContinuous_and_isCocontinuous_inheritedTopology (τ.over (B.obj hS))).2
  let : (f.sheafPushforwardCocontinuous AddCommGrpCat.{a}
      (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ)).Additive :=
    additive_sheafPushforwardCocontinuous B S hS p𝒳 p𝒴 f τ hf
  let : (g.sheafPushforwardContinuous AddCommGrpCat.{a}
      (associatedTopology B S hS p𝒴' τ) (associatedTopology B S hS p𝒴 τ)).Additive :=
    additive_sheafPushforwardContinuous B S hS p𝒴' p𝒴 g τ hg
  let : (g.sheafPushforwardContinuous AddCommGrpCat.{a}
      (associatedTopology B S hS p𝒴' τ)
      (associatedTopology B S hS p𝒴 τ)).PreservesHomology :=
    preservesHomology_sheafPushforwardContinuous B S hS p𝒴' p𝒴 g τ hg
  let : ((TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g).sheafPushforwardContinuous
      AddCommGrpCat.{a}
      (associatedTopology B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
      (associatedTopology B S hS p𝒳 τ)).Additive :=
    additive_sheafPushforwardContinuous B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) τ hprX
  let : ((TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).sheafPushforwardCocontinuous
      AddCommGrpCat.{a}
      (associatedTopology B S hS
        (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) τ)
      (associatedTopology B S hS p𝒴' τ)).Additive :=
    additive_sheafPushforwardCocontinuous B S hS
      (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) τ hprY
  exact (Functor.rightDerivedCompIso
      (f.sheafPushforwardCocontinuous AddCommGrpCat.{a}
        (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ))
      (g.sheafPushforwardContinuous AddCommGrpCat.{a}
        (associatedTopology B S hS p𝒴' τ) (associatedTopology B S hS p𝒴 τ)) n).symm ≪≫
    Functor.rightDerivedIsoOfNatIso
      (abelianDirectImageBaseChangeIso B S hS p𝒳 p𝒴' p𝒴 f g τ h𝒳 h𝒴' h𝒴 hfc hgc) n

end BaseChange

/-! ### Sheaves of modules: the comparison on underlying presheaves -/

section ModuleComparison

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒜 : Type va} [Category.{wa} 𝒜] {ℬ : Type vb} [Category.{wb} ℬ]
  (p : 𝒜 ⥤ BigFppfOver B S hS) (q : ℬ ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (F : 𝒜 ⥤ ℬ) (hF : F ⋙ q = p)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- On underlying abelian presheaves, the direct image of sheaves of modules along a 1-morphism
of categories fibred in groupoids is the right Kan extension along the opposite 1-morphism.

The direct image of sheaves of modules is the direct image of presheaves of modules of Stacks
06WD with nothing else happening, by `AlgebraicGeometry.Stack.moduleSheafPushforward_obj_val`,
and that one is the right Kan extension on underlying abelian presheaves by
`AlgebraicGeometry.Stack.ModuleFunctoriality.pushforward_iso`. -/
noncomputable def moduleSheafPushforwardCompToPresheafIso :
    moduleSheafPushforward.{u, va, wa, mo, vb, wb} B S hS p q hp hq F hF τ hτ ⋙
        (SheafOfModules.forget (ringStructureSheafCore B S hS q hq τ hτ) ⋙
          PresheafOfModules.toPresheaf (ringStructureSheafCore B S hS q hq τ hτ).obj) ≅
      (SheafOfModules.forget (ringStructureSheafCore B S hS p hp τ hτ) ⋙
          PresheafOfModules.toPresheaf (ringStructureSheafCore B S hS p hp τ hτ).obj) ⋙
        F.op.ran :=
  Functor.isoWhiskerLeft (SheafOfModules.forget (ringStructureSheafCore B S hS p hp τ hτ))
    (moduleFunctoriality.{u, va, wa, mo} B S hS p q hp hq F hF).pushforward_iso

/-- On underlying abelian presheaves, the inverse image of sheaves of modules along a 1-morphism
of categories fibred in groupoids is precomposition with the opposite 1-morphism.

The inverse image is objectwise restriction of modules followed by a transport of scalars along
an equality of presheaves of rings, and by
`AlgebraicGeometry.Stack.modulePullback_obj_val_presheaf` neither step changes the underlying
abelian presheaf. The two functors are therefore equal, not merely isomorphic, and this
isomorphism is the identity: nothing is proved below, `Iso.refl` typechecks. -/
noncomputable def modulePullbackCompToPresheafIso :
    modulePullback.{u, va, wa, max u va wa mo vb wb, vb, wb} B S hS p q hp hq F hF τ hτ ⋙
        (SheafOfModules.forget (ringStructureSheafCore B S hS p hp τ hτ) ⋙
          PresheafOfModules.toPresheaf (ringStructureSheafCore B S hS p hp τ hτ).obj) ≅
      (SheafOfModules.forget (ringStructureSheafCore B S hS q hq τ hτ) ⋙
          PresheafOfModules.toPresheaf (ringStructureSheafCore B S hS q hq τ hτ).obj) ⋙
        (Functor.whiskeringLeft _ _ AddCommGrpCat.{max u va wa mo vb wb}).obj F.op :=
  Iso.refl _

/-- The inverse image of sheaves of modules along a 1-morphism of categories fibred in groupoids
preserves finite limits.

This is the statement of `AlgebraicGeometry.Stack.preservesFiniteLimits_modulePullback`, proved
again here in the way
`AlgebraicGeometry.Stack.preservesFiniteLimits_sheafOfModules_pushforward` is, so that this file
need not import the quasi-coherent part of the library for it: on underlying abelian sheaves the
functor is the inverse image of Stacks 06NW, which is left exact, and `SheafOfModules.toSheaf`
reflects finite limits. -/
theorem preservesFiniteLimits_modulePullback' :
    PreservesFiniteLimits
      (modulePullback.{u, va, wa, mo, vb, wb} B S hS p q hp hq F hF τ hτ) := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hF).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  let := (hq.isFibredOneMorphism hF).preservesFiniteLimits_inverseImage
    (J := τ.over (B.obj hS)) (A := AddCommGrpCat.{mo})
  let e : modulePullback.{u, va, wa, mo, vb, wb} B S hS p q hp hq F hF τ hτ ⋙
        SheafOfModules.toSheaf.{mo} (ringStructureSheafCore B S hS p hp τ hτ) ≅
      SheafOfModules.toSheaf.{mo} (ringStructureSheafCore B S hS q hq τ hτ) ⋙
        F.sheafPushforwardContinuous AddCommGrpCat.{mo}
          (associatedTopology B S hS p τ) (associatedTopology B S hS q τ) := Iso.refl _
  let : PreservesFiniteLimits
      (modulePullback.{u, va, wa, mo, vb, wb} B S hS p q hp hq F hF τ hτ ⋙
        SheafOfModules.toSheaf.{mo} (ringStructureSheafCore B S hS p hp τ hτ)) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (SheafOfModules.toSheaf.{mo} (ringStructureSheafCore B S hS p hp τ hτ))

/-- The inverse image of sheaves of modules along a 1-morphism is additive. -/
private theorem additive_modulePullback' :
    (modulePullback.{u, va, wa, mo, vb, wb} B S hS p q hp hq F hF τ hτ).Additive :=
  { map_add := by intros; rfl }

/-- The direct image of sheaves of modules along a 1-morphism is additive, being a right
adjoint. -/
private theorem additive_moduleSheafPushforward' :
    (moduleSheafPushforward.{u, va, wa, mo, vb, wb} B S hS p q hp hq F hF τ hτ).Additive :=
  have := additive_modulePullback'.{u, va, wa, vb, wb, max u va wa mo vb wb}
    B S hS p q hp hq F hF τ hτ
  (moduleSheafAdjunction.{u, va, wa, mo, vb, wb} B S hS p q hp hq F hF τ hτ).right_adjoint_additive

end ModuleComparison

/-! ### The base change isomorphisms for sheaves of modules -/

section ModuleBaseChange

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴' : Type v₂} [Category.{w₂} 𝒴']
  {𝒴 : Type v₃} [Category.{w₃} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- **Stacks 075B at module coefficients.** For the canonical 2-cartesian square of categories
fibred in groupoids over the big fppf category of `S` and any topology `τ` on `B.Schemes`, the
two composites `f_* ⋙ g⁻¹` and `(g')⁻¹ ⋙ f'_*` of inverse- and direct-image functors of sheaves
of modules are isomorphic on underlying abelian presheaves, naturally in the sheaf of modules.

Inverse image of sheaves of modules is objectwise restriction and direct image is the right Kan
extension along the opposite 1-morphism, both on underlying abelian presheaves
(`AlgebraicGeometry.Stack.modulePullbackCompToPresheafIso` and
`AlgebraicGeometry.Stack.moduleSheafPushforwardCompToPresheafIso`), so both composites become
the two ways round the square of a right Kan extension and a restriction, where they are
identified by `AlgebraicGeometry.Stack.abelianPresheafBaseChangeIso`. Nothing here is special to
modules: the Guitart exactness that identification rests on is coefficient-free. -/
@[stacks 075B "module coefficients, on underlying abelian presheaves"]
noncomputable def modulePresheafBaseChangeIso
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a},
      f.op.HasPointwiseRightKanExtension G]
    [∀ G : (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a},
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).op.HasPointwiseRightKanExtension G] :
    ((moduleSheafPushforward.{u, v₁, w₁, max (u + 1) v₂ w₂ a, v₃, w₃}
          B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ) ⋙
        (modulePullback.{u, v₂, w₂, max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₃, w₃}
          B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ)) ⋙
      (SheafOfModules.forget (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ) ⋙
        PresheafOfModules.toPresheaf (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ).obj) ≅
      ((modulePullback.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
              max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₁, w₁}
          B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
            h𝒳 (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g)
            TwoFibreProductOver.fst_comp_eq τ hτ) ⋙
        (moduleSheafPushforward.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
              max v₃ a, v₂, w₂}
          B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
            h𝒴' (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g)
            TwoFibreProductOver.snd_comp_eq τ hτ)) ⋙
      (SheafOfModules.forget (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ) ⋙
        PresheafOfModules.toPresheaf (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ).obj) :=
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft _
    (modulePullbackCompToPresheafIso.{u, v₂, w₂, v₃, w₃, max (u + 1) v₁ w₁ a}
      B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight
    (moduleSheafPushforwardCompToPresheafIso.{u, v₁, w₁, v₃, w₃, max (u + 1) v₂ w₂ a}
      B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ) _ ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft _
    (abelianPresheafBaseChangeIso p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) ≪≫
  (Functor.associator _ _ _).symm ≪≫
  Functor.isoWhiskerRight
    (modulePullbackCompToPresheafIso.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
        v₁, w₁, max v₃ a}
      B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq τ hτ).symm _ ≪≫
  Functor.associator _ _ _ ≪≫
  Functor.isoWhiskerLeft _
    (moduleSheafPushforwardCompToPresheafIso.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
        v₂, w₂, max v₃ a}
      B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
      (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ hτ).symm ≪≫
  (Functor.associator _ _ _).symm

/-- **Stacks 075H in degree zero at module coefficients.** For the canonical 2-cartesian square
of categories fibred in groupoids over the big fppf category of `S` and any topology `τ` on
`B.Schemes`, the base-change map `g⁻¹f_*ℱ ⟶ f'_*(g')⁻¹ℱ` of sheaves of modules over the
structure sheaves of Stacks 06TV is an isomorphism, naturally in `ℱ`, *provided* the
presheaf-level isomorphism `AlgebraicGeometry.Stack.modulePresheafBaseChangeIso` is linear over
the structure sheaf.

Linearity is the hypothesis `hlinear`: a morphism `θ` of the two composites of sheaves of
modules whose underlying morphism of abelian presheaves is that isomorphism. Granting it, `θ` is
invertible, because `PresheafOfModules.toPresheaf` and `SheafOfModules.forget` both reflect
isomorphisms.

This statement carries no Stacks tag. Together with the reflection it applies, `hlinear` is the
module-level isomorphism that Stacks 075H asserts at module coefficients, so tagging it would
name as a hypothesis the thing the tag asserts. The implementation notes of this file record
what would discharge `hlinear` and what stands in the way. -/
theorem nonempty_moduleDirectImageBaseChangeIso
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a},
      f.op.HasPointwiseRightKanExtension G]
    [∀ G : (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a},
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).op.HasPointwiseRightKanExtension G]
    (hlinear : ∃ θ :
        moduleSheafPushforward.{u, v₁, w₁, max (u + 1) v₂ w₂ a, v₃, w₃}
          B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ ⋙
          modulePullback.{u, v₂, w₂, max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₃, w₃}
            B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ ⟶
        modulePullback.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
              max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₁, w₁}
          B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
            h𝒳 (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g)
            TwoFibreProductOver.fst_comp_eq τ hτ ⋙
          moduleSheafPushforward.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
                max v₃ a, v₂, w₂}
            B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
            (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
              h𝒴' (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g)
              TwoFibreProductOver.snd_comp_eq τ hτ,
      Functor.whiskerRight θ
          (SheafOfModules.forget (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ) ⋙
            PresheafOfModules.toPresheaf (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ).obj) =
        (modulePresheafBaseChangeIso B S hS p𝒳 p𝒴' p𝒴 f g τ hτ
          h𝒳 h𝒴' h𝒴 hfc hgc).hom) :
    Nonempty
      ((moduleSheafPushforward.{u, v₁, w₁, max (u + 1) v₂ w₂ a, v₃, w₃}
          B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ) ⋙
          (modulePullback.{u, v₂, w₂, max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₃, w₃}
            B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ) ≅
        (modulePullback.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
              max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₁, w₁}
          B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
            h𝒳 (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g)
            TwoFibreProductOver.fst_comp_eq τ hτ) ⋙
          (moduleSheafPushforward.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
                max v₃ a, v₂, w₂}
            B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
            (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
              h𝒴' (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g)
              TwoFibreProductOver.snd_comp_eq τ hτ)) := by
  obtain ⟨θ, hθ⟩ := hlinear
  have hw : IsIso (Functor.whiskerRight θ
      (SheafOfModules.forget (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ) ⋙
        PresheafOfModules.toPresheaf (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ).obj)) := by
    rw [hθ]; infer_instance
  have hiso : ∀ M, IsIso (θ.app M) := fun M ↦ by
    have h1 : IsIso ((Functor.whiskerRight θ
        (SheafOfModules.forget (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ) ⋙
            PresheafOfModules.toPresheaf
              (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ).obj)).app M) :=
      inferInstance
    simp only [Functor.whiskerRight_app, Functor.comp_map] at h1
    have h2 := isIso_of_reflects_iso
      ((SheafOfModules.forget (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ)).map (θ.app M))
      (PresheafOfModules.toPresheaf (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ).obj)
    exact isIso_of_reflects_iso (θ.app M)
      (SheafOfModules.forget (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ))
  have : IsIso θ := NatIso.isIso_of_isIso_app θ
  exact ⟨asIso θ⟩

/-- **Stacks 075H in every degree at module coefficients.** For the canonical 2-cartesian square
of categories fibred in groupoids over the big fppf category of `S` and any topology `τ` on
`B.Schemes`, the base-change map is an isomorphism `g⁻¹Rⁱf_*ℱ ≅ Rⁱ(f'_*(g')⁻¹)ℱ` of sheaves of
modules, naturally in `ℱ`, under the same linearity hypothesis as
`AlgebraicGeometry.Stack.nonempty_moduleDirectImageBaseChangeIso`.

As at abelian coefficients the right-hand side is the `i`-th right derived functor of the
composite `f'_* ∘ (g')⁻¹` and not the `i`-th right derived functor of `f'_*` evaluated at
`(g')⁻¹ℱ`; the two differ by whether `(g')⁻¹` carries injective sheaves of modules to
`f'_*`-acyclic ones, which is unavailable for the same reason as in the abelian case.

The proof adds nothing to the degree-zero statement beyond exactness of `g⁻¹` on sheaves of
modules: that functor is additive and a left adjoint, hence right exact, and left exact by
`AlgebraicGeometry.Stack.preservesFiniteLimits_modulePullback'`, so it preserves homology and
may be pulled out of a right derived functor.

Like the degree-zero statement this carries no Stacks tag, and for the same reason. -/
theorem nonempty_moduleHigherDirectImageBaseChangeIso
    (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
    (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴') (n : ℕ)
    [∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a},
      f.op.HasPointwiseRightKanExtension G]
    [∀ G : (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a},
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).op.HasPointwiseRightKanExtension G]
    [HasSheafify (associatedTopology B S hS p𝒳 τ) AddCommGrpCat.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [(associatedTopology B S hS p𝒳 τ).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [HasSheafify (associatedTopology B S hS p𝒴' τ) AddCommGrpCat.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [(associatedTopology B S hS p𝒴' τ).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [HasSheafify (associatedTopology B S hS p𝒴 τ) AddCommGrpCat.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [(associatedTopology B S hS p𝒴 τ).WEqualsLocallyBijective
      AddCommGrpCat.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a}]
    [HasInjectiveResolutions
      (SheafOfModules.{max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a} (ringStructureSheafCore B S hS p𝒳 h𝒳 τ hτ))]
    (hlinear : ∃ θ :
        moduleSheafPushforward.{u, v₁, w₁, max (u + 1) v₂ w₂ a, v₃, w₃}
          B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ ⋙
          modulePullback.{u, v₂, w₂, max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₃, w₃}
            B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ ⟶
        modulePullback.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
              max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₁, w₁}
          B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
            h𝒳 (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g)
            TwoFibreProductOver.fst_comp_eq τ hτ ⋙
          moduleSheafPushforward.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
                max v₃ a, v₂, w₂}
            B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
            (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
              h𝒴' (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g)
              TwoFibreProductOver.snd_comp_eq τ hτ,
      Functor.whiskerRight θ
          (SheafOfModules.forget (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ) ⋙
            PresheafOfModules.toPresheaf (ringStructureSheafCore B S hS p𝒴' h𝒴' τ hτ).obj) =
        (modulePresheafBaseChangeIso B S hS p𝒳 p𝒴' p𝒴 f g τ hτ
          h𝒳 h𝒴' h𝒴 hfc hgc).hom) :
    letI : (modulePullback.{u, v₁, w₁, max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₃, w₃}
            B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ).Additive :=
      { map_add := by intros; rfl }
    letI : (moduleSheafPushforward.{u, v₁, w₁, max (u + 1) v₂ w₂ a, v₃, w₃}
            B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ).Additive :=
      (moduleSheafAdjunction.{u, v₁, w₁, max (u + 1) v₂ w₂ a, v₃, w₃}
            B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ).right_adjoint_additive
    letI : (modulePullback.{u, v₂, w₂, max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₃, w₃}
            B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ).Additive :=
      { map_add := by intros; rfl }
    letI : (modulePullback.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
                max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₁, w₁}
            B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
            (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
              h𝒳 (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g)
              TwoFibreProductOver.fst_comp_eq τ hτ).Additive :=
      { map_add := by intros; rfl }
    letI : (modulePullback.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
                max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₂, w₂}
            B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
            (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
              h𝒴' (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g)
              TwoFibreProductOver.snd_comp_eq τ hτ).Additive :=
      { map_add := by intros; rfl }
    letI : (moduleSheafPushforward.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
                max v₃ a, v₂, w₂}
            B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
            (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
              h𝒴' (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g)
              TwoFibreProductOver.snd_comp_eq τ hτ).Additive :=
      (moduleSheafAdjunction.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
                max v₃ a, v₂, w₂}
            B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
            (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
              h𝒴' (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g)
              TwoFibreProductOver.snd_comp_eq τ hτ).right_adjoint_additive
    letI : PreservesFiniteLimits
        (modulePullback.{u, v₂, w₂, max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₃, w₃}
               B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ) :=
      preservesFiniteLimits_modulePullback'.{u, v₂, w₂, v₃, w₃, max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a}
        B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ
    letI := (moduleSheafAdjunction.{u, v₂, w₂, max (u + 1) v₁ w₁ a, v₃, w₃}
            B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ).leftAdjoint_preservesColimits
    letI : (modulePullback.{u, v₂, w₂, max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₃, w₃}
            B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ).PreservesHomology := inferInstance
    Nonempty
      ((moduleSheafPushforward.{u, v₁, w₁, max (u + 1) v₂ w₂ a, v₃, w₃}
          B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ).rightDerived n ⋙
          (modulePullback.{u, v₂, w₂, max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₃, w₃}
            B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ) ≅
        ((modulePullback.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
              max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₁, w₁}
          B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒳
          (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
            h𝒳 (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g)
            TwoFibreProductOver.fst_comp_eq τ hτ) ⋙
            (moduleSheafPushforward.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂,
                  max v₃ a, v₂, w₂}
              B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
              (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc)
                h𝒴' (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g)
                TwoFibreProductOver.snd_comp_eq τ hτ)).rightDerived n) := by
  obtain ⟨e⟩ := nonempty_moduleDirectImageBaseChangeIso B S hS p𝒳 p𝒴' p𝒴 f g τ hτ
    h𝒳 h𝒴' h𝒴 hfc hgc hlinear
  have := additive_moduleSheafPushforward'.{u, v₁, w₁, v₃, w₃, max (u + 1) v₂ w₂ a}
    B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ
  have := additive_modulePullback'.{u, v₂, w₂, v₃, w₃, max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a}
    B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ
  have := additive_modulePullback'.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂, v₁, w₁,
    max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g)
    p𝒳 (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒳
    (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.fst_comp_eq τ hτ
  have := additive_moduleSheafPushforward'.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂, v₂, w₂,
    max v₃ a} B S hS (TwoFibreProductOver.structureFunctor p𝒳 p𝒴' p𝒴 f g) p𝒴'
    (TwoFibreProductOver.isFiberedInGroupoids p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc) h𝒴'
    (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) TwoFibreProductOver.snd_comp_eq τ hτ
  have := preservesFiniteLimits_modulePullback'.{u, v₂, w₂, v₃, w₃,
    max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ
  have := (moduleSheafAdjunction.{u, v₂, w₂, max (u + 1) v₁ w₁ a, v₃, w₃}
    B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ).leftAdjoint_preservesColimits
  exact (Functor.rightDerivedCompIso
      (moduleSheafPushforward.{u, v₁, w₁, max (u + 1) v₂ w₂ a, v₃, w₃}
        B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ)
      (modulePullback.{u, v₂, w₂, max (u + 1) v₁ w₁ v₂ w₂ v₃ w₃ a, v₃, w₃}
        B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ) n).symm ≪≫
    Functor.rightDerivedIsoOfNatIso e n |> Nonempty.intro

end ModuleBaseChange

/-! ### The compatible-sections model and the right Kan extension -/

section SectionsRan

variable {𝒜 : Type va} [Category.{wa} 𝒜] {ℬ : Type vb} [Category.{wb} ℬ] (L : 𝒜 ⥤ ℬ)
  [∀ F : 𝒜 ⥤ AddCommGrpCat.{max va wa mo vb wb}, L.HasRightKanExtension F]

/-- The comparison of the compatible-sections model of the direct image of abelian presheaves
with the right Kan extension: both are right adjoint to restriction along `L`, so they agree by
uniqueness of right adjoints. This is the isomorphism underlying
`AlgebraicGeometry.Stack.ModuleFunctoriality.pushforward_iso`, named here on its own. -/
noncomputable def sectionsFunctorRanIso :
    sectionsFunctor.{va, wa, mo} L ≅ L.ran :=
  (sectionsAdjunction.{va, wa, mo} L).rightAdjointUniq
    (L.ranAdjunction AddCommGrpCat.{max va wa mo vb wb})

/-- **The legs of the Kan extension, read in the compatible-sections model.** Transporting the
leg at `(a, ψ)` of the limit cone that computes the right Kan extension through
`AlgebraicGeometry.Stack.sectionsFunctorRanIso` gives restriction along `ψ` followed by the
counit of the sections adjunction — that is, evaluation of a compatible family at `(a, ψ)`.

This is the formula that makes the module structure of the compatible-sections direct image of
Stacks 06WD comparable with the one `Stacks.SheafOfModules.ranSMul` puts on the Kan extension,
which is characterised on exactly these legs by `Stacks.SheafOfModules.ranSMul_π`. It is proved
from the two standard characterisations and nothing else: the counit of the right Kan extension
adjunction is `CategoryTheory.Functor.ranCounit`
(`CategoryTheory.Functor.ranAdjunction_counit`), and the comparison of two right adjoints
composes with the counit to give the other counit
(`CategoryTheory.Adjunction.rightAdjointUniq_hom_app_counit`). -/
lemma sectionsFunctorRanIso_hom_app_comp_ranπ
    (F : 𝒜 ⥤ AddCommGrpCat.{max va wa mo vb wb}) (V : ℬ) (j : StructuredArrow V L) :
    ((sectionsFunctorRanIso.{va, wa, vb, wb, mo} L).hom.app F).app V ≫
        Stacks.SheafOfModules.ranπ L F V j
      = (sectionsPresheaf.{va, wa, mo} L F).map j.hom ≫
        ((sectionsAdjunction.{va, wa, mo} L).counit.app F).app j.right := by
  have hcu := Adjunction.rightAdjointUniq_hom_app_counit
    (sectionsAdjunction.{va, wa, mo} L)
    (L.ranAdjunction AddCommGrpCat.{max va wa mo vb wb}) F
  rw [Functor.ranAdjunction_counit] at hcu
  have hnat := ((sectionsFunctorRanIso.{va, wa, vb, wb, mo} L).hom.app F).naturality j.hom
  dsimp only [Stacks.SheafOfModules.ranπ]
  rw [← Category.assoc, ← hnat, Category.assoc]
  exact congrArg (fun z => (sectionsPresheaf.{va, wa, mo} L F).map j.hom ≫ z)
    (congr_app hcu j.right)

end SectionsRan

end AlgebraicGeometry.Stack

end
