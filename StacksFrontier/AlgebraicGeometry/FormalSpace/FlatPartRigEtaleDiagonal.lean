module

public import Mathlib.CategoryTheory.Limits.Shapes.Diagonal
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FlatPartOverCdvr
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtale
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSmoothBaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveBaseChange

/-!
# The flat part of a formal algebraic space with rig-étale rig-surjective diagonal

Let `A` be a complete discrete valuation ring and let `X` be a locally Noetherian formal
algebraic space which is locally of finite type over `A`, with structure morphism
`p : X ⟶ Spf A`. Let `ι : X' ⟶ X` be the maximal flat closed formal subspace of **Stacks
0GD8**. **Stacks 0GD9** says that if the relative diagonal `X ⟶ X ×_{Spf A} X` is rig-étale
and rig-surjective then `X' = Spf A` or `X' = ∅`.

The two alternatives are read as `IsIso (ι ≫ p)` — the structure morphism of `X'` over `A` is
an isomorphism — and `Nonempty (IsInitial X')` — `X'` is an initial object of the category of
fppf sheaves, that is the empty formal algebraic space. `X'` itself is not constructed here but
quantified over: the statement is made for *every* closed immersion `ι : X' ⟶ X` with the
properties Stacks 0GD8 concludes, which is what "let `X' ⊂ X` be as in Lemma 0GD8" means and
is what composes with
`AlgebraicGeometry.FormalSpace.exists_flatPart_of_isLocallyNoetherian_of_isAdicComplete`.

The source argues as follows. The square with rows `X' ⟶ X' ×_{Spf A} X'` and
`X ⟶ X ×_{Spf A} X` is cartesian because `ι` is a monomorphism, so the diagonal of `X'` over
`A` inherits rig-étaleness and rig-surjectivity. For an affine chart `a : U ⟶ X'` the square
with rows `U ×_{X'} U ⟶ U ×_{Spf A} U` and `X' ⟶ X' ×_{Spf A} X'` is cartesian too, so
`U ×_{X'} U ⟶ U ×_{Spf A} U` is a rig-étale rig-surjective closed immersion; writing
`U = Spf B` and `U ×_{Spf A} U = Spf (B ⊗̂_A B)` by Stacks 0AN3, the target is flat over `A`,
so Stacks 0GD6 makes it an isomorphism. Hence the image of each chart of `X'` injects into
`Spf A`, and, the charts of Definition 0AIM covering `X'`, so does `X'`; flatness then forces
`X'` to be empty or all of `Spf A`, a nonzero `B` flat over `A` making `Spf B ⟶ Spf A` a
surjection of fppf sheaves.

## Main definitions

* `AlgebraicGeometry.FormalSpace.selfProductMap`: the comparison morphism
  `Z ×_V Z ⟶ W ×_V W` induced by a morphism `Z ⟶ W` over `V`.
* `AlgebraicGeometry.FormalSpace.RelativeDiagonalIsLocallyOfFiniteType`,
  `AlgebraicGeometry.FormalSpace.SelfProductOverBaseIsLocallyNoetherian`,
  `AlgebraicGeometry.FormalSpace.ClosedImmersionsAndChartsAreAdicAndLocallyOfFiniteType`,
  `AlgebraicGeometry.FormalSpace.SelfProductComparisonIsAdicAndLocallyOfFiniteType`,
  `AlgebraicGeometry.FormalSpace.RigEtaleStableUnderAdicBaseChange`,
  `AlgebraicGeometry.FormalSpace.ChartSelfProductInputs`,
  `AlgebraicGeometry.FormalSpace.ClosedImmersionRigEtaleRigSurjectiveIsIso` and
  `AlgebraicGeometry.FormalSpace.FlatPartIsBaseOrEmptyOfChartSelfProductsIso`: the inputs of
  Stacks 0GD9 that this library does not carry, each named once together with the Stacks tag
  it is.

## Main results

* `AlgebraicGeometry.FormalSpace.isPullback_diagonal_comp_of_mono`: the cartesian square the
  source asserts without reference — for a monomorphism `ι` the relative diagonal of `ι ≫ p`
  is the base change of the relative diagonal of `p` along `selfProductMap ι p`.
* `AlgebraicGeometry.FormalSpace.isRigEtale_and_isRigSurjective_diagonal_of_mono`: the descent
  of rig-étaleness and rig-surjectivity of the diagonal to a closed formal subspace.
* `AlgebraicGeometry.FormalSpace.isIso_mapDesc_of_isRigEtale_of_isRigSurjective_diagonal`: for
  every Noetherian affine chart `a : U ⟶ X'` the comparison
  `U ×_{X'} U ⟶ U ×_{Spf A} U` is an isomorphism.

## Implementation notes

"`X` is flat over `A`" and "`X` is locally of finite type over `A`" are read, as the source
does, as flatness and local finite type of the structure morphism `X ⟶ Spf A`, that is
`AlgebraicGeometry.FormalSpace.IsFlat` (Definition 0GCC) and
`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType` (Definition 0AM4). The base is
`formalSpectrum D` for a quotient system `D` presenting `A` over `S`, which is how this library
spells `Spf A`, and the relative diagonal is `CategoryTheory.Limits.pullback.diagonal`, as in
`AlgebraicGeometry.FormalSpace.IsFormalModification`.

Completeness of `A` plays no role in the argument below; it is the standing hypothesis of
Section 0GD7 and is carried for faithfulness, as it is in
`AlgebraicGeometry.FormalSpace.exists_flatPart_of_isLocallyNoetherian_of_isAdicComplete`.

### The inputs this library does not carry

The source's proof is an assembly of results of which this library has exactly one, Stacks
0AQS, `AlgebraicGeometry.FormalSpace.IsRigSurjective.of_isPullback`. The others are explicit
hypotheses, and none of them mentions the conclusion.

* `h0AN2` is the locally-of-finite-type assertion of **Stacks 0AN2**, which the source's
  parenthetical aside invokes to make the hypothesis on the diagonal meaningful and which the
  base change step consumes. The library carries that assertion for a morphism whose source is
  an arbitrary formal algebraic space
  (`…relative_locallyOfFiniteType_pullback_diagonal_of_isFormalAlgebraicSpace`, in
  `StacksFrontier.AlgebraicGeometry.FormalSpace.DiagonalRepresentable`, which this module does not
  import); it is carried as a hypothesis here rather than imported.
* `h0AQ7` is the other half of that aside: a self-product over `Spf A` of a locally Noetherian
  formal algebraic space locally of finite type over `A` is locally Noetherian, which is
  **Stacks 0AQ5** with **Stacks 0AQ8**, the library's 0AQ7 being the comparison of the four
  conditions of that tag rather than this consequence.
* `hfin` and `hcmp` are the finiteness and adicness of the morphisms the base changes are taken
  along: a closed immersion (**Stacks 0ANP**) and a representable étale chart are locally of
  finite type (**Stacks 0AM4**) and adic (**Stacks 0AQ3**), and so is the comparison morphism
  `selfProductMap` they induce on self-products, being a composition of two base changes of
  them (**Stacks 0AQ4**, **Stacks 0AQ5**). The library derives none of these from
  `IsClosedImmersion` or `IsRepresentableEtale`.
* `h0GD1` is the rig-étale half of the base change step. The source attributes both halves to
  Stacks 0AQS, but 0AQS asserts only the rig-surjective one; the rig-étale one is **Stacks
  0GD1**, which the library carries in
  `AlgebraicGeometry.FormalSpace.isRigEtale_pullback_snd_of_isAdicMorphism` only for the chosen
  fibre product and only granting four further open inputs — the locality of the
  cohomology-annihilation half of rig-étaleness, the covering of a fibre product by fibre
  products of charts, the implication (3) ⟹ (1) of Stacks 0ANG, and invariance under
  isomorphism of targets. The adicness hypothesis of Stacks 0GD1 is kept, so the input is an
  instance of that tag rather than a stronger claim.
* `hchart` collects what the source says about a chart of `X'`: that `U ×_{X'} U` and
  `U ×_{Spf A} U` are locally Noetherian (**Stacks 0AJ3** with **Stacks 0AQ8**), that
  `U ×_{Spf A} U` is flat over `A` — it is `Spf (B ⊗̂_A B)` by **Stacks 0AN3** and
  `B ⊗̂_A B` is the `π`-adic completion of the flat `A`-algebra `B ⊗_A B` — and that
  `U ×_{X'} U ⟶ U ×_{Spf A} U` is a closed immersion, which the source asserts without
  argument and which needs the monomorphism assertion of Stacks 0AN2 together with **Stacks
  0GHZ**, carried in this library only with the reduction of the target as data and the
  conclusion of Stacks 07VT granted. Stacks 0AN3 is in this library only for the fibre product
  of affine formal algebraic spaces over a separated base and says nothing about flatness or
  about the completed tensor product.
* `h0GD6` is **Stacks 0GD6**, absent from this library: a closed immersion of locally
  Noetherian formal algebraic spaces which is rig-étale and rig-surjective and whose target is
  flat over `A` is an isomorphism. The tag itself gives the equivalence with the condition that
  the closed immersion comes from a surjection `B ⟶ A` in `WAdm^{Noeth}` whose kernel `J`
  satisfies `IJ = 0` for an ideal of definition `I`; the passage from there to `J = 0` is the
  flatness of the target over `A`, since `I` contains a power of the uniformizer and a flat
  `A`-module has no torsion. Both steps are folded into this one hypothesis.
* `hlast` is the final two paragraphs of the source's proof: a locally Noetherian formal
  algebraic space flat over `A`, all of whose Noetherian affine charts `a` have
  `U ×_{X'} U ⟶ U ×_{Spf A} U` an isomorphism, is either isomorphic to `Spf A` over `A` or
  empty. It is not a tag. It needs the sheaf image of a chart, the fact that a disjoint union
  of two affine formal algebraic spaces is again one — which is why the hypothesis quantifies
  over *all* charts and not only over the members of one atlas, the source applying the
  argument to `Uᵢ ⨿ Uⱼ` as well — the fppf-surjectivity of `Spf B ⟶ Spf A` for a nonzero `B`
  flat over `A`, and the fact that a morphism of fppf sheaves which is both a monomorphism and
  a surjection is an isomorphism. The library carries none of the four.

What the proof does with them is the assembly: it produces the cartesian square for the
diagonal of `ι ≫ p` out of `ι` being a monomorphism, descends rig-étaleness and
rig-surjectivity along it, repeats the base change at each Noetherian affine chart of `X'` with
the cartesian square Mathlib's `CategoryTheory.Limits.pullback_map_diagonal_isPullback`
supplies, applies Stacks 0GD6 to the resulting closed immersion, and hands the family of
isomorphisms so obtained to the last step.

A monomorphism hypothesis on `ι` is carried: a closed immersion of formal algebraic spaces is
a monomorphism of the underlying fppf sheaves, which is **Stacks 0ANP** read through **Stacks
0AQB**, and the library derives `CategoryTheory.Mono` from
`AlgebraicGeometry.FormalSpace.IsClosedImmersion` nowhere — the same gap the `hfac` input of
Stacks 0GD8 documents.

## References

* [Stacks Project, Tag 0AIM](https://stacks.math.columbia.edu/tag/0AIM)
* [Stacks Project, Tag 0AJ3](https://stacks.math.columbia.edu/tag/0AJ3)
* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
* [Stacks Project, Tag 0AN2](https://stacks.math.columbia.edu/tag/0AN2)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0ANG](https://stacks.math.columbia.edu/tag/0ANG)
* [Stacks Project, Tag 0ANP](https://stacks.math.columbia.edu/tag/0ANP)
* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
* [Stacks Project, Tag 0AQ4](https://stacks.math.columbia.edu/tag/0AQ4)
* [Stacks Project, Tag 0AQ5](https://stacks.math.columbia.edu/tag/0AQ5)
* [Stacks Project, Tag 0AQ7](https://stacks.math.columbia.edu/tag/0AQ7)
* [Stacks Project, Tag 0AQ8](https://stacks.math.columbia.edu/tag/0AQ8)
* [Stacks Project, Tag 0AQB](https://stacks.math.columbia.edu/tag/0AQB)
* [Stacks Project, Tag 0AQM](https://stacks.math.columbia.edu/tag/0AQM)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
* [Stacks Project, Tag 07VT](https://stacks.math.columbia.edu/tag/07VT)
* [Stacks Project, Tag 0GCC](https://stacks.math.columbia.edu/tag/0GCC)
* [Stacks Project, Tag 0GD1](https://stacks.math.columbia.edu/tag/0GD1)
* [Stacks Project, Tag 0GD6](https://stacks.math.columbia.edu/tag/0GD6)
* [Stacks Project, Tag 0GD7](https://stacks.math.columbia.edu/tag/0GD7)
* [Stacks Project, Tag 0GD8](https://stacks.math.columbia.edu/tag/0GD8)
* [Stacks Project, Tag 0GD9](https://stacks.math.columbia.edu/tag/0GD9)
* [Stacks Project, Tag 0GHZ](https://stacks.math.columbia.edu/tag/0GHZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-! ### The cartesian square of relative diagonals -/

section Categorical

variable {C : Type*} [Category* C] [HasPullbacks C]

/-- The comparison morphism `Z ×_V Z ⟶ W ×_V W` on self-products over `V` induced by a
morphism `f : Z ⟶ W` over `V`. -/
abbrev selfProductMap {Z W V : C} (f : Z ⟶ W) (i : W ⟶ V) :
    pullback (f ≫ i) (f ≫ i) ⟶ pullback i i :=
  pullback.map (f ≫ i) (f ≫ i) i i f f (𝟙 V) (Category.comp_id _) (Category.comp_id _)

/-- For a monomorphism `ι : X' ⟶ X` and a morphism `p : X ⟶ Y` the relative diagonal of
`ι ≫ p` is the base change of the relative diagonal of `p` along `selfProductMap ι p`. This is
the square the proof of Stacks 0GD9 asserts without reference. -/
theorem isPullback_diagonal_comp_of_mono {X' X Y : C} (ι : X' ⟶ X) (p : X ⟶ Y) [Mono ι] :
    IsPullback ι (pullback.diagonal (ι ≫ p)) (pullback.diagonal p) (selfProductMap ι p) := by
  have hfst : selfProductMap ι p ≫ pullback.fst p p =
      pullback.fst (ι ≫ p) (ι ≫ p) ≫ ι := pullback.lift_fst _ _ _
  have hsnd : selfProductMap ι p ≫ pullback.snd p p =
      pullback.snd (ι ≫ p) (ι ≫ p) ≫ ι := pullback.lift_snd _ _ _
  have hcomm : ι ≫ pullback.diagonal p = pullback.diagonal (ι ≫ p) ≫ selfProductMap ι p :=
    pullback.hom_ext (by simp [hfst]) (by simp [hsnd])
  refine IsPullback.of_isLimit' ⟨hcomm⟩ (PullbackCone.IsLimit.mk hcomm
    (fun s ↦ s.snd ≫ pullback.fst (ι ≫ p) (ι ≫ p)) (fun s ↦ ?_) (fun s ↦ ?_) ?_)
  · have h := congrArg (fun k ↦ k ≫ pullback.fst p p) s.condition
    simp only [Category.assoc, hfst] at h
    simpa using h.symm
  · have h₁ := congrArg (fun k ↦ k ≫ pullback.fst p p) s.condition
    have h₂ := congrArg (fun k ↦ k ≫ pullback.snd p p) s.condition
    simp only [Category.assoc, hfst, hsnd] at h₁ h₂
    have hproj : s.snd ≫ pullback.fst (ι ≫ p) (ι ≫ p) =
        s.snd ≫ pullback.snd (ι ≫ p) (ι ≫ p) := by
      refine (cancel_mono ι).mp ?_
      rw [Category.assoc, Category.assoc, ← h₁, ← h₂]
      simp
    exact pullback.hom_ext (by simp) (by simp [hproj])
  · intro s m _ hm
    rw [← hm]
    simp

end Categorical

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {A : Type u} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  (D : QuotientSystem B S hS A)

/-! ### The inputs this library does not carry -/

/-- The locally-of-finite-type assertion of **Stacks 0AN2**: the relative diagonal of a
morphism of fppf sheaves whose source is a formal algebraic space over `S` is locally of finite
type. The library carries it only when the source is an affine formal algebraic space. -/
abbrev RelativeDiagonalIsLocallyOfFiniteType : Prop :=
  ∀ {Z W : FppfSheaf B S hS} (f : Z ⟶ W), IsFormalAlgebraicSpace B S hS Z →
    IsLocallyOfFiniteType B S hS (pullback.diagonal f)

/-- **Stacks 0AQ5** with **Stacks 0AQ8**: the self-product over `Spf A` of a locally Noetherian
formal algebraic space which is locally of finite type over `A` is locally Noetherian. This is
the second half of the parenthetical aside opening the proof of Stacks 0GD9. -/
abbrev SelfProductOverBaseIsLocallyNoetherian : Prop :=
  ∀ {Z : FppfSheaf B S hS} (q : Z ⟶ formalSpectrum D), IsLocallyNoetherian B S hS Z →
    IsLocallyOfFiniteType B S hS q → IsLocallyNoetherian B S hS (pullback q q)

/-- A closed immersion (**Stacks 0ANP**) and a representable étale chart are locally of finite
type (**Stacks 0AM4**) and adic (**Stacks 0AQ3**). These are the two kinds of morphism the
base changes in the proof of Stacks 0GD9 are taken along. -/
abbrev ClosedImmersionsAndChartsAreAdicAndLocallyOfFiniteType : Prop :=
  ∀ {Z W : FppfSheaf B S hS} (f : Z ⟶ W),
    IsClosedImmersion B S hS f ∨ IsRepresentableEtale B S hS f →
    IsLocallyOfFiniteType B S hS f ∧ IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS f

/-- The comparison morphism on self-products induced by a closed immersion or by a representable
étale chart is locally of finite type and adic, being a composition of two base changes of that
morphism: **Stacks 0AQ4** and **Stacks 0AQ5** for local finite type and **Stacks 0AQ3** for
adicness. -/
abbrev SelfProductComparisonIsAdicAndLocallyOfFiniteType : Prop :=
  ∀ {Z W V : FppfSheaf B S hS} (f : Z ⟶ W) (i : W ⟶ V),
    IsClosedImmersion B S hS f ∨ IsRepresentableEtale B S hS f →
    IsLocallyOfFiniteType B S hS (selfProductMap f i) ∧
      IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS (selfProductMap f i)

/-- **Stacks 0GD1** for an arbitrary cartesian square: the base change of a rig-étale morphism
of locally Noetherian formal algebraic spaces over `S` along an adic morphism is rig-étale.
The library carries this only for the chosen fibre product and only granting four further open
inputs. -/
abbrev RigEtaleStableUnderAdicBaseChange : Prop :=
  ∀ {W X Y Z : FppfSheaf B S hS} {q : W ⟶ Z} {r : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y},
    IsPullback q r g f → IsLocallyNoetherian B S hS X → IsLocallyNoetherian B S hS Y →
      IsLocallyNoetherian B S hS Z → IsRigEtale B S hS f →
        IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS g →
      IsRigEtale B S hS q

/-- What the proof of Stacks 0GD9 says about a Noetherian affine chart `a : U ⟶ X'` of a formal
algebraic space over `A`: the two self-products `U ×_{X'} U` and `U ×_{Spf A} U` are locally
Noetherian (**Stacks 0AJ3** with **Stacks 0AQ8**), the second is flat over `A` — it is
`Spf (B ⊗̂_A B)` by **Stacks 0AN3** and `B ⊗̂_A B` is the completion of the flat `A`-algebra
`B ⊗_A B` — and the comparison `U ×_{X'} U ⟶ U ×_{Spf A} U` is a closed immersion, which needs
the monomorphism assertion of **Stacks 0AN2** with **Stacks 0GHZ**. -/
abbrev ChartSelfProductInputs {X' : FppfSheaf B S hS} (p' : X' ⟶ formalSpectrum D) : Prop :=
  ∀ (U : FppfSheaf B S hS) (a : U ⟶ X'), IsAffineFormalAlgebraicSpace B S hS U →
    IsNoetherian B S hS U → IsRepresentableEtale B S hS a →
    IsLocallyNoetherian B S hS (pullback a a) ∧
      IsLocallyNoetherian B S hS (pullback (a ≫ p') (a ≫ p')) ∧
        IsFlat B S hS (pullback.fst (a ≫ p') (a ≫ p') ≫ a ≫ p') ∧
          IsClosedImmersion B S hS (pullback.mapDesc a a p')

/-- **Stacks 0GD6** in the shape its use in Stacks 0GD9 needs, together with the flatness
argument that use rests on: a closed immersion of locally Noetherian formal algebraic spaces
over `S` which is rig-étale and rig-surjective and whose target is flat over `A` is an
isomorphism. The tag identifies such a closed immersion with one coming from a surjection whose
kernel `J` satisfies `IJ = 0` for an ideal of definition `I`, and flatness of the target over
`A` then gives `J = 0`, an ideal of definition containing a power of the uniformizer and a flat
`A`-module having no torsion. -/
abbrev ClosedImmersionRigEtaleRigSurjectiveIsIso : Prop :=
  ∀ {Z W : FppfSheaf B S hS} (g : Z ⟶ W) (q : W ⟶ formalSpectrum D),
    IsLocallyNoetherian B S hS Z → IsLocallyNoetherian B S hS W →
      IsClosedImmersion B S hS g → IsRigEtale B S hS g → IsRigSurjective B S hS g →
      IsFlat B S hS q → IsIso g

/-- The last two paragraphs of the proof of Stacks 0GD9: a locally Noetherian formal algebraic
space over `S` which is flat over `A` and every Noetherian affine chart `a : U ⟶ X'` of which
has `U ×_{X'} U ⟶ U ×_{Spf A} U` an isomorphism is either isomorphic to `Spf A` over `A` or
empty. The quantification is over all such charts, not over the members of one atlas, because
the source applies the argument to the disjoint union of two members as well. -/
abbrev FlatPartIsBaseOrEmptyOfChartSelfProductsIso {X' : FppfSheaf B S hS}
    (p' : X' ⟶ formalSpectrum D) : Prop :=
  IsLocallyNoetherian B S hS X' → IsFlat B S hS p' →
    (∀ (U : FppfSheaf B S hS) (a : U ⟶ X'), IsAffineFormalAlgebraicSpace B S hS U →
        IsNoetherian B S hS U → IsRepresentableEtale B S hS a →
        IsIso (pullback.mapDesc a a p')) →
      IsIso p' ∨ Nonempty (IsInitial X')

/-! ### The descent of the diagonal along a closed immersion -/

/-- If a square with right edge the diagonal of `p` is cartesian and its left-bottom edge `g` is
adic and locally of finite type, then its top edge is rig-étale and rig-surjective as soon as
the diagonal of `p` is. -/
private theorem isRigEtale_and_isRigSurjective_of_isPullback_diagonal
    {W X Z V : FppfSheaf B S hS} {p : X ⟶ V} {q : W ⟶ Z} {r : W ⟶ X} {g : Z ⟶ pullback p p}
    (sq : IsPullback q r g (pullback.diagonal p)) (hX : IsLocallyNoetherian B S hS X)
    (hY : IsLocallyNoetherian B S hS (pullback p p)) (hZ : IsLocallyNoetherian B S hS Z)
    (h0AN2 : RelativeDiagonalIsLocallyOfFiniteType B S hS)
    (h0GD1 : RigEtaleStableUnderAdicBaseChange B S hS)
    (hg : IsLocallyOfFiniteType B S hS g ∧ IsAdicOnEveryAffineEtaleDiagramNoetherian B S hS g)
    (hdiagEtale : IsRigEtale B S hS (pullback.diagonal p))
    (hdiagSurj : IsRigSurjective B S hS (pullback.diagonal p)) :
    IsRigEtale B S hS q ∧ IsRigSurjective B S hS q :=
  ⟨h0GD1 sq hX hY hZ hdiagEtale hg.2,
    (IsRigSurjective.of_isPullback B S hS sq (h0AN2 p hX.1) hg.1 hdiagSurj).2⟩

omit [IsTopologicalRing A] in
/-- The diagonal of a closed formal subspace over `A` inherits rig-étaleness and
rig-surjectivity from the diagonal of the ambient space: the diagonal of `ι ≫ p` is a base
change of the diagonal of `p` along `selfProductMap ι p`, which is adic and locally of finite
type, so Stacks 0AQS gives rig-surjectivity and `h0GD1` gives rig-étaleness. -/
theorem isRigEtale_and_isRigSurjective_diagonal_of_mono
    {X X' : FppfSheaf B S hS} (ι : X' ⟶ X) (p : X ⟶ formalSpectrum D) (hιmono : Mono ι)
    (hιclosed : IsClosedImmersion B S hS ι) (hX : IsLocallyNoetherian B S hS X)
    (hX' : IsLocallyNoetherian B S hS X') (hp : IsLocallyOfFiniteType B S hS p)
    (h0AN2 : RelativeDiagonalIsLocallyOfFiniteType B S hS)
    (h0AQ7 : SelfProductOverBaseIsLocallyNoetherian B S hS D)
    (hfin : ClosedImmersionsAndChartsAreAdicAndLocallyOfFiniteType B S hS)
    (hcmp : SelfProductComparisonIsAdicAndLocallyOfFiniteType B S hS)
    (h0GD1 : RigEtaleStableUnderAdicBaseChange B S hS)
    (hdiagEtale : IsRigEtale B S hS (pullback.diagonal p))
    (hdiagSurj : IsRigSurjective B S hS (pullback.diagonal p)) :
    IsRigEtale B S hS (pullback.diagonal (ι ≫ p)) ∧
      IsRigSurjective B S hS (pullback.diagonal (ι ≫ p)) := by
  have := hιmono
  exact isRigEtale_and_isRigSurjective_of_isPullback_diagonal B S hS
    (isPullback_diagonal_comp_of_mono ι p).flip hX (h0AQ7 p hX hp)
    (h0AQ7 (ι ≫ p) hX' (IsLocallyOfFiniteType.comp B S hS ι p (hfin ι (Or.inl hιclosed)).1 hp))
    h0AN2 h0GD1 (hcmp ι p (Or.inl hιclosed)) hdiagEtale hdiagSurj

/-! ### The charts of a space with rig-étale rig-surjective diagonal -/

omit [IsTopologicalRing A] in
/-- For every Noetherian affine chart `a : U ⟶ X'` of a locally Noetherian formal algebraic
space `X'` which is locally of finite type over `A` and whose relative diagonal over `A` is
rig-étale and rig-surjective, the comparison `U ×_{X'} U ⟶ U ×_{Spf A} U` is an isomorphism: it
is a base change of that diagonal, hence a rig-étale rig-surjective closed immersion into a
self-product flat over `A`, so Stacks 0GD6 applies. -/
theorem isIso_mapDesc_of_isRigEtale_of_isRigSurjective_diagonal
    {X' : FppfSheaf B S hS} (q : X' ⟶ formalSpectrum D)
    (hX' : IsLocallyNoetherian B S hS X') (hq : IsLocallyOfFiniteType B S hS q)
    (h0AN2 : RelativeDiagonalIsLocallyOfFiniteType B S hS)
    (h0AQ7 : SelfProductOverBaseIsLocallyNoetherian B S hS D)
    (hcmp : SelfProductComparisonIsAdicAndLocallyOfFiniteType B S hS)
    (h0GD1 : RigEtaleStableUnderAdicBaseChange B S hS)
    (hchart : ChartSelfProductInputs B S hS D q)
    (h0GD6 : ClosedImmersionRigEtaleRigSurjectiveIsIso B S hS D)
    (hdiagEtale : IsRigEtale B S hS (pullback.diagonal q))
    (hdiagSurj : IsRigSurjective B S hS (pullback.diagonal q))
    (U : FppfSheaf B S hS) (a : U ⟶ X') (hU : IsAffineFormalAlgebraicSpace B S hS U)
    (hUnoeth : IsNoetherian B S hS U) (ha : IsRepresentableEtale B S hS a) :
    IsIso (pullback.mapDesc a a q) := by
  obtain ⟨hWnoeth, hPnoeth, hPflat, hWclosed⟩ := hchart U a hU hUnoeth ha
  obtain ⟨hEtale, hSurj⟩ := isRigEtale_and_isRigSurjective_of_isPullback_diagonal B S hS
    (pullback_map_diagonal_isPullback a a q).flip hX' (h0AQ7 q hX' hq) hPnoeth h0AN2 h0GD1
    (hcmp a q (Or.inr ha)) hdiagEtale hdiagSurj
  exact h0GD6 (pullback.mapDesc a a q) (pullback.fst (a ≫ q) (a ≫ q) ≫ a ≫ q) hWnoeth hPnoeth
    hWclosed hEtale hSurj hPflat

end AlgebraicGeometry.FormalSpace

end
