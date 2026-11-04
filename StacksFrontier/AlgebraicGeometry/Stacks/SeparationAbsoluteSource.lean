module

public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationComposition
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBase

/-!
# Absolute separation passes to the source of a 1-morphism (Stacks 050L, parts (5)-(8))

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over a scheme `S` contained in a big fppf
site `B`. **Stacks 050L** has eight parts. Parts (1)-(4) say that each of the four separation
axioms of **Stacks 04YW**, read *relative to the base* `S` in the sense of **Stacks 050D** parts
(1)-(4), passes from `𝒴` to `𝒳` as soon as `f` has it; parts (1), (2) and (4) are in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBaseSource` and part (3) is below, beside the
part (7) that consumes it. Parts (5)-(8) are the same four
statements for the *absolute* axioms of **Stacks 050D** parts (5)-(8) — `𝒳` is DM, quasi-DM,
separated, quasi-separated when it is so over `Spec(ℤ)`, viewing `𝒳` as an algebraic stack over
`Spec(ℤ)` by **Stacks 04X6**. Those four are what this file supplies.

The absolute axioms are *not* the relative ones: they are conditions on a different structure
morphism, the one to `Spec(ℤ)`. So parts (5)-(8) are four theorems of their own, about
`AlgebraicGeometry.Stack.IsDMAbs` and its three companions, and not a reading of parts (1)-(4).

The proof is the source's: view `𝒳`, `𝒴` and `f` over `Spec(ℤ)` and apply **Stacks 050K** — the
same argument parts (1)-(4) run, read at the base `Spec(ℤ)`. Each of the four is one application
of the corresponding composition lemma of Stacks 050K
(`AlgebraicGeometry.Stack.AlgebraicStacks.isDM_comp` and its three siblings) to the factorization
of the structure morphism. Part (7) runs it through part (3) below, which is that same application
at a general base; parts (5), (6) and (8) invoke the composition lemma directly. Two things make
it work.

* The structure morphism over `Spec(ℤ)` of `𝒳` viewed is `f` viewed, followed by the structure
  morphism over `Spec(ℤ)` of `𝒴` viewed. This is
  `AlgebraicGeometry.Stack.comp_structureMorphism`, which is stated for an arbitrary base and so
  applies at the terminal base verbatim. It is an equality of 1-morphisms on the nose, but it is
  *not* `rfl`: that lemma is proved by extensionality in three layers, and the terminal base
  changes nothing about that.
* The Stacks 04YW axiom for `f` has to transfer along **Stacks 04X6**, from the base `S` to the
  base `Spec(ℤ)`. For DM and quasi-DM it does, and that is
  `AlgebraicGeometry.Stack.isDM_changeBaseHomAlgebraicStacks` and
  `AlgebraicGeometry.Stack.isQuasiDM_changeBaseHomAlgebraicStacks` below. For separated and
  quasi-separated it is **not available**, and the hypothesis of parts (7) and (8) is therefore
  the axiom for `f` read over `Spec(ℤ)` — see the implementation notes.

## Main definitions

* `AlgebraicGeometry.Stack.unrelocalizeBaseFunctor`: the inverse of
  `AlgebraicGeometry.Stack.relocalizeBaseFunctor`, identifying the 2-fibre product
  `𝒳 ×_{f, 𝒴, f} 𝒳` formed over `S'` after Construction A with the one formed over `S` and then
  viewed.
* `AlgebraicGeometry.Stack.changeBaseHomAlgebraicStacks`: **Stacks 04X6** on a 1-morphism — a
  1-morphism of algebraic stacks over `S`, viewed as a 1-morphism of algebraic stacks over `S'`.
* `AlgebraicGeometry.Stack.viewOverIntHom`: the same at the terminal base, which is the viewing
  that **Stacks 050D** parts (5)-(8) and hence Stacks 050L parts (5)-(8) are stated in terms of.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_changeBase`:
  representability by algebraic spaces of a relative diagonal is carried along Construction A.
* `AlgebraicGeometry.Stack.hasEtaleChartProperty_relativeDiagonal_changeBase`: a condition of
  Stacks 04XB at an étale-chart property is carried along Construction A. This is the converse of
  `AlgebraicGeometry.Stack.hasEtaleChartProperty_relativeDiagonal_of_changeBase`.
* `AlgebraicGeometry.Stack.isDM_changeBaseHomAlgebraicStacks` and
  `AlgebraicGeometry.Stack.isQuasiDM_changeBaseHomAlgebraicStacks`: the DM and quasi-DM axioms of
  **Stacks 04YW** are unchanged by Construction A.
* `AlgebraicGeometry.Stack.isSeparatedOver_of_isSeparated`: **Stacks 050L**, part (3), the
  over-the-base statement its part (7) consumes.
* `AlgebraicGeometry.Stack.isDMAbs_of_isDM`: **Stacks 050L**, part (5).
* `AlgebraicGeometry.Stack.isQuasiDMAbs_of_isQuasiDM`: **Stacks 050L**, part (6).
* `AlgebraicGeometry.Stack.isSeparatedAbs_of_isSeparated`: **Stacks 050L**, part (7).
* `AlgebraicGeometry.Stack.isQuasiSeparatedAbs_of_isQuasiSeparated`: **Stacks 050L**, part (8).

## Implementation notes

**The transfer machinery is `StacksFrontier.AlgebraicGeometry.Stacks.SeparationChangeOfBase`, and
this file adds the direction that module leaves open.** That module supplies
`AlgebraicGeometry.Stack.HasEtaleChartProperty` — the condition of **Stacks 04XB** at a property
of morphisms of schemes read on étale charts (**Stacks 03MJ**), written longhand so that no
instance on the property is needed — together with
`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_changeBaseHom_iff`, which is the *iff* for a
1-morphism's own Stacks 04XB condition, and
`AlgebraicGeometry.Stack.relativeDiagonalBasedFunctor_changeBase`, which says on the nose that
`Δ_{changeBase f}` is `changeBase (Δ_f)` followed by
`AlgebraicGeometry.Stack.relocalizeBaseFunctor`. Its own diagonal result,
`AlgebraicGeometry.Stack.hasEtaleChartProperty_relativeDiagonal_of_changeBase`, moves the
condition *from* `Δ_{changeBase f}` *to* `Δ_f`, which is what the clauses of **Stacks 050N**
consume; its implementation notes record the opposite direction as not proved, because
**Stacks 0457** (`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`) consumes an
equivalence of the *targets* pointing at the one whose condition is known, and in this direction
that equivalence is `CategoryTheory.TwoFibreProductOver.unrelocalizeBase` read over the site,
which is strictly over the site only up to the `hx` field of an object of the relocalized
2-fibre product. `AlgebraicGeometry.Stack.unrelocalizeBaseFunctor` supplies exactly that: its
compatibility with the two structure functors follows from
`CategoryTheory.TwoFibreProductOver.unrelocalizeBase_comp_relocalizeBase` and the fact that
`relocalizeBase` *is* strictly over the site, so the identification need not be unfolded at all.
With it, `AlgebraicGeometry.Stack.hasEtaleChartProperty_relativeDiagonal_changeBase` is the same
two steps run the other way.

**Why the relative diagonal transfers when the absolute one does not.** The implementation notes
of `StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBase` and of
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute` both record this comparison as
unavailable. Those notes are true of the *absolute* diagonal, whose target is formed over the
stack represented by the base and so acquires, over the larger base, the extra objects of pairs
lying over a common `S'`-scheme by two different morphisms to `S`. The *relative* diagonal of
`f : 𝒳 ⟶ 𝒴` has target formed over `changeBase 𝒴`, and the comparison isomorphism of an object
there lies over an identity of the site of `S'`, which forces the two morphisms to `S` to agree.
That is the content of `CategoryTheory.TwoFibreProductOver.relocalizeBaseEquivalence`, and it is
why the relative statement is available where the absolute one is not.

**Only DM and quasi-DM transfer, and the obstruction for the other two is precise.** The transfer
is available at an étale-chart property, because the one thing it needs of the property is
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff`: the
every-étale-chart condition of Stacks 03MJ for the structural morphism of a lower-shriek
extension does not depend on the base. The DM axiom is that condition at unramifiedness
(**Stacks 03ZH**, part (1)) and the quasi-DM axiom at local quasi-finiteness (**Stacks 03XJ**,
part (1)), so both go through. The separated and quasi-separated axioms are the Stacks 04XB
condition at properness (**Stacks 03ZM**) and at quasi-compactness (**Stacks 03HE**) together
with quasi-separatedness (**Stacks 03HL**, part (3)), and none of those three is an
every-étale-chart condition: each quantifies over *all* algebraic spaces over the base mapping to
the target, a quantifier the change of base enlarges. What is missing is the analogue of
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff` at
`AlgebraicGeometry.Space.IsProper`, `AlgebraicGeometry.Space.IsQuasiCompact` and
`AlgebraicGeometry.Space.IsQuasiSeparated`; the library has none of the three.

So parts (7) and (8) take as hypothesis the Stacks 04YW axiom for `f` **read over `Spec(ℤ)`** —
the base at which the absolute statement lives, and the one the source's own proof instructs one
to pass to — and their attribute strings say so. Parts (5) and (6) take the axiom over `S`, which
by the transfer is the weaker hypothesis of the two and hence the stronger theorem. When the
three missing space-level statements land, parts (7) and (8) can be restated with the axiom over
`S` with no change to their proofs beyond composing with the transfer.

**Why a separate module.** Parts (1), (2) and (4), in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationOverBaseSource`, need only **Stacks 050K**; parts
(5)-(8) additionally need **Stacks 04X6** and so the import closure of
`StacksFrontier.AlgebraicGeometry.Stacks.ChangeOfBaseAlgebraicStack`. This is the same build-cost
decision that put Stacks 050D parts (5)-(8) in
`StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute` rather than beside parts (1)-(4); see
the implementation notes there.

## References

* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04X6](https://stacks.math.columbia.edu/tag/04X6)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050K](https://stacks.math.columbia.edu/tag/050K)
* [Stacks Project, Tag 050L](https://stacks.math.columbia.edu/tag/050L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u w w'

section ChangeOfBase

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **The 2-fibre product `𝒳 ×_{f, 𝒴, f} 𝒳` formed over `S'` after Construction A is the one
formed over `S` and then viewed.** This is
`CategoryTheory.TwoFibreProductOver.unrelocalizeBase` read as a 1-morphism of categories over the
big fppf site of `S'`, and so the inverse of `AlgebraicGeometry.Stack.relocalizeBaseFunctor`.

It is strictly over the site, but not on the nose as `relocalizeBaseFunctor` is: the base object
of the image is the one the `𝒳`-component lies over, which agrees with the given base object only
through the identification recorded in the `hx` field. No unfolding of that identification is
needed, because `relocalizeBase` *is* strictly over the site and the two comparison functors are
inverse as an equality of functors
(`CategoryTheory.TwoFibreProductOver.unrelocalizeBase_comp_relocalizeBase`). -/
def unrelocalizeBaseFunctor
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (f : 𝒳 ⟶ 𝒴) :
    (twoFibreProduct B S' hS' (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseHom B S S' hS hS' g f).hom
        (changeBaseHom B S S' hS hS' g f).hom).val ⥤ᵇ
      (changeBaseFiberedInGroupoids B S S' hS hS' g
        (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom)).val where
  toFunctor := TwoFibreProductOver.unrelocalizeBase g f.hom.w f.hom.w
  w := by
    have key := TwoFibreProductOver.unrelocalizeBase_comp_relocalizeBase g
      (F := f.hom.toFunctor) (G := f.hom.toFunctor) f.hom.w f.hom.w
    have h2 : TwoFibreProductOver.unrelocalizeBase g
          (F := f.hom.toFunctor) (G := f.hom.toFunctor) f.hom.w f.hom.w ⋙
        (TwoFibreProductOver.relocalizeBase g ⋙
          TwoFibreProductOver.structureFunctor (𝒳.val.p ⋙ Over.map g) (𝒳.val.p ⋙ Over.map g)
            (𝒴.val.p ⋙ Over.map g) f.hom.toFunctor f.hom.toFunctor) =
        TwoFibreProductOver.structureFunctor (𝒳.val.p ⋙ Over.map g) (𝒳.val.p ⋙ Over.map g)
            (𝒴.val.p ⋙ Over.map g) f.hom.toFunctor f.hom.toFunctor := by
      rw [← Functor.assoc, key, Functor.id_comp]
    exact h2

/-- `AlgebraicGeometry.Stack.unrelocalizeBaseFunctor` is an equivalence: it is the inverse
functor of `CategoryTheory.TwoFibreProductOver.relocalizeBaseEquivalence`, whose two hypotheses
are that the two legs of the 2-fibre product are strictly over the site — here both the
compatibility of `f`. -/
theorem isEquivalence_unrelocalizeBaseFunctor
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (f : 𝒳 ⟶ 𝒴) :
    Functor.IsEquivalence (unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f).toFunctor :=
  (TwoFibreProductOver.relocalizeBaseEquivalence g f.hom.w f.hom.w).isEquivalence_inverse

/-- The identity based functor on the change of base of a fibered category is an equivalence. -/
private theorem isEquivalence_id_changeBaseFiberedInGroupoids
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) :
    Functor.IsEquivalence
      (BasedFunctor.id (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val).toFunctor :=
  inferInstanceAs (Functor.IsEquivalence
    (𝟭 (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳).val.obj))

/-- **Representability by algebraic spaces of a relative diagonal is carried along Construction
A.** If the relative diagonal of `f : 𝒳 ⟶ 𝒴` is representable by algebraic spaces over `S`, then
the relative diagonal of the 1-morphism Construction A produces over `S'` is representable by
algebraic spaces over `S'`.

Two steps, as for the Stacks 04XB condition: `Stacks 04X5`
(`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff`) carries
representability to `changeBase (Δ_f)`, and **Stacks 0457** carries it from there to
`Δ_{changeBase f}` along `AlgebraicGeometry.Stack.unrelocalizeBaseFunctor`, whose
2-commutativity isomorphism is the identity by
`AlgebraicGeometry.Stack.relativeDiagonalBasedFunctor_changeBase`. -/
theorem isRepresentableByAlgebraicSpaces_relativeDiagonal_changeBase
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (f : 𝒳 ⟶ 𝒴)
    (h : IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom)) :
    IsRepresentableByAlgebraicSpaces B S' hS'
      (relativeDiagonalBasedFunctor B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f).hom) := by
  have _ := isEquivalence_id_changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳
  have _ := isEquivalence_unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S' hS'
      (relativeDiagonalBasedFunctor B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f).hom)
      (changeBaseFunctor B S S' hS hS' g (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom))
      (BasedFunctor.id _) (unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f) (Iso.refl _)).1
    ((isRepresentableByAlgebraicSpaces_changeBaseFunctor_iff B S S' hS hS' g
      (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom)).2 h)

/-- **A condition of Stacks 04XB at an étale-chart property is carried along Construction A.** If
the relative diagonal of `f : 𝒳 ⟶ 𝒴` has the étale-chart property `P` over `S`, then the relative
diagonal of the 1-morphism Construction A produces over `S'` has it over `S'`.

This is the converse of
`AlgebraicGeometry.Stack.hasEtaleChartProperty_relativeDiagonal_of_changeBase`, which that
declaration's implementation notes record as needing
`CategoryTheory.TwoFibreProductOver.unrelocalizeBase` over the site; that is
`AlgebraicGeometry.Stack.unrelocalizeBaseFunctor`. The two steps are otherwise the same:
`AlgebraicGeometry.Stack.holdsOnEveryEtaleChart_changeBaseHom_iff` moves the condition from `Δ_f`
to `changeBase (Δ_f)`, and **Stacks 0457**
(`AlgebraicGeometry.Stack.relativeProperty_of_equivalences`) moves it from there to
`Δ_{changeBase f}`. -/
theorem hasEtaleChartProperty_relativeDiagonal_changeBase (P : MorphismProperty Scheme.{u})
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)) (f : 𝒳 ⟶ 𝒴)
    (h : HasEtaleChartProperty B S hS P (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)) :
    HasEtaleChartProperty B S' hS' P
      (relativeDiagonal.{u, u, u + 1} B S' hS'
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
        (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
        (changeBaseHom B S S' hS hS' g f)) := by
  have _ := isEquivalence_id_changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳
  have _ := isEquivalence_unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f
  exact relativeProperty_of_equivalences B S' hS'
    (fun _ _ k => Space.HoldsOnEveryEtaleChart B S' hS' P k.hom)
    (relativeDiagonalBasedFunctor B S' hS'
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒳)
      (changeBaseFiberedInGroupoids B S S' hS hS' g 𝒴)
      (changeBaseHom B S S' hS hS' g f).hom)
    (changeBaseFunctor B S S' hS hS' g (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom))
    (BasedFunctor.id _) (unrelocalizeBaseFunctor B S S' hS hS' g 𝒳 𝒴 f) (Iso.refl _)
    ((holdsOnEveryEtaleChart_changeBaseHom_iff B S S' hS hS' g P
      (relativeDiagonal.{u, u, u + 1} B S hS 𝒳 𝒴 f)).2 h)

variable {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 04X6 on a 1-morphism.** A 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks over `S`,
viewed as a 1-morphism of the algebraic stacks over `S'` that Stacks 04X6 produces from `𝒳` and
`𝒴`. The underlying functor is unchanged; only the two structure functors are composed with
`CategoryTheory.Over.map g`. -/
def changeBaseHomAlgebraicStacks (f : 𝒳 ⟶ 𝒴) :
    changeBaseAlgebraicStacks.{u, w, w'} B S S' hS hS' g 𝒳 ⟶
      changeBaseAlgebraicStacks.{u, w, w'} B S S' hS hS' g 𝒴 :=
  Bicategory.InducedBicategory.mkHom (changeBaseHom B S S' hS hS' g f.hom)

/-- **The DM axiom of Stacks 04YW is carried along Construction A.** If `f : 𝒳 ⟶ 𝒴` is DM over
`S`, then `f` viewed over `S'` by **Stacks 04X6** is DM over `S'`.

The DM condition is representability by algebraic spaces of the relative diagonal together with
the Stacks 04XB condition at unramifiedness (**Stacks 03ZH**, part (1)), which is the
every-étale-chart condition of **Stacks 03MJ**; so the two halves are
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal_changeBase` and
`AlgebraicGeometry.Stack.hasEtaleChartProperty_relativeDiagonal_changeBase`. -/
theorem isDM_changeBaseHomAlgebraicStacks (f : 𝒳 ⟶ 𝒴) (hf : IsDM B S hS f) :
    IsDM B S' hS' (changeBaseHomAlgebraicStacks.{u, w, w'} B S S' hS hS' g f) := by
  obtain ⟨hΔ, hP⟩ := hf
  exact ⟨isRepresentableByAlgebraicSpaces_relativeDiagonal_changeBase B S S' hS hS' g
      𝒳.val 𝒴.val f.hom hΔ,
    hasEtaleChartProperty_relativeDiagonal_changeBase B S S' hS hS' g
      (@AlgebraicGeometry.Unramified.{u}) 𝒳.val 𝒴.val f.hom hP⟩

/-- **The quasi-DM axiom of Stacks 04YW is carried along Construction A.** If `f : 𝒳 ⟶ 𝒴` is
quasi-DM over `S`, then `f` viewed over `S'` by **Stacks 04X6** is quasi-DM over `S'`.

This is `AlgebraicGeometry.Stack.isDM_changeBaseHomAlgebraicStacks` at local quasi-finiteness
(**Stacks 03XJ**, part (1)) instead of unramifiedness; quasi-DM carries no representability
witness, so only the Stacks 04XB half is needed. -/
theorem isQuasiDM_changeBaseHomAlgebraicStacks (f : 𝒳 ⟶ 𝒴)
    (hf : AlgebraicStacks.IsQuasiDM B S hS f) :
    AlgebraicStacks.IsQuasiDM B S' hS'
      (changeBaseHomAlgebraicStacks.{u, w, w'} B S S' hS hS' g f) :=
  hasEtaleChartProperty_relativeDiagonal_changeBase B S S' hS hS' g
    ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    𝒳.val 𝒴.val f.hom hf

end ChangeOfBase

section OverBase

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 050L, part (3).** If `𝒴` is separated over `S` and the 1-morphism `f : 𝒳 ⟶ 𝒴` is
separated, then `𝒳` is separated over `S`.

Being separated over `S` is being separated as a structure morphism (**Stacks 050D**, part (3)),
the structure morphism of `𝒳` is `f` followed by that of `𝒴`
(`AlgebraicGeometry.Stack.comp_structureMorphism`), and separated 1-morphisms compose
(**Stacks 050K**). -/
@[stacks 050L "part (3): separated over the base"]
theorem isSeparatedOver_of_isSeparated (f : 𝒳 ⟶ 𝒴) (h𝒴 : IsSeparatedOver B S hS 𝒴)
    (hf : AlgebraicStacks.IsSeparated B S hS f) : IsSeparatedOver B S hS 𝒳 := by
  simpa only [comp_structureMorphism] using
    AlgebraicStacks.isSeparated_comp B S hS f (structureMorphism B S hS 𝒴) hf h𝒴

end OverBase

section Absolute

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}

/-- **Stacks 04X6 on a 1-morphism, at the terminal base.** A 1-morphism of algebraic stacks over
`S`, viewed as a 1-morphism of algebraic stacks over `Spec(ℤ)` along the unique morphism
`S ⟶ Spec(ℤ)`. This is the viewing that **Stacks 050D** parts (5)-(8), and so Stacks 050L parts
(5)-(8), are stated in terms of. -/
noncomputable abbrev viewOverIntHom (f : 𝒳 ⟶ 𝒴) :
    viewOverInt.{u, w, w'} B S hS 𝒳 ⟶ viewOverInt.{u, w, w'} B S hS 𝒴 :=
  changeBaseHomAlgebraicStacks.{u, w, w'} B S _ hS (contains_specULiftZ B)
    (toIntObject B S hS) f

/-- **Stacks 050L, part (5).** If `𝒴` is DM and the 1-morphism `f : 𝒳 ⟶ 𝒴` is DM, then `𝒳` is
DM — the two conditions on objects in the absolute sense of **Stacks 050D**, part (5).

Being DM is being DM over `Spec(ℤ)` after viewing (**Stacks 050D**, part (5)); the structure
morphism over `Spec(ℤ)` of `𝒳` viewed is `f` viewed followed by that of `𝒴` viewed
(`AlgebraicGeometry.Stack.comp_structureMorphism` at the terminal base); the DM axiom for `f`
survives the viewing (`AlgebraicGeometry.Stack.isDM_changeBaseHomAlgebraicStacks`); and DM
1-morphisms compose (**Stacks 050K**). So this is part (1) of Stacks 050L read at the base
`Spec(ℤ)`. -/
@[stacks 050L "part (5): DM"]
theorem isDMAbs_of_isDM (f : 𝒳 ⟶ 𝒴) (h𝒴 : IsDMAbs.{u, w, w'} B S hS 𝒴)
    (hf : IsDM B S hS f) : IsDMAbs.{u, w, w'} B S hS 𝒳 := by
  simpa only [comp_structureMorphism] using
    AlgebraicStacks.isDM_comp B _ (contains_specULiftZ B)
      (viewOverIntHom.{u, w, w'} B S hS f)
      (structureMorphism B _ (contains_specULiftZ B) (viewOverInt.{u, w, w'} B S hS 𝒴))
      (isDM_changeBaseHomAlgebraicStacks.{u, w, w'} B S _ hS (contains_specULiftZ B)
        (toIntObject B S hS) f hf) h𝒴

/-- **Stacks 050L, part (6).** If `𝒴` is quasi-DM and the 1-morphism `f : 𝒳 ⟶ 𝒴` is quasi-DM,
then `𝒳` is quasi-DM — the two conditions on objects in the absolute sense of **Stacks 050D**,
part (6).

This is part (2) of Stacks 050L read at the base `Spec(ℤ)`, with
`AlgebraicGeometry.Stack.isQuasiDM_changeBaseHomAlgebraicStacks` supplying the axiom for the
viewed 1-morphism. -/
@[stacks 050L "part (6): quasi-DM"]
theorem isQuasiDMAbs_of_isQuasiDM (f : 𝒳 ⟶ 𝒴) (h𝒴 : IsQuasiDMAbs.{u, w, w'} B S hS 𝒴)
    (hf : AlgebraicStacks.IsQuasiDM B S hS f) : IsQuasiDMAbs.{u, w, w'} B S hS 𝒳 := by
  simpa only [comp_structureMorphism] using
    AlgebraicStacks.isQuasiDM_comp B _ (contains_specULiftZ B)
      (viewOverIntHom.{u, w, w'} B S hS f)
      (structureMorphism B _ (contains_specULiftZ B) (viewOverInt.{u, w, w'} B S hS 𝒴))
      (isQuasiDM_changeBaseHomAlgebraicStacks.{u, w, w'} B S _ hS (contains_specULiftZ B)
        (toIntObject B S hS) f hf) h𝒴

/-- **Stacks 050L, part (7).** If `𝒴` is separated and the 1-morphism `f : 𝒳 ⟶ 𝒴` is separated,
then `𝒳` is separated — the two conditions on objects in the absolute sense of **Stacks 050D**,
part (7).

This is part (3) of Stacks 050L read at the base `Spec(ℤ)`. The hypothesis on `f` is the
Stacks 04YW separatedness axiom for `f` **viewed over `Spec(ℤ)`**, which is the base the absolute
statement lives at; it is not the axiom over `S`. Unlike the DM axiom of part (5), the
separatedness axiom is not known in this library to survive the viewing: it is the Stacks 04XB
condition at properness, which is not an every-étale-chart condition. See the implementation
notes of this file. -/
@[stacks 050L "part (7): separated, f's axiom read over Spec(Z) not over S"]
theorem isSeparatedAbs_of_isSeparated (f : 𝒳 ⟶ 𝒴) (h𝒴 : IsSeparatedAbs.{u, w, w'} B S hS 𝒴)
    (hf : AlgebraicStacks.IsSeparated B _ (contains_specULiftZ B)
      (viewOverIntHom.{u, w, w'} B S hS f)) :
    IsSeparatedAbs.{u, w, w'} B S hS 𝒳 :=
  isSeparatedOver_of_isSeparated B _ (contains_specULiftZ B)
    (viewOverIntHom.{u, w, w'} B S hS f) h𝒴 hf

/-- **Stacks 050L, part (8).** If `𝒴` is quasi-separated and the 1-morphism `f : 𝒳 ⟶ 𝒴` is
quasi-separated, then `𝒳` is quasi-separated — the two conditions on objects in the absolute
sense of **Stacks 050D**, part (8), and so each the conjunction of quasi-compactness and
quasi-separatedness of a relative diagonal. Both conjuncts of the conclusion are proved, through
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparated_comp`.

This is part (4) of Stacks 050L read at the base `Spec(ℤ)`. As in part (7) the hypothesis on `f`
is the Stacks 04YW axiom for `f` **viewed over `Spec(ℤ)`**: quasi-separatedness is the Stacks
04XB condition at quasi-compactness together with quasi-separatedness of morphisms of algebraic
spaces, neither of which is an every-étale-chart condition. -/
@[stacks 050L "part (8): quasi-separated, f's axiom read over Spec(Z) not over S"]
theorem isQuasiSeparatedAbs_of_isQuasiSeparated (f : 𝒳 ⟶ 𝒴)
    (h𝒴 : IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒴)
    (hf : AlgebraicStacks.IsQuasiSeparated B _ (contains_specULiftZ B)
      (viewOverIntHom.{u, w, w'} B S hS f)) :
    IsQuasiSeparatedAbs.{u, w, w'} B S hS 𝒳 := by
  simpa only [comp_structureMorphism] using
    AlgebraicStacks.isQuasiSeparated_comp B _ (contains_specULiftZ B)
      (viewOverIntHom.{u, w, w'} B S hS f)
      (structureMorphism B _ (contains_specULiftZ B) (viewOverInt.{u, w, w'} B S hS 𝒴))
      hf h𝒴

end Absolute

end AlgebraicGeometry.Stack

end
