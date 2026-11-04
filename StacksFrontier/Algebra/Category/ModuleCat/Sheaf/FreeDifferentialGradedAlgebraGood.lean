module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeDifferentialGradedAlgebraFiltration
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedUnitColimit
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GoodDifferentialGradedToposDirectSum
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedToposDerivedPushforward
public import StacksCore.Tactic.StacksAttribute

/-!
# The free differential graded algebra on triangular generators is good

Let `(C, O)` be a ringed site. The source considers, for `i = 0, 1, 2, …`, sheaves of graded sets
`Sᵢ` together with maps `δᵢ₊₁ : Sᵢ₊₁ ⟶ Aᵢ = O⟨S₀ ⨿ ⋯ ⨿ Sᵢ⟩` of degree one landing in the closed
sections, the differential of `Aᵢ₊₁` being the Leibniz extension of the one on `Aᵢ` with
`d(s) = δ(s)` on the new generators, and puts `A = colim Aᵢ`. **Tag 0FU1** asserts that for every
morphism of ringed topoi `f : (Sh(C'), O') ⟶ (Sh(C), O)` the pullback `f^*A` is flat as a graded
`O'`-module and K-flat as a complex of `O'`-modules.

Here `A = colim Aᵢ` is the free graded `O`-algebra `O⟨⨿ᵢ Sᵢ⟩` on the whole family, with the
Leibniz extension of the single derivation datum `δ` that is `δᵢ` on the generators of level `i`
— this is the colimit of the stages, each stage being the part spanned by the letters of level
at most `i` — and the source's condition that `δᵢ₊₁` lands in `Aᵢ` is that `δ` is
**triangular**: the differential of a generator of level `k` is locally a combination of words
in letters of level `< k` (`SheafOfModules.DerivationDatum.IsTriangular`). The levels may be any
well-ordered set; the source's are `ℕ`.

The conclusion is read at the goodness of Tag 0FSA, `SheafOfModules.IsGoodToposBaseChange`, for
`A` regarded as a right differential graded module over `(O, 0)`: flat as a graded
`(O, 0)`-module, i.e. as a graded `O`-module; K-flat, i.e. K-flat as a complex of `O`-modules;
and at every morphism of ringed topoi `f` and every sheaf of differential graded algebras `B`
over the source with a unital `O ⟶ f_*B`, a pullback exists and every pullback is again flat and
K-flat. Taking `B = (O', 0)` this is the source's statement about `f^*A`.

## The proof

The source's own argument. The weight of a word counts its letters of each level, and weights
are ordered colexicographically, a well-order. The differential strictly lowers the weight
(`SheafOfModules.algD_isLocallyIn`), so the part `F_w` of weight `≤ w` is a subcomplex, and
`0 ⟶ F_{<w} ⟶ F_w ⟶ (weight w part) ⟶ 0` is split in every degree with third term free with
zero differential (`SheafOfModules.weightSplitting`). By well-founded induction on `w`: `F_{<w}`
is the filtered colimit of the `F_v`, `v < w`, hence good (Tag 0FSD at goodness), and `F_w` is an
extension of a good free module by it, hence good (Tag 0FSC at goodness). Finally
`A = colim_w F_w`.

## Main results

* `SheafOfModules.isGoodToposBaseChange_filtLE`: every stage of the weight filtration is good.
* `SheafOfModules.freeDGAlgebra_isGoodToposBaseChange`: the goodness of `A`, over any ringed topos
  carrying the sheafification instances of the construction.
* `SheafOfModules.freeDGAlgebra_colimit_isGoodToposBaseChange`: **Tag 0FU1**, at a ringed topos
  in one universe, where those instances hold: `A` is the colimit of its stages `Aᵢ`, and `A` is
  good.

## References

* [Stacks Project, Tag 0FU1](https://stacks.math.columbia.edu/tag/0FU1)
* [Stacks Project, Tag 0FSA](https://stacks.math.columbia.edu/tag/0FSA)
* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FSD](https://stacks.math.columbia.edu/tag/0FSD)
* [Stacks Project, Tag 0FSG](https://stacks.math.columbia.edu/tag/0FSG)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite

universe w v₁ u₁ v₂ u₂

namespace SheafOfModules

open Stacks Stacks.SheafOfGradedSets DifferentialGradedModule DifferentialGradedAlgebra

section General

variable {Y : AlgebraicGeometry.RingedTopos.{v₂, u₂, w}}
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget RingCat.{w})]
  [Y.J.HasSheafCompose (CategoryTheory.forget AddCommGrpCat.{w})]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}] [HasSheafify Y.J AddCommGrpCat.{w}]
  [HasSheafify Y.J (Type w)]
  {I : Type w} [LinearOrder I]
  (𝒮 : I → SheafOfGradedSets.{w} Y.J) (δ : DerivationDatum (J := Y.J) 𝒮 Y.O)
  (hδ : ∀ (U : Y.Cᵒᵖ) (x : Letter (C := Y.C) 𝒮 U),
    (algD 𝒮 δ (letterDeg x + 1)).val.app U (δ.app U x) = 0)
  (htri : DerivationDatum.IsTriangular (J := Y.J) 𝒮 δ)

attribute [local instance] Stacks.TensorSheafWorld.monoidalCategory

/-- **A directed union of good stages of the weight filtration is good**, by Tag 0FSD at goodness:
the union is the filtered colimit of the stages. -/
theorem isGoodToposBaseChange_filt_of_union {K : Type w} [LinearOrder K] [Nonempty K]
    (D : K → Set (I →₀ ℕ)) (hmono : Monotone D) (hD : ∀ k, IsWeightLower (D k))
    (E : Set (I →₀ ℕ)) (hE : IsWeightLower E) (hle : ∀ k, D k ⊆ E)
    (hcov : ∀ v ∈ E, ∃ k, v ∈ D k)
    (hK : ∀ k, IsGoodToposBaseChange.{w, v₁, u₁}
      (ofComplex (filtComplex Y.O 𝒮 δ hδ htri (hD k)))) :
    IsGoodToposBaseChange.{w, v₁, u₁} (ofComplex (filtComplex Y.O 𝒮 δ hδ htri hE)) := by
  have hc := filtCocone_isColimit 𝒮 δ hδ htri D hmono hD E hE hle hcov
  have hK' : ∀ k : K, IsGoodToposBaseChange.{w, v₁, u₁}
      ((filtDiagram 𝒮 δ hδ htri D hmono hD).obj k) := hK
  have := isGoodToposBaseChange_of_isColimit_isFiltered.{w, v₁, u₁} hc hK'
  exact this

variable [WellFoundedLT I]

omit [WellFoundedLT I] in
/-- For a minimal weight `w`, the part `F_{<w}` of the weight filtration of weight `< w` is
good. -/
theorem isGoodToposBaseChange_filtLT_of_minimal (w : Colex (I →₀ ℕ)) (hw : ∀ v, ¬ v < w) :
    IsGoodToposBaseChange.{w, v₁, u₁}
      (ofComplex (filtComplex Y.O 𝒮 δ hδ htri (isWeightLower_weightLT w))) := by
  have h₀ : IsGoodToposBaseChange.{w, v₁, u₁}
      (freeOnPresheaves Y.O (fun n => (wordsIn (J := Y.J) 𝒮 (weightLT w) n).toFunctor)) :=
    freeOnPresheaves_isGoodToposBaseChange _
  exact isGoodToposBaseChange_of_iso
    (isoMk (filtLTIsoOfMinimal 𝒮 δ hδ htri w hw).symm) h₀

omit [WellFoundedLT I] in
/-- If some weight lies below `w` and every stage `F_v` with `v < w` is good, then the part
`F_{<w}` of the weight filtration of weight `< w` is good. -/
theorem isGoodToposBaseChange_filtLT_of_lt (w : Colex (I →₀ ℕ)) (v₀ : Colex (I →₀ ℕ))
    (hv₀ : v₀ < w)
    (ih : ∀ v < w, IsGoodToposBaseChange.{w, v₁, u₁}
      (ofComplex (filtComplex Y.O 𝒮 δ hδ htri (isWeightLower_weightLE v)))) :
    IsGoodToposBaseChange.{w, v₁, u₁}
      (ofComplex (filtComplex Y.O 𝒮 δ hδ htri (isWeightLower_weightLT w))) := by
  have : Nonempty {v : Colex (I →₀ ℕ) // v < w} := ⟨⟨v₀, hv₀⟩⟩
  exact isGoodToposBaseChange_filt_of_union 𝒮 δ hδ htri
    (fun v : {v : Colex (I →₀ ℕ) // v < w} => weightLE v.1)
    (fun _ _ h => weightLE_mono h) (fun v => isWeightLower_weightLE v.1) (weightLT w)
    (isWeightLower_weightLT w) (fun v => weightLE_subset_weightLT v.2)
    (fun u hu => ⟨⟨toColex u, hu⟩, mem_weightLE_self u⟩) (fun v => ih v.1 v.2)

/-- **Every stage `F_w` of the weight filtration is good**, by well-founded induction over the
weights. -/
theorem isGoodToposBaseChange_filtLE (w : Colex (I →₀ ℕ)) :
    IsGoodToposBaseChange.{w, v₁, u₁}
      (ofComplex (filtComplex Y.O 𝒮 δ hδ htri (isWeightLower_weightLE w))) := by
  induction w using WellFoundedLT.induction with
  | _ w ih =>
    have hlt : IsGoodToposBaseChange.{w, v₁, u₁}
        (ofComplex (filtComplex Y.O 𝒮 δ hδ htri (isWeightLower_weightLT w))) := by
      by_cases hne : ∃ v, v < w
      · obtain ⟨v₀, hv₀⟩ := hne
        exact isGoodToposBaseChange_filtLT_of_lt 𝒮 δ hδ htri w v₀ hv₀ ih
      · exact isGoodToposBaseChange_filtLT_of_minimal 𝒮 δ hδ htri w
          (fun v hv => hne ⟨v, hv⟩)
    exact isGoodToposBaseChange_of_split_freeOnPresheaves
      (weightPiecePresheaves (J := Y.J) 𝒮 w) _ _ (weightIncl_weightProj 𝒮 δ hδ htri w)
      (weightSplitting 𝒮 δ hδ htri w) hlt

include htri in
/-- **The free differential graded algebra on triangular generators is good**, over an arbitrary
ringed topos whose site carries the sheafification instances of the construction. The
underlying complex of `O`-modules of `O⟨S⟩`, with the Leibniz extension of a closed triangular
derivation datum, regarded as a right differential graded `(O, 0)`-module, is good in the sense
of Tag 0FSA. Tag 0FU1, at a ringed topos in one universe where all those instances hold, is
`SheafOfModules.freeDGAlgebra_colimit_isGoodToposBaseChange`. -/
theorem freeDGAlgebra_isGoodToposBaseChange :
    IsGoodToposBaseChange.{w, v₁, u₁} (toUnitModule (freeDGAlgebra (Osharp := Y.O) 𝒮 δ hδ)) := by
  have : Nonempty (Colex (I →₀ ℕ)) := ⟨toColex 0⟩
  have huniv : IsGoodToposBaseChange.{w, v₁, u₁}
      (ofComplex (filtComplex Y.O 𝒮 δ hδ htri (D := Set.univ) (fun _ _ => trivial))) :=
    isGoodToposBaseChange_filt_of_union 𝒮 δ hδ htri (fun v : Colex (I →₀ ℕ) => weightLE v)
      (fun _ _ h => weightLE_mono h) (fun v => isWeightLower_weightLE v) Set.univ
      (fun _ _ => trivial) (fun _ _ _ => trivial) (fun u _ => ⟨toColex u, mem_weightLE_self u⟩)
      (fun v => isGoodToposBaseChange_filtLE 𝒮 δ hδ htri v)
  exact isGoodToposBaseChange_of_iso (isoMk (filtUnivIso 𝒮 δ hδ htri)) huniv

end General

/-! ### Tag 0FU1 -/

section Tag

universe u

attribute [local instance] AlgebraicGeometry.RingedTopos.hasSheafCompose_forget₂_ringCat

variable {X : AlgebraicGeometry.RingedTopos.{u, u, u}} {I : Type u} [LinearOrder I]
  [WellFoundedLT I] [Nonempty I]
  (𝒮 : I → SheafOfGradedSets.{u} X.J) (δ : DerivationDatum (J := X.J) 𝒮 X.O)
  (hδ : ∀ (U : X.Cᵒᵖ) (x : Letter (C := X.C) 𝒮 U),
    (algD 𝒮 δ (letterDeg x + 1)).val.app U (δ.app U x) = 0)
  (htri : DerivationDatum.IsTriangular (J := X.J) 𝒮 δ)

/-- The stage of all weights is `A` itself, as a right differential graded `(O, 0)`-module. -/
noncomputable def filtUnivModuleIso :
    ofComplex (Osharp := X.O)
        (filtComplex X.O 𝒮 δ hδ htri (D := Set.univ) (fun _ _ => trivial)) ≅
      toUnitModule (Osharp := X.O) (freeDGAlgebra (Osharp := X.O) 𝒮 δ hδ) :=
  isoMk (M := ofComplex (Osharp := X.O)
      (filtComplex X.O 𝒮 δ hδ htri (D := Set.univ) (fun _ _ => trivial)))
    (N := toUnitModule (Osharp := X.O) (freeDGAlgebra (Osharp := X.O) 𝒮 δ hδ))
    (filtUnivIso 𝒮 δ hδ htri)

/-- **The cocone of the stages `Aᵢ` to `A`**: `Aᵢ` is the subcomplex of `A = O⟨⨿ⱼ Sⱼ⟩` spanned by
the words in the letters of level at most `i`, i.e. the underlying complex of
`O⟨S₀ ⨿ ⋯ ⨿ Sᵢ⟩`, and the legs are the inclusions. -/
noncomputable def stagesCocone :
    Cocone (filtDiagram 𝒮 δ hδ htri levelLE levelLE_mono isWeightLower_levelLE) :=
  (filtCocone 𝒮 δ hδ htri levelLE levelLE_mono isWeightLower_levelLE Set.univ
    (fun _ _ => trivial) (fun _ _ _ => trivial)).extend (filtUnivModuleIso 𝒮 δ hδ htri).hom

omit [WellFoundedLT I] [Nonempty I] in
/-- The point of `stagesCocone` is `A`, as a right differential graded `(O, 0)`-module. -/
theorem stagesCocone_pt :
    (stagesCocone 𝒮 δ hδ htri).pt =
      toUnitModule (Osharp := X.O) (freeDGAlgebra (Osharp := X.O) 𝒮 δ hδ) := rfl

/-- `A` is the colimit of the stages `Aᵢ`. -/
noncomputable def stagesCocone_isColimit_pt : IsColimit (stagesCocone 𝒮 δ hδ htri) := by
  have h1 := stagesCocone_isColimit (Osharp := X.O) 𝒮 δ hδ htri
  have h2 := IsColimit.ofIsoColimit h1 (Cocone.extendIso _ (filtUnivModuleIso 𝒮 δ hδ htri))
  exact h2

omit [Nonempty I] in
include htri in
/-- The goodness of `A` at a ringed topos in one universe. -/
theorem freeDGAlgebra_isGoodToposBaseChange' :
    IsGoodToposBaseChange.{u, v₁, u₁}
      (toUnitModule (Osharp := X.O) (freeDGAlgebra (Osharp := X.O) 𝒮 δ hδ)) :=
  freeDGAlgebra_isGoodToposBaseChange 𝒮 δ hδ htri

/-- **Tag 0FU1.** *"In the situation above the differential graded `O`-algebra `A = colim Aᵢ` has
the following property: for any morphism `(f, f^♯) : (Sh(C'), O') ⟶ (Sh(C), O)` of ringed topoi,
the pullback `f^*A` is flat as a graded `O'`-module and is K-flat as a complex of
`O'`-modules."*

The situation: a family `𝒮` of sheaves of graded sets indexed by a nonempty well-ordered set of
levels (the source's `S₀, S₁, …`, indexed by `ℕ`), and a derivation datum `δ` on the free graded
`O`-algebra `A = O⟨⨿ᵢ Sᵢ⟩` whose values are closed (`hδ`) and triangular (`htri`: the value on a
generator of level `k` lies, locally, in the subalgebra generated by the letters of level `< k`,
which is the source's `δₖ : Sₖ ⟶ A_{k-1}`), with the Leibniz extension of `δ` as differential.

The first conjunct is `A = colim Aᵢ`: `A` is the colimit of the stages `Aᵢ`, the subcomplexes
spanned by the words in the letters of level at most `i`. The second is the property: `A`,
regarded as a right differential graded module over `(O, 0)`, is good in the sense of Tag 0FSA,
that is flat as a graded `O`-module, K-flat as a complex of `O`-modules, and the same for its
pullback along every morphism of ringed topoi. -/
@[stacks 0FU1]
theorem freeDGAlgebra_colimit_isGoodToposBaseChange :
    Nonempty (IsColimit (stagesCocone 𝒮 δ hδ htri)) ∧
      IsGoodToposBaseChange.{u, v₁, u₁}
      (toUnitModule (Osharp := X.O) (freeDGAlgebra (Osharp := X.O) 𝒮 δ hδ)) :=
  ⟨⟨stagesCocone_isColimit_pt 𝒮 δ hδ htri⟩, freeDGAlgebra_isGoodToposBaseChange' 𝒮 δ hδ htri⟩

end Tag

end SheafOfModules

end
