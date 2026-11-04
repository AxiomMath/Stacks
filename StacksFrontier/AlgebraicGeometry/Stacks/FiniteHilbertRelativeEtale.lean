module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSquares
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IsomorphismLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpaceEtaleChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleSite
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.FibreSectionSpace
public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbertRelativeRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRelocalize
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveOnObjectsRelative
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangeComposite

/-!
# The induced morphism of relative finite Hilbert stacks is representable and étale (Stacks 05YG)

Let `G : 𝒳' ⟶ 𝒳` be a 1-morphism of stacks in groupoids over the big fppf site of a scheme `S`,
let `F : 𝒳 ⟶ 𝒴` and `F' : 𝒳' ⟶ 𝒴` be 1-morphisms to a third stack and let
`γ : F' ⟶ F ∘ G` be a 2-isomorphism, so that Stacks 05XN produces the canonical 1-morphism
`ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of degree-`d` finite Hilbert stacks. Stacks 05YG asserts that this
1-morphism is representable by algebraic spaces and étale as soon as `G` is, and surjective as
soon as `G` is also surjective.

The geometric content is that each fibre of `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` over a scheme-valued point
is the space of sections of `W ⟶ Z` over the base, where `Z ⟶ U` is the degree-`d` finite locally
free cover the point carries and `W` represents the fibre of `G` over the induced point of `𝒳`;
and that such a space of sections is an algebraic space étale over the base, which is
Stacks 05XR. This file performs that deduction.

## Main results

* `AlgebraicGeometry.Stack.FiniteHilbert.Object.exists_sectionSpace_isEtale`: the fibre over the
  universal family of an object is an algebraic space étale over the base of the object.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_and_isEtale_mapRelative`:
  **Stacks 05YG, part (1)**, the 1-morphism is representable by algebraic spaces and étale, in the
  longhand form of Stacks 03YK that `AlgebraicGeometry.Stack.IsRelativelyEtale` uses; its two
  halves are `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_mapRelative` and
  `AlgebraicGeometry.Stack.isEtale_mapRelative`.
* `AlgebraicGeometry.Stack.isSurjectiveOnObjects_mapRelative`: **Stacks 05YG, part (2)**, it is
  surjective when `G` is also surjective.

## Implementation notes

The hypothesis that `G` is representable by algebraic spaces and étale is stated as the two
clauses `hGrep` and `hGet` that `AlgebraicGeometry.Stack.IsRelativelyEtale` packages, at the free
universes of the stacks involved; `IsRelativelyEtale` itself is pinned at one universe
assignment.

The identification of the fibre over an arbitrary scheme-valued point with the fibre over the
universal family of the object it takes the tautological object to is the 2-Yoneda normalisation
`AlgebraicGeometry.Stack.exists_equivalenceOver_of_obj`; the fibre over a universal family is a
space of sections by
`AlgebraicGeometry.Stack.FiniteHilbert.Object.nonempty_equivalenceOver_sectionSpace`, and that
space of sections is an algebraic space étale over the base by Stacks 05XR,
`AlgebraicGeometry.Space.isAlgebraicSpace_sectionSpace_and_isEtale`, once the étaleness of the
fibre of `G`, which Stacks 03YK reads over `S`, has been read over the cover and then over the
base of the object, by `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff`.

Étaleness is stated in the longhand of Stacks 03YK rather than through
`AlgebraicGeometry.Stack.HasRelativeProperty`, which needs an `IsLocalAtTarget` instance for
étaleness in the fppf precoverage (see
`StacksFrontier/AlgebraicGeometry/Stacks/SeparationOverBase.lean`).

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 05XN](https://stacks.math.columbia.edu/tag/05XN)
* [Stacks Project, Tag 05XR](https://stacks.math.columbia.edu/tag/05XR)
* [Stacks Project, Tag 05YG](https://stacks.math.columbia.edu/tag/05YG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w v₁ u₁

namespace AlgebraicGeometry.Stack

/-! ### Étaleness read over a cover and over a base -/

section Relocalize

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- Surjectivity of `W ⟶ *` over `X` gives surjectivity of the structural morphism of the
lower-shriek extension of `W` along `h : X ⟶ Y`. -/
private theorem isSurjective_relocalizeToYoneda_of_toYonedaId {X Y : Scheme.{u}}
    {hX : B.Contains X} {hY : B.Contains Y} (h : B.obj hX ⟶ B.obj hY)
    (W : (BigFppfOver B X hX)ᵒᵖ ⥤ Type u)
    (hW : Space.IsSurjective B X hX (Space.toYonedaId B X hX W)) :
    Space.IsSurjective B Y hY (OverShriek.relocalizeToYoneda h W) := by
  have := isIso_relocalizeToYoneda_yonedaId B X Y hX hY h
  have h₄ := Space.isSurjective_comp B Y hY (Space.isSurjective_relocalize B X hX Y hY h _ hW)
    (Space.isSurjective_of_isIso B Y hY
      (OverShriek.relocalizeToYoneda h (yoneda.obj (Over.mk (𝟙 (B.obj hX))))))
  rwa [relocalizeToYoneda_eq_map_toYonedaId B X Y hX hY h W] at h₄

/-- A property of morphisms stable under postcomposition with isomorphisms, if it holds for
`A ⟶ *`, holds for the structural morphism `A ⟶ h_{id}` to the terminal representable. -/
private theorem prop_toYonedaId_of_terminal_from
    (P : ∀ {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, (X ⟶ Y) → Prop)
    (hP : ∀ {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} (g : Y ⟶ Z) [IsIso g],
      P f → P (f ≫ g))
    (A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (h : P (terminal.from A)) :
    P (Space.toYonedaId B S hS A) := by
  have hyoneda : IsTerminal (yoneda.obj (Over.mk (𝟙 (B.obj hS)))) :=
    (Over.mkIdTerminal (X := B.obj hS)).isTerminalObj yoneda _
  rw [show Space.toYonedaId B S hS A =
      terminal.from A ≫ (hyoneda.uniqueUpToIso terminalIsTerminal).inv from
    hyoneda.hom_ext _ _]
  exact hP _ h

/-- **Étaleness of an algebraic space over a cover, read over the base of the cover.** Let
`q : Z ⟶ U` be a morphism of the big fppf site of `S` and let `W` be an algebraic space over `Z`
whose structural morphism, read over `S`, is étale. Then the structural morphism of its
lower-shriek extension to the site of `U`, a morphism to `Z` there, is étale. -/
theorem isEtale_relocalizeToYoneda_of_isEtale_algebraicSpaceMap {Z U : BigFppfOver B S hS}
    (q : Z ⟶ U) (W : (BigFppfOver B Z.left.1 Z.left.2)ᵒᵖ ⥤ Type u)
    (hW : IsAlgebraicSpace B Z.left.1 Z.left.2 W)
    (h : Space.IsEtale B S hS (algebraicSpaceMap B S hS Z
      ((spacesOverSmallerBaseFunctor B Z.left.1 S Z.left.2 hS Z.hom).obj ⟨W, hW⟩)).hom) :
    Space.IsEtale B U.left.1 U.left.2 (OverShriek.relocalizeToYoneda q.left W) := by
  have h₁ : Space.IsEtale B S hS (OverShriek.relocalizeToYoneda Z.hom W) :=
    (prop_algebraicSpaceMap_iff B S hS (Space.etaleMorphisms B S hS) Z W hW).1 h
  have h₂ := (Space.isEtale_iff_holdsOnEveryEtaleChart B S hS
    (isAlgebraicSpace_viewOver B Z.left.1 S Z.left.2 hS Z.hom W hW)
    (isAlgebraicSpace_yoneda B S hS Z) _).1 h₁
  have h₃ := (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B Z.left.1 S Z.left.2 hS Z.hom
    (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) W).1 h₂
  have h₄ := (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B Z.left.1 U.left.1 Z.left.2
    U.left.2 q.left (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) W).2 h₃
  exact (Space.isEtale_iff_holdsOnEveryEtaleChart B U.left.1 U.left.2
    (isAlgebraicSpace_viewOver B Z.left.1 U.left.1 Z.left.2 U.left.2 q.left W hW)
    (isAlgebraicSpace_yoneda B U.left.1 U.left.2 (Over.mk q.left)) _).2 h₄

/-- **Surjectivity of an algebraic space over a cover, read over the base of the cover.** Let
`q : Z ⟶ U` be a morphism of the big fppf site of `S` and let `W` be an algebraic space over `Z`
whose structural morphism, read over `S`, is surjective. Then the structural morphism of its
lower-shriek extension to the site of `U`, a morphism to `Z` there, is surjective. -/
theorem isSurjective_relocalizeToYoneda_of_surjective_algebraicSpaceMap
    {Z U : BigFppfOver B S hS} (q : Z ⟶ U) (W : (BigFppfOver B Z.left.1 Z.left.2)ᵒᵖ ⥤ Type u)
    (hW : IsAlgebraicSpace B Z.left.1 Z.left.2 W)
    (h : Space.surjectiveMorphismProperty B S hS (algebraicSpaceMap B S hS Z
      ((spacesOverSmallerBaseFunctor B Z.left.1 S Z.left.2 hS Z.hom).obj ⟨W, hW⟩))) :
    Space.IsSurjective B U.left.1 U.left.2 (OverShriek.relocalizeToYoneda q.left W) := by
  have h₁ : Space.IsSurjective B S hS (OverShriek.relocalizeToYoneda Z.hom W) :=
    (prop_algebraicSpaceMap_iff B S hS (Space.surjectiveMorphismProperty B S hS) Z W hW).1 h
  rw [← relocalizeToYoneda_eq_map_toYonedaId B Z.left.1 S Z.left.2 hS Z.hom W] at h₁
  have h₂ : Space.IsSurjective B S hS ((OverShriek.relocalizePresheafFunctor Z.hom).map
      (Space.toYonedaId B Z.left.1 Z.left.2 W)) := by
    let e := OverShriek.relocalizeToYoneda Z.hom (yoneda.obj (Over.mk (𝟙 (B.obj Z.left.2))))
    have : IsIso e := isIso_relocalizeToYoneda_yonedaId B Z.left.1 S Z.left.2 hS Z.hom
    have hc := Space.isSurjective_comp B S hS h₁ (Space.isSurjective_of_isIso B S hS (inv e))
    rwa [Category.assoc, IsIso.hom_inv_id, Category.comp_id] at hc
  have h₃ := (Space.isSurjective_relocalize_iff B Z.left.1 Z.left.2 S hS Z.hom _).1 h₂
  exact isSurjective_relocalizeToYoneda_of_toYonedaId q.left W h₃

/-- **Surjectivity over a base, read over `S`.** An algebraic space over an object `U` of the big
fppf site of `S` whose structural morphism is surjective has surjective structural morphism when
regarded as an algebraic space over `S` lying over `U`. -/
theorem surjectiveMorphismProperty_algebraicSpaceMap_of_isSurjective (U : BigFppfOver B S hS)
    (A : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u) (hA : IsAlgebraicSpace B U.left.1 U.left.2 A)
    (h : Space.IsSurjective B U.left.1 U.left.2 (terminal.from A)) :
    Space.surjectiveMorphismProperty B S hS (algebraicSpaceMap B S hS U
      ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨A, hA⟩)) := by
  refine (prop_algebraicSpaceMap_iff B S hS (Space.surjectiveMorphismProperty B S hS) U A hA).2 ?_
  exact isSurjective_relocalizeToYoneda_of_toYonedaId U.hom A
    (prop_toYonedaId_of_terminal_from (Space.IsSurjective B U.left.1 U.left.2)
      (fun g _ hf => Space.isSurjective_comp B U.left.1 U.left.2 hf
        (Space.isSurjective_of_isIso B U.left.1 U.left.2 g)) A h)

end Relocalize

/-! ### The fibre over a universal family -/

section HilbertFamily

attribute [local implicit_reducible] BasedCategory.ofFunctor finiteHilbertCategory
  FiniteHilbert.Object.universalFamily

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}
  {𝒳' 𝒳 𝒴 : StackInGroupoids.{w, u, v₁, u + 1, u₁} (BigFppfOver B S hS)
    (BigFppfOver.topology B S hS)}
  {F' : 𝒳'.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}
  {F : 𝒳.toBasedCategory ⥤ᵇ 𝒴.toBasedCategory}
  {G : 𝒳'.toBasedCategory ⥤ᵇ 𝒳.toBasedCategory}

/-- The underlying morphism of schemes of the cover of an object of a relative finite Hilbert
category is finite. -/
theorem FiniteHilbert.Object.isFinite_q (ξ : FiniteHilbert.Object B S hS 𝒳 𝒴 F d) :
    _root_.AlgebraicGeometry.IsFinite (B.inclusion.map ξ.q.left) := by
  have := ξ.finiteLocallyFree
  have := Stacks.Morphisms.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    ((BigFppfOver.toScheme B S hS).map ξ.q) d
  exact Stacks.Morphisms.IsFiniteLocallyFree.isFinite ((BigFppfOver.toScheme B S hS).map ξ.q)

/-- A property `R` of the structural morphism of a presheaf, invariant under isomorphism, which
holds for some presheaf representing the fibre of `f` over each universal family, holds for every
presheaf representing the fibre of `f` over an arbitrary scheme-valued point. -/
private theorem prop_terminal_from_of_exists_sectionSpace
    (R : ∀ (V : Scheme.{u}) (hV : B.Contains V), ((BigFppfOver B V hV)ᵒᵖ ⥤ Type u) → Prop)
    (hR : ∀ V hV (A A' : (BigFppfOver B V hV)ᵒᵖ ⥤ Type u), (A ≅ A') → R V hV A' → R V hV A)
    {𝒵 : BasedCategory (BigFppfOver B S hS)}
    (f : 𝒵 ⥤ᵇ finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)) (h𝒵 : 𝒵.p.IsFiberedInGroupoids)
    (hfam : ∀ ξ : FiniteHilbert.Object B S hS 𝒳 𝒴 F d,
      ∃ A : (BigFppfOver B (B.inclusion.obj ξ.U.left) ξ.U.left.property)ᵒᵖ ⥤ Type u,
        (IsAlgebraicSpace B (B.inclusion.obj ξ.U.left) ξ.U.left.property A ∧
          R (B.inclusion.obj ξ.U.left) ξ.U.left.property A) ∧
          Nonempty (StacksRepresentableCFG.EquivalenceOver
            (TwoFibreProductOver.fst (Over.map ξ.U.hom) 𝒵.p
              (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
                (d := d)).p ξ.universalFamily f.toFunctor)
            (presheafOfCategories (A ⋙ typeToCat)).p))
    (U : BigFppfOver B S hS)
    (y : BigFppfOver B U.left.1 U.left.2 ⥤
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)).obj)
    (hy : y ⋙ (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
      (d := d)).p = Over.map U.hom)
    (A : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
    (he : Nonempty (StacksRepresentableCFG.EquivalenceOver
      (TwoFibreProductOver.fst (Over.map U.hom) 𝒵.p
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).p y f.toFunctor)
      (presheafOfCategories (A ⋙ typeToCat)).p)) :
    R U.left.1 U.left.2 A := by
  have hξU : (y.obj (Over.mk (𝟙 U.left))).U = U :=
    (congrArg (fun K => K.obj (Over.mk (𝟙 U.left))) hy).trans
      (Over.iteratedSliceBackward_obj_mk_id_left U)
  obtain ⟨A', ⟨-, hA'⟩, ⟨e'⟩⟩ := exists_equivalenceOver_of_obj
    (fun V hV A => IsAlgebraicSpace B V hV A ∧ R V hV A) f h𝒵 hfam
    (y.obj (Over.mk (𝟙 U.left))) U hξU y hy rfl
  exact hR _ _ _ _ (CategoryTheory.PresheafOfCategories.isoOfEquivalenceOver he.some e') hA'

/-- **The fibre of `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` over the universal family of an object `ξ` is an
algebraic space étale over the base of `ξ`.** It is the space of sections over the base of the
fibre `W ⟶ Z` of `G` over the object of `𝒳` that `ξ` carries, which is étale because `G` is; so
Stacks 05XR applies, `Z` being finite over the base. -/
theorem FiniteHilbert.Object.exists_sectionSpace_isEtale
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (hGrep : IsRepresentableByAlgebraicSpaces B S hS G)
    (hGet : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.toBasedCategory.obj)
      (_hz : z ⋙ 𝒳.toBasedCategory.p = Over.map U.hom)
      (W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hW : IsAlgebraicSpace B U.left.1 U.left.2 W),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.toBasedCategory.p 𝒳.toBasedCategory.p z
          G.toFunctor)
        (presheafOfCategories (W ⋙ typeToCat)).p) →
      Space.IsEtale B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨W, hW⟩)).hom)
    (ξ : FiniteHilbert.Object B S hS 𝒳 𝒴 F d) :
    ∃ A : (BigFppfOver B (B.inclusion.obj ξ.U.left) ξ.U.left.property)ᵒᵖ ⥤ Type u,
      (IsAlgebraicSpace B (B.inclusion.obj ξ.U.left) ξ.U.left.property A ∧
        Space.IsEtale B (B.inclusion.obj ξ.U.left) ξ.U.left.property (terminal.from A)) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map ξ.U.hom)
          (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳') (𝒴 := 𝒴) (F := F')
            (d := d)).p
          (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
            (d := d)).p ξ.universalFamily
          (mapRelative B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ).toFunctor)
        (presheafOfCategories (A ⋙ typeToCat)).p) := by
  obtain ⟨W, hW, hfibre⟩ := hGrep ξ.Z ξ.sourcePoint ξ.sourcePoint_comp
  have hwet := isEtale_relocalizeToYoneda_of_isEtale_algebraicSpaceMap ξ.q W hW
    (hGet ξ.Z ξ.sourcePoint ξ.sourcePoint_comp W hW hfibre)
  have hsec := Space.isAlgebraicSpace_sectionSpace_and_isEtale (Z := Over.mk ξ.q.left)
    (isAlgebraicSpace_viewOver B ξ.Z.left.1 ξ.U.left.1 ξ.Z.left.2 ξ.U.left.2 ξ.q.left W hW)
    hwet ξ.isFinite_q
  exact ⟨_, hsec, ξ.nonempty_equivalenceOver_sectionSpace W
    (OverShriek.relocalizeToYoneda ξ.q.left W) (fun _ _ => rfl) γ hfibre⟩

/-- The canonical 1-morphism `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of degree-`d` relative
finite Hilbert stacks is representable by algebraic spaces as soon as `G : 𝒳' ⟶ 𝒳` is
representable by algebraic spaces and étale: each of its fibres over a scheme-valued point is a
space of sections of an étale morphism to a finite cover of that point, and such a space of
sections is an algebraic space by Stacks 05XR. -/
theorem isRepresentableByAlgebraicSpaces_mapRelative
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (hGrep : IsRepresentableByAlgebraicSpaces B S hS G)
    (hGet : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.toBasedCategory.obj)
      (_hz : z ⋙ 𝒳.toBasedCategory.p = Over.map U.hom)
      (W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hW : IsAlgebraicSpace B U.left.1 U.left.2 W),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.toBasedCategory.p 𝒳.toBasedCategory.p z
          G.toFunctor)
        (presheafOfCategories (W ⋙ typeToCat)).p) →
      Space.IsEtale B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨W, hW⟩)).hom) :
    IsRepresentableByAlgebraicSpaces B S hS
      (mapRelative B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ) :=
  isRepresentableByAlgebraicSpaces_of_universalFamilies _
    isFiberedInGroupoids_finiteHilbertProjection fun ξ =>
      let ⟨A, hA, he⟩ := ξ.exists_sectionSpace_isEtale γ hGrep hGet
      ⟨A, hA.1, he⟩

/-- The canonical 1-morphism `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` is étale as soon as
`G : 𝒳' ⟶ 𝒳` is representable by algebraic spaces and étale: every algebraic space representing
one of its fibres over a scheme-valued point is isomorphic to a space of sections of an étale
morphism to a finite cover of that point, hence étale over that point by Stacks 05XR, and
étaleness over the point is étaleness of the structural morphism of Stacks 03YK over `S`. -/
theorem isEtale_mapRelative
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (hGrep : IsRepresentableByAlgebraicSpaces B S hS G)
    (hGet : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.toBasedCategory.obj)
      (_hz : z ⋙ 𝒳.toBasedCategory.p = Over.map U.hom)
      (W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hW : IsAlgebraicSpace B U.left.1 U.left.2 W),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.toBasedCategory.p 𝒳.toBasedCategory.p z
          G.toFunctor)
        (presheafOfCategories (W ⋙ typeToCat)).p) →
      Space.IsEtale B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨W, hW⟩)).hom) :
    ∀ (U : BigFppfOver B S hS)
      (y : BigFppfOver B U.left.1 U.left.2 ⥤
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
          (d := d)).obj)
      (_hy : y ⋙ (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
        (d := d)).p = Over.map U.hom)
      (A : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hA : IsAlgebraicSpace B U.left.1 U.left.2 A),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom)
          (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳') (𝒴 := 𝒴) (F := F')
            (d := d)).p
          (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
            (d := d)).p y
          (mapRelative B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ).toFunctor)
        (presheafOfCategories (A ⋙ typeToCat)).p) →
      Space.IsEtale B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨A, hA⟩)).hom := by
  intro U y hy A hA he
  have hterm : Space.IsEtale B U.left.1 U.left.2 (terminal.from A) :=
    prop_terminal_from_of_exists_sectionSpace
      (fun V hV A => Space.IsEtale B V hV (terminal.from A))
      (fun V hV A A' hiso h => by
        rw [show terminal.from A = hiso.hom ≫ terminal.from A' from terminal.hom_ext _ _]
        exact Space.isEtale_comp B V hV (Space.isEtale_of_isIso B V hV hiso.hom) h)
      _ isFiberedInGroupoids_finiteHilbertProjection
      (fun ξ => ξ.exists_sectionSpace_isEtale γ hGrep hGet) U y hy A he
  -- the structural morphism to the representable terminal object is étale too
  have htoId := prop_toYonedaId_of_terminal_from (Space.IsEtale B U.left.1 U.left.2)
    (fun g _ hf => Space.isEtale_comp B U.left.1 U.left.2 hf
      (Space.isEtale_of_isIso B U.left.1 U.left.2 g)) A hterm
  -- read étaleness over `S` on the lower-shriek extension
  have hrel : Space.IsEtale B S hS (OverShriek.relocalizeToYoneda U.hom A) := by
    refine (Space.isEtale_iff_holdsOnEveryEtaleChart B S hS
      (isAlgebraicSpace_viewOver B U.left.1 S U.left.2 hS U.hom A hA)
      (isAlgebraicSpace_yoneda B S hS U) _).2 ?_
    refine (Space.holdsOnEveryEtaleChart_relocalizeToYoneda_iff B U.left.1 S U.left.2 hS U.hom
      (@_root_.AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) A).2 ?_
    exact (Space.isEtale_iff_holdsOnEveryEtaleChart B U.left.1 U.left.2 hA
      (isAlgebraicSpace_yoneda B U.left.1 U.left.2 (Over.mk (𝟙 (B.obj U.left.2)))) _).1 htoId
  exact (prop_algebraicSpaceMap_iff B S hS (Space.etaleMorphisms B S hS) U A hA).mpr hrel

/-- Let `G : 𝒳' ⟶ 𝒳` be a 1-morphism of stacks in groupoids over the big fppf site of `S` which
is representable by algebraic spaces and étale, and let `γ` present `𝒳' ⟶ 𝒴` as the composite of
`G` with `F : 𝒳 ⟶ 𝒴`. Then the canonical 1-morphism `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` of Stacks 05XN is
representable by algebraic spaces and étale.

The conclusion is the shape of `AlgebraicGeometry.Stack.IsRelativelyEtale` at the free universes
of the stacks involved: representability by algebraic spaces, and étaleness over `S` of every
algebraic space representing a fibre over a scheme-valued point. The two halves are
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_mapRelative` and
`AlgebraicGeometry.Stack.isEtale_mapRelative`. -/
@[stacks 05YG "part (1)"]
theorem isRepresentableByAlgebraicSpaces_and_isEtale_mapRelative
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (hGrep : IsRepresentableByAlgebraicSpaces B S hS G)
    (hGet : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.toBasedCategory.obj)
      (_hz : z ⋙ 𝒳.toBasedCategory.p = Over.map U.hom)
      (W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hW : IsAlgebraicSpace B U.left.1 U.left.2 W),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.toBasedCategory.p 𝒳.toBasedCategory.p z
          G.toFunctor)
        (presheafOfCategories (W ⋙ typeToCat)).p) →
      Space.IsEtale B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨W, hW⟩)).hom) :
    ∃ _ : IsRepresentableByAlgebraicSpaces B S hS
        (mapRelative B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ),
      ∀ (U : BigFppfOver B S hS)
        (y : BigFppfOver B U.left.1 U.left.2 ⥤
          (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
            (d := d)).obj)
        (_hy : y ⋙ (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴)
          (F := F) (d := d)).p = Over.map U.hom)
        (A : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
        (hA : IsAlgebraicSpace B U.left.1 U.left.2 A),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map U.hom)
            (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳') (𝒴 := 𝒴) (F := F')
              (d := d)).p
            (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
              (d := d)).p y
            (mapRelative B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ).toFunctor)
          (presheafOfCategories (A ⋙ typeToCat)).p) →
        Space.IsEtale B S hS (algebraicSpaceMap B S hS U
          ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨A, hA⟩)).hom :=
  ⟨isRepresentableByAlgebraicSpaces_mapRelative γ hGrep hGet, isEtale_mapRelative γ hGrep hGet⟩

/-- **The fibre of `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` over the universal family of an object `ξ` is
surjective over the base of `ξ`** when `G` is in addition surjective: the fibre of `G` over the
object of `𝒳` that `ξ` carries is then surjective over the cover `Z`, and its space of sections
over the base has a point over a surjective étale cover of the base by Stacks 05XQ. -/
theorem FiniteHilbert.Object.exists_sectionSpace_isSurjective
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (hGrep : IsRepresentableByAlgebraicSpaces B S hS G)
    (hGet : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.toBasedCategory.obj)
      (_hz : z ⋙ 𝒳.toBasedCategory.p = Over.map U.hom)
      (W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hW : IsAlgebraicSpace B U.left.1 U.left.2 W),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.toBasedCategory.p 𝒳.toBasedCategory.p z
          G.toFunctor)
        (presheafOfCategories (W ⋙ typeToCat)).p) →
      Space.IsEtale B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨W, hW⟩)).hom)
    (hGsurj : IsSurjectiveOnObjects B S hS 𝒳'.toBasedCategory.p 𝒳.toBasedCategory.p G.toFunctor)
    (ξ : FiniteHilbert.Object B S hS 𝒳 𝒴 F d) :
    ∃ A : (BigFppfOver B (B.inclusion.obj ξ.U.left) ξ.U.left.property)ᵒᵖ ⥤ Type u,
      (IsAlgebraicSpace B (B.inclusion.obj ξ.U.left) ξ.U.left.property A ∧
        Space.IsSurjective B (B.inclusion.obj ξ.U.left) ξ.U.left.property (terminal.from A)) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map ξ.U.hom)
          (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳') (𝒴 := 𝒴) (F := F')
            (d := d)).p
          (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F)
            (d := d)).p ξ.universalFamily
          (mapRelative B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ).toFunctor)
        (presheafOfCategories (A ⋙ typeToCat)).p) := by
  obtain ⟨W, hW, hfibre⟩ := hGrep ξ.Z ξ.sourcePoint ξ.sourcePoint_comp
  let G' : CatFiberedInGroupoids.mk 𝒳'.toBasedCategory 𝒳'.isStackInGroupoids.isFiberedInGroupoids ⟶
      CatFiberedInGroupoids.mk 𝒳.toBasedCategory 𝒳.isStackInGroupoids.isFiberedInGroupoids :=
    Bicategory.InducedBicategory.mkHom G
  have hGrel := (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, _, _, u} B S hS G'
    hGrep).1 hGsurj
  have hwS := isSurjective_relocalizeToYoneda_of_surjective_algebraicSpaceMap ξ.q W hW
    (hGrel ξ.Z ξ.sourcePoint ξ.sourcePoint_comp W hW hfibre)
  have hwet := isEtale_relocalizeToYoneda_of_isEtale_algebraicSpaceMap ξ.q W hW
    (hGet ξ.Z ξ.sourcePoint ξ.sourcePoint_comp W hW hfibre)
  have hΛW := isAlgebraicSpace_viewOver B ξ.Z.left.1 ξ.U.left.1 ξ.Z.left.2 ξ.U.left.2 ξ.q.left W hW
  have hsec := Space.isAlgebraicSpace_sectionSpace_and_isEtale (Z := Over.mk ξ.q.left) hΛW hwet
    ξ.isFinite_q
  exact ⟨_, ⟨hsec.1, Space.isSurjective_sectionSpace hΛW hwS hwet ξ.isFinite_q⟩,
    ξ.nonempty_equivalenceOver_sectionSpace W (OverShriek.relocalizeToYoneda ξ.q.left W)
      (fun _ _ => rfl) γ hfibre⟩

/-- If `G : 𝒳' ⟶ 𝒳` is representable by algebraic spaces, étale and surjective, then the
canonical 1-morphism `ℋ_d(𝒳'/𝒴) ⟶ ℋ_d(𝒳/𝒴)` is surjective.

By Stacks 06D7 surjectivity of a 1-morphism representable by algebraic spaces is surjectivity of
every algebraic space representing one of its fibres over a scheme-valued point; that algebraic
space is a space of sections of a surjective étale morphism to a finite cover of the point, which
is surjective over the point by Stacks 05XQ. -/
@[stacks 05YG "part (2)"]
theorem isSurjectiveOnObjects_mapRelative
    (γ : BasedFunctor.comp F' (𝟙 𝒴.toBasedCategory) ≅ BasedFunctor.comp G F)
    (hGrep : IsRepresentableByAlgebraicSpaces B S hS G)
    (hGet : ∀ (U : BigFppfOver B S hS)
      (z : BigFppfOver B U.left.1 U.left.2 ⥤ 𝒳.toBasedCategory.obj)
      (_hz : z ⋙ 𝒳.toBasedCategory.p = Over.map U.hom)
      (W : (BigFppfOver B U.left.1 U.left.2)ᵒᵖ ⥤ Type u)
      (hW : IsAlgebraicSpace B U.left.1 U.left.2 W),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map U.hom) 𝒳'.toBasedCategory.p 𝒳.toBasedCategory.p z
          G.toFunctor)
        (presheafOfCategories (W ⋙ typeToCat)).p) →
      Space.IsEtale B S hS (algebraicSpaceMap B S hS U
        ((spacesOverSmallerBaseFunctor B U.left.1 S U.left.2 hS U.hom).obj ⟨W, hW⟩)).hom)
    (hGsurj : IsSurjectiveOnObjects B S hS 𝒳'.toBasedCategory.p 𝒳.toBasedCategory.p
      G.toFunctor) :
    IsSurjectiveOnObjects B S hS
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳') (𝒴 := 𝒴) (F := F')
        (d := d)).p
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d)).p
      (mapRelative B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ).toFunctor := by
  let M : CatFiberedInGroupoids.mk
      (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳') (𝒴 := 𝒴) (F := F') (d := d))
      isFiberedInGroupoids_finiteHilbertProjection ⟶
      CatFiberedInGroupoids.mk
        (finiteHilbertCategory (B := B) (S := S) (hS := hS) (𝒳 := 𝒳) (𝒴 := 𝒴) (F := F) (d := d))
        isFiberedInGroupoids_finiteHilbertProjection :=
    Bicategory.InducedBicategory.mkHom
      (mapRelative B S hS d 𝒳' 𝒴 𝒳 𝒴 F' F G (𝟙 𝒴.toBasedCategory) γ)
  refine (isSurjectiveOnObjects_iff_isRelativelySurjective.{u, _, _, u} B S hS M
    (isRepresentableByAlgebraicSpaces_mapRelative γ hGrep hGet)).2 ?_
  intro U y hy A hA he
  exact surjectiveMorphismProperty_algebraicSpaceMap_of_isSurjective U A hA
    (prop_terminal_from_of_exists_sectionSpace
      (fun V hV A => Space.IsSurjective B V hV (terminal.from A))
      (fun V hV A A' hiso h => by
        rw [show terminal.from A = hiso.hom ≫ terminal.from A' from terminal.hom_ext _ _]
        exact Space.isSurjective_comp B V hV (Space.isSurjective_of_isIso B V hV hiso.hom) h)
      _ isFiberedInGroupoids_finiteHilbertProjection
      (fun ξ => ξ.exists_sectionSpace_isSurjective γ hGrep hGet hGsurj) U y hy A he)

end HilbertFamily

end AlgebraicGeometry.Stack

end
