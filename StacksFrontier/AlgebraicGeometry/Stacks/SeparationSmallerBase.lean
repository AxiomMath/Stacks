module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactSmallerBase
public import StacksFrontier.AlgebraicGeometry.Stacks.SeparationAbsolute
public import StacksFrontier.CategoryTheory.TwoFibreProductOverRetarget

/-!
# Quasi-separatedness over a larger base descends to the base (Stacks 050N, part (4))

Let `g : S ⟶ S'` be a morphism of a big fppf site and let `𝒳` be an algebraic stack over `S`.
Construction A of Stacks, Section 04WT views `𝒳` as an algebraic stack over `S'` with the same
underlying category and the structure functor composed with `CategoryTheory.Over.map g`. This
file proves that if that view of `𝒳` is quasi-separated over `S'`, then `𝒳` is quasi-separated
over `S`; at `S' = Spec ℤ` this is part (8) of Stacks 050D implying part (4), which is part (4)
of Stacks 050N.

Quasi-separatedness over the base is a condition on the relative diagonal of the structure
morphism, so the content is that the fibre of the relative diagonal over a point of the base is
unchanged by passing to the larger base. For the *relative* diagonal of the structure 1-morphism
to the stack represented by `S` over `S'` that is
`CategoryTheory.TwoFibreProductOver.representedFibre_structure_changeBase`, which is what the
three keys of Stacks 050G consume, and its comparison is an *isomorphism* of categories. For the
*absolute* diagonal over `S'` it cannot be: the self-product of `𝒳` over `S` is a proper
subcategory of its self-product over `S'`, the inclusion being the base change of the diagonal of
`S` over `S'`. What is true, and is all that is needed, is that the inclusion is **fully
faithful**: the comparison isomorphism of an object is only ever carried forward, never pulled
back, and `CategoryTheory.Over.map g` is faithful. A fully faithful change of target induces an
isomorphism of categories on the *fibre* of a 2-fibre product, which is exactly the shape
`CategoryTheory.TwoFibreProductOver.representedFibre_changeBase_and_target` consumes.

## Main definitions

* `CategoryTheory.TwoFibreProductOver.absoluteFibreFunctor`: the comparison from the self-product
  of a category over `T/S` along its structure morphism to the self-product of the same category
  viewed over `T/S'` along *its* structure morphism.

## Main results

* `CategoryTheory.TwoFibreProductOver.full_mapBase` and `...faithful_mapBase`: changing the target
  of a 2-fibre product along a **faithful** 1-morphism is fully faithful. Fullness of the
  1-morphism is needed only for essential surjectivity, which is why
  `CategoryTheory.TwoFibreProductOver.isEquivalence_mapBase` asks for an equivalence.
* `CategoryTheory.TwoFibreProductOver.absoluteFibreFunctor_comp_structureFunctor` and
  `...absoluteFibreFunctor_comp_diagonal`: the comparison commutes with the structure functors up
  to `Over.map g`, and carries the diagonal to the diagonal, both strictly.
* `CategoryTheory.TwoFibreProductOver.representedFibre_structure_absolute`: a representing object
  for the fibre of the relative diagonal over a point of the base survives passing to the larger
  base, together with its structure morphism.
* `AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparatedOver_of_isQuasiSeparatedOver_changeBase`
  and `...isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated`: the two forms of the conclusion.

## Implementation notes

The general statement is not a Stacks tag at all. The absolute one is **part (4) of Stacks 050N**
and carries that tag under the key `quasi_separated_base`, because part (4) is a single
implication — *if `𝒳` is quasi-separated then `𝒳` is quasi-separated over `S`* — so one
fully-proved declaration is the covering set for it. Stacks 050N is registered **per part, under a
key**, not as one joint eight-way covering set: its siblings are `dm_equiv`, `quasi_dm_equiv`,
`separated_base`, `dm_source`, `quasi_dm_source` and `quasi_separated_source`. In particular
`AlgebraicGeometry.Stack.AlgebraicStacks.isSeparatedOver_of_isAbsolutelySeparated` is part (3) —
the separated analogue of the declaration below, by the same terminal-scheme construction — and it
carries `@[stacks 050N "separated_base"]`.

The comparison `absoluteFibreFunctor` is the chain used by
`CategoryTheory.TwoFibreProductOver.structureFibreEquivalenceOver` with its last step replaced by
two: the target is changed from the slice at `𝟙 S` back to the base, the base is relocalized along
`g`, the target is changed from the base of `S` to the base of `S'` along `CategoryTheory.Over.map
g` — the one step that is not an isomorphism of categories — and finally to the slice at `𝟙 S'`.
Splitting the last step in two is what keeps every leg of the result syntactically the structure
morphism of Construction A: going directly along `Over.map` of the morphism `S/S' ⟶ S'/S'` would
produce the structure functor only up to `CategoryTheory.Category.comp_id`.

The ambient categories of the two target changes are given explicitly at every use site, for the
reason recorded in `CategoryTheory.TwoFibreProductOver.mapBaseFstEquivalenceOver`'s own file:
instance search cannot solve `Over ?f.left =?= Over Y` for a metavariable `?f`, and without the
ascription the fullness and faithfulness of the iterated-slice functor are not found.

The same comparison is property-agnostic, so the DM, quasi-DM and separated analogues — parts
(1), (2) and (3) of Stacks 050N in their one-directional form — follow from
`representedFibre_structure_absolute` with
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_spacesOverSmallerBaseFunctor_iff` resp.
`AlgebraicGeometry.Space.isProper_spacesOverSmallerBaseFunctor_of` in place of the two
quasi-compactness transfers. They are not stated here.

## References

* [Stacks Project, Tag 04X5](https://stacks.math.columbia.edu/tag/04X5)
* [Stacks Project, Tag 04XB](https://stacks.math.columbia.edu/tag/04XB)
* [Stacks Project, Tag 04YW](https://stacks.math.columbia.edu/tag/04YW)
* [Stacks Project, Tag 050D](https://stacks.math.columbia.edu/tag/050D)
* [Stacks Project, Tag 050G](https://stacks.math.columbia.edu/tag/050G)
* [Stacks Project, Tag 050N](https://stacks.math.columbia.edu/tag/050N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

universe vC vT vA vB vD uC uT uA uB uD

namespace TwoFibreProductOver

section MapBase

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {T : Type uT} [Category.{vT} T]
  {𝒜 : Type uA} [Category.{vA} 𝒜] {ℬ : Type uB} [Category.{vB} ℬ]
  {𝒟 : Type uD} [Category.{vD} 𝒟]
  {pT : T ⥤ 𝒞} {p𝒜 : 𝒜 ⥤ 𝒞} {pℬ : ℬ ⥤ 𝒞} {p𝒟 : 𝒟 ⥤ 𝒞}

/-- Changing the target of a 2-fibre product is faithful, with no hypothesis on the 1-morphism
along which the target changes: a morphism of a 2-fibre product is its two components. -/
instance faithful_mapBase {G : T ⥤ ℬ} {F : 𝒜 ⥤ ℬ} {b : ℬ ⥤ 𝒟} (hb : b ⋙ p𝒟 = pℬ) :
    (mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb).Faithful where
  map_injective {P Q} {f} {g} h := by
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · simpa only [mapBase] using congrArg TwoFibreProductOver.Hom.a h
    · simpa only [mapBase] using congrArg TwoFibreProductOver.Hom.b h

/-- Changing the target of a 2-fibre product along a **faithful** 1-morphism is full: the
commutation condition on a pair of components is the image under `b` of the commutation condition
over the original target, so injectivity of `b` on morphisms transports it back. Fullness of `b`
is what the essential surjectivity in
`CategoryTheory.TwoFibreProductOver.isEquivalence_mapBase` needs, and is not needed here. -/
instance full_mapBase {G : T ⥤ ℬ} {F : 𝒜 ⥤ ℬ} {b : ℬ ⥤ 𝒟} (hb : b ⋙ p𝒟 = pℬ) [b.Faithful] :
    (mapBase (pT := pT) (p𝒜 := p𝒜) G F b hb).Full where
  map_surjective {P Q} f := by
    refine ⟨⟨f.hbase, f.a, f.b, f.ha, f.hb, ?_⟩, ?_⟩
    · apply b.map_injective
      simpa only [mapBase, Functor.comp_map, Functor.mapIso_hom, Functor.map_comp] using f.w
    · apply TwoFibreProductOver.Hom.ext' <;> rfl

/-- The inverse comparison of `CategoryTheory.TwoFibreProductOver.mapBase` is faithful. -/
instance faithful_unmapBase {G : T ⥤ ℬ} {F : 𝒜 ⥤ ℬ} {b : ℬ ⥤ 𝒟} (hb : b ⋙ p𝒟 = pℬ)
    [b.Full] [b.Faithful] :
    (unmapBase (pT := pT) (p𝒜 := p𝒜) (G := G) (F := F) hb).Faithful :=
  Functor.Faithful.of_comp_eq (unmapBase_comp_mapBase hb)

/-- The inverse comparison of `CategoryTheory.TwoFibreProductOver.mapBase` is full. -/
instance full_unmapBase {G : T ⥤ ℬ} {F : 𝒜 ⥤ ℬ} {b : ℬ ⥤ 𝒟} (hb : b ⋙ p𝒟 = pℬ)
    [b.Full] [b.Faithful] :
    (unmapBase (pT := pT) (p𝒜 := p𝒜) (G := G) (F := F) hb).Full := by
  have h : Functor.Full (unmapBase (pT := pT) (p𝒜 := p𝒜) (G := G) (F := F) hb ⋙
      mapBase G F b hb) := by
    rw [unmapBase_comp_mapBase hb]; infer_instance
  exact Functor.Full.of_comp_faithful
    (unmapBase (pT := pT) (p𝒜 := p𝒜) (G := G) (F := F) hb) (mapBase G F b hb)

end MapBase

section Relocalize

variable {T : Type uT} [Category.{vT} T] {Y Y' : T} (g : Y ⟶ Y')
  {𝒳 : Type uA} [Category.{vA} 𝒳] {𝒴 : Type uB} [Category.{vB} 𝒴]
  {𝒮 : Type uD} [Category.{vD} 𝒮]
  {p𝒳 : 𝒳 ⥤ Over Y} {p𝒴 : 𝒴 ⥤ Over Y} {p𝒮 : 𝒮 ⥤ Over Y} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- Relocalizing the base of a 2-fibre product is faithful. -/
instance faithful_relocalizeBase :
    (relocalizeBase (p𝒳 := p𝒳) (p𝒴 := p𝒴) (p𝒮 := p𝒮) (F := F) (G := G) g).Faithful where
  map_injective {P Q} {f} {k} h := by
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · exact congrArg (fun m => m.a) h
    · exact congrArg (fun m => m.b) h

variable (hF : F ⋙ p𝒮 = p𝒳) (hG : G ⋙ p𝒮 = p𝒴)

/-- Unrelocalizing the base of a 2-fibre product is faithful. -/
instance faithful_unrelocalizeBase : (unrelocalizeBase g hF hG).Faithful where
  map_injective {P Q} {f} {k} h := by
    refine TwoFibreProductOver.Hom.ext' ?_ ?_
    · exact congrArg (fun m => m.a) h
    · exact congrArg (fun m => m.b) h

include hF hG in
/-- Relocalizing the base of a 2-fibre product is full, being a section of a faithful functor
whose composite with it is the identity. -/
lemma full_relocalizeBase :
    (relocalizeBase (p𝒳 := p𝒳) (p𝒴 := p𝒴) (p𝒮 := p𝒮) (F := F) (G := G) g).Full := by
  exact Functor.Full.of_comp_faithful_iso (G := unrelocalizeBase g hF hG)
    (eqToIso (relocalizeBase_comp_unrelocalizeBase g hF hG))

end Relocalize

section AbsoluteFibre

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒳 : Type uT} [Category.{vT} 𝒳]
  {S S' : 𝒞} (p : 𝒳 ⥤ Over S) (g : S ⟶ S')

/-- **The comparison from the self-product over the base to the self-product over a larger
base.** The self-product of a category over `T/S` along its structure morphism maps to the
self-product of the same category viewed over `T/S'` along *its* structure morphism. -/
noncomputable def absoluteFibreFunctor :
    TwoFibreProductOver p p (Over.forget (Over.mk (𝟙 S)))
        (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S)))
        (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))) ⥤
      TwoFibreProductOver (p ⋙ Over.map g) (p ⋙ Over.map g) (Over.forget (Over.mk (𝟙 S')))
        ((p ⋙ Over.map g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S')))
        ((p ⋙ Over.map g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S'))) :=
  unmapBase (pT := p) (p𝒜 := p) (G := p) (F := p)
      (ℬ := Over (Over.mk (𝟙 S)).left) (𝒟 := Over (Over.mk (𝟙 S)))
      (pℬ := 𝟭 (Over S)) (p𝒟 := Over.forget (Over.mk (𝟙 S)))
      (b := Over.iteratedSliceBackward (Over.mk (𝟙 S))) (Over.mapId_eq S) ⋙
    relocalizeBase g ⋙
    mapBase (pT := p ⋙ Over.map g) (p𝒜 := p ⋙ Over.map g)
      (p𝒟 := 𝟭 (Over S')) p p (Over.map g) rfl ⋙
    mapBase (pT := p ⋙ Over.map g) (p𝒜 := p ⋙ Over.map g)
      (ℬ := Over (Over.mk (𝟙 S')).left) (𝒟 := Over (Over.mk (𝟙 S')))
      (p𝒟 := Over.forget (Over.mk (𝟙 S')))
      (p ⋙ Over.map g) (p ⋙ Over.map g) (Over.iteratedSliceBackward (Over.mk (𝟙 S')))
      (Over.mapId_eq S')

/-- The comparison is faithful. -/
instance faithful_absoluteFibreFunctor : (absoluteFibreFunctor p g).Faithful := by
  have h₁ := faithful_unmapBase (pT := p) (p𝒜 := p) (G := p) (F := p)
      (ℬ := Over (Over.mk (𝟙 S)).left) (𝒟 := Over (Over.mk (𝟙 S)))
      (pℬ := 𝟭 (Over S)) (p𝒟 := Over.forget (Over.mk (𝟙 S)))
      (b := Over.iteratedSliceBackward (Over.mk (𝟙 S))) (Over.mapId_eq S)
  have h₄ := faithful_mapBase (pT := p ⋙ Over.map g) (p𝒜 := p ⋙ Over.map g)
      (ℬ := Over (Over.mk (𝟙 S')).left) (𝒟 := Over (Over.mk (𝟙 S')))
      (pℬ := 𝟭 (Over S')) (p𝒟 := Over.forget (Over.mk (𝟙 S')))
      (G := p ⋙ Over.map g) (F := p ⋙ Over.map g)
      (b := Over.iteratedSliceBackward (Over.mk (𝟙 S'))) (Over.mapId_eq S')
  unfold absoluteFibreFunctor
  infer_instance

/-- The comparison is full: the only step that is not an isomorphism of categories is the change
of target along `CategoryTheory.Over.map g`, which is faithful. -/
instance full_absoluteFibreFunctor : (absoluteFibreFunctor p g).Full := by
  have h₁ := full_unmapBase (pT := p) (p𝒜 := p) (G := p) (F := p)
      (ℬ := Over (Over.mk (𝟙 S)).left) (𝒟 := Over (Over.mk (𝟙 S)))
      (pℬ := 𝟭 (Over S)) (p𝒟 := Over.forget (Over.mk (𝟙 S)))
      (b := Over.iteratedSliceBackward (Over.mk (𝟙 S))) (Over.mapId_eq S)
  have h₂ := full_relocalizeBase (p𝒳 := p) (p𝒴 := p) (p𝒮 := 𝟭 (Over S)) (F := p) (G := p) g
      (Functor.comp_id p) (Functor.comp_id p)
  have h₃ := full_mapBase (pT := p ⋙ Over.map g) (p𝒜 := p ⋙ Over.map g)
      (pℬ := 𝟭 (Over S) ⋙ Over.map g) (p𝒟 := 𝟭 (Over S'))
      (G := p) (F := p) (b := Over.map g) rfl
  have h₄ := full_mapBase (pT := p ⋙ Over.map g) (p𝒜 := p ⋙ Over.map g)
      (ℬ := Over (Over.mk (𝟙 S')).left) (𝒟 := Over (Over.mk (𝟙 S')))
      (pℬ := 𝟭 (Over S')) (p𝒟 := Over.forget (Over.mk (𝟙 S')))
      (G := p ⋙ Over.map g) (F := p ⋙ Over.map g)
      (b := Over.iteratedSliceBackward (Over.mk (𝟙 S'))) (Over.mapId_eq S')
  unfold absoluteFibreFunctor
  infer_instance

/-- The comparison commutes strictly with the two structure functors, up to `Over.map g`. -/
lemma absoluteFibreFunctor_comp_structureFunctor :
    absoluteFibreFunctor p g ⋙
        structureFunctor (p ⋙ Over.map g) (p ⋙ Over.map g) (Over.forget (Over.mk (𝟙 S')))
          ((p ⋙ Over.map g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S')))
          ((p ⋙ Over.map g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S'))) =
      structureFunctor p p (Over.forget (Over.mk (𝟙 S)))
          (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S)))
          (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))) ⋙ Over.map g :=
  rfl

/-- **The comparison carries the diagonal to the diagonal, strictly.** -/
lemma absoluteFibreFunctor_comp_diagonal
    (h₀ : (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))) ⋙
      Over.forget (Over.mk (𝟙 S)) = p)
    (h₂ : ((p ⋙ Over.map g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S'))) ⋙
      Over.forget (Over.mk (𝟙 S')) = p ⋙ Over.map g) :
    diagonal h₀ ⋙ absoluteFibreFunctor p g = diagonal h₂ := by
  have hobj : ∀ A : 𝒳,
      (diagonal h₀ ⋙ absoluteFibreFunctor p g).obj A = (diagonal h₂).obj A := by
    intro A
    refine obj_ext (Iso.ext ?_)
    have h1 : (Over.iteratedSliceBackward (Over.mk (𝟙 S))).Full := inferInstance
    have h2 : (Over.iteratedSliceBackward (Over.mk (𝟙 S))).Faithful := inferInstance
    have hpre : (Over.iteratedSliceBackward (Over.mk (𝟙 S))).preimage
        (𝟙 ((p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))).obj A)) = 𝟙 (p.obj A) :=
      Functor.preimage_id
    exact (congrArg (fun k => (Over.iteratedSliceBackward (Over.mk (𝟙 S'))).map
        ((Over.map g).map k)) hpre).trans
      ((congrArg (Over.iteratedSliceBackward (Over.mk (𝟙 S'))).map
        (Functor.map_id (Over.map g) (p.obj A))).trans
        (Functor.map_id (Over.iteratedSliceBackward (Over.mk (𝟙 S'))) _))
  refine Functor.ext hobj (fun A B f => Hom.ext' ?_ ?_)
  all_goals simp only [comp_a, comp_b, eqToHom_a, eqToHom_b, diagonal_map_a, diagonal_map_b]
  all_goals exact ((Category.id_comp _).trans (Category.comp_id _)).symm

end AbsoluteFibre

section AbsoluteStructureSelfProduct

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {𝒳 : Type uT} [Category.{vT} 𝒳]
  {𝒯 : Type uD} [Category.{vD} 𝒯]

/-- **A representing object for the fibre of the relative diagonal over a point of the base
survives passing to the larger base.** -/
lemma representedFibre_structure_absolute {S S' : 𝒞} (p : 𝒳 ⥤ Over S) (g : S ⟶ S')
    (U : Over S)
    (h₀ : (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))) ⋙
      Over.forget (Over.mk (𝟙 S)) = p)
    (h₂ : ((p ⋙ Over.map g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S'))) ⋙
      Over.forget (Over.mk (𝟙 S')) = p ⋙ Over.map g)
    (y : Over U.left ⥤ TwoFibreProductOver p p (Over.forget (Over.mk (𝟙 S)))
      (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S)))
      (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))))
    (hy : y ⋙ structureFunctor p p (Over.forget (Over.mk (𝟙 S)))
      (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S)))
      (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S))) = Over.map U.hom)
    (q : 𝒯 ⥤ Over U.left)
    (e : StacksRepresentableCFG.EquivalenceOver
      (fst (Over.map U.hom) p
        (structureFunctor p p (Over.forget (Over.mk (𝟙 S)))
          (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S)))
          (p ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S)))) y
        (diagonal h₀)) q) :
    ∃ y' : Over U.left ⥤ TwoFibreProductOver (p ⋙ Over.map g) (p ⋙ Over.map g)
        (Over.forget (Over.mk (𝟙 S')))
        ((p ⋙ Over.map g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S')))
        ((p ⋙ Over.map g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S'))),
      y' ⋙ structureFunctor (p ⋙ Over.map g) (p ⋙ Over.map g)
        (Over.forget (Over.mk (𝟙 S')))
        ((p ⋙ Over.map g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S')))
        ((p ⋙ Over.map g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S'))) =
          Over.map (U.hom ≫ g) ∧
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (fst (Over.map (U.hom ≫ g)) (p ⋙ Over.map g)
          (structureFunctor (p ⋙ Over.map g) (p ⋙ Over.map g)
            (Over.forget (Over.mk (𝟙 S')))
            ((p ⋙ Over.map g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S')))
            ((p ⋙ Over.map g) ⋙ Over.iteratedSliceBackward (Over.mk (𝟙 S')))) y'
          (diagonal h₂)) q) := by
  have hH := absoluteFibreFunctor_comp_structureFunctor p g
  have hd := absoluteFibreFunctor_comp_diagonal p g h₀ h₂
  refine ⟨y ⋙ absoluteFibreFunctor p g, ?_, ?_⟩
  · rw [Functor.assoc, hH, ← Functor.assoc, hy, ← Over.mapComp_eq]
  · exact representedFibre_changeBase_and_target g U.hom p _ _ _ _
      (absoluteFibreFunctor p g) hH hd rfl y hy q e

end AbsoluteStructureSelfProduct

end TwoFibreProductOver

end CategoryTheory

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w

variable (B : BigFppfSite.{u}) (S S' : Scheme.{u}) (hS : B.Contains S) (hS' : B.Contains S')
  (g : B.obj hS ⟶ B.obj hS')

/-- **Quasi-separatedness over a larger base implies quasi-separatedness over the base.** If
Construction A of `𝒳` along `g : S ⟶ S'` is quasi-separated over `S'`, then `𝒳` is
quasi-separated over `S`.

Both conditions are the Stacks 04XB quasi-compactness-and-quasi-separatedness condition on the
relative diagonal of a structure morphism, and
`CategoryTheory.TwoFibreProductOver.representedFibre_structure_absolute` carries a representing
object for the fibre of the first diagonal over a point of `S` to a representing object for the
fibre of the second over the corresponding point of `S'`, with the same representing presheaf.
The resulting morphism of algebraic spaces is then read over the two bases by
`AlgebraicGeometry.Space.isQuasiCompact_spacesOverSmallerBaseFunctor_of` and
`AlgebraicGeometry.Space.isQuasiSeparated_spacesOverSmallerBaseFunctor_of`, exactly as in the
three keys of Stacks 050G. -/
theorem isQuasiSeparatedOver_of_isQuasiSeparatedOver_changeBase
    (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : Stack.IsQuasiSeparatedOver B S' hS'
      (Stack.changeBaseAlgebraicStack B S S' hS hS' g 𝒳)) :
    Stack.IsQuasiSeparatedOver B S hS 𝒳 := by
  refine (isQuasiSeparated_iff_forall B S hS
    (Stack.structureMorphism B S hS 𝒳)).2 fun U y hy F hF he => ?_
  obtain ⟨e⟩ := he
  obtain ⟨y', hy', he'⟩ := TwoFibreProductOver.representedFibre_structure_absolute
    𝒳.val.val.p g U
    (Stack.structureMorphism B S hS 𝒳).hom.hom.w
    (Stack.structureMorphism B S' hS'
      (Stack.changeBaseAlgebraicStack B S S' hS hS' g 𝒳)).hom.hom.w
    y hy (presheafOfCategories (F ⋙ typeToCat)).p e
  have hprop := (isQuasiSeparated_iff_forall B S' hS' (Stack.structureMorphism B S' hS'
    (Stack.changeBaseAlgebraicStack B S S' hS hS' g 𝒳))).1 h𝒳
    (Over.mk (U.hom ≫ g)) y' hy' F hF he'
  exact ⟨Space.isQuasiCompact_spacesOverSmallerBaseFunctor_of B U.left.1 S U.left.2 hS
      U.hom S' hS' g _ rfl F hF hprop.1,
    Space.isQuasiSeparated_spacesOverSmallerBaseFunctor_of B U.left.1 S U.left.2 hS
      U.hom S' hS' g _ rfl F hF hprop.2⟩

/-- **Stacks 050N, part (4): a quasi-separated algebraic stack is quasi-separated over its
base.** This is part (8) of Stacks 050D implying part (4): absolute quasi-separatedness is
quasi-separatedness over the terminal scheme `Spec ℤ` after `𝒳` has been viewed over it by
Construction A, so this is
`AlgebraicGeometry.Stack.AlgebraicStacks.isQuasiSeparatedOver_of_isQuasiSeparatedOver_changeBase`
at `S' = Spec ℤ`. -/
@[stacks 050N "quasi_separated_base"]
theorem isQuasiSeparatedOver_of_isAbsolutelyQuasiSeparated
    (hZ : B.Contains (⊤_ Scheme.{u})) (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS)
    (h𝒳 : IsAbsolutelyQuasiSeparated B S hS hZ 𝒳) :
    Stack.IsQuasiSeparatedOver B S hS 𝒳 :=
  isQuasiSeparatedOver_of_isQuasiSeparatedOver_changeBase B S (⊤_ Scheme.{u}) hS hZ
    (⟨terminal.from S⟩ : B.obj hS ⟶ B.obj hZ) 𝒳 h𝒳

end AlgebraicGeometry.Stack.AlgebraicStacks

end
