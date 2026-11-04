module

public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteria
public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalCriteriaDiagonalToProducts
public import StacksFrontier.AlgebraicGeometry.Stacks.LocallyEssImageRepresentableDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyEquivalenceIff
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
public import StacksFrontier.AlgebraicGeometry.Stacks.StructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparison
public import StacksFrontier.CategoryTheory.FiberedCategory.UliftBasedCategory
public import StacksFrontier.CategoryTheory.Sites.Stack.StackBridge.ReverseEffective
public import StacksFrontier.CategoryTheory.Sites.Stack.Transport.UliftStack
public import StacksFrontier.CategoryTheory.Sites.Stackification.DescentPairOfMorSheaf
public import StacksFrontier.CategoryTheory.TwoFibreProduct.AbstractCancelSnd
public import StacksFrontier.CategoryTheory.TwoFibreProduct.IsTwoFibreProductOfEquivalence

/-!
# An étale stack with representable diagonal and a smooth atlas is algebraic (Stacks 076V)

Let `𝒳` be a category fibred in groupoids over the common underlying category of the big étale and
big fppf sites of `S`. **Stacks 076V** says that if `𝒳` is a stack in groupoids for the *étale*
topology, its diagonal is representable by algebraic spaces and it admits a surjective smooth
1-morphism from the category of a scheme, then `𝒳` is an algebraic stack. Conditions (2) and (3)
of the source are independent of the topology, so the content is that `𝒳` is a stack for the fppf
topology.

## The argument

Write `J` for the fppf topology and `J'` for the étale one.

1. *Morphism sheaves.* The diagonal is representable, so the isomorphism presheaves of `𝒳` are
   algebraic spaces, hence fppf sheaves (at the universes `{u, u, u + 1, u + 1}` this is
   `AlgebraicGeometry.Stack.isMorSheaf_of_isAlgebraicSpaceIsomPresheaf`).
2. *The stack of descent data.* With `Mor`-sheaves, the third stage `𝒴` of the stackification of
   Stacks 02ZN — the descent pairs of `𝒳` — is an fppf stack in groupoids, and
   `G : 𝒳 ⟶ 𝒴` is fully faithful with every object of `𝒴` fppf locally in its image
   (`StacksFrontier.CategoryTheory.Sites.Stackification.DescentPairOfMorSheaf`).
3. *The diagonal of `𝒴`.* Since `𝒳` is an étale stack, its isomorphism spaces descend: those of
   `𝒴` are algebraic spaces as well
   (`AlgebraicGeometry.Stack.isAlgebraicSpaceIsomPresheaf_of_locally_essImage`), so every
   1-morphism from a scheme to `𝒴` is representable by algebraic spaces (Stacks 045G).
4. *The atlas of `𝒴`.* The atlas `g : (Sch/U) ⟶ 𝒳` composed with `G` is surjective and smooth:
   `G` is fppf locally essentially surjective and, being fully faithful, has `g` as base change of
   `G ∘ g` (`CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_compSquare`), so Stacks 045D
   descends the two properties from `g`.
5. *Étale local lifts.* By Stacks 06XH every object of `𝒴` comes, étale locally, from `U`, hence
   from `𝒳`; since `𝒳` is an étale stack, the descent of `𝒳` along the étale covering glues these
   local preimages (`CategoryTheory.Functor.exists_iso_of_locally_essImage`), so `G` is
   essentially surjective.
6. So `G` is an equivalence over the site and `𝒳` is an fppf stack because `𝒴` is (Stacks 042W).

This is the source's proof with the quotient stack `[U/R]` replaced by the stackification of `𝒳`:
the source identifies `𝒳` with the étale stackification of the groupoid `(U, R)` and compares it
with the fppf quotient stack, and here `𝒳` is compared directly with its fppf stackification. Both
proofs rest on the same claim — an object of the fppf stack is étale locally in the image of `U`
because the base change of `U` is an algebraic space smooth and surjective over the test scheme —
which is steps 3 to 5.

## Universes

The third stage of the stackification has its morphisms in the universe of the descent data, so
the core of the argument, `AlgebraicGeometry.Stack.isStack_of_isStack_etale_aux`, is stated for
`𝒳` at object and morphism universes `max (u + 1) t`; the general statement is reduced to it
along the universe lift `CategoryTheory.CatFiberedInGroupoids.ulift`, which preserves and
reflects every hypothesis and the conclusion.

## Main results

* `AlgebraicGeometry.Stack.isStack_of_isStackInGroupoids_etale`: the fppf stack condition.
* `AlgebraicGeometry.Stack.isAlgebraicStack_of_isStackInGroupoids_etale_of_smooth`:
  **Stacks 076V**.
* `CategoryTheory.CatFiberedInGroupoids.isTwoFibreProduct_compSquare`: the base change of `g ≫ G`
  along a fully faithful `G` is `g`.

## References

* [Stacks Project, Tag 076V](https://stacks.math.columbia.edu/tag/076V)
* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 042W](https://stacks.math.columbia.edu/tag/042W)
* [Stacks Project, Tag 045D](https://stacks.math.columbia.edu/tag/045D)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits Opposite


namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C]
  {𝒲 𝒵 𝒴 : CatFiberedInGroupoids.{v₁, max v₁ v₂, u₁, max (max u₁ u₂) (max v₁ v₂)} C}

/-- The square exhibiting a 1-morphism `g ≫ G` as its own base change along `G`: apex the source of
`g`, first leg `g`, second leg the identity, filled by a unitor. -/
def compSquare (g : 𝒲 ⟶ 𝒵) (G : 𝒵 ⟶ 𝒴) : Bicategory.TwoCommSq G (g ≫ G) where
  pt := 𝒲
  fst := g
  snd := 𝟙 𝒲
  iso := (Bicategory.leftUnitor (g ≫ G)).symm

/-- **The base change of `g ≫ G` along a fully faithful `G` is `g`.** If the underlying functor of
`G` is fully faithful, the square with apex the source of `g`, legs `g` and the identity, filled by
a unitor, is a 2-fibre product of the cospan `(G, g ≫ G)`. -/
noncomputable def isTwoFibreProduct_compSquare (g : 𝒲 ⟶ 𝒵) (G : 𝒵 ⟶ 𝒴)
    [G.hom.toFunctor.Full] [G.hom.toFunctor.Faithful] :
    Bicategory.IsTwoFibreProduct (compSquare.{v₁, v₂, u₁, u₂} g G) := by
  have : (compSquare.{v₁, v₂, u₁, u₂} g G).snd.hom.toFunctor.Full :=
    inferInstanceAs (𝟭 𝒲.val.obj).Full
  have : (compSquare.{v₁, v₂, u₁, u₂} g G).snd.hom.toFunctor.Faithful :=
    inferInstanceAs (𝟭 𝒲.val.obj).Faithful
  refine Bicategory.isTwoFibreProduct_of_isEquivalence_to
    (isTwoFibreProduct_twoFibreProductSquare.{v₁, v₂, u₁, u₂} G (g ≫ G))
    (canonicalPreHom.{v₁, v₂, u₁, u₂} G (g ≫ G) (compSquare.{v₁, v₂, u₁, u₂} g G))
    (isEquivalence_canonicalPreHom.{v₁, v₂, u₁, u₂} G (g ≫ G)
      (compSquare.{v₁, v₂, u₁, u₂} g G) ?_)
  intro P
  let hG := Functor.FullyFaithful.ofFullyFaithful G.hom.toFunctor
  let ι : g.hom.toFunctor.obj P.y ≅ P.x := hG.preimageIso P.iso.symm
  have hι : G.hom.toFunctor.map ι.hom = P.iso.inv := hG.map_preimage _
  refine ⟨P.y, ι, Iso.refl _, ?_, ?_, ?_⟩
  · refine Functor.isHomLift_of_isHomLift_map_of_comp_eq G.hom.w (𝟙 P.base) ι.hom ?_
    exact hι ▸ @IsHomLift.lift_id_inv _ _ _ _ 𝒴.val.p P.base _ _ P.iso P.vertical
  · change 𝒲.val.p.IsHomLift (𝟙 P.base) (𝟙 P.y)
    rw [← P.hy]
    infer_instance
  · change G.hom.toFunctor.map ι.hom ≫ P.iso.hom = 𝟙 _ ≫ (g ≫ G).hom.toFunctor.map (𝟙 _)
    rw [hι]
    exact P.iso.inv_hom_id.trans (by simp)

end CategoryTheory.CatFiberedInGroupoids

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The core of Stacks 076V**, at object and morphism universes `max (u + 1) t`, where the third
stage of the stackification lives: an étale stack in groupoids whose isomorphism presheaves are
algebraic spaces and which has a 1-morphism from the category of a scheme that is representable by
algebraic spaces, smooth and surjective, is a stack for the fppf topology. -/
theorem isStack_of_isStack_etale_aux
    (𝒵 : CatFiberedInGroupoids.{u, max (u + 1) t, u + 1, max (u + 1) t} (BigFppfOver B S hS))
    (hstack : haveI : 𝒵.val.p.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
      𝒵.val.p.IsStack ((etaleTopology B).over (B.obj hS)))
    (hdiag : IsAlgebraicSpaceIsomPresheaf B S hS 𝒵)
    (W : BigFppfOver B S hS) (g : (schemeFibredCategory B S hS W).val ⥤ᵇ 𝒵.val)
    (hgrep : IsRepresentableByAlgebraicSpaces B S hS g)
    (hgsm : HasRelativePropertyBased B S hS (Space.smoothMorphismProperty B S hS) g hgrep)
    (hgsurj : HasRelativePropertyBased B S hS (Space.surjectiveMorphismProperty B S hS) g hgrep) :
    𝒵.val.p.IsStack (BigFppfOver.topology B S hS) := by
  classical
  let : 𝒵.val.p.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
  let J := BigFppfOver.topology B S hS
  let J' := (etaleTopology B).over (B.obj hS)
  have hJ' : J' ≤ J := fun _ _ h => etaleTopology_le_topology B _ h
  -- the isomorphism presheaves are algebraic spaces, hence fppf sheaves, and over a category
  -- fibred in groupoids `Mor(x, y)` is `Isom(x, y)`
  have hmor : ∀ (U : BigFppfOver B S hS) (x y : 𝒵.val.p.Fiber U), 𝒵.val.p.IsMorSheaf J U x y := by
    intro U x y
    obtain ⟨F, hF, ⟨i⟩⟩ := hdiag U x y
    have hiso : Presheaf.IsSheaf (BigFppfOver.topology B U.left.1 U.left.2)
        ((Over.iteratedSliceBackward U).op ⋙ 𝒵.val.p.isomPresheaf x y) := by
      have h0 := hF.isSheaf
      rw [isSheaf_iff_isSheaf_of_type] at h0 ⊢
      exact (Presieve.isSheaf_comp_uliftFunctor_iff _).1
        (Presieve.isSheaf_iso _ i (Presieve.isSheaf_comp_uliftFunctor _ h0))
    rw [Functor.IsMorSheaf,
      ← Presheaf.isSheaf_of_iso_iff
        (isomPresheafIsoMorPresheaf 𝒵.val.p 𝒵.isFiberedInGroupoids x y),
      ← Presheaf.isSheaf_of_iso_iff
        ((Functor.associator (Over.iteratedSliceForward U).op
            (Over.iteratedSliceBackward U).op (𝒵.val.p.isomPresheaf x y)).symm ≪≫
          Functor.isoWhiskerRight (NatIso.op (Over.iteratedSliceEquiv U).unitIso)
            (𝒵.val.p.isomPresheaf x y) ≪≫
          (𝒵.val.p.isomPresheaf x y).leftUnitor)]
    have : (Over.iteratedSliceForward U).IsContinuous
        ((BigFppfOver.topology B S hS).over U) (BigFppfOver.topology B U.left.1 U.left.2) :=
      inferInstanceAs ((Over.iteratedSliceForward U).IsContinuous
        ((B.topology.over (B.obj hS)).over U) (B.topology.over U.left))
    exact (Over.iteratedSliceForward U).op_comp_isSheaf_of_isSheaf _ _ _ hiso
  let q := 𝒵.val.p.descentPairProj J
  have hqstack : q.IsStack J := isStack_descentPairProj_of_isMorSheaf hmor
  have hqgpd : q.IsFiberedInGroupoids :=
    isFiberedInGroupoids_descentPairProj 𝒵.isFiberedInGroupoids hmor
  let 𝒴 : CatFiberedInGroupoids.{u, max (u + 1) t, u + 1, max (u + 1) t} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk (BasedCategory.ofFunctor q) hqgpd
  let G := toDescentPair 𝒵.val.p J
  have hG : 𝒵.val.p.IsFibredOneMorphism 𝒴.val.p G := isFibredOneMorphism_toDescentPair 𝒵.val.p J
  obtain ⟨hGfull, hGfaith⟩ := full_and_faithful_toDescentPair 𝒵.isFiberedInGroupoids hmor
  let : 𝒴.val.p.IsFibered := hqgpd.isFibered
  have hmor𝒴 : ∀ (T : BigFppfOver B S hS) (x y : 𝒴.val.p.Fiber T), 𝒴.val.p.IsMorSheaf J T x y :=
    hqstack.isMorSheaf
  have hmor𝒴' : ∀ (T : BigFppfOver B S hS) (x y : 𝒴.val.p.Fiber T),
      𝒴.val.p.IsMorSheaf J' T x y := fun T x y =>
    Presheaf.IsSheaf.of_le (fun _ _ h => hJ' _ h) (hmor𝒴 T x y)
  -- every object of the third stage is fppf locally in the image of `G`
  have hlocJ : ∀ (T : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber T),
      ∃ R ∈ J T, ∀ ⦃V : BigFppfOver B S hS⦄ (f : V ⟶ T), R.arrows f →
        ∃ z : 𝒵.val.p.Fiber V,
          Nonempty ((Fiber.mapOfComp 𝒵.val.p 𝒴.val.p G hG.comp_eq V).obj z ≅
            pullbackFiber 𝒴.val.p y f) := by
    intro T y
    obtain ⟨R, hR, hl⟩ := essImage_pullbackFiber_toDescentPair 𝒵.val.p J T y
    exact ⟨R, hR, fun V f hf => hl hf⟩
  -- the isomorphism presheaves of the third stage are algebraic spaces
  have hdiag𝒴 : IsAlgebraicSpaceIsomPresheaf B S hS 𝒴 :=
    @isAlgebraicSpaceIsomPresheaf_of_locally_essImage B S hS 𝒵 𝒴 G hGfull hGfaith hG hmor𝒴
      hstack.hasEffectiveDescent hlocJ hdiag
  -- the composite of the atlas with `G` is representable by algebraic spaces
  let G' : 𝒵 ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom ⟨G, hG.comp_eq⟩
  have : G'.hom.toFunctor.Full := hGfull
  have : G'.hom.toFunctor.Faithful := hGfaith
  have hfrep : IsRepresentableByAlgebraicSpaces B S hS (BasedFunctor.comp g G'.hom) :=
    isRepresentableFromSchemes_of_isAlgebraicSpaceIsomPresheaf B S hS 𝒴 hdiag𝒴 W _
  -- the atlas, read at the universes of `𝒵`
  let W₀ := schemeFibredCategory B S hS W
  let W' : CatFiberedInGroupoids.{u, max (u + 1) t, u + 1, max (u + 1) t} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.ulift.{u, u + 1, u, u + 1, max (u + 1) t, max (u + 1) t} W₀
  let down : W'.val ⥤ᵇ W₀.val := ⟨BasedCategory.uliftDown W₀.val, BasedCategory.uliftDown_comp _⟩
  let up : W₀.val ⥤ᵇ W'.val := ⟨BasedCategory.uliftUp W₀.val, BasedCategory.uliftUp_comp _⟩
  have : down.toFunctor.IsEquivalence :=
    (BasedCategory.uliftEquivalenceOver.{u, u + 1, u, u + 1, max (u + 1) t, max (u + 1) t}
      W₀.val).isEquivalence_hom_functor
  have : up.toFunctor.IsEquivalence := by
    let : Category.{u} (ULift.{max (u + 1) t} W₀.val.obj) := uliftCategory _
    exact (ULiftHomULiftCategory.equiv.{max (u + 1) t, max (u + 1) t}
      W₀.val.obj).isEquivalence_functor
  let g' : W' ⟶ 𝒵 := Bicategory.InducedBicategory.mkHom (BasedFunctor.comp down g)
  let f' : W' ⟶ 𝒴 := g' ≫ G'
  have hg'rep : IsRepresentableByAlgebraicSpaces B S hS g'.hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S hS g g'.hom down
      (Iso.refl _)).1 hgrep
  have hf'rep : IsRepresentableByAlgebraicSpaces B S hS f'.hom :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S hS
      (BasedFunctor.comp g G'.hom) f'.hom down (Iso.refl _)).1 hfrep
  have : (BasedFunctor.id 𝒵.val).toFunctor.IsEquivalence :=
    inferInstanceAs (𝟭 𝒵.val.obj).IsEquivalence
  -- the relative properties of the atlas pass to its universe lift
  have hg'P : ∀ (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)],
      HasRelativePropertyBased B S hS P g hgrep → HasRelativeProperty B S hS P g' hg'rep :=
    fun P _ _ h => relativeProperty_of_equivalences_symm B S hS P g g'.hom up
      (BasedFunctor.id 𝒵.val) (Iso.refl _) h
  -- `G` is fppf locally essentially surjective, in the form Stacks 045D consumes
  have hloc045 : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U),
      ∃ R ∈ BigFppfOver.topology B S hS U,
        ∀ ⦃V : BigFppfOver B S hS⦄ ⦃k : V ⟶ U⦄, R.arrows k →
          ∃ z : 𝒵.val.obj, ∃ φ : (CatFiberedInGroupoids.homFunctor G').obj z ⟶ y.1,
            𝒴.val.p.IsHomLift k φ := by
    intro U y
    obtain ⟨R, hR, hl⟩ := hlocJ U y
    refine ⟨R, hR, fun V k hk => ?_⟩
    obtain ⟨z, ⟨e⟩⟩ := hl k hk
    refine ⟨z.1, Fiber.fiberInclusion.map e.hom ≫ IsPreFibered.pullbackMap y.2 k, ?_⟩
    exact @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒴.val.p _ _ _ V
      (Fiber.fiberInclusion.map e.hom) e.hom.2 _ _ k _
      (IsPreFibered.pullbackMap.IsCartesian y.2 k).toIsHomLift
  -- the relative properties of the lifted atlas pass to its composite with `G` (Stacks 045D)
  have hf'P : ∀ (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)],
      HasRelativeProperty B S hS P g' hg'rep → HasRelativeProperty B S hS P f' hf'rep :=
    fun P _ _ h => hasRelativeProperty_of_baseChange.{u, max (u + 1) t, u, u} B S hS W' 𝒴 𝒵 P
      f' G' (CatFiberedInGroupoids.compSquare.{u, max (u + 1) t, u + 1, max (u + 1) t} g' G')
      (CatFiberedInGroupoids.isTwoFibreProduct_compSquare.{u, max (u + 1) t, u + 1,
        max (u + 1) t} g' G') hf'rep hloc045 h
  have hf'sm := hf'P _ (hg'P _ hgsm)
  have hf'surj := hf'P _ (hg'P _ hgsurj)
  -- every object of the third stage lifts étale locally along the lifted atlas (Stacks 06XH)
  have hlifts := exists_etaleCovering_fibre_lift_of_representable B S hS f' hf'rep
    (fun V yv hyv F hF e => ⟨hf'surj V yv hyv F hF e, hf'sm V yv hyv F hF e⟩)
  -- hence `G` is essentially surjective on fibres
  have hess : ∀ (U : BigFppfOver B S hS) (y : 𝒴.val.p.Fiber U), ∃ x₁ : 𝒵.val.p.Fiber U,
      Nonempty ((Fiber.mapOfComp 𝒵.val.p 𝒴.val.p G hG.comp_eq U).obj x₁ ≅ y) := by
    intro U y
    obtain ⟨R, hR, hl⟩ := hlifts U y
    refine exists_iso_of_locally_essImage (J := J') hG hstack.hasEffectiveDescent (hmor𝒴' U)
      y hR ?_
    intro V k hk
    obtain ⟨x, φ, hφ⟩ := hl hk
    have hz : 𝒵.val.p.obj (g'.hom.toFunctor.obj x) = V := by
      have h₀ := IsHomLift.domain_eq 𝒴.val.p k φ
      rw [← h₀]
      exact (Functor.congr_obj hG.comp_eq (g'.hom.toFunctor.obj x)).symm
    refine ⟨Fiber.mk hz, ⟨?_⟩⟩
    have hφc : 𝒴.val.p.IsCartesian k φ :=
      have := 𝒴.isFiberedInGroupoids.isStronglyCartesian_homLift k φ
      inferInstance
    exact fiberIsoOfCartesian k φ (IsPreFibered.pullbackMap y.2 k) hφc
      (IsPreFibered.pullbackMap.IsCartesian _ _)
  -- so `G` is an equivalence, and `𝒵` is a stack because the third stage is
  have hGess : G.EssSurj := ⟨fun Y => by
    obtain ⟨x₁, ⟨e⟩⟩ := hess (q.obj Y) (Fiber.mk rfl)
    exact ⟨x₁.1, ⟨Fiber.fiberInclusion.mapIso e⟩⟩⟩
  have hGeq : G.IsEquivalence := { }
  obtain ⟨E⟩ := StacksRepresentableCFG.nonempty_equivalenceOver_of_isEquivalence
    𝒵.isFiberedInGroupoids hqgpd G hG.comp_eq hGeq
  exact (BasedCategory.isStack_iff_of_equivalence
    (E.toBasedEquivalence (𝒳 := 𝒵.val) (𝒴 := BasedCategory.ofFunctor q)) J).2 hqstack

/-- A representable diagonal makes every 1-morphism from the category of a scheme representable. -/
private theorem isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpaces_diagonal
    (𝒳c : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS))
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒳c)) :
    IsRepresentableFromSchemes B S hS 𝒳c :=
  (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒳c).1
      ((hasRepresentableDiagonal_iff_isAlgebraicSpaceIsomPresheaf B S hS 𝒳c).1
        ((hasRepresentableDiagonal_iff B S hS 𝒳c).2 hdiag))

/-- **An étale stack with representable diagonal and a smooth surjective atlas is an fppf
stack.** Let `𝒳` be a category over the common underlying category of the big étale and fppf
sites of `S`, at any object and morphism universes, which is a stack in groupoids for the étale
topology, whose diagonal is representable by algebraic spaces, and which admits a 1-morphism from
the category of a scheme `U` over `S` that is representable by algebraic spaces, surjective and
smooth. Then `𝒳` is a stack for the fppf topology. This is the whole content of Stacks 076V. -/
theorem isStack_of_isStackInGroupoids_etale
    (𝒳 : BasedCategory.{v, w} (BigFppfOver B S hS))
    (hstack : 𝒳.p.IsStackInGroupoids.{u + 1} ((etaleTopology B).over (B.obj hS)))
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS
      (diagonalBasedFunctor B S hS (CatFiberedInGroupoids.mk 𝒳 hstack.isFiberedInGroupoids)))
    (U : BigFppfOver B S hS)
    (f : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳)
    (hfrep : IsRepresentableByAlgebraicSpaces B S hS f)
    (hfprop : ∀ (V : BigFppfOver B S hS)
        (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.obj)
        (_hy : y ⋙ 𝒳.p = Over.map V.hom)
        (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map V.hom)
            (schemeFibredCategory B S hS U).val.p 𝒳.p y f.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        (let g := (algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
         Space.IsSurjective B S hS g ∧ Space.IsSmooth B S hS g)) :
    𝒳.p.IsStack (BigFppfOver.topology B S hS) := by
  classical
  have hgpd := hstack.isFiberedInGroupoids
  let : 𝒳.p.IsFibered := hgpd.isFibered
  let 𝒳c : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk 𝒳 hgpd
  have : HasPullbacks (BigFppfOver B S hS) := hasPullbacks_bigFppfOver B S hS
  have hstack' : 𝒳.p.IsStack ((etaleTopology B).over (B.obj hS)) :=
    isStack_of_isStackInGroupoids hstack
  -- the universe lift
  let 𝒵 : CatFiberedInGroupoids.{u, max (u + 1) (max v w), u + 1, max (u + 1) (max v w)}
      (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.ulift.{u, u + 1, v, w, max (u + 1) w, max (u + 1) v} 𝒳c
  let down : 𝒵.val ⥤ᵇ 𝒳c.val := ⟨BasedCategory.uliftDown 𝒳, BasedCategory.uliftDown_comp _⟩
  let up : 𝒳c.val ⥤ᵇ 𝒵.val := ⟨BasedCategory.uliftUp 𝒳, BasedCategory.uliftUp_comp _⟩
  let f₀ : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳c.val := f
  have : down.toFunctor.IsEquivalence :=
    (BasedCategory.uliftEquivalenceOver.{u, u + 1, v, w, max (u + 1) w, max (u + 1) v}
      𝒳).isEquivalence_hom_functor
  have : up.toFunctor.IsEquivalence :=
    (BasedCategory.uliftEquivalenceOver.{u, u + 1, v, w, max (u + 1) w, max (u + 1) v}
      𝒳).isEquivalence_inv_functor
  have hstack𝒵 : have : 𝒵.val.p.IsFibered := 𝒵.isFiberedInGroupoids.isFibered
      𝒵.val.p.IsStack ((etaleTopology B).over (B.obj hS)) :=
    BasedCategory.isStack_ulift.{u, u + 1, v, w, max (u + 1) w, max (u + 1) v} 𝒳 _ hstack'
  -- the diagonal of the lift is representable
  have hfs : IsRepresentableFromSchemes B S hS 𝒳c :=
    isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpaces_diagonal B S hS 𝒳c hdiag
  have hfs𝒵 : IsRepresentableFromSchemes B S hS 𝒵 := by
    intro W y
    have : (BasedFunctor.id (schemeFibredCategory B S hS W).val).toFunctor.IsEquivalence :=
      inferInstanceAs (𝟭 _).IsEquivalence
    exact (isRepresentableByAlgebraicSpaces_iff_of_equivalences B S hS
      (𝒳 := schemeFibredCategory B S hS W) (𝒴 := 𝒳c) y
      (BasedFunctor.comp y down) (BasedFunctor.id (schemeFibredCategory B S hS W).val) down
      (Iso.refl _)).mp (hfs W (BasedFunctor.comp y down))
  have hdiag𝒵 : IsAlgebraicSpaceIsomPresheaf B S hS 𝒵 :=
    (isAlgebraicSpaceIsomPresheaf_iff_isRepresentableFromSchemes B S hS 𝒵).2 hfs𝒵
  -- the atlas, composed into the lift
  let g : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒵.val := BasedFunctor.comp f₀ up
  have hgrep : IsRepresentableByAlgebraicSpaces B S hS g :=
    (isRepresentableByAlgebraicSpaces_iff_of_equivalence_target B S hS
      (𝒳 := schemeFibredCategory B S hS U) (𝒴 := 𝒳c) (𝒴' := 𝒵) f₀ g down
      (Iso.refl _)).1 hfrep
  have : (BasedFunctor.id (schemeFibredCategory B S hS U).val).toFunctor.IsEquivalence :=
    inferInstanceAs (𝟭 _).IsEquivalence
  have hgP : ∀ (P : MorphismProperty (AlgebraicSpaces B S hS)) [P.IsStableUnderBaseChange]
      [P.IsLocalAtTarget (Space.Topology.fppf.precoverage.{u, u} B S hS)],
      HasRelativePropertyBased B S hS P f₀ hfrep → HasRelativePropertyBased B S hS P g hgrep :=
    fun P _ _ h => relativeProperty_of_equivalences_symm B S hS
      (𝒳' := schemeFibredCategory B S hS U) (𝒴' := 𝒳c) P f₀ g
      (BasedFunctor.id (schemeFibredCategory B S hS U).val) up (Iso.refl _) h
  have h𝒵 := isStack_of_isStack_etale_aux.{u, max v w} B S hS 𝒵 hstack𝒵 hdiag𝒵 U g hgrep
    (hgP _ fun V y hy F hF e => (hfprop V y hy F hF e).2)
    (hgP _ fun V y hy F hF e => (hfprop V y hy F hF e).1)
  exact (BasedCategory.isStack_ulift_iff.{u, u + 1, v, w, max (u + 1) w, max (u + 1) v} 𝒳 _).2 h𝒵

/-- **Stacks 076V.** Let `𝒳` be a category over the common underlying category of the big étale
and fppf sites of `S` — at any object and morphism universes — such that

1. `𝒳` is a stack in groupoids for the étale topology,
2. the diagonal `Δ : 𝒳 ⟶ 𝒳 × 𝒳` is representable by algebraic spaces, and
3. there are a scheme `U` over `S` and a 1-morphism `(Sch/U) ⟶ 𝒳` which is surjective and smooth.

Then `𝒳` is an algebraic stack in the sense of Stacks 026O.

Conditions (2) and (3) are stated as the corresponding clauses of
`AlgebraicGeometry.Stack.IsAlgebraicStack`, which do not depend on the topology. The
1-morphism of (3) is not assumed representable by algebraic spaces: by (2) every 1-morphism from
the category of a scheme is (Stacks 045G). What has to be proved is that `𝒳` is a stack for the
fppf topology, which is `AlgebraicGeometry.Stack.isStack_of_isStackInGroupoids_etale`.

This is Stacks 076V; its `@[stacks]` registration lives elsewhere. -/
theorem isAlgebraicStack_of_isStackInGroupoids_etale_of_smooth
    (𝒳 : BasedCategory.{v, w} (BigFppfOver B S hS))
    (hstack : 𝒳.p.IsStackInGroupoids.{u + 1} ((etaleTopology B).over (B.obj hS)))
    (hdiag : IsRepresentableByAlgebraicSpaces B S hS
      (diagonalBasedFunctor B S hS (CatFiberedInGroupoids.mk 𝒳 hstack.isFiberedInGroupoids)))
    (U : BigFppfOver B S hS)
    (f : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳)
    (hfprop : ∀ (V : BigFppfOver B S hS)
        (y : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.obj)
        (_hy : y ⋙ 𝒳.p = Over.map V.hom)
        (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
        (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
        Nonempty (StacksRepresentableCFG.EquivalenceOver
          (TwoFibreProductOver.fst (Over.map V.hom)
            (schemeFibredCategory B S hS U).val.p 𝒳.p y f.toFunctor)
          (presheafOfCategories (F ⋙ typeToCat)).p) →
        (let g := (algebraicSpaceMap B S hS V
          ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
         Space.IsSurjective B S hS g ∧ Space.IsSmooth B S hS g)) :
    IsAlgebraicStack.{u, t} B S hS 𝒳 := by
  let 𝒳c : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS) :=
    CatFiberedInGroupoids.mk 𝒳 hstack.isFiberedInGroupoids
  have hfrep : IsRepresentableByAlgebraicSpaces B S hS f :=
    isRepresentableFromSchemes_of_isRepresentableByAlgebraicSpaces_diagonal B S hS 𝒳c hdiag U f
  have hX := isStack_of_isStackInGroupoids_etale B S hS 𝒳 hstack hdiag U f hfrep hfprop
  exact ⟨hstack.isFiberedInGroupoids, ⟨hX, hX.isStackInGroupoids hstack.isFiberedInGroupoids⟩,
    hdiag, U, f, hfrep, hfprop⟩

end AlgebraicGeometry.Stack

end
