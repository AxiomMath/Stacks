module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionULiftTransfer
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceLowerShriek
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafGivesSpaceQuotient

/-!
# Sheaves on the small étale site and algebraic spaces étale over the base (Stacks 0GF6)

Let `Y` be an algebraic space over a scheme `S` and `𝓕` a sheaf of sets on its small étale site
`Y_étale`. Stacks 0GF6 considers the functor on `(Sch/S)_fppf`
`X(T) = {(y, s) | y : T → Y a morphism over S and s ∈ Γ(T, y_small⁻¹ 𝓕)}`
(`AlgebraicGeometry.Space.sheafPairsFunctor`) and asserts, provided a set-theoretic condition
holds
(`AlgebraicGeometry.Space.SheafGivesSpace.SatisfiesSetTheoreticCondition`), that

1. `X` is an algebraic space,
2. the map `X → Y` is étale,
3. via `Sh(Y_étale) = Sh(Y_{spaces,étale})` one has `𝓕 ≅ h_X`,
4. `𝓕 ≅ f_{small,!} *`.

This file states and proves all four in one theorem,
`AlgebraicGeometry.Space.sheafGivesSpace`.

## Main definitions

* `AlgebraicGeometry.Space.schemeSpaceYonedaIso`: the Yoneda isomorphism between the morphisms
  from the schemes of the site into an algebraic space and the (universe-lifted) space itself.
* `AlgebraicGeometry.Space.sheafPairsFunctorToBase`: the map `X → Y` of the statement,
  `(y, s) ↦ y`, with `Y` read in the value universe of `X`.
* `AlgebraicGeometry.Space.sheafPairsHom`: the presheaf `h_X` on the spaces-étale site of `Y`,
  sending an algebraic space `U` étale over `Y` to the morphisms `U → X` over `Y`.

## Main results

* `AlgebraicGeometry.Space.sheafGivesSpace`: **Stacks 0GF6**.

## Implementation notes

The functor `X` takes values in `Type (u + 1)`, the universe of the sections of a sheaf of sets
on an étale site of an algebraic space over a scheme of universe `u`, while an algebraic space
over `S` is a presheaf of `Type u`. Accordingly part (1) is `IsAlgebraicSpaceULift.{u + 1}`
and part (2) is `IsEtaleULift.{u + 1}`, the algebraic-space and étaleness conditions of
Stacks 025Y and 03FR tested against universe-lifted scheme points. Part (4) needs the small
étale site of `X`, so it is stated for the algebraic space `X'` of `Type u` representing `X`:
the theorem provides `X'`, the étale morphism `f : X' → Y`, and an isomorphism between `X` and
the universe-lifted functor of points of `X'` under which `X → Y` is `f`.

## References

* [Stacks Project, Tag 0GF6](https://stacks.math.columbia.edu/tag/0GF6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The Yoneda isomorphism for the schemes of the big fppf site inside the algebraic spaces over
`S`: a morphism from the algebraic space represented by `T` to `Z` is a `T`-point of `Z`. The
points are lifted to `Type (u + 1)`, the universe of the morphisms of algebraic spaces. -/
noncomputable def schemeSpaceYonedaIso (Z : AlgebraicSpaces B S hS) :
    (schemeSpaceFunctor B S hS).op ⋙ yoneda.obj Z ≅ Z.obj ⋙ uliftFunctor.{u + 1} :=
  NatIso.ofComponents
    (fun T ↦ Equiv.toIso
      { toFun := fun g ↦ ULift.up (yonedaEquiv (show yoneda.obj T.unop ⟶ Z.obj from g.hom))
        invFun := fun z ↦ ObjectProperty.homMk
          (show yoneda.obj T.unop ⟶ Z.obj from yonedaEquiv.symm z.down)
        left_inv := fun g ↦ by
          refine ObjectProperty.hom_ext _ ?_
          exact yonedaEquiv.symm_apply_apply (show yoneda.obj T.unop ⟶ Z.obj from g.hom)
        right_inv := fun z ↦ by
          cases z
          change ULift.up (yonedaEquiv (yonedaEquiv.symm _)) = _
          rw [Equiv.apply_symm_apply] })
    (fun {T T'} g ↦ by
      ext x
      change ULift.up (yonedaEquiv (yoneda.map g.unop ≫
          (show yoneda.obj T.unop ⟶ Z.obj from x.hom))) =
        ULift.up (Z.obj.map g (yonedaEquiv (show yoneda.obj T.unop ⟶ Z.obj from x.hom)))
      rw [yonedaEquiv_naturality'])

/-- The Yoneda isomorphism `AlgebraicGeometry.Space.schemeSpaceYonedaIso` is natural in the
algebraic space. -/
theorem schemeSpaceYonedaIso_hom_naturality {Z Z' : AlgebraicSpaces B S hS} (g : Z ⟶ Z') :
    Functor.whiskerLeft (schemeSpaceFunctor B S hS).op (yoneda.map g) ≫
        (schemeSpaceYonedaIso B S hS Z').hom =
      (schemeSpaceYonedaIso B S hS Z).hom ≫ Functor.whiskerRight g.hom uliftFunctor.{u + 1} := by
  ext T x
  change ULift.up (yonedaEquiv ((show yoneda.obj T.unop ⟶ Z.obj from x.hom) ≫ g.hom)) =
    ULift.up (g.hom.app T (yonedaEquiv (show yoneda.obj T.unop ⟶ Z.obj from x.hom)))
  rw [yonedaEquiv_comp]

variable {Y : AlgebraicSpaces B S hS}

/-- **The map `X → Y` of Stacks 0GF6**, `(y, s) ↦ y`, on the big fppf site: the restriction of
`AlgebraicGeometry.Space.sheafPairsToBase` to the schemes of the site, followed by the Yoneda
identification of the `T`-valued morphisms into `Y` with the points `Y(T)`, lifted to the value
universe of `X`. -/
noncomputable def sheafPairsFunctorToBase (G : spacesEtaleSheafCat B S hS Y) :
    sheafPairsFunctor B S hS G ⟶ Y.obj ⋙ uliftFunctor.{u + 1} :=
  Functor.whiskerLeft (schemeSpaceFunctor B S hS).op (sheafPairsToBase B S hS G) ≫
    (schemeSpaceYonedaIso B S hS Y).hom

/-- **The presheaf `h_X` of Stacks 0GF6, part (3).** On the spaces-étale site of `Y` it sends an
algebraic space `U` étale over `Y` to the morphisms from `U` to the functor `X` over `Y`: the
natural transformations from the functor of points of `U` (lifted to the value universe of
`X`) to `X`, on `(Sch/S)_fppf`, whose composite with `X → Y` is the structure morphism of
`U`. -/
noncomputable def sheafPairsHom (G : spacesEtaleSheafCat B S hS Y) :
    (SpacesEtale B S hS Y)ᵒᵖ ⥤ Type (u + 1) where
  obj U := {g : U.unop.obj.left.obj ⋙ uliftFunctor.{u + 1} ⟶ sheafPairsFunctor B S hS G //
    g ≫ sheafPairsFunctorToBase B S hS G =
      Functor.whiskerRight U.unop.obj.hom.hom uliftFunctor.{u + 1}}
  map {U U'} φ := TypeCat.ofHom fun g ↦
    ⟨Functor.whiskerRight φ.unop.hom.left.hom uliftFunctor.{u + 1} ≫ g.1, by
      rw [Category.assoc, g.2, ← Functor.whiskerRight_comp]
      congr 1
      exact congrArg (fun k ↦ k.hom) (Over.w φ.unop.hom)⟩
  map_id U := by
    refine TypeCat.homEquiv.injective (funext fun g ↦ ?_)
    apply Subtype.ext
    change Functor.whiskerRight (𝟙 U.unop.obj.left.obj) uliftFunctor.{u + 1} ≫ g.1 = g.1
    rw [Functor.whiskerRight_id', Category.id_comp]
  map_comp φ ψ := by
    refine TypeCat.homEquiv.injective (funext fun g ↦ ?_)
    apply Subtype.ext
    change Functor.whiskerRight (ψ.unop.hom.left.hom ≫ φ.unop.hom.left.hom)
        uliftFunctor.{u + 1} ≫ g.1 =
      Functor.whiskerRight ψ.unop.hom.left.hom uliftFunctor.{u + 1} ≫
        Functor.whiskerRight φ.unop.hom.left.hom uliftFunctor.{u + 1} ≫ g.1
    rw [Functor.whiskerRight_comp, Category.assoc]

/-- Lifting to `Type (u + 1)` is fully faithful on presheaves of `Type u` on the big fppf
site. -/
noncomputable def uliftWhiskeringFullyFaithful :
    ((Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
      uliftFunctor.{u + 1}).FullyFaithful :=
  fullyFaithfulULiftFunctor.whiskeringRight _

/-- If the functor `X` attached to `G` is identified over `Y` with the universe-lifted functor
of points of the underlying space of an object `W` of the spaces-étale site, then `h_X` is the
presheaf represented by `W`. -/
noncomputable def yonedaIsoSheafPairsHom (G : spacesEtaleSheafCat B S hS Y)
    (W : SpacesEtale B S hS Y) (ι : sheafPairsFunctor B S hS G ≅
      W.obj.left.obj ⋙ uliftFunctor.{u + 1})
    (hι : sheafPairsFunctorToBase B S hS G =
      ι.hom ≫ Functor.whiskerRight W.obj.hom.hom uliftFunctor.{u + 1}) :
    yoneda.obj W ≅ sheafPairsHom B S hS G :=
  let L := (Functor.whiskeringRight (BigFppfOver B S hS)ᵒᵖ (Type u) (Type (u + 1))).obj
    uliftFunctor.{u + 1}
  let H : L.FullyFaithful := uliftWhiskeringFullyFaithful B S hS
  NatIso.ofComponents
    (fun U ↦ Equiv.toIso
      { toFun := fun φ ↦ ⟨Functor.whiskerRight φ.hom.left.hom uliftFunctor.{u + 1} ≫ ι.inv, by
          rw [Category.assoc, hι, Iso.inv_hom_id_assoc, ← Functor.whiskerRight_comp]
          congr 1
          exact congrArg (fun k ↦ k.hom) (Over.w φ.hom)⟩
        invFun := fun g ↦ ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk
          (H.preimage (g.1 ≫ ι.hom))) (by
            refine ObjectProperty.hom_ext _ (H.map_injective ?_)
            change Functor.whiskerRight (H.preimage (g.1 ≫ ι.hom) ≫ W.obj.hom.hom)
              uliftFunctor.{u + 1} = Functor.whiskerRight U.unop.obj.hom.hom uliftFunctor.{u + 1}
            rw [Functor.whiskerRight_comp]
            change L.map (H.preimage (g.1 ≫ ι.hom)) ≫ _ = _
            rw [H.map_preimage, Category.assoc, ← hι, g.2]))
        left_inv := fun φ ↦ by
          refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (ObjectProperty.hom_ext _ ?_))
          apply H.map_injective
          change L.map (H.preimage _) = _
          rw [H.map_preimage, Category.assoc, Iso.inv_hom_id, Category.comp_id]
          rfl
        right_inv := fun g ↦ by
          refine Subtype.ext ?_
          change L.map (H.preimage (g.1 ≫ ι.hom)) ≫ ι.inv = g.1
          rw [H.map_preimage, Category.assoc, Iso.hom_inv_id, Category.comp_id] })
    (fun {U U'} φ ↦ by
      ext ψ
      refine Subtype.ext ?_
      change Functor.whiskerRight (φ.unop ≫ ψ).hom.left.hom uliftFunctor.{u + 1} ≫ ι.inv =
        Functor.whiskerRight φ.unop.hom.left.hom uliftFunctor.{u + 1} ≫
          Functor.whiskerRight ψ.hom.left.hom uliftFunctor.{u + 1} ≫ ι.inv
      rw [← Category.assoc, ← Functor.whiskerRight_comp]
      rfl)

/-- Let `Y` be an algebraic space over `S` and `𝓕` a sheaf of sets on its small étale site,
satisfying the set-theoretic condition of the source's proof. Write `G` for the corresponding
sheaf on the spaces-étale site (Stacks 03G1) and `X` for the functor
`T ↦ {(y, s) | y : T → Y, s ∈ Γ(T, y⁻¹ 𝓕)}` on `(Sch/S)_fppf`. Then

1. `X` is an algebraic space;
2. the map `X → Y`, `(y, s) ↦ y`, is étale;
3. via `Sh(Y_étale) = Sh(Y_{spaces,étale})`, `𝓕 ≅ h_X`, where `h_X(U)` is the set of
   morphisms `U → X` over `Y` of functors on `(Sch/S)_fppf`;
4. `X` is the (universe-lifted) functor of points of an algebraic space `X'`, under which the
   map `X → Y` is an étale morphism `f : X' → Y`; the inverse image `f_small⁻¹` has a left
   adjoint `f_{small,!}` (Stacks 03LP), and for every such left adjoint `𝓕 ≅ f_{small,!} *`,
   where `*` is the terminal sheaf on `X'_étale`. -/
@[stacks 0GF6]
theorem sheafGivesSpace (F : Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)))
    (hF : SheafGivesSpace.SatisfiesSetTheoreticCondition B S hS Y F) :
    IsAlgebraicSpaceULift.{u + 1} B S hS
        (sheafPairsFunctor B S hS ((smallEtaleToposEquiv B S hS Y).inverse.obj F)) ∧
      IsEtaleULift.{u + 1} B S hS
        (sheafPairsFunctorToBase B S hS ((smallEtaleToposEquiv B S hS Y).inverse.obj F)) ∧
      Nonempty (((smallEtaleToposEquiv B S hS Y).inverse.obj F).obj ≅
        sheafPairsHom B S hS ((smallEtaleToposEquiv B S hS Y).inverse.obj F)) ∧
      ∃ (X' : AlgebraicSpaces B S hS) (f : X' ⟶ Y) (_ : IsEtale B S hS f.hom)
        (ι : sheafPairsFunctor B S hS ((smallEtaleToposEquiv B S hS Y).inverse.obj F) ≅
          X'.obj ⋙ uliftFunctor.{u + 1}),
        sheafPairsFunctorToBase B S hS ((smallEtaleToposEquiv B S hS Y).inverse.obj F) =
            ι.hom ≫ Functor.whiskerRight f.hom uliftFunctor.{u + 1} ∧
          (∃ L : Sheaf (SmallEtale.topology B S hS X'.1) (Type (u + 1)) ⥤
              Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)),
            Nonempty (L ⊣ (smallToposMorphism B S hS f).inverseImage)) ∧
          ∀ (L : Sheaf (SmallEtale.topology B S hS X'.1) (Type (u + 1)) ⥤
              Sheaf (SmallEtale.topology B S hS Y.1) (Type (u + 1)))
            (_ : L ⊣ (smallToposMorphism B S hS f).inverseImage),
            Nonempty (F ≅ L.obj (⊤_ (Sheaf (SmallEtale.topology B S hS X'.1) (Type (u + 1))))) := by
  let G := (smallEtaleToposEquiv B S hS Y).inverse.obj F
  obtain ⟨V, e, he⟩ := SheafGivesSpace.exists_epi_of_satisfiesSetTheoreticCondition B S hS hF
  obtain ⟨W, ⟨α⟩⟩ := exists_iso_yoneda_of_epi B S hS G V e
  let ι : sheafPairsPresheaf B S hS G ≅ yoneda.obj W.obj.left :=
    sheafPairsPresheafMapIso B S hS α ≪≫ sheafPairsPresheafRepresentableIso B S hS W
  have hι : ι.hom ≫ yoneda.map W.obj.hom = sheafPairsToBase B S hS G := by
    change ((sheafPairsPresheafMapIso B S hS α).hom ≫
      (sheafPairsPresheafRepresentableIso B S hS W).hom) ≫ yoneda.map W.obj.hom = _
    rw [Category.assoc, sheafPairsPresheafRepresentableIso_hom_comp,
      sheafPairsPresheafMapIso_hom_comp_sheafPairsToBase]
  let ι' : sheafPairsFunctor B S hS G ≅ W.obj.left.obj ⋙ uliftFunctor.{u + 1} :=
    Functor.isoWhiskerLeft (schemeSpaceFunctor B S hS).op ι ≪≫
      schemeSpaceYonedaIso B S hS W.obj.left
  have hbase : sheafPairsFunctorToBase B S hS G =
      ι'.hom ≫ Functor.whiskerRight W.obj.hom.hom uliftFunctor.{u + 1} := by
    change Functor.whiskerLeft (schemeSpaceFunctor B S hS).op (sheafPairsToBase B S hS G) ≫ _ =
      (Functor.whiskerLeft (schemeSpaceFunctor B S hS).op ι.hom ≫
        (schemeSpaceYonedaIso B S hS W.obj.left).hom) ≫ _
    rw [Category.assoc, ← schemeSpaceYonedaIso_hom_naturality, ← Category.assoc,
      ← Functor.whiskerLeft_comp, hι]
  refine ⟨?_, ?_, ?_, W.obj.left, W.obj.hom, W.property, ι', hbase, ?_⟩
  · exact isAlgebraicSpaceULift_of_iso B S hS ι'.symm
      ((isAlgebraicSpaceULift_comp_uliftFunctor_iff B S hS W.obj.left.obj).2 W.obj.left.property)
  · rw [hbase, isEtaleULift_isIso_comp_iff, isEtaleULift_whiskerRight_iff]
    exact W.property
  · let hW : Sheaf (SpacesEtale.topology B S hS Y) (Type (u + 1)) :=
      ⟨yoneda.obj W, (isSheaf_iff_isSheaf_of_type _ _).2
        (SpacesEtale.isSheaf_yoneda_obj B S hS W)⟩
    exact ⟨(sheafToPresheaf _ _).mapIso (α ≪≫ (sheafificationIso hW).symm) ≪≫
      yonedaIsoSheafPairsHom B S hS G W ι' hbase⟩
  refine ⟨⟨_, ⟨smallEtaleLowerShriekAdjunction B S hS W.obj.hom W.property⟩⟩, fun L adj ↦ ?_⟩
  obtain ⟨β⟩ := smallEtaleLowerShriek_terminal_iso B S hS W F α
  exact ⟨β ≪≫ ((smallEtaleLowerShriekAdjunction B S hS W.obj.hom W.property).leftAdjointUniq
    adj).app _⟩

end AlgebraicGeometry.Space

end
