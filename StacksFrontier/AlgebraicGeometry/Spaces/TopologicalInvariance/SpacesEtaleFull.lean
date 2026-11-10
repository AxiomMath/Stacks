module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.IntegralFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversalHomeomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.OpenSubspaces
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SpacesEtaleFullGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# Fullness of base change on spaces-étale sites along a universal homeomorphism

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. This file proves that base
change `V ↦ X ×_Y V` from the spaces-étale site of `Y` to that of `X` is full as soon as `f` is
a universal homeomorphism in the sense of Stacks 05Z5, and that an integral, universally
injective and surjective morphism is one. These are the fullness half of Stacks 05ZH; the
faithfulness half is `AlgebraicGeometry.Space.faithful_spacesBaseChange_of_isSurjective`.

## Main results

* `AlgebraicGeometry.Space.universalHomeomorphism_of_isIntegralHom`: an integral, universally
  injective and surjective morphism of algebraic spaces is a universal homeomorphism.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_isPullback_of_isHomeomorph`: an open subspace
  of the source of a morphism of algebraic spaces which is a homeomorphism on points is the
  inverse image of an open subspace of the target.
* `AlgebraicGeometry.Space.full_spacesBaseChange_of_universalHomeomorphism`: base change along
  a universal homeomorphism is full on spaces-étale sites.

## Implementation notes

The fullness argument is the one of
`AlgebraicGeometry.Space.full_spacesBaseChange_of_isThickening` with the inclusion of a
thickening replaced by `f`. The graph of a morphism `c : V'_X ⟶ V_X` of base changes is an open
subspace of `(V' ×_Y V)_X`, being a base change of the relative diagonal of the unramified
`V_X ⟶ X`; the projection `(V' ×_Y V)_X ⟶ V' ×_Y V` is a homeomorphism on points because `f`
is a universal homeomorphism, so the graph is the inverse image of an open subspace
`Γ ⊂ V' ×_Y V`; and the projection `Γ ⟶ V'` is étale with an isomorphism as base change along
the point-surjective `V'_X ⟶ V'`, hence an isomorphism.

The descent of open subspaces needs nothing about thickenings: open subspaces of an algebraic
space are the subfunctors cut out by open sets of points (Stacks 03BZ), and taking inverse
images of such subfunctors is taking preimages of point sets,
`AlgebraicGeometry.Space.preimage_openSubspaceOfPoints`.

## References

* [Stacks Project, Tag 05ZH](https://stacks.math.columbia.edu/tag/05ZH)
* [Stacks Project, Tag 05Z5](https://stacks.math.columbia.edu/tag/05Z5)
* [Stacks Project, Tag 03BZ](https://stacks.math.columbia.edu/tag/03BZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

set_option synthInstance.maxHeartbeats 400000 in
-- the `HasPullbacks` instance search for presheaves on `BigFppfOver B S hS` is heavy
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance hasPullbacks_presheaf_SpacesEtaleFull :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

/-- A pullback of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
local instance (priority := high) hasPullback_presheaf_SpacesEtaleFull
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-! ### Integral, universally injective and surjective morphisms -/

section UniversalHomeomorphism

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An integral, universally injective and surjective morphism of algebraic spaces is a
universal homeomorphism.** Every base change of it along a morphism from an algebraic space is
again integral, hence universally closed and so closed on points, again universally injective,
hence injective on points, and again surjective; a continuous closed bijection is a
homeomorphism. -/
theorem universalHomeomorphism_of_isIntegralHom (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : IsIntegralHom B S hS f)
    (hinj : UniversallyInjective B S hS f) (hsurj : IsSurjective B S hS f) :
    UniversalHomeomorphism B S hS f := by
  intro Z hZ g
  have hP : IsAlgebraicSpace B S hS (pullback g f) := isAlgebraicSpace_pullback B S hS g f hZ hX hY
  have hsq : IsPullback (pullback.fst g f) (pullback.snd g f) g f := IsPullback.of_hasPullback g f
  have hint : IsIntegralHom B S hS (pullback.fst g f) :=
    isIntegralHom_of_isPullback B S hS hsq.flip hf
  have hclosed : IsClosedMap (pointsMap B S hS (pullback g f) (pullback.fst g f)) :=
    isClosed_of_universallyClosed B S hS hZ _ (universallyClosed_of_isIntegralHom B S hS hP hZ hint)
  have hinj' : Function.Injective (pointsMap B S hS (pullback g f) (pullback.fst g f)) :=
    injective_pointsMap_of_universallyInjective B S hS hZ
      (universallyInjective_of_isPullback B S hS hX hZ hY f g hinj hsq)
  have hsurj' : Function.Surjective (pointsMap B S hS (pullback g f) (pullback.fst g f)) :=
    isSurjective_of_isPullback B S hS
      (p := (ObjectProperty.homMk (pullback.snd g f) :
        (⟨pullback g f, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨X, hX⟩))
      (q := (ObjectProperty.homMk (pullback.fst g f) :
        (⟨pullback g f, hP⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Z, hZ⟩))
      (g := (ObjectProperty.homMk f : (⟨X, hX⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩))
      (f := (ObjectProperty.homMk g : (⟨Z, hZ⟩ : AlgebraicSpaces B S hS) ⟶ ⟨Y, hY⟩))
      (IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsq.flip) hsurj
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨continuous_pointsMap B S hS _, hclosed, hinj', hsurj'⟩

/-- **A universal homeomorphism is a homeomorphism on points**: it is its own base change along
the identity of its target, up to the isomorphism `X ≅ Y ×_Y X`. -/
theorem isHomeomorph_pointsMap_of_isAlgebraicSpace_of_universalHomeomorphism
    (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y} (hf : UniversalHomeomorphism B S hS f) :
    IsHomeomorph (pointsMap B S hS X f) := by
  have hsq : IsPullback f (𝟙 X) (𝟙 Y) f := IsPullback.of_vert_isIso ⟨by simp⟩
  exact isHomeomorph_pointsMap_of_comp_isIso B S hS hsq.isoPullback.hom
    hsq.isoPullback_hom_fst (hf Y hY (𝟙 Y))

end UniversalHomeomorphism

/-! ### Descending an open subspace along a homeomorphism on points -/

section OpenDescent

variable {F F' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **An open subspace of the source of a morphism which is a homeomorphism on points is the
inverse image of an open subspace of the target.** Let `g : F' ⟶ F` be a morphism of algebraic
spaces over `S` whose map on points is a homeomorphism. Every open subspace `U ⊂ F'` fits into a
cartesian square over `g` whose opposite edge is the inclusion of an open subspace `U' ⊂ F`.

`U'` is the open subspace cut out by the image of the point set of `U` (Stacks 03BZ); its inverse
image is cut out by the preimage of that image, which is the point set of `U` again because `g`
is injective on points. -/
theorem exists_isOpenSubspace_isPullback_of_isHomeomorph (hF' : IsAlgebraicSpace B S hS F')
    (hF : IsAlgebraicSpace B S hS F) (g : F' ⟶ F) (hg : IsHomeomorph (pointsMap B S hS F' g))
    (U : Subfunctor F') (hU : IsOpenSubspace B S hS U) :
    ∃ U' : Subfunctor F, IsOpenSubspace B S hS U' ∧
      ∃ a : U.toFunctor ⟶ U'.toFunctor, IsPullback a U.ι U'.ι g := by
  have hWopen : IsOpen (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS U.ι hU.2
  have hUeq : U = openSubspaceOfPoints B S hS F'
      (Set.range (pointsMap B S hS U.toFunctor U.ι)) :=
    eq_openSubspaceOfPoints_range_pointsMap B S hS hF' U hU
  set U' := openSubspaceOfPoints B S hS F
    (pointsMap B S hS F' g '' Set.range (pointsMap B S hS U.toFunctor U.ι)) with hU'
  have hpre : U'.preimage g = U := by
    rw [hU', preimage_openSubspaceOfPoints, Set.preimage_image_eq _ hg.injective]
    exact hUeq.symm
  refine ⟨U', isOpenSubspace_openSubspaceOfPoints B S hS hF _ (hg.isOpenMap _ hWopen), ?_⟩
  rw [← hpre]
  exact ⟨U'.fromPreimage g, Subfunctor.isPullback_preimage g U'⟩

end OpenDescent

/-! ### Descending a morphism of base changes along a universal homeomorphism -/

section Descent

variable {X Y : AlgebraicSpaces B S hS}
variable {A M A' M' W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Descending a morphism of base changes along a universal homeomorphism.** Let
`f : X ⟶ Y` be a universal homeomorphism of algebraic spaces over `S`, let `v' : A ⟶ Y` and
`v : M ⟶ Y` have a fibre product `(W, p₁, p₂)` whose first projection is étale, and let
`(A', πA, xA)` and `(M', πM, xM)` be base changes of `A` and `M` along `f`, with `xM`
unramified. Then every morphism `c₀ : A' ⟶ M'` over `X` is the base change of a morphism
`a : A ⟶ M` over `Y`.

The graph of `c₀` is an open subspace of the base change `W ×_Y X` of `W`
(`AlgebraicGeometry.Space.isOpenImmersion_graph_of_isUnramified`); it descends to an open
subspace `Γ ⊂ W` along the projection `W ×_Y X ⟶ W`, which is a homeomorphism on points
(`AlgebraicGeometry.Space.exists_isOpenSubspace_isPullback_of_isHomeomorph`); the projection
`Γ ⟶ A` is étale and its base change is the isomorphism from the graph to `A'`, so it is an
isomorphism (`AlgebraicGeometry.Space.isIso_of_isEtale_of_isPullback_of_isIso`); and `a` is its
inverse followed by the second projection. -/
private theorem exists_hom_baseChange_eq_of_universalHomeomorphism
    (hA : IsAlgebraicSpace B S hS A) (hA' : IsAlgebraicSpace B S hS A')
    (hM' : IsAlgebraicSpace B S hS M') (hW : IsAlgebraicSpace B S hS W)
    (f : X ⟶ Y) (hf : UniversalHomeomorphism B S hS f.hom)
    {v' : A ⟶ Y.1} {v : M ⟶ Y.1} {p₁ : W ⟶ A} {p₂ : W ⟶ M}
    (hWsq : IsPullback p₁ p₂ v' v) (hp₁ : IsEtale B S hS p₁)
    {wmap : W ⟶ Y.1} (hw : p₁ ≫ v' = wmap)
    {πA : A' ⟶ A} {xA : A' ⟶ X.1} (sqA : IsPullback πA xA v' f.hom)
    {πM : M' ⟶ M} {xM : M' ⟶ X.1} (sqM : IsPullback πM xM v f.hom)
    (hxM : IsUnramified B S hS xM) (c₀ : A' ⟶ M') (hc₀ : c₀ ≫ xM = xA) :
    ∃ a : A ⟶ M, a ≫ v = v' ∧ πA ≫ a = c₀ ≫ πM := by
  -- The base change of `W` along `f`.
  have sqW : IsPullback (pullback.fst wmap f.hom) (pullback.snd wmap f.hom) wmap f.hom :=
    IsPullback.of_hasPullback wmap f.hom
  have hP : IsAlgebraicSpace B S hS (pullback wmap f.hom) :=
    isAlgebraicSpace_pullback B S hS wmap f.hom hW X.2 Y.2
  -- The two projections of the base change of `W`, onto the base changes of `A` and `M`.
  obtain ⟨r₁, hr₁A, hr₁X⟩ : ∃ r₁ : pullback wmap f.hom ⟶ A',
      r₁ ≫ πA = pullback.fst wmap f.hom ≫ p₁ ∧ r₁ ≫ xA = pullback.snd wmap f.hom :=
    ⟨sqA.lift (pullback.fst wmap f.hom ≫ p₁) (pullback.snd wmap f.hom)
      (by rw [Category.assoc, hw]; exact sqW.w),
      sqA.lift_fst _ _ _, sqA.lift_snd _ _ _⟩
  obtain ⟨r₂, hr₂A, hr₂X⟩ : ∃ r₂ : pullback wmap f.hom ⟶ M',
      r₂ ≫ πM = pullback.fst wmap f.hom ≫ p₂ ∧ r₂ ≫ xM = pullback.snd wmap f.hom :=
    ⟨sqM.lift (pullback.fst wmap f.hom ≫ p₂) (pullback.snd wmap f.hom)
      (by rw [Category.assoc, ← hWsq.w, hw]; exact sqW.w),
      sqM.lift_fst _ _ _, sqM.lift_snd _ _ _⟩
  -- The base change of `W` is the fibre product of the base changes of `A` and `M`.
  have s₁ : IsPullback (pullback.fst wmap f.hom) r₁ p₁ πA :=
    IsPullback.of_bot (by rw [hr₁X, hw]; exact sqW) hr₁A.symm sqA
  have sqProd : IsPullback r₁ r₂ xA xM :=
    (IsPullback.of_right (by rw [hr₂A, ← sqA.w]; exact s₁.paste_horiz hWsq.flip)
      (by rw [hr₂X, hr₁X]) sqM).flip
  -- The graph of `c₀`, an open subspace of the base change of `W`.
  obtain ⟨γ, hγ₁, hγ₂⟩ : ∃ γ : A' ⟶ pullback wmap f.hom, γ ≫ r₁ = 𝟙 A' ∧ γ ≫ r₂ = c₀ :=
    ⟨sqProd.lift (𝟙 A') c₀ (by rw [Category.id_comp, hc₀]),
      sqProd.lift_fst _ _ _, sqProd.lift_snd _ _ _⟩
  have hγopen : IsOpenImmersion B S hS γ :=
    isOpenImmersion_graph_of_isUnramified B S hS hM' X.2 xM hxM sqProd c₀ hc₀ γ hγ₁ hγ₂
  have _ : Mono γ := mono_of_presheaf_isOpenImmersion hγopen
  have hinv : inv (Subfunctor.toRange γ) = (Subfunctor.range γ).ι ≫ r₁ :=
    IsIso.inv_eq_of_hom_inv_id (by rw [← Category.assoc, Subfunctor.toRange_ι, hγ₁])
  -- It descends to an open subspace of `W`.
  obtain ⟨U', hU', k, sqQ⟩ := exists_isOpenSubspace_isPullback_of_isHomeomorph B S hS hP hW
    (pullback.fst wmap f.hom) (hf W hW wmap) (Subfunctor.range γ)
    (isOpenSubspace_subfunctorRange B S hS hA' hγopen)
  -- Its projection to `A` has an isomorphism as base change, hence is an isomorphism.
  have hkiso : IsIso ((Subfunctor.range γ).ι ≫ r₁) := by rw [← hinv]; infer_instance
  have hπAsurj : IsSurjective B S hS πA :=
    (isHomeomorph_pointsMap_of_isAlgebraicSpace_of_universalHomeomorphism B S hS hA
      (universalHomeomorphism_of_isPullback B S hS X.2 hA Y.2 f.hom v' hf sqA)).surjective
  have hIso : IsIso (U'.ι ≫ p₁) :=
    isIso_of_isEtale_of_isPullback_of_isIso B S hS hU'.1 hA hA'
      (isEtale_comp B S hS (isEtale_of_isOpenImmersion B S hS hU'.2) hp₁)
      (sqQ.paste_vert s₁).flip hkiso hπAsurj
  -- The descended morphism.
  have hπA : πA = Subfunctor.toRange γ ≫ k ≫ U'.ι ≫ p₁ := by
    have h₁ : inv (Subfunctor.toRange γ) ≫ πA = k ≫ U'.ι ≫ p₁ := by
      rw [hinv]; exact (sqQ.paste_vert s₁).flip.w
    rw [← h₁, IsIso.hom_inv_id_assoc]
  have hinvfac : πA ≫ inv (U'.ι ≫ p₁) = Subfunctor.toRange γ ≫ k := by
    rw [hπA, Category.assoc, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  have hk : k ≫ U'.ι ≫ p₂ = (Subfunctor.range γ).ι ≫ r₂ ≫ πM := by
    rw [← Category.assoc, sqQ.w, Category.assoc, ← hr₂A]
  refine ⟨inv (U'.ι ≫ p₁) ≫ U'.ι ≫ p₂, ?_, ?_⟩
  · rw [Category.assoc, Category.assoc, ← hWsq.w, ← Category.assoc U'.ι p₁ v',
      IsIso.inv_hom_id_assoc]
  · rw [← Category.assoc, hinvfac, Category.assoc, hk, ← Category.assoc,
      Subfunctor.toRange_ι, ← Category.assoc, hγ₂]

end Descent

/-! ### Fullness of base change along a universal homeomorphism -/

section Full

variable {X Y : AlgebraicSpaces B S hS}

/-- Every morphism between two base changes along a universal homeomorphism is the base change
of a morphism of the spaces-étale site of the target. -/
private theorem exists_map_eq_spacesBaseChange_of_universalHomeomorphism (f : X ⟶ Y)
    (hf : UniversalHomeomorphism B S hS f.hom) (D : SpacesBaseChange B S hS f)
    (V' V : SpacesEtale B S hS Y) (c : D.functor.obj V' ⟶ D.functor.obj V) :
    ∃ a : V' ⟶ V, D.functor.map a = c := by
  have hWsq : IsPullback (pullback.fst V'.1.hom.hom V.1.hom.hom)
      (pullback.snd V'.1.hom.hom V.1.hom.hom) V'.1.hom.hom V.1.hom.hom :=
    IsPullback.of_hasPullback _ _
  have hW : IsAlgebraicSpace B S hS (pullback V'.1.hom.hom V.1.hom.hom) :=
    isAlgebraicSpace_of_isPullback V'.1.left.property V.1.left.property Y.property.isSheaf
      Y.property.diagonal_representable hWsq
  have hp₁ : IsEtale B S hS (pullback.fst V'.1.hom.hom V.1.hom.hom) :=
    isEtale_of_isPullback B S hS
      (ObjectProperty.homMk (pullback.snd V'.1.hom.hom V.1.hom.hom) :
        (⟨pullback V'.1.hom.hom V.1.hom.hom, hW⟩ : AlgebraicSpaces B S hS) ⟶ V.1.left)
      (ObjectProperty.homMk (pullback.fst V'.1.hom.hom V.1.hom.hom)) V.1.hom V'.1.hom
      (IsPullback.of_map_of_faithful (ObjectProperty.ι _) hWsq.flip) V.property
  obtain ⟨a, haV, haπ⟩ := exists_hom_baseChange_eq_of_universalHomeomorphism B S hS
    V'.1.left.property (D.functor.obj V').1.left.property (D.functor.obj V).1.left.property
    hW f hf hWsq hp₁ rfl (AlgebraicSpaces.isPullback_hom B S hS (D.isPullback V'))
    (AlgebraicSpaces.isPullback_hom B S hS (D.isPullback V))
    (isUnramified_of_isEtale B S hS (D.functor.obj V).property) c.hom.left.hom
    (congrArg (fun k ↦ k.hom) (Over.w c.hom))
  have hα : (ObjectProperty.homMk a : V'.1.left ⟶ V.1.left) ≫ V.1.hom = V'.1.hom :=
    ObjectProperty.hom_ext _ haV
  let m : V' ⟶ V := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk a) hα)
  refine ⟨m, ObjectProperty.hom_ext _ (Over.OverMorphism.ext ((D.isPullback V).hom_ext ?_ ?_))⟩
  · exact (D.projection.naturality m).trans (ObjectProperty.hom_ext _ haπ)
  · exact (Over.w (D.functor.map m).hom).trans (Over.w c.hom).symm

/-- **Fullness of base change along a universal homeomorphism.** Let `f : X ⟶ Y` be a universal
homeomorphism of algebraic spaces over `S` (Stacks 05Z5). Base change `V ↦ X ×_Y V` is full from
the spaces-étale site of `Y` to that of `X`.

This is the fullness half of Stacks 05ZH. The proof is a graph argument: the graph of a
morphism of base changes is open, it descends along the homeomorphism on points of the base
change of `f`, and the projection of the descended graph is an isomorphism because its base
change is. -/
theorem full_spacesBaseChange_of_universalHomeomorphism (f : X ⟶ Y)
    (hf : UniversalHomeomorphism B S hS f.hom) :
    (spacesBaseChange B S hS f).functor.Full where
  map_surjective {V' V} c :=
    exists_map_eq_spacesBaseChange_of_universalHomeomorphism B S hS f hf
      (spacesBaseChange B S hS f) V' V c

end Full

end AlgebraicGeometry.Space

end
