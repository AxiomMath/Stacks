module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceCovering
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalAffineLifts
public import StacksFrontier.Deformation.Artin.RimSchlessinger.CoconeUniqueFlat
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FormallySmoothCocone
public import StacksFrontier.Deformation.Artin.RimSchlessinger.FromThickeningPushouts
public import StacksFrontier.Deformation.Artin.RimSchlessinger.Strong

/-!
# Condition (RS*) from a smooth atlas which is formally smooth on objects

Let `𝒳` be a stack in groupoids over the big fppf site of `S` with representable diagonal, and let
`P : (Sch/U) ⟶ 𝒳` be a 1-morphism from a scheme, representable by algebraic spaces, surjective and
smooth, which is moreover formally smooth on objects ([Stacks Project, Tag 06D0]). Then `𝒳`
satisfies condition (RS*) of [Stacks Project, Tag 07Y8].

Fix a square of condition (RS*): affine schemes `X ⊂ X'` (a first-order thickening), `X ⟶ Y` and
`Y' = Y ⨿_X X'`. Full faithfulness of the comparison
`𝒳_{Y'} ⟶ 𝒳_Y ×_{𝒳_X} 𝒳_{X'}` comes from the representable diagonal alone
(`Deformation.Artin.fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal`). For
essential surjectivity, take an object `x` over `Y`, `x'` over `X'` and an identification over
`X`; this is a span of `𝒳` over the square, and what is wanted is a cocone over it.

1. By part (2) of [Stacks Project, Tag 06XH], `x` lifts along `P` over a jointly surjective family
   of étale morphisms `W k ⟶ Y` with affine sources.
2. By the topological invariance of the étale site ([Stacks Project, Tag 039R]) these lift to étale
   morphisms `Y'_k ⟶ Y'`, whose sources are affine ([Stacks Project, Tag 06AD]) and which cover
   `Y'`.
3. The base change of the square along `Y'_k ⟶ Y'` is again a square of the same kind and a
   pushout. Over it, the object over `Y` comes from the atlas; formal smoothness on objects extends
   the lift across the thickening `X_k ⊂ X'_k`, and in the slice category over `U` every span over
   a pushout square has a cocone. Carried back along `P`, this is a cocone over the restricted
   span.
4. Cocones over spans at flat affine base changes are unique up to unique isomorphism, by full
   faithfulness again, so the local cocones glue
   (`CategoryTheory.Functor.IsStackInGroupoids.nonempty_cocone_of_baseChange`).

## Main results

* `Deformation.Artin.nonempty_cocone_of_atlas_of_hasLiftsAlong`: cocones over spans at a square
  with affine corners, cartesian global sections and two thickenings as legs, for a stack with a
  smooth atlas having lifts along the base changes of the thickening.
* `Deformation.Artin.nonempty_cocone_of_atlas`: cocones over spans at a square of condition
  (RS*), for a stack with such an atlas.
* `Deformation.Artin.satisfiesRSStar_of_atlas`: condition (RS*) for such a stack.

## Implementation notes

The source ([Stacks Project, Tag 07WN]) builds the object over `Y'` by pushing out algebraic
spaces; here the pushout is taken only in the slice category over the scheme `U`, where it is a
pushout of schemes, and the algebraic space appears only through formal smoothness on objects of
the atlas.

## References

* [Stacks Project, Tag 07Y8](https://stacks.math.columbia.edu/tag/07Y8)
* [Stacks Project, Tag 07WN](https://stacks.math.columbia.edu/tag/07WN)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

universe u

namespace Deformation.Artin

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] Space.preservesLimitsOfShape_walkingCospan_toScheme

/-- The pullback of a flat morphism of affine objects along a morphism of affine objects is affine,
and its first projection is flat. -/
private theorem isAffine_and_flat_pullback_fst {X Y Z : BigFppfOver B S hS} (f : X ⟶ Z)
    (g : Y ⟶ Z) [IsAffine ((BigFppfOver.toScheme B S hS).obj X)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Y)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Z)]
    [Flat ((BigFppfOver.toScheme B S hS).map g)] :
    IsAffine ((BigFppfOver.toScheme B S hS).obj (pullback f g)) ∧
      Flat ((BigFppfOver.toScheme B S hS).map (pullback.fst f g)) := by
  have sq := (IsPullback.of_hasPullback f g).map (BigFppfOver.toScheme B S hS)
  exact ⟨IsAffine.of_isPullback sq, MorphismProperty.of_isPullback sq.flip inferInstance⟩

/-- **Cocones at a thickening square, through a smooth atlas with lifts along its base
changes.** Let `𝒳` be a stack in groupoids with representable diagonal, and `P : (Sch/U) ⟶ 𝒳`
representable by algebraic spaces, surjective and smooth. Let `Q` be a commutative square of the
site with affine corners and cartesian square of global sections whose second map `Q.g` and third
map `Q.i` are thickenings, and suppose that `P` has lifts along the base change of `Q.g` along
every étale morphism from an affine object to the terminal corner. Then every span of `𝒳` over
`Q` has a cocone. -/
theorem nonempty_cocone_of_atlas_of_hasLiftsAlong
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hst : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳)
    {U : BigFppfOver B S hS} (P : Stack.schemeFibredCategory B S hS U ⟶ 𝒳)
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS P.hom)
    (hprop : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
      (_hyv : yv ⋙ 𝒳.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) (Stack.schemeFibredCategory B S hS U).val.p
          𝒳.val.p yv (CatFiberedInGroupoids.homFunctor P))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h))
    (Q : BaseSquare (BigFppfOver B S hS))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.Z)]
    (hΓ : IsPullback ((BigFppfOver.toScheme B S hS).map Q.i).appTop
      ((BigFppfOver.toScheme B S hS).map Q.j).appTop
      ((BigFppfOver.toScheme B S hS).map Q.f).appTop
      ((BigFppfOver.toScheme B S hS).map Q.g).appTop)
    (hgt : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map Q.g))
    (hit : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map Q.i))
    (hlift : ∀ (Z₁ : BigFppfOver B S hS) (τ : Z₁ ⟶ Q.Z),
      Etale ((BigFppfOver.toScheme B S hS).map τ) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z₁) → Stack.HasLiftsAlong P (Q.baseChange τ).g)
    (s : SquareSpan 𝒳.val.p Q.f Q.g) : Nonempty (s.Cocone Q.i Q.j) := by
  let T := BigFppfOver.toScheme B S hS
  have hp := hst.isStackInGroupoids.{u + 1} 𝒳.isFiberedInGroupoids
  have hx : 𝒳.val.p.obj s.x = Q.V := IsHomLift.codomain_eq _ Q.f s.α
  obtain ⟨I, W, e, he, hW, hjs, hlift'⟩ :=
    Stack.exists_affine_etale_family_lift_of_representable B S hS P hrep hprop Q.V ⟨s.x, hx⟩
  obtain ⟨Z₁, τ, ι, hτ, hZ₁, hι, hcov⟩ :=
    BigFppfOver.exists_etale_covering_lift_of_isThickening B S hS Q.i hit W e he hW hjs
  refine hp.nonempty_cocone_of_baseChange Q τ hcov s ?_ ?_ ?_
  · -- local existence, through the atlas
    intro k s' m
    have := hZ₁ k
    have : Flat (T.map (τ k)) := inferInstance
    let Qk := Q.baseChange (τ k)
    let a := Q.baseChangeHom (τ k)
    have hpush : IsPushout Qk.f Qk.g Qk.i Qk.j :=
      IsPushout.of_map T Qk.w (isPushout_toScheme_baseChange_of_flat B S hS Q hΓ hgt (τ k))
    have hcoc : ∀ t : SquareSpan (Stack.schemeFibredCategory B S hS U).val.p Qk.f Qk.g,
        Nonempty (t.Cocone Qk.i Qk.j) := fun t => SquareSpan.nonempty_cocone_over_forget hpush t
    -- the object of the atlas over the middle corner
    obtain ⟨x₀, α₀, hα₀⟩ := hlift' k
    let F := CatFiberedInGroupoids.homFunctor P
    have hF : F ⋙ 𝒳.val.p = (Stack.schemeFibredCategory B S hS U).val.p :=
      CatFiberedInGroupoids.homFunctor_comp_p P
    have hx₀ : (Stack.schemeFibredCategory B S hS U).val.p.obj x₀ = W k := by
      rw [← hF]; exact IsHomLift.domain_eq 𝒳.val.p (e k) α₀
    have hιk : ι k ≫ e k = a.aV := hι k
    obtain ⟨x₁, l₁, hl₁⟩ :=
      (Stack.schemeFibredCategory B S hS U).isFiberedInGroupoids.exists_lift (ι k) x₀ hx₀
    have h₁ : 𝒳.val.p.IsHomLift (ι k) (F.map l₁) := isHomLift_map_of_comp_eq hF (ι k) l₁
    have h₂ : 𝒳.val.p.IsHomLift a.aV (F.map l₁ ≫ α₀) := by
      rw [← hιk]; infer_instance
    have hmx : 𝒳.val.p.IsHomLift a.aV m.mx := m.isHomLift_mx
    let ε := 𝒳.isFiberedInGroupoids.fill (f := a.aV) (g := 𝟙 Qk.V) (f' := a.aV) (by simp)
      m.mx (F.map l₁ ≫ α₀)
    have hε : 𝒳.val.p.IsHomLift (𝟙 Qk.V) ε := 𝒳.isFiberedInGroupoids.fill_isHomLift _ _ _
    exact Stack.nonempty_cocone_of_hasLiftsAlong Qk (hlift _ (τ k) (hτ k) (hZ₁ k)) hcoc s' x₁ ε
  · intro k l
    have := hZ₁ k
    have := hZ₁ l
    obtain ⟨_, _⟩ := isAffine_and_flat_pullback_fst B S hS (τ k) (τ l)
    have : Flat (T.map (pullback.fst (τ k) (τ l) ≫ τ k)) := by
      rw [T.map_comp]; infer_instance
    exact hasUniqueSquareCocones_baseChange_of_flat B S hS 𝒳 hdiag Q hΓ hgt _
  · intro k l m
    have := hZ₁ k
    have := hZ₁ l
    have := hZ₁ m
    obtain ⟨_, _⟩ := isAffine_and_flat_pullback_fst B S hS (τ k) (τ l)
    obtain ⟨_, _⟩ := isAffine_and_flat_pullback_fst B S hS (τ l) (τ m)
    obtain ⟨_, _⟩ := isAffine_and_flat_pullback_fst B S hS (pullback.snd (τ k) (τ l))
      (pullback.fst (τ l) (τ m))
    have : Flat (T.map (pullback.fst (pullback.snd (τ k) (τ l)) (pullback.fst (τ l) (τ m)) ≫
        pullback.fst (τ k) (τ l) ≫ τ k)) := by
      rw [T.map_comp, T.map_comp]; infer_instance
    exact hasUniqueSquareCocones_baseChange_of_flat B S hS 𝒳 hdiag Q hΓ hgt _


/-- **Cocones at a square of condition (RS*), through a smooth atlas formally smooth on objects.**
Let `𝒳` be a stack in groupoids with representable diagonal, and `P : (Sch/U) ⟶ 𝒳` representable
by algebraic spaces, surjective, smooth and formally smooth on objects. For a commutative square
`Q` of the site with affine corners, cartesian square of global sections and second map a
surjection on global sections with square-zero kernel, every span of `𝒳` over `Q` has a cocone. -/
theorem nonempty_cocone_of_atlas
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hst : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳)
    {U : BigFppfOver B S hS} (P : Stack.schemeFibredCategory B S hS U ⟶ 𝒳)
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS P.hom)
    (hprop : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
      (_hyv : yv ⋙ 𝒳.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) (Stack.schemeFibredCategory B S hS U).val.p
          𝒳.val.p yv (CatFiberedInGroupoids.homFunctor P))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h))
    (hFS : Stack.IsFormallySmoothOnObjects B S hS (Stack.schemeFibredCategory B S hS U) 𝒳 P)
    (Q : BaseSquare (BigFppfOver B S hS))
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.U)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.V)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.W)]
    [IsAffine ((BigFppfOver.toScheme B S hS).obj Q.Z)]
    (hΓ : IsPullback ((BigFppfOver.toScheme B S hS).map Q.i).appTop
      ((BigFppfOver.toScheme B S hS).map Q.j).appTop
      ((BigFppfOver.toScheme B S hS).map Q.f).appTop
      ((BigFppfOver.toScheme B S hS).map Q.g).appTop)
    (hsurj : Function.Surjective ((BigFppfOver.toScheme B S hS).map Q.g).appTop.hom)
    (hker : RingHom.ker ((BigFppfOver.toScheme B S hS).map Q.g).appTop.hom ^ 2 = ⊥)
    (s : SquareSpan 𝒳.val.p Q.f Q.g) : Nonempty (s.Cocone Q.i Q.j) := by
  let T := BigFppfOver.toScheme B S hS
  have hg : Stacks.Thickenings.IsFirstOrderThickening (T.map Q.g) :=
    isFirstOrderThickening_of_surjective_appTop _ hsurj hker
  have hi : Stacks.Thickenings.IsFirstOrderThickening (T.map Q.i) :=
    isFirstOrderThickening_of_isPullback_appTop _ _ _ _ hΓ hsurj hker
  refine nonempty_cocone_of_atlas_of_hasLiftsAlong B S hS 𝒳 hst hdiag P hrep hprop Q hΓ
    hg.isThickening hi.isThickening ?_ s
  intro Z₁ τ hτ hZ₁ x y' φ hφ
  have := hτ
  have := hZ₁
  let Qk := Q.baseChange τ
  let a := Q.baseChangeHom τ
  have sX' : IsPullback (T.map Qk.j) (T.map a.aW) (T.map τ) (T.map Q.j) :=
    (Q.isPullback_baseChange_j τ).map T
  have sX'' : IsPullback (T.map Qk.g) (T.map a.aU) (T.map a.aW) (T.map Q.g) :=
    (Q.isPullback_baseChange_g τ).map T
  have hWk : IsAffine (T.obj Qk.W) := IsAffine.of_isPullback sX'
  have hUk : IsAffine (T.obj Qk.U) := IsAffine.of_isPullback sX''
  have hgk : Stacks.Thickenings.IsFirstOrderThickening (T.map Qk.g) :=
    Stacks.Thickenings.isFirstOrderThickening_of_isPullback sX'' hg
  have := hφ
  exact hFS.exists_lift Qk.g hUk hWk hgk φ

/-- **Condition (RS*) for a stack with a smooth atlas formally smooth on objects.** A stack in
groupoids over the big fppf site of `S` with representable diagonal and a 1-morphism from a scheme
which is representable by algebraic spaces, surjective, smooth and formally smooth on objects
satisfies condition (RS*) of [Stacks Project, Tag 07Y8]. -/
theorem satisfiesRSStar_of_atlas
    (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (hst : 𝒳.val.p.IsStack (BigFppfOver.topology B S hS))
    (hdiag : Stack.HasRepresentableDiagonal B S hS 𝒳)
    {U : BigFppfOver B S hS} (P : Stack.schemeFibredCategory B S hS U ⟶ 𝒳)
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS P.hom)
    (hprop : ∀ (V : BigFppfOver B S hS)
      (yv : BigFppfOver B V.left.1 V.left.2 ⥤ 𝒳.val.obj)
      (_hyv : yv ⋙ 𝒳.val.p = Over.map V.hom)
      (F : (BigFppfOver B V.left.1 V.left.2)ᵒᵖ ⥤ Type u)
      (hF : IsAlgebraicSpace B V.left.1 V.left.2 F),
      Nonempty (StacksRepresentableCFG.EquivalenceOver
        (TwoFibreProductOver.fst (Over.map V.hom) (Stack.schemeFibredCategory B S hS U).val.p
          𝒳.val.p yv (CatFiberedInGroupoids.homFunctor P))
        (presheafOfCategories (F ⋙ typeToCat)).p) →
      (let h := (algebraicSpaceMap B S hS V
        ((spacesOverSmallerBaseFunctor B V.left.1 S V.left.2 hS V.hom).obj ⟨F, hF⟩)).hom
       Space.IsSurjective B S hS h ∧ Space.IsSmooth B S hS h))
    (hFS : Stack.IsFormallySmoothOnObjects B S hS (Stack.schemeFibredCategory B S hS U) 𝒳 P) :
    SatisfiesRSStar B S hS 𝒳.val.p 𝒳.isFiberedInGroupoids := by
  let : 𝒳.val.p.IsFibered := 𝒳.isFiberedInGroupoids.isFibered
  intro U' V W Z f g i j h hsq hsurj hker
  let ι := BigAffineFppf.inclusion B S hS
  let T := BigFppfOver.toScheme B S hS
  have : IsAffine (T.obj (ι.obj U')) := U'.property
  have : IsAffine (T.obj (ι.obj V)) := V.property
  have : IsAffine (T.obj (ι.obj W)) := W.property
  have : IsAffine (T.obj (ι.obj Z)) := Z.property
  have hw : ι.map f ≫ ι.map i = ι.map g ≫ ι.map j := by
    simpa only [Functor.map_comp] using congrArg ι.map h
  let Q : BaseSquare (BigFppfOver B S hS) := ⟨_, _, _, _, ι.map f, ι.map g, ι.map i, ι.map j, hw⟩
  have hfirst : Stacks.Thickenings.IsFirstOrderThickening (T.map (ι.map g)) :=
    isFirstOrderThickening_of_surjective_appTop _ hsurj hker
  have hpush : IsPushout (T.map (ι.map f)) (T.map (ι.map g)) (T.map (ι.map i))
      (T.map (ι.map j)) :=
    isPushout_of_isPullback_appTop _ _ _ _ hsq hsurj
  have hFF := fullyFaithful_fiberSquareComparison_of_hasRepresentableDiagonal B S hS 𝒳 hdiag
    (ι.map g) (ι.map f) (ι.map j) (ι.map i) hw.symm hfirst.isThickening hpush.flip
  have := hFF.full
  have := hFF.faithful
  have : (fiberSquareComparison 𝒳.val.p (chosenPullbacks 𝒳.val.p) (ι.map f) (ι.map g)
      (ι.map i) (ι.map j) hw).EssSurj :=
    essSurj_fiberSquareComparison_of_nonempty_cocone 𝒳.isFiberedInGroupoids _ _ _ _ _ hw
      fun s => nonempty_cocone_of_atlas B S hS 𝒳 hst hdiag P hrep hprop hFS Q hsq hsurj hker s
  exact Functor.IsEquivalence.mk

end Deformation.Artin

end
