module

public import StacksFrontier.AlgebraicGeometry.Topologies.CartesianFlatAffineSite
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
public import StacksFrontier.CategoryTheory.Sites.Stack.InheritedSite
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv

/-!
# Fibre products in the affine part of a full subcategory of a fibred category

Let `p : 𝒞 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids, let `P` be a property of the
objects of `𝒞` and let `W` be a class of morphisms of schemes, stable under base change, such that
`P` is closed under arrows lying over members of `W`: if `f : x ⟶ y` lies over a member of `W` and
`y` has `P` then so does `x`. Let `A` be the full subcategory of the objects of `P.FullSubcategory`
lying over affine schemes, and let `Q` be the class of arrows of `A` lying over members of `W`.

This is the shape of the affine part of the lisse-étale site (`P` the smooth objects, `W` the étale
morphisms) and of the flat-fppf site (`P` the flat objects, `W` the flat morphisms locally of
finite presentation) of an algebraic stack. Such a site does not have fibre products in general,
but it has them along the members of `Q`: the fibre product in `𝒞` exists because `𝒞` is fibred
in groupoids (**Stacks 06N5**), lies over the fibre product of schemes, so over an affine scheme,
and has `P` because its second projection lies over a base change of a member of `W`.

## Main results

* `AlgebraicGeometry.Stack.AffineFullSubsite.isPullback_map_of_isPullback`: a fibre product
  square of `A` along a member of `Q` is a fibre product square of `𝒞`.
* `AlgebraicGeometry.Stack.AffineFullSubsite.preservesPullbacksAlong`: and lies over a fibre
  product square of schemes.
* `AlgebraicGeometry.Stack.AffineFullSubsite.hasPullbacks`,
  `AlgebraicGeometry.Stack.AffineFullSubsite.isStableUnderBaseChange`: `Q` has fibre products and
  is stable under base change.

## References

* [Stacks Project, Tag 06N5](https://stacks.math.columbia.edu/tag/06N5)
* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack.AffineFullSubsite

universe u v v'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒞 : Type v} [Category.{v'} 𝒞] (p : 𝒞 ⥤ BigFppfOver B S hS) (P : ObjectProperty 𝒞)

/-- The scheme underneath an object of a full subcategory of `𝒞`. -/
abbrev schemeFunctor : P.FullSubcategory ⥤ Scheme.{u} :=
  P.ι ⋙ p ⋙ BigFppfOver.toScheme B S hS

/-- The objects of a full subcategory of `𝒞` lying over affine schemes. -/
abbrev affineObject : ObjectProperty P.FullSubcategory :=
  fun x => IsAffine ((schemeFunctor B S hS p P).obj x)

/-- The arrows between objects over affine schemes whose underlying morphism of schemes lies in
`W`. -/
def morphismProperty (W : MorphismProperty Scheme.{u}) :
    MorphismProperty (affineObject B S hS p P).FullSubcategory :=
  fun _ _ f => W (((affineObject B S hS p P).ι ⋙ schemeFunctor B S hS p P).map f)

/-- The inclusion of the objects over affine schemes into `𝒞`. -/
abbrev inclusion : (affineObject B S hS p P).FullSubcategory ⥤ 𝒞 :=
  (affineObject B S hS p P).ι ⋙ P.ι

/-- The arrows between objects over affine schemes whose underlying morphism of schemes lies in
`W` are stable under composition when `W` is. -/
instance isStableUnderComposition (W : MorphismProperty Scheme.{u})
    [W.IsStableUnderComposition] :
    (morphismProperty B S hS p P W).IsStableUnderComposition where
  comp_mem f g hf hg := by
    change W (((affineObject B S hS p P).ι ⋙ schemeFunctor B S hS p P).map (f ≫ g))
    rw [Functor.map_comp]
    exact W.comp_mem _ _ hf hg

variable {B S hS p P}

/-- The base functor carries a fibre product square of `𝒞` along an arbitrary arrow to a fibre
product square of schemes, `𝒞` being fibred in groupoids (**Stacks 06N5**). -/
theorem map_isPullback_toScheme (hp : p.IsFiberedInGroupoids) {x y z w : 𝒞} {φ : x ⟶ z}
    {g : y ⟶ z} {q₁ : w ⟶ y} {q₂ : w ⟶ x} (hq : IsPullback q₁ q₂ g φ) :
    IsPullback ((p ⋙ BigFppfOver.toScheme B S hS).map q₁)
      ((p ⋙ BigFppfOver.toScheme B S hS).map q₂) ((p ⋙ BigFppfOver.toScheme B S hS).map g)
      ((p ⋙ BigFppfOver.toScheme B S hS).map φ) := by
  have : p.IsFibered := hp.isFibered
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    comp_preservesLimitsOfShape _ _
  exact (Functor.map_isPullback_of_isPullback p (hp.isStronglyCartesian φ) g hq).map
    (BigFppfOver.toScheme B S hS)

variable {W : MorphismProperty Scheme.{u}}

/-- The fibre product in `𝒞` of an arrow of `A` lying over a member of `W` with an arbitrary arrow
of `A` lies in `A`. -/
theorem exists_isPullback (hp : p.IsFiberedInGroupoids) [W.IsStableUnderBaseChange]
    (hP : ∀ ⦃x y : 𝒞⦄ (f : x ⟶ y), W ((p ⋙ BigFppfOver.toScheme B S hS).map f) → P y → P x)
    {X Y Z : (affineObject B S hS p P).FullSubcategory} {f : X ⟶ Z}
    (hf : morphismProperty B S hS p P W f)
    (g : Y ⟶ Z) :
    ∃ (T : (affineObject B S hS p P).FullSubcategory) (fst : T ⟶ X) (snd : T ⟶ Y),
      IsPullback ((inclusion B S hS p P).map fst) ((inclusion B S hS p P).map snd)
        ((inclusion B S hS p P).map f) ((inclusion B S hS p P).map g) := by
  have : p.IsFibered := hp.isFibered
  let G := inclusion B S hS p P
  have : p.IsStronglyCartesian (p.map (G.map f)) (G.map f) := hp.isStronglyCartesian _
  have : HasPullback (G.map f) (G.map g) :=
    Functor.IsFibered.hasPullback_of_isStronglyCartesian p _ _
  have hpb := IsPullback.of_hasPullback (G.map f) (G.map g)
  have hsch := map_isPullback_toScheme hp hpb
  have hPT : P (pullback (G.map f) (G.map g)) :=
    hP _ (MorphismProperty.of_isPullback hsch hf) Y.obj.property
  have : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj (G.obj X)) := X.property
  have : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj (G.obj Y)) := Y.property
  have : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj (G.obj Z)) := Z.property
  have haff : IsAffine ((p ⋙ BigFppfOver.toScheme B S hS).obj (pullback (G.map f) (G.map g))) :=
    @IsAffine.of_isIso _ _ hsch.isoPullback.hom inferInstance inferInstance
  let T : (affineObject B S hS p P).FullSubcategory := ⟨⟨_, hPT⟩, haff⟩
  exact ⟨T, ObjectProperty.homMk (ObjectProperty.homMk (pullback.fst _ _)),
    ObjectProperty.homMk (ObjectProperty.homMk (pullback.snd _ _)), hpb⟩

/-- **A fibre product square of `A` along an arrow lying over a member of `W` is a fibre product
square of `𝒞`.** -/
theorem isPullback_map_of_isPullback (hp : p.IsFiberedInGroupoids) [W.IsStableUnderBaseChange]
    (hP : ∀ ⦃x y : 𝒞⦄ (f : x ⟶ y), W ((p ⋙ BigFppfOver.toScheme B S hS).map f) → P y → P x)
    {X Y Z T : (affineObject B S hS p P).FullSubcategory} {fst : T ⟶ X} {snd : T ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback fst snd f g) (hf : morphismProperty B S hS p P W f) :
    IsPullback ((inclusion B S hS p P).map fst) ((inclusion B S hS p P).map snd)
      ((inclusion B S hS p P).map f) ((inclusion B S hS p P).map g) := by
  let G := inclusion B S hS p P
  obtain ⟨T', fst', snd', h'⟩ := exists_isPullback hp hP hf g
  have hT' : IsPullback fst' snd' f g := h'.of_map_of_faithful
  refine IsPullback.of_iso h' (G.mapIso (h.isoIsPullback _ _ hT')).symm (Iso.refl _) (Iso.refl _)
    (Iso.refl _) ?_ ?_ (by simp) (by simp)
  · simp only [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.comp_id]
    exact (congrArg G.map (h.isoIsPullback_inv_fst _ _ hT').symm).trans (G.map_comp _ _)
  · simp only [Iso.symm_hom, Functor.mapIso_inv, Iso.refl_hom, Category.comp_id]
    exact (congrArg G.map (h.isoIsPullback_inv_snd _ _ hT').symm).trans (G.map_comp _ _)

/-- **The scheme functor of `A` preserves the fibre products along the members of `Q`.** -/
theorem preservesPullbacksAlong (hp : p.IsFiberedInGroupoids) [W.IsStableUnderBaseChange]
    (hP : ∀ ⦃x y : 𝒞⦄ (f : x ⟶ y), W ((p ⋙ BigFppfOver.toScheme B S hS).map f) → P y → P x) :
    Stacks.FlatAffineSite.PreservesPullbacksAlong
      ((affineObject B S hS p P).ι ⋙ schemeFunctor B S hS p P) (morphismProperty B S hS p P W) :=
  fun _ _ _ _ _ _ _ _ h hf => map_isPullback_toScheme hp (isPullback_map_of_isPullback hp hP h hf)

/-- **The arrows of `A` lying over members of `W` have fibre products in `A`.** -/
theorem hasPullbacks (hp : p.IsFiberedInGroupoids) [W.IsStableUnderBaseChange]
    (hP : ∀ ⦃x y : 𝒞⦄ (f : x ⟶ y), W ((p ⋙ BigFppfOver.toScheme B S hS).map f) → P y → P x) :
    (morphismProperty B S hS p P W).HasPullbacks where
  hasPullback {X Y Z f} g hf := by
    obtain ⟨T, fst, snd, h⟩ := exists_isPullback hp hP hf g
    exact h.of_map_of_faithful.hasPullback

/-- **The arrows of `A` lying over members of `W` are stable under base change in `A`.** -/
theorem isStableUnderBaseChange (hp : p.IsFiberedInGroupoids) [W.IsStableUnderBaseChange]
    (hP : ∀ ⦃x y : 𝒞⦄ (f : x ⟶ y), W ((p ⋙ BigFppfOver.toScheme B S hS).map f) → P y → P x) :
    (morphismProperty B S hS p P W).IsStableUnderBaseChange where
  of_isPullback {_ _ _ _ _ _ _ _} sq hg :=
    MorphismProperty.of_isPullback (P := W) (preservesPullbacksAlong hp hP sq hg) hg

end AlgebraicGeometry.Stack.AffineFullSubsite

end
