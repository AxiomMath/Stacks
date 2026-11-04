module

public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.ShortExact
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Depth
public import StacksFrontier.AlgebraicGeometry.Flatness.Flattening.StrictTransformFlatnessTransport
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffinePushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.RingTheory.Flat.ShortExact
public import StacksFrontier.Topology.Sheaves.Modules.Exactness

/-!
# Two steps of the Raynaud–Gruson induction: short exactness and affine pushforward

The dévissage step of [Stacks, Tag 0815] presents the module `ℱ` being flattened as the middle
term of a short exact sequence whose outer terms are already handled, and as the direct image of
a module along a finite — in particular affine — morphism. This module records the two
transfers of flatness of the strict transform that those presentations call for.

**Short exactness.** [Stacks, Tag 080W]
(`AlgebraicGeometry.strictTransformSheaf_shortExact`) says that a short exact sequence of
quasi-coherent modules which stays short exact after every base change of the base has short
exact strict transforms. Flatness over a base is a stalkwise condition and satisfies two out of
three ([Stacks, Tag 00HM], `_root_.flat_of_flat_of_flat`), so flatness of the strict
transforms of the two outer terms gives it for the middle one:
`AlgebraicGeometry.isFlatOver_strictTransformSheaf_middle_of_shortExact`. In the application the
first term is already flat over `S` itself, where
`AlgebraicGeometry.isFlatOver_strictTransformSheaf_of_isFlatOver` supplies the hypothesis.

**Affine pushforward.** [Stacks, Tag 080G]
(`AlgebraicGeometry.strictTransformSheafPushforwardIso`) identifies the direct image of the
strict transform of `ℱ` along the base change of an affine `g : X ⟶ Y` with the strict transform
of `g_* ℱ`; [Stacks, Tag 0FLM] (`AlgebraicGeometry.isFlatOver_pushforward_iff`) says a
quasi-coherent module on the source of an affine morphism is flat over a base exactly when its
direct image is. Together the two flattening questions — for `ℱ` over `Y ×_S S'` through
`X ⟶ Y ⟶ S`, and for `g_* ℱ` over `Y ×_S S'` — are the same question:
`AlgebraicGeometry.isFlatOver_strictTransformSheaf_iff_pushforward`. This is what lets the
induction replace the module on the closed subscheme `Z` of a dévissage by its direct image on
the smooth scheme `Y`.

## Main definitions

* `AlgebraicGeometry.schemeStalkMap`: the map on stalks induced by a morphism of modules.
* `AlgebraicGeometry.baseStalkLinearMap`: the same map, read as linear over the local ring of the
  base, which is the ring flatness over the base is measured over.

## Main results

* `AlgebraicGeometry.shortExact_schemeStalkMaps`: a short exact sequence of modules on a scheme
  is short exact on stalks ([Stacks, Tag 01AG]).
* `AlgebraicGeometry.isFlatOverAt_middle_of_shortExact`: **two out of three for flatness over the
  base**, at a point.
* `AlgebraicGeometry.isFlatOver_strictTransformSheaf_middle_of_shortExact`: **flatness of the
  strict transform of the middle term of a universally short exact sequence.**
* `AlgebraicGeometry.isFlatOver_strictTransformSheaf_iff_pushforward`: **flatness of the strict
  transform is unchanged by direct image along an affine morphism.**

## Implementation notes

The stalk of a module on a scheme is a module over the local ring of the scheme, and a morphism
of modules induces a linear map of stalks over it: that is
`AlgebraicGeometry.schemeStalkLinearMap`. Flatness over the base reads the stalk instead as a
module over the local ring of the *base*, through the stalk map of the structure morphism, so
`AlgebraicGeometry.baseStalkLinearMap` repackages the stalk map as a linear map over that ring:
the `Module.compHom` scalar multiplication is by definition the one along the stalk map, so
linearity over the base is the `X`-linearity of `AlgebraicGeometry.schemeStalkLinearMap` read at
the image scalar. Restricting scalars would say the same thing, but it needs the
`LinearMap.CompatibleSMul` instance, which is not found against the module structure that
`AlgebraicGeometry.schemeStalkLinearMap` carries inside its own type.

The comparison morphism of the affine-pushforward statement is the canonical
`pullback.lift` from `X ×_S S'` to `Y ×_S S'`, which is the base change of `g` and so is affine;
that it is a pullback square is checked by `CategoryTheory.IsPullback.of_bot` against the
pullback square of `f` and the blowup.

## References

* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 080W](https://stacks.math.columbia.edu/tag/080W)
* [Stacks Project, Tag 080G](https://stacks.math.columbia.edu/tag/080G)
* [Stacks Project, Tag 0FLM](https://stacks.math.columbia.edu/tag/0FLM)
* [Stacks Project, Tag 01AG](https://stacks.math.columbia.edu/tag/01AG)
* [Stacks Project, Tag 00HM](https://stacks.math.columbia.edu/tag/00HM)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Two out of three for flatness over the base -/

/-- The map on stalks induced by a morphism of modules on a scheme, as a morphism of abelian
groups. It is the underlying function of `AlgebraicGeometry.schemeStalkLinearMap`. -/
def schemeStalkMap {X : Scheme.{u}} {F G : X.Modules} (α : F ⟶ G) (x : X) :
    F.presheaf.stalk x ⟶ G.presheaf.stalk x :=
  (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map α.mapPresheaf

/-- **A short exact sequence of modules on a scheme is short exact on stalks**, [Stacks, Tag
01AG]. The stalk functor to abelian groups is additive, and it carries exact short complexes to
exact ones; an additive functor with that property preserves short exactness. -/
theorem shortExact_schemeStalkMaps {X : Scheme.{u}} (C : ShortComplex X.Modules)
    (hC : C.ShortExact) (x : X) :
    Function.Injective (schemeStalkMap C.f x) ∧
      Function.Exact (schemeStalkMap C.f x) (schemeStalkMap C.g x) ∧
        Function.Surjective (schemeStalkMap C.g x) := by
  let A : X.Modules ⥤ AddCommGrpCat.{u} :=
    Scheme.Modules.toPresheaf X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x
  have : A.Additive := ⟨fun {F G a b} ↦ by
    change (TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} x).map
      (a.mapPresheaf + b.mapPresheaf) = _
    exact Functor.map_add _⟩
  have hA : ∀ D : ShortComplex X.Modules, D.ShortExact → (D.map A).ShortExact :=
    (A.exact_tfae.out 2 1).mp fun D hD ↦
      (SheafOfModules.exact_iff_stalkShortComplex_exact _ D).mp hD x
  have hCA := hA C hC
  exact ⟨(AddCommGrpCat.mono_iff_injective _).mp hCA.mono_f,
    (ShortComplex.ab_exact_iff_function_exact _).mp hCA.exact,
    (AddCommGrpCat.epi_iff_surjective _).mp hCA.epi_g⟩

/-- **The stalk map of a morphism of modules, as a linear map over the local ring of the base.**
The stalk is a module over the local ring of `S` through the stalk map of `f`
(`Module.compHom`), and the stalk map of `α` is linear over the local ring of `X`, hence over
that of `S`. -/
def baseStalkLinearMap {X S : Scheme.{u}} (f : X ⟶ S) {F G : X.Modules} (α : F ⟶ G) (x : X) :
    letI : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
      Module.compHom _ (f.stalkMap x).hom
    letI : Module (S.presheaf.stalk (f x)) (G.presheaf.stalk x) :=
      Module.compHom _ (f.stalkMap x).hom
    F.presheaf.stalk x →ₗ[S.presheaf.stalk (f x)] G.presheaf.stalk x := by
  letI : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  letI : Module (S.presheaf.stalk (f x)) (G.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  exact
    { toFun := schemeStalkMap α x
      map_add' := (schemeStalkMap α x).hom.map_add
      map_smul' := fun r m ↦ (schemeStalkLinearMap α x).map_smul ((f.stalkMap x).hom r) m }

/-- **Two out of three for flatness over the base.** If the two outer terms of a short exact
sequence of modules on `X` are flat over `S` at `x`, so is the middle term: flatness over the
base is flatness of the stalk as a module over the local ring of `S`, the sequence of stalks is
short exact by [Stacks, Tag 01AG], and [Stacks, Tag 00HM] is two out of three for flatness of
modules. -/
theorem isFlatOverAt_middle_of_shortExact {X S : Scheme.{u}} (f : X ⟶ S)
    (C : ShortComplex X.Modules) (hC : C.ShortExact) (x : X)
    (h₁ : IsFlatOverAt f.toLRSHom.toShHom C.X₁ x)
    (h₃ : IsFlatOverAt f.toLRSHom.toShHom C.X₃ x) :
    IsFlatOverAt f.toLRSHom.toShHom C.X₂ x := by
  let : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  let _ (F : X.Modules) : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  have _ (F : X.Modules) : IsScalarTower (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
      (F.presheaf.stalk x) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  have : Module.Flat (S.presheaf.stalk (f x)) (C.X₁.presheaf.stalk x) := h₁
  have : Module.Flat (S.presheaf.stalk (f x)) (C.X₃.presheaf.stalk x) := h₃
  obtain ⟨hi, he, hs⟩ := shortExact_schemeStalkMaps C hC x
  change Module.Flat (S.presheaf.stalk (f x)) (C.X₂.presheaf.stalk x)
  exact _root_.flat_of_flat_of_flat (baseStalkLinearMap f C.f x) (baseStalkLinearMap f C.g x)
    hi he hs

/-! ### The strict transform of the middle term -/

/-- **The strict transform of the middle term of a universally short exact sequence is flat over
the blowup** as soon as the first term is flat over the base and the strict transform of the
third is flat over the blowup.

[Stacks, Tag 080W] gives the short exact sequence of strict transforms, and
`AlgebraicGeometry.isFlatOver_strictTransformSheaf_of_isFlatOver` turns flatness of `C.X₁` over
`S` into flatness of its strict transform; two out of three finishes. -/
theorem isFlatOver_strictTransformSheaf_middle_of_shortExact {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) (C : ShortComplex X.Modules)
    [C.X₁.IsQuasicoherent] [C.X₂.IsQuasicoherent] [C.X₃.IsQuasicoherent]
    (hC : ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (C.map (Scheme.Modules.pullback (pullback.fst f g))).ShortExact)
    (h₁ : IsFlatOver f.toLRSHom.toShHom C.X₁)
    (h₃ : IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) C.X₃)) :
    IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
      (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I) C.X₂) := by
  obtain ⟨a, b, w, hE, -, -⟩ := strictTransformSheaf_shortExact f I C hC
  exact fun x ↦ isFlatOverAt_middle_of_shortExact _ (ShortComplex.mk a b w) hE x
    (isFlatOver_strictTransformSheaf_of_isFlatOver f I C.X₁ h₁ x) (h₃ x)

/-! ### The strict transform of a direct image -/

/-- **Flatness of the strict transform is unchanged by direct image along an affine morphism.**
For `g : X ⟶ Y` affine and `f : Y ⟶ S`, the strict transform of a quasi-coherent `ℱ` on `X` is
flat over the blowup of `S` exactly when the strict transform of `g_* ℱ` is.

The two are identified by [Stacks, Tag 080G]
(`AlgebraicGeometry.strictTransformSheafPushforwardIso`) across the direct image along the base
change `g'` of `g`, which is affine because it is a base change of `g`, so [Stacks, Tag 0FLM]
(`AlgebraicGeometry.isFlatOver_pushforward_iff`) applies to it. -/
theorem isFlatOver_strictTransformSheaf_iff_pushforward {X Y S : Scheme.{u}} (g : X ⟶ Y)
    (f : Y ⟶ S) [IsAffineHom g] (I : S.IdealSheafData) (F : X.Modules) [F.IsQuasicoherent] :
    IsFlatOver (pullback.snd (g ≫ f) (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf (g ≫ f) (blowUpToBase I) (exceptionalIdeal I) F) ↔
      IsFlatOver (pullback.snd f (blowUpToBase I)).toLRSHom.toShHom
        (Stacks.StrictTransform.sheaf f (blowUpToBase I) (exceptionalIdeal I)
          ((Scheme.Modules.pushforward g).obj F)) := by
  set b := blowUpToBase I
  let g' : pullback (g ≫ f) b ⟶ pullback f b :=
    pullback.lift (pullback.fst (g ≫ f) b ≫ g) (pullback.snd (g ≫ f) b)
      (by rw [Category.assoc, pullback.condition])
  have hg' : g' ≫ pullback.snd f b = pullback.snd (g ≫ f) b := pullback.lift_snd _ _ _
  have houter : IsPullback (pullback.fst (g ≫ f) b) (g' ≫ pullback.snd f b) (g ≫ f) b := by
    rw [hg']
    exact IsPullback.of_hasPullback (g ≫ f) b
  have hsquare : IsPullback (pullback.fst (g ≫ f) b) g' g (pullback.fst f b) :=
    IsPullback.of_bot houter (pullback.lift_fst _ _ _).symm (IsPullback.of_hasPullback f b)
  have : IsAffineHom g' := MorphismProperty.of_isPullback hsquare inferInstance
  have hpush := isFlatOver_pushforward_iff g' (pullback.snd f b)
    (Stacks.StrictTransform.sheaf (g ≫ f) b (exceptionalIdeal I) F)
  rw [hg'] at hpush
  exact hpush.trans (isFlatOver_iff_of_moduleIso (pullback.snd f b).toLRSHom.toShHom
    (strictTransformSheafPushforwardIso g f I F))

end AlgebraicGeometry

end
